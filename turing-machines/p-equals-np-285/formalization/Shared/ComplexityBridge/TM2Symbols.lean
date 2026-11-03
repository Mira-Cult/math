import Shared.ComplexityBridge.CanonicalClasses

/-! Finite reachable stack symbols and finite-alphabet translation for the
pinned mathlib TM2 model. One TM2 step executes a complete statement block.
The normalized bundle uses classical finite enumeration; it is not an
effective reification of arbitrary Lean functions. Input/output boundaries,
finite numeric codes, and single-tape polynomial simulations remain separate. -/
namespace Shared.ComplexityBridge.TM2Symbols

open Turing.TM2

variable {K Λ σ : Type} {Γ : K → Type}

/-- Values that a statement can push onto a given stack, over all local states. -/
def pushed (k : K) : Stmt Γ Λ σ → Set (Γ k)
  | .push j f q => {a | ∃ (h : j = k) (s : σ), h ▸ f s = a} ∪ pushed k q
  | .peek _ _ q => pushed k q
  | .pop _ _ q => pushed k q
  | .load _ q => pushed k q
  | .branch _ q₁ q₂ => pushed k q₁ ∪ pushed k q₂
  | .goto _ => ∅
  | .halt => ∅

theorem pushed_finite [Finite σ] [DecidableEq K] (k : K) (q : Stmt Γ Λ σ) :
    (pushed k q).Finite := by
  induction q with
  | push j f q ih =>
    by_cases h : j = k
    · subst j
      have hs : {a | ∃ (h : k = k) (s : σ), h ▸ f s = a} = Set.range f := by
        ext a
        simp [Set.mem_range]
      rw [pushed, hs]
      exact (Set.finite_range f).union ih
    · simpa [pushed, h] using ih
  | peek j f q ih => exact ih
  | pop j f q ih => exact ih
  | load f q ih => exact ih
  | branch f q₁ q₂ ih₁ ih₂ => exact ih₁.union ih₂
  | goto f => exact Set.finite_empty
  | halt => exact Set.finite_empty

def programPushed (M : Λ → Stmt Γ Λ σ) (k : K) : Set (Γ k) :=
  ⋃ l : Λ, pushed k (M l)

theorem programPushed_finite [Finite σ] [Finite Λ] [DecidableEq K]
    (M : Λ → Stmt Γ Λ σ) (k : K) : (programPushed M k).Finite := by
  exact Set.finite_iUnion fun l => pushed_finite k (M l)


theorem update_push_member [DecidableEq K] (S : ∀ k, List (Γ k)) (j : K) (b : Γ j)
    (k : K) (a : Γ k) (h : a ∈ (Function.update S j (b :: S j)) k) :
    a ∈ S k ∨ ∃ hj : j = k, hj ▸ b = a := by
  by_cases hj : j = k
  · subst j
    simp only [Function.update_self, List.mem_cons] at h
    rcases h with h | h
    · right; exact ⟨rfl, h.symm⟩
    · exact Or.inl h
  · have heq : k ≠ j := Ne.symm hj
    simp only [Function.update_of_ne heq] at h
    exact Or.inl h

theorem update_pop_member [DecidableEq K] (S : ∀ k, List (Γ k)) (j k : K) (a : Γ k)
    (h : a ∈ (Function.update S j (S j).tail) k) : a ∈ S k := by
  by_cases hj : j = k
  · subst j
    simp only [Function.update_self] at h
    exact List.mem_of_mem_tail h
  · have heq : k ≠ j := Ne.symm hj
    simpa only [Function.update_of_ne heq] using h

theorem stepAux_member [DecidableEq K] (q : Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (k : K) (a : Γ k)
    (h : a ∈ (stepAux q v S).stk k) : a ∈ S k ∨ a ∈ pushed k q := by
  induction q generalizing v S with
  | push j f q ih =>
    change a ∈ (stepAux q v (Function.update S j (f v :: S j))).stk k at h
    rcases ih v _ h with h | h
    · rcases update_push_member S j (f v) k a h with old | fresh
      · exact Or.inl old
      · right
        exact Or.inl ⟨fresh.choose, v, fresh.choose_spec⟩
    · exact Or.inr (Or.inr h)
  | peek j f q ih =>
    exact ih _ S h
  | pop j f q ih =>
    change a ∈ (stepAux q (f v (S j).head?) (Function.update S j (S j).tail)).stk k at h
    rcases ih _ _ h with h | h
    · exact Or.inl (update_pop_member S j k a h)
    · exact Or.inr h
  | load f q ih => exact ih _ S h
  | branch f q₁ q₂ ih₁ ih₂ =>
    by_cases hf : f v
    · have hh : a ∈ (stepAux q₁ v S).stk k := by simpa [stepAux, hf] using h
      rcases ih₁ v S hh with old | fresh
      · exact Or.inl old
      · exact Or.inr (Or.inl fresh)
    · have hh : a ∈ (stepAux q₂ v S).stk k := by simpa [stepAux, hf] using h
      rcases ih₂ v S hh with old | fresh
      · exact Or.inl old
      · exact Or.inr (Or.inr fresh)
  | goto f => exact Or.inl h
  | halt => exact Or.inl h


/-- All program-generated symbols plus the entire finite input alphabet on the
input stack. This set does not depend on the input value or run length. -/
def allowed (tm : Turing.FinTM2) (k : tm.K) : Set (tm.Γ k) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  exact programPushed tm.m k ∪ if k = tm.k₀ then Set.univ else ∅

theorem allowed_finite (tm : Turing.FinTM2) (k : tm.K) : (allowed tm k).Finite := by
  letI : Fintype tm.σ := tm.σFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : DecidableEq tm.K := tm.kDecidableEq
  by_cases h : k = tm.k₀
  · subst k
    letI : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin
    exact Set.toFinite _
  · simpa [allowed, h] using programPushed_finite tm.m k

def Safe (tm : Turing.FinTM2) (c : tm.Cfg) : Prop :=
  ∀ k a, a ∈ c.stk k → a ∈ allowed tm k

theorem initial_safe (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) :
    Safe tm (Turing.initList tm input) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  intro k a ha
  by_cases hk : k = tm.k₀
  · subst k
    simp [allowed]
  · have : a ∈ ([] : List (tm.Γ k)) := by simpa [Turing.initList, hk] using ha
    simp at this

theorem step_safe (tm : Turing.FinTM2) {c d : tm.Cfg}
    (hc : Safe tm c) (hstep : d ∈ tm.step c) : Safe tm d := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  rcases c with ⟨l, v, S⟩
  cases l with
  | none =>
    change d ∈ (none : Option tm.Cfg) at hstep
    exact False.elim ((Option.not_mem_none d) hstep)
  | some l =>
    change d ∈ some (stepAux (tm.m l) v S) at hstep
    have hd : d = stepAux (tm.m l) v S := (Option.mem_some_iff.mp hstep).symm
    subst d
    intro k a ha
    rcases stepAux_member (tm.m l) v S k a ha with old | fresh
    · exact hc k a old
    · left
      exact Set.mem_iUnion.mpr ⟨l, fresh⟩

theorem reachable_safe (tm : Turing.FinTM2) (input : List (tm.Γ tm.k₀)) (c : tm.Cfg)
    (h : Relation.ReflTransGen (fun a b => b ∈ tm.step a) (Turing.initList tm input) c) :
    Safe tm c := by
  induction h with
  | refl => exact initial_safe tm input
  | tail hprev hstep ih => exact step_safe tm ih hstep


/-- Replace each stack alphabet by a subtype that contains all values that
the statement can push. Local reads are projected back to the original alphabet. -/
def restrictStmt (A : ∀ k, Set (Γ k)) : (q : Stmt Γ Λ σ) →
    (∀ k, pushed k q ⊆ A k) → Stmt (fun k => {a : Γ k // a ∈ A k}) Λ σ
  | .push j f q, h => .push j
      (fun v => ⟨f v, h j (Or.inl ⟨rfl, v, rfl⟩)⟩)
      (restrictStmt A q (fun k _ ha => h k (Or.inr ha)))
  | .peek j f q, h => .peek j
      (fun v o => f v (o.map Subtype.val)) (restrictStmt A q h)
  | .pop j f q, h => .pop j
      (fun v o => f v (o.map Subtype.val)) (restrictStmt A q h)
  | .load f q, h => .load f (restrictStmt A q h)
  | .branch f q₁ q₂, h => .branch f
      (restrictStmt A q₁ (fun k _ ha => h k (Or.inl ha)))
      (restrictStmt A q₂ (fun k _ ha => h k (Or.inr ha)))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

/-- Each label's translated statement uses the same uniform finite alphabets. -/
def restrictProgram (tm : Turing.FinTM2) (l : tm.Λ) :
    Stmt (fun k => {a : tm.Γ k // a ∈ allowed tm k}) tm.Λ tm.σ :=
  restrictStmt (allowed tm) (tm.m l) (fun k _ ha => Or.inl (Set.mem_iUnion.mpr ⟨l, ha⟩))


def eraseStacks (A : ∀ k, Set (Γ k))
    (S : ∀ k, List {a : Γ k // a ∈ A k}) : ∀ k, List (Γ k) :=
  fun k => (S k).map Subtype.val

def eraseCfg (A : ∀ k, Set (Γ k))
    (c : Cfg (fun k => {a : Γ k // a ∈ A k}) Λ σ) : Cfg Γ Λ σ :=
  ⟨c.l, c.var, eraseStacks A c.stk⟩

theorem erase_update [DecidableEq K] (A : ∀ k, Set (Γ k))
    (S : ∀ k, List {a : Γ k // a ∈ A k}) (j : K)
    (xs : List {a : Γ j // a ∈ A j}) :
    eraseStacks A (Function.update S j xs) =
      Function.update (eraseStacks A S) j (xs.map Subtype.val) := by
  funext k
  by_cases h : k = j
  · subst k
    simp [eraseStacks]
  · simp [eraseStacks, Function.update_of_ne h]

theorem restrict_stepAux [DecidableEq K] (A : ∀ k, Set (Γ k))
    (q : Stmt Γ Λ σ) (h : ∀ k, pushed k q ⊆ A k) (v : σ)
    (S : ∀ k, List {a : Γ k // a ∈ A k}) :
    eraseCfg A (stepAux (restrictStmt A q h) v S) =
      stepAux q v (eraseStacks A S) := by
  induction q generalizing v S with
  | push j f q ih =>
    have htail : ∀ k, pushed k q ⊆ A k := fun k _ ha => h k (Or.inr ha)
    have hpush : f v ∈ A j := h j (Or.inl ⟨rfl, v, rfl⟩)
    have hi := ih htail v (Function.update S j (⟨f v, hpush⟩ :: S j))
    simpa only [restrictStmt, stepAux, erase_update, eraseStacks, List.map_cons] using hi
  | peek j f q ih =>
    have ht : ∀ k, pushed k q ⊆ A k := h
    have hh : ((S j).map Subtype.val).head? = (S j).head?.map Subtype.val := by
      cases S j <;> rfl
    simpa only [restrictStmt, stepAux, eraseStacks, hh] using
      ih ht (f v ((S j).head?.map Subtype.val)) S
  | pop j f q ih =>
    have ht : ∀ k, pushed k q ⊆ A k := h
    have hi := ih ht (f v ((S j).head?.map Subtype.val))
      (Function.update S j (S j).tail)
    have hh : ((S j).map Subtype.val).head? = (S j).head?.map Subtype.val := by
      cases S j <;> rfl
    have htail : (S j).tail.map Subtype.val = ((S j).map Subtype.val).tail := by
      cases S j <;> rfl
    simpa only [restrictStmt, stepAux, erase_update, eraseStacks, hh, htail] using hi
  | load f q ih =>
    have ht : ∀ k, pushed k q ⊆ A k := h
    simpa only [restrictStmt, stepAux] using ih ht (f v) S
  | branch f q₁ q₂ ih₁ ih₂ =>
    cases hf : f v with
    | false =>
      simpa only [restrictStmt, stepAux, hf, Bool.cond_false] using
        ih₂ (fun k _ ha => h k (Or.inr ha)) v S
    | true =>
      simpa only [restrictStmt, stepAux, hf, Bool.cond_true] using
        ih₁ (fun k _ ha => h k (Or.inl ha)) v S
  | goto f => rfl
  | halt => rfl


theorem finite_alphabet (tm : Turing.FinTM2) (k : tm.K) :
    Finite {a : tm.Γ k // a ∈ allowed tm k} := (allowed_finite tm k).to_subtype

theorem restrict_step (tm : Turing.FinTM2)
    (c : Cfg (fun k => {a : tm.Γ k // a ∈ allowed tm k}) tm.Λ tm.σ) :
    (Turing.TM2.step (restrictProgram tm) c).map (eraseCfg (allowed tm)) =
      Turing.TM2.step tm.m (eraseCfg (allowed tm) c) := by
  letI : DecidableEq tm.K := tm.kDecidableEq
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
    simp only [Turing.TM2.step, Option.map_some, eraseCfg, restrictProgram]
    exact congrArg some (restrict_stepAux (allowed tm) (tm.m l) _ v S)


/-- Mathematical finite-alphabet realization. Finite enumeration is chosen
classically here; this is not an executable reification of arbitrary functions. -/
noncomputable def normalized (tm : Turing.FinTM2) : Turing.FinTM2 where
  K := tm.K
  kDecidableEq := tm.kDecidableEq
  kFin := tm.kFin
  k₀ := tm.k₀
  k₁ := tm.k₁
  Γ := fun k => {a : tm.Γ k // a ∈ allowed tm k}
  Λ := tm.Λ
  main := tm.main
  ΛFin := tm.ΛFin
  σ := tm.σ
  initialState := tm.initialState
  σFin := tm.σFin
  Γk₀Fin := @Fintype.ofFinite _ (finite_alphabet tm tm.k₀)
  m := restrictProgram tm

end Shared.ComplexityBridge.TM2Symbols
