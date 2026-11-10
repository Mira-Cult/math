import PASoundness.PAtoCompactScopedActiveAll

/-! Conditional universal step for active-name replacement by a lower name.
The target may already be free or occur elsewhere in the active environment. -/
namespace PASoundness.PAtoCompactScopedActiveDownUniversal

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactScopedActiveAll
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactVacuousQuantifierFree

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The low-target structural induction hypothesis, allowing aliasing. -/
def DownIH {n : Nat} (φ : Peano.language.BoundedFormula Nat n) : Type :=
  ∀ (bound : Fin n → Nat) (i : Fin n) (w : Nat),
    bound i ∉ φ.freeVarFinset → w < bound i →
    KBoth (replace (bound i) w (scopedFormula n φ bound))
      (scopedFormula n φ (rename (bound i) w ∘ bound))

/-- A low-target replacement commutes with a universal node up to finite K
proof, provided the corresponding child alignment has been constructed. -/
noncomputable def universal_down_step {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (ih : DownIH body)
    (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hfree : bound i ∉ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset)
    (hlt : w < bound i) :
    KBoth (replace (bound i) w (scopedFormula n (.all body) bound))
      (scopedFormula n (.all body) (rename (bound i) w ∘ bound)) := by
  let a := bound i
  let p := scopeBase (.all body) bound
  let new := rename a w ∘ bound
  let q := scopeBase (.all body) new
  let F := scopedFormula (n+1) body (Fin.snoc bound p)
  let M := scopedFormula (n+1) body (Fin.snoc new p)
  let G := scopedFormula (n+1) body (Fin.snoc new q)
  let z := max p (max q (max a (max w ((F.names ∪ M.names ∪ G.names).sup id)))) + 1
  have hp : a < p := bound_lt_scopeBase (.all body) bound i
  have hfa : a ∉ body.freeVarFinset := by simpa using hfree
  have hfp : p ∉ body.freeVarFinset := by
    intro hh
    have hh' : p ∈ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset := by simpa using hh
    have := free_lt_scopeBase (.all body) bound p hh'
    dsimp [p] at *
    omega
  have hfq : q ∉ body.freeVarFinset := by
    intro hh
    have hh' : q ∈ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset := by simpa using hh
    have := free_lt_scopeBase (.all body) new q hh'
    dsimp [q] at *
    omega
  have hpz : p < z := by dsimp [z]; omega
  have hqz : q < z := by dsimp [z]; omega
  have haz : a < z := by dsimp [z]; omega
  have hwz : w < z := by dsimp [z]; omega
  have hzF : z ∉ F.names := by
    intro hh
    have hl : z ≤ (F.names ∪ M.names ∪ G.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_left _ (Finset.mem_union_left _ hh))
    dsimp [z] at hl; omega
  have hzM : z ∉ M.names := by
    intro hh
    have hl : z ≤ (F.names ∪ M.names ∪ G.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_left _ (Finset.mem_union_right _ hh))
    dsimp [z] at hl; omega
  have hzG : z ∉ G.names := by
    intro hh
    have hl : z ≤ (F.names ∪ M.names ∪ G.names).sup id := Finset.le_sup (f := id) (Finset.mem_union_right _ hh)
    dsimp [z] at hl; omega
  have hnew : ∀ j, new j ≠ p := by
    intro j
    have hj := bound_lt_scopeBase (.all body) bound j
    dsimp [new, rename, a, p] at *
    split_ifs <;> omega
  have hnewq : ∀ j, new j ≠ q := fun j => Nat.ne_of_lt (bound_lt_scopeBase (.all body) new j)
  have h1 := ih (Fin.snoc bound p) (Fin.castSucc i) w (by simpa [a] using hfa)
    (by simpa [a] using hlt)
  have env1 : (rename a w ∘ Fin.snoc bound p) = Fin.snoc new p :=
    rename_snoc_old bound a w p (by omega)
  have pair1 : KBoth (replace a w F) M := by simpa [F, M, a, env1] using h1
  have hFp : p ∉ F.binders := by
    have hh := active_not_binder body (Fin.snoc bound p) (Fin.last n)
    simpa [F] using hh
  have hMp : p ∉ M.binders := by
    have hh := active_not_binder body (Fin.snoc new p) (Fin.last n)
    simpa [M] using hh
  have hzFb : z ∉ (replace a w F).binders := by
    simpa [replace_binders] using fun h => hzF (F.binders_subset_names h)
  have hzMb : z ∉ M.binders := fun h => hzM (M.binders_subset_names h)
  have hpFb : p ∉ (replace a w F).binders := by simpa [replace_binders] using hFp
  have pair1' := replace_implications p z (replace a w F) M hpFb hMp hzFb hzMb pair1.1 pair1.2
  have h2 := scoped_active_replace body (Fin.snoc new p) (Fin.last n) z
    (by simpa using hfp) (by simpa using hpz) (by simpa [M] using hzM)
  have env2 : (rename p z ∘ Fin.snoc new p) = Fin.snoc new z := rename_snoc_nonhit new p z hnew
  have pair2 : KBoth (replace p z M) (scopedFormula (n+1) body (Fin.snoc new z)) := by simpa [M, env2] using h2
  have h3 := scoped_active_replace body (Fin.snoc new q) (Fin.last n) z
    (by simpa using hfq) (by simpa using hqz) (by simpa [G] using hzG)
  have env3 : (rename q z ∘ Fin.snoc new q) = Fin.snoc new z := rename_snoc_nonhit new q z hnewq
  have pair3 : KBoth (replace q z G) (scopedFormula (n+1) body (Fin.snoc new z)) := by simpa [G, env3] using h3
  have child : KBoth (replace p z (replace a w F)) (replace q z G) :=
    ⟨compose (compose pair1'.1 pair2.1) pair3.2, compose pair3.1 (compose pair2.2 pair1'.2)⟩
  have hzFw : z ∉ (replace a w F).names := by
    intro hh
    have hh' := PASoundness.CompactNamed.replace_names_subset a w F hh
    simp only [Finset.mem_insert] at hh'
    rcases hh' with he | he
    · omega
    · exact hzF he
  have hGq : q ∉ G.binders := by
    have hh := active_not_binder body (Fin.snoc new q) (Fin.last n)
    simpa [G] using hh
  have result := raw_align p q z (z+1) (replace a w F) G hpz hqz (by omega) hpFb hGq hzFw hzG child
  have hguard : replace a w (domainAt (p+1) p) = domainAt (p+1) p :=
    replace_other_domain_guard (p+1) p a w (by omega) (by omega)
  change KBoth (Formula.all p (.imp (replace a w (domainAt (p+1) p)) (replace a w F)))
    (rawGuard q G)
  rw [hguard]
  exact result

end PASoundness.PAtoCompactScopedActiveDownUniversal

#print axioms PASoundness.PAtoCompactScopedActiveDownUniversal.universal_down_step
