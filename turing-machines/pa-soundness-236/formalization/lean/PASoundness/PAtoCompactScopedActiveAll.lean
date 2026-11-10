import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactVacuousUniversalFresh

/-! Active-name replacement for arbitrary scoped PA formulas, including nested universals. -/

namespace PASoundness.PAtoCompactScopedActiveAll
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactHilbertBasis
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactVacuousUniversalFresh
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactTemplateBlockShift

def rawGuard (p : Nat) (f : Formula) : Formula := .all p (.imp (domainAt (p+1) p) f)

def rawRebased (p H : Nat) (f : Formula) : Formula := .all p (.imp (domainAt H p) f)

def raw_rebase (p H : Nat) (f : Formula) (hp : p < H + 32) : KBoth (rawGuard p f) (rawRebased p H f) := by
  have oldnew := domainAt_transport (p+1) H p (by omega) hp
  have newold := domainAt_transport H (p+1) p hp (by omega)
  exact ⟨allCongr p (implicationCongr newold (identity f.encode)),
    allCongr p (implicationCongr oldnew (identity f.encode))⟩

def raw_high_alpha (p z H : Nat) (f : Formula) (hpH : p < H) (hpz : p ≠ z)
    (hp : p ∉ f.binders) (hz : z ∉ (.imp (domainAt H p) f : Formula).names) :
    ProofEquiv (rawRebased p H f) (.all z (.imp (domainAt H z) (replace p z f))) := by
  have hn : p ∉ (.imp (domainAt H p) f : Formula).binders := by
    simp only [Formula.binders, Finset.mem_union, not_or]
    constructor
    · intro h
      have hh := PAtoCompactTermGraphBinderRange.domainAt_private H p p h
      omega
    · exact hp
  have h := ProofEquiv.alphaAll p z (.imp (domainAt H p) f) hpz hn hz
  simpa only [rawRebased, replace, replace_domainAt H p z hpH] using h

def raw_align (p q z H : Nat) (f g : Formula)
    (hpz : p < z) (hqz : q < z) (hzH : z < H)
    (hp : p ∉ f.binders) (hq : q ∉ g.binders)
    (hzf : z ∉ f.names) (hzg : z ∉ g.names)
    (child : KBoth (replace p z f) (replace q z g)) : KBoth (rawGuard p f) (rawGuard q g) := by
  have hpH : p < H := by omega
  have hqH : q < H := by omega
  have hpf : z ∉ (.imp (domainAt H p) f : Formula).names := by
    simp only [Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names H p z (by omega) (by omega), hzf⟩
  have hqg : z ∉ (.imp (domainAt H q) g : Formula).names := by
    simp only [Formula.names, Finset.mem_union, not_or]
    exact ⟨low_name_not_domain_names H q z (by omega) (by omega), hzg⟩
  have ra := raw_rebase p H f (by omega)
  have rb := raw_rebase q H g (by omega)
  have aa := raw_high_alpha p z H f hpH (by omega) hp hpf
  have ba := raw_high_alpha q z H g hqH (by omega) hq hqg
  have hf := allCongr z (implicationCongr (identity (domainAt H z).encode) child.1)
  have hr := allCongr z (implicationCongr (identity (domainAt H z).encode) child.2)
  exact ⟨compose ra.1 (compose aa.forward (compose hf (compose ba.backward rb.2))),
    compose rb.1 (compose ba.forward (compose hr (compose aa.backward ra.2)))⟩

#print axioms PASoundness.PAtoCompactScopedActiveAll.raw_align
end PASoundness.PAtoCompactScopedActiveAll


namespace PASoundness.PAtoCompactScopedActiveAll
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTemplateBlockShift

/-- Replacing a name below a guard's private block changes only the free
operand; target freshness is a separate quantifier-side obligation. -/
theorem replace_domain_guard (base operand a w : Nat) (ha : a < base) :
    replace a w (domainAt base operand) = domainAt base (rename a w operand) := by
  have hb : a ∉ (domainAt base operand).binders := by
    intro h
    have h' := domainAt_private base operand a h
    omega
  rw [← PAtoCompactAlphaMapOne.map_eq_replace a w _ hb]
  apply domainAt_shift
  intro i hi
  simp [rename, show base + i ≠ a by omega]

theorem replace_other_domain_guard (base operand a w : Nat)
    (ha : a < base) (hne : operand ≠ a) :
    replace a w (domainAt base operand) = domainAt base operand := by
  simpa [rename, hne] using replace_domain_guard base operand a w ha

end PASoundness.PAtoCompactScopedActiveAll

#print axioms PASoundness.PAtoCompactScopedActiveAll.replace_domain_guard
#print axioms PASoundness.PAtoCompactScopedActiveAll.replace_other_domain_guard

namespace PASoundness.PAtoCompactScopedActiveAll
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactFormulaTranslation

theorem rename_snoc_nonhit {n : Nat} (bound : Fin n → Nat) (p z : Nat)
    (hp : ∀ i, bound i ≠ p) :
    (rename p z ∘ Fin.snoc bound p) = Fin.snoc bound z := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [rename]
  · simp [rename, hp i]

theorem rename_snoc_old {n : Nat} (bound : Fin n → Nat) (a w p : Nat)
    (hpa : p ≠ a) :
    (rename a w ∘ Fin.snoc bound p) = Fin.snoc (rename a w ∘ bound) p := by
  funext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [Function.comp_def, rename, hpa]
  · simp [Function.comp_def]

theorem updated_bound_avoids_scope {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (bound : Fin n → Nat)
    (a w : Nat) (hwa : w ≠ scopeBase (.all body) bound) :
    ∀ j, rename a w (bound j) ≠ scopeBase (.all body) bound := by
  intro j
  have hp := bound_lt_scopeBase (.all body) bound j
  unfold rename
  split_ifs <;> omega

end PASoundness.PAtoCompactScopedActiveAll
#print axioms PASoundness.PAtoCompactScopedActiveAll.rename_snoc_nonhit
#print axioms PASoundness.PAtoCompactScopedActiveAll.rename_snoc_old
#print axioms PASoundness.PAtoCompactScopedActiveAll.updated_bound_avoids_scope

namespace PASoundness.PAtoCompactScopedActiveAll
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactVacuousQuantifierFree

abbrev ActiveIH {n : Nat} (φ : Peano.language.BoundedFormula Nat n) :=
  ∀ (bound : Fin n → Nat) (i : Fin n) (w : Nat),
    bound i ∉ φ.freeVarFinset → bound i < w → w ∉ (scopedFormula n φ bound).names →
    KBoth (replace (bound i) w (scopedFormula n φ bound))
      (scopedFormula n φ (rename (bound i) w ∘ bound))

noncomputable def universal_active_step {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1)) (ih : ActiveIH body)
    (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hfree : bound i ∉ (.all body : Peano.language.BoundedFormula Nat n).freeVarFinset)
    (hgt : bound i < w) (hw : w ∉ (scopedFormula n (.all body) bound).names) :
    KBoth (replace (bound i) w (scopedFormula n (.all body) bound))
      (scopedFormula n (.all body) (rename (bound i) w ∘ bound)) := by
  let a := bound i
  let p := scopeBase (.all body) bound
  let new := rename a w ∘ bound
  let q := scopeBase (.all body) new
  let F := scopedFormula (n+1) body (Fin.snoc bound p)
  let M := scopedFormula (n+1) body (Fin.snoc new p)
  let G := scopedFormula (n+1) body (Fin.snoc new q)
  let z := max p (max q (max w ((F.names ∪ M.names ∪ G.names).sup id))) + 1
  have hp : a < p := bound_lt_scopeBase (.all body) bound i
  have hwne : w ≠ p := by
    intro he
    apply hw
    change w ∈ (Formula.all p (.imp (domainAt (p+1) p) F)).names
    simp [Formula.names, he]
  have hwF : w ∉ F.names := by
    intro hh
    apply hw
    change w ∈ (Formula.all p (.imp (domainAt (p+1) p) F)).names
    simp [Formula.names, hh]
  have hq : w < q := by
    have hh := bound_lt_scopeBase (.all body) new i
    simpa [new, a, rename] using hh
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
  have hold : ∀ j, bound j ≠ p := fun j => Nat.ne_of_lt (bound_lt_scopeBase (.all body) bound j)
  have hnew : ∀ j, new j ≠ p := updated_bound_avoids_scope body bound a w hwne
  have hnewq : ∀ j, new j ≠ q := fun j => Nat.ne_of_lt (bound_lt_scopeBase (.all body) new j)
  have h1 := ih (Fin.snoc bound p) (Fin.castSucc i) w (by simpa [a] using hfa)
    (by simpa [a] using hgt) (by simpa [F] using hwF)
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
  have h2 := ih (Fin.snoc new p) (Fin.last n) z (by simpa using hfp) (by simpa using hpz) (by simpa [M] using hzM)
  have env2 : (rename p z ∘ Fin.snoc new p) = Fin.snoc new z := rename_snoc_nonhit new p z hnew
  have pair2 : KBoth (replace p z M) (scopedFormula (n+1) body (Fin.snoc new z)) := by simpa [M, env2] using h2
  have h3 := ih (Fin.snoc new q) (Fin.last n) z (by simpa using hfq) (by simpa using hqz) (by simpa [G] using hzG)
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

#print axioms PASoundness.PAtoCompactScopedActiveAll.universal_active_step
end PASoundness.PAtoCompactScopedActiveAll

namespace PASoundness.PAtoCompactScopedActiveAll
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.CompactHilbertBasis

/-- Active-bound name replacement for arbitrary PA scoped formulas, including
nested universals, under the explicit free-name and fresh-target hypotheses. -/
noncomputable def scoped_active_replace {n : Nat} (φ : Peano.language.BoundedFormula Nat n) : ActiveIH φ := by
  induction φ with
  | falsum =>
      intro bound i w hfree hgt hw
      exact ⟨identity 1, identity 1⟩
  | equal t u =>
      intro bound i w hfree hgt hw
      exact scoped_equal_active_replace t u bound i w hfree hgt hw
  | rel r ts => exact nomatch r
  | imp a b iha ihb =>
      intro bound i w hfree hgt hw
      have hfa : bound i ∉ a.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hfb : bound i ∉ b.freeVarFinset := by
        intro h; apply hfree; simp [BoundedFormula.freeVarFinset, h]
      have hwa : w ∉ (scopedFormula _ a bound).names := by
        intro h; apply hw; simp [scopedFormula, Formula.names, h]
      have hwb : w ∉ (scopedFormula _ b bound).names := by
        intro h; apply hw; simp [scopedFormula, Formula.names, h]
      have aa := iha bound i w hfa hgt hwa
      have bb := ihb bound i w hfb hgt hwb
      change KBoth (.imp (replace (bound i) w (scopedFormula _ a bound))
          (replace (bound i) w (scopedFormula _ b bound)))
        (.imp (scopedFormula _ a (rename (bound i) w ∘ bound))
          (scopedFormula _ b (rename (bound i) w ∘ bound)))
      exact ⟨implicationCongr aa.2 bb.1, implicationCongr aa.1 bb.2⟩
  | all body ih =>
      exact universal_active_step body ih

theorem scoped_active_replace_forward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hf : bound i ∉ φ.freeVarFinset) (hg : bound i < w)
    (hw : w ∉ (scopedFormula n φ bound).names) :
    theoremCode (certificate ((scoped_active_replace φ bound i w hf hg hw).1)) =
      imp (replace (bound i) w (scopedFormula n φ bound)).encode
        (scopedFormula n φ (rename (bound i) w ∘ bound)).encode := certificate_correct _

theorem scoped_active_replace_backward_certificate {n : Nat}
    (φ : Peano.language.BoundedFormula Nat n) (bound : Fin n → Nat) (i : Fin n) (w : Nat)
    (hf : bound i ∉ φ.freeVarFinset) (hg : bound i < w)
    (hw : w ∉ (scopedFormula n φ bound).names) :
    theoremCode (certificate ((scoped_active_replace φ bound i w hf hg hw).2)) =
      imp (scopedFormula n φ (rename (bound i) w ∘ bound)).encode
        (replace (bound i) w (scopedFormula n φ bound)).encode := certificate_correct _

#print axioms PASoundness.PAtoCompactScopedActiveAll.scoped_active_replace
#print axioms PASoundness.PAtoCompactScopedActiveAll.scoped_active_replace_forward_certificate
#print axioms PASoundness.PAtoCompactScopedActiveAll.scoped_active_replace_backward_certificate
end PASoundness.PAtoCompactScopedActiveAll
