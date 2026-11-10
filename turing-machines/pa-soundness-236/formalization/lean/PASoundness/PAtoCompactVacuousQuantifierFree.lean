import PASoundness.PAtoCompactVacuousEqualityAlignment

/-! Bidirectional K alignment and vacuous axiom for quantifier-free PA
formulas. Both sides share the same source free names; no semantic soundness
theorem is used. -/
namespace PASoundness.PAtoCompactVacuousQuantifierFree

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactScopedEqualityReplace PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuousAxiom
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactAllTermTransport

inductive QuantifierFree : Peano.Formula → Type
  | falsum : QuantifierFree .falsum
  | equal (t u : Peano.Term) : QuantifierFree (t.equal u)
  | imp {φ ψ : Peano.Formula} : QuantifierFree φ → QuantifierFree ψ → QuantifierFree (φ.imp ψ)

def KBoth (a b : Formula) : Type :=
  KDerivation (imp a.encode b.encode) × KDerivation (imp b.encode a.encode)

/-- Equality frames at arbitrary bases have finite K implications in both
directions when all occurring source names are below both bases. The shared
high frame handles overlapping or equal bases and aliased source names. -/
noncomputable def equalityFrame_base_transport {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (b c : Nat)
    (htb : ∀ a ∈ t.varFinset, v a < b) (hub : ∀ a ∈ u.varFinset, v a < b)
    (htc : ∀ a ∈ t.varFinset, v a < c) (huc : ∀ a ∈ u.varFinset, v a < c) :
    KBoth (equalityFrame v t u b) (equalityFrame v t u c) := by
  let d := max b c + 10
  have pairHigh (a : Nat) (had : a + 1 < d)
      (hta : ∀ k ∈ t.varFinset, v k < a) (hua : ∀ k ∈ u.varFinset, v k < a) :
      KBoth (equalityFrame v t u a) (equalityFrame v t u d) := by
    have ht := termGraph_base_transport v t (a+2) (d+2) a (by omega) (by omega)
      (by intro k hk; have := hta k hk; omega)
      (by intro k hk; have := hta k hk; omega)
    have hu := termGraph_base_transport v u (a+2+termCost t) (d+2+termCost t) (a+1)
      (by omega) (by omega)
      (by intro k hk; have := hua k hk; omega)
      (by intro k hk; have := hua k hk; omega)
    exact ⟨equalityFrame_high_forward v t u a d had hta hua ht.1 hu.1,
      equalityFrame_high_backward v t u a d had hta hua ht.2 hu.2⟩
  have hb := pairHigh b (by dsimp [d]; omega) htb hub
  have hc := pairHigh c (by dsimp [d]; omega) htc huc
  exact ⟨compose hb.1 hc.2, compose hc.1 hb.2⟩

/-- The equality-atom body, when the removed source variable is absent and
the common enclosing binder exceeds every source free name. -/
theorem atom_scope_shape (t u : Peano.Term) (x z : Nat)
    (hx : x ∉ (t.equal u).freeVarFinset)
    (hz : ∀ a ∈ (t.equal u).freeVarFinset, a < z) :
    scopedFormula 1 (allAtBody x (t.equal u)) (Fin.snoc Fin.elim0 z) =
      equalityFrame id t u (z + 1) := by
  have ht := (eq_not t u x hx).1
  have hu := (eq_not t u x hx).2
  unfold allAtBody
  simp only [Term.equal, Term.bdEqual, BoundedFormula.relabel, BoundedFormula.mapTermRel]
  rw [fresh_term t x ht, fresh_term u x hu]
  rw [scoped_equal_frame, frame_relabel]
  have hb : scopeBase (.equal (t.relabel Sum.inl) (u.relabel Sum.inl))
      (Fin.snoc Fin.elim0 z) = z + 1 := by
    unfold scopeBase
    have hsup : ((.equal (t.relabel Sum.inl) (u.relabel Sum.inl) :
        Peano.language.BoundedFormula Nat 1).freeVarFinset ∪
          Finset.univ.image (Fin.snoc Fin.elim0 z)).sup id = z := by
      apply le_antisymm
      · apply Finset.sup_le
        intro a ha
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ha
        rcases ha with ha | ⟨i, hi⟩
        · have hfree : a ∈ (t.equal u).freeVarFinset := by
            simpa [Term.equal, Term.bdEqual, BoundedFormula.freeVarFinset] using ha
          exact Nat.le_of_lt (hz a hfree)
        · fin_cases i
          simpa [Fin.snoc] using (le_of_eq hi.symm)
      · apply Finset.le_sup (f := id)
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp [Fin.snoc]⟩
    rw [hsup]
  rw [hb]
  rfl

/-- Abstract local interface while assembling the common-label induction.
The two directions are actual finite K proof data. -/
structure FrameTransport where
  transport : ∀ (t u : Peano.Term) (b c : Nat),
    (∀ a ∈ (t.equal u).freeVarFinset, a < b) →
    (∀ a ∈ (t.equal u).freeVarFinset, a < c) →
    KBoth (equalityFrame id t u b) (equalityFrame id t u c)

/-- Every required equality-frame instance is supplied by all-term transport. -/
noncomputable def frameTransport : FrameTransport where
  transport := by
    intro t u b c hb hc
    apply equalityFrame_base_transport id t u b c
    · intro a ha; exact hb a (by simp [eq_free, ha])
    · intro a ha; exact hb a (by simp [eq_free, ha])
    · intro a ha; exact hc a (by simp [eq_free, ha])
    · intro a ha; exact hc a (by simp [eq_free, ha])

noncomputable def scoped_align (H : FrameTransport) {φ : Peano.Formula}
    (h : QuantifierFree φ) (x z : Nat) (hx : x ∉ φ.freeVarFinset)
    (hz : ∀ a ∈ φ.freeVarFinset, a < z) :
    KBoth (formula φ) (scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 z)) := by
  induction h with
  | falsum =>
      exact ⟨CompactHilbertBasis.identity 1, CompactHilbertBasis.identity 1⟩
  | equal t u =>
      rw [original_shape, atom_scope_shape t u x z hx hz]
      exact H.transport t u (scopeBase (t.equal u) Fin.elim0) (z + 1)
        (fun a ha => free_lt_scopeBase _ _ a ha) (fun a ha => by have := hz a ha; omega)
  | @imp φ ψ hφ hψ ihφ ihψ =>
      have hxφ : x ∉ φ.freeVarFinset := by
        intro h; apply hx; simp [BoundedFormula.freeVarFinset, h]
      have hxψ : x ∉ ψ.freeVarFinset := by
        intro h; apply hx; simp [BoundedFormula.freeVarFinset, h]
      have hzφ : ∀ a ∈ φ.freeVarFinset, a < z := by
        intro a h; exact hz a (by simp [BoundedFormula.freeVarFinset, h])
      have hzψ : ∀ a ∈ ψ.freeVarFinset, a < z := by
        intro a h; exact hz a (by simp [BoundedFormula.freeVarFinset, h])
      have ha := ihφ hxφ hzφ
      have hb := ihψ hxψ hzψ
      change KBoth (.imp (formula φ) (formula ψ))
        (.imp (scopedFormula 1 (allAtBody x φ) (Fin.snoc Fin.elim0 z))
          (scopedFormula 1 (allAtBody x ψ) (Fin.snoc Fin.elim0 z)))
      exact ⟨implicationCongr ha.2 hb.1, implicationCongr ha.1 hb.2⟩

/-- The scoped alignment yields the guarded vacuous axiom whenever the
explicit equality-frame transport has been supplied. -/
noncomputable def vacuous_with_transport (H : FrameTransport) (φ : Peano.Formula)
    (h : QuantifierFree φ) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ))) := by
  apply vacuous_of_body_alignment φ x hx
  have hz : ∀ a ∈ φ.freeVarFinset, a < topName x φ := by
    intro a ha
    apply free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 a
    simpa [PASoundness.SyntaxTransport.allAt_freeVars, hx] using ha
  exact (scoped_align H h x (topName x φ) hx hz).1

/-- The guarded vacuous PA axiom for every quantifier-free formula. -/
noncomputable def vacuous (φ : Peano.Formula) (h : QuantifierFree φ)
    (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    KDerivation (guardedCode (φ.imp (FOL.allAt x φ))) :=
  vacuous_with_transport frameTransport φ h x hx

theorem vacuous_certificate (φ : Peano.Formula) (h : QuantifierFree φ)
    (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    theoremCode (certificate (vacuous φ h x hx)) =
      guardedCode (φ.imp (FOL.allAt x φ)) := certificate_correct _

end PASoundness.PAtoCompactVacuousQuantifierFree

#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.equalityFrame_base_transport
#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.atom_scope_shape
#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.frameTransport
#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.scoped_align
#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.vacuous
#print axioms PASoundness.PAtoCompactVacuousQuantifierFree.vacuous_certificate
