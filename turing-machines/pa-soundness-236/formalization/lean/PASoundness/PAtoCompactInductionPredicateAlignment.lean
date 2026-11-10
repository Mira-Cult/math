import PASoundness.PAtoCompactAllElimVariableFull

/-! A candidate induction predicate obtained by opening the PA formula at a
fresh active name. Named replacement at any lower name aligns with actual PA
variable substitution as finite K proofs; no semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionPredicateAlignment

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedAllImp
open PASoundness.PAtoCompactScopedActiveDownFull PASoundness.PAtoCompactScopedBindVariable
open PASoundness.PAtoCompactVacuousQuantifierFree

/-- If the active label t is above the translated universal's top label and
y<t, replacing t with y in the named induction predicate agrees in both K
proof directions with the actual PA formula φ[y/x]. The target y may already
be free in φ. -/
noncomputable def named_predicate_alignment (φ : Peano.Formula) (x t y : Nat)
    (htop : topName x φ < t) (hy : y < t) :
    KBoth (replace t y (scopeAt φ x t)) (formula (FOL.substAt φ x (.var y))) := by
  let B := allAtBody x φ
  have hfree : t ∉ B.freeVarFinset := by
    intro h
    have hl := free_lt_scopeBase (FOL.allAt x φ) Fin.elim0 t (by
      change t ∈ (allAtBody x φ).freeVarFinset
      exact h)
    change t < topName x φ at hl
    omega
  have henv : (rename t y ∘ Fin.snoc Fin.elim0 t) = Fin.snoc Fin.elim0 y := by
    funext i
    fin_cases i
    simp [rename]
  have h := scoped_active_down B (Fin.snoc Fin.elim0 t) (Fin.last 0) y
    (by simpa using hfree) (by simpa using hy)
  simp only [Fin.snoc_last, henv] at h
  have hs : KBoth (replace t y (scopeAt φ x t)) (scopeAt φ x y) := by
    simpa only [scopeAt, B, henv] using h
  have hb := formula_bind_variable φ x y
  exact ⟨compose hs.1 hb.2, compose hb.1 hs.2⟩

/-- The forward alignment may be weakened under any additional guard and
candidate premise, matching the pointwise PA-induction step interface. -/
noncomputable def named_predicate_under (φ : Peano.Formula) (x t y G C : Nat)
    (htop : topName x φ < t) (hy : y < t) :
    KDerivation (imp G (imp C
      (imp (replace t y (scopeAt φ x t)).encode (code (FOL.substAt φ x (.var y)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(replace t y (scopeAt φ x t)).encode,C,G]
  have hp : Context Γ (replace t y (scopeAt φ x t)).encode := Context.head _ _
  exact .mp hp (.closed ((named_predicate_alignment φ x t y htop hy).1))

theorem named_predicate_under_certificate (φ : Peano.Formula) (x t y G C : Nat)
    (htop : topName x φ < t) (hy : y < t) :
    theoremCode (certificate (named_predicate_under φ x t y G C htop hy)) =
      imp G (imp C (imp (replace t y (scopeAt φ x t)).encode
        (code (FOL.substAt φ x (.var y))))) := certificate_correct _

end PASoundness.PAtoCompactInductionPredicateAlignment

#print axioms PASoundness.PAtoCompactInductionPredicateAlignment.named_predicate_alignment
#print axioms PASoundness.PAtoCompactInductionPredicateAlignment.named_predicate_under
#print axioms PASoundness.PAtoCompactInductionPredicateAlignment.named_predicate_under_certificate
