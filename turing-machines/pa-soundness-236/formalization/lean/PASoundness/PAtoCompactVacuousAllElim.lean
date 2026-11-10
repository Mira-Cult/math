import PASoundness.PAtoCompactScopedUnusedFull
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PeanoBetaCRTPrefixSubst

/-! The guarded universal-elimination axiom when the substituted variable
is absent from the source formula. No interpretation or value of the
substitution term is required in this case. -/
namespace PASoundness.PAtoCompactVacuousAllElim

set_option maxRecDepth 65536
set_option maxHeartbeats 0

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedVacuousAxiom PASoundness.PAtoCompactGuardedPropositional
open PASoundness.PAtoCompactScopedUnusedFull PASoundness.PAtoCompactScopedUnusedLevel
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactFreeVacuity

/-- Universal quantification of a formula unused at `x` implies the original
translation. Candidate inhabitation is proved in K. -/
noncomputable def allAt_implies_of_unused (φ : Peano.Formula) (x : Nat)
    (hx : x ∉ φ.freeVarFinset) :
    KDerivation (imp (code (FOL.allAt x φ)) (code φ)) := by
  let z := topName x φ
  have eqenv : (Fin.append (fun _ : Fin 1 => z) (Fin.elim0 : Fin 0 → Nat)) =
      Fin.snoc Fin.elim0 z := by
    funext i
    fin_cases i
    rfl
  have hscope := scoped_unused φ x z Fin.elim0 hx
  have halign : KDerivation (imp (topBody x φ).encode (code φ)) := by
    change KDerivation (imp
      (scopedFormula 1 (BoundedFormula.relabel (bindName x) φ) (Fin.snoc Fin.elim0 z)).encode
      (scopedFormula 0 φ Fin.elim0).encode)
    simpa only [Nat.add_zero, eqenv] using hscope.2
  have htop : z ∉ φ.freeVarFinset := topName_not_free φ x hx
  have hv : KDerivation (imp (code φ) (allCode z (code φ))) :=
    free_vacuity z (formula φ) (fun h => htop (formula_free_subset φ h))
  have hbody : KDerivation (imp
      (imp (domainAt (z+1) z).encode (topBody x φ).encode)
      (imp (domainAt (z+1) z).encode (code φ))) :=
    implicationCongr (CompactHilbertBasis.identity _) halign
  have hall := allCongr z hbody
  have he := candidate_exists (z+1) z (by omega)
  rw [code_allAt]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.existsElim hv
  · exact .mp (Context.head [] _) (.closed hall)
  · exact .closed he

/-- Every PA universal-elimination instance with an unused source variable
has finite K proof data, for an arbitrary substitution term. -/
noncomputable def allElim_of_unused (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∉ φ.freeVarFinset) :
    KDerivation (guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t))) := by
  rw [PASoundness.PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh φ x t hx]
  apply guardedOfUnconditional
  simpa only [code_imp] using allAt_implies_of_unused φ x hx

theorem allElim_of_unused_certificate (φ : Peano.Formula) (x : Nat) (t : Peano.Term)
    (hx : x ∉ φ.freeVarFinset) :
    theoremCode (certificate (allElim_of_unused φ x t hx)) =
      guardedCode ((FOL.allAt x φ).imp (FOL.substAt φ x t)) := certificate_correct _

end PASoundness.PAtoCompactVacuousAllElim

#print axioms PASoundness.PAtoCompactVacuousAllElim.allAt_implies_of_unused
#print axioms PASoundness.PAtoCompactVacuousAllElim.allElim_of_unused
#print axioms PASoundness.PAtoCompactVacuousAllElim.allElim_of_unused_certificate
