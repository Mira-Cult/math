import PASoundness.PAtoCompactGuardedAllImpAlignment
import PASoundness.PAtoCompactDirectGeneralization
import PASoundness.PAtoCompactFreeVacuity

/-! Finite K proof assembly for closing a pointwise induction conclusion.
This constructor consumes explicit proof data for the pointwise conclusion,
domain and body alignments, and vacuity. It does not prove those inputs or a
PA induction axiom. -/
namespace PASoundness.PAtoCompactInductionConcludeGeneralize

open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactGuardedBridge PASoundness.PAtoCompactGuardedVacuity PASoundness.PAtoCompactFreeVacuity
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactGuardedGeneralizationAlignment
open PASoundness.PAtoCompactGuardedAllImpAlignment PASoundness.PAtoCompactDirectGeneralization

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Universally quantify an aligned pointwise candidate-domain conclusion,
then align that universal with the literal translation of the PA universal.
All hypotheses are finite K proof data; `z` must also be fresh for the
existing translated universal body. -/
noncomputable def close_induction_conclusion
    (φ : Peano.Formula) (x z G A B D F : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (vG : KDerivation (imp G (allCode z G)))
    (vA : KDerivation (imp A (allCode z A)))
    (vB : KDerivation (imp B (allCode z B)))
    (hpoint : KDerivation (imp G (imp A (imp B (imp D F)))))
    (hdom : KDerivation (imp (domainAt (z+1) z).encode D))
    (hbody : KDerivation (imp F (scopeAt φ x z).encode)) :
    KDerivation (imp G (imp A (imp B (code (FOL.allAt x φ))))) := by
  let P := (domainAt (z+1) z).encode
  let Q := (scopeAt φ x z).encode
  let Γ := [B,A,G]
  have hlocal : Context Γ (imp P Q) := by
    apply Context.deduction
    let Δ := P :: Γ
    have hp : Context Δ P := Context.head Γ P
    have hg : Context Δ G := .hypothesis (by simp [Δ, Γ])
    have ha : Context Δ A := .hypothesis (by simp [Δ, Γ])
    have hb : Context Δ B := .hypothesis (by simp [Δ, Γ])
    have hd : Context Δ D := .mp hp (.closed hdom)
    have hf : Context Δ F := .mp hd (.mp hb (.mp ha (.mp hg (.closed hpoint))))
    exact .mp hf (.closed hbody)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode z h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hb : h = B
    · subst h; exact vB
    · by_cases ha : h = A
      · subst h; exact vA
      · have hg : h = G := (hh.resolve_left hb).resolve_left ha
        subst h; exact vG
  have hall : Context Γ (allCode z (imp P Q)) := Context.generalize z hv hlocal
  have halign := (align_at φ x z hgt hz).2
  have hc : Context Γ (code (FOL.allAt x φ)) := by
    apply Context.mp _ (.closed halign)
    simpa only [commonAll, scopeAt, P, Q, Formula.encode] using hall
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hc

theorem close_induction_conclusion_certificate
    (φ : Peano.Formula) (x z G A B D F : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (vG : KDerivation (imp G (allCode z G)))
    (vA : KDerivation (imp A (allCode z A)))
    (vB : KDerivation (imp B (allCode z B)))
    (hpoint : KDerivation (imp G (imp A (imp B (imp D F)))))
    (hdom : KDerivation (imp (domainAt (z+1) z).encode D))
    (hbody : KDerivation (imp F (scopeAt φ x z).encode)) :
    theoremCode (certificate (close_induction_conclusion φ x z G A B D F hgt hz
      vG vA vB hpoint hdom hbody)) = imp G (imp A (imp B (code (FOL.allAt x φ)))) :=
  certificate_correct _


/-- Specialize the three vacuity premises to the actual PA induction guard,
base and universally quantified step. Source freshness alone suffices even if
the name is bound within one of the translated formulas. The pointwise,
domain and body K alignments remain explicit inputs. -/
noncomputable def close_pa_induction_conclusion
    (φ : Peano.Formula) (x z D F : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (hfresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (hpoint : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (code (FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))))
          (imp D F)))))
    (hdom : KDerivation (imp (domainAt (z+1) z).encode D))
    (hbody : KDerivation (imp F (scopeAt φ x z).encode)) :
    KDerivation (guardedCode (Peano.inductionAxiom φ x)) := by
  let I := Peano.inductionAxiom φ x
  let P := FOL.substAt φ x Peano.zero
  let S := FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))
  have hp : z ∉ P.freeVarFinset := by
    intro h
    apply hfresh
    change z ∈ (P.imp (S.imp (FOL.allAt x φ))).freeVarFinset
    exact Finset.mem_union_left _ h
  have hs : z ∉ S.freeVarFinset := by
    intro h
    apply hfresh
    change z ∈ (P.imp (S.imp (FOL.allAt x φ))).freeVarFinset
    exact Finset.mem_union_right _ (Finset.mem_union_left _ h)
  have hvG := guardFormula_vacuity I z hfresh
  have hvP := translated_vacuity P z hp
  have hvS := translated_vacuity S z hs
  have hh := close_induction_conclusion φ x z (guardFormula I).encode (code P) (code S) D F
    hgt hz hvG hvP hvS hpoint hdom hbody
  simpa only [guardedCode, Peano.inductionAxiom, code_imp, I, P, S] using hh

theorem close_pa_induction_conclusion_certificate
    (φ : Peano.Formula) (x z D F : Nat)
    (hgt : topName x φ < z) (hz : z ∉ (originalChild φ x).names)
    (hfresh : z ∉ (Peano.inductionAxiom φ x).freeVarFinset)
    (hpoint : KDerivation (imp (guardFormula (Peano.inductionAxiom φ x)).encode
      (imp (code (FOL.substAt φ x Peano.zero))
        (imp (code (FOL.allAt x (φ.imp (FOL.substAt φ x (Peano.succ (.var x))))))
          (imp D F)))))
    (hdom : KDerivation (imp (domainAt (z+1) z).encode D))
    (hbody : KDerivation (imp F (scopeAt φ x z).encode)) :
    theoremCode (certificate (close_pa_induction_conclusion φ x z D F hgt hz hfresh
      hpoint hdom hbody)) = guardedCode (Peano.inductionAxiom φ x) :=
  certificate_correct _

end PASoundness.PAtoCompactInductionConcludeGeneralize

#print axioms PASoundness.PAtoCompactInductionConcludeGeneralize.close_induction_conclusion
#print axioms PASoundness.PAtoCompactInductionConcludeGeneralize.close_induction_conclusion_certificate

#print axioms PASoundness.PAtoCompactInductionConcludeGeneralize.close_pa_induction_conclusion
#print axioms PASoundness.PAtoCompactInductionConcludeGeneralize.close_pa_induction_conclusion_certificate
