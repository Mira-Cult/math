import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactDerivations

/-! Quantifier congruence under a retained hypothesis. The hypothesis is
explicitly required to admit generalization at the selected binder; this file
does not provide the graph-substitution induction hypothesis. -/
namespace PASoundness.PAtoCompactGuardedAllCongruence

open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactNamed PASoundness.PAtoCompactFreeVacuity

/-- Lift a K implication under one retained hypothesis through a universal.
The input vacuity proof is indispensable: no restriction is imposed on the
two matrix codes or their variable occurrences. -/
def all_congr_of_vacuity (z H A B : Nat)
    (vacuity : KDerivation (imp H (allCode z H)))
    (step : KDerivation (imp H (imp A B))) :
    KDerivation (imp H (imp (allCode z A) (allCode z B))) := by
  apply Context.closeEmpty
  apply Context.deduction
  have hH : Context [H] H := Context.head [] H
  have hstep : Context [H] (imp A B) := .mp hH (.closed step)
  have hall : Context [H] (allCode z (imp A B)) :=
    generalizeOne z vacuity hstep
  apply Context.deduction
  exact Context.allMP (Context.head [H] (allCode z A))
    (Context.under hall (allCode z A))

/-- Lift both directions of a graph-conditioned matrix alignment. -/
def all_both_of_vacuity (z H A B : Nat)
    (vacuity : KDerivation (imp H (allCode z H)))
    (forward : KDerivation (imp H (imp A B)))
    (backward : KDerivation (imp H (imp B A))) :
    KDerivation (imp H (imp (allCode z A) (allCode z B))) ×
      KDerivation (imp H (imp (allCode z B) (allCode z A))) :=
  ⟨all_congr_of_vacuity z H A B vacuity forward,
    all_congr_of_vacuity z H B A vacuity backward⟩

/-- Syntactic free-name absence constructs the required vacuity proof. -/
def all_both_of_free (z : Nat) (H : Formula) (A B : Nat)
    (fresh : z ∉ H.free)
    (forward : KDerivation (imp H.encode (imp A B)))
    (backward : KDerivation (imp H.encode (imp B A))) :
    KDerivation (imp H.encode (imp (allCode z A) (allCode z B))) ×
      KDerivation (imp H.encode (imp (allCode z B) (allCode z A))) :=
  all_both_of_vacuity z H.encode A B (free_vacuity z H fresh) forward backward

/-- Lift a body step that additionally consumes the candidate condition D.
D stays inside the universal, and may itself mention the bound name. -/
def guarded_all_congr (z H D A B : Nat)
    (vacuity : KDerivation (imp H (allCode z H)))
    (step : KDerivation (imp H (imp D (imp A B)))) :
    KDerivation (imp H (imp (allCode z (imp D A)) (allCode z (imp D B)))) := by
  apply all_congr_of_vacuity z H (imp D A) (imp D B) vacuity
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [D, imp D A, H]
  have hD : Context Γ D := Context.head _ _
  have hDA : Context Γ (imp D A) := .hypothesis (by simp [Γ])
  have hH : Context Γ H := .hypothesis (by simp [Γ])
  exact .mp (.mp hD hDA) (.mp hD (.mp hH (.closed step)))

/-- Both directions with the same retained hypothesis and candidate guard. -/
def guarded_all_both (z H D A B : Nat)
    (vacuity : KDerivation (imp H (allCode z H)))
    (forward : KDerivation (imp H (imp D (imp A B))))
    (backward : KDerivation (imp H (imp D (imp B A)))) :
    KDerivation (imp H (imp (allCode z (imp D A)) (allCode z (imp D B)))) ×
      KDerivation (imp H (imp (allCode z (imp D B)) (allCode z (imp D A)))) :=
  ⟨guarded_all_congr z H D A B vacuity forward,
    guarded_all_congr z H D B A vacuity backward⟩

theorem all_congr_of_vacuity_certificate (z H A B : Nat)
    (vacuity : KDerivation (imp H (allCode z H)))
    (step : KDerivation (imp H (imp A B))) :
    theoremCode (certificate (all_congr_of_vacuity z H A B vacuity step)) =
      imp H (imp (allCode z A) (allCode z B)) := certificate_correct _

end PASoundness.PAtoCompactGuardedAllCongruence

#print axioms PASoundness.PAtoCompactGuardedAllCongruence.all_congr_of_vacuity
#print axioms PASoundness.PAtoCompactGuardedAllCongruence.all_both_of_vacuity
#print axioms PASoundness.PAtoCompactGuardedAllCongruence.all_both_of_free
#print axioms PASoundness.PAtoCompactGuardedAllCongruence.guarded_all_congr
#print axioms PASoundness.PAtoCompactGuardedAllCongruence.guarded_all_both
#print axioms PASoundness.PAtoCompactGuardedAllCongruence.all_congr_of_vacuity_certificate
