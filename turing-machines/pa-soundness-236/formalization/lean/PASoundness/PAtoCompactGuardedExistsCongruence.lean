import PASoundness.PAtoCompactFreeVacuity
import PASoundness.CompactQuantifiers

/-! Finite K existential congruence under a retained guard. The guard is
explicitly required to be vacuous at the quantified name. -/
namespace PASoundness.PAtoCompactGuardedExistsCongruence

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFreeVacuity

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Lift a guarded pointwise implication through an existential. The target
body must not bind the chosen name, so same-name introduction is valid. -/
def exists_congr_of_vacuity (z H : Nat) (A B : Formula)
    (vacuity : KDerivation (imp H (allCode z H)))
    (targetBinder : z ∉ B.binders)
    (step : KDerivation (imp H (imp A.encode B.encode))) :
    KDerivation (imp H (imp (existsCode z A.encode) (existsCode z B.encode))) := by
  have hi := existsIntroduce z B targetBinder
  have hp : KDerivation (imp H (imp A.encode (existsCode z B.encode))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A.encode, H]
    have hA : Context Γ A.encode := Context.head _ _
    have hH : Context Γ H := .hypothesis (by simp [Γ])
    exact .mp (.mp hA (.mp hH (.closed step))) (.closed hi)
  have hv : KDerivation (imp (existsCode z B.encode)
      (allCode z (existsCode z B.encode))) := by
    have hf : z ∉ (Formula.ex z B).free := by simp [Formula.free]
    simpa [Formula.encode] using free_vacuity z (Formula.ex z B) hf
  have hall : Context [H] (allCode z (imp A.encode (existsCode z B.encode))) := by
    apply generalizeOne z vacuity
    exact .mp (Context.head [] H) (.closed hp)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact Context.existsElim hv (Context.under hall (existsCode z A.encode))
    (Context.head [H] (existsCode z A.encode))

/-- Both implications use the same guard and require the quantified name to
be absent from each target body's binder set. -/
def exists_both_of_vacuity (z H : Nat) (A B : Formula)
    (vacuity : KDerivation (imp H (allCode z H)))
    (ha : z ∉ A.binders) (hb : z ∉ B.binders)
    (forward : KDerivation (imp H (imp A.encode B.encode)))
    (backward : KDerivation (imp H (imp B.encode A.encode))) :
    KDerivation (imp H (imp (existsCode z A.encode) (existsCode z B.encode))) ×
      KDerivation (imp H (imp (existsCode z B.encode) (existsCode z A.encode))) :=
  ⟨exists_congr_of_vacuity z H A B vacuity hb forward,
    exists_congr_of_vacuity z H B A vacuity ha backward⟩

/-- A syntactically fresh guard supplies its own K vacuity proof. -/
def exists_both_of_free (z : Nat) (H A B : Formula) (fresh : z ∉ H.free)
    (ha : z ∉ A.binders) (hb : z ∉ B.binders)
    (forward : KDerivation (imp H.encode (imp A.encode B.encode)))
    (backward : KDerivation (imp H.encode (imp B.encode A.encode))) :
    KDerivation (imp H.encode (imp (existsCode z A.encode) (existsCode z B.encode))) ×
      KDerivation (imp H.encode (imp (existsCode z B.encode) (existsCode z A.encode))) :=
  exists_both_of_vacuity z H.encode A B (free_vacuity z H fresh) ha hb forward backward

theorem exists_congr_of_vacuity_certificate (z H : Nat) (A B : Formula)
    (vacuity : KDerivation (imp H (allCode z H))) (targetBinder : z ∉ B.binders)
    (step : KDerivation (imp H (imp A.encode B.encode))) :
    theoremCode (certificate (exists_congr_of_vacuity z H A B vacuity targetBinder step)) =
      imp H (imp (existsCode z A.encode) (existsCode z B.encode)) := certificate_correct _

end PASoundness.PAtoCompactGuardedExistsCongruence

#print axioms PASoundness.PAtoCompactGuardedExistsCongruence.exists_congr_of_vacuity
#print axioms PASoundness.PAtoCompactGuardedExistsCongruence.exists_both_of_vacuity
#print axioms PASoundness.PAtoCompactGuardedExistsCongruence.exists_both_of_free
#print axioms PASoundness.PAtoCompactGuardedExistsCongruence.exists_congr_of_vacuity_certificate
