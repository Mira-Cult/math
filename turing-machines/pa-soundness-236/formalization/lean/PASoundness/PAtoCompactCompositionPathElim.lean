import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! K elimination of a supplied composition-path witness. The caller provides
literal K proof data for the pointwise step and for vacuity of its context;
this module assumes neither graph existence nor a semantic truth principle. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCompositionPathElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A witness 4 lies in the middle domain and connects query 2 to query 3. -/
def pathBody : Nat := both (member 1 4)
  (both (graphFormula 6 2 4).encode (graphFormula 7 4 3).encode)

def target : Nat := (graphFormula 17 2 3).encode

/-- For any supplied context code U that is K-vacuous at the witness name 4,
a pointwise K derivation from U and the explicit path body yields the same
conclusion from U and an existentially quantified path. The context-vacuity
proof is an explicit proof-data argument: U may contain 4 as a bound name. -/
def eliminate_path (U : Nat)
    (vacuous : KDerivation (imp U (allCode 4 U)))
    (step : KDerivation (imp U (imp pathBody target))) :
    KDerivation (imp U (imp (existsCode 4 pathBody) target)) := by
  let Γ := [U]
  have hu : Context Γ U := Context.head [] U
  have hlocal : Context Γ (imp pathBody target) := .mp hu (.closed step)
  have hv : ∀ a, a ∈ Γ → KDerivation (imp a (allCode 4 a)) := by
    intro a ha
    have he : a = U := by simpa [Γ] using ha
    subst a
    exact vacuous
  have hall : Context Γ (allCode 4 (imp pathBody target)) :=
    Context.generalize 4 hv hlocal
  have htarget : KDerivation (imp target (allCode 4 target)) :=
    (graphFormula 17 2 3).vacuity 4 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Δ := [existsCode 4 pathBody,U]
  have hp : Context Δ (existsCode 4 pathBody) := Context.head _ _
  have hall' : Context Δ (allCode 4 (imp pathBody target)) := Context.under hall _
  exact Context.existsElim htarget hall' hp

theorem eliminate_path_certificate (U : Nat)
    (vacuous : KDerivation (imp U (allCode 4 U)))
    (step : KDerivation (imp U (imp pathBody target))) :
    theoremCode (certificate (eliminate_path U vacuous step)) =
      imp U (imp (existsCode 4 pathBody) target) :=
  certificate_correct (eliminate_path U vacuous step)

end PASoundness.PAtoCompactCompositionPathElim

#print axioms PASoundness.PAtoCompactCompositionPathElim.eliminate_path
#print axioms PASoundness.PAtoCompactCompositionPathElim.eliminate_path_certificate
