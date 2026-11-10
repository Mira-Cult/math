import PASoundness.PAtoCompactPartialCompositionBase
import PASoundness.PAtoCompactPartialCompositionBackwardNew

/-! Quantifier packaging for a supplied pointwise composition-extension
backward proof. All vacuity derivations and the pointwise K proof are explicit
proof-data inputs. No graph construction or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionBackwardLift
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialCompositionBase
open PASoundness.PAtoCompactPartialCompositionBackwardNew
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def conj (a b : Formula) : Formula := (a.imp b.not).not

/-- Exact guarded backward clause for a new partial composition graph. -/
def backwardFormula : Formula := .all 2 (.all 3
  (.imp (conj (.member 0 2) (.member 8 3))
    (.imp (graphFormula 17 2 3) (conj (.member 13 2) path))))

/-- Lift an explicit pointwise derivation under P and the original partial
composition invariant. Each hypothesis has separately supplied K vacuity
at both query names; no syntactic freshness or graph existence is inferred. -/
def backward_lift (P : Formula)
    (p2 : KDerivation (imp P.encode (allCode 2 P.encode)))
    (p3 : KDerivation (imp P.encode (allCode 3 P.encode)))
    (o2 : KDerivation (imp partialComposition.encode (allCode 2 partialComposition.encode)))
    (o3 : KDerivation (imp partialComposition.encode (allCode 3 partialComposition.encode)))
    (pointwise : KDerivation (imp P.encode (imp partialComposition.encode
      (imp (both (member 0 2) (member 8 3))
        (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode)))))) :
    KDerivation (imp P.encode (imp partialComposition.encode backwardFormula.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [partialComposition.encode,P.encode]
  have ho : Context Γ partialComposition.encode := Context.head _ _
  have hp : Context Γ P.encode := .hypothesis (by simp [Γ])
  have hl : Context Γ (imp (both (member 0 2) (member 8 3))
      (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode))) :=
    .mp ho (.mp hp (.closed pointwise))
  have hv2 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 2 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases h : q = partialComposition.encode
    · subst q; exact o2
    · have h' : q = P.encode := hq.resolve_left h
      subst q; exact p2
  have hv3 : ∀ q, q ∈ Γ → KDerivation (imp q (allCode 3 q)) := by
    intro q hq
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hq
    by_cases h : q = partialComposition.encode
    · subst q; exact o3
    · have h' : q = P.encode := hq.resolve_left h
      subst q; exact p3
  exact Context.generalize 2 hv2 (Context.generalize 3 hv3 hl)

theorem backward_lift_certificate (P : Formula)
    (p2 : KDerivation (imp P.encode (allCode 2 P.encode)))
    (p3 : KDerivation (imp P.encode (allCode 3 P.encode)))
    (o2 : KDerivation (imp partialComposition.encode (allCode 2 partialComposition.encode)))
    (o3 : KDerivation (imp partialComposition.encode (allCode 3 partialComposition.encode)))
    (pointwise : KDerivation (imp P.encode (imp partialComposition.encode
      (imp (both (member 0 2) (member 8 3))
        (imp (graphFormula 17 2 3).encode (both (member 13 2) path.encode)))))) :
    theoremCode (certificate (backward_lift P p2 p3 o2 o3 pointwise)) =
      imp P.encode (imp partialComposition.encode backwardFormula.encode) :=
  certificate_correct (backward_lift P p2 p3 o2 o3 pointwise)

end PASoundness.PAtoCompactPartialCompositionBackwardLift

#print axioms PASoundness.PAtoCompactPartialCompositionBackwardLift.backward_lift
#print axioms PASoundness.PAtoCompactPartialCompositionBackwardLift.backward_lift_certificate
