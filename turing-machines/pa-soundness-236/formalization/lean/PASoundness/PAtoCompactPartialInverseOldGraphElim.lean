import PASoundness.PAtoCompactPartialInversePairElim
import PASoundness.PAtoCompactAdjunction

/-! Scope-safe elimination of the old partial-inverse graph witness for the
inside-source successor step. The fixed-old-graph step is explicit finite K
proof data. This constructs no step, induction, or isomorphism in itself. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOldGraphElim
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactPartialInverseBase
open PASoundness.PAtoCompactPartialInversePairElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The next graph existential, alpha-renamed from binder 7 to binder 17 so
that eliminating the old graph witness 7 cannot capture the conclusion. -/
def nextWithBinder17 : Formula := .ex 17 (replace 7 17 nextInvariant)

def oldGraphStepCode : Nat := imp bijectionFormula.encode (imp (successorCode 8 10 15)
  (imp (member 0 8) (imp partialInverse.encode (existsCode 7 nextInvariant.encode))))

/-- Eliminate the old graph witness under a supplied fixed-graph successor
proof. The conclusion is explicitly alpha-renamed to binder 17. -/
def eliminate_old_graph_renamed (step : KDerivation oldGraphStepCode) : KDerivation
    (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp (existsCode 7 partialInverse.encode) nextWithBinder17.encode)))) := by
  let B := bijectionFormula.encode
  let S := successorCode 8 10 15
  let M := member 0 8
  let P := partialInverse.encode
  let T := nextWithBinder17.encode
  let Γ := [M,S,B]
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have halpha : KDerivation (imp (existsCode 7 nextInvariant.encode) T) :=
    (existentialAlpha 7 17 nextInvariant (by decide) (by decide) (by decide)).1
  have hfixed : Context Γ (imp P (existsCode 7 nextInvariant.encode)) :=
    .mp hm (.mp hs (.mp hb (.closed step)))
  have hlocal : Context Γ (imp P T) := by
    apply Context.deduction
    have hp : Context (P :: Γ) P := Context.head _ _
    exact .mp (.mp hp (Context.under hfixed P)) (.closed halpha)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 7 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases heM : h = M
    · subst h
      exact membershipVacuity 0 8 7 (by decide) (by decide)
    · by_cases heS : h = S
      · subst h
        have hvS := (namedSuccessor 8 10 15).vacuity 7 (by decide)
        exact hvS
      · have heB : h = B := (hh.resolve_left heM).resolve_left heS
        subst h
        exact bijectionFormula.vacuity 7 (by decide)
  have hall : Context Γ (allCode 7 (imp P T)) := Context.generalize 7 hv hlocal
  have htarget : KDerivation (imp T (allCode 7 T)) :=
    nextWithBinder17.vacuity 7 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [existsCode 7 P,M,S,B]
  have he : Context Δ (existsCode 7 P) := Context.head _ _
  have hall' : Context Δ (allCode 7 (imp P T)) := Context.weaken hall (by
    intro h hh; exact List.mem_cons_of_mem _ hh)
  exact Context.existsElim htarget hall' he

/-- The alpha-renamed conclusion is transported back to the canonical graph
binder 7. The fixed-graph step remains the only proof-data input. -/
def eliminate_old_graph (step : KDerivation oldGraphStepCode) : KDerivation
    (imp bijectionFormula.encode (imp (successorCode 8 10 15)
      (imp (member 0 8) (imp (existsCode 7 partialInverse.encode)
        (existsCode 7 nextInvariant.encode))))) := by
  have halpha : KDerivation (imp nextWithBinder17.encode (existsCode 7 nextInvariant.encode)) :=
    (existentialAlpha 7 17 nextInvariant (by decide) (by decide) (by decide)).2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode 7 partialInverse.encode,member 0 8,successorCode 8 10 15,bijectionFormula.encode]
  have he : Context Γ (existsCode 7 partialInverse.encode) := Context.head _ _
  have hm : Context Γ (member 0 8) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode 8 10 15) := .hypothesis (by simp [Γ])
  have hb : Context Γ bijectionFormula.encode := .hypothesis (by simp [Γ])
  have ht : Context Γ nextWithBinder17.encode :=
    .mp he (.mp hm (.mp hs (.mp hb (.closed (eliminate_old_graph_renamed step)))))
  exact .mp ht (.closed halpha)

theorem eliminate_old_graph_certificate (step : KDerivation oldGraphStepCode) :
    theoremCode (certificate (eliminate_old_graph step)) =
      imp bijectionFormula.encode (imp (successorCode 8 10 15)
        (imp (member 0 8) (imp (existsCode 7 partialInverse.encode)
          (existsCode 7 nextInvariant.encode)))) :=
  certificate_correct (eliminate_old_graph step)

end PASoundness.PAtoCompactPartialInverseOldGraphElim

#print axioms PASoundness.PAtoCompactPartialInverseOldGraphElim.eliminate_old_graph
#print axioms PASoundness.PAtoCompactPartialInverseOldGraphElim.eliminate_old_graph_certificate
