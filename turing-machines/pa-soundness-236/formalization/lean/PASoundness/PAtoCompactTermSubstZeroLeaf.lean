import PASoundness.PAtoCompactUnaryGraphFunctional

/-! Zero-substitution term-graph leaf. The reverse direction is constructed
from zero-graph functionality; the forward direction currently takes the
finite K zero-output transport proof as an explicit input. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTermSubstZeroLeaf
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactUnaryGraphFunctional
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A retained zero graph and a variable graph imply a zero graph at the
variable graph's output, given the explicit zero-output transport proof. -/
def zero_leaf_forward (b q r : Nat)
    (ho : KDerivation (imp (domainAt b r).encode
      (imp (termGraph id Peano.zero q b).encode
        (imp (equivAt b q r).encode (termGraph id Peano.zero r b).encode)))) :
    KDerivation (imp (termGraph id Peano.zero q b).encode
      (imp (termGraph id (.var q : Peano.Term) r b).encode
        (termGraph id Peano.zero r b).encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id Peano.zero q b).encode
  let V := (termGraph id (.var q : Peano.Term) r b).encode
  let Γ := [V,G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hV : Context Γ V := Context.head _ _
  have hD : Context Γ (domainAt b r).encode := Context.conjunctionLeft hV
  have hE : Context Γ (equivAt b q r).encode := Context.conjunctionRight hV
  exact .mp hE (.mp hG (.mp hD (.closed ho)))

/-- The two zero graphs supply quotient equivalence directly. Their labels may
coincide; no guard, semantic truth, or functionality premise is required. -/
def zero_leaf_reverse (b q r : Nat) (hq : q < b+2) (hr : r < b+2) :
    KDerivation (imp (termGraph id Peano.zero q b).encode
      (imp (termGraph id Peano.zero r b).encode
        (termGraph id (.var q : Peano.Term) r b).encode)) := by
  have hf := zero_graph_functional id b q r hq hr
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let G := (termGraph id Peano.zero q b).encode
  let T := (termGraph id Peano.zero r b).encode
  let Γ := [T,G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hT : Context Γ T := Context.head _ _
  have hD : Context Γ (domainAt b r).encode := Context.conjunctionLeft hT
  have hE : Context Γ (equivAt b q r).encode := .mp hT (.mp hG (.closed hf))
  exact Context.conjunctionIntro hD hE

theorem zero_leaf_forward_certificate (b q r : Nat)
    (ho : KDerivation (imp (domainAt b r).encode
      (imp (termGraph id Peano.zero q b).encode
        (imp (equivAt b q r).encode (termGraph id Peano.zero r b).encode)))) :
    theoremCode (certificate (zero_leaf_forward b q r ho)) =
      imp (termGraph id Peano.zero q b).encode
        (imp (termGraph id (.var q : Peano.Term) r b).encode
          (termGraph id Peano.zero r b).encode) := certificate_correct _

theorem zero_leaf_reverse_certificate (b q r : Nat) (hq : q < b+2) (hr : r < b+2) :
    theoremCode (certificate (zero_leaf_reverse b q r hq hr)) =
      imp (termGraph id Peano.zero q b).encode
        (imp (termGraph id Peano.zero r b).encode
          (termGraph id (.var q : Peano.Term) r b).encode) := certificate_correct _

end PASoundness.PAtoCompactTermSubstZeroLeaf

#print axioms PASoundness.PAtoCompactTermSubstZeroLeaf.zero_leaf_forward
#print axioms PASoundness.PAtoCompactTermSubstZeroLeaf.zero_leaf_reverse
#print axioms PASoundness.PAtoCompactTermSubstZeroLeaf.zero_leaf_forward_certificate
#print axioms PASoundness.PAtoCompactTermSubstZeroLeaf.zero_leaf_reverse_certificate
