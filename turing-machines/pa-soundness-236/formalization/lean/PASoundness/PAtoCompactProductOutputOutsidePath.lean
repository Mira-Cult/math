import PASoundness.PAtoCompactProductOutputPartialBase
import PASoundness.PAtoCompactOutsidePrefixGeneric
import PASoundness.PAtoCompactAdjunction

/-! On the outside-source successor branch, the same selected source output
belongs to the old prefix exactly when it belongs to the new prefix. This is
a pointwise path-body comparison, not yet the whole graph induction step. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputOutsidePath

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOutsidePrefixGeneric PASoundness.PAtoCompactProductOutputImagePoint
open PASoundness.PAtoCompactProductOutputImageUnique PASoundness.PAtoCompactProductOutputPartialBase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceAt : Formula := replace 33 60 (replace 31 57 (replace 30 56 sourceBody))
def imageAt : Formula := replace 33 60 (replace 31 57 (replace 30 56 imageBody))
def payloadAt : Formula := replace 33 60 (replace 31 57 (replace 30 56 pairedBody))
def sourceTail : Formula := replace 33 60 (replace 31 57 (replace 30 56
  (namedBoth (PAtoCompactMultiplicationCandidate.tripleFormula 30 31 32) (.all 9 sourceUnique))))
def oldBody : Formula := namedBoth (.member 74 32) payloadAt
def nextBody : Formula := namedBoth (.member 59 32) payloadAt
def guard : Formula := namedBoth (namedSuccessor 74 59 76) (.imp (.member 0 74) .bottom)

theorem payload_shape : payloadAt = namedBoth sourceAt imageAt := by decide
theorem source_shape : sourceAt = namedBoth (.member 0 32) sourceTail := by decide
theorem next_body_shape : nextBody = bodyAt := by decide

/-- The outside-source hypothesis transfers the same payload between the
old and successor prefix, in both directions. -/
def outside_body_equiv : KDerivation (imp guard.encode
    (both (imp nextBody.encode oldBody.encode) (imp oldBody.encode nextBody.encode))) := by
  have hp : KDerivation (imp guard.encode (imp payloadAt.encode
      (both (imp (member 59 32) (member 74 32)) (imp (member 74 32) (member 59 32))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [payloadAt.encode,guard.encode]
    have hpay : Context Γ payloadAt.encode := .head _ _
    have hg : Context Γ guard.encode := .hypothesis (by simp [Γ])
    have hg' : Context Γ (both (successorCode 74 59 76) (neg (member 0 74))) := by
      simpa [guard, namedSuccessor, namedSuccessorBody, successorCode, namedBoth, namedEither,
        Formula.not, Formula.encode, both, neg, either] using hg
    have hpay' : Context Γ (both sourceAt.encode imageAt.encode) := by
      simpa [payload_shape, namedBoth, Formula.not, Formula.encode, both, neg] using hpay
    have hsource : Context Γ (both (member 0 32) sourceTail.encode) := by
      simpa [source_shape, namedBoth, Formula.not, Formula.encode, both, neg] using Context.conjunctionLeft hpay'
    have h := Context.mp (Context.conjunctionLeft hsource)
      (Context.mp (Context.conjunctionRight hg') (Context.mp (Context.conjunctionLeft hg')
        (.closed (outside_prefix_point 0 74 59 32 76 (by decide) (by decide) (by decide)))))
    simpa [Γ] using h
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [guard.encode]
  have hg : Context Γ guard.encode := .head _ _
  have hforward : Context Γ (imp nextBody.encode oldBody.encode) := by
    apply Context.deduction
    let Δ := [nextBody.encode,guard.encode]
    have hn : Context Δ nextBody.encode := .head _ _
    have hg₀ : Context Δ guard.encode := .hypothesis (by simp [Δ])
    have hn' : Context Δ (both (member 59 32) payloadAt.encode) := by
      simpa [nextBody, namedBoth, Formula.not, Formula.encode, both, neg] using hn
    have hcmp := Context.mp (Context.conjunctionRight hn') (Context.mp hg₀ (.closed hp))
    have hm := Context.mp (Context.conjunctionLeft hn') (Context.conjunctionLeft hcmp)
    simpa [Δ, oldBody, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hm (Context.conjunctionRight hn')
  have hbackward : Context Γ (imp oldBody.encode nextBody.encode) := by
    apply Context.deduction
    let Δ := [oldBody.encode,guard.encode]
    have ho : Context Δ oldBody.encode := .head _ _
    have hg₀ : Context Δ guard.encode := .hypothesis (by simp [Δ])
    have ho' : Context Δ (both (member 74 32) payloadAt.encode) := by
      simpa [oldBody, namedBoth, Formula.not, Formula.encode, both, neg] using ho
    have hcmp := Context.mp (Context.conjunctionRight ho') (Context.mp hg₀ (.closed hp))
    have hm := Context.mp (Context.conjunctionLeft ho') (Context.conjunctionRight hcmp)
    simpa [Δ, nextBody, namedBoth, Formula.not, Formula.encode, both, neg] using
      Context.conjunctionIntro hm (Context.conjunctionRight ho')
  simpa [Γ] using Context.conjunctionIntro hforward hbackward

theorem outside_body_equiv_certificate : theoremCode (certificate outside_body_equiv) =
    imp guard.encode (both (imp nextBody.encode oldBody.encode) (imp oldBody.encode nextBody.encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactProductOutputOutsidePath

#print axioms PASoundness.PAtoCompactProductOutputOutsidePath.outside_body_equiv
#print axioms PASoundness.PAtoCompactProductOutputOutsidePath.outside_body_equiv_certificate
