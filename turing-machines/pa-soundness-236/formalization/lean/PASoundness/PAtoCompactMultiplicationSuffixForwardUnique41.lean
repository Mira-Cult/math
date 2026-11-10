import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactZeroSuccessor

/-! A fixed-name K forward-uniqueness implication for the suffix bijection.
The graph and bijection are supplied as literal antecedents. This proves no
suffix graph existence, product graph, multiplication totality, or PA bridge. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Source 31, target 40 and graph 6; labels are syntactic. -/
def suffixBijection : Formula := replace 1 40 (replace 0 31 bijectionFormula)

private def witness (i : Nat) : Formula := namedBoth (.member 40 3)
  (namedBoth (graphFormula 6 i 3)
    (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 6 i 4)) (.equal 4 3))))
private def forwardBody : Formula := .imp (.member 31 2) (.ex 3 (witness 2))
private def target : Formula := .imp (.member 40 5)
  (.imp (graphFormula 6 41 5) (.imp (.member 40 11)
    (.imp (graphFormula 6 41 11) (.equal 5 11))))
private def uniqueBody : Formula := .imp (namedBoth (.member 40 4) (graphFormula 6 41 4)) (.equal 4 3)

/-- Two target-guarded edges from one source agree. No identity of pair
representatives is assumed; the actual bijection's uniqueness clause is used. -/
def forward_unique : KDerivation (imp suffixBijection.encode (imp (member 31 41)
    (imp (member 40 5) (imp (graphFormula 6 41 5).encode
      (imp (member 40 11) (imp (graphFormula 6 41 11).encode (equal 5 11))))))) := by
  have hf : KDerivation (imp suffixBijection.encode (allCode 2 forwardBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hb : Context [suffixBijection.encode] suffixBijection.encode := .head _ _
    change Context [suffixBijection.encode] (both (allCode 2 forwardBody.encode) _) at hb
    exact Context.conjunctionLeft hb
  have hi := universalInstance 2 41 forwardBody (by decide) (by decide) (by decide)
  have hs : replace 2 41 forwardBody = .imp (.member 31 41) (.ex 3 (witness 41)) := by decide
  rw [hs] at hi
  have h5 := universalInstance 4 5 uniqueBody (by decide) (by decide) (by decide)
  have h11 := universalInstance 4 11 uniqueBody (by decide) (by decide) (by decide)
  have hs5 : replace 4 5 uniqueBody = .imp (namedBoth (.member 40 5) (graphFormula 6 41 5)) (.equal 5 3) := by decide
  have hs11 : replace 4 11 uniqueBody = .imp (namedBoth (.member 40 11) (graphFormula 6 41 11)) (.equal 11 3) := by decide
  rw [hs5] at h5
  rw [hs11] at h11
  have hl : KDerivation (imp (witness 41).encode target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [(graphFormula 6 41 11).encode,member 40 11,
      (graphFormula 6 41 5).encode,member 40 5,(witness 41).encode]
    have hw : Context Γ (witness 41).encode := .hypothesis (by simp [Γ])
    have hu : Context Γ (allCode 4 uniqueBody.encode) := by
      change Context Γ (both (member 40 3)
        (both (graphFormula 6 41 3).encode (allCode 4 uniqueBody.encode))) at hw
      exact Context.conjunctionRight (Context.conjunctionRight hw)
    have hm5 : Context Γ (member 40 5) := .hypothesis (by simp [Γ])
    have hm11 : Context Γ (member 40 11) := .hypothesis (by simp [Γ])
    have hg5 : Context Γ (graphFormula 6 41 5).encode := .hypothesis (by simp [Γ])
    have hg11 : Context Γ (graphFormula 6 41 11).encode := .head _ _
    have he5 : Context Γ (equal 5 3) := .mp (Context.conjunctionIntro hm5 hg5) (.mp hu (.closed h5))
    have he11 : Context Γ (equal 11 3) := .mp (Context.conjunctionIntro hm11 hg11) (.mp hu (.closed h11))
    exact Context.eqTrans he5 (Context.eqSymm he11)
  have hv : KDerivation (imp target.encode (allCode 3 target.encode)) := target.vacuity 3 (by decide)
  have helim : KDerivation (imp (existsCode 3 (witness 41).encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 3 hl)) (.head [] _)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 41,suffixBijection.encode]
  have hm : Context Γ (member 31 41) := .head _ _
  have hb : Context Γ suffixBijection.encode := .hypothesis (by simp [Γ])
  have he : Context Γ (existsCode 3 (witness 41).encode) := .mp hm (.mp (.mp hb (.closed hf)) (.closed hi))
  simpa [target,Formula.encode] using (.mp he (.closed helim))

theorem forward_unique_certificate : theoremCode (certificate forward_unique) =
    imp suffixBijection.encode (imp (member 31 41)
      (imp (member 40 5) (imp (graphFormula 6 41 5).encode
        (imp (member 40 11) (imp (graphFormula 6 41 11).encode (equal 5 11)))))) :=
  certificate_correct forward_unique
end PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41
#print axioms PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41.forward_unique
#print axioms PASoundness.PAtoCompactMultiplicationSuffixForwardUnique41.forward_unique_certificate
