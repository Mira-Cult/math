import PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
import PASoundness.CompactQuantifiers

/-! Pointwise uniqueness of a supplied clean suffix bijection. This is finite
K proof data for fixed names, not graph existence, multiplication totality,
or a PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationCleanMapUnique41
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactMultiplicationSuffixCleanEdges
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Source 31, target 40, and graph 6, with their actual bijection syntax. -/
def mapBijection40 : Formula := replace 1 40 (replace 0 31 bijectionFormula)
private def witness (x : Nat) : Formula := namedBoth (.member 40 3)
  (namedBoth (graphFormula 6 x 3)
    (.all 4 (.imp (namedBoth (.member 40 4) (graphFormula 6 x 4)) (.equal 4 3))))
private def forwardBody : Formula := .imp (.member 31 2) (.ex 3 (witness 2))
private def compareBody : Formula := .imp (namedBoth (.member 40 4) (graphFormula 6 41 4)) (.equal 4 3)
private def target : Formula := .imp (.member 40 42) (.imp (graphFormula 6 41 42)
  (.imp (.member 40 43) (.imp (graphFormula 6 41 43) (.equal 42 43))))

private def forward_at : KDerivation (imp mapBijection40.encode
    (imp (member 31 41) (existsCode 3 (witness 41).encode))) := by
  have hp : KDerivation (imp mapBijection40.encode (allCode 2 forwardBody.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have h : Context [mapBijection40.encode] mapBijection40.encode := .head _ _
    change Context [mapBijection40.encode] (both (allCode 2 forwardBody.encode) _) at h
    exact Context.conjunctionLeft h
  have hi := universalInstance 2 41 forwardBody (by decide) (by decide) (by decide)
  have hs : replace 2 41 forwardBody = .imp (.member 31 41) (.ex 3 (witness 41)) := by decide
  rw [hs] at hi
  exact compose hp hi

private def point_from_witness : KDerivation (imp (witness 41).encode target.encode) := by
  have h42 := universalInstance 4 42 compareBody (by decide) (by decide) (by decide)
  have h43 := universalInstance 4 43 compareBody (by decide) (by decide) (by decide)
  have hg42 : replace 4 42 (graphFormula 6 41 4) = graphFormula 6 41 42 := by decide
  have hg43 : replace 4 43 (graphFormula 6 41 4) = graphFormula 6 41 43 := by decide
  have h42' : KDerivation (imp (allCode 4 compareBody.encode)
      (imp (both (member 40 42) (graphFormula 6 41 42).encode) (equal 42 3))) := by
    simpa [compareBody,namedBoth,Formula.not,Formula.encode,replace,rename,both,neg,hg42] using h42
  have h43' : KDerivation (imp (allCode 4 compareBody.encode)
      (imp (both (member 40 43) (graphFormula 6 41 43).encode) (equal 43 3))) := by
    simpa [compareBody,namedBoth,Formula.not,Formula.encode,replace,rename,both,neg,hg43] using h43
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 41 43).encode,member 40 43,
    (graphFormula 6 41 42).encode,member 40 42,(witness 41).encode]
  have hw : Context Γ (witness 41).encode := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode 4 compareBody.encode) := by
    have hh : Context Γ (both (member 40 3)
        (both (graphFormula 6 41 3).encode (allCode 4 compareBody.encode))) := by
      simpa [witness,compareBody,namedBoth,Formula.not,Formula.encode,both,neg] using hw
    exact Context.conjunctionRight (Context.conjunctionRight hh)
  have hm42 : Context Γ (member 40 42) := .hypothesis (by simp [Γ])
  have hg42 : Context Γ (graphFormula 6 41 42).encode := .hypothesis (by simp [Γ])
  have hm43 : Context Γ (member 40 43) := .hypothesis (by simp [Γ])
  have hg43 : Context Γ (graphFormula 6 41 43).encode := .head _ _
  have he42 : Context Γ (equal 42 3) :=
    .mp (Context.conjunctionIntro hm42 hg42) (.mp hu (.closed h42'))
  have he43 : Context Γ (equal 43 3) :=
    .mp (Context.conjunctionIntro hm43 hg43) (.mp hu (.closed h43'))
  exact Context.eqTrans he42 (Context.eqSymm he43)

/-- Two codomain-guarded images of the same source point are equal. -/
def guarded_unique : KDerivation (imp mapBijection40.encode (imp (member 31 41)
    (imp (member 40 42) (imp (graphFormula 6 41 42).encode
      (imp (member 40 43) (imp (graphFormula 6 41 43).encode (equal 42 43))))))) := by
  have hv : KDerivation (imp target.encode (allCode 3 target.encode)) := target.vacuity 3 (by decide)
  have helim : KDerivation (imp (existsCode 3 (witness 41).encode) target.encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.existsElim hv (.closed (.generalize 3 point_from_witness)) (.head _ _)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 31 41,mapBijection40.encode]
  have hm : Context Γ (member 31 41) := .head _ _
  have hb : Context Γ mapBijection40.encode := .hypothesis (by simp [Γ])
  have hw : Context Γ (existsCode 3 (witness 41).encode) := .mp hm (.mp hb (.closed forward_at))
  have ht := Context.mp hw (.closed helim)
  simpa [target,Formula.encode] using ht

/-- Cleanliness supplies the two target guards, so no guard on either
queried image needs to be assumed separately. -/
def clean_unique : KDerivation (imp suffixClean.encode (imp mapBijection40.encode
    (imp (member 31 41) (imp (graphFormula 6 41 42).encode
      (imp (graphFormula 6 41 43).encode (equal 42 43)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(graphFormula 6 41 43).encode,(graphFormula 6 41 42).encode,
    member 31 41,mapBijection40.encode,suffixClean.encode]
  have hc : Context Γ suffixClean.encode := .hypothesis (by simp [Γ])
  have hb : Context Γ mapBijection40.encode := .hypothesis (by simp [Γ])
  have hm : Context Γ (member 31 41) := .hypothesis (by simp [Γ])
  have h42 : Context Γ (graphFormula 6 41 42).encode := .hypothesis (by simp [Γ])
  have h43 : Context Γ (graphFormula 6 41 43).encode := .head _ _
  have hm42 : Context Γ (member 40 42) :=
    Context.conjunctionRight (.mp h42 (.mp hc (.closed (clean_endpoints 41 42 (by decide)))))
  have hm43 : Context Γ (member 40 43) :=
    Context.conjunctionRight (.mp h43 (.mp hc (.closed (clean_endpoints 41 43 (by decide)))))
  exact .mp h43 (.mp hm43 (.mp h42 (.mp hm42 (.mp hm (.mp hb (.closed guarded_unique))))))

theorem clean_unique_certificate : theoremCode (certificate clean_unique) =
    imp suffixClean.encode (imp mapBijection40.encode
      (imp (member 31 41) (imp (graphFormula 6 41 42).encode
        (imp (graphFormula 6 41 43).encode (equal 42 43))))) := certificate_correct clean_unique
end PASoundness.PAtoCompactMultiplicationCleanMapUnique41
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUnique41.guarded_unique
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUnique41.clean_unique
#print axioms PASoundness.PAtoCompactMultiplicationCleanMapUnique41.clean_unique_certificate
