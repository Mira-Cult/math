import PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactFreeVacuity

/-! Split one queried nested edge of extended graph 64 into an old graph10
edge or the actual row-witness branch, using the no-garbage invariant. The
very same outer edge witness is retained; no uniqueness of pair objects or
extensionality is assumed. -/
namespace PASoundness.PAtoCompactMultiplicationSecondBranchSplit
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactFixedFirstCoverageBase PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactMultiplicationRowQuerySecond
open PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

def tripleAt (g : Nat) : Formula := .ex 18 (namedBoth (pairFormula 18 7 8) (graphFormula g 18 9))
def branches : Formula := namedEither (tripleAt 10) queriedNewRowSecond
private def f19 : Formula := namedBoth (.member 64 19) (pairFormula 19 18 9)
private def f63 : Formula := namedBoth (.member 64 63) (pairFormula 63 18 9)
private def old19 : Formula := namedBoth (.member 10 19) (pairFormula 19 18 9)
private def old63 : Formula := namedBoth (.member 10 63) (pairFormula 63 18 9)
private def body : Formula := .imp (.member 64 9) (namedEither (.member 10 9) rowWitness)
private def B : Formula := namedBoth queryPairsSecond (replace 9 63 rowWitness)

/-- The chosen graph label may be renamed from the original product triple
without changing the actual query syntax. -/
theorem triple_shape : replace 6 64 (tripleFormula 7 8 9) = tripleAt 64 := by decide
theorem old_triple_shape : replace 6 10 (tripleFormula 7 8 9) = tripleAt 10 := by decide

private def graph_alpha : KDerivation (imp (graphFormula 64 18 9).encode (existsCode 63 f63.encode)) := by
  have h := (existentialAlpha 19 63 f19 (by decide) (by decide) (by decide)).1
  have he : replace 19 63 f19 = f63 := by decide
  rw [he] at h
  change KDerivation (imp (existsCode 19 f19.encode) (existsCode 63 f63.encode)) at h
  change KDerivation (imp (existsCode 19 f19.encode) (existsCode 63 f63.encode))
  exact h

private def split_at63 : KDerivation (imp (noGarbage 64).encode
    (imp (pairFormula 18 7 8).encode (imp f63.encode branches.encode))) := by
  have hinst := universalInstance 9 63 body (by decide) (by decide) (by decide)
  have hb : replace 9 63 body = .imp (.member 64 63)
      (namedEither (.member 10 63) (replace 9 63 rowWitness)) := by decide
  rw [hb] at hinst
  have hno : KDerivation (imp (noGarbage 64).encode
      (imp (member 64 63) (either (member 10 63) (replace 9 63 rowWitness).encode))) := by
    simpa [noGarbage,body,namedEither,Formula.encode,Formula.not,either,neg] using hinst
  have hiOld := exists_variable_intro 19 63 old19 (by decide) (by decide) (by decide)
  have ho : replace 19 63 old19 = old63 := by decide
  rw [ho] at hiOld
  have hOldGraph : KDerivation (imp old63.encode (graphFormula 10 18 9).encode) := by
    change KDerivation (imp old63.encode (existsCode 19 old19.encode))
    exact hiOld
  have hiOldTriple := existsIntroduce 18
    (namedBoth (pairFormula 18 7 8) (graphFormula 10 18 9)) (by decide)
  have hiNew63 := existsIntroduce 63 B (by decide)
  have hiNew18 := existsIntroduce 18 (.ex 63 B) (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [f63.encode,(pairFormula 18 7 8).encode,(noGarbage 64).encode]
  have hf : Context Γ f63.encode := .head _ _
  have hp : Context Γ (pairFormula 18 7 8).encode := .hypothesis (by simp [Γ])
  have hg : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hf' : Context Γ (both (member 64 63) (pairFormula 63 18 9).encode) := by
    simpa [f63,namedBoth,Formula.not,Formula.encode,both,neg] using hf
  have hcases : Context Γ (either (member 10 63) (replace 9 63 rowWitness).encode) :=
    .mp (Context.conjunctionLeft hf') (.mp hg (.closed hno))
  apply Context.disjunctionElim hcases
  · let Δ := member 10 63 :: Γ
    have hm : Context Δ (member 10 63) := .head _ _
    have hpair : Context Δ (pairFormula 63 18 9).encode := .under (Context.conjunctionRight hf') _
    have hold : Context Δ old63.encode := by
      simpa [old63,namedBoth,Formula.encode,Formula.not,both,neg] using Context.conjunctionIntro hm hpair
    have hedge : Context Δ (graphFormula 10 18 9).encode := .mp hold (.closed hOldGraph)
    have hmatrix : Context Δ (namedBoth (pairFormula 18 7 8) (graphFormula 10 18 9)).encode := by
      simpa [namedBoth,Formula.encode,Formula.not,both,neg] using
        (Context.conjunctionIntro (.under hp _) hedge)
    have htriple : Context Δ (tripleAt 10).encode := by
      simpa [tripleAt,Formula.encode] using (.mp hmatrix (.closed hiOldTriple))
    simpa [branches,namedEither,Formula.encode,Formula.not,either,neg] using
      (Context.disjunctionLeft (b := queriedNewRowSecond.encode) htriple)
  · let Δ := (replace 9 63 rowWitness).encode :: Γ
    have hr : Context Δ (replace 9 63 rowWitness).encode := .head _ _
    have hpair : Context Δ (pairFormula 63 18 9).encode := .under (Context.conjunctionRight hf') _
    have hq : Context Δ queryPairsSecond.encode := by
      simpa [queryPairsSecond,namedBoth,Formula.encode,Formula.not,both,neg] using
        (Context.conjunctionIntro hpair (.under hp _))
    have hb' : Context Δ B.encode := by
      simpa [B,namedBoth,Formula.encode,Formula.not,both,neg] using Context.conjunctionIntro hq hr
    have hn : Context Δ queriedNewRowSecond.encode := by
      simpa [queriedNewRowSecond,Formula.encode] using (.mp (.mp hb' (.closed hiNew63)) (.closed hiNew18))
    simpa [branches,namedEither,Formula.encode,Formula.not,either,neg] using
      (Context.disjunctionRight (a := (tripleAt 10).encode) hn)

/-- For a second-point triple in the extended graph, no-garbage forces an
old-graph triple or its exact new-row query branch. -/
def second_branch_split : KDerivation
    (imp (noGarbage 64).encode (imp (tripleAt 64).encode branches.encode)) := by
  have hresult63 : KDerivation (imp branches.encode (allCode 63 branches.encode)) :=
    free_vacuity 63 branches (by decide)
  have hresult18 : KDerivation (imp branches.encode (allCode 18 branches.encode)) :=
    free_vacuity 18 branches (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(tripleAt 64).encode,(noGarbage 64).encode]
  have ht : Context Γ (existsCode 18 (namedBoth (pairFormula 18 7 8) (graphFormula 64 18 9)).encode) := by
    exact Context.head _ _
  apply Context.existsElim hresult18 _ ht
  apply Context.generalize 18
  · intro q hq
    change q ∈ Γ at hq
    by_cases hq1 : q = (tripleAt 64).encode
    · subst q
      have hh := free_vacuity 18 (tripleAt 64) (by decide)
      simpa using hh
    · have hq2 : q = (noGarbage 64).encode := by simpa [Γ,hq1] using hq
      subst q
      exact (noGarbage 64).vacuity 18 (by decide)
  apply Context.deduction
  let Δ := [(namedBoth (pairFormula 18 7 8) (graphFormula 64 18 9)).encode,
    (tripleAt 64).encode,(noGarbage 64).encode]
  have hbody : Context Δ (both (pairFormula 18 7 8).encode (graphFormula 64 18 9).encode) := by
    have hh := Context.head [(tripleAt 64).encode,(noGarbage 64).encode]
      (namedBoth (pairFormula 18 7 8) (graphFormula 64 18 9)).encode
    simpa [Δ,namedBoth,Formula.encode,Formula.not,both,neg] using hh
  have hp := Context.conjunctionLeft hbody
  have hex : Context Δ (existsCode 63 f63.encode) := .mp (Context.conjunctionRight hbody) (.closed graph_alpha)
  apply Context.existsElim hresult63 _ hex
  apply Context.generalize 63
  · intro q hq
    change q ∈ Δ at hq
    by_cases hq1 : q = (namedBoth (pairFormula 18 7 8) (graphFormula 64 18 9)).encode
    · subst q
      exact (namedBoth (pairFormula 18 7 8) (graphFormula 64 18 9)).vacuity 63 (by decide)
    · by_cases hq2 : q = (tripleAt 64).encode
      · subst q
        exact (tripleAt 64).vacuity 63 (by decide)
      · have hq3 : q = (noGarbage 64).encode := by simpa [Δ,hq1,hq2] using hq
        subst q
        exact (noGarbage 64).vacuity 63 (by decide)
  apply Context.deduction
  let Θ := f63.encode :: Δ
  have hf : Context Θ f63.encode := .head _ _
  have hpair : Context Θ (pairFormula 18 7 8).encode := .under hp _
  have hng : Context Θ (noGarbage 64).encode := .hypothesis (by simp [Θ,Δ])
  exact .mp hf (.mp hpair (.mp hng (.closed split_at63)))

theorem second_branch_split_certificate : theoremCode (certificate second_branch_split) =
    imp (noGarbage 64).encode (imp (tripleAt 64).encode branches.encode) := certificate_correct _
end PASoundness.PAtoCompactMultiplicationSecondBranchSplit
#print axioms PASoundness.PAtoCompactMultiplicationSecondBranchSplit.second_branch_split
#print axioms PASoundness.PAtoCompactMultiplicationSecondBranchSplit.second_branch_split_certificate
