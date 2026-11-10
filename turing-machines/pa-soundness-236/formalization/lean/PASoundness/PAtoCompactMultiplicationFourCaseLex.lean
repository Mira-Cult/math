import PASoundness.PAtoCompactMultiplicationFirstBranchSplit
import PASoundness.PAtoCompactMultiplicationSecondBranchSplit
import PASoundness.PAtoCompactMultiplicationSameRowLex

/-! Propositional finite-K assembly of four multiplication lexicographic
point cases. The actual first and second graph64 triples are split using the
explicit prefix0 no-garbage invariant. All four case proofs remain explicit
proof data under an arbitrary common premise. This does not supply those case
proofs, construct a row graph, prove the quantified product matrix, or prove
multiplication totality. -/
namespace PASoundness.PAtoCompactMultiplicationFourCaseLex
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFixedFirstCoverageBase
open PASoundness.PAtoCompactMultiplicationOldTripleIntro
open PASoundness.PAtoCompactMultiplicationTripleEdgeAlpha
open PASoundness.PAtoCompactMultiplicationFirstBranchSplit
open PASoundness.PAtoCompactMultiplicationRowQueryFirstExists
open PASoundness.PAtoCompactMultiplicationRowQuerySecondExists
open PASoundness.PAtoCompactMultiplicationSameRowLex
attribute [local irreducible] imp Cantor.pair Cantor.triangle
set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The two queried old and new branches and their exact two-directional
lexicographic goal, all as literal compact codes. -/
def oldFirst : Nat := oldTriple.encode
def newFirst : Nat := queriedNewRow.encode
def oldSecond : Nat := (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 10).encode
def newSecond : Nat := queriedNewRowSecond.encode
def comparisons : Nat := both forwardClause reverseClause

/-- The supplied four K derivations may use the same explicit common premise;
no omitted graph-domain or cleanliness assumptions are supplied here. -/
structure CaseProofs (P : Nat) where
  oldOld : KDerivation (imp P (imp oldFirst (imp oldSecond comparisons)))
  oldNew : KDerivation (imp P (imp oldFirst (imp newSecond comparisons)))
  newOld : KDerivation (imp P (imp newFirst (imp oldSecond comparisons)))
  newNew : KDerivation (imp P (imp newFirst (imp newSecond comparisons)))

/-- Split each actual queried triple using the same supplied no-garbage
invariant, then apply the corresponding explicitly supplied K case proof. -/
def point_of_cases (P : Nat) (cases : CaseProofs P) : KDerivation
    (imp P (imp (noGarbage 64).encode (imp queriedTriple.encode
      (imp (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode comparisons)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode,
    queriedTriple.encode,(noGarbage 64).encode,P]
  have ht2 : Context Γ (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode := .head _ _
  have ht1 : Context Γ queriedTriple.encode := .hypothesis (by simp [Γ])
  have hn : Context Γ (noGarbage 64).encode := .hypothesis (by simp [Γ])
  have hp : Context Γ P := .hypothesis (by simp [Γ])
  have h1 : Context Γ (either oldFirst newFirst) := by
    have h := Context.mp ht1 (Context.mp hn (.closed first_branch_split))
    simpa [branchResult,oldFirst,newFirst,namedEither,Formula.not,Formula.encode,either,neg] using h
  have h2 : Context Γ (either oldSecond newSecond) := by
    have h := Context.mp ht2 (Context.mp hn (.closed PAtoCompactMultiplicationSecondBranchSplit.second_branch_split))
    simpa [PAtoCompactMultiplicationSecondBranchSplit.branches,oldSecond,newSecond,
      namedEither,Formula.not,Formula.encode,either,neg] using h
  apply Context.disjunctionElim h1
  · let Δ := oldFirst :: Γ
    have hfirst : Context Δ oldFirst := .head _ _
    apply Context.disjunctionElim (.under h2 _)
    · let Θ := oldSecond :: Δ
      have hsecond : Context Θ oldSecond := .head _ _
      exact .mp hsecond (.mp (.under hfirst _) (.mp (.under (.under hp _) _) (.closed cases.oldOld)))
    · let Θ := newSecond :: Δ
      have hsecond : Context Θ newSecond := .head _ _
      exact .mp hsecond (.mp (.under hfirst _) (.mp (.under (.under hp _) _) (.closed cases.oldNew)))
  · let Δ := newFirst :: Γ
    have hfirst : Context Δ newFirst := .head _ _
    apply Context.disjunctionElim (.under h2 _)
    · let Θ := oldSecond :: Δ
      have hsecond : Context Θ oldSecond := .head _ _
      exact .mp hsecond (.mp (.under hfirst _) (.mp (.under (.under hp _) _) (.closed cases.newOld)))
    · let Θ := newSecond :: Δ
      have hsecond : Context Θ newSecond := .head _ _
      exact .mp hsecond (.mp (.under hfirst _) (.mp (.under (.under hp _) _) (.closed cases.newNew)))

theorem point_of_cases_certificate (P : Nat) (cases : CaseProofs P) :
    theoremCode (certificate (point_of_cases P cases)) =
      imp P (imp (noGarbage 64).encode (imp queriedTriple.encode
        (imp (PAtoCompactMultiplicationSecondBranchSplit.tripleAt 64).encode comparisons))) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationFourCaseLex
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLex.CaseProofs
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLex.point_of_cases
#print axioms PASoundness.PAtoCompactMultiplicationFourCaseLex.point_of_cases_certificate
