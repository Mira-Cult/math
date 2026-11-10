import PASoundness.PAtoCompactProductOutputClauseAlpha
import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactMultiplicationSingleTripleExtension

/-! Align the explicitly collected forward product clause with the canonical
product-matrix forward formula, using literal alpha conversion followed by K
conjunction reassociation. No reverse or order alignment is asserted. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductOutputForwardAlignment

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationSingleTripleExtension PASoundness.PAtoCompactProductOutputClauseAlpha
open PASoundness.PAtoCompactProductOutputForwardClauseAll

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K conjunction reassociation in the needed direction. -/
def both_assoc (a b c : Nat) : KDerivation (imp (both (both a b) c) (both a (both b c))) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both (both a b) c]
  have h : Context Γ (both (both a b) c) := .head _ _
  have hab := Context.conjunctionLeft h
  exact Context.conjunctionIntro (Context.conjunctionLeft hab)
    (Context.conjunctionIntro (Context.conjunctionRight hab) (Context.conjunctionRight h))

def outputTriple (x y z : Nat) : Formula := tripleAt 58 x y z
def uniqueBody : Formula := .all 9 (.imp (namedBoth (.member 42 9) (outputTriple 3 4 9)) (.equal 9 5))
def mappedBody : Formula := namedBoth (namedBoth (.member 42 5) (outputTriple 3 4 5)) uniqueBody
def canonicalBody : Formula := namedBoth (.member 42 5) (namedBoth (outputTriple 3 4 5) uniqueBody)
def mappedForward : Formula := .all 3 (.all 4 (.imp (.member 43 3) (.imp (.member 44 4) (.ex 5 mappedBody))))
def canonicalForward : Formula := replace 6 58 (replace 2 42 (replace 1 44 (replace 0 43
  PAtoCompactMultiplicationCandidate.forwardFormula)))

theorem mapped_forward_shape : forwardMapped = mappedForward := by decide
theorem canonical_forward_shape : canonicalForward = .all 3 (.imp (.member 43 3)
  (.all 4 (.imp (.member 44 4) (.ex 5 canonicalBody)))) := by decide

/-- Move a vacuous antecedent outside a universal using only K distribution. -/
def pull_all (x a b : Nat) (ha : KDerivation (imp a (allCode x a))) :
    KDerivation (imp (allCode x (imp a b)) (imp a (allCode x b))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [a, allCode x (imp a b)]
  have hA : Context Γ a := .head _ _
  have hAll : Context Γ (allCode x (imp a b)) := .hypothesis (by simp [Γ])
  exact Context.allMP (Context.mp hA (.closed ha)) hAll

def mapped_to_canonical : KDerivation (imp forwardMapped.encode canonicalForward.encode) := by
  have hb : KDerivation (imp mappedBody.encode canonicalBody.encode) := by
    simpa [mappedBody, canonicalBody, namedBoth, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using both_assoc (member 42 5) (outputTriple 3 4 5).encode uniqueBody.encode
  have he := existsCongr 5 hb
  have hi4 := implicationCongr (CompactHilbertBasis.identity (member 44 4)) he
  have hi3 := implicationCongr (CompactHilbertBasis.identity (member 43 3)) hi4
  have ha4 := allCongr 4 hi3
  have hmove := pull_all 4 (member 43 3) (imp (member 44 4) (existsCode 5 canonicalBody.encode))
    (membershipVacuity 43 3 4 (by decide) (by decide))
  have ha3 := allCongr 3 (compose ha4 hmove)
  simpa [mapped_forward_shape, mappedForward, canonical_forward_shape, CompactNamed.Formula.encode] using ha3

/-- The complete explicit forward clause implies the canonical target-matrix
forward clause for the same free graph58. -/
def forward_alignment : KDerivation (imp forwardClause.encode canonicalForward.encode) :=
  compose forward_alpha.forward mapped_to_canonical

theorem forward_alignment_certificate : theoremCode (certificate forward_alignment) =
    imp forwardClause.encode canonicalForward.encode := certificate_correct _

end PASoundness.PAtoCompactProductOutputForwardAlignment

#print axioms PASoundness.PAtoCompactProductOutputForwardAlignment.both_assoc
#print axioms PASoundness.PAtoCompactProductOutputForwardAlignment.mapped_to_canonical
#print axioms PASoundness.PAtoCompactProductOutputForwardAlignment.forward_alignment
#print axioms PASoundness.PAtoCompactProductOutputForwardAlignment.forward_alignment_certificate
