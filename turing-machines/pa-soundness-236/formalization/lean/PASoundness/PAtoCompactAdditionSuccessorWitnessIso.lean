import PASoundness.PAtoCompactAdditionSuccessorEquivStep
import PASoundness.PAtoCompactNestedWitnessMapper

/-! Construct and retain the suffix, pair and graph witnesses while deriving
their successor equivalence, from explicitly supplied old graph and domain
hypotheses. This is not general addition totality, PA induction or soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuccessorWitnessIso
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionRightContext PASoundness.PAtoCompactAdditionJointWitness
open PASoundness.PAtoCompactAdditionSuccessorEquivStep PASoundness.PAtoCompactNestedWitnessMapper
attribute [local irreducible] imp Cantor.pair Cantor.triangle
private def H := fixedHypotheses
private def B := suffixWitness
private def P := pairF
private def G := graphA
private def Q := equivAt 38 40
private def HB := namedBoth H B
private def HBP := namedBoth HB P

private def hH : KDerivation (imp H.encode (allCode 40 H.encode)) := H.vacuity 40 (by decide)
private def hHB : KDerivation (imp HB.encode (allCode 11 HB.encode)) := HB.vacuity 11 (by decide)
private def hHBP : KDerivation (imp HBP.encode (allCode 9 HBP.encode)) := HBP.vacuity 9 (by decide)

/-- Retain the constructed suffix, pair and graph while adding the canonical
quotient equivalence at that same suffix. -/
def retain_witness_equiv : KDerivation (imp H.encode
    (imp (existsCode 40 (both B.encode (existsCode 11 (both P.encode (existsCode 9 G.encode)))))
      (existsCode 40 (both B.encode (existsCode 11 (both P.encode (existsCode 9 (both G.encode Q.encode)))))))) := by
  have h := map_nested_witnesses 40 11 9 H.encode B.encode P.encode G.encode Q.encode hH hHB hHBP local_equiv
  exact h

/-- The suffix, pair and graph are constructed in K; the canonical new
source-to-suffix equivalence is retained for the same witnesses. -/
def constructed_witness_equiv : KDerivation (imp H.encode
    (imp (neg (member 33 32)) (imp (successorCode 32 45 39)
      (existsCode 40 (both B.encode (existsCode 11 (both P.encode
        (existsCode 9 (both G.encode Q.encode))))))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [successorCode 32 45 39,neg (member 33 32),H.encode]
  have hs : Context Γ (successorCode 32 45 39) := .head _ _
  have hn : Context Γ (neg (member 33 32)) := .hypothesis (by simp [Γ])
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  have hf := Context.conjunctionLeft hh
  have he : Context Γ (existsCode 40 (both B.encode (existsCode 11 (both P.encode (existsCode 9 G.encode))))) := by
    simpa [H,B,P,G,pairF,suffix_witness_code,suffix_code,graph_code] using
      (.mp hs (.mp hf (.mp hn (.closed joint_witness_exists))) : Context Γ _)
  exact .mp he (.mp hh (.closed retain_witness_equiv))

theorem constructed_witness_equiv_certificate : theoremCode (certificate constructed_witness_equiv) =
    imp H.encode (imp (neg (member 33 32)) (imp (successorCode 32 45 39)
      (existsCode 40 (both B.encode (existsCode 11 (both P.encode
        (existsCode 9 (both G.encode Q.encode)))))))) := certificate_correct constructed_witness_equiv
end PASoundness.PAtoCompactAdditionSuccessorWitnessIso
#print axioms PASoundness.PAtoCompactAdditionSuccessorWitnessIso.retain_witness_equiv
#print axioms PASoundness.PAtoCompactAdditionSuccessorWitnessIso.constructed_witness_equiv
#print axioms PASoundness.PAtoCompactAdditionSuccessorWitnessIso.constructed_witness_equiv_certificate
