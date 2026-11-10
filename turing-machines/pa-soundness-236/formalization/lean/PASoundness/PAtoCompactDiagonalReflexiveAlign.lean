import PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport
import PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
import PASoundness.PAtoCompactDiagonalReflexiveVacuity

/-! Capture-safe K alignment from the supplied diagonal-invariant graph to
reflexive quotient syntax on input name 30. The matrix proof is an explicit
metatheoretic premise; this file neither supplies the candidate graph nor
establishes quotient congruence or PA proof transport. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDiagonalReflexiveAlign
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactDiagonalInvariantStep PASoundness.PAtoCompactDiagonalExistentialStep
open PASoundness.PAtoCompactDiagonalReflexiveInvariantTransport
open PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport PASoundness.PAtoCompactDiagonalReflexiveVacuity

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A supplied matrix derivation and three explicitly equal aliases transport
one given diagonal-invariant graph into the exact reflexive quotient formula. -/
def alias_point (hMatrix : KDerivation (imp (equal 0 1)
    (imp oldInvariant (both bijectionFormula.encode orderFormula.encode)))) :
    KDerivation (imp (equal 0 30) (imp (equal 1 30) (imp (equal 6 11)
      (imp (invariantNamed 30 11).encode reflexive30.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let I := (invariantNamed 30 11).encode
  let Γ := [I,equal 6 11,equal 1 30,equal 0 30]
  have h0 : Context Γ (equal 0 30) := .hypothesis (by simp [Γ])
  have h1 : Context Γ (equal 1 30) := .hypothesis (by simp [Γ])
  have h6 : Context Γ (equal 6 11) := .hypothesis (by simp [Γ])
  have hi : Context Γ I := Context.head _ _
  have h01 : Context Γ (equal 0 1) := Context.eqTrans h0 (Context.eqSymm h1)
  have ho : Context Γ oldInvariant := .mp hi (.mp h6 (.mp h0 (.closed invariant_transport)))
  have hm : Context Γ (both bijectionFormula.encode orderFormula.encode) :=
    .mp ho (.mp h01 (.closed hMatrix))
  exact .mp hm (.mp h1 (.mp h0 (.closed matrix_to_reflexive)))

/-- Eliminate an alias from an implication whose conclusion is independent of
that alias, using the literal K equality-existence axiom. -/
def eliminate_alias (x y F : Nat)
    (hv : KDerivation (imp F (allCode x F)))
    (h : KDerivation (imp (equal x y) F)) : KDerivation F := by
  apply Context.closeEmpty
  exact Context.existsElim hv (.closed (.generalize x h)) (.closed (existsEqual x y))

/-- The exact graph-existence formula entails the reflexive quotient formula,
conditional only on the explicitly supplied matrix derivation. -/
def invariant_exists_to_reflexive (hMatrix : KDerivation (imp (equal 0 1)
    (imp oldInvariant (both bijectionFormula.encode orderFormula.encode)))) :
    KDerivation (imp (existsCode 11 (invariantNamed 30 11).encode) reflexive30.encode) := by
  let Inv := invariantNamed 30 11
  let E := reflexive30
  let F0 : CompactNamed.Formula := .imp (.equal 1 30) (.imp (.equal 6 11) (.imp Inv E))
  let F1 : CompactNamed.Formula := .imp (.equal 6 11) (.imp Inv E)
  let F6 : CompactNamed.Formula := .imp Inv E
  have hv0 : KDerivation (imp F0.encode (allCode 0 F0.encode)) := F0.vacuity 0 (by decide)
  have hv1 : KDerivation (imp F1.encode (allCode 1 F1.encode)) := F1.vacuity 1 (by decide)
  have hvInv6 : KDerivation (imp Inv.encode (allCode 6 Inv.encode)) := Inv.vacuity 6 (by decide)
  have hvE6 : KDerivation (imp E.encode (allCode 6 E.encode)) := reflexive_vacuity_6
  have hv6 : KDerivation (imp F6.encode (allCode 6 F6.encode)) := implicationVacuity 6 hvInv6 hvE6
  have h0 : KDerivation (imp (equal 0 30) F0.encode) := alias_point hMatrix
  have hF0 : KDerivation F0.encode := eliminate_alias 0 30 F0.encode hv0 h0
  have hF1 : KDerivation F1.encode := eliminate_alias 1 30 F1.encode hv1 hF0
  have hlocal : KDerivation (imp Inv.encode E.encode) := eliminate_alias 6 11 F6.encode hv6 hF1
  have hvE11 : KDerivation (imp E.encode (allCode 11 E.encode)) := E.vacuity 11 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.existsElim hvE11 (.closed (.generalize 11 hlocal))
    (Context.head [] (existsCode 11 Inv.encode))

theorem invariant_exists_to_reflexive_certificate (hMatrix : KDerivation (imp (equal 0 1)
    (imp oldInvariant (both bijectionFormula.encode orderFormula.encode)))) :
    theoremCode (certificate (invariant_exists_to_reflexive hMatrix)) =
      imp (existsCode 11 (invariantNamed 30 11).encode) reflexive30.encode :=
  certificate_correct (invariant_exists_to_reflexive hMatrix)

end PASoundness.PAtoCompactDiagonalReflexiveAlign

#print axioms PASoundness.PAtoCompactDiagonalReflexiveAlign.invariant_exists_to_reflexive
#print axioms PASoundness.PAtoCompactDiagonalReflexiveAlign.invariant_exists_to_reflexive_certificate
