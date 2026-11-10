import PASoundness.PAtoCompactMultiplicationTopCoverageTriple

/-! Generic finite K assembly of an extra output property for a top-row
witness. Both the existential coverage and property implication are explicit
proof inputs. No uniqueness, product-forward clause, multiplication
totality, or PA bridge is asserted by this module. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationTopPointAssembler
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactMultiplicationTopCoverageTriple
attribute [local irreducible] imp Cantor.pair Cantor.triangle

/-- Add a supplied arbitrary property code `U` to the same output witness.
`H` must be vacuous at binder 5, and both K derivations are explicit inputs.
The result does not assert what `U` means or independently establish it. -/
def assemble (H U : Nat)
    (hHv : KDerivation (imp H (allCode 5 H)))
    (hcoverage : KDerivation (imp H (existsCode 5 tripleWitness.encode)))
    (hproperty : KDerivation (imp H (imp tripleWitness.encode U))) :
    KDerivation (imp H
      (existsCode 5 (both (member 45 5) (both topTriple.encode U)))) := by
  have hpoint : KDerivation (imp H (imp tripleWitness.encode
      (both (member 45 5) (both topTriple.encode U)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [tripleWitness.encode,H]
    have hw : Context Γ tripleWitness.encode := .head _ _
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    have hw' : Context Γ (both (member 45 5)
        (both (graphFormula 6 3 5).encode topTriple.encode)) := by
      simpa [tripleWitness,namedBoth,Formula.not,Formula.encode,both,neg] using hw
    have hu : Context Γ U := .mp hw (.mp hh (.closed hproperty))
    exact Context.conjunctionIntro (Context.conjunctionLeft hw')
      (Context.conjunctionIntro (Context.conjunctionRight (Context.conjunctionRight hw')) hu)
  have hlift := conditionalExistsCongr 5 hHv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [H]
  have hh : Context Γ H := .head _ _
  exact .mp (.mp hh (.closed hcoverage)) (.mp hh (.closed hlift))

theorem assemble_certificate (H U : Nat)
    (hHv : KDerivation (imp H (allCode 5 H)))
    (hcoverage : KDerivation (imp H (existsCode 5 tripleWitness.encode)))
    (hproperty : KDerivation (imp H (imp tripleWitness.encode U))) :
    theoremCode (certificate (assemble H U hHv hcoverage hproperty)) =
      imp H (existsCode 5 (both (member 45 5) (both topTriple.encode U))) :=
  certificate_correct _
end PASoundness.PAtoCompactMultiplicationTopPointAssembler
#print axioms PASoundness.PAtoCompactMultiplicationTopPointAssembler.assemble
#print axioms PASoundness.PAtoCompactMultiplicationTopPointAssembler.assemble_certificate
