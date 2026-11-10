import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactNamed

/-! K equality transport for the fresh endpoint aliases in the two-witness
quotient-successor construction. Each formula below is literal named syntax;
no raw replacement through a bound name or semantic soundness is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactQuotSuccAliasTransport
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact E conjuncts in the first and second alpha-fresh bodies. -/
def firstAlias : Formula := replace 1 41 equivalentFormula
def secondAlias : Formula := replace 0 1 (replace 1 43 equivalentFormula)
def firstTarget : Formula := replace 1 7 equivalentFormula
def secondTarget : Formula := replace 0 1 (replace 1 8 equivalentFormula)

/-- E with both free endpoint names freshened. -/
def bothAliases : Formula := replace 1 43 (replace 0 41 equivalentFormula)
def firstMoved : Formula := replace 1 43 (replace 0 7 equivalentFormula)
def bothTarget : Formula := replace 1 8 (replace 0 7 equivalentFormula)

/-- Transport only the first witness's output alias; all relevant binder
freshness conditions are checked on the actual named formula. -/
def first_output_transport : KDerivation
    (imp (equal 41 7) (imp firstAlias.encode firstTarget.encode)) := by
  have h := (equalityReplace 41 7 firstAlias (by decide) (by decide)).1
  have hs : replace 41 7 firstAlias = firstTarget := by decide
  simpa only [hs] using h

/-- Transport the second witness's output alias capture-safely. -/
def second_output_transport : KDerivation
    (imp (equal 43 8) (imp secondAlias.encode secondTarget.encode)) := by
  have h := (equalityReplace 43 8 secondAlias (by decide) (by decide)).1
  have hs : replace 43 8 secondAlias = secondTarget := by decide
  simpa only [hs] using h

/-- Transport both aliases in an E premise, retaining both equality guards. -/
def both_output_transport : KDerivation
    (imp (equal 41 7) (imp (equal 43 8) (imp bothAliases.encode bothTarget.encode))) := by
  have h1 := (equalityReplace 41 7 bothAliases (by decide) (by decide)).1
  have hs1 : replace 41 7 bothAliases = firstMoved := by decide
  rw [hs1] at h1
  have h2 := (equalityReplace 43 8 firstMoved (by decide) (by decide)).1
  have hs2 : replace 43 8 firstMoved = bothTarget := by decide
  rw [hs2] at h2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [bothAliases.encode, equal 43 8, equal 41 7]
  have he1 : Context Γ (equal 41 7) := .hypothesis (by simp [Γ])
  have he2 : Context Γ (equal 43 8) := .hypothesis (by simp [Γ])
  have ha : Context Γ bothAliases.encode := Context.head _ _
  exact .mp (.mp ha (.mp he1 (.closed h1))) (.mp he2 (.closed h2))

theorem first_output_transport_certificate : theoremCode (certificate first_output_transport) =
    imp (equal 41 7) (imp firstAlias.encode firstTarget.encode) :=
  certificate_correct first_output_transport

theorem second_output_transport_certificate : theoremCode (certificate second_output_transport) =
    imp (equal 43 8) (imp secondAlias.encode secondTarget.encode) :=
  certificate_correct second_output_transport

theorem both_output_transport_certificate : theoremCode (certificate both_output_transport) =
    imp (equal 41 7) (imp (equal 43 8) (imp bothAliases.encode bothTarget.encode)) :=
  certificate_correct both_output_transport

end PASoundness.PAtoCompactQuotSuccAliasTransport

#print axioms PASoundness.PAtoCompactQuotSuccAliasTransport.first_output_transport
#print axioms PASoundness.PAtoCompactQuotSuccAliasTransport.second_output_transport
#print axioms PASoundness.PAtoCompactQuotSuccAliasTransport.both_output_transport
