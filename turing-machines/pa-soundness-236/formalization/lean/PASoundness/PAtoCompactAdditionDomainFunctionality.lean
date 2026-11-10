import PASoundness.PAtoCompactAllocatedAdditionFunctionality
import PASoundness.PAtoCompactDomainToNamedCandidate
import PASoundness.PAtoCompactUnaryGraphFunctional
import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactScopedActiveReplace

/-! Guard the allocated addition functionality result by the actual domainAt
predicates from the term translation. -/
namespace PASoundness.PAtoCompactAdditionDomainFunctionality

open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPartialCompositionAtSource
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactDomainToNamedCandidate
open PASoundness.PAtoCompactAllocatedAdditionFunctionality PASoundness.PAtoCompactCommonSourceSpanEquivalence
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactUnaryGraphFunctional
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactEquivNoShadow

set_option maxRecDepth 262144
set_option maxHeartbeats 0
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guard (d28 d1 d0 d8 b c : Nat) : Formula := namedBoth (domainAt d28 28)
  (namedBoth (domainAt d1 1) (namedBoth (domainAt d0 0) (namedBoth (domainAt d8 8)
    (namedBoth (addAt b 28 1 0) (addAt c 28 1 8)))))

/-- The two allocated addition results are isomorphic under the four actual
domain guards, with independent valid addition binder bases. -/
def addition_domain_functionality (d28 d1 d0 d8 b c : Nat) (hb : 28 < b + 2) (hc : 28 < c + 2) :
    KDerivation (imp (guard d28 d1 d0 d8 b c).encode targetEquivalent.encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(guard d28 d1 d0 d8 b c).encode]
  have hg : Context Γ (guard d28 d1 d0 d8 b c).encode := .head _ _
  have hd28 : Context Γ (domainAt d28 28).encode := Context.conjunctionLeft hg
  have hr := Context.conjunctionRight hg
  have hd1 : Context Γ (domainAt d1 1).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hd0 : Context Γ (domainAt d0 0).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have hd8 : Context Γ (domainAt d8 8).encode := Context.conjunctionLeft hr
  have hr := Context.conjunctionRight hr
  have ha1 : Context Γ (addAt b 28 1 0).encode := Context.conjunctionLeft hr
  have ha2 : Context Γ (addAt c 28 1 8).encode := Context.conjunctionRight hr
  have hc28 : Context Γ (namedCandidate 28).encode := .mp hd28
    (.closed (domain_to_named_candidate d28 28 (by omega) (by decide) (by decide)))
  have hc1 : Context Γ (namedCandidate 1).encode := .mp hd1
    (.closed (domain_to_named_candidate d1 1 (by omega) (by decide) (by decide)))
  have hc0 : Context Γ (namedCandidate 0).encode := .mp hd0
    (.closed (domain_to_named_candidate d0 0 (by omega) (by decide) (by decide)))
  have hc8 : Context Γ (namedCandidate 8).encode := .mp hd8
    (.closed (domain_to_named_candidate d8 8 (by omega) (by decide) (by decide)))
  have hguard : Context Γ (PASoundness.PAtoCompactAllocatedAdditionFunctionality.guard b c).encode :=
    Context.conjunctionIntro hc28 (Context.conjunctionIntro hc1 (Context.conjunctionIntro hc0
      (Context.conjunctionIntro hc8 (Context.conjunctionIntro ha1 ha2))))
  exact .mp hguard (.closed (allocated_addition_functionality b c hb hc))

theorem addition_domain_functionality_certificate (d28 d1 d0 d8 b c : Nat) (hb : 28 < b + 2) (hc : 28 < c + 2) :
    theoremCode (certificate (addition_domain_functionality d28 d1 d0 d8 b c hb hc)) =
      imp (guard d28 d1 d0 d8 b c).encode targetEquivalent.encode := certificate_correct _

private def quotientFrame : Formula := .imp equivalentFormula (equivAt 100 0 1)

private def target_to_allocated : KDerivation (imp targetEquivalent.encode (equivAt 100 0 8).encode) := by
  have hbase : KDerivation quotientFrame.encode := by
    simpa [quotientFrame, Formula.encode, equivTemplate, normalizeBottom_encode] using (canonical_equiv_alpha 100 (by omega)).forward
  have h := replace_derivation 1 8 quotientFrame (by decide) (by decide) hbase
  have halign : replace 1 8 quotientFrame = .imp targetEquivalent (equivAt 100 0 8) := by decide
  rw [halign] at h
  exact h

/-- The same conclusion in the term translation's allocated equivalence
syntax, with an independently chosen valid output base. -/
def addition_domain_functionality_allocated (d28 d1 d0 d8 b c e : Nat)
    (hb : 28 < b + 2) (hc : 28 < c + 2) (he : 8 < e + 2) :
    KDerivation (imp (guard d28 d1 d0 d8 b c).encode (equivAt e 0 8).encode) := by
  have ha := (equivAt_base_alpha 100 e 0 8 (by decide) (by decide) (by omega) he).forward
  exact compose (addition_domain_functionality d28 d1 d0 d8 b c hb hc) (compose target_to_allocated ha)

theorem addition_domain_functionality_allocated_certificate (d28 d1 d0 d8 b c e : Nat)
    (hb : 28 < b + 2) (hc : 28 < c + 2) (he : 8 < e + 2) :
    theoremCode (certificate (addition_domain_functionality_allocated d28 d1 d0 d8 b c e hb hc he)) =
      imp (guard d28 d1 d0 d8 b c).encode (equivAt e 0 8).encode := certificate_correct _

end PASoundness.PAtoCompactAdditionDomainFunctionality

#print axioms PASoundness.PAtoCompactAdditionDomainFunctionality.guard
#print axioms PASoundness.PAtoCompactAdditionDomainFunctionality.addition_domain_functionality
#print axioms PASoundness.PAtoCompactAdditionDomainFunctionality.addition_domain_functionality_certificate
#print axioms PASoundness.PAtoCompactAdditionDomainFunctionality.addition_domain_functionality_allocated
#print axioms PASoundness.PAtoCompactAdditionDomainFunctionality.addition_domain_functionality_allocated_certificate
