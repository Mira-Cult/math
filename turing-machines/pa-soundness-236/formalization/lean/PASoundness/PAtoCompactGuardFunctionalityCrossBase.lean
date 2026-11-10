import PASoundness.PAtoCompactTermSubstPolyReplacement
import PASoundness.PAtoCompactAllTermTransport

/-! Reuse a guarded term-graph functionality family when the two input
graphs have independently allocated private blocks. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGuardFunctionalityCrossBase

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactGuardBaseTransport

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

noncomputable def cross_base (g : Formula) (t : Peano.Term) (b r s d p q : Nat)
    (hbr : b ≤ r) (hbs : b ≤ s) (hbd : b ≤ d)
    (hpr : p < r) (hqs : q < s) (hpd : p < d) (hqd : q < d)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode))
    (functional : GuardFunctionality g t) : KDerivation
    (imp g.encode (imp (termGraph id t p r).encode
      (imp (termGraph id t q s).encode (equivAt d p q).encode))) := by
  have htr : ∀ a ∈ t.varFinset, id a < r := by
    intro a ha
    change a < r
    have h := ht a ha
    omega
  have hts : ∀ a ∈ t.varFinset, id a < s := by
    intro a ha
    change a < s
    have h := ht a ha
    omega
  have htd : ∀ a ∈ t.varFinset, a < d := by intro a ha; have h := ht a ha; omega
  have hgd : ∀ a ∈ g.free, a < d := by intro a ha; have h := hg a ha; omega
  have hdomd : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt d a).encode) := by
    intro a ha
    have hb := ht a ha
    exact compose (hdom a ha) (domainAt_transport b d a (by omega) (by omega))
  have hfirst := (termGraph_base_transport id t r d p hpr hpd htr htd).1
  have hsecond := (termGraph_base_transport id t s d q hqs hqd hts htd).1
  have hf := functional d p q hpd hqd htd hgd hdomd
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(termGraph id t q s).encode,(termGraph id t p r).encode,g.encode]
  have hq : Context Γ (termGraph id t q s).encode := .head _ _
  have hp : Context Γ (termGraph id t p r).encode := .hypothesis (by simp [Γ])
  have hg₀ : Context Γ g.encode := .hypothesis (by simp [Γ])
  have h := Context.mp (Context.mp hq (.closed hsecond))
    (Context.mp (Context.mp hp (.closed hfirst)) (Context.mp hg₀ (.closed hf)))
  simpa [Γ] using h

theorem cross_base_certificate (g : Formula) (t : Peano.Term) (b r s d p q : Nat)
    (hbr : b ≤ r) (hbs : b ≤ s) (hbd : b ≤ d)
    (hpr : p < r) (hqs : q < s) (hpd : p < d) (hqd : q < d)
    (ht : ∀ a ∈ t.varFinset, a < b) (hg : ∀ a ∈ g.free, a < b)
    (hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b a).encode))
    (functional : GuardFunctionality g t) :
    theoremCode (certificate (cross_base g t b r s d p q hbr hbs hbd hpr hqs hpd hqd ht hg hdom functional)) =
      imp g.encode (imp (termGraph id t p r).encode
        (imp (termGraph id t q s).encode (equivAt d p q).encode)) := certificate_correct _

end PASoundness.PAtoCompactGuardFunctionalityCrossBase

#print axioms PASoundness.PAtoCompactGuardFunctionalityCrossBase.cross_base
#print axioms PASoundness.PAtoCompactGuardFunctionalityCrossBase.cross_base_certificate
