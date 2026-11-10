import PASoundness.PAtoCompactSuccRightZeroFunctionalSucc
import PASoundness.PAtoCompactTermSubstPolyReplacement

/-! Bridge the tracked successor-functionality proof transformer to the
`GuardFunctionality` interface used by the PA proof compiler. -/

namespace PASoundness.PAtoCompactSuccGuardFunctionalityStep

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermSubstPolyReplacement
open PASoundness.PAtoCompactSuccRightZeroFunctionalSucc

/-- Construct successor graph functionality from the corresponding family
for an arbitrary PA child term, with the original guard retained. The guard
must furnish candidate-domain proofs for the child's variables at each
requested base, as in `GuardFunctionality`. Names and represented values may
alias. No child proof is constructed by this adapter. -/
noncomputable def successor_guard_functionality (g : Formula) (t : Peano.Term)
    (child : GuardFunctionality g t) : GuardFunctionality g (Peano.succ t) := by
  intro b p q hp hq hv hg hd
  have hvars : (Peano.succ t).varFinset = t.varFinset := by
    simp [Peano.succ, Term.varFinset]
  have ht : ∀ a ∈ t.varFinset, id a < b := by
    intro a ha
    exact hv a (hvars ▸ ha)
  have hdom : ∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (id a)).encode) := by
    intro a ha
    exact hd a (hvars ▸ ha)
  have hc : ∀ b p q, (∀ a ∈ t.varFinset, id a < b) →
      (∀ a ∈ g.free, a < b) →
      (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (id a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode
        (imp (termGraph id t p b).encode
          (imp (termGraph id t q b).encode (equivAt b p q).encode))) := by
    intro b p q hvars hg' hdom' hp' hq'
    exact child b p q hp' hq' hvars hg' hdom'
  simpa only [Peano.succ] using
    successor_functional id g t hc b p q ht hg hdom hp hq

theorem successor_guard_functionality_certificate (g : Formula) (t : Peano.Term)
    (child : GuardFunctionality g t) (b p q : Nat) (hp : p < b) (hq : q < b)
    (hv : ∀ a ∈ (Peano.succ t).varFinset, a < b)
    (hg : ∀ a ∈ g.free, a < b)
    (hd : ∀ a ∈ (Peano.succ t).varFinset,
      KDerivation (imp g.encode (domainAt b a).encode)) :
    theoremCode (certificate (successor_guard_functionality g t child b p q hp hq hv hg hd)) =
      imp g.encode (imp (termGraph id (Peano.succ t) p b).encode
        (imp (termGraph id (Peano.succ t) q b).encode (equivAt b p q).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactSuccGuardFunctionalityStep

#print axioms PASoundness.PAtoCompactSuccGuardFunctionalityStep.successor_guard_functionality
#print axioms PASoundness.PAtoCompactSuccGuardFunctionalityStep.successor_guard_functionality_certificate
