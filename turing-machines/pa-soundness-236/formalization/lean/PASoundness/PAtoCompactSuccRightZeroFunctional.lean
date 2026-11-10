import PASoundness.PAtoCompactSuccRightZeroGrammar
import PASoundness.PAtoCompactSuccRightZeroFunctionalSucc
import PASoundness.PAtoCompactRightZeroTermFunctional

/-! Guarded graph functionality for arbitrary interleavings of successor
and right addition of zero. The guard supplies candidate conditions for the
term's occurring variables; all relevant names lie below the allocator. -/
namespace PASoundness.PAtoCompactSuccRightZeroFunctional

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactUnaryGraphFunctionalityFull
open PASoundness.PAtoCompactRightZeroTermFunctional
open PASoundness.PAtoCompactSuccRightZeroGrammar
open PASoundness.PAtoCompactSuccRightZeroFunctionalSucc

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Construct finite K functionality proof data by structural recursion;
aliases of source names and output names are permitted. -/
noncomputable def functional {α : Type} [DecidableEq α] (v : α → Nat)
    (g : Formula) {t : Peano.language.Term α} (ht : SuccRightZeroTerm t) :
    ∀ b p q, (∀ a ∈ t.varFinset, v a < b) → (∀ x ∈ g.free, x < b) →
      (∀ a ∈ t.varFinset, KDerivation (imp g.encode (domainAt b (v a)).encode)) →
      p < b → q < b → KDerivation (imp g.encode (imp (termGraph v t p b).encode
        (imp (termGraph v t q b).encode (equivAt b p q).encode))) := by
  induction ht with
  | unary h => exact unary_functional v g h
  | @succ u h ih =>
      intro b p q hv hg hd hp hq
      have hvars : (.func .succ ![u] : Peano.language.Term α).varFinset = u.varFinset := by
        simp [Term.varFinset]
      apply successor_functional v g u ih b p q
      · simpa only [hvars] using hv
      · exact hg
      · intro a ha
        exact hd a (hvars ▸ ha)
      · exact hp
      · exact hq
  | @addZero u h ih =>
      exact add_zero_step v g u ih

end PASoundness.PAtoCompactSuccRightZeroFunctional

#print axioms PASoundness.PAtoCompactSuccRightZeroFunctional.functional
