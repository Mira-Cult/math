import PASoundness.PAtoCompactAdditionZeroAllocated
import PASoundness.PAtoCompactAdditionOutputAlpha

/-! The right-zero addition witness with one common allocated base, at the
fixed input labels. Arbitrary input-label instantiation remains separate. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroRebased

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAdditionOutputAlpha
open PASoundness.PAtoCompactAdditionZeroAllocated

def conj_first {a b : Formula} (c : Formula) (h : KDerivation (imp a.encode b.encode)) :
    KDerivation (imp (andF a c).encode (andF b c).encode) := by
  change KDerivation (imp (neg (imp a.encode (neg c.encode))) (neg (imp b.encode (neg c.encode))))
  exact contrapose (implicationCongr h (PASoundness.CompactHilbertBasis.identity (neg c.encode)))

/-- A fixed-input right-zero witness with a common guard and addition base.
The explicit bounds make the output binder capture-safe. -/
def rebased (b out : Nat) (hb : 38 ≤ b) (ho : 32 < out) (hbound : out < b+2) : KDerivation
  (imp (domainAt b 30).encode (imp (zeroAt b 31).encode
    (existsCode out (body b b out).encode))) := by
  have hd := domainAt_transport b 100 30 (by omega) (by decide)
  have hz := zeroAt_base_forward b 100 31 (by omega) (by decide)
  have hbody : KDerivation (imp (andF (domainAt 100 32) (addAt b 30 31 32)).encode
      (body b b 32).encode) :=
    conj_first (addAt b 30 31 32) (domainAt_transport 100 b 32 (by decide) (by omega))
  have hq := existsCongr 32 hbody
  have ha := (output_alpha b b out (by omega) ho (by omega) hbound).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(zeroAt b 31).encode, (domainAt b 30).encode]
  have hzr : Context Γ (zeroAt b 31).encode := .head _ _
  have hdr : Context Γ (domainAt b 30).encode := .hypothesis (by simp [Γ])
  have hd100 : Context Γ (domainAt 100 30).encode := .mp hdr (.closed hd)
  have hz100 : Context Γ (zeroAt 100 31).encode := .mp hzr (.closed hz)
  have hfixed : Context Γ (existsCode 32
      (andF (domainAt 100 32) (addAt b 30 31 32)).encode) :=
    .mp hz100 (.mp hd100 (.closed (guarded_allocated_right_zero b hb)))
  exact .mp (.mp hfixed (.closed hq)) (.closed ha)

theorem rebased_certificate (b out : Nat) (hb : 38 ≤ b) (ho : 32 < out) (hbound : out < b+2) :
    theoremCode (certificate (rebased b out hb ho hbound)) =
      imp (domainAt b 30).encode (imp (zeroAt b 31).encode
        (existsCode out (body b b out).encode)) := certificate_correct _

end PASoundness.PAtoCompactAdditionZeroRebased

#print axioms PASoundness.PAtoCompactAdditionZeroRebased.rebased
#print axioms PASoundness.PAtoCompactAdditionZeroRebased.rebased_certificate
