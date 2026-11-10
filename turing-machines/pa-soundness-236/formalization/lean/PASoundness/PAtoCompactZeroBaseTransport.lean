import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactFreshen

/-! Capture-safe transport of the zero graph's private binder. This gives
actual finite K derivations; no soundness theorem supplies the transport. -/
namespace PASoundness.PAtoCompactZeroBaseTransport

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation

/-- The named zero graph has one private binder. -/
theorem zeroAt_shape (b x : Nat) :
    zeroAt b x = .all (b + 3) (.imp (.member x (b + 3)) .bottom) := by
  simp [zeroAt, zeroTemplate, mapNames, oneMap]

/-- Change the private zero-graph binder, preserving the named input. -/
def zeroAt_base_equiv (b c x : Nat) (hxb : x < b + 3) (hxc : x < c + 3) :
    ProofEquiv (zeroAt b x) (zeroAt c x) := by
  by_cases he : b = c
  · subst c
    exact ProofEquiv.refl _
  · let body : Formula := .imp (.member x (b + 3)) .bottom
    have hbc : b + 3 ≠ c + 3 := by omega
    have hfree : b + 3 ∉ body.binders := by simp [body, Formula.binders]
    have hnew : c + 3 ∉ body.names := by
      have h1 : c + 3 ≠ x := by omega
      simp [body, Formula.names, h1, Ne.symm he]
    have h := ProofEquiv.alphaAll (b + 3) (c + 3) body hbc hfree hnew
    have hxb' : x ≠ b + 3 := by omega
    simpa [zeroAt_shape, body, replace, rename, hxb'] using h

def zeroAt_base_forward (b c x : Nat) (hxb : x < b + 3) (hxc : x < c + 3) :
    KDerivation (imp (zeroAt b x).encode (zeroAt c x).encode) :=
  (zeroAt_base_equiv b c x hxb hxc).forward

def zeroAt_base_backward (b c x : Nat) (hxb : x < b + 3) (hxc : x < c + 3) :
    KDerivation (imp (zeroAt c x).encode (zeroAt b x).encode) :=
  (zeroAt_base_equiv b c x hxb hxc).backward

theorem zeroAt_base_forward_certificate (b c x : Nat) (hxb : x < b + 3) (hxc : x < c + 3) :
    theoremCode (certificate (zeroAt_base_forward b c x hxb hxc)) =
      imp (zeroAt b x).encode (zeroAt c x).encode := certificate_correct _

theorem zeroAt_base_backward_certificate (b c x : Nat) (hxb : x < b + 3) (hxc : x < c + 3) :
    theoremCode (certificate (zeroAt_base_backward b c x hxb hxc)) =
      imp (zeroAt c x).encode (zeroAt b x).encode := certificate_correct _

end PASoundness.PAtoCompactZeroBaseTransport

#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_shape
#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_base_equiv
#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_base_forward
#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_base_backward
#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_base_forward_certificate
#print axioms PASoundness.PAtoCompactZeroBaseTransport.zeroAt_base_backward_certificate
