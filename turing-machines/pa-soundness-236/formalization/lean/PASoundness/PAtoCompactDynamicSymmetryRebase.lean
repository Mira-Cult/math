import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Finite-K proof transport for a candidate-relative symmetry frame. This
file provides allocator rebasing only: it takes a proof of symmetry at private
blocks `d,e` as explicit input and proves the same instance at block `b`.
It does not itself construct that input or use semantic soundness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0

namespace PASoundness.PAtoCompactDynamicSymmetryRebase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha

/-- Rebase a candidate-relative symmetry proof; `x` and `y` may be the same
operand label. The candidate and the quotient relation may begin at different
private blocks. All inequalities are syntactic name bounds. -/
def rebase_symmetry (b d e x y : Nat)
    (hxb : x < b+2) (hyb : y < b+2)
    (hxd : x < d+2) (hxe : x < e+2) (hye : y < e+2)
    (h : KDerivation (imp (domainAt d x).encode
      (imp (equivAt e x y).encode (equivAt e y x).encode))) :
    KDerivation (imp (domainAt b x).encode
      (imp (equivAt b x y).encode (equivAt b y x).encode)) := by
  have hd := domainAt_transport b d x (by omega) (by omega)
  have hab := (equivAt_base_alpha b e x y hxb hyb hxe hye).forward
  have hba := (equivAt_base_alpha e b y x hye hxe hyb hxb).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(equivAt b x y).encode, (domainAt b x).encode]
  have heq : Context Γ (equivAt b x y).encode := Context.head [_] _
  have hdom : Context Γ (domainAt b x).encode := .hypothesis (List.Mem.tail _ (List.Mem.head _))
  have hdom' : Context Γ (domainAt d x).encode := .mp hdom (.closed hd)
  have hsym : Context Γ (imp (equivAt e x y).encode (equivAt e y x).encode) :=
    .mp hdom' (.closed h)
  have heq' : Context Γ (equivAt e x y).encode := .mp heq (.closed hab)
  have hrev : Context Γ (equivAt e y x).encode := .mp heq' hsym
  exact .mp hrev (.closed hba)

theorem rebase_symmetry_certificate (b d e x y : Nat)
    (hxb : x < b+2) (hyb : y < b+2)
    (hxd : x < d+2) (hxe : x < e+2) (hye : y < e+2)
    (h : KDerivation (imp (domainAt d x).encode
      (imp (equivAt e x y).encode (equivAt e y x).encode))) :
    theoremCode (certificate (rebase_symmetry b d e x y hxb hyb hxd hxe hye h)) =
      imp (domainAt b x).encode (imp (equivAt b x y).encode (equivAt b y x).encode) :=
  certificate_correct _

#print axioms rebase_symmetry
#print axioms rebase_symmetry_certificate
end PASoundness.PAtoCompactDynamicSymmetryRebase
