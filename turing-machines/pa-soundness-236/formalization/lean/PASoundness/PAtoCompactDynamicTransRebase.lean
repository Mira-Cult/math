import PASoundness.PAtoCompactDynamicTransRelocation
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Rebase a finite K transitivity proof from separate private blocks to one
requested block. The operand names may coincide. The source transitivity
derivation is explicit proof data; no semantic soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDynamicTransRebase

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactDynamicTransRelocation

/-- Rebase candidate and quotient-equivalence blocks. Only the named operand
bounds are needed; none of the operands must be distinct. -/
def trans_rebase (b d e x y z : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hzb : z < b+2)
    (hxd : x < d+2) (hxe : x < e+2) (hye : y < e+2) (hze : z < e+2)
    (h : KDerivation (transFrame d e x y z).encode) :
    KDerivation (transFrame b b x y z).encode := by
  have hd := domainAt_transport b d x (by omega) (by omega)
  have hxy := (equivAt_base_alpha b e x y hxb hyb hxe hye).forward
  have hyz := (equivAt_base_alpha b e y z hyb hzb hye hze).forward
  have hxz := (equivAt_base_alpha e b x z hxe hze hxb hzb).forward
  change KDerivation (imp (domainAt b x).encode
    (imp (equivAt b x y).encode (imp (equivAt b y z).encode (equivAt b x z).encode)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b x).encode
  let A := (equivAt b x y).encode
  let B := (equivAt b y z).encode
  let Γ := [B,A,D]
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hB : Context Γ B := .head _ _
  have hd' : Context Γ (domainAt d x).encode := .mp hD (.closed hd)
  have hxy' : Context Γ (equivAt e x y).encode := .mp hA (.closed hxy)
  have hyz' : Context Γ (equivAt e y z).encode := .mp hB (.closed hyz)
  have he : Context Γ (equivAt e x z).encode := by
    exact .mp hyz' (.mp hxy' (.mp hd' (.closed h)))
  exact .mp he (.closed hxz)

theorem trans_rebase_certificate (b d e x y z : Nat)
    (hxb : x < b+2) (hyb : y < b+2) (hzb : z < b+2)
    (hxd : x < d+2) (hxe : x < e+2) (hye : y < e+2) (hze : z < e+2)
    (h : KDerivation (transFrame d e x y z).encode) :
    theoremCode (certificate (trans_rebase b d e x y z hxb hyb hzb hxd hxe hye hze h)) =
      (transFrame b b x y z).encode := certificate_correct _

end PASoundness.PAtoCompactDynamicTransRebase

#print axioms PASoundness.PAtoCompactDynamicTransRebase.trans_rebase
#print axioms PASoundness.PAtoCompactDynamicTransRebase.trans_rebase_certificate
