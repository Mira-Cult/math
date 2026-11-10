import PASoundness.PAtoCompactAddBaseMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport

/-!
Transport an already constructed K proof for an addition witness between
allocator bases. This is a proof transformer, not a construction of the source
proof. If the existential output is intended to be independent of the inputs,
the caller must additionally ensure that its name differs from both inputs.
-/

namespace PASoundness.PAtoCompactAdditionGeneralBaseTransport

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactAddBaseMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private def conjFirst {a b : Formula} (c : Formula)
    (h : KDerivation (imp a.encode b.encode)) :
    KDerivation (imp (andF a c).encode (andF b c).encode) := by
  change KDerivation (imp (neg (imp a.encode (neg c.encode)))
    (neg (imp b.encode (neg c.encode))))
  exact contrapose (implicationCongr h (PASoundness.CompactHilbertBasis.identity (neg c.encode)))

private def conjSecond (a : Formula) {b c : Formula}
    (h : KDerivation (imp b.encode c.encode)) :
    KDerivation (imp (andF a b).encode (andF a c).encode) := by
  change KDerivation (imp (neg (imp a.encode (neg b.encode)))
    (neg (imp a.encode (neg c.encode))))
  exact contrapose (implicationCongr (PASoundness.CompactHilbertBasis.identity a.encode) (contrapose h))

def rebase (b c x y out : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hob : out < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hoc : out < c + 2)
    (d : KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)))) :
    KDerivation (imp (domainAt c x).encode (imp (domainAt c y).encode
      (existsCode out (andF (domainAt c out) (addAt c x y out)).encode))) := by
  have hx := domainAt_transport c b x (by omega) (by omega)
  have hy := domainAt_transport c b y (by omega) (by omega)
  have ho := domainAt_transport b c out (by omega) (by omega)
  have ha := (addAt_base_alpha b c x y out hxb hyb hob hxc hyc hoc).forward
  have hbody : KDerivation (imp (andF (domainAt b out) (addAt b x y out)).encode
      (andF (domainAt c out) (addAt c x y out)).encode) :=
    compose (conjFirst (addAt b x y out) ho) (conjSecond (domainAt c out) ha)
  have hq := existsCongr out hbody
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt c y).encode, (domainAt c x).encode]
  have hyc' : Context Γ (domainAt c y).encode := .head _ _
  have hxc' : Context Γ (domainAt c x).encode := .hypothesis (by simp [Γ])
  have hxb' : Context Γ (domainAt b x).encode := .mp hxc' (.closed hx)
  have hyb' : Context Γ (domainAt b y).encode := .mp hyc' (.closed hy)
  have hsource : Context Γ (existsCode out (andF (domainAt b out) (addAt b x y out)).encode) :=
    .mp hyb' (.mp hxb' (.closed d))
  exact .mp hsource (.closed hq)

theorem rebase_certificate (b c x y out : Nat)
    (hxb : x < b + 2) (hyb : y < b + 2) (hob : out < b + 2)
    (hxc : x < c + 2) (hyc : y < c + 2) (hoc : out < c + 2)
    (d : KDerivation (imp (domainAt b x).encode (imp (domainAt b y).encode
      (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)))) :
    theoremCode (certificate (rebase b c x y out hxb hyb hob hxc hyc hoc d)) =
      imp (domainAt c x).encode (imp (domainAt c y).encode
        (existsCode out (andF (domainAt c out) (addAt c x y out)).encode)) :=
  certificate_correct _

end PASoundness.PAtoCompactAdditionGeneralBaseTransport

#print axioms PASoundness.PAtoCompactAdditionGeneralBaseTransport.rebase
#print axioms PASoundness.PAtoCompactAdditionGeneralBaseTransport.rebase_certificate
