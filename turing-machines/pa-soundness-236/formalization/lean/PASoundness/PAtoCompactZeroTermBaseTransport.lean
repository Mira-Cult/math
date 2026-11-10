import PASoundness.PAtoCompactZeroBaseTransport
import PASoundness.PAtoCompactGuardBaseTransport

/-! Finite K transport of the zero term graph between allocator bases. This
is one leaf of the desired term-graph alpha-invariance proof. -/
namespace PASoundness.PAtoCompactZeroTermBaseTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactZeroBaseTransport

/-- Pointwise K implications lift through the named conjunction encoding. -/
def andF_transport (a a' b b' : Formula)
    (ha : KDerivation (imp a.encode a'.encode))
    (hb : KDerivation (imp b.encode b'.encode)) :
    KDerivation (imp (andF a b).encode (andF a' b').encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(andF a b).encode]
  have h : Context Γ (both a.encode b.encode) := by
    have ht : Context Γ (andF a b).encode := Context.head [] _
    simpa [andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using ht
  have hl : Context Γ a'.encode := .mp (Context.conjunctionLeft h) (.closed ha)
  have hr : Context Γ b'.encode := .mp (Context.conjunctionRight h) (.closed hb)
  have hc := Context.conjunctionIntro hl hr
  simpa [Γ, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using hc

/-- The zero term graph can move to a new base under the explicit label
freshness bounds; represented values are not required to be distinct. -/
def zeroTerm_base_forward {α : Type} (v : α → Nat) (b c out : Nat)
    (hb : out < b + 3) (hc : out < c + 3) :
    KDerivation (imp (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out b).encode
      (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out c).encode) := by
  change KDerivation (imp (andF (domainAt b out) (zeroAt b out)).encode
    (andF (domainAt c out) (zeroAt c out)).encode)
  exact andF_transport _ _ _ _ (domainAt_transport b c out (by omega) (by omega))
    (zeroAt_base_forward b c out hb hc)

def zeroTerm_base_backward {α : Type} (v : α → Nat) (b c out : Nat)
    (hb : out < b + 3) (hc : out < c + 3) :
    KDerivation (imp (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out c).encode
      (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out b).encode) :=
  zeroTerm_base_forward v c b out hc hb

theorem zeroTerm_base_forward_certificate {α : Type} (v : α → Nat) (b c out : Nat)
    (hb : out < b + 3) (hc : out < c + 3) :
    theoremCode (certificate (zeroTerm_base_forward v b c out hb hc)) =
      imp (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out b).encode
        (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out c).encode := certificate_correct _

theorem zeroTerm_base_backward_certificate {α : Type} (v : α → Nat) (b c out : Nat)
    (hb : out < b + 3) (hc : out < c + 3) :
    theoremCode (certificate (zeroTerm_base_backward v b c out hb hc)) =
      imp (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out c).encode
        (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out b).encode := certificate_correct _

end PASoundness.PAtoCompactZeroTermBaseTransport

#print axioms PASoundness.PAtoCompactZeroTermBaseTransport.andF_transport
#print axioms PASoundness.PAtoCompactZeroTermBaseTransport.zeroTerm_base_forward
#print axioms PASoundness.PAtoCompactZeroTermBaseTransport.zeroTerm_base_backward
#print axioms PASoundness.PAtoCompactZeroTermBaseTransport.zeroTerm_base_forward_certificate
#print axioms PASoundness.PAtoCompactZeroTermBaseTransport.zeroTerm_base_backward_certificate
