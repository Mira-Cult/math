import PASoundness.PAtoCompactZeroTermBaseTransport
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Finite K transport of a variable term graph between allocator bases.
This is one leaf of the term-graph alpha-invariance proof. -/
namespace PASoundness.PAtoCompactVariableTermBaseTransport

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactZeroTermBaseTransport PASoundness.PAtoCompactEquivMultiAlpha

/-- Change the private base of a variable graph. The variable and output
labels may be equal; the four bounds concern syntax labels only. -/
def variableTerm_base_forward {α : Type} (v : α → Nat) (a : α) (b c out : Nat)
    (hvb : v a < b + 2) (hob : out < b + 2)
    (hvc : v a < c + 2) (hoc : out < c + 2) :
    KDerivation (imp (termGraph v (.var a) out b).encode
      (termGraph v (.var a) out c).encode) := by
  change KDerivation (imp (andF (domainAt b out) (equivAt b (v a) out)).encode
    (andF (domainAt c out) (equivAt c (v a) out)).encode)
  exact andF_transport _ _ _ _ (domainAt_transport b c out (by omega) (by omega))
    (equivAt_base_alpha b c (v a) out hvb hob hvc hoc).forward

def variableTerm_base_backward {α : Type} (v : α → Nat) (a : α) (b c out : Nat)
    (hvb : v a < b + 2) (hob : out < b + 2)
    (hvc : v a < c + 2) (hoc : out < c + 2) :
    KDerivation (imp (termGraph v (.var a) out c).encode
      (termGraph v (.var a) out b).encode) :=
  variableTerm_base_forward v a c b out hvc hoc hvb hob

theorem variableTerm_base_forward_certificate {α : Type} (v : α → Nat) (a : α)
    (b c out : Nat) (hvb : v a < b + 2) (hob : out < b + 2)
    (hvc : v a < c + 2) (hoc : out < c + 2) :
    theoremCode (certificate (variableTerm_base_forward v a b c out hvb hob hvc hoc)) =
      imp (termGraph v (.var a) out b).encode (termGraph v (.var a) out c).encode :=
  certificate_correct _

theorem variableTerm_base_backward_certificate {α : Type} (v : α → Nat) (a : α)
    (b c out : Nat) (hvb : v a < b + 2) (hob : out < b + 2)
    (hvc : v a < c + 2) (hoc : out < c + 2) :
    theoremCode (certificate (variableTerm_base_backward v a b c out hvb hob hvc hoc)) =
      imp (termGraph v (.var a) out c).encode (termGraph v (.var a) out b).encode :=
  certificate_correct _

end PASoundness.PAtoCompactVariableTermBaseTransport

#print axioms PASoundness.PAtoCompactVariableTermBaseTransport.variableTerm_base_forward
#print axioms PASoundness.PAtoCompactVariableTermBaseTransport.variableTerm_base_backward
#print axioms PASoundness.PAtoCompactVariableTermBaseTransport.variableTerm_base_forward_certificate
#print axioms PASoundness.PAtoCompactVariableTermBaseTransport.variableTerm_base_backward_certificate
