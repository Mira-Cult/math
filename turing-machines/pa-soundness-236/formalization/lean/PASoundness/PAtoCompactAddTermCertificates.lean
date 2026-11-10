import PASoundness.PAtoCompactAddTermTransport

/-! Certificate equations for the conditional addition-term base transport.
All child-graph derivations remain explicit inputs. -/
namespace PASoundness.PAtoCompactAddTermCertificates

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAddTermTransport

variable {α : Type} [DecidableEq α] (v : α → Nat)
variable (l r : Peano.language.Term α) (b c out : Nat)
variable (hbo : out < b) (hco : out < c)
variable (hbl : ∀ a ∈ l.varFinset, v a < b) (hcl : ∀ a ∈ l.varFinset, v a < c)
variable (hbr : ∀ a ∈ r.varFinset, v a < b) (hcr : ∀ a ∈ r.varFinset, v a < c)
variable (blF : KDerivation (imp (termGraph v l b (b + 64)).encode
  (termGraph v l b (intermediateBase b c + 64)).encode))
variable (blB : KDerivation (imp (termGraph v l b (intermediateBase b c + 64)).encode
  (termGraph v l b (b + 64)).encode))
variable (brF : KDerivation (imp (termGraph v r (b + 1) (b + 64 + termCost l)).encode
  (termGraph v r (b + 1) (intermediateBase b c + 64 + termCost l)).encode))
variable (brB : KDerivation (imp (termGraph v r (b + 1) (intermediateBase b c + 64 + termCost l)).encode
  (termGraph v r (b + 1) (b + 64 + termCost l)).encode))
variable (clF : KDerivation (imp (termGraph v l c (c + 64)).encode
  (termGraph v l c (intermediateBase b c + 64)).encode))
variable (clB : KDerivation (imp (termGraph v l c (intermediateBase b c + 64)).encode
  (termGraph v l c (c + 64)).encode))
variable (crF : KDerivation (imp (termGraph v r (c + 1) (c + 64 + termCost l)).encode
  (termGraph v r (c + 1) (intermediateBase b c + 64 + termCost l)).encode))
variable (crB : KDerivation (imp (termGraph v r (c + 1) (intermediateBase b c + 64 + termCost l)).encode
  (termGraph v r (c + 1) (c + 64 + termCost l)).encode))

theorem addTerm_base_forward_certificate :
    theoremCode (certificate (addTerm_base_transport v l r b c out hbo hco
      hbl hcl hbr hcr blF blB brF brB clF clB crF crB).1) =
      imp (termGraph v (.func .add ![l, r]) out b).encode
        (termGraph v (.func .add ![l, r]) out c).encode := certificate_correct _

theorem addTerm_base_backward_certificate :
    theoremCode (certificate (addTerm_base_transport v l r b c out hbo hco
      hbl hcl hbr hcr blF blB brF brB clF clB crF crB).2) =
      imp (termGraph v (.func .add ![l, r]) out c).encode
        (termGraph v (.func .add ![l, r]) out b).encode := certificate_correct _

end PASoundness.PAtoCompactAddTermCertificates

#print axioms PASoundness.PAtoCompactAddTermCertificates.addTerm_base_forward_certificate
#print axioms PASoundness.PAtoCompactAddTermCertificates.addTerm_base_backward_certificate
