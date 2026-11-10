import PASoundness.PAtoCompactSuccGraphOutputLift
import PASoundness.PAtoCompactSuccRelationOutputTransport

/-! Finite K output transport for a successor term graph. The output names and
source variables are below the parent allocator base to avoid capture by its
existential witness; output labels may coincide. -/
namespace PASoundness.PAtoCompactSuccGraphOutputClosed

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactSuccRelationOutputTransport

/-- A successor graph output can be replaced by a quotient-equivalent
candidate. This constructs K proof data for every child term; no graph
existence or functionality premise is required. -/
noncomputable def succ_graph_output {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    KDerivation (imp (domainAt b r).encode
      (imp (termGraph v (.func .succ ![t]) q b).encode
        (imp (equivAt b q r).encode
          (termGraph v (.func .succ ![t]) r b).encode))) :=
  succ_output_lift v t b q r hq hr hv (succ_output b b q r (by omega) (by omega) (by omega))

theorem succ_graph_output_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (b q r : Nat) (hq : q < b) (hr : r < b)
    (hv : ∀ a ∈ t.varFinset, v a < b) :
    theoremCode (certificate (succ_graph_output v t b q r hq hr hv)) =
      imp (domainAt b r).encode
        (imp (termGraph v (.func .succ ![t]) q b).encode
          (imp (equivAt b q r).encode
            (termGraph v (.func .succ ![t]) r b).encode)) := certificate_correct _

end PASoundness.PAtoCompactSuccGraphOutputClosed

#print axioms PASoundness.PAtoCompactSuccGraphOutputClosed.succ_graph_output
#print axioms PASoundness.PAtoCompactSuccGraphOutputClosed.succ_graph_output_certificate
