import Sude.PhysicalStageInvoice
import Sude.PrefixPairAllocation

/-! Identify the indexed physical network layers with allocator pair slots. -/
namespace Sude
noncomputable section

/-- A stage/layer/edge/side label names exactly the corresponding cell in
the allocator's actual network sequence. -/
theorem prefixStageLayer_sequenceCell {P layers n : ℕ}
    (network : List (LayerPacking.Layer n)) (hlen : network.length = P * layers)
    (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    LayerPacking.sequenceCell network
      (Fin.cast hlen.symm (finProdFinEquiv (j, k)), (edge, side)) =
    LayerPacking.layerCell (prefixStageLayer network hlen j k).1
      (prefixStageLayer network hlen j k).2 (edge, side) := by
  rfl

/-- The same physical label is sent by the allocator to the corresponding
stage's actual ordinary pair slot, preserving the endpoint orientation. -/
theorem prefixStageLayer_networkInput {P d layers n Q m : ℕ}
    (hfit : (4 * d) * 2 + 2 * (layers * n) ≤ Q) (hlen : m = P * layers)
    (network : Fin 2) (j : Fin P) (k : Fin layers) (edge : Fin n) (side : Bool) :
    prefixNetworkInput hfit hlen network
      (Fin.cast hlen.symm (finProdFinEquiv (j, k)), (edge, side)) =
    ((j, prefixOrdinaryPairIndex hfit (network, k, edge)), side) := by
  simp [prefixNetworkInput, prefixOrdinaryInput]

end
end Sude
