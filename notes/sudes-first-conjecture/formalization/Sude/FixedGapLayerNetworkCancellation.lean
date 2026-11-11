import Sude.NetworkSwitches

/-! Full layers of fixed-gap network pairs have zero signed line correction.
The same statement applies to physical columns through transposition. -/
namespace Sude
noncomputable section

/-- A fixed gap gives zero total transfer into any vertex when every edge of
one permutation layer is included. Gaps may differ between layers. -/
theorem layer_fixed_gap_transfer_sum_zero {n : ℕ}
    (layers : List (LayerPacking.Layer n)) (i : Fin layers.length)
    (g : ℕ) (r : Fin n) :
    (∑ e : Fin n, layerTransfer layers (fun _ _ => g) (i,e) r) = 0 := by
  classical
  unfold layerTransfer
  simp only [Finset.sum_sub_distrib]
  have h := Equiv.sum_comp (layers.get i).1 (fun x : Fin n => if x = r then (g : ℤ) else 0)
  rw [h]
  exact sub_self _

/-- A physical full layer has zero signed row correction if its slots are
exactly the labelled layer slots and all of its pairs have the same gap.
Apply to a transposed placement to obtain the physical-column statement. -/
theorem row_network_fixed_gap_layer_sum_zero {n : ℕ}
    (layers : List (LayerPacking.Layer n)) {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin layers.length × Fin n) a)
    (i : Fin layers.length) (g : ℕ)
    (hslot : ∀ e side, rowNetworkSlot v ((i,e),side) = layerPairSlot layers (i,e) side)
    (hgap : ∀ e, v.gap (i,e) = g) (r : Fin n) :
    (∑ e : Fin n, rowNetworkDelta v (i,e) r) = 0 := by
  classical
  have hlo (e : Fin n) : v.low (i,e) = e := by
    have h := congrArg Prod.fst (hslot e false)
    simpa [rowNetworkSlot, layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell] using h
  have hhi (e : Fin n) : v.high (i,e) = (layers.get i).1 e := by
    have h := congrArg Prod.fst (hslot e true)
    simpa [rowNetworkSlot, layerPairSlot, LayerPacking.sequenceCell, LayerPacking.layerCell] using h
  calc
    (∑ e : Fin n, rowNetworkDelta v (i,e) r) =
        ∑ e : Fin n, layerTransfer layers (fun _ _ => g) (i,e) r := by
          apply Finset.sum_congr rfl
          intro e he
          simp [rowNetworkDelta, layerTransfer, hlo e, hhi e, hgap e]
    _ = 0 := layer_fixed_gap_transfer_sum_zero layers i g r


/-- Any collection of complete layers has zero correction, provided each
selected layer has a gap constant across its edges. -/
theorem row_network_fixed_gap_layers_sum_zero {n : ℕ}
    (layers : List (LayerPacking.Layer n)) {a : Cell n ≃ Fin (n*n)}
    (v : RowNetworkPairs (Fin layers.length × Fin n) a)
    (I : Finset (Fin layers.length)) (g : Fin layers.length → ℕ)
    (hslot : ∀ i ∈ I, ∀ e side, rowNetworkSlot v ((i,e),side) = layerPairSlot layers (i,e) side)
    (hgap : ∀ i ∈ I, ∀ e, v.gap (i,e) = g i) (r : Fin n) :
    (∑ k ∈ I.product Finset.univ, rowNetworkDelta v k r) = 0 := by
  classical
  change (∑ k ∈ I ×ˢ (Finset.univ : Finset (Fin n)), rowNetworkDelta v k r) = 0
  rw [Finset.sum_product]
  apply Finset.sum_eq_zero
  intro i hi
  exact row_network_fixed_gap_layer_sum_zero layers v i (g i) (hslot i hi) (hgap i hi) r

end
end Sude
