import Sude.FWPhysicalMidpointReference
import Sude.FWPhysicalRadiusCentering

/-! Physical midpoint references for the supplied same-square invoice, for
both rows and transposed columns. Exact block-gap totals remain hypotheses. -/
namespace Sude
noncomputable section

theorem fw_reference_invoice_physical_midpoint_bounds {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (a b₀ : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ) (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork (Fin 3 × Fin n) (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork (Fin 3 × Fin n) (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap))
    (hends : ∀ e, BR.source e = e.2 ∧ BC.source e = e.2 ∧
      BR.target e = p e.1 e.2 ∧ BC.target e = p e.1 e.2)
    (hrowTotal : ∀ e, ∑ k ∈ BR.block e, (hr.rowPairs a rowGap hrowGap).gap k = BR.radius e)
    (hcolTotal : ∀ e, ∑ k ∈ BC.block e, (hc.columnPairs a colGap hcolGap).gap k = BC.radius e)
    (hinvoice : TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC) :
    (∀ r, |2 * (rowSum b₀ r : ℤ) -
      physicalNetworkMidpointTwice (hr.rowPairs a rowGap hrowGap) BR r| ≤ 9) ∧
    (∀ c, |2 * (columnSum b₀ c : ℤ) -
      physicalNetworkMidpointTwice (hc.columnPairs a colGap hcolGap) BC c| ≤ 9) := by
  obtain ⟨hrow, hcol⟩ := fw_reference_invoice_radius_bounds p a b₀ reserved rows cols hr hc
    rowGap colGap hrowGap hcolGap BR BC hends hinvoice
  have hrs : BR.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e; exact (hends e).1
  have hcs : BC.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e; exact (hends e).2.1
  have hrt : BR.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e; exact (hends e).2.2.1
  have hct : BC.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e; exact (hends e).2.2.2
  constructor
  · intro r
    have heq := physical_network_midpoint_identity (hr.rowPairs a rowGap hrowGap) BR hrowTotal r
    rw [hrs, hrt] at heq
    rw [heq]
    exact hrow r
  · intro c
    have heq := physical_network_midpoint_identity (hc.columnPairs a colGap hcolGap) BC hcolTotal c
    rw [hcs, hct] at heq
    simp only [LayerPacking.rowSum_transpose] at heq
    rw [heq]
    exact hcol c

end
end Sude
