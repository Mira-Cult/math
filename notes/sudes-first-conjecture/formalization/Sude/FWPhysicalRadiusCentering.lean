import Sude.FWRadiusCenteringAny
import Sude.FWCenteredFlowInvoice

/-! Apply the radius-centering bound to the actual reference square and both
physical networks retained by the supplied invoice. The algebraic reference
has not yet been identified with the actual physical midpoint sum. -/
namespace Sude
noncomputable section

theorem fw_reference_invoice_radius_bounds {n : ℕ}
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
    (hinvoice : TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC) :
    (∀ r, |2 * (rowSum b₀ r : ℤ) - (2 * (rowSum a r : ℤ) +
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (BR.radius e : ℤ)) e r)| ≤ 9) ∧
    (∀ c, |2 * (columnSum b₀ c : ℤ) - (2 * (columnSum a c : ℤ) +
      ∑ e : Fin 3 × Fin n, edgeTransfer Prod.snd (fun e => p e.1 e.2)
        (fun e => (BC.radius e : ℤ)) e c)| ≤ 9) := by
  obtain ⟨_, _, _, _, _, _, _, _, hrows, hcols⟩ := hinvoice
  have hrs : BR.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e
    exact (hends e).1
  have hcs : BC.source = (fun e : Fin 3 × Fin n => e.2) := by
    funext e
    exact (hends e).2.1
  have hrt : BR.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e
    exact (hends e).2.2.1
  have hct : BC.target = (fun e : Fin 3 × Fin n => p e.1 e.2) := by
    funext e
    exact (hends e).2.2.2
  rw [hrs, hrt] at hrows
  rw [hcs, hct] at hcols
  constructor
  · exact fw_three_permutation_centered_invoice_any p BR.radius
      (fun r => rowSum a r) (fun r => rowSum b₀ r) hrows
  · exact fw_three_permutation_centered_invoice_any p BC.radius
      (fun c => columnSum a c) (fun c => columnSum b₀ c) hcols

end
end Sude
