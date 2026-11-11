import Sude.ActiveSupportCenteredInvoice
import Sude.RoleValueReallocation
import Sude.ActualUnusedRoleImageTransport

/-! A fresh centered reference and supplied-flow outcomes preserve a larger
keepout value image and its actual unused pool. No theta witness or stagewise
concentration transfer is asserted. -/
namespace Sude
noncomputable section

/-- Equal active value images and agreement outside the active set preserve
both the larger full keepout value image and its actual unused pool. -/
theorem full_keepout_value_image_and_unused_eq {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (active full : Finset (Cell n))
    (hsub : active ⊆ full) (hfixed : ∀ c ∉ active, entry b c = entry a c)
    (himage : active.image (entry b) = active.image (entry a)) :
    full.image (entry b) = full.image (entry a) ∧
      actualUnusedPool b full = actualUnusedPool a full := by
  have hfull := role_value_image_preserved full active (entry a) (entry b) hsub
    (fun c _ hc => hfixed c hc) himage
  exact ⟨hfull, actualUnusedPool_eq_of_role_value_image_eq b a full hfull⟩

/-- The newly constructed reference and all supplied-flow outcomes preserve the
larger full keepout value image and its actual unused pool, in addition to the
active-support, invoice, flow and placement guarantees. -/
theorem twoNetworks_centered_invoice_preserves_full_unused_pool {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved active full : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (hrowActive : LayerPacking.layersSupport rows ⊆ active)
    (hcolActive : LayerPacking.transposeCells (LayerPacking.layersSupport cols) ⊆ active)
    (hactiveFull : active ⊆ full)
    (rowGap : Fin rows.length → Fin n → ℕ) (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (BR : CenteredNetwork Er (Fin rows.length × Fin n) (hr.rowPairs a rowGap hrowGap))
    (BC : CenteredNetwork Ec (Fin cols.length × Fin n) (hc.columnPairs a colGap hcolGap)) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      TwoNetworkReferenceInvoice a b₀ rows cols hr hc rowGap colGap hrowGap hcolGap BR BC ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      (∀ c ∉ active, entry b₀ c = entry a c) ∧
      active.image (entry b₀) = active.image (entry a) ∧
      full.image (entry b₀) = full.image (entry a) ∧
      actualUnusedPool b₀ full = actualUnusedPool a full ∧
      Set.range (entry b₀) = pool n ∧ Function.Injective (entry b₀) ∧
      (∀ tr : Er → ℤ, (∀ e, (2 : ℤ) ∣ tr e) →
        (∀ e, -(evenGridCenter (BR.radius e) : ℤ) ≤ tr e) →
        (∀ e, tr e ≤ evenGridCenter (BR.radius e)) →
        ∀ tc : Ec → ℤ, (∀ e, (2 : ℤ) ∣ tc e) →
        (∀ e, -(evenGridCenter (BC.radius e) : ℤ) ≤ tc e) →
        (∀ e, tc e ≤ evenGridCenter (BC.radius e)) →
        ∃ b : Cell n ≃ Fin (n * n),
          (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
            ∑ e : Er, edgeTransfer BR.source BR.target tr e r) ∧
          (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
            ∑ e : Ec, edgeTransfer BC.source BC.target tc e c) ∧
          mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
          (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
          (∀ c ∉ active, entry b c = entry a c) ∧
          active.image (entry b) = active.image (entry a) ∧
          full.image (entry b) = full.image (entry a) ∧
          actualUnusedPool b full = actualUnusedPool a full ∧
          Set.range (entry b) = pool n ∧ Function.Injective (entry b)) := by
  obtain ⟨b₀, hinvoice, hm, ha, hfixed, houtside, himage, hpool, hinj, hflows⟩ :=
    twoNetworks_centered_invoice_preserves_active_values a reserved active rows cols hr hc
      hrowActive hcolActive rowGap colGap hrowGap hcolGap BR BC
  have hfull := full_keepout_value_image_and_unused_eq a b₀ active full hactiveFull houtside himage
  refine ⟨b₀, hinvoice, hm, ha, hfixed, houtside, himage, hfull.1, hfull.2, hpool, hinj, ?_⟩
  intro tr hre hrl hrh tc hce hcl hch
  obtain ⟨b, hrows, hcols, hm', ha', hfixed', houtside', himage', hpool', hinj'⟩ :=
    hflows tr hre hrl hrh tc hce hcl hch
  have hfull' := full_keepout_value_image_and_unused_eq a b active full hactiveFull houtside' himage'
  exact ⟨b, hrows, hcols, hm', ha', hfixed', houtside', himage', hfull'.1, hfull'.2, hpool', hinj'⟩

end
end Sude
