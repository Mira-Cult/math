import Sude.FWSelectedSparePairCells
import Sude.FWSelectedSpareDiagonalBound
import Sude.SparePairedCellPermutation
import Sude.SingleMoveLineBound

/-! Rebalance the designated latent spare cells of one supplied square.  This
does not construct a CY completion, transport a flow or prove a prime target. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- On one supplied square, paired swaps supported in its spare rectangle cells
balance their two diagonal sums within X and change each row/column by at most X.
The geometry, choice and selected P are supplied; no other witness is identified. -/
theorem fw_selected_spare_rebalance {n P : ℕ} (hnlo : 19485 ≤ n) (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    let X : ℝ := poolMaximum n
    ∃ σ : Equiv.Perm (Cell n),
      (∀ z ∉ spare, σ z = z) ∧
      |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans a) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans a) z : ℝ))| ≤ X ∧
      (∀ r, |(rowSum (σ.trans a) r : ℝ) - rowSum a r| ≤ X) ∧
      (∀ c, |(columnSum (σ.trans a) c : ℝ) - columnSum a c| ≤ X) := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  let cells := fwSelectedSparePairCell hP hnlo hs otherChoice
  let line : Bool × Fin n → Cell n → Prop := fun l z => if l.1 then z.1 = l.2 else z.2 = l.2
  have hX : (0 : ℝ) ≤ poolMaximum n := by positivity
  have hinj : Function.Injective cells := fw_selected_spare_pair_cell_injective hP hnlo hs otherChoice
  have hvalue : ∀ i b, 0 ≤ (entry a (cells (i,b)) : ℝ) ∧
      (entry a (cells (i,b)) : ℝ) ≤ poolMaximum n := by
    intro i b
    exact physical_entry_pool_range a _
  have hline : ∀ l x y, line l x → line l y → x ∈ Set.range cells → y ∈ Set.range cells → x = y := by
    rintro ⟨side,i⟩ x y hx hy ⟨u,rfl⟩ ⟨v,rfl⟩
    apply congrArg cells
    have hpair := fw_selected_spare_pair_line_injective hP hnlo hs otherChoice u v
    cases side with
    | false => exact hpair.2 (by simpa [line] using hx.trans hy.symm)
    | true => exact hpair.1 (by simpa [line] using hx.trans hy.symm)
  obtain ⟨σ, hoff, hpairs, hbal, hsingle⟩ :=
    spare_paired_cell_permutation cells hinj (fun z => (entry a z : ℝ)) (poolMaximum n : ℝ) hX hvalue line hline
  have hrange : Set.range cells ⊆ (spare : Set (Cell n)) := by
    rintro _ ⟨⟨x,b⟩,rfl⟩
    have hmem := fw_selected_spare_side_mem (n := n) hP b x
    have hsp := (fw_spare_rectangle_line_separation hP hs choice).2.2.2
    change cells (x,b) ∈ spare
    dsimp only [spare]
    rw [hsp]
    apply Finset.mem_image.mpr
    exact ⟨(fwSelectedSpareSideLabel hP b x,0), Finset.mem_product.mpr ⟨hmem,Finset.mem_univ _⟩, rfl⟩
  have houtside : ∀ z ∉ spare, σ z = z := by
    intro z hz
    apply hoff z
    intro h
    exact hz (hrange h)
  have himages := fw_selected_spare_pair_cell_images hP hnlo hs otherChoice
  have hmaininj : Function.Injective (fun i => cells (i,true)) := by
    intro i j h
    exact congrArg Prod.fst (hinj h)
  have hantiinj : Function.Injective (fun i => cells (i,false)) := by
    intro i j h
    exact congrArg Prod.fst (hinj h)
  have hdiag : |(∑ z ∈ spare ∩ mainCells n, (entry (σ.trans a) z : ℝ)) -
        (∑ z ∈ spare ∩ antiCells n, (entry (σ.trans a) z : ℝ))| ≤ (poolMaximum n : ℝ) := by
    rw [← himages.1, ← himages.2, Finset.sum_image, Finset.sum_image]
    · simpa [entry, Equiv.trans_apply, cells] using hbal
    · exact fun x _ y _ h => hantiinj h
    · exact fun x _ y _ h => hmaininj h
  refine ⟨σ, houtside, hdiag, ?_, ?_⟩
  · intro r
    have h := single_move_line_sum_bound (rowCells r) (fun z => (entry a z : ℝ)) σ
      (poolMaximum n : ℝ) hX (by intro z hz; exact ⟨(physical_entry_pool_range a z).1,
        (physical_entry_pool_range a z).2, (physical_entry_pool_range a (σ z)).1,
        (physical_entry_pool_range a (σ z)).2⟩)
      (by
        intro x hx y hy hxm hym
        apply hsingle (true,r) x y ?_ ?_ hxm hym
        · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx
          simpa [line] using (congrArg Prod.fst hv).symm
        · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
          simpa [line] using (congrArg Prod.fst hv).symm)
    have hrow1 : (∑ z ∈ rowCells r, (entry a (σ z) : ℝ)) = (rowSum (σ.trans a) r : ℝ) := by
      unfold rowCells rowSum
      rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.snd h)]
      simp [entry, Equiv.trans_apply]
    have hrow2 : (∑ z ∈ rowCells r, (entry a z : ℝ)) = (rowSum a r : ℝ) := by
      unfold rowCells rowSum
      rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.snd h)]
      simp
    rw [hrow1, hrow2] at h
    exact h
  · intro c
    have h := single_move_line_sum_bound (columnCells c) (fun z => (entry a z : ℝ)) σ
      (poolMaximum n : ℝ) hX (by intro z hz; exact ⟨(physical_entry_pool_range a z).1,
        (physical_entry_pool_range a z).2, (physical_entry_pool_range a (σ z)).1,
        (physical_entry_pool_range a (σ z)).2⟩)
      (by
        intro x hx y hy hxm hym
        apply hsingle (false,c) x y ?_ ?_ hxm hym
        · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hx
          simpa [line] using (congrArg Prod.snd hv).symm
        · obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hy
          simpa [line] using (congrArg Prod.snd hv).symm)
    have hcol1 : (∑ z ∈ columnCells c, (entry a (σ z) : ℝ)) = (columnSum (σ.trans a) c : ℝ) := by
      unfold columnCells columnSum
      rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.fst h)]
      simp [entry, Equiv.trans_apply]
    have hcol2 : (∑ z ∈ columnCells c, (entry a z : ℝ)) = (columnSum a c : ℝ) := by
      unfold columnCells columnSum
      rw [Finset.sum_image (by intro x _ y _ h; exact congrArg Prod.fst h)]
      simp
    rw [hcol1, hcol2] at h
    exact h

end
end Sude
