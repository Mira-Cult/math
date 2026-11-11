import Sude.FWBridgeWideReferenceDiagonalBound
import Sude.FWSeedReferenceDiagonalBound
import Sude.FWGrowthCYDiagonalDifference
import Sude.FWFirstBandActiveDiagonalNumericInvoice
import Sude.FWSelectedFullDiagonalCounts
import Sude.FWProjectedCYSpareOriginalActiveOutputGrids
import Sude.FWThetaFreshSpareOutputGrids

/-! Complete active-role diagonal difference bound (`< 27 * poolMaximum n`)
for the first FW band (`19485 ≤ n ≤ 21248`) on the original network reference
and on the spare-rebalanced CY square `σ.trans cy`. -/
namespace Sude
noncomputable section
open scoped BigOperators
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

private theorem disjoint_image_of_injective_sum {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) (hinj : Function.Injective (Sum.elim f g)) :
    Disjoint (Finset.univ.image f) (Finset.univ.image g) ∧ Function.Injective f := by
  refine ⟨Finset.disjoint_left.mpr ?_, ?_⟩
  · intro z hzf hzg
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hzf
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hzg
    have h : Sum.elim f g (Sum.inl a) = Sum.elim f g (Sum.inr b) := hb.symm
    exact nomatch hinj h
  · intro a₁ a₂ h
    have h' : Sum.elim f g (Sum.inl a₁) = Sum.elim f g (Sum.inl a₂) := h
    exact Sum.inl.inj (hinj h')

private theorem image_sum_univ_eq {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq γ]
    (f : α → γ) (g : β → γ) :
    Finset.univ.image (Sum.elim f g) = Finset.univ.image f ∪ Finset.univ.image g := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨x, rfl⟩
    cases x with
    | inl a => exact Or.inl ⟨a, rfl⟩
    | inr b => exact Or.inr ⟨b, rfl⟩
  · rintro (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨Sum.inl a, rfl⟩
    · exact ⟨Sum.inr b, rfl⟩

/-- The four-family active role set has equal main- and anti-diagonal
cardinalities under `fwSelectedThetaChoice`. -/
theorem fw_selected_active_roles_diagonal_card_eq {n : ℕ}
    (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (roles : Finset (Cell n))
    (hroles : roles = fwGrowthEarlyRoleCells f.hrect f.hseedrect f.hwide f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.hbr f.hbc f.sr f.sc f.hsr f.hsc f.wr f.wc f.hwr f.hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        f.hoff f.hs (fwSelectedThetaChoice hnlo otherChoice) f.gr f.gc f.hgr f.hgc)) :
    (mainCells n ∩ roles).card = (antiCells n ∩ roles).card := by
  classical
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let full := fwThetaFamilyFull f
  let spare := packedRectangleSupport f.hs choice \ activeRectangleSupport f.hs choice
    (fwActiveRectangleLabels n f.stages.length f.stageCap)
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hsub : roles ⊆ full := by
    rw [hroles]
    simpa only [full, fwThetaFamilyFull] using hgeom.2.2.1
  have hspare : full \ roles = spare := by
    rw [hroles]
    simpa only [full, spare, fwThetaFamilyFull] using hgeom.2.2.2.1
  have hdis : Disjoint roles spare := by
    rw [← hspare]
    exact Finset.disjoint_sdiff
  have hunion : roles ∪ spare = full := by
    rw [← hspare]
    exact Finset.union_sdiff_of_subset hsub
  have hsplit (L : Finset (Cell n)) :
      (L ∩ full).card = (L ∩ roles).card + (L ∩ spare).card := by
    rw [← hunion, Finset.inter_union_distrib_left, Finset.card_union_of_disjoint
      (hdis.mono Finset.inter_subset_right Finset.inter_subset_right)]
  have hfull := fw_selected_full_diagonal_counts hnlo otherChoice f
  have hsp := fw_selected_spare_diagonal_bound hnlo f.stageCap f.hs otherChoice f.ordered
  have hfull_eq : (mainCells n ∩ full).card = (antiCells n ∩ full).card := by
    rw [Finset.inter_comm (mainCells n), Finset.inter_comm (antiCells n)]
    exact hfull.1.trans hfull.2.1.symm
  have hsp_eq : (mainCells n ∩ spare).card = (antiCells n ∩ spare).card := by
    rw [Finset.inter_comm (mainCells n), Finset.inter_comm (antiCells n)]
    exact hsp.1.trans hsp.2.1.symm
  rw [hsplit (mainCells n), hsplit (antiCells n), hsp_eq] at hfull_eq
  exact Nat.add_right_cancel hfull_eq

/-- Partition a line-filtered sum over `roles` into the four disjoint family sums. -/
theorem fw_four_family_roles_line_sum_partition {n : ℕ}
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (roles : Finset (Cell n))
    (hroles : roles = fwGrowthEarlyRoleCells f.hrect f.hseedrect f.hwide f.hs
      choice
      f.br f.bc f.hbr f.hbc f.sr f.sc f.hsr f.hsc f.wr f.wc f.hwr f.hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        f.hoff f.hs choice f.gr f.gc f.hgr f.hgc))
    (L : Finset (Cell n)) (v : Cell n → ℝ) :
    let bridge := fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
    let seed := fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc
    let wide := fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    (∑ z ∈ L ∩ roles, v z) =
      (∑ z ∈ (Finset.univ.image bridge).filter (fun z => z ∈ L), v z) +
      (∑ z ∈ (Finset.univ.image seed).filter (fun z => z ∈ L), v z) +
      (∑ z ∈ (Finset.univ.image wide).filter (fun z => z ∈ L), v z) +
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ L), v z) := by
  classical
  dsimp only
  let bridge := fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc
  let seed := fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc
  let wide := fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
  obtain ⟨hinj4, himage4⟩ := fw_four_family_pair_cells_injective f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  dsimp only [fwFourFamilyPairCells] at hinj4
  obtain ⟨hdis_g, hinj3⟩ := disjoint_image_of_injective_sum _ growth hinj4
  obtain ⟨hdis_w, hinj2⟩ := disjoint_image_of_injective_sum _ wide hinj3
  obtain ⟨hdis_s, _⟩ := disjoint_image_of_injective_sum bridge seed hinj2
  rw [image_sum_univ_eq] at hdis_w hdis_g
  rw [image_sum_univ_eq] at hdis_g
  have hcov : ((Finset.univ.image bridge ∪ Finset.univ.image seed) ∪ Finset.univ.image wide) ∪
      Finset.univ.image growth = roles := by
    rw [hroles]
    exact fw_four_family_pair_cells_cover_roles f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
  have hcomm : L ∩ roles = roles.filter (fun z => z ∈ L) := by
    rw [Finset.inter_comm, Finset.filter_mem_eq_inter]
  rw [hcomm, ← hcov,
      Finset.filter_union,
      Finset.sum_union (hdis_g.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Finset.filter_union,
      Finset.sum_union (hdis_w.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)),
      Finset.filter_union,
      Finset.sum_union (hdis_s.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _))]

/-- The centered active-role diagonal difference on `oldReference`, plus `(7/2) * X`,
is strictly less than `27 * X` for the first FW band `19485 ≤ n ≤ 21248`. -/
theorem fw_first_band_active_reference_diagonal_bound {n : ℕ}
    (lower : RSIndexLower) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (intermediate oldReference : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (g : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice) f)
    (fresh : FWThetaFreshWideProjection f intermediate oldReference)
    (ν : ℝ) :
    |(∑ z ∈ mainCells n ∩ roles, ((entry oldReference z : ℝ) - ν)) -
      (∑ z ∈ antiCells n ∩ roles, ((entry oldReference z : ℝ) - ν))| +
      (7 / 2 : ℝ) * (poolMaximum n : ℝ) < 32 * (poolMaximum n : ℝ) := by
  classical
  let choice := fwSelectedThetaChoice hnlo otherChoice
  have hcard_eq := fw_selected_active_roles_diagonal_card_eq hnlo otherChoice f roles net.roles_eq
  have hcenter_cancel :
      (∑ z ∈ mainCells n ∩ roles, ((entry oldReference z : ℝ) - ν)) -
        (∑ z ∈ antiCells n ∩ roles, ((entry oldReference z : ℝ) - ν)) =
      (∑ z ∈ mainCells n ∩ roles, (entry oldReference z : ℝ)) -
        (∑ z ∈ antiCells n ∩ roles, (entry oldReference z : ℝ)) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hcard_eq]
    ring
  rw [hcenter_cancel]
  have hpart_main := fw_four_family_roles_line_sum_partition choice f roles net.roles_eq
    (mainCells n) (fun z => (entry oldReference z : ℝ))
  have hpart_anti := fw_four_family_roles_line_sum_partition choice f roles net.roles_eq
    (antiCells n) (fun z => (entry oldReference z : ℝ))
  dsimp only at hpart_main hpart_anti
  rw [hpart_main, hpart_anti]
  have hbw := fw_bridge_wide_reference_diagonal_differences hnlo otherChoice f p intermediate oldReference roles net fresh
  dsimp only at hbw
  let hrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).1
  let hseedrect := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.1
  let hwide := (fw_reserved_wide_rectangle_capacity (P₀ := 254) hnlo (by decide) (by decide)).2.2.1
  let hmax := fw_growth_offset_rectangle_capacity (n := n) (P := 238) (P₀ := 254) (by decide)
  have hL : 3 ≤ fwJointRectangleCount n 254 := by
    simp [fwJointRectangleCount]
    omega
  have hseed_bound := fw_seed_reference_first_band_diagonal_difference lower hnlo hnhi
    hrect hseedrect hL (fwWideRectangleChoice hwide (fwGrowthRectangleChoice hmax otherChoice))
    f p oldReference roles net
  dsimp only at hseed_bound
  have hseed_supp_main := fw_seed_reference_diagonal_support choice f (mainCells n)
    (fun z hz => Finset.mem_union_left _ hz)
  have hseed_supp_anti := fw_seed_reference_diagonal_support choice f (antiCells n)
    (fun z hz => Finset.mem_union_right _ hz)
  change |(∑ z ∈ activeRectangleSupport f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect)) ∩ mainCells n,
      (entry oldReference z : ℝ)) -
    (∑ z ∈ activeRectangleSupport f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect)) ∩ antiCells n,
      (entry oldReference z : ℝ))| ≤ 3 * (poolMaximum n : ℝ) at hseed_bound
  rw [← hseed_supp_main, ← hseed_supp_anti] at hseed_bound
  have hgrowth_bound := fw_growth_cy_diagonal_difference (by omega : 0 < n) choice f p oldReference roles net g
    oldReference (fun _ _ => rfl)
  dsimp only at hgrowth_bound
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100 : ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hnum := fw_all_bands_active_diagonal_numeric_invoice hnlo hnhi hX
  dsimp only at hnum
  obtain ⟨hb1, hb2⟩ := abs_lt.mp hbw.1
  obtain ⟨hw1, hw2⟩ := abs_lt.mp hbw.2
  obtain ⟨hs1, hs2⟩ := abs_le.mp hseed_bound
  obtain ⟨hg1, hg2⟩ := abs_le.mp hgrowth_bound
  have htri :
      |((∑ z ∈ (Finset.univ.image (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc)).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
          (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc)).filter (fun z => z ∈ mainCells n), (entry oldReference z : ℝ))) -
       ((∑ z ∈ (Finset.univ.image (fwBridgePhysicalPairCells f.hrect f.hs choice f.br f.bc f.hbr f.hbc)).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (fwSeedExistingPairCells f.hseedrect f.hs choice f.sr f.sc f.hsr f.hsc)).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ)) +
        (∑ z ∈ (Finset.univ.image (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
          (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) f.hoff f.hs choice f.gr f.gc f.hgr f.hgc)).filter (fun z => z ∈ antiCells n), (entry oldReference z : ℝ)))| <
      2 * ((poolMaximum n : ℝ) * (23 / 924 : ℝ) * Real.sqrt (94 * Real.log (8 * (n : ℝ) + 8))) +
        (613256873 / 949132107 : ℝ) * (poolMaximum n : ℝ) +
        3 * (poolMaximum n : ℝ) +
        2 * ((poolMaximum n : ℝ) * (2 / 235 : ℝ) * Real.sqrt ((54 * ((n / 450 : ℕ) : ℝ) + 4) * Real.log (8 * (n : ℝ) + 8))) +
        2 * Real.sqrt ((3 / 2 : ℝ) * (3 * ((n / 450 : ℕ) : ℝ)) * ((64 / 235 : ℝ) * (poolMaximum n : ℝ))^2 * Real.log 16) +
        (((n : ℝ) + 7) / (6 * ((n : ℝ) + 6))) * (poolMaximum n : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  linarith

/-- On the spare-rebalanced CY square `σ.trans cy` of `fw_projected_cy_spare_original_active_output_grids`,
the diagonal difference is strictly less than `27 * poolMaximum n`. -/
theorem fw_projected_cy_spare_first_band_diagonal_difference_lt_27
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n))
    (intermediate oldReference : Cell n ≃ Fin (n * n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (g : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice) f)
    (fresh : FWThetaFreshWideProjection f intermediate oldReference)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let prior := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd
      otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    let cy := Classical.choose prior
    let σ := Classical.choose (Classical.choose_spec prior)
    |(mainSum (σ.trans cy) : ℝ) - (antiSum (σ.trans cy) : ℝ)| < 32 * (poolMaximum n : ℝ) := by
  dsimp only
  have horig := (fw_projected_cy_spare_original_active_difference bmor lower upper hnlo hnhi hodd
    otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget).2
  have hact := fw_first_band_active_reference_diagonal_bound lower hnlo hnhi
    otherChoice f p intermediate oldReference roles net g fresh
    (centralEntriesMean (actualUnusedPool oldReference (fwThetaFamilyFull f)) centralPoolValue)
  exact lt_of_le_of_lt horig hact

end
end Sude
