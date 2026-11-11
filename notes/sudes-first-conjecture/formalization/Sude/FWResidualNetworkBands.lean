import Sude.FWBridgeWideNetworkMatching

/-! Exact seed and growth bands left after removing bridge and wide network
slots. This is set geometry only; no gap or cancellation claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Actual growth ordinary-network pair indices in the joint list. -/
def fwGrowthJointPairImage {n P : ℕ} (br sr wr gr : List (LayerPacking.Layer n))
    (hgr : gr.length = P * 3) : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :=
  Finset.univ.image (fun x : (Fin P × Fin 3) × Fin n =>
    (fwGrowthJointLayerIndex br sr wr gr hgr x.1.1 x.1.2, x.2))

/-- The supported joint network is exactly the four family bands. -/
theorem fw_joint_network_four_bands {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    Finset.univ.biUnion blocks =
      (fwBridgeJointPairImage br sr wr gr hbr ∪ fwSeedJointPairImage br sr wr gr hsr) ∪
      (fwWideJointPairImage br sr wr gr hwr ∪ fwGrowthJointPairImage br sr wr gr hgr) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨⟨k,e⟩, _, hx⟩ := Finset.mem_biUnion.mp hx
    rw [hblock] at hx
    obtain ⟨⟨tag, htag⟩, _, rfl⟩ := Finset.mem_image.mp hx
    rcases tag with ((j | j) | j) | j
    · simp only [Finset.mem_union]
      left; right
      exact Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, rfl⟩
    · simp only [Finset.mem_union]
      right; right
      exact Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, rfl⟩
    · have hj : j < 5 := by
        simpa [fwJointGridLabels, fwJointPreWideGridLabels] using htag
      simp only [Finset.mem_union]
      left; left
      exact Finset.mem_image.mpr ⟨((⟨j,hj⟩,k),e), Finset.mem_univ _, rfl⟩
    · simp only [Finset.mem_union]
      right; left
      exact Finset.mem_image.mpr ⟨((j,k),e), Finset.mem_univ _, rfl⟩
  · intro hx
    simp only [Finset.mem_union] at hx
    rcases hx with (hb | hs) | hw | hg
    · exact fw_bridge_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr blocks hblock hb
    · exact fw_seed_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr blocks hblock hs
    · exact fw_wide_joint_image_subset_blocks br sr wr gr hbr hsr hwr hgr blocks hblock hw
    · obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp hg
      apply Finset.mem_biUnion.mpr
      refine ⟨(k,e), Finset.mem_univ _, ?_⟩
      rw [hblock]
      let tag : FWJointGridTag n P := Sum.inl (Sum.inl (Sum.inr j))
      have htag : tag ∈ fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450)) := by
        simp [tag, fwJointGridLabels, fwJointPreWideGridLabels]
      exact Finset.mem_image.mpr ⟨⟨tag, htag⟩, Finset.mem_attach _ _, rfl⟩

/-- Family image membership locates the actual layer in its half-open band. -/
theorem fw_joint_image_bands {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (t : Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n) :
    (t ∈ fwBridgeJointPairImage br sr wr gr hbr → t.1.val < br.length) ∧
    (t ∈ fwSeedJointPairImage br sr wr gr hsr → br.length ≤ t.1.val ∧ t.1.val < br.length + sr.length) ∧
    (t ∈ fwWideJointPairImage br sr wr gr hwr → br.length + sr.length ≤ t.1.val ∧ t.1.val < br.length + sr.length + wr.length) ∧
    (t ∈ fwGrowthJointPairImage br sr wr gr hgr → br.length + sr.length + wr.length ≤ t.1.val) := by
  constructor
  · intro h
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp h
    have hi := (finProdFinEquiv (j,k)).isLt
    simp only [fwBridgeJointLayerIndex]
    omega
  constructor
  · intro h
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp h
    have hi := (finProdFinEquiv (j,k)).isLt
    simp only [fwSeedJointLayerIndex]
    omega
  constructor
  · intro h
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp h
    have hi := (finProdFinEquiv (j,k)).isLt
    simp only [fwWideJointLayerIndex]
    omega
  · intro h
    obtain ⟨⟨⟨j,k⟩,e⟩, _, rfl⟩ := Finset.mem_image.mp h
    simp only [fwGrowthJointLayerIndex]
    omega

/-- Removing the two movable bands leaves exactly the disjoint seed and
trace-growth ordinary slots. No assertion is made about their gaps. -/
theorem fw_joint_network_residual_seed_growth {n P : ℕ}
    (br sr wr gr : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (blocks : (Fin 3 × Fin n) → Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (hblock : ∀ edge, blocks edge =
      (fwJointGridLabels (fwJointPreWideGridLabels P) (3 * (n / 450))).attach.image
        (fun x => fwJointActualGridPairIndex br sr wr gr hbr hsr hwr hgr ((x,edge.1),edge.2))) :
    (Finset.univ.biUnion blocks) \ (fwBridgeJointPairImage br sr wr gr hbr ∪ fwWideJointPairImage br sr wr gr hwr) =
      fwSeedJointPairImage br sr wr gr hsr ∪ fwGrowthJointPairImage br sr wr gr hgr ∧
    Disjoint (fwSeedJointPairImage br sr wr gr hsr) (fwGrowthJointPairImage br sr wr gr hgr) := by
  classical
  have disj : Disjoint (fwSeedJointPairImage br sr wr gr hsr) (fwGrowthJointPairImage br sr wr gr hgr) := by
    apply Finset.disjoint_left.mpr
    intro x hs hg
    obtain ⟨_, hseed, _, hgrow⟩ := fw_joint_image_bands br sr wr gr hbr hsr hwr hgr x
    have hs' := hseed hs
    have hg' := hgrow hg
    omega
  refine ⟨?_, disj⟩
  rw [fw_joint_network_four_bands br sr wr gr hbr hsr hwr hgr blocks hblock]
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
  obtain ⟨hbridge, hseed, hwide, hgrowth⟩ := fw_joint_image_bands br sr wr gr hbr hsr hwr hgr x
  constructor
  · rintro ⟨((hb | hs) | hw | hg), hnB, hnW⟩ <;> tauto
  · rintro (hs | hg)
    · have hbounds := hseed hs
      have hnB : x ∉ fwBridgeJointPairImage br sr wr gr hbr := by
        intro hb; have := hbridge hb; omega
      have hnW : x ∉ fwWideJointPairImage br sr wr gr hwr := by
        intro hw; have := hwide hw; omega
      exact ⟨Or.inl (Or.inr hs), hnB, hnW⟩
    · have hbounds := hgrowth hg
      have hnB : x ∉ fwBridgeJointPairImage br sr wr gr hbr := by
        intro hb; have := hbridge hb; omega
      have hnW : x ∉ fwWideJointPairImage br sr wr gr hwr := by
        intro hw; have := hwide hw; omega
      exact ⟨Or.inr (Or.inr hg), hnB, hnW⟩

end
end Sude
