import Sude.CombinedPhysicalStageFamilies
import Sude.FWSeedGrowthPhysicalDisjoint
import Sude.FWSeedReallocationGrowthPreservation

/-! Actual supplied FW seed and growth stage cells on the same square. No
theta witness, numerical mean, line or diagonal bound is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- The supplied same-square FW seed and growth maps form one disjoint stage
family. Seed injection and value membership, trace pool membership, stock
separation and physical growth placement are explicit hypotheses. -/
theorem fw_combined_physical_stage_family
    {g n P L : ℕ} {initial final : Finset ℕ} {radius last : ℕ}
    {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6 * (n + 8)) initial radius final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (earlyValues : Finset ℕ) (hdis : Disjoint initial earlyValues)
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (offset : ℕ) (hoff : offset + P * (4 * 6) ≤ L) (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (a : Cell n ≃ Fin (n * n))
    (hseedInj : Function.Injective (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc))
    (hseedValues : ∀ x, entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) ∈ earlyValues)
    (hplaced : ∀ x : PrefixPhysicalInputs P 6 3 n,
      entry a (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc x) =
        (trace.poolValues hlen hpool (prefixPhysicalInput (by omega) (by omega) x)).val) :
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
    let cells := combinedPhysicalPairStageCells seed growth
    let means := Sum.elim (physicalStageMidpointAverage a seed) (physicalStageMidpointAverage a growth)
    Set.PairwiseDisjoint (Set.univ : Set (Fin 16 ⊕ Fin P)) cells ∧
    (∀ j, (cells j).card = 12 * (n + 8)) ∧
    (∀ j, (∑ c ∈ cells j, (entry a c : ℝ)) = ((12 * (n + 8) : ℕ) : ℝ) * means j) ∧
    (∀ S : Finset (Fin 16 ⊕ Fin P), S.biUnion cells ⊆ roles) := by
  classical
  dsimp only
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    offset hoff hs choice gr gc hgr hgc
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc)
  have hgrowthInj : Function.Injective growth :=
    (bt_growing_physical_stage_totals trace hlen hpool (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc a hplaced).1
  have hsep : Disjoint (Finset.univ.image seed) (Finset.univ.image growth) :=
    fw_seed_growth_physical_pair_images_disjoint trace hlen hpool earlyValues hdis
      hseed offset hoff hs choice sr sc gr gc hsr hsc hgr hgc a hseedValues hplaced
  have hseedRoles : Finset.univ.image seed ⊆ roles := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_union_left _ (fw_seed_existing_cells_mem_early hrect hseed hwide hs choice
      br bc hbr hbc sr sc hsr hsc wr wc hwr hwc x)
  have hgrowthRoles : Finset.univ.image growth ⊆ roles := by
    intro c hc
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hc
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(prefixPhysicalInputEquiv (P := P) (by omega) (by omega) (by omega)).symm x,
      Finset.mem_univ _, rfl⟩
  have hQ : 0 < 6 * (n + 8) := by omega
  have hfam := combined_physical_stage_family hQ a roles seed growth hseedInj hgrowthInj hsep hseedRoles hgrowthRoles
  dsimp only at hfam
  have heq : 2 * (6 * (n + 8)) = 12 * (n + 8) := by omega
  simpa only [heq] using hfam

end
end Sude
