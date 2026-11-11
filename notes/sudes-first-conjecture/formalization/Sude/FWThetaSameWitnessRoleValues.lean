import Sude.FWFourFamilyRoleCoverage
import Sude.FWPhysicalDoubleBlockCells
import Sude.FWWideRoleValueCoverage
import Sude.BTGrowingFootprintCoverage
import Sude.PermutedSeedPlacement
import Sude.FWWheelWitnessTraceStock

namespace Sude
noncomputable section

/-- Equality of each stage's value image implies equality of the full
indexed-family value image; the stage and slot types may be empty. -/
private theorem scratch_stagewise_images_eq {J I V : Type*} [Fintype J] [Fintype I] [DecidableEq V]
    (f g : J → I → V)
    (hstage : ∀ j, (Finset.univ.image (f j)) = Finset.univ.image (g j)) :
    (Finset.univ.image (fun x : J × I => f x.1 x.2)) =
      Finset.univ.image (fun x : J × I => g x.1 x.2) := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j,i⟩, hi⟩
    have h : v ∈ Finset.univ.image (f j) := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    rw [hstage j] at h
    obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp h
    exact ⟨(j,i'), hi'⟩
  · rintro ⟨⟨j,i⟩, hi⟩
    have h : v ∈ Finset.univ.image (g j) := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    rw [← hstage j] at h
    obtain ⟨i', _, hi'⟩ := Finset.mem_image.mp h
    exact ⟨(j,i'), hi'⟩
end
end Sude
namespace Sude
noncomputable section

/-- Stage image equality in the nested double-block index convention implies
equality of the whole family value image, including empty stage types. -/
private theorem scratch_doubleblock_stagewise_images_eq
    {J K P S V : Type*} [Fintype J] [Fintype K] [Fintype P] [Fintype S] [DecidableEq V]
    (f g : ((J × K × P) × S) → V)
    (hstage : ∀ j, (Finset.univ.image (fun x : (K × P) × S => f ((j,x.1.1,x.1.2),x.2))) =
      Finset.univ.image (fun x : (K × P) × S => g ((j,x.1.1,x.1.2),x.2))) :
    (Finset.univ.image f) = Finset.univ.image g := by
  classical
  ext v
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨j,k,p⟩,s⟩, hv⟩
    have h : v ∈ Finset.univ.image (fun x : (K × P) × S => f ((j,x.1.1,x.1.2),x.2)) :=
      Finset.mem_image.mpr ⟨((k,p),s), Finset.mem_univ _, hv⟩
    rw [hstage j] at h
    obtain ⟨⟨⟨k',p'⟩,s'⟩, _, hv'⟩ := Finset.mem_image.mp h
    exact ⟨((j,k',p'),s'), hv'⟩
  · rintro ⟨⟨⟨j,k,p⟩,s⟩, hv⟩
    have h : v ∈ Finset.univ.image (fun x : (K × P) × S => g ((j,x.1.1,x.1.2),x.2)) :=
      Finset.mem_image.mpr ⟨((k,p),s), Finset.mem_univ _, hv⟩
    rw [← hstage j] at h
    obtain ⟨⟨⟨k',p'⟩,s'⟩, _, hv'⟩ := Finset.mem_image.mp h
    exact ⟨((j,k',p'),s'), hv'⟩
end
end Sude
namespace Sude
noncomputable section

/-- A supplied source square's three actual family images are the supplied
bridge reservation, retained seeds, and matched-wide endpoint values. -/
private theorem scratch_base_bridge_seed_wide_images {n L : ℕ}
    (hrect : 5*(4*6) ≤ L) (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17)
    (blocks : List DoublePair) (hlen : blocks.length = (3*(n/450))*(3*(n+8)))
    (b : Cell n ≃ Fin (n*n))
    (hbd : ∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t,side)))
    (hbo : ∀ x, entry b (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hseedImage : Finset.univ.image (fun x => entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub)
    (hwp : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) :
    Finset.univ.image (fun x => entry b (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) =
      priorBridgeReservation ∅ (Finset.range 5) batches ∧
    Finset.univ.image (fun x => entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub ∧
    Finset.univ.image (fun x => entry b (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) =
      doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
  classical
  have hbridgeCells : Finset.univ.image (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) =
      Finset.univ.image (fun x : Fin (5*(4*6)) × Fin 4 =>
        packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect x.1,x.2)) ∪
      Finset.univ.image (fwBridgeLayerCells br bc hbr hbc) := by
    change Finset.univ.image (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc ∘ fwBlockPairIndex 5 n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex 5 n).surjective]
    exact fw_bridge_physical_pair_cells_image hrect hs choice br bc hbr hbc
  have hwideCells : Finset.univ.image (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) =
      Finset.univ.image (fwWidePhysicalCells hwide hs choice wr wc hwr hwc) := by
    change Finset.univ.image (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc ∘
      fwBlockPairIndex (3*(n/450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3*(n/450)) n).surjective]
    exact fw_wide_physical_pair_cells_image hwide hs choice wr wc hwr hwc
  have hb : (Finset.univ.image (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc)).image (entry b) =
      priorBridgeReservation ∅ (Finset.range 5) batches := by
    rw [hbridgeCells]
    exact fw_bridge_role_values_eq_reservation hrect hs choice batches hvalid br bc hbr hbc b hbd hbo
  have hw : (Finset.univ.image (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)).image (entry b) =
      doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
    rw [hwideCells]
    exact fw_wide_role_values_eq_batch hwide hs choice wr wc hwr hwc blocks hlen b hwp
  exact ⟨by simpa [Finset.image_image, Function.comp_def] using hb,
    hseedImage, by simpa [Finset.image_image, Function.comp_def] using hw⟩
end
end Sude
namespace Sude
noncomputable section

/-- The exact supplied square's stage-preserving placement has the trace's
entire indexed footprint image; no independent reallocation is introduced. -/
private theorem scratch_permuted_growth_role_values
    {g Q n P : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial R final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (cells : ((Fin P × Fin Q) × Bool) → Cell n) (a : Cell n ≃ Fin (n*n))
    (τ : Fin P → Equiv.Perm (Fin Q))
    (hplaced : ∀ x, entry a (cells x) = (trace.poolValues hlen hpool (stagePairPermutation τ x)).val) :
    (Finset.univ.image cells).image (entry a) =
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  have hfun : (entry a ∘ cells) =
      (fun x => (trace.poolValues hlen hpool x).val) ∘ stagePairPermutation τ := by
    funext x
    exact hplaced x
  rw [Finset.image_image, hfun, ← Finset.image_image,
    Finset.image_univ_of_surjective (stagePairPermutation τ).surjective]
  exact trace.poolValues_image_eq_footprints hlen hpool

/-- The same result over the FW growth role's original physical index set. -/
private theorem scratch_permuted_fw_growth_role_values
    {g Q n P d r L : ℕ} {initial final : Finset ℕ} {R last : ℕ}
    {stages : List BTSelectedStage} (trace : BTGrowingTrace g Q initial R final last stages)
    (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4*d)*2 + 2*(r*n) ≤ Q) (hdiag : (4*d)*2 ≤ Q)
    (hexact : (4*d)*2 + 2*(r*n) = Q)
    (offset : ℕ) (hoff : offset + P*(4*d) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = P*r) (hc : cols.length = P*r)
    (a : Cell n ≃ Fin (n*n)) (τ : Fin P → Equiv.Perm (Fin Q))
    (hplaced : ∀ x, entry a (btGrowingOffsetPairCells hfit hdiag hexact offset hoff hs choice rows cols hr hc x) =
      (trace.poolValues hlen hpool (stagePairPermutation τ x)).val) :
    (Finset.univ.image (btGrowingOffsetCells offset hoff hs choice rows cols hr hc)).image (entry a) =
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  rw [← bt_growing_offset_pair_cells_image hfit hdiag hexact offset hoff hs choice rows cols hr hc]
  exact scratch_permuted_growth_role_values trace hlen hpool _ a τ hplaced

end
end Sude
namespace Sude
noncomputable section

/-- Double-block bridge and wide maps, retained seed map, and growth pair map
cover exactly the supplied physical roles, without injection assumptions. -/
private theorem scratch_four_double_family_roles {n P L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3) :
    let offset := 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)
    let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
    let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      offset hoff hs choice gr gc hgr hgc
    ((Finset.univ.image bridge ∪ Finset.univ.image seed) ∪ Finset.univ.image wide) ∪
      Finset.univ.image growth =
    fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells offset hoff hs choice gr gc hgr hgc) := by
  classical
  dsimp only
  have hb : Finset.univ.image (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc) =
      Finset.univ.image (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc) := by
    change Finset.univ.image (fwBridgePhysicalPairCells hrect hs choice br bc hbr hbc ∘ fwBlockPairIndex 5 n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex 5 n).surjective]
  have hw : Finset.univ.image (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc) =
      Finset.univ.image (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc) := by
    change Finset.univ.image (fwWidePhysicalPairCells hwide hs choice wr wc hwr hwc ∘ fwBlockPairIndex (3*(n/450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3*(n/450)) n).surjective]
  rw [hb, hw]
  exact fw_four_family_pair_cells_cover_roles hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc
end
end Sude
namespace Sude
noncomputable section

/-- Assemble the four same-square value images over the exact physical-role
cover, then transfer the result to any reference with the same role image. -/
private theorem scratch_four_family_role_images {n : ℕ}
    {IB IS IW IG : Type*} [Fintype IB] [Fintype IS] [Fintype IW] [Fintype IG]
    (bridge : IB → Cell n) (seed : IS → Cell n) (wide : IW → Cell n) (growth : IG → Cell n)
    (roles : Finset (Cell n)) (final reference : Cell n ≃ Fin (n*n))
    (B S W G : Finset ℕ)
    (hroles : roles = ((Finset.univ.image bridge ∪ Finset.univ.image seed) ∪
      Finset.univ.image wide) ∪ Finset.univ.image growth)
    (hbridge : Finset.univ.image (fun x => entry final (bridge x)) = B)
    (hseed : Finset.univ.image (fun x => entry final (seed x)) = S)
    (hwide : Finset.univ.image (fun x => entry final (wide x)) = W)
    (hgrowth : Finset.univ.image (fun x => entry final (growth x)) = G)
    (href : roles.image (entry reference) = roles.image (entry final)) :
    roles.image (entry final) = ((B ∪ S) ∪ W) ∪ G ∧
      roles.image (entry reference) = ((B ∪ S) ∪ W) ∪ G := by
  classical
  have hfinal : roles.image (entry final) = ((B ∪ S) ∪ W) ∪ G := by
    rw [hroles, Finset.image_union, Finset.image_union, Finset.image_union]
    simp [Finset.image_image, Function.comp_def, hbridge, hseed, hwide, hgrowth]
  exact ⟨hfinal, href.trans hfinal⟩
end
end Sude
namespace Sude
noncomputable section

/-- Conditional adapter on the already selected same final/reference squares:
actual family value images plus their joint physical coverage yield the exact
FW early-and-growth role image on both squares. -/
private theorem scratch_actual_family_images_to_role_image {n P L g : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (batches : ℕ → List DoublePair) (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (blocks : List DoublePair)
    {initial lastStock : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (_trace : BTGrowingTrace g (6*(n+8)) initial R lastStock last stages) (hlen : stages.length = P)
    (final reference : Cell n ≃ Fin (n*n))
    (hbridge : Finset.univ.image (fun x => entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) =
      priorBridgeReservation ∅ (Finset.range 5) batches)
    (hseedImage : Finset.univ.image (fun x => entry final (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub)
    (hwideImage : Finset.univ.image (fun x => entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) =
      doubleBatchLow blocks ∪ doubleBatchHigh blocks)
    (hgrowth : Finset.univ.image (fun x => entry final (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x)) =
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
    (href : let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
      roles.image (entry reference) = roles.image (entry final)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    roles.image (entry final) = fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) ∧
    roles.image (entry reference) = fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  dsimp only
  let bridge := fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc
  let seed := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let growth := btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
    (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  have hcover : roles = ((Finset.univ.image bridge ∪ Finset.univ.image seed) ∪
      Finset.univ.image wide) ∪ Finset.univ.image growth := by
    symm
    exact scratch_four_double_family_roles hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc
      hbr hbc hsr hsc hwr hwc hgr hgc
  have hi := scratch_four_family_role_images bridge seed wide growth roles final reference
    (priorBridgeReservation ∅ (Finset.range 5) batches)
    (retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub)
    (doubleBatchLow blocks ∪ doubleBatchHigh blocks)
    (Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint))
    hcover hbridge hseedImage hwideImage hgrowth href
  simpa [fwWheelWitnessEarlyValues, fwBridgeSeedProtectedValues] using hi
end
end Sude
namespace Sude
noncomputable section
set_option maxRecDepth 32768

/-- Supplied theta-chain placements and image transfers identify the actual
role-value image on the same final and reference squares. -/
theorem fw_theta_same_witness_role_values {n P L g : ℕ}
    (hrect : 5*(4*6) ≤ L) (hseed : 5*(4*6)+16*(4*6) ≤ L)
    (hwide : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6) ≤ L)
    (hoff : 5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)+P*(4*6) ≤ L)
    (hs : 2*L+1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5*3) (hbc : bc.length = 5*3)
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (hwr : wr.length = (3*(n/450))*3) (hwc : wc.length = (3*(n/450))*3)
    (hgr : gr.length = P*3) (hgc : gc.length = P*3)
    (batches : ℕ → List DoublePair) (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17*(6*(n+8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17)
    (blocks : List DoublePair) (hlenBlocks : blocks.length = (3*(n/450))*(3*(n+8)))
    {initial lastStock : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g (6*(n+8)) initial R lastStock last stages)
    (hlen : stages.length = P) (hpool : ∀ v ∈ initial, v ∈ pool n)
    (b new final reference : Cell n ≃ Fin (n*n)) (τ : Fin P → Equiv.Perm (Fin (6*(n+8))))
    (hbd : ∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeDiagonalSlot n (t,side)))
    (hbo : ∀ x, entry b (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n ∅ batches hvalid (fwBridgeOrdinarySlot n x))
    (hseedBase : Finset.univ.image (fun x => entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub)
    (hwp : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlenBlocks.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2))
    (hbridgeStage : ∀ j, Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,x.1.1,x.1.2),x.2))) =
      Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry b (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc ((j,x.1.1,x.1.2),x.2))))
    (hwideStage : ∀ j, Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,x.1.1,x.1.2),x.2))) =
      Finset.univ.image (fun x : (Fin (3*(n+8)) × Fin 2) × Bool =>
      entry b (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc ((j,x.1.1,x.1.2),x.2))))
    (hseedNew : Finset.univ.image (fun x => entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub)
    (hbridgeFinal : ∀ x, entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x) =
      entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x))
    (hwideFinal : ∀ x, entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x) =
      entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x))
    (hseedFinal : ∀ x, entry final (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x) =
      entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x))
    (hplacedGrowth : ∀ x, entry final (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x) =
      (trace.poolValues hlen hpool (stagePairPermutation τ x)).val)
    (href : let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
      roles.image (entry reference) = roles.image (entry final)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    roles.image (entry final) = fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) ∧
    roles.image (entry reference) = fwWheelWitnessEarlyValues batches candidates hcard kept hsub blocks ∪
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
  classical
  have hbase := scratch_base_bridge_seed_wide_images hrect hseed hwide hs choice br bc sr sc wr wc
    hbr hbc hsr hsc hwr hwc batches hvalid candidates hcard kept hsub blocks hlenBlocks b hbd hbo hseedBase hwp
  have hbStage := scratch_doubleblock_stagewise_images_eq
    (fun x => entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x))
    (fun x => entry b (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) hbridgeStage
  have hwStage := scratch_doubleblock_stagewise_images_eq
    (fun x => entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x))
    (fun x => entry b (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) hwideStage
  have hbFinal : Finset.univ.image (fun x => entry final (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) =
      priorBridgeReservation ∅ (Finset.range 5) batches := by
    calc
      _ = Finset.univ.image (fun x => entry new (fwBridgePhysicalDoubleCells hrect hs choice br bc hbr hbc x)) := by
        apply Finset.image_congr
        intro x _
        exact hbridgeFinal x
      _ = _ := hbStage.trans hbase.1
  have hwFinal : Finset.univ.image (fun x => entry final (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) =
      doubleBatchLow blocks ∪ doubleBatchHigh blocks := by
    calc
      _ = Finset.univ.image (fun x => entry new (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc x)) := by
        apply Finset.image_congr
        intro x _
        exact hwideFinal x
      _ = _ := hwStage.trans hbase.2.2
  have hsFinal : Finset.univ.image (fun x => entry final (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) =
      retainedSeedEndpoints candidates 17 (6*(n+8)) 2 hcard kept hsub := by
    calc
      _ = Finset.univ.image (fun x => entry new (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc x)) := by
        apply Finset.image_congr
        intro x _
        exact hseedFinal x
      _ = _ := hseedNew
  have hgFinal := scratch_permuted_growth_role_values trace hlen hpool
    (btGrowingOffsetPairCells (Q := 6*(n+8)) (by omega) (by omega) (by omega)
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    final τ hplacedGrowth
  have hgFinal' : Finset.univ.image (fun x => entry final (btGrowingOffsetPairCells (Q := 6*(n+8))
      (by omega) (by omega) (by omega) (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc x)) =
      Finset.univ.biUnion (fun j : Fin P => (BTStageTrace.stageAt stages hlen j).footprint) := by
    simpa [Finset.image_image, Function.comp_def] using hgFinal
  exact scratch_actual_family_images_to_role_image hrect hseed hwide hoff hs choice br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc batches candidates hcard kept hsub blocks trace hlen final reference
    hbFinal hsFinal hwFinal hgFinal' href
end
end Sude
