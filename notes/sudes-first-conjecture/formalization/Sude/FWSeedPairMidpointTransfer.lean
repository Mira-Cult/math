import Sude.FWSeedOffsetActualDiagonal
import Sude.FWSeedNetworkMatching
import Sude.MarkedPairMidpointTransfer

/-! Transfer retained-seed pair midpoints to a supplied fresh reference using
explicit pair-sum preservation. Ordered gaps and entry-sum orientations are
not preserved by this lemma. -/
namespace Sude
noncomputable section

/-- Every actual seed pair lies in the packed rectangle reservation or is an
actual row or transposed-column joint network pair, side for side. -/
theorem fw_seed_pair_network_coverage {n L : ℕ}
    (hseed : 5*(4*6) + 16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (j : Fin 16) (i : Fin (6*(n+8))) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    (∀ side, cells ((j,i),side) ∈ packedRectangleSupport hs choice) ∨
    (∃ k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n,
      ∀ side, cells ((j,i),side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k side) ∨
    (∃ k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n,
      ∀ side, cells ((j,i),side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k side).swap) := by
  classical
  dsimp only
  let hf : (4*6)*2 + 2*(3*n) ≤ 6*(n+8) := by omega
  let hd : (4*6)*2 ≤ 6*(n+8) := by omega
  let he : (4*6)*2 + 2*(3*n) = 6*(n+8) := by omega
  obtain ⟨p, hp⟩ := (prefixStagePairSlot_bijective (d := 6) (layers := 3) (n := n) hf hd he).2 i
  subst i
  cases p with
  | inl v =>
    rcases v with ⟨rect, pair⟩
    left
    intro side
    change fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
      ((j,prefixDiagonalPairIndex hd (rect,pair)),side) ∈ _
    rw [fw_seed_existing_rectangle_cell]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  | inr v =>
    rcases v with ⟨network,k,e⟩
    fin_cases network
    · right; left
      exact ⟨(fwSeedJointLayerIndex br sr wr gr hsr j k,e),
        fun side => fw_seed_existing_joint_row_match hseed hs choice br sr wr gr sc hsr hsc j k e side⟩
    · right; right
      exact ⟨(fwSeedJointLayerIndex bc sc wc gc hsc j k,e),
        fun side => fw_seed_existing_joint_column_match hseed hs choice sr bc sc wc gc hsr hsc j k e side⟩

/-- Fixed rectangle cells and exact joint-network pair sums preserve the
midpoint of each physical seed pair on these same two squares. -/
theorem fw_seed_pair_midpoint_transfer {n L : ℕ}
    (hseed : 5*(4*6) + 16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (a b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ packedRectangleSupport hs choice, entry b c = entry a c)
    (hrow : ∀ k, entry b (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry b (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true) =
      entry a (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k false) +
        entry a (layerPairSlot (((br ++ sr) ++ wr) ++ gr) k true))
    (hcol : ∀ k, entry b ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry b ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap) =
      entry a ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k false).swap) +
        entry a ((layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k true).swap)) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    ∀ j i, (((entry b (cells ((j,i),false)) : ℝ) + entry b (cells ((j,i),true))) / 2) =
      (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2) := by
  classical
  dsimp only
  let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
  have hc : ∀ z : Fin 16 × Fin (6*(n+8)),
      (∀ side, cells (z,side) ∈ packedRectangleSupport hs choice) ∨
      (∃ (k : Fin ((((br ++ sr) ++ wr) ++ gr).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = layerPairSlot (((br ++ sr) ++ wr) ++ gr) k (if rev then !side else side)) ∨
      (∃ (k : Fin ((((bc ++ sc) ++ wc) ++ gc).length) × Fin n) (rev : Bool), ∀ side,
        cells (z,side) = (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) k (if rev then !side else side)).swap) := by
    rintro ⟨j,i⟩
    rcases fw_seed_pair_network_coverage hseed hs choice br sr wr gr bc sc wc gc hsr hsc j i with h | h | h
    · exact Or.inl h
    · obtain ⟨k,hk⟩ := h
      exact Or.inr (Or.inl ⟨k,false,by simpa using hk⟩)
    · obtain ⟨k,hk⟩ := h
      exact Or.inr (Or.inr ⟨k,false,by simpa using hk⟩)
  have hm := marked_pair_midpoint_preserved a b (packedRectangleSupport hs choice) cells
    (fun z => layerPairSlot (((br ++ sr) ++ wr) ++ gr) z.1 z.2)
    (fun z => (layerPairSlot (((bc ++ sc) ++ wc) ++ gc) z.1 z.2).swap)
    hfixed hrow hcol hc
  exact fun j i => hm (j,i)

/-- Fixed weights and fixed source-stage means preserve the centered seed
midpoint score. This does not preserve an ordered-gap orientation invoice. -/
theorem fw_seed_centered_midpoint_scores_transfer {n L : ℕ}
    (hseed : 5*(4*6) + 16*(4*6) ≤ L) (hs : 2*L+1 ≤ n)
    (choice : Fin L → Bool) (sr sc : List (LayerPacking.Layer n))
    (hsr : sr.length = 16*3) (hsc : sc.length = 16*3)
    (a b : Cell n ≃ Fin (n*n)) (w : Fin 16 × Fin (6*(n+8)) → ℝ) (μ : Fin 16 → ℝ)
    (hmid : ∀ j i,
      (((entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry b (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2) =
      (((entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),false)) : ℝ) +
          entry a (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc ((j,i),true))) / 2)) :
    let cells := fwSeedExistingPairCells hseed hs choice sr sc hsr hsc
    (∑ z : Fin 16 × Fin (6*(n+8)), w z *
      ((((entry b (cells (z,false)) : ℝ) + entry b (cells (z,true))) / 2) - μ z.1)) =
    ∑ z : Fin 16 × Fin (6*(n+8)), w z *
      ((((entry a (cells (z,false)) : ℝ) + entry a (cells (z,true))) / 2) - μ z.1) := by
  classical
  dsimp only
  apply Finset.sum_congr rfl
  rintro ⟨j,i⟩ _
  rw [hmid j i]

end
end Sude
