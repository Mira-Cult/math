import Sude.FWBridgeFiveSequential
import Sude.BridgePhysical

/-! Actual FW stage/block endpoint indexing; no physical placement. -/
namespace Sude
noncomputable section

/-- The selected block at a nominal FW stage and within-stage index. -/
def fwBridgeStageBlock (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (j : Fin 5) (i : Fin (3 * (n + 8))) : DoublePair :=
  (batches j).get ⟨i, by rw [(hvalid j j.isLt).1.1]; exact i.isLt⟩

theorem fwBridgeStageBlock_mem (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (j : Fin 5) (i : Fin (3 * (n + 8))) :
    fwBridgeStageBlock n initial batches hvalid j i ∈ batches j := by
  apply List.get_mem

theorem fwBridgeStageBlock_valid (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (j : Fin 5) (i : Fin (3 * (n + 8))) :
    (fwBridgeStageBlock n initial batches hvalid j i).valid
      (fwBridgeLowStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) \ initial)
      (fwBridgeHighStock (poolMaximum n) (fwBridgeRadius (poolMaximum n) j) \ initial) :=
  (hvalid j j.isLt).1.2.1 _ (fwBridgeStageBlock_mem n initial batches hvalid j i)

/-- All low entries in an FW source window lie below all high entries of
that stage. -/
theorem fw_bridge_stocks_order (X R : ℝ) (hX : 0 < X) (hR : 0 < R) :
    ∀ a ∈ fwBridgeLowStock X R, ∀ b ∈ fwBridgeHighStock X R, a < b := by
  intro a ha b hb
  have hg := fw_bridge_window_geometry X R hX hR
  have ha' := (mem_apInterval_iff (fwBridgeLowStart X R) (fwBridgeLowEnd X R) 2 1
    (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) a).mp ha
  have hb' := (mem_apInterval_iff (fwBridgeHighStart X R) (fwBridgeHighEnd X R) 2 1
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b).mp hb
  exact (fw_bridge_cross_gap X R hX hR a b ⟨ha'.2.1, ha'.2.2.1⟩
    ⟨hb'.2.1, hb'.2.2.1⟩).1

/-- Four endpoint slots per selected block in the original rectangle order. -/
def fwBridgeStageEndpoint (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (x : (Fin 5 × Fin (3 * (n + 8))) × Fin 4) : ℕ :=
  (fwBridgeStageBlock n initial batches hvalid x.1.1 x.1.2).endpoint x.2

/-- All nominal FW endpoint slots refer to distinct values. This uses
within-stage block disjointness and avoidance of each actual prior
reservation, not any physical cell assignment. -/
theorem fwBridgeStageEndpoint_injective (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j) :
    Function.Injective (fwBridgeStageEndpoint n initial batches hvalid) := by
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hcross : ∀ (j j' : Fin 5) (i i' : Fin (3 * (n + 8))), j ≠ j' →
      Disjoint (fwBridgeStageBlock n initial batches hvalid j i).footprint
        (fwBridgeStageBlock n initial batches hvalid j' i').footprint := by
    intro j j' i i' hne
    have hforward : ∀ (u v : Fin 5) (a b : Fin (3 * (n + 8))), u < v →
        Disjoint (fwBridgeStageBlock n initial batches hvalid u a).footprint
          (fwBridgeStageBlock n initial batches hvalid v b).footprint := by
      intro u v a b huv
      have hprior : (fwBridgeStageBlock n initial batches hvalid u a).footprint ⊆
          priorBridgeReservation initial (Finset.range v) batches := by
        apply (doublePair_footprint_subset_batch (batches u) _
          (fwBridgeStageBlock_mem n initial batches hvalid u a)).trans
        exact priorBridgeReservation_contains_batch initial (Finset.range v) batches u
          (Finset.mem_range.mpr huv)
      have hav := (hvalid v v.isLt).2.2.1 _ (fwBridgeStageBlock_mem n initial batches hvalid v b)
      exact (Disjoint.mono_right hprior hav).symm
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hforward j j' i i' hlt
    · exact (hforward j' j i' i hgt).symm
  rintro ⟨⟨j, i⟩, side⟩ ⟨⟨j', i'⟩, side'⟩ heq
  change (fwBridgeStageBlock n initial batches hvalid j i).endpoint side =
    (fwBridgeStageBlock n initial batches hvalid j' i').endpoint side' at heq
  by_cases hj : j = j'
  · subst j'
    by_cases hi : i = i'
    · subst i'
      have hR := fw_bridge_nominal_radius_pos (poolMaximum n) hX j j.isLt
      have horder := fw_bridge_stocks_order (poolMaximum n)
        (fwBridgeRadius (poolMaximum n) j) hX hR
      have hv := fwBridgeStageBlock_valid n initial batches hvalid j i
      have hv' := DoublePair.valid_mono hv Finset.sdiff_subset Finset.sdiff_subset
      have hs : side = side' := DoublePair.endpoint_injective _ _ _ horder hv' heq
      cases hs
      rfl
    · let p : Fin (batches j).length := ⟨i, by rw [(hvalid j j.isLt).1.1]; exact i.isLt⟩
      let q : Fin (batches j).length := ⟨i', by rw [(hvalid j j.isLt).1.1]; exact i'.isLt⟩
      have hpq : p ≠ q := by
        intro he
        apply hi
        apply Fin.ext
        exact congrArg (fun z : Fin (batches j).length => z.val) he
      have hpair := (hvalid j j.isLt).1.2.2.1
      have hd : Disjoint (fwBridgeStageBlock n initial batches hvalid j i).footprint
          (fwBridgeStageBlock n initial batches hvalid j i').footprint := by
        change Disjoint ((batches j).get p).footprint ((batches j).get q).footprint
        rcases lt_or_gt_of_ne hpq with hlt | hgt
        · exact hpair.rel_get_of_lt hlt
        · exact (hpair.rel_get_of_lt hgt).symm
      have hx := DoublePair.endpoint_mem (fwBridgeStageBlock n initial batches hvalid j i) side
      have hy := DoublePair.endpoint_mem (fwBridgeStageBlock n initial batches hvalid j i') side'
      rw [← heq] at hy
      exact False.elim (Finset.disjoint_left.mp hd hx hy)
  · have hd := hcross j j' i i' hj
    have hx := DoublePair.endpoint_mem (fwBridgeStageBlock n initial batches hvalid j i) side
    have hy := DoublePair.endpoint_mem (fwBridgeStageBlock n initial batches hvalid j' i') side'
    rw [← heq] at hy
    exact False.elim (Finset.disjoint_left.mp hd hx hy)

/-- Each indexed endpoint is a prescribed pool value outside the original
reservation. The BMOR and RS premises enter only through the established
source-window pool membership theorem. -/
theorem fwBridgeStageEndpoint_pool_avoids (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    (n : ℕ) (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (hn : 3 ≤ n) (hnmax : n ≤ 2 ^ 18)
    (x : (Fin 5 × Fin (3 * (n + 8))) × Fin 4) :
    fwBridgeStageEndpoint n initial batches hvalid x ∈ pool n ∧
      fwBridgeStageEndpoint n initial batches hvalid x ∉ initial := by
  rcases x with ⟨⟨j, i⟩, side⟩
  let b := fwBridgeStageBlock n initial batches hvalid j i
  have hv := fwBridgeStageBlock_valid n initial batches hvalid j i
  have hX : (0 : ℝ) < poolMaximum n := by exact_mod_cast (poolMaximum_prime n).pos
  have hstock := bmor_fw_bridge_stocks bmor upper n (fwBridgeRadius (poolMaximum n) j)
    hn hnmax (fw_bridge_nominal_radius_pos (poolMaximum n) hX j j.isLt)
  have hav := (hvalid j j.isLt).1.2.2.2.1 b
    (fwBridgeStageBlock_mem n initial batches hvalid j i)
  have hm := DoublePair.endpoint_mem b side
  have hnot : b.endpoint side ∉ initial := fun h => Finset.disjoint_left.mp hav hm h
  refine ⟨?_, hnot⟩
  fin_cases side
  · exact hstock.2.2.1 _ (Finset.mem_sdiff.mp hv.1).1
  · exact hstock.2.2.2 _ (Finset.mem_sdiff.mp hv.2.2.1).1
  · exact hstock.2.2.2 _ (Finset.mem_sdiff.mp hv.2.2.2.1).1
  · exact hstock.2.2.1 _ (Finset.mem_sdiff.mp hv.2.1).1

/-- The block's gap is the same gap used by the FW abstract grid proof. -/
theorem fwBridgeStageBlock_gap (n : ℕ) (initial : Finset ℕ)
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (j : Fin 5) (i : Fin (3 * (n + 8))) :
    selectedBridgeGap batches i j =
      (fwBridgeStageBlock n initial batches hvalid j i).high₁ -
        (fwBridgeStageBlock n initial batches hvalid j i).low₁ := by
  have hi : i.val < (batches j).length := by rw [(hvalid j j.isLt).1.1]; exact i.isLt
  simp [selectedBridgeGap, List.getElem?_eq_getElem hi, fwBridgeStageBlock]

end
end Sude
