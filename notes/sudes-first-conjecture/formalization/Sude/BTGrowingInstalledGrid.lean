import Sude.BTGrowingPhysicalGrid
import Sude.BTInstalledStepGrid

/-! Growing-radius selections on actual network pair slots. -/
namespace Sude
noncomputable section

/-- For each network edge the traced pair slots give a complete grid of
multiples of `g`, provided a distinct physical seed pair has gap `g`. The
network's pair-gap equations then identify these slot gaps with the actual
entry differences in the installed square. -/
theorem BTGrowingTrace.installed_network_step_grid {g Q P r m n : ℕ}
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial R final last stages)
    (hP : stages.length = P) (hlen : m = P * r) (edge : Fin r × Fin n)
    (seed : Fin m × Fin n) (hg : 0 < g) (hstart : R ≤ g)
    (hseed : variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hP j).gap)
      hlen seed.1 seed.2 = g)
    (hfresh : seed ∉ prefixPairBlock P (prefixPhysicalStageSlot (n := n) hlen) edge) :
    CompleteStepGrid ({seed} ∪ prefixPairBlock P (prefixPhysicalStageSlot (n := n) hlen) edge)
      (fun x => variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hP j).gap)
        hlen x.1 x.2) g
      (g + (List.ofFn (fun j : Fin P => (BTStageTrace.stageAt stages hP j).gap)).sum) := by
  let slot := prefixPhysicalStageSlot (n := n) hlen
  let labels : List (Fin m × Fin n) := List.ofFn (fun j : Fin P => slot (edge, j))
  let gap : Fin m × Fin n → ℕ := fun x => variablePrefixNetworkGap
    (fun j => (BTStageTrace.stageAt stages hP j).gap) hlen x.1 x.2
  have hnodup : labels.Nodup := by
    apply List.nodup_ofFn.mpr
    intro a b heq
    exact congrArg Prod.snd (prefixPhysicalStageSlot_injective hlen heq)
  have hfresh' : seed ∉ labels := by
    intro hm
    apply hfresh
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hm
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels := by
    apply List.forall₂_of_length_eq_of_get
    · simpa [labels] using hP
    · intro i hi hj
      have hiP : i < P := hP ▸ hi
      simp [labels, gap, slot, BTStageTrace.stageAt, variablePrefixNetworkGap_slot] at *
  have hgrid := trace.physical_seeded_step_grid gap seed labels hg hseed hstart hnodup hfresh' hlabels
  have hset : labels.toFinset = prefixPairBlock P slot edge := by
    ext x
    simp [labels, prefixPairBlock]
  have hsum : (labels.map gap).sum =
      (List.ofFn (fun j : Fin P => (BTStageTrace.stageAt stages hP j).gap)).sum := by
    congr 1
    apply List.ext_get
    · simp [labels]
    · intro i hi₁ hi₂
      simp [labels, gap, slot, variablePrefixNetworkGap_slot]
  simpa [gap, slot, hset, hsum] using hgrid

/-- Extend an existing physical `g`-grid by the traced slots for one edge.
The initial grid and its separation from the newly installed slots are
explicit inputs, as in the source's phase argument. -/
theorem BTGrowingTrace.extend_installed_network_grid {g Q P r m n : ℕ}
    {initial final : Finset ℕ} {R last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial R final last stages)
    (hP : stages.length = P) (hlen : m = P * r) (edge : Fin r × Fin n)
    (base : Finset (Fin m × Fin n)) (radius : ℕ) (hg : 0 < g)
    (hbase : CompleteStepGrid base
      (fun x => variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hP j).gap)
        hlen x.1 x.2) g radius)
    (hdiv : g ∣ radius) (hstart : R ≤ radius)
    (hseparate : Disjoint base (prefixPairBlock P (prefixPhysicalStageSlot hlen) edge)) :
    CompleteStepGrid (base ∪ prefixPairBlock P (prefixPhysicalStageSlot hlen) edge)
      (fun x => variablePrefixNetworkGap (fun j => (BTStageTrace.stageAt stages hP j).gap)
        hlen x.1 x.2) g
      (radius + (List.ofFn (fun j : Fin P => (BTStageTrace.stageAt stages hP j).gap)).sum) := by
  let slot := prefixPhysicalStageSlot (n := n) hlen
  let labels : List (Fin m × Fin n) := List.ofFn (fun j : Fin P => slot (edge, j))
  let gap : Fin m × Fin n → ℕ := fun x => variablePrefixNetworkGap
    (fun j => (BTStageTrace.stageAt stages hP j).gap) hlen x.1 x.2
  have hnodup : labels.Nodup := by
    apply List.nodup_ofFn.mpr
    intro a b heq
    exact congrArg Prod.snd (prefixPhysicalStageSlot_injective hlen heq)
  have hset : labels.toFinset = prefixPairBlock P slot edge := by
    ext x
    simp [labels, prefixPairBlock]
  have hfresh : ∀ k ∈ labels, k ∉ base := by
    intro k hk hb
    have hk' : k ∈ prefixPairBlock P slot edge := hset ▸ List.mem_toFinset.mpr hk
    exact Finset.disjoint_left.mp hseparate hb hk'
  have hlabels : List.Forall₂ (fun stage label => gap label = stage.gap) stages labels := by
    apply List.forall₂_of_length_eq_of_get
    · simpa [labels] using hP
    · intro i hi hj
      have hiP : i < P := hP ▸ hi
      simp [labels, gap, slot, BTStageTrace.stageAt, variablePrefixNetworkGap_slot] at *
  have hgrid := extend_step_gap_chain gap g base radius labels hg hbase hdiv hnodup hfresh
    (trace.physical_step_chain gap labels hlabels radius hstart)
  have hsum : (labels.map gap).sum =
      (List.ofFn (fun j : Fin P => (BTStageTrace.stageAt stages hP j).gap)).sum := by
    congr 1
    apply List.ext_get
    · simp [labels]
    · intro i hi₁ hi₂
      simp [labels, gap, slot, variablePrefixNetworkGap_slot]
  simpa [gap, slot, hset, hsum] using hgrid


end
end Sude
