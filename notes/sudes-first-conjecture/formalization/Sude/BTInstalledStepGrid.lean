import Sude.BTPhysicalStepGrid
import Sude.VariablePrefixPhysical
import Sude.PrefixInstalledNetwork

/-! Instantiate the variable-gap grid on the installed network pair slots. -/
namespace Sude
noncomputable section

/-- The physical gap at a stage/layer slot is exactly the selected stage gap. -/
theorem variablePrefixNetworkGap_slot {P r m n : ℕ}
    (gaps : Fin P → ℕ) (hlen : m = P * r) (edge : Fin r × Fin n) (j : Fin P) :
    variablePrefixNetworkGap gaps hlen (prefixPhysicalStageSlot hlen (edge, j)).1
      (prefixPhysicalStageSlot hlen (edge, j)).2 = gaps j := by
  simp [variablePrefixNetworkGap, prefixPhysicalStageSlot, bridgeStageLayerIndex]

/-- For each network edge the traced pair slots give a complete grid of
multiples of `g`, provided a distinct physical seed pair has gap `g`. The
network's pair-gap equations then identify these slot gaps with the actual
entry differences in the installed square. -/
theorem BTStageTrace.installed_network_step_grid {g Q P r m n : ℕ}
    {initial final : Finset ℕ} {R last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q initial R final last stages)
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

/-- If the supplied seed belongs to this same directed edge, every label in
the grid has the same physical source and target. Repeated permutations are
proved to provide this property for the traced stages. -/
theorem installed_variable_grid_endpoints {P r n : ℕ}
    (layers : List (LayerPacking.Layer n)) (hlen : layers.length = P * r)
    (perms : Fin r → Equiv.Perm (Fin n))
    (hperms : layers.map Prod.fst = bridgeRepeatedPermutations P perms)
    (edge : Fin r × Fin n) (seed : Fin layers.length × Fin n)
    (hsource : seed.2 = edge.2)
    (htarget : (layers.get seed.1).1 seed.2 = perms edge.1 edge.2) :
    ∀ k ∈ ({seed} ∪ prefixPairBlock P (prefixPhysicalStageSlot hlen) edge),
      k.2 = edge.2 ∧ (layers.get k.1).1 k.2 = perms edge.1 edge.2 := by
  intro k hk
  rcases Finset.mem_union.mp hk with hs | hs
  · have he : k = seed := Finset.mem_singleton.mp hs
    subst k
    exact ⟨hsource, htarget⟩
  · obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hs
    exact ⟨rfl, bridgeStageLayer_endpoints layers hlen perms hperms j edge.1 edge.2⟩

/-- Extend an existing physical `g`-grid by the traced slots for one edge.
The initial grid and its separation from the newly installed slots are
explicit inputs, as in the source's phase argument. -/
theorem BTStageTrace.extend_installed_network_grid {g Q P r m n : ℕ}
    {initial final : Finset ℕ} {R last : ℝ} {stages : List BTSelectedStage}
    (trace : BTStageTrace g Q initial R final last stages)
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
