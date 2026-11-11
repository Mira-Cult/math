import Sude.FWThetaFamilyWitness
import Sude.FWSeedTraceGridExact
import Sude.BridgePhysicalGrid

/-! Transport the seed-plus-growth even grid into two supplied physical
rectangle-label families. Existence of the matching maps and their physical
gap equations remains explicit; arbitrary choices need not support them. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- If each abstract seed or growth stage has a distinct representative on
each side of the supplied choice, with its exact gap, both physical label
families cover every even demand through the trace's actual final radius.
No extra bridge/wide radius or matching-map existence is asserted. -/
theorem fw_choice_seed_trace_even_grids {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (labels : Finset (Fin L)) (gap : Fin L → ℕ)
    (mainLabel antiLabel : {x // x ∈ fwSeedTraceLabels f.stages} → Fin L)
    (hmainInj : Function.Injective mainLabel) (hantiInj : Function.Injective antiLabel)
    (hmain : ∀ x, mainLabel x ∈ labels ∧ choice (mainLabel x) = true ∧
      gap (mainLabel x) = fwSeedTraceGap x.val)
    (hanti : ∀ x, antiLabel x ∈ labels ∧ choice (antiLabel x) = false ∧
      gap (antiLabel x) = fwSeedTraceGap x.val) :
    CompleteEvenGrid (labels.filter fun i => choice i = true) gap f.last ∧
    CompleteEvenGrid (labels.filter fun i => choice i = false) gap f.last ∧
    2 ∣ f.last := by
  classical
  have hbase := fw_seed_trace_even_grid_unconditional_coverage (by omega) f.trace
  have hm := completeEvenGrid_finite_relabel (fwSeedTraceLabels f.stages) fwSeedTraceGap f.last
    mainLabel hmainInj gap (fun x => (hmain x).2.2) hbase.1
  have ha := completeEvenGrid_finite_relabel (fwSeedTraceLabels f.stages) fwSeedTraceGap f.last
    antiLabel hantiInj gap (fun x => (hanti x).2.2) hbase.1
  have hmSub : (fwSeedTraceLabels f.stages).attach.image mainLabel ⊆
      labels.filter (fun i => choice i = true) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨(hmain x).1, (hmain x).2.1⟩
  have haSub : (fwSeedTraceLabels f.stages).attach.image antiLabel ⊆
      labels.filter (fun i => choice i = false) := by
    intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨(hanti x).1, (hanti x).2.1⟩
  refine ⟨?_, ?_, hbase.2⟩
  · intro t ht heven
    obtain ⟨T, hT, hsum⟩ := hm t ht heven
    exact ⟨T, hT.trans hmSub, hsum⟩
  · intro t ht heven
    obtain ⟨T, hT, hsum⟩ := ha t ht heven
    exact ⟨T, hT.trans haSub, hsum⟩

end
end Sude
