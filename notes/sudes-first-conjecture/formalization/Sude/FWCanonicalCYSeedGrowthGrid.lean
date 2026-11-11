import Sude.FWCanonicalSeedGrowthLabels
import Sude.FWChoiceSeedTraceGrid
import Sude.FWRectangleCYSignedGapTransport
import Sude.FWOrderedCanonicalRectangleGap

/-! The canonical choice grids and signed physical gaps on the exact same CY
completion. No bridge crossing, centered-radius budget, or primality is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Each canonical physical representative has its abstract seed/trace gap. -/
theorem fw_canonical_seed_growth_label_gap {n : ℕ} {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice) (side : Bool)
    (x : {x // x ∈ fwSeedTraceLabels f.stages}) :
    fwOrderedCanonicalRectangleGap f (fwCanonicalSeedGrowthLabel f side x) = fwSeedTraceGap x.val := by
  classical
  have hg := fw_ordered_canonical_rectangle_gap f
  rcases x with ⟨x,hx⟩
  cases x with
  | inl j =>
    rw [fw_canonical_seed_label f side j hx]
    exact hg.2.1 j (fwCanonicalChoiceRectangle side)
  | inr s =>
    let e := List.Nodup.getEquiv f.stages (f.trace.nodup (by omega))
    let t : {a // a ∈ f.stages} := ⟨s, fw_seed_trace_stage_mem f.stages s hx⟩
    let j := e.symm t
    have he : f.stages.get j = s := congrArg Subtype.val (e.apply_symm_apply t)
    have hlabel : fwCanonicalSeedGrowthLabel f side ⟨Sum.inr s, hx⟩ =
      btGrowingOffsetRectangle (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff
        (finProdFinEquiv (j, fwCanonicalChoiceRectangle side)) := by
      dsimp [fwCanonicalSeedGrowthLabel, j, e, t]
    rw [hlabel, hg.2.2.2.1 j (fwCanonicalChoiceRectangle side), he]
    rfl

/-- Both choice grids use actual selected rectangles and the exact trace radius.
The same gap has both physical signed equations on the same CY completion. -/
theorem fw_canonical_cy_seed_growth_grids {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice) f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc
      f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols p f.ordered oldReference roles)
    (cy : Cell n ≃ Fin (n*n))
    (hcy : ∀ z ∈ fwThetaFamilyFull f, entry cy z = entry oldReference z) :
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    CompleteEvenGrid (labels.filter fun i => fwSelectedThetaChoice hnlo otherChoice i = true) gap f.last ∧
    CompleteEvenGrid (labels.filter fun i => fwSelectedThetaChoice hnlo otherChoice i = false) gap f.last ∧
    2 ∣ f.last ∧
    (∀ i ∈ labels,
      entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,1)) =
        entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,0)) + gap i ∧
      entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,2)) =
        entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,3)) + gap i) := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
  let gap := fwOrderedCanonicalRectangleGap f
  have hordered := (fw_ordered_canonical_rectangle_gap f).2.2.2.2
  have hcyg := (fw_rectangle_cy_signed_gap_transport choice f p oldReference roles net cy hcy labels gap
    (by simpa [labels, gap, choice, packedRectangleCorner] using hordered)).2.1
  have hgrid := fw_choice_seed_trace_even_grids f labels gap
    (fwCanonicalSeedGrowthLabel f true) (fwCanonicalSeedGrowthLabel f false)
    (fw_canonical_seed_growth_label_injective f true) (fw_canonical_seed_growth_label_injective f false)
    (fun x => ⟨fw_canonical_seed_growth_label_mem f true x,
      fw_canonical_seed_growth_label_choice hnlo otherChoice f true x, fw_canonical_seed_growth_label_gap f true x⟩)
    (fun x => ⟨fw_canonical_seed_growth_label_mem f false x,
      fw_canonical_seed_growth_label_choice hnlo otherChoice f false x, fw_canonical_seed_growth_label_gap f false x⟩)
  exact ⟨hgrid.1, hgrid.2.1, hgrid.2.2, by simpa [labels, gap, choice, packedRectangleCorner] using hcyg⟩

end
end Sude
