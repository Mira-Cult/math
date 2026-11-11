import Sude.FWCanonicalFamilyChoiceGrids
import Sude.FWRectangleCYSignedGapTransport

/-! Canonical four-family choice grids and their signed gaps on the same CY
completion. No post-centering margin or primality is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- The two choice grids retain their separate actual radii, and the very
same canonical gap is realized on the supplied CY square and on any supplied
output fixing its packed rectangles. -/
theorem fw_canonical_cy_family_choice_grids {n : ℕ} (hnlo : 19485 ≤ n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254)
      (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice) f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc
      f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols p f.ordered oldReference roles)
    (cy : Cell n ≃ Fin (n*n))
    (hcy : ∀ z ∈ fwThetaFamilyFull f, entry cy z = entry oldReference z)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ f.last)
    (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ (Lucas.poolTotal n : ℝ) / (n*n : ℕ))
    (hmhi : (Lucas.poolTotal n : ℝ) / (n*n : ℕ) ≤ (123 / 250 : ℝ) * poolMaximum n) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    (∀ side, CompleteEvenGrid (labels.filter fun i => choice i = side) gap
      (fwCanonicalFamilyRadius f side) ∧ 2 ∣ fwCanonicalFamilyRadius f side) ∧
    (∀ z ∈ packedRectangleSupport f.hs choice, entry cy z = entry f.ordered z) ∧
    (∀ i ∈ labels,
      entry cy (packedRectangleCorner f.hs choice (i,1)) =
        entry cy (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
      entry cy (packedRectangleCorner f.hs choice (i,2)) =
        entry cy (packedRectangleCorner f.hs choice (i,3)) + gap i) ∧
    (∀ out : Cell n ≃ Fin (n*n),
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) →
      ∀ i ∈ labels,
        entry out (packedRectangleCorner f.hs choice (i,1)) =
          entry out (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
        entry out (packedRectangleCorner f.hs choice (i,2)) =
          entry out (packedRectangleCorner f.hs choice (i,3)) + gap i) := by
  classical
  dsimp only
  let choice := fwSelectedThetaChoice hnlo otherChoice
  let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
  let gap := fwOrderedCanonicalRectangleGap f
  have hordered := (fw_ordered_canonical_rectangle_gap f).2.2.2.2
  have htransport := fw_rectangle_cy_signed_gap_transport choice f p oldReference roles net cy hcy labels gap
    (by simpa [labels, gap, choice, packedRectangleCorner] using hordered)
  refine ⟨fw_canonical_family_choice_grids hnlo otherChoice f hcross hX hmlo hmhi, htransport.1, ?_, ?_⟩
  · simpa [labels, gap, choice, packedRectangleCorner] using htransport.2.1
  · simpa [labels, gap, choice, packedRectangleCorner] using htransport.2.2

end
end Sude
