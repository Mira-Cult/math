import Sude.FWThetaFamilyDQRFInputs
import Sude.FWThetaNetworkWitness

/-! Transport supplied signed rectangle gaps to the same CY completion and
any later square preserving its packed rectangles. No diagonal grid,
unreserved-cell agreement, flow existence, or primality is inferred. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 1500000

/-- If the ordered square has the two signed trade equations on selected
rectangle labels, then the same equations hold on a completion fixing the
full reservation relative to its exact network reference. They also hold on
any supplied square that agrees with that completion on packed rectangles. -/
theorem fw_rectangle_cy_signed_gap_transport {n : ℕ}
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (cy : Cell n ≃ Fin (n*n))
    (hcy : ∀ z ∈ fwThetaFamilyFull f, entry cy z = entry oldReference z)
    (labels : Finset (Fin (fwJointRectangleCount n 254)))
    (gap : Fin (fwJointRectangleCount n 254) → ℕ)
    (hgaps : ∀ i ∈ labels,
      entry f.ordered (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
        entry f.ordered (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
      entry f.ordered (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
        entry f.ordered (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) :
    (∀ z ∈ packedRectangleSupport f.hs choice, entry cy z = entry f.ordered z) ∧
    (∀ i ∈ labels,
      entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
        entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
      entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
        entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) ∧
    (∀ out : Cell n ≃ Fin (n*n),
      (∀ z ∈ packedRectangleSupport f.hs choice, entry out z = entry cy z) →
      ∀ i ∈ labels,
        entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
          entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
        entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
          entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i) := by
  classical
  have hsame : ∀ z ∈ packedRectangleSupport f.hs choice, entry cy z = entry f.ordered z := by
    intro z hz
    have hfull : z ∈ fwThetaFamilyFull f := by
      dsimp only [fwThetaFamilyFull]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ hz)
    exact (hcy z hfull).trans (net.rectangle_fixed z hz)
  have hcorner (i : Fin (fwJointRectangleCount n 254)) (k : Fin 4) :
      packedRectangleCorner f.hs choice (i,k) ∈ packedRectangleSupport f.hs choice :=
    Finset.mem_image.mpr ⟨(i,k), Finset.mem_univ _, rfl⟩
  have hgcy : ∀ i ∈ labels,
      entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
        entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) + gap i ∧
      entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
        entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) + gap i := by
    intro i hi
    have h0 := hsame _ (hcorner i 0)
    have h1 := hsame _ (hcorner i 1)
    have h2 := hsame _ (hcorner i 2)
    have h3 := hsame _ (hcorner i 3)
    change entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
      entry f.ordered (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) at h0
    change entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
      entry f.ordered (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) at h1
    change entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
      entry f.ordered (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) at h2
    change entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
      entry f.ordered (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) at h3
    rw [h1, h0, h2, h3]
    exact hgaps i hi
  refine ⟨hsame, hgcy, ?_⟩
  intro out hout i hi
  have h0 := hout _ (hcorner i 0)
  have h1 := hout _ (hcorner i 1)
  have h2 := hout _ (hcorner i 2)
  have h3 := hout _ (hcorner i 3)
  change entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
    entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.firstColumn f.hs choice i) at h0
  change entry out (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
    entry cy (RectanglePacking.firstRow f.hs i, RectanglePacking.secondColumn f.hs choice i) at h1
  change entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) =
    entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.firstColumn f.hs choice i) at h2
  change entry out (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) =
    entry cy (RectanglePacking.secondRow f.hs i, RectanglePacking.secondColumn f.hs choice i) at h3
  rw [h1, h0, h2, h3]
  exact hgcy i hi

end
end Sude
