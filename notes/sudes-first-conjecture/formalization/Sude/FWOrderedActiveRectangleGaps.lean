import Sude.FWOrderedBridgeWideRectangleGaps
import Sude.FWOrderedSeedGrowthRectangleGaps
import Sude.FWActiveRectangleLabels

/-! Signed gaps on exactly the active rectangle labels of one ordered witness.
The supplied label gap agrees with each family's actual signed gap. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Both oriented physical pairs have the specified signed gap for every active
label, provided that function agrees with each of the four family gaps. -/
theorem fw_ordered_active_rectangle_signed_gaps {n : ℕ}
    {choice : Fin (fwJointRectangleCount n 254) → Bool}
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (gap : Fin (fwJointRectangleCount n 254) → ℕ)
    (hb : ∀ (j : Fin 5) (r : Fin (4*6)),
      gap (bridgeDiagonalRectangle f.hrect (finProdFinEquiv (j,r))) =
        f.gapb j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r))
    (hs : ∀ (j : Fin 16) (r : Fin (4*6)),
      gap (fwSeedRectangle f.hseedrect (finProdFinEquiv (j,r))) = 2)
    (hw : ∀ (j : Fin (3*(n/450))) (r : Fin (4*6)),
      gap (fwWideRectangle f.hwide (finProdFinEquiv (j,r))) =
        f.gapw j (Fin.castLE (by omega : 4*6 ≤ 3*(n+8)) r))
    (hg : ∀ (j : Fin f.stages.length) (r : Fin (4*6)),
      gap (btGrowingOffsetRectangle
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) f.hoff (finProdFinEquiv (j,r))) =
        (f.stages.get j).gap) :
    ∀ i ∈ fwActiveRectangleLabels n f.stages.length f.stageCap,
      entry f.ordered (packedRectangleCorner f.hs choice (i,1)) =
        entry f.ordered (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
      entry f.ordered (packedRectangleCorner f.hs choice (i,2)) =
        entry f.ordered (packedRectangleCorner f.hs choice (i,3)) + gap i := by
  classical
  intro i hi
  rw [fw_active_labels_eq_family_union n f.stages.length f.stageCap] at hi
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hi
  rcases hi with (((⟨t, ht⟩ | ⟨t, ht⟩) | ⟨t, ht⟩) | ⟨t, ht⟩)
  · let p : Fin 5 × Fin (4*6) := finProdFinEquiv.symm t
    have hp : finProdFinEquiv (p.1, p.2) = t := finProdFinEquiv.apply_symm_apply t
    subst i
    have h := fw_ordered_bridge_rectangle_gaps f p.1 p.2
    dsimp only at h
    rw [← hb p.1 p.2] at h
    simpa only [hp] using h
  · let p : Fin 16 × Fin (4*6) := finProdFinEquiv.symm t
    have hp : finProdFinEquiv (p.1, p.2) = t := finProdFinEquiv.apply_symm_apply t
    subst i
    have h := fw_ordered_seed_rectangle_signed_gaps f p.1 p.2
    dsimp only at h
    rw [← hs p.1 p.2] at h
    simpa only [hp] using h
  · let p : Fin (3*(n/450)) × Fin (4*6) := finProdFinEquiv.symm t
    have hp : finProdFinEquiv (p.1, p.2) = t := finProdFinEquiv.apply_symm_apply t
    subst i
    have h := fw_ordered_wide_rectangle_gaps f p.1 p.2
    dsimp only at h
    rw [← hw p.1 p.2] at h
    simpa only [hp] using h
  · let p : Fin f.stages.length × Fin (4*6) := finProdFinEquiv.symm t
    have hp : finProdFinEquiv (p.1, p.2) = t := finProdFinEquiv.apply_symm_apply t
    subst i
    have h := fw_ordered_growth_rectangle_signed_gaps f p.1 p.2
    dsimp only at h
    rw [← hg p.1 p.2] at h
    simpa only [hp] using h

end
end Sude
