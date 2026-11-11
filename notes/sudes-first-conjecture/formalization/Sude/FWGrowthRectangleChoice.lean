import Sude.FWGrowthEarlyGeometry
import Sude.BTGrowingOffsetPhysical

/-! Common diagonal choices for reserved future growth rectangles. This does
not construct or install a growth trace. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Assign each potential growth stage's first twelve rectangles to one
labelled diagonal and the remaining twelve to the other. -/
def fwGrowthRectangleChoice {n L P : ℕ}
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  Function.extend (fwGrowthRectangle hgrowth)
    (fun x => decide ((finProdFinEquiv.symm x : Fin P × Fin (4 * 6)).2.val < 2 * 6))
    otherChoice

/-- The early choice map keeps its priority over the growth fallback. -/
def fwBridgeSeedWideGrowthChoice {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  fwBridgeSeedWideRectangleChoice hrect hseed hwide (fwGrowthRectangleChoice hgrowth otherChoice)

theorem fw_bridge_growth_rectangle_ne {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (b : Fin (5 * (4 * 6))) (g : Fin (P * (4 * 6))) :
    bridgeDiagonalRectangle hrect b ≠ fwGrowthRectangle hgrowth g := by
  intro h
  have hv := congrArg Fin.val h
  have hb := b.isLt
  simp only [bridgeDiagonalRectangle, Fin.val_castLE, fwGrowthRectangle] at hv
  omega

theorem fw_seed_growth_rectangle_ne {n L P : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (s : Fin (16 * (4 * 6))) (g : Fin (P * (4 * 6))) :
    fwSeedRectangle hseed s ≠ fwGrowthRectangle hgrowth g := by
  intro h
  have hv := congrArg Fin.val h
  have hs := s.isLt
  simp only [fwSeedRectangle, fwGrowthRectangle] at hv
  omega

theorem fw_wide_growth_rectangle_ne {n L P : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (w : Fin ((3 * (n / 450)) * (4 * 6))) (g : Fin (P * (4 * 6))) :
    fwWideRectangle hwide w ≠ fwGrowthRectangle hgrowth g := by
  intro h
  have hv := congrArg Fin.val h
  have hw := w.isLt
  simp only [fwWideRectangle, fwGrowthRectangle] at hv
  omega

/-- All growth choices coexist with the earlier source assignments. -/
theorem fwBridgeSeedWideGrowthChoice_growth {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin P) (i : Fin (4 * 6)) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
      (fwGrowthRectangle hgrowth (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  unfold fwBridgeSeedWideGrowthChoice
  rw [fwBridgeSeedWideChoice_outside hrect hseed hwide _ _ (by
    rintro ⟨b, hb⟩
    exact fw_bridge_growth_rectangle_ne hrect hgrowth b _ hb) (by
    rintro ⟨s, hs⟩
    exact fw_seed_growth_rectangle_ne hseed hgrowth s _ hs) (by
    rintro ⟨w, hw⟩
    exact fw_wide_growth_rectangle_ne hwide hgrowth w _ hw)]
  rw [fwGrowthRectangleChoice, (fwGrowthRectangle_injective hgrowth).extend_apply]
  simp

/-- The three earlier families retain their source diagonal choices. -/
theorem fwBridgeSeedWideGrowthChoice_bridge {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 5) (i : Fin (4 * 6)) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
      (bridgeDiagonalRectangle hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) :=
  fwBridgeSeedWideChoice_bridge hrect hseed hwide (fwGrowthRectangleChoice hgrowth otherChoice) j i

theorem fwBridgeSeedWideGrowthChoice_seed {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 16) (i : Fin (4 * 6)) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
      (fwSeedRectangle hseed (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) :=
  fwBridgeSeedWideChoice_seed hrect hseed hwide (fwGrowthRectangleChoice hgrowth otherChoice) j i

theorem fwBridgeSeedWideGrowthChoice_wide {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin (3 * (n / 450))) (i : Fin (4 * 6)) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice
      (fwWideRectangle hwide (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) :=
  fwBridgeSeedWideChoice_wide hrect hseed hwide (fwGrowthRectangleChoice hgrowth otherChoice) j i

/-- A shorter realized trace uses the choices reserved in advance for the
same initial stage labels of a larger potential trace. -/
theorem fwBridgeSeedWideGrowthChoice_offset_restrict {n L P M : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hmax : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + M * (4 * 6) ≤ L)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hle : P ≤ M) (otherChoice : Fin L → Bool) (j : Fin P) (i : Fin (4 * 6)) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hmax otherChoice
      (btGrowingOffsetRectangle (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
        hoff (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  let jmax : Fin M := ⟨j.val, by have hj := j.isLt; omega⟩
  have heq : btGrowingOffsetRectangle (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      hoff (finProdFinEquiv (j, i)) = fwGrowthRectangle hmax (finProdFinEquiv (jmax, i)) := by
    apply Fin.ext
    simp [btGrowingOffsetRectangle, fwGrowthRectangle, jmax, finProdFinEquiv]
  rw [heq]
  exact fwBridgeSeedWideGrowthChoice_growth hrect hseed hwide hmax otherChoice jmax i

/-- Labels outside all four allocated families keep the supplied fallback. -/
theorem fwBridgeSeedWideGrowthChoice_outside {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (x : Fin L)
    (hb : ¬ ∃ t, bridgeDiagonalRectangle hrect t = x)
    (hs : ¬ ∃ t, fwSeedRectangle hseed t = x)
    (hw : ¬ ∃ t, fwWideRectangle hwide t = x)
    (hg : ¬ ∃ t, fwGrowthRectangle hgrowth t = x) :
    fwBridgeSeedWideGrowthChoice hrect hseed hwide hgrowth otherChoice x = otherChoice x := by
  unfold fwBridgeSeedWideGrowthChoice
  rw [fwBridgeSeedWideChoice_outside hrect hseed hwide _ _ hb hs hw]
  unfold fwGrowthRectangleChoice
  exact Function.extend_apply' _ _ _ hg

end
end Sude
