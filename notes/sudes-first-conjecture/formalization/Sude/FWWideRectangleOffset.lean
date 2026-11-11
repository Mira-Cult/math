import Sude.FWSeedRectangleOffset

/-! A common RP1 label space for FW bridge, seed, and wide rectangles.
No later rectangle capacity, gap supply, or physical placement is asserted. -/
namespace Sude
noncomputable section

/-- Wide rectangles start after the 120 bridge and 384 seed labels.
The number `J` of wide stages is arbitrary. -/
def fwWideRectangle {J L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (t : Fin (J * (4 * 6))) : Fin L :=
  ⟨5 * (4 * 6) + 16 * (4 * 6) + t.val, by have ht := t.isLt; omega⟩

theorem fwWideRectangle_injective {J L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L) :
    Function.Injective (fwWideRectangle hwide) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [fwWideRectangle] at hv
  omega

theorem fw_bridge_wide_rectangle_ne {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (b : Fin (5 * (4 * 6))) (w : Fin (J * (4 * 6))) :
    bridgeDiagonalRectangle hrect b ≠ fwWideRectangle hwide w := by
  intro h
  have hv := congrArg Fin.val h
  have hb := b.isLt
  simp only [bridgeDiagonalRectangle, Fin.val_castLE, fwWideRectangle] at hv
  omega

theorem fw_seed_wide_rectangle_ne {J L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (s : Fin (16 * (4 * 6))) (w : Fin (J * (4 * 6))) :
    fwSeedRectangle hseed s ≠ fwWideRectangle hwide w := by
  intro h
  have hv := congrArg Fin.val h
  have ht := s.isLt
  simp only [fwSeedRectangle, fwWideRectangle] at hv
  omega

/-- On wide labels prescribe the first 12 of each stage to the main
diagonal and the next 12 to the antidiagonal; other labels are supplied. -/
def fwWideRectangleChoice {J L : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  Function.extend (fwWideRectangle hwide)
    (fun x => decide ((finProdFinEquiv.symm x : Fin J × Fin (4 * 6)).2.val < 2 * 6))
    otherChoice

/-- One choice map for all three families, with untouched labels supplied
by the caller. -/
def fwBridgeSeedWideRectangleChoice {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  fwBridgeSeedRectangleChoice hrect hseed (fwWideRectangleChoice hwide otherChoice)

theorem fwBridgeSeedWideChoice_bridge {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 5) (i : Fin (4 * 6)) :
    fwBridgeSeedWideRectangleChoice hrect hseed hwide otherChoice
      (bridgeDiagonalRectangle hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  exact fwBridgeSeedRectangleChoice_bridge hrect hseed (fwWideRectangleChoice hwide otherChoice) j i

theorem fwBridgeSeedWideChoice_seed {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 16) (i : Fin (4 * 6)) :
    fwBridgeSeedWideRectangleChoice hrect hseed hwide otherChoice
      (fwSeedRectangle hseed (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  exact fwBridgeSeedRectangleChoice_seed hrect hseed (fwWideRectangleChoice hwide otherChoice) j i

theorem fwBridgeSeedWideChoice_wide {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin J) (i : Fin (4 * 6)) :
    fwBridgeSeedWideRectangleChoice hrect hseed hwide otherChoice
      (fwWideRectangle hwide (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  unfold fwBridgeSeedWideRectangleChoice fwBridgeSeedRectangleChoice
  rw [bridgeDiagonalChoice_outside hrect _ _ (by
    rintro ⟨b, hb⟩
    exact fw_bridge_wide_rectangle_ne hrect hwide b _ hb)]
  unfold fwSeedRectangleChoice
  rw [Function.extend_apply' _ _ _ (by
    rintro ⟨s, hs⟩
    exact fw_seed_wide_rectangle_ne hseed hwide s _ hs)]
  rw [fwWideRectangleChoice, (fwWideRectangle_injective hwide).extend_apply]
  simp

/-- Labels outside all three allocated families retain the caller's choice. -/
theorem fwBridgeSeedWideChoice_outside {J L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (x : Fin L)
    (hb : ¬ ∃ t, bridgeDiagonalRectangle hrect t = x)
    (hs : ¬ ∃ t, fwSeedRectangle hseed t = x)
    (hw : ¬ ∃ t, fwWideRectangle hwide t = x) :
    fwBridgeSeedWideRectangleChoice hrect hseed hwide otherChoice x = otherChoice x := by
  unfold fwBridgeSeedWideRectangleChoice fwBridgeSeedRectangleChoice
  rw [bridgeDiagonalChoice_outside hrect _ _ hb]
  unfold fwSeedRectangleChoice
  rw [Function.extend_apply' _ _ _ hs]
  unfold fwWideRectangleChoice
  exact Function.extend_apply' _ _ _ hw

/-- Any wide rectangle has disjoint physical support from all bridge and
seed rectangles in the same packing and with the same choice. -/
theorem fw_wide_rectangles_disjoint_from_prior {J L n : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (w : Fin (J * (4 * 6))) (b : Fin (5 * (4 * 6)))
    (s : Fin (16 * (4 * 6))) :
    let choice := fwBridgeSeedWideRectangleChoice hrect hseed hwide otherChoice
    let support := fun i => rectangleCells (RectanglePacking.firstRow hs i)
      (RectanglePacking.secondRow hs i) (RectanglePacking.firstColumn hs choice i)
      (RectanglePacking.secondColumn hs choice i)
    Disjoint (support (fwWideRectangle hwide w)) (support (bridgeDiagonalRectangle hrect b)) ∧
      Disjoint (support (fwWideRectangle hwide w)) (support (fwSeedRectangle hseed s)) := by
  constructor
  · exact RectanglePacking.rectangle_cells_disjoint hs _ _ _
      (fw_bridge_wide_rectangle_ne hrect hwide b w).symm
  · exact RectanglePacking.rectangle_cells_disjoint hs _ _ _
      (fw_seed_wide_rectangle_ne hseed hwide s w).symm

/-- Distinct wide labels also have disjoint four-cell supports. -/
theorem fw_wide_rectangles_pairwise_disjoint {J L n : ℕ}
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + J * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (w w' : Fin (J * (4 * 6))) (hne : w ≠ w') :
    Disjoint (rectangleCells (RectanglePacking.firstRow hs (fwWideRectangle hwide w))
      (RectanglePacking.secondRow hs (fwWideRectangle hwide w))
      (RectanglePacking.firstColumn hs choice (fwWideRectangle hwide w))
      (RectanglePacking.secondColumn hs choice (fwWideRectangle hwide w)))
      (rectangleCells (RectanglePacking.firstRow hs (fwWideRectangle hwide w'))
      (RectanglePacking.secondRow hs (fwWideRectangle hwide w'))
      (RectanglePacking.firstColumn hs choice (fwWideRectangle hwide w'))
      (RectanglePacking.secondColumn hs choice (fwWideRectangle hwide w'))) := by
  apply RectanglePacking.rectangle_cells_disjoint hs choice
  exact fun heq => hne (fwWideRectangle_injective hwide heq)

end
end Sude
