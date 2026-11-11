import Sude.FWBridgeLayerSlots

/-! A single RP1 label space for the 120 FW bridge rectangles followed by
384 narrow-seed rectangles. This is geometry only: no seeds are selected or
installed here and no later layout is asserted. -/
namespace Sude
noncomputable section

/-- Put the sixteen seed stages' 24 rectangle labels immediately after the
five bridge stages' 120 labels in a common RP1 packing. -/
def fwSeedRectangle {L : ℕ} (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (t : Fin (16 * (4 * 6))) : Fin L :=
  ⟨5 * (4 * 6) + t.val, by have ht := t.isLt; omega⟩

theorem fwSeedRectangle_injective {L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L) :
    Function.Injective (fwSeedRectangle hseed) := by
  intro x y h
  apply Fin.ext
  have hv := congrArg Fin.val h
  simp only [fwSeedRectangle] at hv
  omega

/-- Bridge and seed rectangles occupy disjoint label intervals. -/
theorem fw_bridge_seed_rectangle_ne {L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (b : Fin (5 * (4 * 6))) (s : Fin (16 * (4 * 6))) :
    bridgeDiagonalRectangle hrect b ≠ fwSeedRectangle hseed s := by
  intro h
  have hv := congrArg Fin.val h
  have hb := b.isLt
  simp only [bridgeDiagonalRectangle, Fin.val_castLE, fwSeedRectangle] at hv
  omega

/-- Assign each seed stage's first 12 rectangles to the main diagonal and
its remaining 12 to the antidiagonal, leaving all other labels supplied by
the caller. -/
def fwSeedRectangleChoice {L : ℕ}
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  Function.extend (fwSeedRectangle hseed)
    (fun x => decide ((finProdFinEquiv.symm x : Fin 16 × Fin (4 * 6)).2.val < 2 * 6))
    otherChoice

/-- One common choice map simultaneously prescribes the bridge and seed
source diagonal assignments. -/
def fwBridgeSeedRectangleChoice {L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) : Fin L → Bool :=
  bridgeDiagonalChoice hrect (fwSeedRectangleChoice hseed otherChoice)

theorem fwBridgeSeedRectangleChoice_bridge {L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 5) (i : Fin (4 * 6)) :
    fwBridgeSeedRectangleChoice hrect hseed otherChoice
      (bridgeDiagonalRectangle hrect (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  exact bridgeDiagonalChoice_at hrect (fwSeedRectangleChoice hseed otherChoice) j i

theorem fwBridgeSeedRectangleChoice_seed {L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (otherChoice : Fin L → Bool) (j : Fin 16) (i : Fin (4 * 6)) :
    fwBridgeSeedRectangleChoice hrect hseed otherChoice
      (fwSeedRectangle hseed (finProdFinEquiv (j, i))) = decide (i.val < 2 * 6) := by
  unfold fwBridgeSeedRectangleChoice
  rw [bridgeDiagonalChoice_outside hrect _ _ (by
    rintro ⟨b, hb⟩
    exact fw_bridge_seed_rectangle_ne hrect hseed b _ hb)]
  rw [fwSeedRectangleChoice, (fwSeedRectangle_injective hseed).extend_apply]
  simp

/-- Any bridge rectangle and any offset seed rectangle have disjoint actual
four-cell supports in the same RP1 packing and with the same choice map. -/
theorem fw_bridge_seed_rectangles_disjoint {L n : ℕ}
    (hrect : 5 * (4 * 6) ≤ L)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (otherChoice : Fin L → Bool)
    (b : Fin (5 * (4 * 6))) (s : Fin (16 * (4 * 6))) :
    let choice := fwBridgeSeedRectangleChoice hrect hseed otherChoice
    Disjoint (rectangleCells (RectanglePacking.firstRow hs (bridgeDiagonalRectangle hrect b))
      (RectanglePacking.secondRow hs (bridgeDiagonalRectangle hrect b))
      (RectanglePacking.firstColumn hs choice (bridgeDiagonalRectangle hrect b))
      (RectanglePacking.secondColumn hs choice (bridgeDiagonalRectangle hrect b)))
      (rectangleCells (RectanglePacking.firstRow hs (fwSeedRectangle hseed s))
      (RectanglePacking.secondRow hs (fwSeedRectangle hseed s))
      (RectanglePacking.firstColumn hs choice (fwSeedRectangle hseed s))
      (RectanglePacking.secondColumn hs choice (fwSeedRectangle hseed s))) := by
  exact RectanglePacking.rectangle_cells_disjoint hs _ _ _
    (fw_bridge_seed_rectangle_ne hrect hseed b s)

/-- The minimum joint label capacity, 504 rectangles, fits the FW range. -/
theorem fw_bridge_seed_rectangle_capacity {n : ℕ} (hn : 19485 ≤ n) :
    5 * (4 * 6) + 16 * (4 * 6) ≤ 504 ∧ 2 * 504 + 1 ≤ n := by omega

end
end Sude
