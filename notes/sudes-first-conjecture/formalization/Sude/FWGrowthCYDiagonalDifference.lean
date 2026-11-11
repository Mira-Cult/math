import Sude.FWGrowthCYDiagonalTransfer

/-! Difference bound for the growth contribution on the supplied CY square.
No assertion about the rest of either diagonal or a prime is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The selected growth diagonals have a common baseline. Their two deviations
therefore bound their difference on the exact same supplied CY completion. -/
theorem fw_growth_cy_diagonal_difference {n : ℕ} (hn : 0 < n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (g : FWThetaGrowthDiagonalWitness n (fwJointRectangleCount n 254) choice f)
    (cy : Cell n ≃ Fin (n*n))
    (hcy : ∀ z ∈ fwThetaFamilyFull f, entry cy z = entry oldReference z) :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    |(∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)) -
      (∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ))| ≤
      (((n : ℝ) + 7) / (6 * ((n : ℝ) + 6))) * (poolMaximum n : ℝ) := by
  dsimp only
  have h := fw_growth_cy_diagonal_transfer choice f p oldReference roles net g cy hcy
  dsimp only at h
  have hm := h.2.2.2.2.2.1
  have ha := h.2.2.2.2.2.2
  let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
    (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
    f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
  let M : ℝ := ∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ mainCells n), (entry cy z : ℝ)
  let A : ℝ := ∑ z ∈ (Finset.univ.image growth).filter (fun z => z ∈ antiCells n), (entry cy z : ℝ)
  let K : ℝ := (12 : ℝ) * ∑ j, (∑ q ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) q) /
    (6 * (n + 8) : ℕ) - 6 * ∑ j, ((f.stages.get j).gap : ℝ)
  change |M - K| ≤ ((poolMaximum n : ℝ) / 6) / 2 at hm
  change |A - K| ≤ (((n : ℝ) + 8) / (2 * ((n : ℝ) + 6))) * ((poolMaximum n : ℝ) / 6) at ha
  change |M - A| ≤ _
  have htri := abs_sub_le M K A
  rw [abs_sub_comm K A] at htri
  have hden : (0 : ℝ) < (n : ℝ) + 6 := by positivity
  have hcoeff : ((poolMaximum n : ℝ) / 6) / 2 +
      (((n : ℝ) + 8) / (2 * ((n : ℝ) + 6))) * ((poolMaximum n : ℝ) / 6) =
      (((n : ℝ) + 7) / (6 * ((n : ℝ) + 6))) * (poolMaximum n : ℝ) := by
    field_simp [ne_of_gt hden]
    <;> ring
  calc
    |M - A| ≤ |M - K| + |A - K| := htri
    _ ≤ _ := add_le_add hm ha
    _ = _ := hcoeff

end
end Sude
