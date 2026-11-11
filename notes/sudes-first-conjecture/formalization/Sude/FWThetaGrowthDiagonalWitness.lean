import Sude.FWThetaFamilyWitness

/-! The growth-diagonal portion of a selected theta witness. Every field is
about the ordered square and stage data of the supplied family witness. The
record assumes its fields; it does not assert witness existence, transport to
a reference or flow output, or any prime-line conclusion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- Original selected growth labels, signed diagonal identities and midpoint
invoices on the same ordered square as `f`. -/
structure FWThetaGrowthDiagonalWitness
    (n L : ℕ) (choice : Fin L → Bool) (f : FWThetaFamilyWitness n L choice) where
  T : Fin f.stages.length → Finset ℕ
  U : Fin f.stages.length → Finset ℕ
  V : Fin f.stages.length → Finset ℕ
  selected : ∀ j, T j ⊆ (f.stages.get j).lows ∧ U j ⊆ (f.stages.get j).lows \ T j ∧
    V j ⊆ (f.stages.get j).lows \ (T j ∪ U j) ∧
    (T j).card = 12 ∧ (U j).card = 12 ∧ (V j).card = 24
  slot_images : ∀ j,
    (fwGrowthMainSlots n).image (fun i => f.trace.lowAt rfl j (f.τ j i)) = T j ∧
    (fwGrowthAntiSlots n).image (fun i => f.trace.lowAt rfl j (f.τ j i)) = U j ∧
    (fwGrowthPartnerSlots n).image (fun i => f.trace.lowAt rfl j (f.τ j i)) = V j
  main_identity :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    (∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ mainCells n), (entry f.ordered c : ℝ)) =
      (∑ j, ∑ p ∈ T j, growthStageMidpoint (f.stages.get j) p) -
        6 * ∑ j, ((f.stages.get j).gap : ℝ)
  anti_identity :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    (∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ antiCells n), (entry f.ordered c : ℝ)) =
      (∑ j, ∑ p ∈ U j, growthStageMidpoint (f.stages.get j) p) -
        6 * ∑ j, ((f.stages.get j).gap : ℝ)
  midpoint_bounds :
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    let E1 := (∑ j, ∑ p ∈ T j, growthStageMidpoint (f.stages.get j) p) - (12 : ℝ) * ∑ j, μ j
    let D2 := (∑ j, ∑ p ∈ U j, growthStageMidpoint (f.stages.get j) p) - (12 : ℝ) * ∑ j, μ j
    let E2 := (∑ j, ∑ p ∈ T j ∪ U j, growthStageMidpoint (f.stages.get j) p) - (24 : ℝ) * ∑ j, μ j
    let E3 := (∑ j, ∑ p ∈ (T j ∪ U j) ∪ V j, growthStageMidpoint (f.stages.get j) p) - (48 : ℝ) * ∑ j, μ j
    |E1| ≤ ((poolMaximum n : ℝ) / 6) / 2 ∧
    |D2| ≤ ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6) ∧
    |E2| ≤ ((n + 5 : ℝ) / (n + 6)) * ((poolMaximum n : ℝ) / 6) ∧
    |E3| ≤ (3 / 2 : ℝ) * ((poolMaximum n : ℝ) / 6) ∧
    (0 < (poolMaximum n : ℝ) / 6 → |E3| < (3 / 2 : ℝ) * ((poolMaximum n : ℝ) / 6))
  main_deviation :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    |(∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ mainCells n), (entry f.ordered c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤ ((poolMaximum n : ℝ) / 6) / 2
  anti_deviation :
    let growth := btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6))
      f.hoff f.hs choice f.gr f.gc f.hgr f.hgc
    let μ := fun j => (∑ p ∈ (f.stages.get j).lows, growthStageMidpoint (f.stages.get j) p) / (6 * (n + 8) : ℕ)
    |(∑ c ∈ (Finset.univ.image growth).filter (fun c => c ∈ antiCells n), (entry f.ordered c : ℝ)) -
      ((12 : ℝ) * ∑ j, μ j - 6 * ∑ j, ((f.stages.get j).gap : ℝ))| ≤
        ((n + 8 : ℝ) / (2 * (n + 6))) * ((poolMaximum n : ℝ) / 6)

end
end Sude
