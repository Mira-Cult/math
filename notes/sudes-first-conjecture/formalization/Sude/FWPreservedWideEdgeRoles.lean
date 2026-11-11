import Sude.FWPhysicalBridgeWideTrace
import Sude.FWWideEdgeRoles

/-! Transport selected wide-edge gaps through the actual early-role
preservation interface. No cell disjointness or trace crossing is asserted. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Preserving the early role cells preserves each fixed-edge wide pair in
both networks, with one common positive even gap and its numeric bounds. -/
theorem fw_preserved_wide_edge_physical_gap {n L : ℕ}
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (old grown : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice rows cols hr hc sr sc hsr hsc wr wc hwr hwc,
      entry grown c = entry old c)
    (hgap : let cells := fwWideSequenceCells blocks hlen hwide hs choice wr wc hwr hwc
      ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry old (cells (i, 1)) = entry old (cells (i, 0)) + gap ∧
        entry old (cells (i, 2)) = entry old (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n)
    (j : Fin (3 * (n / 450))) (k : Fin 3) (e : Fin n) :
    ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
      (∀ network : Bool,
        entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network true)) =
        entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc (fwWideEdgeRole n j k e network false)) + gap) ∧
      (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n := by
  have hpreserved := fw_preserved_wide_block_gaps blocks hlen hrect hseed hwide hs choice rows cols hr hc
    sr sc hsr hsc wr wc hwr hwc old grown hfixed hgap
  exact fw_wide_edge_physical_gap (poolMaximum n) blocks hlen hwide hs choice wr wc hwr hwc grown hpreserved j k e

end
end Sude
