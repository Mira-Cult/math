import Sude.APBTNarrowMinimum
import Sude.BTGrowingPhysical

/-! Transfer midpoint narrowing to indexed actual-pool pair values. -/
namespace Sude
noncomputable section

/-- Positive pool entries bounded by `X` fit into `z` midpoint bins of
width `X/z`; the extra unit in the half-open interval avoids losing the
largest pool prime at the boundary. -/
theorem bounded_positive_pool_midpoint_span (S : Finset ℕ) (X : ℝ) (z : ℕ)
    (hX : 0 < X) (hz : 0 < z) (hpos : ∀ p ∈ S, 0 < p)
    (hupper : ∀ p ∈ S, (p : ℝ) ≤ X) :
    0 < X / z ∧ ∀ p ∈ S, (1 : ℝ) ≤ p ∧ (p : ℝ) < 1 + z * (X / z) := by
  have hzR : (0 : ℝ) < z := by exact_mod_cast hz
  refine ⟨div_pos hX hzR, ?_⟩
  intro p hp
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hpos p hp
  have heq : (z : ℝ) * (X / z) = X := by field_simp
  exact ⟨hpR, by rw [heq]; linarith [hupper p hp]⟩

/-- The source midpoint-bin span follows directly for any subset of the
exact prescribed pool, with `X` equal to its canonical maximum prime. -/
theorem prescribed_pool_midpoint_span (S : Finset ℕ) (n z : ℕ) (hz : 0 < z)
    (hpool : ∀ p ∈ S, p ∈ pool n) :
    0 < (poolMaximum n : ℝ) / z ∧
      ∀ p ∈ S, (1 : ℝ) ≤ p ∧ (p : ℝ) < 1 + z * ((poolMaximum n : ℝ) / z) := by
  apply bounded_positive_pool_midpoint_span S (poolMaximum n) z
  · exact_mod_cast (poolMaximum_prime n).pos
  · exact hz
  · intro p hp
    obtain ⟨i, rfl⟩ := hpool p hp
    exact (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (i.val + 1)).pos
  · intro p hp
    exact_mod_cast pool_le_poolMaximum (hpool p hp)

/-- Every two indexed retained pairs in a narrowed stage have the proved
midpoint spread, with their entries taken from the prescribed prime pool. -/
theorem BTGrowingTrace.poolValues_midpoints {g Q n : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hnarrow : NarrowedStages width stages)
    {P : ℕ} (hlen : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (j : Fin P) (i k : Fin Q) :
    |(((trace.poolValues hlen hpool ((j, i), false)).val : ℝ) +
         (trace.poolValues hlen hpool ((j, i), true)).val) / 2 -
      (((trace.poolValues hlen hpool ((j, k), false)).val : ℝ) +
         (trace.poolValues hlen hpool ((j, k), true)).val) / 2| < width := by
  have h := hnarrow (BTStageTrace.stageAt stages hlen j) (BTStageTrace.stageAt_mem stages hlen j)
    (trace.lowAt hlen j i) (trace.lowAt_mem hlen j i)
    (trace.lowAt hlen j k) (trace.lowAt_mem hlen j k)
  simpa [BTGrowingTrace.poolValues] using h

/-- The physical ordinary-network allocation reads each stage from one
traced batch, so all its indexed pairs retain the midpoint bound. -/
theorem BTGrowingTrace.network_midpoints {g Q n P d r m : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hnarrow : NarrowedStages width stages) (hP : stages.length = P)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (network : Fin 2)
    (layer : Fin m) (e f : Fin n) :
    |(((trace.poolValues hP hpool (prefixNetworkInput hfit hlen network (layer, (e, false)))).val : ℝ) +
         (trace.poolValues hP hpool (prefixNetworkInput hfit hlen network (layer, (e, true)))).val) / 2 -
      (((trace.poolValues hP hpool (prefixNetworkInput hfit hlen network (layer, (f, false)))).val : ℝ) +
         (trace.poolValues hP hpool (prefixNetworkInput hfit hlen network (layer, (f, true)))).val) / 2| < width := by
  let p : Fin P × Fin r := finProdFinEquiv.symm (Fin.cast hlen layer)
  have h := trace.poolValues_midpoints hnarrow hP hpool p.1
    (prefixOrdinaryPairIndex hfit (network, p.2, e))
    (prefixOrdinaryPairIndex hfit (network, p.2, f))
  simpa [prefixNetworkInput, prefixOrdinaryInput, p] using h

/-- Transfer the bound to the actual placed cells whenever the square has
the installed-network entry equations. -/
theorem BTGrowingTrace.placed_network_midpoints {g Q n P d r m : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hnarrow : NarrowedStages width stages) (hP : stages.length = P)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q) (hlen : m = P * r) (network : Fin 2)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin m × (Fin n × Bool) → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (trace.poolValues hP hpool (prefixNetworkInput hfit hlen network x)).val)
    (layer : Fin m) (e f : Fin n) :
    |((entry a (cells (layer, (e, false))) : ℝ) + entry a (cells (layer, (e, true)))) / 2 -
      ((entry a (cells (layer, (f, false))) : ℝ) + entry a (cells (layer, (f, true)))) / 2| < width := by
  simp only [hplaced]
  exact trace.network_midpoints hnarrow hP hpool hfit hlen network layer e f

/-- Corner of one of the two equal-gap pairs in an allocated rectangle. -/
def prefixPairCorner (pair : Fin 2) (side : Bool) : Fin 4 :=
  if pair = 0 then (if side then 1 else 0) else (if side then 2 else 3)

theorem prefixRectangleInput_pair {P d Q : ℕ} (hdiag : (4 * d) * 2 ≤ Q)
    (j : Fin P) (rect : Fin (4 * d)) (pair : Fin 2) (side : Bool) :
    prefixRectangleInput hdiag (finProdFinEquiv (j, rect), prefixPairCorner pair side) =
      ((j, prefixDiagonalPairIndex hdiag (rect, pair)), side) := by
  fin_cases pair <;> cases side <;>
    simp [prefixRectangleInput, prefixPairCorner, prefixCornerCode]

/-- Both rectangle pairs have the exact traced stage gap in the placed
square, including the second pair's reversed corner orientation. -/
theorem BTGrowingTrace.placed_rectangle_pair_gap {g Q n P d : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hP : stages.length = P) (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hdiag : (4 * d) * 2 ≤ Q) (a : Cell n ≃ Fin (n * n))
    (cells : Fin (P * (4 * d)) × Fin 4 → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (trace.poolValues hP hpool (prefixRectangleInput hdiag x)).val)
    (j : Fin P) (rect : Fin (4 * d)) (pair : Fin 2) :
    entry a (cells (finProdFinEquiv (j, rect), prefixPairCorner pair true)) =
      entry a (cells (finProdFinEquiv (j, rect), prefixPairCorner pair false)) +
        (BTStageTrace.stageAt stages hP j).gap := by
  simp only [hplaced, prefixRectangleInput_pair]
  exact trace.poolValues_gap hP hpool j (prefixDiagonalPairIndex hdiag (rect, pair))

/-- Both equal-gap pairs in the actual diagonal rectangles retain the
midpoint bound, including the reversed corner orientation of the second pair. -/
theorem BTGrowingTrace.placed_rectangle_midpoints {g Q n P d : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hnarrow : NarrowedStages width stages) (hP : stages.length = P)
    (hpool : ∀ p ∈ initial, p ∈ pool n) (hdiag : (4 * d) * 2 ≤ Q)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin (P * (4 * d)) × Fin 4 → Cell n)
    (hplaced : ∀ x, entry a (cells x) =
      (trace.poolValues hP hpool (prefixRectangleInput hdiag x)).val)
    (j : Fin P) (u v : Fin (4 * d)) (b c : Fin 2) :
    |((entry a (cells (finProdFinEquiv (j, u), prefixPairCorner b false)) : ℝ) +
         entry a (cells (finProdFinEquiv (j, u), prefixPairCorner b true))) / 2 -
      ((entry a (cells (finProdFinEquiv (j, v), prefixPairCorner c false)) : ℝ) +
         entry a (cells (finProdFinEquiv (j, v), prefixPairCorner c true))) / 2| < width := by
  simp only [hplaced, prefixRectangleInput_pair]
  exact trace.poolValues_midpoints hnarrow hP hpool j
    (prefixDiagonalPairIndex hdiag (u, b)) (prefixDiagonalPairIndex hdiag (v, c))

/-- The exact row and column placements returned by the joint network
installer carry the selected midpoint bound on each physical layer. -/
theorem BTGrowingTrace.packed_networks_midpoints {g Q n P d r : ℕ} {initial final : Finset ℕ}
    {radius last : ℕ} {stages : List BTSelectedStage} {width : ℝ}
    (trace : BTGrowingTrace g Q initial radius final last stages)
    (hnarrow : NarrowedStages width stages) (hP : stages.length = P)
    (hpool : ∀ p ∈ initial, p ∈ pool n)
    (hfit : (4 * d) * 2 + 2 * (r * n) ≤ Q)
    (rows cols : List (LayerPacking.Layer n)) (rowPerms colPerms : List (Equiv.Perm (Fin n)))
    (hrows : rows.length = rowPerms.length) (hcols : cols.length = colPerms.length)
    (hrlen : rowPerms.length = P * r) (hclen : colPerms.length = P * r)
    (a : Cell n ≃ Fin (n * n))
    (hrow : ∀ x, entry a (LayerPacking.sequenceCell rows x) =
      (trace.poolValues hP hpool (prefixNetworkInput hfit hrlen 0 (Fin.cast hrows x.1, x.2))).val)
    (hcol : ∀ x, entry a (LayerPacking.sequenceCell cols x).swap =
      (trace.poolValues hP hpool (prefixNetworkInput hfit hclen 1 (Fin.cast hcols x.1, x.2))).val) :
    (∀ i : Fin rows.length, ∀ e f : Fin n,
      |((entry a (LayerPacking.sequenceCell rows (i, (e, false))) : ℝ) +
           entry a (LayerPacking.sequenceCell rows (i, (e, true)))) / 2 -
        ((entry a (LayerPacking.sequenceCell rows (i, (f, false))) : ℝ) +
           entry a (LayerPacking.sequenceCell rows (i, (f, true)))) / 2| < width) ∧
    (∀ i : Fin cols.length, ∀ e f : Fin n,
      |((entry a (LayerPacking.sequenceCell cols (i, (e, false))).swap : ℝ) +
           entry a (LayerPacking.sequenceCell cols (i, (e, true))).swap) / 2 -
        ((entry a (LayerPacking.sequenceCell cols (i, (f, false))).swap : ℝ) +
           entry a (LayerPacking.sequenceCell cols (i, (f, true))).swap) / 2| < width) := by
  constructor
  · intro i e f
    simp only [hrow]
    exact trace.network_midpoints hnarrow hP hpool hfit hrlen 0 (Fin.cast hrows i) e f
  · intro i e f
    simp only [hcol]
    exact trace.network_midpoints hnarrow hP hpool hfit hclen 1 (Fin.cast hcols i) e f

end
end Sude
