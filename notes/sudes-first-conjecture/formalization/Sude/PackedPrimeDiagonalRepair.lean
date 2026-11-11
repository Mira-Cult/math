import Sude.DiagonalTargetFromVector
import Sude.PackedCenteredDiagonalAdapter

/-! Conditional prime-diagonal repair after row/column routing.  The packed
rectangle grids and the chosen centered reference's baseline are supplied. -/
namespace Sude
noncomputable section

/-- Given prime rows and columns on a routed square which still agrees with the
installed rectangle support and diagonal sums, select one already-supplied
prime target for both diagonals. After the controller chooses its common
center, a bound around that exact centered reference and two radius budgets
suffice for a valid square. No prime supply or baseline estimate is asserted. -/
theorem packed_prime_diagonal_repair {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : Odd n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Rm Ra : ℕ) (a b : Cell n ≃ Fin (n*n)) (keep : Finset (Cell n))
    (hm : CompleteEvenGrid (active.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (active.filter fun i => choice i = false) gap Ra)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ keep, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i))
    (hagree : ∀ z ∈ packedLabelSupport hs choice active, entry b z = entry a z)
    (hmain : mainSum b = mainSum a) (hanti : antiSum b = antiSum a)
    (hrows : ∀ r, Nat.Prime (rowSum b r)) (hcols : ∀ c, Nat.Prime (columnSum b c))
    (f : Fin n → ℕ) (y U D : ℝ)
    (hf : ∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) :
    ∃ before : Finset (Fin L), before ⊆ active ∧
      let reference := packedTradeSequence hs choice a before.toList
      (|(mainSum reference : ℝ) - y| ≤ U →
       |(antiSum reference : ℝ) - y| ≤ U →
       U + D ≤ (evenGridCenter Rm : ℝ) →
       U + D ≤ (evenGridCenter Ra : ℝ) →
       ∃ (q : ℕ) (result : Cell n ≃ Fin (n*n)),
         Nat.Prime q ∧ (∃ i, q = f i) ∧
         (∀ r, rowSum result r = rowSum b r) ∧
         (∀ c, columnSum result c = columnSum b c) ∧
         mainSum result = q ∧ antiSum result = q ∧ Valid result ∧
         Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
         (∀ c ∈ keep, entry result c = entry b c)) := by
  classical
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  obtain ⟨before, hbefore, hcontroller⟩ :=
    packed_centered_diagonal_adapter hs hL hnpos choice gap active Rm Ra a keep hm ha hgaps hprotect
  refine ⟨before, hbefore, ?_⟩
  dsimp only
  intro hmr har hbudgetm hbudgeta
  let reference := packedTradeSequence hs choice a before.toList
  have hi : 0 < n := hnpos
  let i : Fin n := ⟨0, hi⟩
  have hq := hf i
  -- Use one explicit vector entry for both diagonals.
  have hmEven : (2 : ℤ) ∣ ((f i : ℤ) - mainSum reference) := by
    exact ⟨halfLineDemand (f i) (mainSum reference),
      (halfLineDemand_exact _ _ hq.2.1 (mainSum_odd_of_odd_order hn reference)).symm⟩
  have haEven : (2 : ℤ) ∣ ((f i : ℤ) - antiSum reference) := by
    exact ⟨halfLineDemand (f i) (antiSum reference),
      (halfLineDemand_exact _ _ hq.2.1 (antiSum_odd_of_odd_order hn reference)).symm⟩
  have hdistm' : |(f i : ℝ) - (mainSum reference : ℝ)| ≤ U + D := by
    have h := abs_add_le ((f i : ℝ) - y) (y - (mainSum reference : ℝ))
    have hy : |y - (mainSum reference : ℝ)| ≤ U := by simpa only [abs_sub_comm] using hmr
    have heq : (f i : ℝ) - (mainSum reference : ℝ) =
        ((f i : ℝ) - y) + (y - (mainSum reference : ℝ)) := by ring
    rw [heq]; linarith [hq.2.2]
  have hdista' : |(f i : ℝ) - (antiSum reference : ℝ)| ≤ U + D := by
    have h := abs_add_le ((f i : ℝ) - y) (y - (antiSum reference : ℝ))
    have hy : |y - (antiSum reference : ℝ)| ≤ U := by simpa only [abs_sub_comm] using har
    have heq : (f i : ℝ) - (antiSum reference : ℝ) =
        ((f i : ℝ) - y) + (y - (antiSum reference : ℝ)) := by ring
    rw [heq]; linarith [hq.2.2]
  have hmbound : |((f i : ℤ) - mainSum reference)| ≤ (evenGridCenter Rm : ℤ) := by
    exact_mod_cast hdistm'.trans hbudgetm
  have habound : |((f i : ℤ) - antiSum reference)| ≤ (evenGridCenter Ra : ℤ) := by
    exact_mod_cast hdista'.trans hbudgeta
  obtain ⟨hml, hmu⟩ := abs_le.mp hmbound
  obtain ⟨hal, hau⟩ := abs_le.mp habound
  obtain ⟨result, hr, hc, hmd, had, hpool, hinj, hcenter, hfixed⟩ :=
    hcontroller b hagree hmain hanti ((f i : ℤ) - mainSum reference)
      ((f i : ℤ) - antiSum reference) hmEven haEven hml hmu hal hau
  change (mainSum result : ℤ) - (mainSum reference : ℤ) =
    (f i : ℤ) - (mainSum reference : ℤ) at hmd
  change (antiSum result : ℤ) - (antiSum reference : ℤ) =
    (f i : ℤ) - (antiSum reference : ℤ) at had
  have hmainq : mainSum result = f i := by exact_mod_cast (by omega : (mainSum result : ℤ) = f i)
  have hantiq : antiSum result = f i := by exact_mod_cast (by omega : (antiSum result : ℤ) = f i)
  refine ⟨f i, result, hq.1, ⟨i, rfl⟩, hr, hc, hmainq, hantiq, ?_, hpool, hinj, hfixed⟩
  exact ⟨fun r => by rw [hr r]; exact hrows r,
    fun c => by rw [hc c]; exact hcols c,
    by rw [hmainq]; exact hq.1, by rw [hantiq]; exact hq.1⟩

end
end Sude
