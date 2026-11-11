import Sude.ReservedPoolMean
import Sude.CentralExactPool

/-! Connect original-pool midpoint accounting to actual diagonal placement. -/
namespace Sude
noncomputable section

/-- A row meets the two labelled diagonals in at most two cells, even when
they coincide at the center. -/
theorem row_unreserved_diagonal_card_le_two {n : ℕ} (reserved : Finset (Cell n)) (r : Fin n) :
    (rowCells r ∩ unreservedDiagonalCells reserved).card ≤ 2 := by
  classical
  have hsub : rowCells r ∩ unreservedDiagonalCells reserved ⊆
      ({(r, r), (r, r.rev)} : Finset (Cell n)) := by
    intro z hz
    obtain ⟨hzrow, hzdiag⟩ := Finset.mem_inter.mp hz
    have hr := (mem_rowCells r z).mp hzrow
    have hd := (Finset.mem_sdiff.mp hzdiag).1
    rcases Finset.mem_union.mp hd with hm | ha
    · have hm' := (mem_mainCells z).mp hm
      have he : z = (r, r) := Prod.ext hr (hm'.symm.trans hr)
      simp [he]
    · have ha' := (mem_antiCells z).mp ha
      have he : z = (r, r.rev) := Prod.ext hr (ha'.trans (congrArg Fin.rev hr))
      simp [he]
  exact (Finset.card_le_card hsub).trans (by
    simpa using Finset.card_insert_le (r, r) ({(r, r.rev)} : Finset (Cell n)))

/-- The corresponding bound for a column uses the total index reversal. -/
theorem column_unreserved_diagonal_card_le_two {n : ℕ} (reserved : Finset (Cell n)) (c : Fin n) :
    (columnCells c ∩ unreservedDiagonalCells reserved).card ≤ 2 := by
  classical
  have hsub : columnCells c ∩ unreservedDiagonalCells reserved ⊆
      ({(c, c), (c.rev, c)} : Finset (Cell n)) := by
    intro z hz
    obtain ⟨hzcol, hzdiag⟩ := Finset.mem_inter.mp hz
    have hc := (mem_columnCells c z).mp hzcol
    have hd := (Finset.mem_sdiff.mp hzdiag).1
    rcases Finset.mem_union.mp hd with hm | ha
    · have hm' := (mem_mainCells z).mp hm
      have he : z = (c, c) := Prod.ext (hm'.trans hc) hc
      simp [he]
    · have ha' := (mem_antiCells z).mp ha
      have hzrev : z.1 = c.rev := by
        have h := congrArg Fin.rev (ha'.symm.trans hc)
        simpa using h
      have he : z = (c.rev, c) := Prod.ext hzrev hc
      simp [he]
  exact (Finset.card_le_card hsub).trans (by
    simpa using Finset.card_insert_le (c, c) ({(c.rev, c)} : Finset (Cell n)))

/-- Starting from globally distinct reserved physical pairs, use their
midpoint budgets to justify the central diagonal placement and track the
post-diagonal mean relative to the original source mean `T/n²`.
The two-sided prime-stock bounds are explicit inputs. -/
theorem central_diagonals_from_reserved_pairs {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (pair : I × Bool → Cell n) (budget : I → ℝ) (η : ℝ)
    (hη : 0 < η) (hn : 20 ≤ n) (hodd : Odd n)
    (hinj : Function.Injective pair)
    (hcover : (Finset.univ : Finset (I × Bool)).image pair = reserved)
    (hcenter : centralCell n (by omega) ∉ reserved)
    (hreserved : 4 * reserved.card ≤ n * n)
    (hpair : ∀ i, |(entry a (pair (i, true)) : ℝ) + (entry a (pair (i, false)) : ℝ) -
      2 * ((Lucas.poolTotal n : ℝ) / (n * n : ℕ))| ≤ budget i)
    (hbudget : (∑ i, budget i) / (n * n - reserved.card : ℕ) ≤ η / 4)
    (hlow : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter (fun v =>
        (Lucas.poolTotal n : ℝ) / (n * n : ℕ) - η < centralPoolValue v ∧
        centralPoolValue v ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) - η / 2)).card)
    (hhigh : 1 + (centralFreeMain (by omega) reserved).card + (centralFreeAnti (by omega) reserved).card ≤
      ((actualUnusedPool a reserved).filter (fun v =>
        (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + η / 2 < centralPoolValue v ∧
        centralPoolValue v ≤ (Lucas.poolTotal n : ℝ) / (n * n : ℕ) + η)).card) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ z ∈ reserved, entry b z = entry a z) ∧
      (∀ z ∈ unreservedDiagonalCells reserved,
        |(entry b z : ℝ) - (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤ η) ∧
      n * n / 2 ≤ (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        centralEntriesMean (actualUnusedPool a reserved) centralPoolValue| ≤
          3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
        (Lucas.poolTotal n : ℝ) / (n * n : ℕ)| ≤
        (∑ i, budget i) / (n * n - reserved.card : ℕ) +
          3 * η / (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)).card ∧
      |(mainSum b : ℝ) - ((∑ z ∈ mainCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeMain (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ 2 * η ∧
      |(antiSum b : ℝ) - ((∑ z ∈ antiCells n ∩ reserved, (entry a z : ℝ)) +
        ((1 + (centralFreeAnti (by omega) reserved).card : ℕ) : ℝ) *
          centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)| ≤ (201 / 100) * η ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  have hsmall : reserved.card < n * n := by nlinarith
  have hmean0 := actual_unused_mean_from_reserved_pairs_source a reserved pair budget hinj hcover hsmall hpair
  have hmean := hmean0.trans hbudget
  obtain ⟨b, A, B, C, _, _, _, _, _, _, hfixed, hcentral, _, hcount, _, _, hshift,
      hmain, hanti, hpool, hinject⟩ :=
    central_place_odd_diagonals_exact_pool a reserved ((Lucas.poolTotal n : ℝ) / (n * n : ℕ)) η
      hη hn hodd hcenter hreserved hmean hlow hhigh
  refine ⟨b, hfixed, hcentral, hcount, hshift, ?_, hmain, hanti, hpool, hinject⟩
  have htriangle := abs_add_le
    (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue)
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ))
  have heq : centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ) =
    (centralEntriesMean (actualUnusedPool b (reserved ∪ unreservedDiagonalCells reserved)) centralPoolValue -
      centralEntriesMean (actualUnusedPool a reserved) centralPoolValue) +
    (centralEntriesMean (actualUnusedPool a reserved) centralPoolValue -
      (Lucas.poolTotal n : ℝ) / (n * n : ℕ)) := by ring
  rw [heq]
  linarith

end
end Sude
