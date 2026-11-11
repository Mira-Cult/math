import Sude.PhysicalPairLineSum
import Sude.Switches

/-! Split full labelled line sums into actual selected pairs and every residual cell. -/
namespace Sude
noncomputable section

/-- Every full line sum splits into the midpoint/orientation contribution
of the distinct selected physical pairs plus the sum of all remaining line
cells. No assumption that labelled lines are distinct is made. -/
theorem fullLine_sum_pair_and_residual {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hcells : Function.Injective cells)
    (line : Finset (Cell n)) (a : Cell n ≃ Fin (n * n)) :
    (∑ c ∈ line, (entry a c : ℝ)) =
      (∑ i, (physicalPairLineWeight cells (fun c => c ∈ line) i *
        (((entry a (cells (i, false)) : ℝ) + entry a (cells (i, true))) / 2) +
      physicalPairLineOrientation cells (fun c => c ∈ line) i *
        (((entry a (cells (i, true)) : ℝ) - entry a (cells (i, false))) / 2))) +
      ∑ c ∈ line \ Finset.univ.image cells, (entry a c : ℝ) := by
  classical
  let selected := Finset.univ.image cells
  let onLine := selected.filter (fun c => c ∈ line)
  have hdis : Disjoint onLine (line \ selected) := by
    apply Finset.disjoint_left.mpr
    intro c hc hr
    exact (Finset.mem_sdiff.mp hr).2 (Finset.mem_filter.mp hc).1
  have hpartition : line = onLine ∪ (line \ selected) := by
    ext c
    simp [onLine]
    tauto
  have hselected := physicalPair_line_sum_midpoint cells hcells (fun c => c ∈ line) a
  change (∑ c ∈ onLine, (entry a c : ℝ)) = _ at hselected
  calc
    _ = (∑ c ∈ onLine, (entry a c : ℝ)) + ∑ c ∈ line \ selected, (entry a c : ℝ) := by
      calc
        _ = ∑ c ∈ onLine ∪ (line \ selected), (entry a c : ℝ) :=
          congrArg (fun s : Finset (Cell n) => ∑ c ∈ s, (entry a c : ℝ)) hpartition
        _ = _ := Finset.sum_union hdis
    _ = _ := by rw [hselected]

/-- If the odd-order center is outside the selected pairs, it is retained
in the residual part of both labelled diagonals, including order one. -/
theorem center_mem_both_line_residuals {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hn : 0 < n) (hodd : Odd n)
    (hcenter : (centerIndex n hn, centerIndex n hn) ∉ Finset.univ.image cells) :
    (centerIndex n hn, centerIndex n hn) ∈ mainCells n \ Finset.univ.image cells ∧
    (centerIndex n hn, centerIndex n hn) ∈ antiCells n \ Finset.univ.image cells := by
  have hc := centerCell_on_both_diagonals n hn hodd
  exact ⟨Finset.mem_sdiff.mpr ⟨hc.1, hcenter⟩, Finset.mem_sdiff.mpr ⟨hc.2, hcenter⟩⟩

end
end Sude
