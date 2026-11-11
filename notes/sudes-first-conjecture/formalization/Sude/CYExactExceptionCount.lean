import Sude.CentralExactPool
namespace Sude
noncomputable section

/-- CY's exact total occupancy identity, conditional on the stated full
reservation and actual diagonal-overlap cardinalities. -/
theorem cy_post_diagonal_residual_occupancy {n ρ J : ℕ}
    (R : Finset (Cell n)) (hn : 0 < n) (hodd : Odd n)
    (hR : R.card = ρ*n + 4*J)
    (hinter : (R ∩ (mainCells n ∪ antiCells n)).card = J) :
    ((Finset.univ : Finset (Cell n)) \ (R ∪ (mainCells n ∪ antiCells n))).card +
      ρ*n + 3*J + 2*n = n*n+1 := by
  classical
  let D := mainCells n ∪ antiCells n
  have hdiag := Finset.card_union_add_card_inter (mainCells n) (antiCells n)
  rw [main_anti_intersection hn hodd, mainCells_card, antiCells_card] at hdiag
  simp only [Finset.card_singleton] at hdiag
  have hunion := Finset.card_union_add_card_inter R D
  have hfree := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (R ∪ D))
  simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at hfree
  change (R ∩ D).card = J at hinter
  change D.card + 1 = n+n at hdiag
  change ((Finset.univ : Finset (Cell n)) \ (R ∪ D)).card + ρ*n + 3*J + 2*n = n*n+1
  nlinarith

/-- Combining the exact occupancy and the factor's actual complement count
with k+ρ+5=n gives CY13; no geometry or factor existence is asserted. -/
theorem cy_exact_exception_arithmetic {n ρ J k T N : ℕ}
    (hN : N + ρ*n + 3*J + 2*n = n*n+1)
    (hT : T + k*n = N) (hk : k + ρ + 5 = n) :
    T + 3*J = 3*n+1 ∧ T ≤ 3*n+1 := by
  have hm := congrArg (fun x : ℕ => x*n) hk
  constructor <;> nlinarith

/-- Arithmetic composition for the actual enlarged keepout; the supplied
factor-complement count and full-geometry counts remain hypotheses. -/
theorem cy_actual_exception_count {n ρ J k T : ℕ}
    (R : Finset (Cell n)) (hn : 0 < n) (hodd : Odd n)
    (hR : R.card = ρ*n + 4*J)
    (hinter : (R ∩ (mainCells n ∪ antiCells n)).card = J)
    (hT : T + k*n = ((Finset.univ : Finset (Cell n)) \ (R ∪ (mainCells n ∪ antiCells n))).card)
    (hk : k + ρ + 5 = n) : T + 3*J = 3*n+1 ∧ T ≤ 3*n+1 := by
  exact cy_exact_exception_arithmetic (cy_post_diagonal_residual_occupancy R hn hodd hR hinter) hT hk

end
end Sude
