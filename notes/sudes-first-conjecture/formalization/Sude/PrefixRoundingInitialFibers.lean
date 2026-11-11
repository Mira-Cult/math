import Sude.CentralWindow

/-! Initial groupwise fractions for one simultaneous prefix-rounding level. -/
namespace Sude
noncomputable section

/-- The initial coordinate assigns each slot the prescribed group fraction. -/
def prefixGroupInitial {S G : Type*} [DecidableEq G]
    (U : Finset S) (group : S → G) (m : G → ℕ) (s : S) : ℝ :=
  (m (group s) : ℝ) / ((U.filter (fun t => group t = group s)).card : ℝ)

/-- On actual slots, the initial coordinate belongs to the unit interval. -/
theorem prefix_group_initial_box {S G : Type*} [DecidableEq G]
    (U : Finset S) (group : S → G) (m : G → ℕ)
    (hm : ∀ g, m g ≤ (U.filter (fun t => group t = g)).card)
    (s : S) (hs : s ∈ U) :
    0 ≤ prefixGroupInitial U group m s ∧ prefixGroupInitial U group m s ≤ 1 := by
  classical
  have hmem : s ∈ U.filter (fun t => group t = group s) := Finset.mem_filter.mpr ⟨hs, rfl⟩
  have hpos : 0 < (U.filter (fun t => group t = group s)).card := Finset.card_pos.mpr ⟨s, hmem⟩
  have hp : (0 : ℝ) < ((U.filter (fun t => group t = group s)).card : ℝ) := by exact_mod_cast hpos
  have hle : (m (group s) : ℝ) ≤ ((U.filter (fun t => group t = group s)).card : ℝ) := by
    exact_mod_cast hm (group s)
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hp)
  · exact (div_le_one hp).mpr hle

/-- The full initial sum in each group is the prescribed integer, including
empty groups, whose prescribed cardinality is necessarily zero. -/
theorem prefix_group_initial_sum {S G : Type*} [DecidableEq G]
    (U : Finset S) (group : S → G) (m : G → ℕ)
    (hm : ∀ g, m g ≤ (U.filter (fun t => group t = g)).card) (g : G) :
    (∑ s ∈ U, if group s = g then prefixGroupInitial U group m s else 0) = (m g : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  let B := U.filter (fun t => group t = g)
  have heq : ∀ s ∈ B, prefixGroupInitial U group m s = (m g : ℝ) / (B.card : ℝ) := by
    intro s hs
    have hsg : group s = g := (Finset.mem_filter.mp hs).2
    simp [prefixGroupInitial, hsg, B]
  change (∑ s ∈ B, prefixGroupInitial U group m s) = (m g : ℝ)
  rw [Finset.sum_congr rfl heq]
  by_cases hB : B.card = 0
  · have hmzero : m g = 0 := by have h := hm g; change m g ≤ B.card at h; omega
    have hBempty : B = ∅ := Finset.card_eq_zero.mp hB
    simp [hBempty, hmzero]
  · have hBreal : (B.card : ℝ) ≠ 0 := by exact_mod_cast hB
    simp only [Finset.sum_const, nsmul_eq_mul]
    field_simp

end
end Sude
