import Sude.FlowRealization

/-! Cut bounds for the FC2K routing step. These results do not assert the
existence of a graph with the expansion property or of an integral flow. -/
namespace Sude
noncomputable section

/-- Each edge occurrence is counted separately, including parallel edges. -/
def cutEdges {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (S : Finset (Fin n)) : Finset E :=
  Finset.univ.filter fun e => (source e ∈ S ∧ target e ∉ S) ∨
    (source e ∉ S ∧ target e ∈ S)

/-- A zero-total bounded demand is bounded by either side of every cut. -/
theorem zero_total_cut_demand {n : ℕ} (d : Fin n → ℤ) (B : ℕ)
    (hzero : ∑ v, d v = 0) (hbound : ∀ v, |d v| ≤ (B : ℤ))
    (S : Finset (Fin n)) :
    |∑ v ∈ S, d v| ≤ ((B * min S.card (n - S.card) : ℕ) : ℤ) := by
  have each (T : Finset (Fin n)) :
      |∑ v ∈ T, d v| ≤ (B : ℤ) * T.card := by
    calc
      _ ≤ ∑ v ∈ T, |d v| := Finset.abs_sum_le_sum_abs d T
      _ ≤ ∑ _v ∈ T, (B : ℤ) := Finset.sum_le_sum (fun v _ => hbound v)
      _ = (B : ℤ) * T.card := by simp [mul_comm]
  have hcompl : (∑ v ∈ Sᶜ, d v) = -(∑ v ∈ S, d v) := by
    have h := Finset.sum_add_sum_compl S d
    rw [hzero] at h
    omega
  have hleft := each S
  have hright := each Sᶜ
  rw [hcompl, abs_neg] at hright
  simp only [Finset.card_compl, Fintype.card_fin] at hright
  rcases le_total S.card (n - S.card) with h | h
  · simpa [Nat.min_eq_left h, mul_comm] using hleft
  · simpa [Nat.min_eq_right h, mul_comm] using hright

/-- Across a cut a bounded edge contributes at most its capacity;
non-crossing edges, including loops, contribute exactly zero. -/
theorem edgeTransfer_cut_bound {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ)) (S : Finset (Fin n)) (e : E) :
    |∑ v ∈ S, edgeTransfer source target flow e v| ≤
      if e ∈ cutEdges source target S then (C : ℤ) else 0 := by
  classical
  by_cases hs : source e ∈ S <;> by_cases ht : target e ∈ S <;>
    simp [edgeTransfer, Finset.sum_sub_distrib, cutEdges, hs, ht, hflow e]

/-- Every bounded physical edge flow satisfies the corresponding cut bound. -/
theorem bounded_flow_cut_inequality {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ)) (S : Finset (Fin n)) :
    |∑ v ∈ S, ∑ e : E, edgeTransfer source target flow e v| ≤
      ((C * (cutEdges source target S).card : ℕ) : ℤ) := by
  classical
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ e : E, |∑ v ∈ S, edgeTransfer source target flow e v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e : E, if e ∈ cutEdges source target S then (C : ℤ) else 0 :=
      Finset.sum_le_sum (fun e _ => edgeTransfer_cut_bound source target flow C hflow S e)
    _ = _ := by simp [mul_comm]

/-- The signed divergence of any family of edge values has total zero. -/
theorem edge_divergence_sum_zero {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (flow : E → ℤ) :
    (∑ v : Fin n, ∑ e : E, edgeTransfer source target flow e v) = 0 := by
  classical
  rw [Finset.sum_comm]
  simp [edgeTransfer, Finset.sum_sub_distrib]

/-- A supplied bounded flow necessarily has zero-total demand and satisfies
all cut inequalities, with exactly the same sign convention as the
physical realization theorem. This is the necessary direction only. -/
theorem bounded_flow_necessary_conditions {E : Type*} [Fintype E] [DecidableEq E]
    {n : ℕ} (source target : E → Fin n) (flow : E → ℤ) (C : ℕ)
    (hflow : ∀ e, |flow e| ≤ (C : ℤ)) (d : Fin n → ℤ)
    (hdiv : ∀ v, d v = ∑ e : E, edgeTransfer source target flow e v) :
    (∑ v, d v = 0) ∧ ∀ S : Finset (Fin n),
      |∑ v ∈ S, d v| ≤ ((C * (cutEdges source target S).card : ℕ) : ℤ) := by
  constructor
  · simp_rw [hdiv]
    exact edge_divergence_sum_zero source target flow
  · intro S
    simp_rw [hdiv]
    exact bounded_flow_cut_inequality source target flow C hflow S

/-- Integer arithmetic form of the expansion/capacity comparison. -/
theorem scaled_cut_capacity (scale expansion B C m crossing : ℕ)
    (hscale : 0 < scale) (hbox : scale * B ≤ expansion * C)
    (hexp : expansion * m ≤ scale * crossing) : B * m ≤ C * crossing := by
  apply Nat.le_of_mul_le_mul_left (c := scale) _ hscale
  calc
    scale * (B * m) = (scale * B) * m := by ring
    _ ≤ (expansion * C) * m := Nat.mul_le_mul_right m hbox
    _ = C * (expansion * m) := by ring
    _ ≤ C * (scale * crossing) := Nat.mul_le_mul_left C hexp
    _ = scale * (C * crossing) := by ring

/-- FC2K's expansion hypothesis and rounded capacity imply every cut
inequality for the whole zero-total demand box. Graph construction and
integral flow existence remain separate obligations. -/
theorem fc2k_cut_inequalities {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ) (N B : ℕ)
    (hN : 2000 ≤ N) (hB : 400000 * B < 199 * 999 * N)
    (hzero : ∑ v, d v = 0) (hbound : ∀ v, |d v| ≤ (B : ℤ))
    (hexp : ∀ S : Finset (Fin n),
      199 * min S.card (n - S.card) ≤ 200 * (cutEdges source target S).card) :
    ∀ S : Finset (Fin n),
      |∑ v ∈ S, d v| ≤ (((N / 2) * (cutEdges source target S).card : ℕ) : ℤ) := by
  intro S
  have hgate := fc2k_floor_capacity_gate N B hN hB
  have hnum := scaled_cut_capacity 200 199 B (N / 2)
    (min S.card (n - S.card)) (cutEdges source target S).card
    (by decide) (Nat.le_of_lt hgate) (hexp S)
  exact (zero_total_cut_demand d B hzero hbound S).trans (by exact_mod_cast hnum)

end
end Sude
