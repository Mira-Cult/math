import Sude.ActiveSupportFullKeepout
import Sude.CentralPhysicalPlacement

/-! Exact same-reservation transport of cancellation quantities. The stage-sum
and spare-cell conditions are explicit; no numerical or later-flow bound is asserted. -/
namespace Sude
noncomputable section

variable {n : ℕ} {I J : Type*} [Fintype I] [Fintype J]

def fullReservationStageMean (a : Cell n ≃ Fin (n * n))
    (cells : (I × J) × Bool → Cell n) (j : I) : ℝ :=
  (∑ i, (((entry a (cells ((j, i), false)) : ℝ) +
    entry a (cells ((j, i), true))) / 2)) / (Fintype.card J : ℝ)

def fullReservationMeanDeviation (a : Cell n ≃ Fin (n * n))
    (cells : (I × J) × Bool → Cell n) (μ : ℝ) : ℝ :=
  ∑ j, (fullReservationStageMean a cells j - μ)

def fullReservationSpareDeviation (a : Cell n ≃ Fin (n * n))
    (roles full : Finset (Cell n)) (μ : ℝ) : ℝ :=
  (∑ z ∈ full \ roles, (entry a z : ℝ)) - ((full \ roles).card : ℝ) * μ

/-- Preservation of the stage sums, spare entries and full value image preserves
all cancellation ingredients and the resulting scalar expression. -/
theorem full_reservation_cancellation_transport
    (a b : Cell n ≃ Fin (n * n)) (cells : (I × J) × Bool → Cell n)
    (roles full : Finset (Cell n)) (μ : ℝ)
    (hstage : ∀ j : I,
      (∑ i : J, (((entry a (cells ((j, i), false)) : ℝ) +
        entry a (cells ((j, i), true))) / 2)) =
      (∑ i : J, (((entry b (cells ((j, i), false)) : ℝ) +
        entry b (cells ((j, i), true))) / 2)))
    (hspare : ∀ z ∈ full \ roles, entry a z = entry b z)
    (hfull : full.image (entry a) = full.image (entry b)) :
    (∀ j, fullReservationStageMean a cells j = fullReservationStageMean b cells j) ∧
    fullReservationMeanDeviation a cells μ = fullReservationMeanDeviation b cells μ ∧
    fullReservationSpareDeviation a roles full μ = fullReservationSpareDeviation b roles full μ ∧
    actualUnusedPool a full = actualUnusedPool b full ∧
    (∀ α k : ℝ, α * fullReservationMeanDeviation a cells μ +
        k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
      α * fullReservationMeanDeviation b cells μ +
        k * (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ)) := by
  classical
  have hm : ∀ j, fullReservationStageMean a cells j = fullReservationStageMean b cells j := by
    intro j
    simp only [fullReservationStageMean, hstage j]
  have hA : fullReservationMeanDeviation a cells μ = fullReservationMeanDeviation b cells μ := by
    simp only [fullReservationMeanDeviation, hm]
  have hD : fullReservationSpareDeviation a roles full μ =
      fullReservationSpareDeviation b roles full μ := by
    unfold fullReservationSpareDeviation
    congr 1
    apply Finset.sum_congr rfl
    intro z hz
    exact_mod_cast hspare z hz
  have hu := actualUnusedPool_eq_of_role_value_image_eq a b full hfull
  refine ⟨hm, hA, hD, hu, ?_⟩
  intro α k
  rw [hA, hu]

/-- Equal active images and agreement outside that support also suffice when
active is contained in roles and roles in full. -/
theorem full_reservation_cancellation_transport_of_active
    (a b : Cell n ≃ Fin (n * n)) (cells : (I × J) × Bool → Cell n)
    (active roles full : Finset (Cell n)) (μ : ℝ)
    (hactiveRoles : active ⊆ roles) (hrolesFull : roles ⊆ full)
    (hfixed : ∀ z ∉ active, entry b z = entry a z)
    (himage : active.image (entry b) = active.image (entry a))
    (hstage : ∀ j : I,
      (∑ i : J, (((entry a (cells ((j, i), false)) : ℝ) +
        entry a (cells ((j, i), true))) / 2)) =
      (∑ i : J, (((entry b (cells ((j, i), false)) : ℝ) +
        entry b (cells ((j, i), true))) / 2))) :
    (∀ j, fullReservationStageMean a cells j = fullReservationStageMean b cells j) ∧
    fullReservationMeanDeviation a cells μ = fullReservationMeanDeviation b cells μ ∧
    fullReservationSpareDeviation a roles full μ = fullReservationSpareDeviation b roles full μ ∧
    actualUnusedPool a full = actualUnusedPool b full ∧
    (∀ α k : ℝ, α * fullReservationMeanDeviation a cells μ +
        k * (centralEntriesMean (actualUnusedPool a full) centralPoolValue - μ) =
      α * fullReservationMeanDeviation b cells μ +
        k * (centralEntriesMean (actualUnusedPool b full) centralPoolValue - μ)) := by
  classical
  have hfull := full_keepout_value_image_and_unused_eq a b active full
    (hactiveRoles.trans hrolesFull) hfixed himage
  apply full_reservation_cancellation_transport a b cells roles full μ hstage
  · intro z hz
    have hz' : z ∉ active := by
      intro ha
      exact (Finset.mem_sdiff.mp hz).2 (hactiveRoles ha)
    exact (hfixed z hz').symm
  · exact hfull.1.symm

end
end Sude
