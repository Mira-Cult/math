import Sude.DirectedResidualPath

/-! Integral directed unit-capacity flow from all one-sided cuts. -/
namespace Sude
noncomputable section

/-- One available residual augmentation respects capacities zero and one. -/
theorem directed_unit_adjustments_preserve_capacity {E : Type*} (flow delta : E → ℤ)
    (hflow : ∀ e, 0 ≤ flow e ∧ flow e ≤ 1)
    (hdelta : ∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < 1) ∨
      (delta e = -1 ∧ 0 < flow e)) :
    ∀ e, 0 ≤ flow e + delta e ∧ flow e + delta e ≤ 1 := by
  intro e
  have hf := hflow e
  rcases hdelta e with hz | ⟨hp, hc⟩ | ⟨hm, hc⟩ <;> omega

/-- Terminating augmentation from a zero flow, for any source of valid
one-unit adjustments. No fractional flow or rounding premise is used. -/
theorem directed_routing_by_unit_augmentations {E : Type*} [Fintype E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ)
    (hstep : ∀ flow : E → ℤ, (∀ e, 0 ≤ flow e ∧ flow e ≤ 1) →
      (∃ x, residualDemand source target d flow x ≠ 0) →
      ∃ (delta : E → ℤ) (u v : Fin n),
        0 < residualDemand source target d flow u ∧
        residualDemand source target d flow v < 0 ∧
        (∀ e, delta e = 0 ∨ (delta e = 1 ∧ flow e < 1) ∨
          (delta e = -1 ∧ 0 < flow e)) ∧
        (∀ x, (∑ e : E, edgeTransfer source target delta e x) = unitTransfer u v x)) :
    ∃ flow : E → ℤ, (∀ e, 0 ≤ flow e ∧ flow e ≤ 1) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  classical
  have loop : ∀ k : ℕ, ∀ flow : E → ℤ,
      (∀ e, 0 ≤ flow e ∧ flow e ≤ 1) →
      (residualMass (residualDemand source target d flow)).toNat = k →
      ∃ final : E → ℤ, (∀ e, 0 ≤ final e ∧ final e ≤ 1) ∧
        ∀ v, (∑ e : E, edgeTransfer source target final e v) = d v := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro flow hflow hmeasure
      by_cases hdone : ∀ v, residualDemand source target d flow v = 0
      · refine ⟨flow, hflow, ?_⟩
        intro v
        have h := hdone v
        dsimp [residualDemand] at h
        omega
      · push Not at hdone
        obtain ⟨delta, u, v, hu, hv, hdelta, hdiv⟩ := hstep flow hflow hdone
        have hcap := directed_unit_adjustments_preserve_capacity flow delta hflow hdelta
        have hres : ∀ x, residualDemand source target d (fun e => flow e + delta e) x =
            residualDemand source target d flow x - unitTransfer u v x := by
          intro x
          rw [residualDemand_add, hdiv x]
        have hmass : residualMass (residualDemand source target d (fun e => flow e + delta e)) =
            residualMass (residualDemand source target d flow) - 2 := by
          rw [show residualDemand source target d (fun e => flow e + delta e) =
              (fun x => residualDemand source target d flow x - unitTransfer u v x) from funext hres]
          exact unit_transfer_decreases_mass (residualDemand source target d flow) u v hu hv
        have hnonneg := residualMass_nonneg (residualDemand source target d (fun e => flow e + delta e))
        have hsmaller : (residualMass (residualDemand source target d (fun e => flow e + delta e))).toNat < k := by
          omega
        exact ih _ hsmaller (fun e => flow e + delta e) hcap rfl
  apply loop ((residualMass (residualDemand source target d (fun _ => 0))).toNat) (fun _ => 0)
  · intro e
    simp
  · rfl

/-- Integral one-sided unit-capacity flow exists whenever every directed cut
has sufficient capacity. Flow values are genuine zeros or ones. -/
theorem directed_unit_flow_of_cut_inequalities {E : Type*} [Fintype E] [DecidableEq E] {n : ℕ}
    (source target : E → Fin n) (d : Fin n → ℤ)
    (hzero : ∑ v, d v = 0)
    (hcut : ∀ S : Finset (Fin n), (∑ v ∈ S, d v) ≤ (directedCutEdges source target S).card) :
    ∃ flow : E → ℤ, (∀ e, 0 ≤ flow e ∧ flow e ≤ 1) ∧
      ∀ v, (∑ e : E, edgeTransfer source target flow e v) = d v := by
  apply directed_routing_by_unit_augmentations source target d
  intro flow hflow hnonzero
  have hreszero := residualDemand_sum_zero source target d flow hzero
  have hpositive := zero_total_nonzero_has_positive _ hreszero hnonzero
  obtain ⟨u, v, hu, hv, hreach⟩ :=
    directed_positive_reaches_negative source target d flow hflow hcut hpositive
  obtain ⟨delta, hdelta, hdiv⟩ := directed_residual_path_adjustment source target flow u v hreach
  exact ⟨delta, u, v, hu, hv, hdelta, hdiv⟩

end
end Sude
