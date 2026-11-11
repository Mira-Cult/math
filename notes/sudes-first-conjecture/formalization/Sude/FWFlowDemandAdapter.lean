import Sude.FWPermutationDemandRouting
import Sude.FWCenteredSuppliedFlows

/-! Route supplied bounded zero-total demands through an existing FW physical
flow interface. No target vectors, discrepancy bounds, or prime lines are supplied. -/
namespace Sude
noncomputable section

/-- If one reference already realizes all bounded flows on the same FW graph,
then any supplied zero-total demand vectors in the stated exact box can be
realized from that reference. The capacity uses labelled edge occurrences. -/
theorem fw_supplied_flows_realize_demand_box {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n))
    (b₀ : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n)) (N B : ℕ)
    (hexp : ∀ S : Finset (Fin n),
      519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (hcapacity : 500 * B ≤ 519 * (N / 2))
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n,
            edgeTransfer (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n,
            edgeTransfer (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b)) :
    ∀ dr dc : Fin n → ℤ,
      (∑ r, dr r = 0) → (∑ c, dc c = 0) →
      (∀ r, |dr r| ≤ (B : ℤ)) → (∀ c, |dc c| ≤ (B : ℤ)) →
      ∃ b : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) = 2 * dr r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) = 2 * dc c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  intro dr dc hzr hzc hbr hbc
  obtain ⟨fr, hfr, hdivr⟩ := fw_permutation_integral_flow_of_demand_box p dr B (N / 2)
    hcapacity hzr hbr hexp
  obtain ⟨fc, hfc, hdivc⟩ := fw_permutation_integral_flow_of_demand_box p dc B (N / 2)
    hcapacity hzc hbc hexp
  obtain ⟨b, hrow, hcol, hm, ha, hfixed, hpool, hinj⟩ :=
    hflows fr (fun e => abs_le.mp (hfr e)) fc (fun e => abs_le.mp (hfc e))
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj⟩
  · intro r
    simpa [hdivr r] using hrow r
  · intro c
    simpa [hdivc c] using hcol c

end
end Sude
