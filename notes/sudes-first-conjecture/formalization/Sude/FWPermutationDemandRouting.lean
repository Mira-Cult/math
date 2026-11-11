import Sude.SimpleResidualPath

/-! Route supplied zero-total demands on the actual FW labelled permutation
edges. The graph expansion and the demand box are explicit hypotheses. -/
namespace Sude
noncomputable section

/-- The FW `519/500` cut bound and an exact capacity comparison give an
integer flow with the supplied bounded zero-total demand as its divergence.
Parallel labelled edge occurrences are counted separately. -/
theorem fw_permutation_integral_flow_of_demand_box {n : ℕ}
    (p : Fin 3 → Equiv.Perm (Fin n)) (d : Fin n → ℤ) (B C : ℕ)
    (hcapacity : 500 * B ≤ 519 * C)
    (hzero : ∑ v, d v = 0) (hbound : ∀ v, |d v| ≤ (B : ℤ))
    (hexp : ∀ S : Finset (Fin n),
      519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card) :
    ∃ flow : Fin 3 × Fin n → ℤ,
      (∀ e, |flow e| ≤ (C : ℤ)) ∧
      ∀ v, (∑ e : Fin 3 × Fin n,
        edgeTransfer (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) flow e v) = d v := by
  let source : Fin 3 × Fin n → Fin n := fun e => e.2
  let target : Fin 3 × Fin n → Fin n := fun e => p e.1 e.2
  apply integer_flow_of_cut_inequalities source target d C hzero
  intro S
  have hnum := scaled_cut_capacity 500 519 B C
    (min S.card (n - S.card)) (cutEdges source target S).card (by decide) hcapacity (hexp S)
  exact (zero_total_cut_demand d B hzero hbound S).trans (by exact_mod_cast hnum)

end
end Sude
