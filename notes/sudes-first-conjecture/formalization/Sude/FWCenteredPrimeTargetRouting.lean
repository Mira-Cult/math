import Sude.FWFlowDemandAdapter
import Sude.FWTargetDemandBudget

/-! Conditional same-reference routing of one centered odd-prime target vector.
The predicate `P` carries additional invariants of the supplied flow interface. -/
namespace Sude
noncomputable section

/-- One supplied odd-prime vector of the pool total can serve as both the row
and column target. The baseline estimates and flow interface must concern the
same reference square and the same line-scale center. The arbitrary predicate
retains additional invariants of the physical continuation. No target supply,
line estimate, expansion, or diagonal primality is inferred. -/
theorem fw_centered_prime_target_of_supplied_flows {n N : ℕ}
    (hn : Odd n) (p : Fin 3 → Equiv.Perm (Fin n))
    (b₀ : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (P : (Cell n ≃ Fin (n*n)) → Prop)
    (target : Fin n → ℕ) {y U D : ℝ}
    (hN : 3000 ≤ N)
    (hprime : ∀ i, Nat.Prime (target i))
    (hodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - y| ≤ D)
    (hrow : ∀ i, |(rowSum b₀ i : ℝ) - y| ≤ U)
    (hcol : ∀ i, |(columnSum b₀ i : ℝ) - y| ≤ U)
    (hbudget : U + D ≤ (518481 / 500000 : ℝ) * N)
    (hexp : ∀ S : Finset (Fin n),
      519 * min S.card (n - S.card) ≤
        500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
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
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧ P b) :
    ∃ b : Cell n ≃ Fin (n*n),
      (∀ i, rowSum b i = target i ∧ Nat.Prime (rowSum b i)) ∧
      (∀ i, columnSum b i = target i ∧ Nat.Prime (columnSum b i)) ∧
      mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
      (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) ∧ P b := by
  let B : ℕ := 519 * (N / 2) / 500
  have hcap : 500 * B ≤ 519 * (N / 2) := (fw_demand_box_rounding hN).1
  have hb := fw_reference_target_bounds_of_fw18 b₀ target target hN hrow hcol htarget htarget hbudget
  let dr : Fin n → ℤ := fun i => halfLineDemand (target i) (rowSum b₀ i)
  let dc : Fin n → ℤ := fun i => halfLineDemand (target i) (columnSum b₀ i)
  have hrowSum : (∑ i, target i) = ∑ i, rowSum b₀ i := by rw [htotal, Lucas.sum_rowSums]
  have hcolSum : (∑ i, target i) = ∑ i, columnSum b₀ i := by rw [htotal, Lucas.sum_columnSums]
  have ⟨hzr, her⟩ := halfLineDemand_system target (rowSum b₀) hodd (rowSum_odd hn b₀) hrowSum
  have ⟨hzc, hec⟩ := halfLineDemand_system target (columnSum b₀) hodd (columnSum_odd hn b₀) hcolSum
  have hdr : ∀ i, |dr i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (hodd i) (rowSum_odd hn b₀ i) (hb.1 i)
  have hdc : ∀ i, |dc i| ≤ (B : ℤ) := fun i =>
    halfLineDemand_bound _ _ B (hodd i) (columnSum_odd hn b₀ i) (hb.2 i)
  obtain ⟨fr, hfr, hdivr⟩ := fw_permutation_integral_flow_of_demand_box p dr B (N / 2)
    hcap hzr hdr hexp
  obtain ⟨fc, hfc, hdivc⟩ := fw_permutation_integral_flow_of_demand_box p dc B (N / 2)
    hcap hzc hdc hexp
  obtain ⟨b, hr, hc, hm, ha, hfixed, hpool, hinj, hp⟩ :=
    hflows fr (fun e => abs_le.mp (hfr e)) fc (fun e => abs_le.mp (hfc e))
  refine ⟨b, ?_, ?_, hm, ha, hfixed, hpool, hinj, hp⟩
  · intro i
    have heq : rowSum b i = target i := by
      have h₁ := hr i
      have h₂ := her i
      rw [hdivr i] at h₁
      change (rowSum b i : ℤ) - rowSum b₀ i =
        2 * halfLineDemand (target i) (rowSum b₀ i) at h₁
      exact_mod_cast (show (rowSum b i : ℤ) = target i by omega)
    exact ⟨heq, heq.symm ▸ hprime i⟩
  · intro i
    have heq : columnSum b i = target i := by
      have h₁ := hc i
      have h₂ := hec i
      rw [hdivc i] at h₁
      change (columnSum b i : ℤ) - columnSum b₀ i =
        2 * halfLineDemand (target i) (columnSum b₀ i) at h₁
      exact_mod_cast (show (columnSum b i : ℤ) = target i by omega)
    exact ⟨heq, heq.symm ▸ hprime i⟩

end
end Sude
