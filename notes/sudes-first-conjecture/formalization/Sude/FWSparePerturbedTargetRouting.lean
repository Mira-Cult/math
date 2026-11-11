import Sude.FWCenteredPrimeTargetRouting
import Sude.FWFirstBandSpareRoutingBudget

/-! Route a supplied nominal target vector after a separately bounded line
perturbation. The modified square and its flow continuation are supplied;
this does not construct them, prove target supply or repair diagonals. -/

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- A supplied post-perturbation square can use the nominal first-band target
budget when every row and column has changed by at most `X`. The supplied flow
continuation must concern exactly that modified square. -/
theorem fw_spare_perturbed_nominal_target_routing
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (p : Fin 3 → Equiv.Perm (Fin n))
    (cy modified : Cell n ≃ Fin (n*n)) (reserved : Finset (Cell n))
    (P : (Cell n ≃ Fin (n*n)) → Prop) (target : Fin n → ℕ)
    (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (hrow : ∀ r, |(rowSum cy r : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n)
    (hcol : ∀ c, |(columnSum cy c : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤ fwFrozenCYLineRadius n)
    (hrowChange : ∀ r, |(rowSum modified r : ℝ) - rowSum cy r| ≤ (poolMaximum n : ℝ))
    (hcolChange : ∀ c, |(columnSum modified c : ℝ) - columnSum cy c| ≤ (poolMaximum n : ℝ))
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (hflows : ∀ fr : Fin 3 × Fin n → ℤ,
      (∀ e, -(((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ) ≤ fr e ∧
        fr e ≤ (((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ)) →
      ∀ fc : Fin 3 × Fin n → ℤ,
      (∀ e, -(((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ) ≤ fc e ∧
        fc e ≤ (((((n/450)*poolMaximum n) / 2 : ℕ)) : ℤ)) →
      ∃ out : Cell n ≃ Fin (n*n),
        (∀ r, (rowSum out r : ℤ) - (rowSum modified r : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fr e r) ∧
        (∀ c, (columnSum out c : ℤ) - (columnSum modified c : ℤ) =
          2 * ∑ e : Fin 3 × Fin n, edgeTransfer (fun x => x.2) (fun x => p x.1 x.2) fc e c) ∧
        mainSum out = mainSum modified ∧ antiSum out = antiSum modified ∧
        (∀ z ∈ reserved, entry out z = entry modified z) ∧
        Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧ P out) :
    ∃ out : Cell n ≃ Fin (n*n),
      (∀ i, rowSum out i = target i ∧ Nat.Prime (rowSum out i)) ∧
      (∀ i, columnSum out i = target i ∧ Nat.Prime (columnSum out i)) ∧
      mainSum out = mainSum modified ∧ antiSum out = antiSum modified ∧
      (∀ z ∈ reserved, entry out z = entry modified z) ∧
      Set.range (entry out) = pool n ∧ Function.Injective (entry out) ∧ P out := by
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let X : ℝ := poolMaximum n
  have hrow' : ∀ r, |(rowSum modified r : ℝ) - y| ≤ fwFrozenCYLineRadius n + X := by
    intro r
    calc
      _ = |((rowSum modified r : ℝ) - rowSum cy r) + ((rowSum cy r : ℝ) - y)| := by congr 1; ring
      _ ≤ |(rowSum modified r : ℝ) - rowSum cy r| + |(rowSum cy r : ℝ) - y| := abs_add_le _ _
      _ ≤ _ := by have h₁ := hrowChange r; have h₂ := hrow r; dsimp [X, y] at *; linarith
  have hcol' : ∀ c, |(columnSum modified c : ℝ) - y| ≤ fwFrozenCYLineRadius n + X := by
    intro c
    calc
      _ = |((columnSum modified c : ℝ) - columnSum cy c) + ((columnSum cy c : ℝ) - y)| := by congr 1; ring
      _ ≤ |(columnSum modified c : ℝ) - columnSum cy c| + |(columnSum cy c : ℝ) - y| := abs_add_le _ _
      _ ≤ _ := by have h₁ := hcolChange c; have h₂ := hcol c; dsimp [X, y] at *; linarith
  have hbudget := le_of_lt (fw_first_band_nominal_routing_budget_with_spare_perturbation bmor lower upper hnlo hnhi)
  exact fw_centered_prime_target_of_supplied_flows
    (N := (n/450)*poolMaximum n) hodd p modified reserved P target
    (fw_first_band_demand_rounding_threshold lower hnlo) hprime htodd htotal htarget
    hrow' hcol' (by simpa [X, y] using hbudget) hexp hflows

end
end Sude
