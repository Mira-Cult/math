import Sude.FWFreshT75ReferenceGains

/-! Repair both packed diagonals to one supplied reachable prime target. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Repair to the supplied indexed odd prime when it lies in both exact
physical reachable intervals. No existence of such an index is inferred. -/
theorem packed_prime_diagonal_repair_reachable_target {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : Odd n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Rm Ra : ℕ) (a b : Cell n ≃ Fin (n*n)) (keep : Finset (Cell n))
    (hm : CompleteEvenGrid (active.filter fun i => choice i = true) gap Rm)
    (ha : CompleteEvenGrid (active.filter fun i => choice i = false) gap Ra)
    (hgaps : ∀ i ∈ active,
      entry a (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry a (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry a (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry a (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i)
    (hprotect : ∀ c ∈ keep, ∀ i ∈ active,
      c ∉ rectangleCells (RectanglePacking.firstRow hs i) (RectanglePacking.secondRow hs i)
        (RectanglePacking.firstColumn hs choice i) (RectanglePacking.secondColumn hs choice i))
    (hagree : ∀ z ∈ packedLabelSupport hs choice active, entry b z = entry a z)
    (hmain : mainSum b = mainSum a) (hanti : antiSum b = antiSum a)
    (hrows : ∀ r, Nat.Prime (rowSum b r)) (hcols : ∀ c, Nat.Prime (columnSum b c))
    (f : Fin n → ℕ) (i : Fin n) (hprime : Nat.Prime (f i)) (hodd : Odd (f i))
    (hreachm : 0 ≤ ((f i : ℤ) - mainSum a) ∧
      (f i : ℤ) - mainSum a ≤ 2 * evenGridCenter Rm)
    (hreacha : 0 ≤ ((f i : ℤ) - antiSum a) ∧
      (f i : ℤ) - antiSum a ≤ 2 * evenGridCenter Ra) :
    ∃ before : Finset (Fin L), before ⊆ active ∧
      let reference := packedTradeSequence hs choice a before.toList
      (mainSum reference : ℤ) - (mainSum a : ℤ) = evenGridCenter Rm ∧
      (antiSum reference : ℤ) - (antiSum a : ℤ) = evenGridCenter Ra ∧
      ∃ result : Cell n ≃ Fin (n*n),
        (∀ r, rowSum result r = rowSum b r) ∧
        (∀ c, columnSum result c = columnSum b c) ∧
        mainSum result = f i ∧ antiSum result = f i ∧ Valid result ∧
        Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
        entry result (centerIndex n (by obtain ⟨k, hk⟩ := hn; omega), centerIndex n (by obtain ⟨k, hk⟩ := hn; omega)) =
          entry b (centerIndex n (by obtain ⟨k, hk⟩ := hn; omega), centerIndex n (by obtain ⟨k, hk⟩ := hn; omega)) ∧
        (∀ z ∈ keep, entry result z = entry b z) := by
  classical
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  obtain ⟨before, hbefore, hmgain, hagain, hcontroller⟩ :=
    packed_centered_diagonal_adapter_with_reference_gains hs hL hnpos choice gap active Rm Ra a keep hm ha hgaps hprotect
  let reference := packedTradeSequence hs choice a before.toList
  have hmEven : (2 : ℤ) ∣ ((f i : ℤ) - mainSum reference) := by
    exact ⟨halfLineDemand (f i) (mainSum reference),
      (halfLineDemand_exact _ _ hodd (mainSum_odd_of_odd_order hn reference)).symm⟩
  have haEven : (2 : ℤ) ∣ ((f i : ℤ) - antiSum reference) := by
    exact ⟨halfLineDemand (f i) (antiSum reference),
      (halfLineDemand_exact _ _ hodd (antiSum_odd_of_odd_order hn reference)).symm⟩
  have hmbounds : -(evenGridCenter Rm : ℤ) ≤ ((f i : ℤ) - mainSum reference) ∧
      (f i : ℤ) - mainSum reference ≤ evenGridCenter Rm := by
    change (mainSum reference : ℤ) - (mainSum a : ℤ) = evenGridCenter Rm at hmgain
    omega
  have habounds : -(evenGridCenter Ra : ℤ) ≤ ((f i : ℤ) - antiSum reference) ∧
      (f i : ℤ) - antiSum reference ≤ evenGridCenter Ra := by
    change (antiSum reference : ℤ) - (antiSum a : ℤ) = evenGridCenter Ra at hagain
    omega
  obtain ⟨result, hr, hc, hmd, had, hpool, hinj, hcenter, hkeep⟩ :=
    hcontroller b hagree hmain hanti ((f i : ℤ) - mainSum reference) ((f i : ℤ) - antiSum reference)
      hmEven haEven hmbounds.1 hmbounds.2 habounds.1 habounds.2
  change (mainSum result : ℤ) - (mainSum reference : ℤ) = (f i : ℤ) - mainSum reference at hmd
  change (antiSum result : ℤ) - (antiSum reference : ℤ) = (f i : ℤ) - antiSum reference at had
  have hmq : mainSum result = f i := by exact_mod_cast (by omega : (mainSum result : ℤ) = f i)
  have haq : antiSum result = f i := by exact_mod_cast (by omega : (antiSum result : ℤ) = f i)
  refine ⟨before, hbefore, hmgain, hagain, result, hr, hc, hmq, haq, ?_, hpool, hinj, hcenter, hkeep⟩
  exact ⟨fun r => by rw [hr r]; exact hrows r,
    fun c => by rw [hc c]; exact hcols c,
    by rw [hmq]; exact hprime, by rw [haq]; exact hprime⟩
end
end Sude
