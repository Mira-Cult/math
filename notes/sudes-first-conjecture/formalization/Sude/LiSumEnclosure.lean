import Sude.LiIntegralBridge

open scoped BigOperators Interval
open MeasureTheory Set

namespace Sude

/-- Unit left and right Riemann sums enclose the interval integral of an
increasing integrable function. -/
theorem intervalIntegral_monotoneOn_nat_sum_enclosure (f : ℝ → ℝ) {m n : ℕ}
    (hmn : m ≤ n) (hmono : MonotoneOn f (Set.Icc (m : ℝ) n))
    (hint : ∀ k ∈ Finset.Ico m n,
      IntervalIntegrable f volume (k : ℝ) (k + 1 : ℕ)) :
    (∑ k ∈ Finset.Ico m n, f (k : ℝ)) ≤ ∫ t in (m : ℝ)..(n : ℝ), f t := by
  have hparts : (∑ k ∈ Finset.Ico m n, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t) =
      ∫ t in (m : ℝ)..(n : ℝ), f t := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k => (k : ℝ)) hmn
    intro k hk
    exact hint k (by simpa only [Finset.mem_Ico, Set.mem_Ico] using hk)
  rw [← hparts]
  apply Finset.sum_le_sum
  intro k hk
  have hkn := Finset.mem_Ico.mp hk
  have hkI : (k : ℝ) ∈ Set.Icc (m : ℝ) (n : ℝ) := by
    constructor
    · exact_mod_cast (by omega : m ≤ k)
    · exact_mod_cast (by omega : k ≤ n)
  have hk1I : ((k + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (n : ℝ) := by
    constructor
    · exact_mod_cast (by omega : m ≤ k + 1)
    · exact_mod_cast (by omega : k + 1 ≤ n)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
  have hp : (∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f (k : ℝ)) ≤
      ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t := by
    apply intervalIntegral.integral_mono_on hkle intervalIntegrable_const (hint k hk)
    intro x hx
    apply hmono hkI
    · exact ⟨le_trans hkI.1 hx.1, le_trans hx.2 hk1I.2⟩
    · exact hx.1
  simpa using hp

/-- The right unit Riemann sum is an upper bound. -/
theorem intervalIntegral_monotoneOn_nat_sum_upper (f : ℝ → ℝ) {m n : ℕ}
    (hmn : m ≤ n) (hmono : MonotoneOn f (Set.Icc (m : ℝ) n))
    (hint : ∀ k ∈ Finset.Ico m n,
      IntervalIntegrable f volume (k : ℝ) (k + 1 : ℕ)) :
    (∫ t in (m : ℝ)..(n : ℝ), f t) ≤
      ∑ k ∈ Finset.Ico m n, f ((k + 1 : ℕ) : ℝ) := by
  have hparts : (∑ k ∈ Finset.Ico m n, ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t) =
      ∫ t in (m : ℝ)..(n : ℝ), f t := by
    apply intervalIntegral.sum_integral_adjacent_intervals_Ico (a := fun k => (k : ℝ)) hmn
    intro k hk
    exact hint k (by simpa only [Finset.mem_Ico, Set.mem_Ico] using hk)
  rw [← hparts]
  apply Finset.sum_le_sum
  intro k hk
  have hkn := Finset.mem_Ico.mp hk
  have hkI : (k : ℝ) ∈ Set.Icc (m : ℝ) (n : ℝ) := by
    constructor
    · exact_mod_cast (by omega : m ≤ k)
    · exact_mod_cast (by omega : k ≤ n)
  have hk1I : ((k + 1 : ℕ) : ℝ) ∈ Set.Icc (m : ℝ) (n : ℝ) := by
    constructor
    · exact_mod_cast (by omega : m ≤ k + 1)
    · exact_mod_cast (by omega : k + 1 ≤ n)
  have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
  have hp : (∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f t) ≤
      ∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), f ((k + 1 : ℕ) : ℝ) := by
    apply intervalIntegral.integral_mono_on hkle (hint k hk) intervalIntegrable_const
    intro x hx
    apply hmono _ hk1I hx.2
    exact ⟨le_trans hkI.1 hx.1, le_trans hx.2 hk1I.2⟩
  simpa using hp

/-- The exact sum occurring in the pool-mean bridge is bounded by adjacent
left/right sums around the logarithmic-integral integral. -/
theorem liFromTwo_nat_sum_enclosure {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 n, liFromTwo (k : ℝ)) ≤
        (∫ t in (2 : ℝ)..(n : ℝ), liFromTwo t) ∧
    (∫ t in (2 : ℝ)..(n : ℝ), liFromTwo t) ≤
        ∑ k ∈ Finset.Ico 2 n, liFromTwo ((k + 1 : ℕ) : ℝ) := by
  have hm : MonotoneOn liFromTwo (Set.Icc (2 : ℝ) (n : ℝ)) := by
    intro a ha b hb hab
    exact liFromTwo_mono ha.1 hab
  have hi : ∀ k ∈ Finset.Ico 2 n,
      IntervalIntegrable liFromTwo volume (k : ℝ) (k + 1 : ℕ) := by
    intro k hk
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by
      exact_mod_cast (Finset.mem_Ico.mp hk).1
    have hkle : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ k
    have hk1 := hk2.trans hkle
    have hc : ContinuousOn liFromTwo (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
      apply (liFromTwo_continuousOn hk1).mono
      intro x hx
      exact ⟨hk2.trans hx.1, hx.2⟩
    exact hc.intervalIntegrable_of_Icc hkle
  exact ⟨intervalIntegral_monotoneOn_nat_sum_enclosure liFromTwo hn hm hi,
    intervalIntegral_monotoneOn_nat_sum_upper liFromTwo hn hm hi⟩

/-- The integral exceeds the left sum by at most its endpoint value. -/
theorem liFromTwo_nat_sum_endpoint_enclosure {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 n, liFromTwo (k : ℝ)) ≤
        (∫ t in (2 : ℝ)..(n : ℝ), liFromTwo t) ∧
    (∫ t in (2 : ℝ)..(n : ℝ), liFromTwo t) ≤
      (∑ k ∈ Finset.Ico 2 n, liFromTwo (k : ℝ)) + liFromTwo (n : ℝ) := by
  obtain ⟨hlo, hhi⟩ := liFromTwo_nat_sum_enclosure hn
  have hshift : (∑ k ∈ Finset.Ico 2 n, liFromTwo ((k + 1 : ℕ) : ℝ)) =
      ∑ k ∈ Finset.Ico 3 (n + 1), liFromTwo (k : ℝ) := by
    simpa using Finset.sum_Ico_add' (fun k : ℕ => liFromTwo (k : ℝ)) 2 n 1
  have hbot := Finset.sum_Ico_sub_bot (fun k : ℕ => liFromTwo (k : ℝ))
    (show 2 < n + 1 by omega)
  have htop := Finset.sum_Ico_succ_top hn (fun k : ℕ => liFromTwo (k : ℝ))
  have h2 : liFromTwo ((2 : ℕ) : ℝ) = 0 := by norm_num [liFromTwo]
  rw [htop] at hbot
  rw [hshift, ← hbot, h2, sub_zero] at hhi
  exact ⟨hlo, hhi⟩

/-- The finite sum is enclosed by the exact integral expression, with a
single endpoint term for the discretization error. -/
theorem liFromTwo_nat_sum_identity_enclosure {n : ℕ} (hn : 2 ≤ n) :
    (∑ k ∈ Finset.Ico 2 n, liFromTwo (k : ℝ)) ≤
        (n : ℝ) * liFromTwo (n : ℝ) - liFromTwo ((n : ℝ) ^ 2) + liFromTwo 4 ∧
    (n : ℝ) * liFromTwo (n : ℝ) - liFromTwo ((n : ℝ) ^ 2) + liFromTwo 4 ≤
      (∑ k ∈ Finset.Ico 2 n, liFromTwo (k : ℝ)) + liFromTwo (n : ℝ) := by
  have hr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := liFromTwo_nat_sum_endpoint_enclosure hn
  rw [liFromTwo_integral_identity hr] at h
  exact h

end Sude
