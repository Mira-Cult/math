import Sude.T75TwoUnitResidues
import Mathlib.Data.Real.Basic

/-!
# T75.5 Wheel Potential and Favorable-Gap Seed Existence

Proves via an explicit 8-unit potential on `W = 30` that any finite set `S` of primes `> 5`
satisfying `9 + (S.max' - S.min') < 35 * (S.card - 1)` (in particular any set of primes `> 5`
in an interval `[a, b]` with `b - a + 44 < 35 * (S.card : ℝ)`) contains a prime pair
`(r0, r0 + h)` with `r0 ∈ S`, `r0 + h ∈ S`, and `h ∈ t75FavorableGaps`.
-/

namespace Sude

noncomputable section

set_option maxHeartbeats 2000000

/-- Potential on the 8 units modulo 30 (`{1, 7, 11, 13, 17, 19, 23, 29}`), shifted to `[0, 9]`. -/
def wheel30Potential (r : ℕ) : ℕ :=
  if r = 1 then 3
  else if r = 7 then 9
  else if r = 11 then 8
  else if r = 13 then 5
  else if r = 17 then 4
  else if r = 19 then 1
  else if r = 23 then 0
  else if r = 29 then 6
  else 0

theorem wheel30Potential_le_nine (r : ℕ) : wheel30Potential r ≤ 9 := by
  dsimp [wheel30Potential]
  split_ifs <;> omega

private theorem mod_thirty_units :
    ∀ r ∈ Finset.range 30, r % 2 = 1 → r % 3 ≠ 0 → r % 5 ≠ 0 →
      r = 1 ∨ r = 7 ∨ r = 11 ∨ r = 13 ∨ r = 17 ∨ r = 19 ∨ r = 23 ∨ r = 29 := by
  decide

/-- Every prime greater than 5 has residue modulo 30 in `{1, 7, 11, 13, 17, 19, 23, 29}`. -/
theorem prime_gt_five_mod_thirty {p : ℕ} (hp5 : 5 < p) (hp : Nat.Prime p) :
    p % 30 = 1 ∨ p % 30 = 7 ∨ p % 30 = 11 ∨ p % 30 = 13 ∨
    p % 30 = 17 ∨ p % 30 = 19 ∨ p % 30 = 23 ∨ p % 30 = 29 := by
  have hp2 : p % 2 = 1 := by
    by_contra h2
    have hdvd : 2 ∣ p := Nat.dvd_of_mod_eq_zero (by omega)
    rcases hp.eq_one_or_self_of_dvd 2 hdvd with h | h <;> omega
  have hp3 : p % 3 ≠ 0 := by
    intro h3
    have hdvd : 3 ∣ p := Nat.dvd_of_mod_eq_zero h3
    rcases hp.eq_one_or_self_of_dvd 3 hdvd with h | h <;> omega
  have hp5_mod : p % 5 ≠ 0 := by
    intro h5
    have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h5
    rcases hp.eq_one_or_self_of_dvd 5 hdvd with h | h <;> omega
  have hm2 : (p % 30) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by decide)]
    exact hp2
  have hm3 : (p % 30) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by decide)]
    exact hp3
  have hm5 : (p % 30) % 5 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by decide)]
    exact hp5_mod
  exact mod_thirty_units (p % 30) (Finset.mem_range.mpr (Nat.mod_lt p (by decide))) hm2 hm3 hm5

/-- Single-step potential inequality on `W = 30`: if `5 < p < q` are primes and
`q - p ∉ t75FavorableGaps`, then `wheel30Potential (q % 30) + 35 ≤ wheel30Potential (p % 30) + (q - p)`. -/
theorem wheel30_step_bound {p q : ℕ}
    (hp5 : 5 < p) (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p < q)
    (hbad : q - p ∉ t75FavorableGaps) :
    wheel30Potential (q % 30) + 35 ≤ wheel30Potential (p % 30) + (q - p) := by
  have hp_mod := prime_gt_five_mod_thirty hp5 hp
  have hq_mod := prime_gt_five_mod_thirty (by omega) hq
  simp only [t75FavorableGaps, Finset.mem_insert, Finset.mem_singleton, not_or] at hbad
  rcases hp_mod with hp_r | hp_r | hp_r | hp_r | hp_r | hp_r | hp_r | hp_r <;>
    rcases hq_mod with hq_r | hq_r | hq_r | hq_r | hq_r | hq_r | hq_r | hq_r <;>
    { rw [hp_r, hq_r]; dsimp [wheel30Potential]; omega }

/-- Telescoped potential inequality across any finite set `S` of `k + 1` primes `> 5`
containing no favorable-gap pair. -/
theorem wheel30_finset_spread_bound :
    ∀ (k : ℕ) (S : Finset ℕ) (hne : S.Nonempty),
      S.card = k + 1 →
      (∀ p ∈ S, 5 < p ∧ Nat.Prime p) →
      (∀ p ∈ S, ∀ h ∈ t75FavorableGaps, p + h ∉ S) →
      wheel30Potential (S.max' hne % 30) + 35 * k ≤
        wheel30Potential (S.min' hne % 30) + (S.max' hne - S.min' hne) := by
  intro k
  induction k with
  | zero =>
    intro S hne hcard _hprime _hno
    have hmin_mem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hmax_mem : S.max' hne ∈ S := Finset.max'_mem S hne
    have hle1 : S.card ≤ 1 := by omega
    have heq : S.min' hne = S.max' hne :=
      Finset.card_le_one.mp hle1 (S.min' hne) hmin_mem (S.max' hne) hmax_mem
    rw [heq]
    omega
  | succ k ih =>
    intro S hne hcard hprime hno
    let p0 := S.min' hne
    have hp0_mem : p0 ∈ S := Finset.min'_mem S hne
    let S' := S.erase p0
    have hS'_card : S'.card = k + 1 := by
      rw [Finset.card_erase_of_mem hp0_mem]
      omega
    have hS'_ne : S'.Nonempty := Finset.card_pos.mp (by omega)
    let p1 := S'.min' hS'_ne
    have hp1_mem' : p1 ∈ S' := Finset.min'_mem S' hS'_ne
    have hp1_ne : p1 ≠ p0 := (Finset.mem_erase.mp hp1_mem').1
    have hp1_mem : p1 ∈ S := (Finset.mem_erase.mp hp1_mem').2
    have hp0_le_p1 : p0 ≤ p1 := Finset.min'_le S p1 hp1_mem
    have hp0_lt_p1 : p0 < p1 := by omega
    have hmax_eq : S'.max' hS'_ne = S.max' hne := by
      have hm1_mem' : S'.max' hS'_ne ∈ S' := Finset.max'_mem S' hS'_ne
      have hm1_mem : S'.max' hS'_ne ∈ S := (Finset.mem_erase.mp hm1_mem').2
      have hle_a : S'.max' hS'_ne ≤ S.max' hne := Finset.le_max' S _ hm1_mem
      have hm2_mem : S.max' hne ∈ S := Finset.max'_mem S hne
      have hp1_le_max : p1 ≤ S.max' hne := Finset.le_max' S p1 hp1_mem
      have hm2_ne : S.max' hne ≠ p0 := by omega
      have hm2_mem' : S.max' hne ∈ S' := Finset.mem_erase.mpr ⟨hm2_ne, hm2_mem⟩
      have hle_b : S.max' hne ≤ S'.max' hS'_ne := Finset.le_max' S' _ hm2_mem'
      omega
    have hbad : p1 - p0 ∉ t75FavorableGaps := by
      intro hfav
      have hsum : p0 + (p1 - p0) = p1 := by omega
      have hnotin := hno p0 hp0_mem (p1 - p0) hfav
      rw [hsum] at hnotin
      exact hnotin hp1_mem
    have hstep := wheel30_step_bound (hprime p0 hp0_mem).1 (hprime p0 hp0_mem).2
      (hprime p1 hp1_mem).2 hp0_lt_p1 hbad
    have hS'_prime : ∀ p ∈ S', 5 < p ∧ Nat.Prime p := by
      intro p hp
      exact hprime p (Finset.mem_erase.mp hp).2
    have hS'_no : ∀ p ∈ S', ∀ h ∈ t75FavorableGaps, p + h ∉ S' := by
      intro p hp h hh hmem'
      exact hno p (Finset.mem_erase.mp hp).2 h hh (Finset.mem_erase.mp hmem').2
    have htail := ih S' hS'_ne hS'_card hS'_prime hS'_no
    rw [hmax_eq] at htail
    have hp1_le_max : p1 ≤ S.max' hne := Finset.le_max' S p1 hp1_mem
    change wheel30Potential (S.max' hne % 30) + 35 * (k + 1) ≤
      wheel30Potential (p0 % 30) + (S.max' hne - p0)
    change wheel30Potential (S.max' hne % 30) + 35 * k ≤
      wheel30Potential (p1 % 30) + (S.max' hne - p1) at htail
    omega

/-- Any finite set `S` of primes `> 5` inside `[a, b]` with `b - a + 44 < 35 * (S.card : ℝ)`
contains a prime pair `(r0, r0 + h)` with `r0 ∈ S`, `r0 + h ∈ S`, and `h ∈ t75FavorableGaps`. -/
theorem exists_favorable_gap_pair_in_finset (S : Finset ℕ) (a b : ℝ)
    (hprime : ∀ p ∈ S, 5 < p ∧ Nat.Prime p)
    (hint : ∀ p ∈ S, a ≤ (p : ℝ) ∧ (p : ℝ) ≤ b)
    (hba : a ≤ b)
    (hdense : b - a + 44 < 35 * (S.card : ℝ)) :
    ∃ r0 ∈ S, ∃ h ∈ t75FavorableGaps, r0 + h ∈ S := by
  by_contra hno
  push Not at hno
  have hcard_pos : 1 ≤ S.card := by
    by_contra h0
    have hScard0 : S.card = 0 := by omega
    rw [hScard0] at hdense
    simp at hdense
    linarith
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  let k : ℕ := S.card - 1
  have hk : S.card = k + 1 := by omega
  have hbound := wheel30_finset_spread_bound k S hne hk hprime hno
  have hpot_le : wheel30Potential (S.min' hne % 30) ≤ 9 := wheel30Potential_le_nine _
  have hnat_bound : 35 * k ≤ 9 + (S.max' hne - S.min' hne) := by omega
  have hmin_mem : S.min' hne ∈ S := Finset.min'_mem S hne
  have hmax_mem : S.max' hne ∈ S := Finset.max'_mem S hne
  have hmin_le_max : S.min' hne ≤ S.max' hne := Finset.min'_le S _ hmax_mem
  have hdiff_real : ((S.max' hne - S.min' hne : ℕ) : ℝ) ≤ b - a := by
    rw [Nat.cast_sub hmin_le_max]
    linarith [(hint _ hmin_mem).1, (hint _ hmax_mem).2]
  have hreal_bound : 35 * (k : ℝ) ≤ 9 + (b - a) := by
    have hcast : ((35 * k : ℕ) : ℝ) ≤ ((9 + (S.max' hne - S.min' hne) : ℕ) : ℝ) := by
      exact_mod_cast hnat_bound
    push_cast at hcast
    linarith
  have hk_real : (S.card : ℝ) = (k : ℝ) + 1 := by exact_mod_cast hk
  linarith

end

end Sude
