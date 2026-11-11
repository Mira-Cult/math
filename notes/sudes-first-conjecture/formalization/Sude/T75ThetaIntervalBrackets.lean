import Sude.APInterval

/-!
Conditional bridge from positive theta increments to free T75 prime brackets.
No analytic theta estimate, controlled prime pair, or seed chain is proved here.
In particular, positivity for modulus 42 is not derived from modulus 21.
-/

namespace Sude
noncomputable section

/-- A positive theta increment gives an actual prime in the half-open interval. -/
theorem t75_prime_of_theta_increment_pos (b c : ℝ) (q : ℕ) (a : ℤ)
    (hb : 0 ≤ b) (hbc : b ≤ c)
    (hpos : 0 < thetaAP c q a - thetaAP b q a) :
    ∃ p : ℕ, Nat.Prime p ∧ b < (p : ℝ) ∧ (p : ℝ) ≤ c ∧
      (p : ℤ) % (q : ℤ) = a % (q : ℤ) := by
  classical
  have hne : (apInterval b c q a).Nonempty := by
    by_contra h
    have hempty : apInterval b c q a = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    rw [thetaAP_sub_eq_interval_sum b c q a hbc, hempty] at hpos
    simp at hpos
  obtain ⟨p, hp⟩ := hne
  exact ⟨p, (mem_apInterval_iff b c q a hb (le_trans hb hbc) p).mp hp⟩

/-- Positive theta increments on both halves give the explicit reduced-class
    prime brackets consumed by `t75_free_prime_brackets_from_unit_supply`. -/
theorem t75_unit_brackets_of_theta_increments (h : ℕ) (y D : ℝ)
    (hD : 0 ≤ D) (hleft : 0 ≤ y-D)
    (hpos : ∀ r : ℕ, r < h → Nat.Coprime r h →
      0 < thetaAP y h (r : ℤ) - thetaAP (y-D) h (r : ℤ) ∧
      0 < thetaAP (y+D) h (r : ℤ) - thetaAP y h (r : ℤ)) :
    ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D := by
  intro r hr hc
  obtain ⟨hlo, hhi⟩ := hpos r hr hc
  have hy : 0 ≤ y := by linarith
  obtain ⟨p, hp, hpL, hpU, hpmod⟩ :=
    t75_prime_of_theta_increment_pos (y-D) y h r hleft (by linarith) hlo
  obtain ⟨q, hq, hqL, hqU, hqmod⟩ :=
    t75_prime_of_theta_increment_pos y (y+D) h r hy (by linarith) hhi
  have hpmod' : p % h = r := by
    have heq : p % h = r % h := by exact_mod_cast hpmod
    simpa [Nat.mod_eq_of_lt hr] using heq
  have hqmod' : q % h = r := by
    have heq : q % h = r % h := by exact_mod_cast hqmod
    simpa [Nat.mod_eq_of_lt hr] using heq
  exact ⟨p, q, hp, hq, hpmod', hqmod', le_of_lt hpL, hpU, le_of_lt hqL, hqU⟩

end
end Sude
