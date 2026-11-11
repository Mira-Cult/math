import Sude.BMORFinite
import Sude.PrefixCount
import Sude.UniformSqrtLog
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
A narrow, pointwise formulation of the q=4 prime-count computation in
Bennett, Martin, O'Bryant, and Rechnitzer, Appendix A.3, (A.2)--(A.3)
and Table 4 (printed pp. 513--516). The table's rounded-up q=4 value
2.253192 is taken as an explicit hypothesis, including its finite
computation. This module does not import the problematic printed maximum
with lower endpoint 1 in Theorem 1.9; every evaluation here is at least 2.
-/

namespace Sude
noncomputable section

/-- BMOR's normalization (1.4): the integral begins at 2. -/
def liFromTwo (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, (Real.log t)⁻¹

/-- The real-valued count of primes up to x in one residue class. -/
def apPrimeCount (x : ℝ) (q : ℕ) (a : ℤ) : ℝ :=
  ((apPrefix x q a).card : ℝ)

/-- The real-valued count of odd primes up to x. -/
def oddPrimeCountReal (x : ℝ) : ℝ := ((oddPrimePrefix ⌊x⌋₊).card : ℝ)

/-- At an integer endpoint this is the existing odd-prime prefix count. -/
@[simp] theorem oddPrimeCountReal_natCast (k : ℕ) :
    oddPrimeCountReal (k : ℝ) = ((oddPrimePrefix k).card : ℝ) := by
  simp [oddPrimeCountReal]

/-- External finite-computation hypothesis: the q=4 pointwise specialization
of BMOR Appendix A.3 and its Table 4, with printed rounded-up coefficient.
This is a proposition to be supplied by callers, not an axiom or a proof. -/
def BMORFinitePiFour : Prop := ∀ (a : ℤ) (x : ℝ),
  (a = 1 ∨ a = 3) → 2 ≤ x → x ≤ (4 * 10 ^ 13 : ℝ) →
  |apPrimeCount x 4 a - liFromTwo x / 2| ≤
    (281649 / 125000 : ℝ) * (Real.sqrt x / Real.log x)

/-- The odd-prime prefix is exactly the disjoint union of the two odd classes
modulo four, including the closed real endpoint. -/
theorem oddPrimePrefix_eq_ap_four_union (x : ℝ) :
    oddPrimePrefix ⌊x⌋₊ = apPrefix x 4 1 ∪ apPrefix x 4 3 := by
  classical
  ext p
  have hm41 : ((p : ℤ) % 4 = 1) ↔ p % 4 = 1 := by exact_mod_cast Iff.rfl
  have hm43 : ((p : ℤ) % 4 = 3) ↔ p % 4 = 3 := by exact_mod_cast Iff.rfl
  simp only [oddPrimePrefix, apPrefix, Finset.mem_filter, Finset.mem_range,
    Finset.mem_union, Nat.lt_succ_iff]
  norm_num
  rw [hm41, hm43]
  constructor
  · rintro ⟨hbound, hp, hne⟩
    have hodd := hp.eq_two_or_odd.resolve_left hne
    have hsplit : p % 4 = 1 ∨ p % 4 = 3 := by omega
    rcases hsplit with h1 | h3
    · exact Or.inl ⟨hbound, hp, h1⟩
    · exact Or.inr ⟨hbound, hp, h3⟩
  · rintro (⟨hbound, hp, h1⟩ | ⟨hbound, hp, h3⟩)
    · exact ⟨hbound, hp, by omega⟩
    · exact ⟨hbound, hp, by omega⟩

/-- The two odd residue classes have no common prime. -/
theorem ap_four_classes_disjoint (x : ℝ) :
    Disjoint (apPrefix x 4 1) (apPrefix x 4 3) := by
  classical
  apply Finset.disjoint_left.mpr
  intro p hp1 hp3
  simp only [apPrefix, Finset.mem_filter, Finset.mem_range] at hp1 hp3
  norm_num at hp1 hp3
  omega

/-- Exact two-class count identity. -/
theorem oddPrimeCountReal_eq_ap_four (x : ℝ) :
    oddPrimeCountReal x = apPrimeCount x 4 1 + apPrimeCount x 4 3 := by
  unfold oddPrimeCountReal apPrimeCount
  rw [oddPrimePrefix_eq_ap_four_union, Finset.card_union_of_disjoint (ap_four_classes_disjoint x)]
  norm_cast

/-- The two-class pointwise estimate follows by the triangle inequality. -/
theorem bmor_odd_count_four_pointwise (h : BMORFinitePiFour) {x : ℝ}
    (hx : 2 ≤ x) (hcap : x ≤ (4 * 10 ^ 13 : ℝ)) :
    |oddPrimeCountReal x - liFromTwo x| ≤
      (281649 / 62500 : ℝ) * (Real.sqrt x / Real.log x) := by
  have h1 := h 1 x (Or.inl rfl) hx hcap
  have h3 := h 3 x (Or.inr rfl) hx hcap
  have heq : oddPrimeCountReal x - liFromTwo x =
      (apPrimeCount x 4 1 - liFromTwo x / 2) +
      (apPrimeCount x 4 3 - liFromTwo x / 2) := by
    rw [oddPrimeCountReal_eq_ap_four]
    ring
  rw [heq]
  calc
    _ ≤ |apPrimeCount x 4 1 - liFromTwo x / 2| +
        |apPrimeCount x 4 3 - liFromTwo x / 2| := abs_add_le _ _
    _ ≤ _ := by linarith

/-- Uniform endpoint form for the supplied pointwise finite computation. -/
theorem bmor_odd_count_four_uniform (h : BMORFinitePiFour) {X : ℝ}
    (hlog : 24 ≤ Real.log X) (hcap : X ≤ (4 * 10 ^ 13 : ℝ)) :
    ∀ x, 2 ≤ x → x ≤ X →
      |oddPrimeCountReal x - liFromTwo x| ≤
        (281649 / 62500 : ℝ) * (Real.sqrt X / Real.log X) := by
  apply uniform_sqrt_log_error (by norm_num) hlog
  intro x hx hxX
  exact bmor_odd_count_four_pointwise h hx (le_trans hxX hcap)

end
end Sude
