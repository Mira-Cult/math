import Sude.BTStageDepletion

/-! Source BT2--BT5 scalar implications, separate from prime supplies. -/
namespace Sude
noncomputable section

/-- The source's `c₀` coefficient is a lower bound for the exact bin
coefficient when the number of classes and the radius obey the stated
continuous bounds. -/
theorem bt_source_bin_coefficient (c X r R L B : ℝ)
    (hc : 0 ≤ c) (hX : 0 < X) (hr : 0 < r) (hR : 0 < R)
    (hL : 0 < L) (hB : 0 < B)
    (hradius : R ≤ X / L) (hclasses : B ≤ r * (c * X / R + 1)) :
    R / (2 * r * X * (c + 1 / L)) ≤ 1 / (2 * B) := by
  have hcL : 0 < c + 1 / L := add_pos_of_nonneg_of_pos hc (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hclasses hR.le
  have heq : r * (c * X / R + 1) * R = r * (c * X + R) := by
    field_simp
  rw [heq] at hmul
  have hright : r * (c * X + R) ≤ r * X * (c + 1 / L) := by
    have hid : X * (c + 1 / L) = c * X + X / L := by ring
    have hbase : c * X + R ≤ X * (c + 1 / L) := by rw [hid]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hbase hr.le]
  have hden₁ : 0 < 2 * r * X * (c + 1 / L) := by positivity
  have hden₂ : 0 < 2 * B := by positivity
  apply (div_le_div_iff₀ hden₁ hden₂).2
  nlinarith [hmul, hright]

/-- The surplus from `N ≥ M` and `ε = c₀-η` covers the source's
uniform `ε M²` pair budget. -/
theorem bt_source_pair_surplus (N M c₀ η : ℝ)
    (hM : 0 ≤ M) (hNM : M ≤ N) (hη : 0 ≤ η)
    (hε : 0 ≤ c₀ - η) :
    (c₀ - η) * M ^ 2 ≤ c₀ * N ^ 2 - η * M * N := by
  have hN : 0 ≤ N := le_trans hM hNM
  have hc₀ : 0 ≤ c₀ := by linarith
  have hp := mul_nonneg (show 0 ≤ N - M by linarith)
    (show 0 ≤ c₀ * N + (c₀ - η) * M by positivity)
  nlinarith

/-- The BT5 population budget implies the exact real-bin gate once the
bin coefficient and BT3 neighbour cancellation have been established. -/
theorem bt_source_pair_gate (N M c₀ η r X R g Q B : ℝ)
    (hM : 0 ≤ M) (hNM : M ≤ N) (hη : 0 ≤ η) (hε : 0 ≤ c₀ - η)
    (hr : 0 < r) (hX : 0 < X) (hR : 0 ≤ R) (hg : 0 < g)
    (hcoef : c₀ * R / (r * X) ≤ 1 / (2 * B))
    (hBT5 : 2 * Q * r * X ≤ (c₀ - η) * M ^ 2 * g) :
    2 * Q * R / g + N * (η * M * R / (r * X) - 1 / 2) ≤
      (N ^ 2 / B - N) / 2 := by
  have hsurplus := bt_source_pair_surplus N M c₀ η hM hNM hη hε
  have hcoefN := mul_le_mul_of_nonneg_left hcoef (sq_nonneg N)
  have hCS : c₀ * N ^ 2 * R / (r * X) ≤ N ^ 2 / (2 * B) := by
    have hl : c₀ * N ^ 2 * R / (r * X) = N ^ 2 * (c₀ * R / (r * X)) := by ring
    have hr' : N ^ 2 / (2 * B) = N ^ 2 * (1 / (2 * B)) := by ring
    rw [hl, hr']
    exact hcoefN
  have hBT5R := mul_le_mul_of_nonneg_right hBT5 hR
  have hbudget : 2 * Q * R / g ≤ (c₀ - η) * M ^ 2 * R / (r * X) := by
    apply (div_le_div_iff₀ hg (mul_pos hr hX)).2
    have hl : 2 * Q * R * (r * X) = (2 * Q * r * X) * R := by ring
    have hr' : (c₀ - η) * M ^ 2 * R * g = ((c₀ - η) * M ^ 2 * g) * R := by ring
    rw [hl, hr']
    exact hBT5R
  have hsurplusR := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hsurplus hR)
    (le_of_lt (mul_pos hr hX))
  have hcombined : 2 * Q * R / g ≤ (c₀ * N ^ 2 - η * M * N) * R / (r * X) :=
    hbudget.trans hsurplusR
  have hid : (c₀ * N ^ 2 - η * M * N) * R / (r * X) +
      N * (η * M * R / (r * X) - 1 / 2) = c₀ * N ^ 2 * R / (r * X) - N / 2 := by ring
  have hrhs : N ^ 2 / (2 * B) - N / 2 = (N ^ 2 / B - N) / 2 := by ring
  linarith

/-- BT5 with the source's `c₀` implies the exact real population gate,
under the source's bin-count and radius bounds. -/
theorem bt_source_gate_from_bins (N M c X r R L g Q B η : ℝ)
    (hM : 0 ≤ M) (hNM : M ≤ N) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g) (hB : 0 < B)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L) (hclasses : B ≤ r * (c * X / R + 1))
    (hBT5 : 2 * Q * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g) :
    2 * Q * R / g + N * (η * M * R / (r * X) - 1 / 2) ≤
      (N ^ 2 / B - N) / 2 := by
  have hcoef0 := bt_source_bin_coefficient c X r R L B hc hX hr hR hL hB hradius hclasses
  have hcL : 0 < c + 1 / L := add_pos_of_nonneg_of_pos hc (by positivity)
  have heq : (1 / (2 * (c + 1 / L))) * R / (r * X) =
      R / (2 * r * X * (c + 1 / L)) := by
    field_simp
  have hcoef : (1 / (2 * (c + 1 / L))) * R / (r * X) ≤ 1 / (2 * B) := by
    rw [heq]
    exact hcoef0
  exact bt_source_pair_gate N M (1 / (2 * (c + 1 / L))) η r X R g Q B
    hM hNM hη hε hr hX hR.le hg hcoef hBT5

/-- The exact natural number of possible spatial-bin/class labels is at
most the continuous bin count used in BT2. -/
theorem bt_bin_count_le_source (classes : Finset ℕ) (c X R r : ℝ)
    (hc : 0 ≤ c) (hX : 0 < X) (hR : 0 < R)
    (hclasses : (classes.card : ℝ) ≤ r) :
    (((⌊(c * X) / R⌋₊ + 1) * classes.card : ℕ) : ℝ) ≤ r * (c * X / R + 1) := by
  have hdiv : 0 ≤ c * X / R := div_nonneg (mul_nonneg hc hX.le) hR.le
  have hf := Nat.floor_le hdiv
  have hfactor : ((⌊(c * X) / R⌋₊ : ℕ) : ℝ) + 1 ≤ c * X / R + 1 := by linarith
  calc
    _ = (((⌊(c * X) / R⌋₊ : ℕ) : ℝ) + 1) * (classes.card : ℝ) := by push_cast; ring
    _ ≤ (c * X / R + 1) * (classes.card : ℝ) := mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ (c * X / R + 1) * r := mul_le_mul_of_nonneg_left hclasses (by positivity)
    _ = _ := by ring

/-- The source BT5 gate implies the exact finite-bin gate used by the
formal common-gap stage, including both natural floors and the BT3 radius. -/
theorem bt_source_implies_exact_bin_gate
    (unused classes : Finset ℕ) (c X r R L η M ell width : ℝ) (g Q : ℕ)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g) (hell : 0 < ell)
    (hclassespos : 0 < classes.card) (hclasses : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L)
    (hwidth : width = (ell * (Nat.totient g : ℝ) / (2 * g)) * g *
      (η * M * R / (r * X) - 1 / 2))
    (hBT5 : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g) :
    (((⌊R⌋₊ / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient g : ℝ) * ell)) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊(c * X) / R⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2 := by
  let B : ℕ := (⌊(c * X) / R⌋₊ + 1) * classes.card
  have hBpos : 0 < B := Nat.mul_pos (by omega) hclassespos
  have hBR : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hBupper : (B : ℝ) ≤ r * (c * X / R + 1) := bt_bin_count_le_source classes c X R r hc hX hR hclasses
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast (Nat.totient_pos.mpr hg)
  have hreal := bt_source_gate_from_bins (unused.card : ℝ) M c X r R L g Q B η
    hM hNM hc hX hr hR hL hgR hBR hη hε hradius hBupper hBT5
  have hfloor : ((⌊R⌋₊ / g : ℕ) : ℝ) ≤ R / g := by
    apply (le_div_iff₀ hgR).2
    have hn := Nat.div_mul_le_self ⌊R⌋₊ g
    have hnR : (((⌊R⌋₊ / g) * g : ℕ) : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast hn
    have hf := Nat.floor_le hR.le
    push_cast at hnR
    linarith
  have hgap : (((⌊R⌋₊ / g) * (2 * Q) : ℕ) : ℝ) ≤ 2 * (Q : ℝ) * R / g := by
    have hm := mul_le_mul_of_nonneg_right hfloor (show (0 : ℝ) ≤ 2 * (Q : ℝ) by positivity)
    have heq : (R / g) * (2 * (Q : ℝ)) = 2 * (Q : ℝ) * R / g := by ring
    rw [heq] at hm
    push_cast
    exact hm
  have hcancel : 2 * width / ((Nat.totient g : ℝ) * ell) = η * M * R / (r * X) - 1 / 2 := by
    rw [hwidth]
    exact mv_neighbour_radius_identity ell (Nat.totient g) g η M R r X
      (ne_of_gt hell) (ne_of_gt hphi) (ne_of_gt hgR)
  rw [hcancel]
  linarith [hgap, hreal]

/-- A complete single BT stage under the source's continuous BT5 budget,
with actual unused primes, multiple reduced classes, integer gap floors,
physical endpoint disjointness and exact depletion. The phase-start and
repeated-stage numerical gates remain explicit. -/
theorem mv_interval_stage_from_source_budget (mv : MVBrunTitchmarsh)
    (unused classes : Finset ℕ) (lo c X r R L η M ell width : ℝ) (g Q : ℕ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g) (hell : 0 < ell)
    (hclasscount : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L)
    (hwidth : width = (ell * (Nat.totient g : ℝ) / (2 * g)) * g *
      (η * M * R / (r * X) - 1 / 2))
    (hexp : Real.exp ell ≤ width / g)
    (hBT5 : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g) :
    ∃ (h : ℕ) (chosen : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊R⌋₊ ∧ width ≤ h ∧
      chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card := by
  have hne' : unused.Nonempty := hne
  obtain ⟨p, hp⟩ := hne'
  have hclasspos : 0 < classes.card := Finset.card_pos.mpr ⟨p % g, hclasses p hp⟩
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hwidthpos : (g : ℝ) < width :=
    (one_lt_div hgR).1 (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr hell) hexp)
  have hgate := bt_source_implies_exact_bin_gate unused classes c X r R L η M ell width g Q
    hM hNM hc hX hr hR hL hg hell hclasspos hclasscount hη hε hradius hwidth hBT5
  exact mv_interval_stage_select_and_deplete mv unused classes lo (c * X) R width ell g Q
    hne hprimes hinterval hclasses hreduced hg hR hwidthpos hell hexp hgate

end
end Sude
