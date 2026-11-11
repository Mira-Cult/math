import Sude.BTIntervalBins
import Sude.StepGrid

/-!
# T75.4 Fine-Grid Binning and Step-Gap Chain Construction

Band-independent construction of the `StepGapChain`, `narrow`, `wide`, `seed`, and `labels`
for T75's variable-gap step grid from:
1. A seed pair `(r0, r0 + h)` in `[y - D/2, y + D/2]` with `0 < h`,
2. A central prime set `A` in `[y - D/2, y + D/2]` in a single residue class modulo `h`
   with `D < 20 * (h : ℝ) * (A.card : ℝ)` and `2 ≤ A.card`,
3. A wide prime pair `(uw, vw)` in `[y - 3*D/4, y - D/2] × [y + D/2, y + 3*D/4]`
   in a single residue class modulo `h`.
-/

namespace Sude

noncomputable section

set_option maxHeartbeats 2000000

/-- In any nonempty finite set `B` of natural numbers in a single residue class modulo `h > 0`,
the difference between `B.max'` and `B.min'` is a multiple of `h` of size at least `(B.card - 1) * h`. -/
theorem mod_spread_ge_card_sub_one_mul (B : Finset ℕ) (h b : ℕ)
    (_hh : 0 < h) (hne : B.Nonempty) (hmod : ∀ x ∈ B, x % h = b) :
    let p_min := B.min' hne
    let p_max := B.max' hne
    p_min ∈ B ∧ p_max ∈ B ∧ p_min ≤ p_max ∧
      h ∣ p_max - p_min ∧ (B.card - 1) * h ≤ p_max - p_min := by
  dsimp only
  set p_min := B.min' hne
  set p_max := B.max' hne
  have hpmin : p_min ∈ B := Finset.min'_mem B hne
  have hpmax : p_max ∈ B := Finset.max'_mem B hne
  have hle : p_min ≤ p_max := Finset.min'_le B p_max hpmax
  have hdvd_elem : ∀ x ∈ B, h ∣ x - p_min := by
    intro x hx
    have hmin_x : p_min ≤ x := Finset.min'_le B x hx
    have hmx : x % h = b := hmod x hx
    have hmp : p_min % h = b := hmod p_min hpmin
    have hxdiv := (Nat.div_add_mod x h).symm
    have hpdiv := (Nat.div_add_mod p_min h).symm
    refine ⟨x / h - p_min / h, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  have hdvd : h ∣ p_max - p_min := hdvd_elem p_max hpmax
  let f : ℕ → ℕ := fun x => (x - p_min) / h
  have hinj : Set.InjOn f B := by
    intro x hx y hy hxy
    have hdx := Nat.div_mul_cancel (hdvd_elem x hx)
    have hdy := Nat.div_mul_cancel (hdvd_elem y hy)
    have hmin_x : p_min ≤ x := Finset.min'_le B x hx
    have hmin_y : p_min ≤ y := Finset.min'_le B y hy
    have hfx : (x - p_min) / h * h = (y - p_min) / h * h := congrArg (· * h) hxy
    omega
  have hsub : B.image f ⊆ Finset.range ((p_max - p_min) / h + 1) := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hx, rfl⟩
    rw [Finset.mem_range]
    have hxmax : x ≤ p_max := Finset.le_max' B x hx
    have hsub_le : x - p_min ≤ p_max - p_min := by omega
    have hdiv_le : (x - p_min) / h ≤ (p_max - p_min) / h := Nat.div_le_div_right hsub_le
    change (x - p_min) / h < (p_max - p_min) / h + 1
    omega
  have hcard_img : B.card ≤ (p_max - p_min) / h + 1 := by
    have hc1 : (B.image f).card = B.card := Finset.card_image_of_injOn hinj
    have hc2 : (B.image f).card ≤ (Finset.range ((p_max - p_min) / h + 1)).card :=
      Finset.card_le_card hsub
    rw [Finset.card_range, hc1] at hc2
    exact hc2
  have hcard_sub : B.card - 1 ≤ (p_max - p_min) / h := Nat.sub_le_of_le_add hcard_img
  have hmul : (B.card - 1) * h ≤ (p_max - p_min) / h * h := Nat.mul_le_mul_right h hcard_sub
  rw [Nat.div_mul_cancel hdvd] at hmul
  exact ⟨hpmin, hpmax, hle, hdvd, hmul⟩

/-- Pigeonhole on `⌊((p : ℝ) - u0) / (R : ℝ)⌋₊` produces two elements of `A` in the same bin
whose difference is a multiple of `h` in `[q * h, R]`. -/
theorem pigeonhole_spatial_bin (A : Finset ℕ) (u0 D : ℝ) (R h b q : ℕ)
    (hh : 0 < h) (hR : 0 < R) (hq : 1 ≤ q)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card) :
    ∃ p_min p_max : ℕ,
      p_min ∈ A ∧ p_max ∈ A ∧ p_min ≤ p_max ∧
      h ∣ p_max - p_min ∧ q * h ≤ p_max - p_min ∧ p_max - p_min ≤ R := by
  let K : ℕ := ⌊D / (R : ℝ)⌋₊ + 1
  let bin : ℕ → ℕ := fun p => ⌊((p : ℝ) - u0) / (R : ℝ)⌋₊
  let fiber : ℕ → Finset ℕ := fun k => A.filter (fun p => bin p = k)
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hA_sub : A ⊆ (Finset.range K).biUnion fiber := by
    intro p hp
    rw [Finset.mem_biUnion]
    refine ⟨bin p, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hp_int := hA_int p hp
      have hdiv : ((p : ℝ) - u0) / (R : ℝ) ≤ D / (R : ℝ) :=
        div_le_div_of_nonneg_right (by linarith) hRpos.le
      have hfl : bin p ≤ ⌊D / (R : ℝ)⌋₊ := Nat.floor_mono hdiv
      change bin p < ⌊D / (R : ℝ)⌋₊ + 1
      omega
    · simp [fiber, hp]
  have hex : ∃ k ∈ Finset.range K, q + 1 ≤ (fiber k).card := by
    by_contra hno
    have hle_q : ∀ k ∈ Finset.range K, (fiber k).card ≤ q := by
      intro k hk
      by_contra hgt
      exact hno ⟨k, hk, by omega⟩
    have hsum1 : A.card ≤ ((Finset.range K).biUnion fiber).card := Finset.card_le_card hA_sub
    have hsum2 : ((Finset.range K).biUnion fiber).card ≤ ∑ k ∈ Finset.range K, (fiber k).card :=
      Finset.card_biUnion_le
    have hsum3 : ∑ k ∈ Finset.range K, (fiber k).card ≤ ∑ _k ∈ Finset.range K, q :=
      Finset.sum_le_sum hle_q
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum3
    change (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card at hcard
    change ∑ k ∈ Finset.range K, (fiber k).card ≤ (⌊D / (R : ℝ)⌋₊ + 1) * q at hsum3
    omega
  rcases hex with ⟨k, _hk, hkcard⟩
  have hBne : (fiber k).Nonempty := Finset.card_pos.mp (by omega)
  have hBmod : ∀ x ∈ fiber k, x % h = b := by
    intro x hx
    exact hA_mod x (Finset.mem_filter.mp hx).1
  obtain ⟨hpmin, hpmax, hle, hdvd, hspread⟩ :=
    mod_spread_ge_card_sub_one_mul (fiber k) h b hh hBne hBmod
  have hpminA : (fiber k).min' hBne ∈ A := (Finset.mem_filter.mp hpmin).1
  have hpmaxA : (fiber k).max' hBne ∈ A := (Finset.mem_filter.mp hpmax).1
  have hbin_min : bin ((fiber k).min' hBne) = k :=
    (Finset.mem_filter.mp hpmin).2
  have hbin_max : bin ((fiber k).max' hBne) = k :=
    (Finset.mem_filter.mp hpmax).2
  have hgap_lt : (((fiber k).max' hBne : ℝ) - ((fiber k).min' hBne : ℝ)) < (R : ℝ) :=
    same_spatial_bin_gap hRpos (hA_int _ hpminA).1 (hbin_min.trans hbin_max.symm)
  have hgap_real : ((((fiber k).max' hBne - (fiber k).min' hBne : ℕ) : ℝ)) ≤ (R : ℝ) := by
    rw [Nat.cast_sub hle]
    linarith
  have hgap_nat : (fiber k).max' hBne - (fiber k).min' hBne ≤ R := by
    exact_mod_cast hgap_real
  have hq_le : q * h ≤ (fiber k).max' hBne - (fiber k).min' hBne := by
    have h1 : q ≤ (fiber k).card - 1 := by omega
    exact le_trans (Nat.mul_le_mul_right h h1) hspread
  exact ⟨(fiber k).min' hBne, (fiber k).max' hBne, hpminA, hpmaxA, hle, hdvd, hq_le, hgap_nat⟩

/-- Concatenation of two `StepGapChain`s. -/
theorem StepGapChain.append {K : Type*} (gap : K → ℕ) (step R : ℕ) (l₁ l₂ : List K)
    (h₁ : StepGapChain gap step R l₁)
    (h₂ : StepGapChain gap step (R + (l₁.map gap).sum) l₂) :
    StepGapChain gap step R (l₁ ++ l₂) := by
  induction h₁ with
  | nil R => simpa using h₂
  | cons R k ks hdvd hle _htail ih =>
    simp only [List.cons_append, List.map_cons, List.sum_cons] at h₂ ⊢
    rw [← Nat.add_assoc] at h₂
    exact StepGapChain.cons R k (ks ++ l₂) hdvd hle (ih h₂)

/-- Repeating a single valid step element `k` times forms a `StepGapChain`. -/
theorem StepGapChain.replicate {K : Type*} (gap : K → ℕ) (step R k : ℕ) (x : K)
    (hdvd : step ∣ gap x) (hle : gap x ≤ R + step) :
    StepGapChain gap step R (List.replicate k x) := by
  induction k generalizing R with
  | zero => exact StepGapChain.nil R
  | succ k ih =>
    simp only [List.replicate_succ]
    refine StepGapChain.cons R x (List.replicate k x) hdvd hle ?_
    exact ih (R + gap x) (by omega)

/-- Sum of mapped gaps on `List.replicate k x`. -/
theorem map_sum_replicate {K : Type*} (gap : K → ℕ) (k : ℕ) (x : K) :
    ((List.replicate k x).map gap).sum = k * gap x := by
  simp [List.map_replicate, List.sum_replicate]

/-- Single doubling step: while `(R : ℝ) ≤ D` and `72 * h ≤ R`, 144 copies of a same-bin pair
from `A` extend the step-gap chain and more than double `R`. -/
theorem t75_bin_double_step (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR72 : 72 * h ≤ R) (hRD : (R : ℝ) ≤ D)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 36 * (h : ℝ) * (A.card : ℝ)) :
    ∃ step_pairs : List (ℕ × ℕ),
      step_pairs.length = 144 ∧
      (∀ x ∈ step_pairs, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R step_pairs ∧
      2 * R < R + (step_pairs.map Prod.snd).sum := by
  have hRpos : 0 < R := by omega
  have hRposR : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hRpos
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le hRposR hRD
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  let q : ℕ := R / (72 * h)
  have hq : 1 ≤ q := Nat.div_pos hR72 (by omega)
  have hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card := by
    have hdiv1 : (1 : ℝ) ≤ D / (R : ℝ) := (one_le_div hRposR).mpr hRD
    have hfl : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) ≤ D / (R : ℝ) := Nat.floor_le (by positivity)
    have hK_le : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * D / (R : ℝ) := by
      have hsum : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ D / (R : ℝ) + D / (R : ℝ) :=
        add_le_add hfl hdiv1
      have htwo : D / (R : ℝ) + D / (R : ℝ) = 2 * D / (R : ℝ) := by ring
      push_cast
      linarith
    have hq_nat : q * (72 * h) ≤ R := Nat.div_mul_le_self R (72 * h)
    have hq_real : (q : ℝ) * (72 * (h : ℝ)) ≤ (R : ℝ) := by exact_mod_cast hq_nat
    have hq_nonneg : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hmul1 : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((q : ℝ) * (72 * (h : ℝ))) ≤
        (2 * D / (R : ℝ)) * (R : ℝ) := by
      have h2D_nonneg : (0 : ℝ) ≤ 2 * D / (R : ℝ) := div_nonneg (by linarith) hRposR.le
      have hm1 := mul_le_mul_of_nonneg_right hK_le (show (0 : ℝ) ≤ (q : ℝ) * (72 * (h : ℝ)) by positivity)
      have hm2 := mul_le_mul_of_nonneg_left hq_real h2D_nonneg
      exact le_trans hm1 hm2
    have hcancel : (2 * D / (R : ℝ)) * (R : ℝ) = 2 * D := div_mul_cancel₀ (2 * D) (ne_of_gt hRposR)
    rw [hcancel] at hmul1
    have hlt_real : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) < (A.card : ℝ) := by
      have hprod : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) * (72 * (h : ℝ)) <
          (A.card : ℝ) * (72 * (h : ℝ)) := by
        push_cast at hmul1 ⊢
        linarith
      exact lt_of_mul_lt_mul_right hprod (by positivity)
    exact_mod_cast hlt_real
  obtain ⟨p_min, p_max, hpmin, hpmax, hle, hdvd, hq_le, hgap_le⟩ :=
    pigeonhole_spatial_bin A u0 D R h b q hh hRpos hq hA_int hA_mod hcard
  let d : ℕ := p_max - p_min
  have hd_pos : 0 < d := by
    have hqh_pos : 0 < q * h := Nat.mul_pos (by omega) hh
    omega
  refine ⟨List.replicate 144 (p_min, d), by simp, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_replicate] at hx
    rcases hx with ⟨_, rfl⟩
    refine ⟨hpmin, ?_, hd_pos, hdvd⟩
    dsimp only
    have : p_min + d = p_max := by omega
    rw [this]
    exact hpmax
  · exact StepGapChain.replicate Prod.snd h R 144 (p_min, d) hdvd (by dsimp; omega)
  · rw [map_sum_replicate]
    dsimp only
    have hdiv_mod := (Nat.div_add_mod R (72 * h)).symm
    have hmod_lt : R % (72 * h) < 72 * h := Nat.mod_lt R (by omega)
    have hR_lt : R < 72 * h * (q + 1) := by
      change R < 72 * h * (R / (72 * h) + 1)
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have h2q : 72 * h * (q + 1) ≤ 144 * (q * h) := by
      have : q + 1 ≤ 2 * q := by omega
      nlinarith
    have h144d : 144 * (q * h) ≤ 144 * d := Nat.mul_le_mul_left 144 hq_le
    omega

/-- Iterating `t75_bin_double_step` `k` times either pushes the radius above `D`
or multiplies the initial radius by at least `2 ^ k`. -/
theorem t75_bin_double_loop (k : ℕ) (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hR72 : 72 * h ≤ R)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 36 * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 144 * k ∧
      (∀ x ∈ chain, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R chain ∧
      (D < ((R + (chain.map Prod.snd).sum : ℕ) : ℝ) ∨
        R * 2 ^ k ≤ R + (chain.map Prod.snd).sum) := by
  induction k generalizing R with
  | zero =>
    refine ⟨[], by simp, by simp, StepGapChain.nil R, Or.inr (by simp)⟩
  | succ k ih =>
    by_cases hRD : (R : ℝ) ≤ D
    · obtain ⟨step_pairs, hlen1, hmem1, hchain1, hdouble⟩ :=
        t75_bin_double_step A u0 D R h b hh hR72 hRD hA_int hA_mod hA_card
      let R1 : ℕ := R + (step_pairs.map Prod.snd).sum
      have hR1_72 : 72 * h ≤ R1 := by omega
      obtain ⟨rest, hlen2, hmem2, hchain2, hor⟩ :=
        ih R1 hR1_72
      refine ⟨step_pairs ++ rest, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hlen1]
        omega
      · intro x hx
        rcases List.mem_append.mp hx with hx1 | hx2
        · exact hmem1 x hx1
        · exact hmem2 x hx2
      · exact StepGapChain.append Prod.snd h R step_pairs rest hchain1 hchain2
      · rw [List.map_append, List.sum_append, ← Nat.add_assoc]
        rcases hor with hgt | hpow
        · exact Or.inl hgt
        · right
          have h2R : 2 * R ≤ R1 := by omega
          calc
            R * 2 ^ (k + 1) = (2 * R) * 2 ^ k := by ring
            _ ≤ R1 * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) h2R
            _ ≤ R1 + (rest.map Prod.snd).sum := hpow
    · have hRD' : D < (R : ℝ) := lt_of_not_ge hRD
      refine ⟨[], by simp, by simp, StepGapChain.nil R, Or.inl (by simpa using hRD')⟩

/-- Full narrow chain construction reaching `2 * D ≤ ((72 * h + sum : ℕ) : ℝ)`
with at most `4682` pairs from `A`. -/
theorem t75_narrow_chain_to_two_D (A : Finset ℕ) (u0 D : ℝ) (h b : ℕ)
    (hh : 0 < h) (hD_upper : D < ((72 * h * 2 ^ 32 : ℕ) : ℝ))
    (hA_card_ge : 2 ≤ A.card)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < 36 * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 4682 ∧
      (∀ x ∈ chain, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h (72 * h) chain ∧
      2 * D ≤ ((72 * h + (chain.map Prod.snd).sum : ℕ) : ℝ) := by
  obtain ⟨chain1, hlen1, hmem1, hchain1, hor⟩ :=
    t75_bin_double_loop 32 A u0 D (72 * h) h b hh (le_refl _) hA_int hA_mod hA_card
  let R1 : ℕ := 72 * h + (chain1.map Prod.snd).sum
  have hD_lt_R1 : D < (R1 : ℝ) := by
    rcases hor with hgt | hpow
    · exact hgt
    · have hpowR : ((72 * h * 2 ^ 32 : ℕ) : ℝ) ≤ (R1 : ℝ) := by exact_mod_cast hpow
      linarith
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hpmin, hpmax, hle, hdvd, hspread⟩ :=
    mod_spread_ge_card_sub_one_mul A h b hh hAne hA_mod
  let p_min := A.min' hAne
  let p_max := A.max' hAne
  let d_max := p_max - p_min
  have hdmax_pos : 0 < d_max := by
    have h1 : 1 * h ≤ (A.card - 1) * h := Nat.mul_le_mul_right h (by omega)
    omega
  have hdmax_le_D : (d_max : ℝ) ≤ D := by
    have hmin_int := hA_int p_min hpmin
    have hmax_int := hA_int p_max hpmax
    have hcast : (d_max : ℝ) = (p_max : ℝ) - (p_min : ℝ) := Nat.cast_sub hle
    linarith
  have hdmax_le_R1 : d_max ≤ R1 := by
    have : (d_max : ℝ) ≤ (R1 : ℝ) := by linarith
    exact_mod_cast this
  let top := List.replicate 74 (p_min, d_max)
  have hchain_top : StepGapChain Prod.snd h R1 top :=
    StepGapChain.replicate Prod.snd h R1 74 (p_min, d_max) hdvd (by dsimp; omega)
  refine ⟨chain1 ++ top, ?_, ?_, ?_, ?_⟩
  · rw [List.length_append]
    simp only [top, List.length_replicate]
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hmem1 x hx1
    · rw [List.mem_replicate] at hx2
      rcases hx2 with ⟨_, rfl⟩
      refine ⟨hpmin, ?_, hdmax_pos, hdvd⟩
      dsimp only
      have : p_min + d_max = p_max := by omega
      rw [this]
      exact hpmax
  · exact StepGapChain.append Prod.snd h (72 * h) chain1 top hchain1 hchain_top
  · rw [List.map_append, List.sum_append, map_sum_replicate]
    dsimp only
    have hm1 : 72 * ((A.card - 1) * h) ≤ 72 * d_max := Nat.mul_le_mul_left 72 hspread
    have hm2 : 36 * A.card ≤ 72 * (A.card - 1) := by omega
    have hm3 : 36 * A.card * h ≤ 72 * (A.card - 1) * h := Nat.mul_le_mul_right h hm2
    have h36_le : 36 * A.card * h ≤ 74 * d_max := by
      have h72_eq : 72 * (A.card - 1) * h = 72 * ((A.card - 1) * h) := by ring
      omega
    have h36_real : 36 * (h : ℝ) * (A.card : ℝ) ≤ ((74 * d_max : ℕ) : ℝ) := by
      have hcast : ((36 * A.card * h : ℕ) : ℝ) ≤ ((74 * d_max : ℕ) : ℝ) := by
        exact_mod_cast h36_le
      have heq : ((36 * A.card * h : ℕ) : ℝ) = 36 * (h : ℝ) * (A.card : ℝ) := by
        push_cast
        ring
      linarith
    have hsplit : ((72 * h + ((chain1.map Prod.snd).sum + 74 * d_max) : ℕ) : ℝ) =
        (R1 : ℝ) + ((74 * d_max : ℕ) : ℝ) := by
      have hnat : 72 * h + ((chain1.map Prod.snd).sum + 74 * d_max) = R1 + 74 * d_max := by
        dsimp [R1]
        omega
      rw [hnat, Nat.cast_add]
    linarith

/-- Attach sequential natural indices starting at `s` to a list of pairs. -/
def indexPairs : ℕ → List (ℕ × ℕ) → List (ℕ × (ℕ × ℕ))
  | _, [] => []
  | s, x :: xs => (s, x) :: indexPairs (s + 1) xs

@[simp]
theorem indexPairs_length (s : ℕ) (xs : List (ℕ × ℕ)) :
    (indexPairs s xs).length = xs.length := by
  induction xs generalizing s with
  | nil => rfl
  | cons _ xs ih => simp [indexPairs, ih (s + 1)]

theorem mem_indexPairs {s : ℕ} {xs : List (ℕ × ℕ)} {z : ℕ × (ℕ × ℕ)}
    (hz : z ∈ indexPairs s xs) :
    s ≤ z.1 ∧ z.1 < s + xs.length ∧ z.2 ∈ xs := by
  induction xs generalizing s with
  | nil => simp [indexPairs] at hz
  | cons x xs ih =>
    simp only [indexPairs, List.mem_cons] at hz
    rcases hz with rfl | htail
    · simp
    · obtain ⟨h1, h2, h3⟩ := ih htail
      refine ⟨by omega, ?_, List.mem_cons_of_mem x h3⟩
      simp only [List.length_cons]
      omega

theorem indexPairs_nodup (s : ℕ) (xs : List (ℕ × ℕ)) :
    (indexPairs s xs).Nodup := by
  induction xs generalizing s with
  | nil => simp [indexPairs]
  | cons x xs ih =>
    simp only [indexPairs, List.nodup_cons]
    refine ⟨?_, ih (s + 1)⟩
    intro hmem
    have h1 := (mem_indexPairs hmem).1
    omega

theorem indexPairs_append (s : ℕ) (xs ys : List (ℕ × ℕ)) :
    indexPairs s (xs ++ ys) = indexPairs s xs ++ indexPairs (s + xs.length) ys := by
  induction xs generalizing s with
  | nil => simp [indexPairs]
  | cons x xs ih =>
    simp only [List.cons_append, indexPairs, List.length_cons, ih (s + 1)]
    have : s + 1 + xs.length = s + (xs.length + 1) := by omega
    rw [this]

theorem indexPairs_stepGapChain (s h R : ℕ) (xs : List (ℕ × ℕ))
    (hchain : StepGapChain Prod.snd h R xs) :
    StepGapChain (fun z : ℕ × (ℕ × ℕ) => z.2.2) h R (indexPairs s xs) := by
  induction hchain generalizing s with
  | nil R => exact StepGapChain.nil R
  | cons R k ks hdvd hle _htail ih =>
    exact StepGapChain.cons R (s, k) (indexPairs (s + 1) ks) hdvd hle (ih (s + 1))

theorem indexPairs_toFinset_card (s : ℕ) (xs : List (ℕ × ℕ)) :
    (indexPairs s xs).toFinset.card = xs.length := by
  rw [List.toFinset_card_of_nodup (indexPairs_nodup s xs), indexPairs_length]

theorem indexPairs_toFinset_append (s : ℕ) (xs ys : List (ℕ × ℕ)) :
    (indexPairs s (xs ++ ys)).toFinset =
      (indexPairs s xs).toFinset ∪ (indexPairs (s + xs.length) ys).toFinset := by
  rw [indexPairs_append, List.toFinset_append]

/-- Abstract a replicated pair list so its length is not symbolically unfolded by `whnf`. -/
theorem exists_replicate_chain (h R k : ℕ) (x : ℕ × ℕ)
    (hdvd : h ∣ x.2) (hle : x.2 ≤ R + h) :
    ∃ l : List (ℕ × ℕ),
      l.length = k ∧
      (∀ y ∈ l, y = x) ∧
      (l.map Prod.snd).sum = k * x.2 ∧
      StepGapChain Prod.snd h R l :=
  ⟨List.replicate k x, List.length_replicate,
    fun _ hy => (List.mem_replicate.mp hy).2,
    map_sum_replicate Prod.snd k x,
    StepGapChain.replicate Prod.snd h R k x hdvd hle⟩

/-- Package the narrow, wide, seed, and label sets and functions for `fw_t75_nominal_targets_from_seed_chain`
from the seed pair `(r0, r0 + h)`, central prime set `A`, and wide prime pair `(uw, vw)`. -/
theorem t75_seed_chain_package_from_supplies
    {n h b b_w : ℕ} (hnlo : 14269 ≤ n) (hh_pos : 0 < h)
    (y D : ℝ) (hD_upper : D < ((72 * h * 2 ^ 32 : ℕ) : ℝ))
    (r0 : ℕ) (hr0_prime : Nat.Prime r0) (hr0h_prime : Nat.Prime (r0 + h))
    (hr0_lo : y - D / 2 ≤ (r0 : ℝ)) (hr0_hi : ((r0 + h : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ) (hA_prime : ∀ p ∈ A, Nat.Prime p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card_ge : 2 ≤ A.card) (hA_card : D < 36 * (h : ℝ) * (A.card : ℝ))
    (uw vw : ℕ) (huw_prime : Nat.Prime uw) (hvw_prime : Nat.Prime vw)
    (huw_mod : uw % h = b_w) (hvw_mod : vw % h = b_w)
    (huw_int : y - D ≤ (uw : ℝ) ∧ (uw : ℝ) ≤ y - D / 2)
    (hvw_int : y + D / 2 ≤ (vw : ℝ) ∧ (vw : ℝ) ≤ y + D) :
    ∃ (m : ℕ) (narrow wide seed : Finset (ℕ × (ℕ × ℕ)))
      (low gap : ℕ × (ℕ × ℕ) → ℕ) (labels : List (ℕ × (ℕ × ℕ))),
      2 ≤ m ∧
      Disjoint narrow wide ∧
      2 * narrow.card + 5 ≤ wide.card ∧
      m + (narrow ∪ wide).card = n ∧
      (∀ z ∈ narrow ∪ wide, Nat.Prime (low z) ∧ Nat.Prime (low z + gap z)) ∧
      (∀ z ∈ narrow ∪ wide, y - D ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D) ∧
      seed ∪ labels.toFinset = narrow ∪ wide ∧
      (∀ z ∈ seed, gap z = h) ∧
      labels.Nodup ∧
      (∀ z ∈ labels, z ∉ seed) ∧
      StepGapChain gap h (∑ z ∈ seed, gap z) labels ∧
      (∀ z ∈ narrow, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 2) ∧
      (∀ z ∈ wide, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 4) ∧
      (∀ z ∈ wide, D ≤ (gap z : ℝ)) := by
  obtain ⟨chain_narrow, hlen_narrow, hmem_narrow, hchain_narrow, hR_two_D⟩ :=
    t75_narrow_chain_to_two_D A (y - D / 2) D h b hh_pos hD_upper hA_card_ge
      (by
        intro p hp
        have hp' := hA_int p hp
        exact ⟨hp'.1, by linarith [hp'.2]⟩)
      hA_mod hA_card
  let dw : ℕ := vw - uw
  have huw_le_vw : uw ≤ vw := by
    have : (uw : ℝ) ≤ (vw : ℝ) := by linarith [huw_int.2, hvw_int.1]
    exact_mod_cast this
  have hdw_dvd : h ∣ dw := by
    have hudiv := (Nat.div_add_mod uw h).symm
    have hvdiv := (Nat.div_add_mod vw h).symm
    refine ⟨vw / h - uw / h, ?_⟩
    rw [Nat.mul_sub_left_distrib]
    omega
  have hdw_lo : D ≤ (dw : ℝ) := by
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    linarith [huw_int.2, hvw_int.1]
  have hdw_hi : (dw : ℝ) ≤ 2 * D := by
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    linarith [huw_int.1, hvw_int.2]
  have hdw_le_R : dw ≤ 72 * h + (chain_narrow.map Prod.snd).sum := by
    have : (dw : ℝ) ≤ ((72 * h + (chain_narrow.map Prod.snd).sum : ℕ) : ℝ) :=
      le_trans hdw_hi hR_two_D
    exact_mod_cast this
  let P : ℕ := 72 + chain_narrow.length
  let W : ℕ := 2 * P + 5
  obtain ⟨seed_list, hseed_len, hseed_mem, _hseed_sum_list, _hchain_seed⟩ :=
    exists_replicate_chain h 0 72 (r0, h) (dvd_refl h) (by dsimp; omega)
  obtain ⟨wide_list, hwide_len, hwide_mem, _hwide_sum_list, hchain_wide⟩ :=
    exists_replicate_chain h (72 * h + (chain_narrow.map Prod.snd).sum) W (uw, dw)
      hdw_dvd (by dsimp; omega)
  let seed : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 seed_list).toFinset
  let narrow : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 (seed_list ++ chain_narrow)).toFinset
  let wide : Finset (ℕ × (ℕ × ℕ)) := (indexPairs P wide_list).toFinset
  let labels : List (ℕ × (ℕ × ℕ)) := indexPairs 72 (chain_narrow ++ wide_list)
  let low : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.1
  let gap : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.2
  have hnarrow_card : narrow.card = P := by
    change (indexPairs 0 (seed_list ++ chain_narrow)).toFinset.card = P
    rw [indexPairs_toFinset_card, List.length_append, hseed_len]
  have hwide_card : wide.card = W := by
    change (indexPairs P wide_list).toFinset.card = W
    rw [indexPairs_toFinset_card, hwide_len]
  have hseed_card : seed.card = 72 := by
    change (indexPairs 0 seed_list).toFinset.card = 72
    rw [indexPairs_toFinset_card, hseed_len]
  have hdis : Disjoint narrow wide := by
    rw [Finset.disjoint_left]
    intro z hzn hzw
    rw [List.mem_toFinset] at hzn hzw
    have h1 := (mem_indexPairs hzn).2.1
    have h2 := (mem_indexPairs hzw).1
    rw [List.length_append, hseed_len] at h1
    omega
  have hS : seed ∪ labels.toFinset = narrow ∪ wide := by
    change (indexPairs 0 seed_list).toFinset ∪ (indexPairs 72 (chain_narrow ++ wide_list)).toFinset =
      (indexPairs 0 (seed_list ++ chain_narrow)).toFinset ∪ (indexPairs P wide_list).toFinset
    rw [indexPairs_toFinset_append 0 seed_list chain_narrow,
        indexPairs_toFinset_append 72 chain_narrow wide_list]
    simp only [hseed_len, Nat.zero_add, Finset.union_assoc]
    rfl
  have hseed_gap : ∀ z ∈ seed, gap z = h := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hzeq := hseed_mem z.2 (mem_indexPairs hz).2.2
    simp [gap, hzeq]
  have hseed_sum : (∑ z ∈ seed, gap z) = 72 * h := by
    calc
      (∑ z ∈ seed, gap z) = ∑ _z ∈ seed, h := Finset.sum_congr rfl hseed_gap
      _ = seed.card * h := by simp
      _ = 72 * h := by rw [hseed_card]
  have hchain_combined : StepGapChain Prod.snd h (72 * h) (chain_narrow ++ wide_list) :=
    StepGapChain.append Prod.snd h (72 * h) chain_narrow wide_list hchain_narrow hchain_wide
  have hchain : StepGapChain gap h (∑ z ∈ seed, gap z) labels := by
    rw [hseed_sum]
    exact indexPairs_stepGapChain 72 h (72 * h) (chain_narrow ++ wide_list) hchain_combined
  have hnodup : labels.Nodup := indexPairs_nodup 72 (chain_narrow ++ wide_list)
  have hfresh : ∀ z ∈ labels, z ∉ seed := by
    intro z hzl hzs
    rw [List.mem_toFinset] at hzs
    have h1 := (mem_indexPairs hzl).1
    have h2 := (mem_indexPairs hzs).2.1
    rw [hseed_len] at h2
    omega
  have hunion_card : (narrow ∪ wide).card = P + W := by
    rw [Finset.card_union_of_disjoint hdis, hnarrow_card, hwide_card]
  have hPW_le : P + W + 2 ≤ n := by
    have : P ≤ 4754 := by omega
    have : W = 2 * P + 5 := rfl
    omega
  let m : ℕ := n - (P + W)
  have hm : 2 ≤ m := by omega
  have hlen : m + (narrow ∪ wide).card = n := by
    rw [hunion_card]
    omega
  have hcount : 2 * narrow.card + 5 ≤ wide.card := by
    rw [hnarrow_card, hwide_card]
  have hmem_narrow_pair : ∀ z ∈ narrow, z.2 = (r0, h) ∨ z.2 ∈ chain_narrow := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hm_pair := (mem_indexPairs hz).2.2
    rcases List.mem_append.mp hm_pair with hm1 | hm2
    · exact Or.inl (hseed_mem z.2 hm1)
    · exact Or.inr hm2
  have hmem_wide_pair : ∀ z ∈ wide, z.2 = (uw, dw) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    exact hwide_mem z.2 (mem_indexPairs hz).2.2
  have hprime : ∀ z ∈ narrow ∪ wide, Nat.Prime (low z) ∧ Nat.Prime (low z + gap z) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · rcases hmem_narrow_pair z hzn with hseed_eq | hch
      · simp only [low, gap, hseed_eq]
        exact ⟨hr0_prime, hr0h_prime⟩
      · obtain ⟨hp1, hp2, _, _⟩ := hmem_narrow z.2 hch
        exact ⟨hA_prime _ hp1, hA_prime _ hp2⟩
    · have hw_eq := hmem_wide_pair z hzw
      simp only [low, gap, hw_eq]
      have : uw + dw = vw := by omega
      rw [this]
      exact ⟨huw_prime, hvw_prime⟩
  have hnarrow_bounds : ∀ z ∈ narrow, y - D / 2 ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D / 2 := by
    intro z hzn
    rcases hmem_narrow_pair z hzn with hseed_eq | hch
    · simp only [low, gap, hseed_eq]
      exact ⟨hr0_lo, hr0_hi⟩
    · obtain ⟨hp1, hp2, _, _⟩ := hmem_narrow z.2 hch
      exact ⟨(hA_int _ hp1).1, (hA_int _ hp2).2⟩
  have hwindow : ∀ z ∈ narrow ∪ wide, y - D ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · obtain ⟨hlo, hhi⟩ := hnarrow_bounds z hzn
      exact ⟨by linarith, by linarith [huw_int.1, hvw_int.1]⟩
    · have hw_eq := hmem_wide_pair z hzw
      simp only [low, gap, hw_eq]
      have hsum : uw + dw = vw := by omega
      rw [hsum]
      exact ⟨by linarith [huw_int.1, hvw_int.1], by linarith [huw_int.1, hvw_int.1, hvw_int.2]⟩
  have hnarrow_mid : ∀ z ∈ narrow, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 2 := by
    intro z hzn
    obtain ⟨hlo, hhi⟩ := hnarrow_bounds z hzn
    have hhi' : (low z : ℝ) + (gap z : ℝ) ≤ y + D / 2 := by exact_mod_cast hhi
    have hgap_nonneg : (0 : ℝ) ≤ (gap z : ℝ) := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hwide_mid : ∀ z ∈ wide, |(low z : ℝ) + (gap z : ℝ) / 2 - y| ≤ D / 4 := by
    intro z hzw
    have hw_eq := hmem_wide_pair z hzw
    simp only [low, gap, hw_eq]
    have hcast : (dw : ℝ) = (vw : ℝ) - (uw : ℝ) := Nat.cast_sub huw_le_vw
    rw [hcast, abs_le]
    constructor <;> linarith [huw_int.1, huw_int.2, hvw_int.1, hvw_int.2]
  have hgap_wide : ∀ z ∈ wide, D ≤ (gap z : ℝ) := by
    intro z hzw
    have hw_eq := hmem_wide_pair z hzw
    simp only [gap, hw_eq]
    exact hdw_lo
  exact ⟨m, narrow, wide, seed, low, gap, labels, hm, hdis, hcount, hlen, hprime, hwindow, hS,
    hseed_gap, hnodup, hfresh, hchain, hnarrow_mid, hwide_mid, hgap_wide⟩

end

end Sude
