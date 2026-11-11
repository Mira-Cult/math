import Sude.EvenIntervalGrid
import Sude.UpperTailAnalytic
import Sude.T75CompactBinning

/-!
# T75 Prime Target Vector Construction for the Open Upper Tail (`n ≥ 35,735`)

Constructs the prime line-sum target vector `f : Fin n → ℕ` with:
- `(∑ i, f i) = Lucas.poolTotal n`,
- `∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D` (`D = y / 400`),
for every odd `n ≥ 35,735` (unbounded above), using `EvenIntervalGrid` (step 2)
combined with `t75_greedy_brackets` at modulus `h = 2`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Section 1: T75 Target Vector from `EvenIntervalGrid` at Modulus `h = 2` -/

/-- Construct an indexed prime target vector `f : Fin n → ℕ` of exact total `Lucas.poolTotal n`
from a single odd-prime bracket `(p_lo, p_hi)` and an `EvenIntervalGrid` of controlled
odd-prime pairs in `[y - D, y + D]`. -/
theorem t75_targets_of_evenIntervalGrid {β : Type*} [DecidableEq β]
    {n m : ℕ} (hn_pos : 0 < n) (hn : Odd n)
    (p_lo p_hi : ℕ) (S : Finset β) (low gap : β → ℕ) (A B : ℕ)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD : 0 ≤ D)
    (hlen : m + S.card = n)
    (hplo : Nat.Prime p_lo ∧ Odd p_lo ∧ y - D ≤ (p_lo : ℝ) ∧ (p_lo : ℝ) ≤ y)
    (hphi : Nat.Prime p_hi ∧ Odd p_hi ∧ y ≤ (p_hi : ℝ) ∧ (p_hi : ℝ) ≤ y + D)
    (hS_prime : ∀ i ∈ S, Nat.Prime (low i) ∧ Odd (low i) ∧
      Nat.Prime (low i + gap i) ∧ Odd (low i + gap i))
    (hS_win : ∀ i ∈ S, y - D ≤ (low i : ℝ) ∧ ((low i + gap i : ℕ) : ℝ) ≤ y + D)
    (hgrid : EvenIntervalGrid S gap A B)
    (hmargin_lo : (A : ℝ) + D ≤ (S.card : ℝ) * y - ((∑ i ∈ S, low i : ℕ) : ℝ))
    (hmargin_hi : (S.card : ℝ) * y - ((∑ i ∈ S, low i : ℕ) : ℝ) + D ≤ (B : ℝ)) :
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  let xs : List Unit := List.replicate m ()
  let freeLo : Unit → ℕ := fun _ => p_lo
  let freeHi : Unit → ℕ := fun _ => p_hi
  have hbracket : ∀ x ∈ xs, y - D ≤ (freeLo x : ℝ) ∧ (freeLo x : ℝ) ≤ y ∧
      y ≤ (freeHi x : ℝ) ∧ (freeHi x : ℝ) ≤ y + D := by
    intro _ _
    exact ⟨hplo.2.2.1, hplo.2.2.2, hphi.2.2.1, hphi.2.2.2⟩
  have hclass : ∀ x ∈ xs, freeLo x % 2 = freeHi x % 2 := by
    intro _ _
    dsimp [freeLo, freeHi]
    rw [Nat.odd_iff.mp hplo.2.1, Nat.odd_iff.mp hphi.2.1]
  obtain ⟨values, hchoice, hbalance, hmod⟩ :=
    t75_greedy_brackets xs freeLo freeHi 2 y D hD hbracket hclass
  have hval_len : values.length = m := by
    simpa [xs] using hchoice.length_eq.symm
  have hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ) * y := by
    rw [hy, prescribedPoolValues_mean]
    have h1 := t75_pool_mean_line_total hn_pos
    rw [t75_line_mean_eq_order_mul_pool_mean hn_pos] at h1
    nlinarith
  have htotal : (Lucas.poolTotal n : ℝ) = ((m : ℝ) + (S.card : ℝ)) * y := by
    have hn_cast : (n : ℝ) = (m : ℝ) + (S.card : ℝ) := by exact_mod_cast hlen.symm
    rw [hcenter, hn_cast]
  have hb := abs_le.mp (by simpa [xs] using hbalance : |(values.sum : ℝ) - (m : ℝ) * y| ≤ D)
  have hlo_real : (values.sum : ℝ) + ((∑ i ∈ S, low i : ℕ) : ℝ) + (A : ℝ) ≤
      (Lucas.poolTotal n : ℝ) := by
    linarith [hb.2, hmargin_lo, htotal]
  have hhi_real : (Lucas.poolTotal n : ℝ) ≤
      (values.sum : ℝ) + ((∑ i ∈ S, low i : ℕ) : ℝ) + (B : ℝ) := by
    linarith [hb.1, hmargin_hi, htotal]
  have hlo_nat : values.sum + (∑ i ∈ S, low i) + A ≤ Lucas.poolTotal n := by
    exact_mod_cast hlo_real
  have hhi_nat : Lucas.poolTotal n ≤ values.sum + (∑ i ∈ S, low i) + B := by
    exact_mod_cast hhi_real
  let q_res : ℕ := Lucas.poolTotal n - (values.sum + ∑ i ∈ S, low i)
  have hqA : A ≤ q_res := by omega
  have hqB : q_res ≤ B := by omega
  have hLmod : (∑ i ∈ S, low i) % 2 = S.card % 2 := by
    rw [Finset.sum_nat_mod]
    have heq : (∑ i ∈ S, low i % 2) = S.card := by
      calc (∑ i ∈ S, low i % 2)
          = ∑ _i ∈ S, (1 : ℕ) :=
            Finset.sum_congr rfl (fun i hi => Nat.odd_iff.mp (hS_prime i hi).2.1)
        _ = S.card := by simp
    rw [heq]
  have hxs_mod : (xs.map freeLo).sum % 2 = m % 2 := by
    have hplo_mod : p_lo % 2 = 1 := Nat.odd_iff.mp hplo.2.1
    simp [xs, freeLo, Nat.mul_mod, hplo_mod]
  have htmod : Lucas.poolTotal n % 2 = n % 2 := t75_pool_total_mod_two hn
  have hq_even : 2 ∣ q_res := by
    rw [Nat.dvd_iff_mod_eq_zero]
    have hsum_eq : (values.sum + ∑ i ∈ S, low i) + q_res = Lucas.poolTotal n := by omega
    have hm1 : (values.sum + ∑ i ∈ S, low i) % 2 = n % 2 := by
      rw [Nat.add_mod, hmod, hxs_mod, hLmod, ← Nat.add_mod, hlen]
    omega
  obtain ⟨chosen, hsub, hsum_chosen⟩ := hgrid q_res hqA hqB hq_even
  let controlled := S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
  let targets := values ++ controlled
  have htargets_len : targets.length = n := by
    simp [targets, controlled, hval_len, hlen]
  have hsum_ctrl : controlled.sum = (∑ i ∈ S, low i) + ∑ i ∈ chosen, gap i := by
    dsimp [controlled]
    rw [Finset.sum_map_toList]
    calc
      (∑ i ∈ S, (if i ∈ chosen then low i + gap i else low i))
        = ∑ i ∈ S, (low i + if i ∈ chosen then gap i else 0) := by
          apply Finset.sum_congr rfl
          intro i _
          split <;> omega
      _ = (∑ i ∈ S, low i) + ∑ i ∈ S, (if i ∈ chosen then gap i else 0) := Finset.sum_add_distrib
      _ = (∑ i ∈ S, low i) + ∑ i ∈ chosen, gap i := by
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
  have htargets_sum : targets.sum = Lucas.poolTotal n := by
    dsimp [targets]
    rw [List.sum_append, hsum_ctrl, hsum_chosen]
    omega
  have hfree_prime_odd : ∀ x ∈ xs, (Nat.Prime (freeLo x) ∧ Odd (freeLo x)) ∧
      (Nat.Prime (freeHi x) ∧ Odd (freeHi x)) := by
    intro _ _
    exact ⟨⟨hplo.1, hplo.2.1⟩, ⟨hphi.1, hphi.2.1⟩⟩
  have hval_mem : ∀ v ∈ values, v = p_lo ∨ v = p_hi := by
    have hforall : ∀ (xs' : List Unit) (vs' : List ℕ),
        List.Forall₂ (fun x v => v = freeLo x ∨ v = freeHi x) xs' vs' →
        ∀ v ∈ vs', v = p_lo ∨ v = p_hi := by
      intro xs' vs' h
      induction h with
      | nil => simp
      | @cons x v xs'' vs'' hhead _ ih =>
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hz'
        · exact hhead
        · exact ih z hz'
    exact hforall xs values hchoice
  let e : Fin n ≃ Fin targets.length := finCongr htargets_len.symm
  let f : Fin n → ℕ := fun i => targets.get (e i)
  refine ⟨f, ?_, ?_⟩
  · calc (∑ i, f i)
        = ∑ i : Fin targets.length, targets.get i := Equiv.sum_comp e targets.get
      _ = targets.sum := by rw [← List.sum_ofFn, List.ofFn_get]
      _ = Lucas.poolTotal n := htargets_sum
  · intro i
    have hmem : f i ∈ targets := List.get_mem _ _
    simp only [targets, controlled, List.mem_append, List.mem_map, Finset.mem_toList] at hmem
    rcases hmem with hv | ⟨k, hk, hfk⟩
    · rcases hval_mem (f i) hv with hlo_eq | hhi_eq
      · rw [hlo_eq]
        exact ⟨hplo.1, hplo.2.1, abs_le.mpr ⟨by linarith [hplo.2.2.1], by linarith [hplo.2.2.2]⟩⟩
      · rw [hhi_eq]
        exact ⟨hphi.1, hphi.2.1, abs_le.mpr ⟨by linarith [hphi.2.2.1], by linarith [hphi.2.2.2]⟩⟩
    · rw [← hfk]
      have hkp := hS_prime k hk
      have hkw := hS_win k hk
      have hle : (low k : ℝ) ≤ ((low k + gap k : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right (low k) (gap k)
      split
      · exact ⟨hkp.2.2.1, hkp.2.2.2, abs_le.mpr ⟨by linarith, by linarith⟩⟩
      · exact ⟨hkp.1, hkp.2.1, abs_le.mpr ⟨by linarith, by linarith⟩⟩

/-! ## Section 2: Doubling Step-Gap Chain and Modulo-`h0` Cover Extraction -/

/-- Single doubling step for a `StepGapChain` of step `h` inside `A`. -/
theorem upper_tail_double_step (C : ℕ) (hC : 1 ≤ C)
    (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hRC : 2 * C * h ≤ R) (hRD : (R : ℝ) ≤ D)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < (C : ℝ) * (h : ℝ) * (A.card : ℝ)) :
    ∃ step_pairs : List (ℕ × ℕ),
      step_pairs.length = 4 * C ∧
      (∀ x ∈ step_pairs, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2) ∧
      StepGapChain Prod.snd h R step_pairs ∧
      2 * R < R + (step_pairs.map Prod.snd).sum := by
  have h2Ch_pos : 0 < 2 * C * h := Nat.mul_pos (by omega) hh
  have hRpos : 0 < R := lt_of_lt_of_le h2Ch_pos hRC
  have hRposR : (0 : ℝ) < (R : ℝ) := Nat.cast_pos.mpr hRpos
  have h2ChR_pos : (0 : ℝ) < 2 * (C : ℝ) * (h : ℝ) := by exact_mod_cast h2Ch_pos
  let q : ℕ := R / (2 * C * h)
  have hq1 : 1 ≤ q := Nat.div_pos hRC h2Ch_pos
  have hcard : (⌊D / (R : ℝ)⌋₊ + 1) * q < A.card := by
    have hdiv1 : (1 : ℝ) ≤ D / (R : ℝ) := (one_le_div hRposR).mpr hRD
    have hfl : ((⌊D / (R : ℝ)⌋₊ : ℕ) : ℝ) ≤ D / (R : ℝ) := Nat.floor_le (by positivity)
    have hK_le : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (D / (R : ℝ)) := by
      push_cast; linarith
    have hq_nat : q * (2 * C * h) ≤ R := Nat.div_mul_le_self R (2 * C * h)
    have hq_real : (q : ℝ) * (2 * (C : ℝ) * (h : ℝ)) ≤ (R : ℝ) := by exact_mod_cast hq_nat
    have hm1 := mul_le_mul_of_nonneg_right hK_le
      (show (0 : ℝ) ≤ (q : ℝ) * (2 * (C : ℝ) * (h : ℝ)) by positivity)
    have hm2 := mul_le_mul_of_nonneg_left hq_real (show (0 : ℝ) ≤ 2 * (D / (R : ℝ)) by positivity)
    have hmul : ((⌊D / (R : ℝ)⌋₊ + 1 : ℕ) : ℝ) * ((q : ℝ) * (2 * (C : ℝ) * (h : ℝ))) ≤ 2 * D := by
      have hc : (2 * (D / (R : ℝ))) * (R : ℝ) = 2 * D := by
        rw [mul_assoc, div_mul_cancel₀ _ hRposR.ne']
      linarith
    have hlt_real : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) < (A.card : ℝ) := by
      have hprod : (((⌊D / (R : ℝ)⌋₊ + 1) * q : ℕ) : ℝ) * (2 * (C : ℝ) * (h : ℝ)) <
          (A.card : ℝ) * (2 * (C : ℝ) * (h : ℝ)) := by
        push_cast at hmul ⊢; linarith
      exact lt_of_mul_lt_mul_right hprod h2ChR_pos.le
    exact_mod_cast hlt_real
  obtain ⟨p_min, p_max, hpmin, hpmax, hle, hdvd, hq_le, hgap_le⟩ :=
    pigeonhole_spatial_bin A u0 D R h b q hh hRpos hq1 hA_int hA_mod hcard
  let d : ℕ := p_max - p_min
  have hd_pos : 0 < d := lt_of_lt_of_le (Nat.mul_pos hq1 hh) hq_le
  refine ⟨List.replicate (4 * C) (p_min, d), by simp, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_replicate.mp hx with ⟨_, rfl⟩
    refine ⟨hpmin, ?_, hd_pos, hdvd⟩
    dsimp only
    have : p_min + d = p_max := by omega
    rw [this]; exact hpmax
  · exact StepGapChain.replicate Prod.snd h R (4 * C) (p_min, d) hdvd (by dsimp; omega)
  · rw [map_sum_replicate]
    dsimp only
    have hdiv_mod := (Nat.div_add_mod R (2 * C * h)).symm
    have hmod_lt : R % (2 * C * h) < 2 * C * h := Nat.mod_lt R h2Ch_pos
    have hR_lt : R < (2 * C * h) * (q + 1) := by
      change R < (2 * C * h) * (R / (2 * C * h) + 1)
      rw [Nat.mul_add, Nat.mul_one]; omega
    have h2q : (2 * C * h) * (q + 1) ≤ (4 * C) * (q * h) := by
      have hq2 : q + 1 ≤ 2 * q := by omega
      calc (2 * C * h) * (q + 1) ≤ (2 * C * h) * (2 * q) := Nat.mul_le_mul_left _ hq2
        _ = (4 * C) * (q * h) := by ring
    have h4Cd : (4 * C) * (q * h) ≤ (4 * C) * d := Nat.mul_le_mul_left (4 * C) hq_le
    omega

/-- Multi-step doubling loop for a `StepGapChain` of step `h` inside `A`. -/
theorem upper_tail_double_loop (C k : ℕ) (hC : 1 ≤ C)
    (A : Finset ℕ) (u0 D : ℝ) (R h b : ℕ)
    (hh : 0 < h) (hRC : 2 * C * h ≤ R)
    (hA_int : ∀ p ∈ A, u0 ≤ (p : ℝ) ∧ (p : ℝ) ≤ u0 + D)
    (hA_mod : ∀ p ∈ A, p % h = b)
    (hA_card : D < (C : ℝ) * (h : ℝ) * (A.card : ℝ)) :
    ∃ chain : List (ℕ × ℕ),
      chain.length ≤ 4 * C * k ∧
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
        upper_tail_double_step C hC A u0 D R h b hh hRC hRD hA_int hA_mod hA_card
      let R1 : ℕ := R + (step_pairs.map Prod.snd).sum
      obtain ⟨rest, hlen2, hmem2, hchain2, hor⟩ := ih R1 (by omega)
      refine ⟨step_pairs ++ rest, ?_, ?_, ?_, ?_⟩
      · rw [List.length_append, hlen1]
        have : 4 * C + 4 * C * k = 4 * C * (k + 1) := by ring
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
          calc R * 2 ^ (k + 1) = (2 * R) * 2 ^ k := by ring
            _ ≤ R1 * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) (by omega)
            _ ≤ R1 + (rest.map Prod.snd).sum := hpow
    · exact ⟨[], by simp, by simp, StepGapChain.nil R, Or.inl (by simpa using lt_of_not_ge hRD)⟩

/-- Construct an indexed set `S_mod : Finset (ℕ × (ℕ × ℕ))` of size `steps ≤ h0 - 1` (with indices
in `Finset.Ico offset (offset + steps)`) covering at least `steps + 1` residues modulo `h0`. -/
theorem exists_indexed_mod_cover {h0 : ℕ} (hh0 : 0 < h0)
    (P : ℕ → ℕ → Prop) (offset : ℕ)
    (hsupply : ∀ p : ℕ, Nat.Prime p → p ∣ h0 →
      ∃ u g : ℕ, P u g ∧ 2 ∣ g ∧ ¬ (p ∣ g / 2)) :
    ∀ steps : ℕ, steps ≤ h0 - 1 →
      ∃ (S_mod : Finset (ℕ × (ℕ × ℕ))) (A : Finset ℕ),
        S_mod.card = steps ∧
        (∀ z ∈ S_mod, offset ≤ z.1 ∧ z.1 < offset + steps ∧ P z.2.1 z.2.2 ∧ 2 ∣ z.2.2) ∧
        ModAchievable h0 (fun z => z.2.2) S_mod A ∧
        min h0 (steps + 1) ≤ A.card := by
  intro steps
  induction steps with
  | zero =>
    intro _
    refine ⟨∅, {0}, by simp, by simp,
      modAchievable_empty h0 (fun z : ℕ × (ℕ × ℕ) => z.2.2) hh0, ?_⟩
    simp [Nat.min_eq_right hh0]
  | succ s ih =>
    intro hs
    have hh0_2 : 2 ≤ h0 := by omega
    obtain ⟨S_s, A_s, hcard_s, hmem_s, hmod_s, hA_card_s⟩ := ih (by omega)
    obtain ⟨p, hp_prime, hp_dvd, hstep⟩ := modAchievable_step_prime hh0_2 hmod_s
    obtain ⟨u, g, hP, heven, hndvd⟩ := hsupply p hp_prime hp_dvd
    let z_new : ℕ × (ℕ × ℕ) := (offset + s, (u, g))
    have hz_notMem : z_new ∉ S_s := by
      intro hm
      have hlt := (hmem_s z_new hm).2.1
      dsimp [z_new] at hlt
      omega
    have ⟨hmod_new, hcard_new⟩ := hstep z_new hz_notMem heven hndvd
    refine ⟨insert z_new S_s, _, ?_, ?_, hmod_new, ?_⟩
    · rw [Finset.card_insert_of_notMem hz_notMem, hcard_s]
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz_old
      · dsimp [z_new]
        exact ⟨by omega, by omega, hP, heven⟩
      · have hold := hmem_s z hz_old
        exact ⟨hold.1, by omega, hold.2.2.1, hold.2.2.2⟩
    · omega

/-- Pigeonhole on the `h0` odd residue classes modulo `2 * h0`: for any finite set `S` of odd
integers, there is an odd residue `b < 2 * h0` whose fiber `A` satisfies `S.card ≤ h0 * A.card`. -/
theorem exists_odd_residue_fiber_ge (S : Finset ℕ) (h0 : ℕ) (hh0 : 0 < h0)
    (hodd : ∀ p ∈ S, Odd p) :
    ∃ b < 2 * h0,
      S.card ≤ h0 * (S.filter (fun p => p % (2 * h0) = b)).card := by
  let fiber : ℕ → Finset ℕ := fun j => S.filter (fun p => p % (2 * h0) = 2 * j + 1)
  have hsub : S ⊆ (Finset.range h0).biUnion fiber := by
    intro p hp
    rw [Finset.mem_biUnion]
    let j := (p % (2 * h0)) / 2
    have hmod_lt : p % (2 * h0) < 2 * h0 := Nat.mod_lt p (by omega)
    have hp_odd_mod : (p % (2 * h0)) % 2 = 1 := by
      rw [Nat.mod_mod_of_dvd p ⟨h0, by ring⟩]
      exact Nat.odd_iff.mp (hodd p hp)
    refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [fiber, Finset.mem_filter]
    exact ⟨hp, by omega⟩
  have hsum : S.card ≤ ∑ j ∈ Finset.range h0, (fiber j).card :=
    (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  by_contra hno
  have hlt : ∀ j ∈ Finset.range h0, h0 * (fiber j).card < S.card := by
    intro j hj
    have hj_lt : j < h0 := Finset.mem_range.mp hj
    by_contra hge
    exact hno ⟨2 * j + 1, by omega, by dsimp [fiber] at hge; omega⟩
  have hsum_mul : h0 * ∑ j ∈ Finset.range h0, (fiber j).card < h0 * S.card := by
    rw [Finset.mul_sum]
    calc (∑ j ∈ Finset.range h0, h0 * (fiber j).card)
        < ∑ _j ∈ Finset.range h0, S.card :=
          Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (by omega)) hlt
      _ = h0 * S.card := by simp
  have hle_mul : h0 * S.card ≤ h0 * ∑ j ∈ Finset.range h0, (fiber j).card :=
    Nat.mul_le_mul_left h0 hsum
  omega

/-- Package seed, doubling step-gap chain, modulo-`h0` cover, and wide prime pairs into an
`EvenIntervalGrid` and extract the T75 prime target vector `f : Fin n → ℕ`. -/
theorem t75_targets_from_evenIntervalGrid_supplies
    {n h0 b C k H0 : ℕ} (hn_pos : 0 < n) (hn : Odd n)
    (hC : 1 ≤ C) (hh0 : 0 < h0) (hh0_le : h0 ≤ H0)
    (hsize_le : 2 * (2 * C + 4 * C * k + (H0 + 6) * C + H0) + H0 + 4 ≤ n)
    (y D : ℝ)
    (hy : y = (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue)
    (hD_pos : 0 < D)
    (hD_upper : D < ((2 * C * (2 * h0) * 2 ^ k : ℕ) : ℝ))
    (p_lo p_hi : ℕ)
    (hplo : Nat.Prime p_lo ∧ Odd p_lo ∧ y - D ≤ (p_lo : ℝ) ∧ (p_lo : ℝ) ≤ y - D / 2)
    (hphi : Nat.Prime p_hi ∧ Odd p_hi ∧ y + D / 2 ≤ (p_hi : ℝ) ∧ (p_hi : ℝ) ≤ y + D)
    (r0 : ℕ)
    (hr0 : Nat.Prime r0 ∧ Odd r0 ∧ Nat.Prime (r0 + 2 * h0) ∧ Odd (r0 + 2 * h0))
    (hr0_int : y - D / 2 ≤ (r0 : ℝ) ∧ ((r0 + 2 * h0 : ℕ) : ℝ) ≤ y + D / 2)
    (A : Finset ℕ)
    (hA_prime : ∀ p ∈ A, Nat.Prime p ∧ Odd p)
    (hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2)
    (hA_mod : ∀ p ∈ A, p % (2 * h0) = b)
    (hA_card_ge : 2 ≤ A.card)
    (hA_card : D < (C : ℝ) * ((2 * h0 : ℕ) : ℝ) * (A.card : ℝ))
    (hmod_supply : ∀ p : ℕ, Nat.Prime p → p ∣ h0 →
      ∃ u g : ℕ,
        (Nat.Prime u ∧ Odd u ∧ Nat.Prime (u + g) ∧ Odd (u + g) ∧
          y - D / 2 ≤ (u : ℝ) ∧ ((u + g : ℕ) : ℝ) ≤ y + D / 2 ∧ (g : ℝ) ≤ D / 2) ∧
        2 ∣ g ∧ ¬ (p ∣ g / 2)) :
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  let h : ℕ := 2 * h0
  have hh_pos : 0 < h := by omega
  have hA_int_shift : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ (y - D / 2) + D := by
    intro p hp
    exact ⟨(hA_int p hp).1, by linarith [(hA_int p hp).2]⟩
  obtain ⟨ch1, hlen1, hmem1, hsc1, hor1⟩ :=
    upper_tail_double_loop C k hC A (y - D / 2) D (2 * C * h) h b hh_pos (le_refl _)
      hA_int_shift hA_mod hA_card
  let R1 : ℕ := 2 * C * h + (ch1.map Prod.snd).sum
  have hD_lt_R1 : D < (R1 : ℝ) := by
    rcases hor1 with hgt | hpow
    · exact hgt
    · have hpowR : ((2 * C * h * 2 ^ k : ℕ) : ℝ) ≤ (R1 : ℝ) := Nat.cast_le.mpr hpow
      linarith
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨hpmin, hpmax, hle_minmax, hdvd_max, hspread⟩ :=
    mod_spread_ge_card_sub_one_mul A h b hh_pos hAne hA_mod
  let p_min := A.min' hAne
  let p_max := A.max' hAne
  let d_max := p_max - p_min
  have hdmax_pos : 0 < d_max := lt_of_lt_of_le (Nat.mul_pos (by omega) hh_pos) hspread
  have hdmax_le_R1 : d_max ≤ R1 := by
    have hcast : (d_max : ℝ) = (p_max : ℝ) - (p_min : ℝ) := Nat.cast_sub hle_minmax
    have hleD : (d_max : ℝ) ≤ D := by linarith [(hA_int p_min hpmin).1, (hA_int p_max hpmax).2]
    have : (d_max : ℝ) ≤ (R1 : ℝ) := by linarith
    exact_mod_cast this
  let top_count : ℕ := (H0 + 6) * C
  let top := List.replicate top_count (p_min, d_max)
  have hsc_top : StepGapChain Prod.snd h R1 top :=
    StepGapChain.replicate Prod.snd h R1 top_count (p_min, d_max) hdvd_max (by dsimp; omega)
  let chain_narrow := ch1 ++ top
  have hchain_narrow : StepGapChain Prod.snd h (2 * C * h) chain_narrow :=
    StepGapChain.append Prod.snd h (2 * C * h) ch1 top hsc1 hsc_top
  have hmem_narrow : ∀ x ∈ chain_narrow, x.1 ∈ A ∧ x.1 + x.2 ∈ A ∧ 0 < x.2 ∧ h ∣ x.2 := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx2
    · exact hmem1 x hx1
    · rcases List.mem_replicate.mp hx2 with ⟨_, rfl⟩
      refine ⟨hpmin, ?_, hdmax_pos, hdvd_max⟩
      dsimp only
      have : p_min + d_max = p_max := by omega
      rw [this]; exact hpmax
  let R_step : ℕ := 2 * C * h + (chain_narrow.map Prod.snd).sum
  have hR_step_bound : ((H0 + 6 : ℕ) : ℝ) * (D / 2) < (R_step : ℝ) := by
    have hm2 : A.card ≤ 2 * (A.card - 1) := by omega
    have hm3 : C * A.card * h ≤ 2 * C * ((A.card - 1) * h) := by
      calc C * A.card * h ≤ C * (2 * (A.card - 1)) * h :=
            Nat.mul_le_mul_right h (Nat.mul_le_mul_left C hm2)
        _ = 2 * C * ((A.card - 1) * h) := by ring
    have hm4 : 2 * C * ((A.card - 1) * h) ≤ 2 * C * d_max :=
      Nat.mul_le_mul_left (2 * C) hspread
    have hCd : D < 2 * (C : ℝ) * (d_max : ℝ) := by
      have hc : ((C * A.card * h : ℕ) : ℝ) ≤ ((2 * C * d_max : ℕ) : ℝ) :=
        Nat.cast_le.mpr (hm3.trans hm4)
      push_cast at hc
      linarith
    have htop_real : ((H0 + 6 : ℕ) : ℝ) * (D / 2) < ((top_count * d_max : ℕ) : ℝ) := by
      have hpos_H : (0 : ℝ) < ((H0 + 6 : ℕ) : ℝ) := by positivity
      have hm := mul_lt_mul_of_pos_left hCd hpos_H
      dsimp [top_count]
      push_cast at hm ⊢
      linarith
    have hR_eq : R_step = R1 + top_count * d_max := by
      simp only [R_step, chain_narrow, top, List.map_append, List.sum_append, map_sum_replicate]
      dsimp [R1]; omega
    have hR1_nonneg : (0 : ℝ) ≤ (R1 : ℝ) := Nat.cast_nonneg R1
    rw [hR_eq]
    push_cast at htop_real ⊢
    linarith
  -- Package `S_step` as a `CompleteStepGrid` of step `h = 2 * h0`
  let seed_count : ℕ := 2 * C
  obtain ⟨seed_list, hseed_len, hseed_mem, _, _⟩ :=
    exists_replicate_chain h 0 seed_count (r0, h) (dvd_refl h) (by dsimp; omega)
  let seed : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 seed_list).toFinset
  let labels_step : List (ℕ × (ℕ × ℕ)) := indexPairs seed_count chain_narrow
  let S_step : Finset (ℕ × (ℕ × ℕ)) := (indexPairs 0 (seed_list ++ chain_narrow)).toFinset
  let low : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.1
  let gap : ℕ × (ℕ × ℕ) → ℕ := fun z => z.2.2
  have hseed_card : seed.card = seed_count := by
    change (indexPairs 0 seed_list).toFinset.card = seed_count
    rw [indexPairs_toFinset_card, hseed_len]
  have hS_step_card : S_step.card = seed_count + chain_narrow.length := by
    change (indexPairs 0 (seed_list ++ chain_narrow)).toFinset.card = _
    rw [indexPairs_toFinset_card, List.length_append, hseed_len]
  have hS_step_union : seed ∪ labels_step.toFinset = S_step := by
    change (indexPairs 0 seed_list).toFinset ∪ (indexPairs seed_count chain_narrow).toFinset =
      (indexPairs 0 (seed_list ++ chain_narrow)).toFinset
    rw [indexPairs_toFinset_append 0 seed_list chain_narrow]
    simp only [hseed_len, Nat.zero_add]
  have hseed_gap : ∀ z ∈ seed, gap z = h := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hzeq := hseed_mem z.2 (mem_indexPairs hz).2.2
    simp [gap, hzeq]
  have hseed_sum : (∑ z ∈ seed, gap z) = seed_count * h := by
    calc (∑ z ∈ seed, gap z) = ∑ _z ∈ seed, h := Finset.sum_congr rfl hseed_gap
      _ = seed.card * h := by simp
      _ = seed_count * h := by rw [hseed_card]
  have hlabels_nodup : labels_step.Nodup := indexPairs_nodup seed_count chain_narrow
  have hlabels_fresh : ∀ z ∈ labels_step, z ∉ seed := by
    intro z hzl hzs
    rw [List.mem_toFinset] at hzs
    have h1 := (mem_indexPairs hzl).1
    have h2 := (mem_indexPairs hzs).2.1
    rw [hseed_len] at h2
    omega
  have hchain_step : StepGapChain gap h (∑ z ∈ seed, gap z) labels_step := by
    rw [hseed_sum]
    exact indexPairs_stepGapChain seed_count h (seed_count * h) chain_narrow hchain_narrow
  have hgrid_step0 :=
    t75_uniform_seed_extend gap h seed labels_step hh_pos hseed_gap hlabels_nodup hlabels_fresh hchain_step
  rw [hS_step_union] at hgrid_step0
  have hlabels_sum : (labels_step.map gap).sum = (chain_narrow.map Prod.snd).sum := by
    have hmap : ∀ (s : ℕ) (xs : List (ℕ × ℕ)),
        ((indexPairs s xs).map gap) = xs.map Prod.snd := by
      intro s xs
      induction xs generalizing s with
      | nil => rfl
      | cons x xs ih => simp [indexPairs, gap, ih (s + 1)]
    rw [hmap]
  have hS_step_sum : (∑ z ∈ S_step, gap z) = R_step := by
    have hdisj_sl : Disjoint seed labels_step.toFinset := by
      rw [Finset.disjoint_right]
      intro z hzl
      exact hlabels_fresh z (List.mem_toFinset.mp hzl)
    rw [← hS_step_union, Finset.sum_union hdisj_sl, hseed_sum,
      List.sum_toFinset _ hlabels_nodup, hlabels_sum]
  have hgrid_step : CompleteStepGrid S_step gap (2 * h0) R_step := by
    rwa [hS_step_sum] at hgrid_step0
  have hmem_S_step : ∀ z ∈ S_step,
      z.1 < seed_count + chain_narrow.length ∧
      (z.2 = (r0, h) ∨ z.2 ∈ chain_narrow) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    have hm := mem_indexPairs hz
    rw [List.length_append, hseed_len, Nat.zero_add] at hm
    rcases List.mem_append.mp hm.2.2 with hm1 | hm2
    · exact ⟨hm.2.1, Or.inl (hseed_mem z.2 hm1)⟩
    · exact ⟨hm.2.1, Or.inr hm2⟩
  -- Modulo-`h0` cover `S_mod`
  let P_step : ℕ := seed_count + chain_narrow.length
  let P_pred : ℕ → ℕ → Prop := fun u g =>
    Nat.Prime u ∧ Odd u ∧ Nat.Prime (u + g) ∧ Odd (u + g) ∧
      y - D / 2 ≤ (u : ℝ) ∧ ((u + g : ℕ) : ℝ) ≤ y + D / 2 ∧ (g : ℝ) ≤ D / 2
  obtain ⟨S_mod, A_mod, hS_mod_card, hS_mod_mem, hS_mod_ach, hA_mod_card⟩ :=
    exists_indexed_mod_cover hh0 P_pred P_step hmod_supply (h0 - 1) (le_refl _)
  obtain ⟨hmod_even, hmod_cover⟩ := modAchievable_full_cover hS_mod_ach (by omega)
  have hdisj_step_mod : Disjoint S_step S_mod := by
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 := (hmem_S_step z hz1).1
    have h2 := (hS_mod_mem z hz2).1
    dsimp [P_step] at h2
    omega
  let R_mod : ℕ := ∑ z ∈ S_mod, gap z
  have hR_mod_le : (R_mod : ℝ) ≤ (H0 : ℝ) * (D / 2) := by
    have hsum_le : (R_mod : ℝ) ≤ ∑ _z ∈ S_mod, (D / 2) := by
      dsimp [R_mod]
      push_cast
      exact Finset.sum_le_sum (fun z hz => (hS_mod_mem z hz).2.2.1.2.2.2.2.2.2)
    rw [Finset.sum_const, nsmul_eq_mul, hS_mod_card] at hsum_le
    have hh0_H0 : ((h0 - 1 : ℕ) : ℝ) ≤ (H0 : ℝ) := by exact_mod_cast (by omega : h0 - 1 ≤ H0)
    exact hsum_le.trans (mul_le_mul_of_nonneg_right hh0_H0 (by positivity))
  let narrow : Finset (ℕ × (ℕ × ℕ)) := S_step ∪ S_mod
  have hgrid_narrow : EvenIntervalGrid narrow gap R_mod R_step :=
    evenIntervalGrid_of_stepGrid_and_modCover S_step S_mod gap h0 R_mod R_step hh0
      hdisj_step_mod hgrid_step hmod_even (le_refl _) hmod_cover
  have hR_step_even : 2 ∣ R_step := by
    rw [← hS_step_sum]
    apply Finset.dvd_sum
    intro z hz
    rcases (hmem_S_step z hz).2 with hzeq | hch
    · simp only [gap, hzeq]
      exact ⟨h0, rfl⟩
    · obtain ⟨_, _, _, hdvd_h⟩ := hmem_narrow z.2 hch
      exact dvd_trans ⟨h0, rfl⟩ hdvd_h
  -- Wide extension `wide`
  have hplo_le_phi : p_lo ≤ p_hi := by
    have : (p_lo : ℝ) ≤ (p_hi : ℝ) := by linarith [hplo.2.2.2, hphi.2.2.1]
    exact_mod_cast this
  let dw : ℕ := p_hi - p_lo
  have hdw_even : 2 ∣ dw := by
    obtain ⟨k1, hk1⟩ := hplo.2.1
    obtain ⟨k2, hk2⟩ := hphi.2.1
    refine ⟨k2 - k1, ?_⟩
    omega
  have hdw_bounds : D ≤ (dw : ℝ) ∧ (dw : ℝ) ≤ 2 * D := by
    have hcast : (dw : ℝ) = (p_hi : ℝ) - (p_lo : ℝ) := Nat.cast_sub hplo_le_phi
    exact ⟨by linarith [hplo.2.2.2, hphi.2.2.1], by linarith [hplo.2.2.1, hphi.2.2.2]⟩
  have hR_mod_dw_le : R_mod + dw ≤ R_step := by
    have hreal : ((R_mod + dw : ℕ) : ℝ) ≤ (R_step : ℝ) := by
      push_cast
      have hH6 : ((H0 + 6 : ℕ) : ℝ) * (D / 2) = (H0 : ℝ) * (D / 2) + 3 * D := by
        push_cast; ring
      linarith [hR_mod_le, hdw_bounds.2, hR_step_bound]
    exact_mod_cast hreal
  let P_narrow : ℕ := P_step + (h0 - 1)
  have hnarrow_card : narrow.card = P_narrow := by
    rw [Finset.card_union_of_disjoint hdisj_step_mod, hS_step_card, hS_mod_card]
  let W : ℕ := P_narrow + H0 + 4
  obtain ⟨wide_list, hwide_len, hwide_mem, _, _⟩ :=
    exists_replicate_chain 2 R_step W (p_lo, dw) hdw_even (by dsimp; omega)
  let wide : Finset (ℕ × (ℕ × ℕ)) := (indexPairs P_narrow wide_list).toFinset
  have hwide_card : wide.card = W := by
    change (indexPairs P_narrow wide_list).toFinset.card = W
    rw [indexPairs_toFinset_card, hwide_len]
  have hdisj_nw : Disjoint narrow wide := by
    rw [Finset.disjoint_left]
    intro z hzn hzw
    rw [List.mem_toFinset] at hzw
    have hw_idx := (mem_indexPairs hzw).1
    rcases Finset.mem_union.mp hzn with hzs | hzm
    · have hs_idx := (hmem_S_step z hzs).1
      dsimp [P_narrow, P_step] at hw_idx
      omega
    · have hm_idx := (hS_mod_mem z hzm).2.1
      dsimp [P_narrow] at hw_idx
      omega
  have hwide_pair : ∀ z ∈ wide, z.2 = (p_lo, dw) := by
    intro z hz
    rw [List.mem_toFinset] at hz
    exact hwide_mem z.2 (mem_indexPairs hz).2.2
  have hwide_grid_cond : ∀ z ∈ wide, 2 ∣ gap z ∧ gap z ≤ R_step - R_mod + 2 := by
    intro z hz
    have hzeq := hwide_pair z hz
    simp only [gap, hzeq]
    exact ⟨hdw_even, by omega⟩
  have hgrid_full := (evenIntervalGrid_extend_finset narrow wide gap R_mod R_step
    hR_step_even (by omega) hdisj_nw hwide_grid_cond hgrid_narrow).1
  let S := narrow ∪ wide
  let B : ℕ := R_step + ∑ z ∈ wide, gap z
  have hS_card : S.card = 2 * P_narrow + H0 + 4 := by
    rw [Finset.card_union_of_disjoint hdisj_nw, hnarrow_card, hwide_card]
    dsimp [W]; omega
  have hS_le_n : S.card ≤ n := by
    have hch_len : chain_narrow.length = ch1.length + top_count := by
      simp [chain_narrow, top]
    have hPn_le : P_narrow ≤ 2 * C + 4 * C * k + (H0 + 6) * C + H0 := by
      dsimp [P_narrow, P_step, seed_count]
      rw [hch_len]
      dsimp [top_count]
      omega
    omega
  let m : ℕ := n - S.card
  have hlen : m + S.card = n := by omega
  have hnarrow_props : ∀ z ∈ narrow,
      (Nat.Prime (low z) ∧ Odd (low z) ∧ Nat.Prime (low z + gap z) ∧ Odd (low z + gap z)) ∧
      (y - D / 2 ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D / 2) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzs | hzm
    · rcases (hmem_S_step z hzs).2 with hzeq | hch
      · simp only [low, gap, hzeq]
        exact ⟨⟨hr0.1, hr0.2.1, hr0.2.2.1, hr0.2.2.2⟩, hr0_int⟩
      · obtain ⟨hp1, hp2, _, _⟩ := hmem_narrow z.2 hch
        exact ⟨⟨(hA_prime _ hp1).1, (hA_prime _ hp1).2, (hA_prime _ hp2).1, (hA_prime _ hp2).2⟩,
          ⟨(hA_int _ hp1).1, (hA_int _ hp2).2⟩⟩
    · have hm := (hS_mod_mem z hzm).2.2.1
      exact ⟨⟨hm.1, hm.2.1, hm.2.2.1, hm.2.2.2.1⟩, ⟨hm.2.2.2.2.1, hm.2.2.2.2.2.1⟩⟩
  have hS_prime : ∀ z ∈ S, Nat.Prime (low z) ∧ Odd (low z) ∧
      Nat.Prime (low z + gap z) ∧ Odd (low z + gap z) := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · exact (hnarrow_props z hzn).1
    · have hzeq := hwide_pair z hzw
      simp only [low, gap, hzeq]
      have : p_lo + dw = p_hi := by omega
      rw [this]
      exact ⟨hplo.1, hplo.2.1, hphi.1, hphi.2.1⟩
  have hS_win : ∀ z ∈ S, y - D ≤ (low z : ℝ) ∧ ((low z + gap z : ℕ) : ℝ) ≤ y + D := by
    intro z hz
    rcases Finset.mem_union.mp hz with hzn | hzw
    · have hw := (hnarrow_props z hzn).2
      exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
    · have hzeq := hwide_pair z hzw
      simp only [low, gap, hzeq]
      have : p_lo + dw = p_hi := by omega
      rw [this]
      exact ⟨hplo.2.2.1, hphi.2.2.2⟩
  -- Margin inequalities `hmargin_lo` and `hmargin_hi`
  have hlow_narrow : ((∑ z ∈ narrow, low z : ℕ) : ℝ) ≤ (narrow.card : ℝ) * (y + D / 2) := by
    calc ((∑ z ∈ narrow, low z : ℕ) : ℝ)
        = ∑ z ∈ narrow, (low z : ℝ) := by push_cast; rfl
      _ ≤ ∑ _z ∈ narrow, (y + D / 2) := by
          apply Finset.sum_le_sum
          intro z hz
          have hw := (hnarrow_props z hz).2
          have hle : (low z : ℝ) ≤ ((low z + gap z : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_add_right (low z) (gap z)
          linarith
      _ = (narrow.card : ℝ) * (y + D / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hlow_wide : ((∑ z ∈ wide, low z : ℕ) : ℝ) ≤ (wide.card : ℝ) * (y - D / 2) := by
    calc ((∑ z ∈ wide, low z : ℕ) : ℝ)
        = ∑ z ∈ wide, (low z : ℝ) := by push_cast; rfl
      _ ≤ ∑ _z ∈ wide, (y - D / 2) := by
          apply Finset.sum_le_sum
          intro z hz
          have hzeq := hwide_pair z hz
          simp only [low, hzeq]
          exact hplo.2.2.2
      _ = (wide.card : ℝ) * (y - D / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hsplit_card : (S.card : ℝ) = (narrow.card : ℝ) + (wide.card : ℝ) := by
    dsimp [S]
    rw [Finset.card_union_of_disjoint hdisj_nw, Nat.cast_add]
  have hsplit_y : (S.card : ℝ) * y = (narrow.card : ℝ) * y + (wide.card : ℝ) * y := by
    rw [hsplit_card, add_mul]
  have hdiff_card : (wide.card : ℝ) - (narrow.card : ℝ) = (H0 : ℝ) + 4 := by
    rw [hnarrow_card, hwide_card]
    dsimp [W]
    push_cast; ring
  have hdiff_D : ((wide.card : ℝ) - (narrow.card : ℝ)) * (D / 2) = ((H0 : ℝ) + 4) * (D / 2) := by
    rw [hdiff_card]
  have hmargin_lo : (R_mod : ℝ) + D ≤ (S.card : ℝ) * y - ((∑ z ∈ S, low z : ℕ) : ℝ) := by
    have hsplit_sum : ((∑ z ∈ S, low z : ℕ) : ℝ) =
        ((∑ z ∈ narrow, low z : ℕ) : ℝ) + ((∑ z ∈ wide, low z : ℕ) : ℝ) := by
      dsimp [S]
      rw [Finset.sum_union hdisj_nw, Nat.cast_add]
    linarith [hlow_narrow, hlow_wide, hR_mod_le, hsplit_y, hdiff_D]
  have hhigh_narrow : (narrow.card : ℝ) * (y - D / 2) ≤
      ((∑ z ∈ narrow, (low z + gap z) : ℕ) : ℝ) := by
    calc (narrow.card : ℝ) * (y - D / 2)
        = ∑ _z ∈ narrow, (y - D / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ narrow, ((low z + gap z : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro z hz
          have hw := (hnarrow_props z hz).2
          have hle : (low z : ℝ) ≤ ((low z + gap z : ℕ) : ℝ) := by
            exact_mod_cast Nat.le_add_right (low z) (gap z)
          linarith
      _ = ((∑ z ∈ narrow, (low z + gap z) : ℕ) : ℝ) := by push_cast; rfl
  have hhigh_wide : (wide.card : ℝ) * (y + D / 2) ≤
      ((∑ z ∈ wide, (low z + gap z) : ℕ) : ℝ) := by
    calc (wide.card : ℝ) * (y + D / 2)
        = ∑ _z ∈ wide, (y + D / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ wide, ((low z + gap z : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro z hz
          have hzeq := hwide_pair z hz
          simp only [low, gap, hzeq]
          have : p_lo + dw = p_hi := by omega
          rw [this]
          exact hphi.2.2.1
      _ = ((∑ z ∈ wide, (low z + gap z) : ℕ) : ℝ) := by push_cast; rfl
  have hmargin_hi : (S.card : ℝ) * y - ((∑ z ∈ S, low z : ℕ) : ℝ) + D ≤ (B : ℝ) := by
    have hB_eq : B + R_mod = ∑ z ∈ S, gap z := by
      dsimp [B, R_mod, S, narrow]
      rw [Finset.sum_union hdisj_nw, Finset.sum_union hdisj_step_mod, hS_step_sum]
      omega
    have hsum_lg : (∑ z ∈ S, low z) + (∑ z ∈ S, gap z) = ∑ z ∈ S, (low z + gap z) :=
      Finset.sum_add_distrib.symm
    have hsplit_lg : ((∑ z ∈ S, (low z + gap z) : ℕ) : ℝ) =
        ((∑ z ∈ narrow, (low z + gap z) : ℕ) : ℝ) + ((∑ z ∈ wide, (low z + gap z) : ℕ) : ℝ) := by
      dsimp [S]
      rw [Finset.sum_union hdisj_nw, Nat.cast_add]
    have hB_real : (B : ℝ) + (R_mod : ℝ) = ((∑ z ∈ S, gap z : ℕ) : ℝ) := by exact_mod_cast hB_eq
    have hlg_real : ((∑ z ∈ S, low z : ℕ) : ℝ) + ((∑ z ∈ S, gap z : ℕ) : ℝ) =
        ((∑ z ∈ S, (low z + gap z) : ℕ) : ℝ) := by exact_mod_cast hsum_lg
    linarith [hhigh_narrow, hhigh_wide, hR_mod_le, hsplit_y, hdiff_D]
  exact t75_targets_of_evenIntervalGrid hn_pos hn p_lo p_hi S low gap R_mod B y D hy hD_pos.le
    hlen ⟨hplo.1, hplo.2.1, hplo.2.2.1, by linarith [hplo.2.2.2]⟩
    ⟨hphi.1, hphi.2.1, by linarith [hphi.2.2.1], hphi.2.2.2⟩
    hS_prime hS_win hgrid_full hmargin_lo hmargin_hi

/-! ## Section 3: Unbounded Upper-Tail T75 Target Supply (`n ≥ 35,735`) -/

/-- For every odd `n ≥ 35,735` (unbounded above), there exists a prime target vector
`f : Fin n → ℕ` of exact sum `Lucas.poolTotal n` with `|(f i : ℝ) - y| ≤ y / 400`. -/
theorem upper_tail_t75_targets
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (rs : RSPrimeCountImports)
    (hMV : MVBrunTitchmarsh) (sharp : RSIndexLowerSharp) (hRS_hi : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) (hn_odd : Odd n) :
    let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let D : ℝ := y / 400
    ∃ f : Fin n → ℕ,
      (∑ i, f i) = Lucas.poolTotal n ∧
      (∀ i, Nat.Prime (f i) ∧ Odd (f i) ∧ |(f i : ℝ) - y| ≤ D) := by
  dsimp only
  have hn_pos : 0 < n := by omega
  let Xnat := poolMaximum n
  let X : ℝ := Xnat
  let y : ℝ := (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue
  let D : ℝ := y / 400
  obtain ⟨hX_lo_n2, hX_gt_283, hX_lt_n3, hlogX_gt, hlogX_lt⟩ :=
    poolMaximum_bounds_ge_35735 sharp hRS_hi hn
  obtain ⟨hlogn_gt, hlogn3, hlogn4⟩ := log_nat_pow_bounds_ge_35735 hn
  have hXpos : 0 < X := by linarith
  have hm_bounds := global_pool_mean_bounds rs sharp (by omega : 2001 ≤ n)
  have hm_lo : (449 / 1000 : ℝ) * X < centralEntriesMean (prescribedPoolValues n) centralPoolValue := by
    rw [prescribedPoolValues_mean]
    exact (lt_div_iff₀ hXpos).mp hm_bounds.1
  have hm_hi : centralEntriesMean (prescribedPoolValues n) centralPoolValue < (519 / 1000 : ℝ) * X := by
    rw [prescribedPoolValues_mean]
    exact (div_lt_iff₀ hXpos).mp hm_bounds.2
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hy_lo : (35735 : ℝ) * ((449 / 1000 : ℝ) * (283 * 10 ^ 8 : ℝ)) ≤ y := by
    have hm1 : (449 / 1000 : ℝ) * (283 * 10 ^ 8 : ℝ) ≤
        centralEntriesMean (prescribedPoolValues n) centralPoolValue := by linarith
    dsimp [y]
    exact mul_le_mul hnR hm1 (by positivity) hn_nonneg
  have hy_gt : (45 * 10 ^ 13 : ℝ) < y := by linarith
  have hD_gt : (10 ^ 12 : ℝ) < D := by dsimp [D]; linarith
  have hD_pos : 0 < D := by linarith
  have hy_eq : y = 400 * D := by dsimp [D]; ring
  have hyD_lt_n4 : y + D < (n : ℝ) ^ 4 := by
    have hy1 : y < (n : ℝ) * ((519 / 1000 : ℝ) * X) := by
      dsimp [y]
      exact mul_lt_mul_of_pos_left hm_hi (by linarith)
    have hy2 : (n : ℝ) * ((519 / 1000 : ℝ) * X) < (n : ℝ) * ((519 / 1000 : ℝ) * (n : ℝ) ^ 3) :=
      mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hX_lt_n3 (by norm_num)) (by linarith)
    have hy3 : (n : ℝ) * ((519 / 1000 : ℝ) * (n : ℝ) ^ 3) = (519 / 1000 : ℝ) * (n : ℝ) ^ 4 := by ring
    have hn4_pos : 0 < (n : ℝ) ^ 4 := by positivity
    dsimp [D]
    linarith
  have hlog_yD : Real.log (y + D) ≤ 4 * Real.log (n : ℝ) := by
    have h1 := Real.log_le_log (by linarith) hyD_lt_n4.le
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  -- Parameters `Ln`, `C`, `H0`, `k`
  let Ln : ℕ := ⌈Real.log (n : ℝ)⌉₊
  have hLn_ge : Real.log (n : ℝ) ≤ (Ln : ℝ) := Nat.le_ceil _
  have hLn_lt : (Ln : ℝ) < Real.log (n : ℝ) + 1 := Nat.ceil_lt_add_one (by linarith)
  have hLn_11 : 11 ≤ Ln := by
    have : (10 : ℝ) < (Ln : ℝ) := lt_of_lt_of_le hlogn_gt hLn_ge
    exact_mod_cast this
  have hLn_ratio : (Ln : ℝ) ≤ (11 / 10 : ℝ) * Real.log (n : ℝ) := by linarith
  let C : ℕ := 3 * Ln
  let H0 : ℕ := 3 * Ln
  let k : ℕ := 6 * Ln
  have hC_ge : 1 ≤ C := by omega
  have hlog_sq_100 : (100 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hlogn_gt.le hlogn_gt.le (by norm_num) (by linarith)
    linarith
  have hlog2_le : 223 * (Real.log (n : ℝ)) ^ 2 ≤ (n : ℝ) := by
    have hmul : 100 * (Real.log (n : ℝ)) ^ 2 ≤ (Real.log (n : ℝ)) ^ 4 := by
      calc 100 * (Real.log (n : ℝ)) ^ 2
          ≤ (Real.log (n : ℝ)) ^ 2 * (Real.log (n : ℝ)) ^ 2 :=
            mul_le_mul_of_nonneg_right hlog_sq_100 (sq_nonneg _)
        _ = (Real.log (n : ℝ)) ^ 4 := by ring
    linarith [hlogn4]
  have hLn2_le : (Ln : ℝ) ^ 2 ≤ (121 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hLn_ratio hLn_ratio (by positivity) (by positivity)
    linarith
  have hLn1_le : (Ln : ℝ) ≤ (11 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by
    have hm := mul_le_mul hlogn_gt.le hLn_ratio (by positivity) (by linarith)
    linarith
  have hD_ge_nX : (n : ℝ) * X ≤ 1000 * D := by
    have hm := mul_le_mul_of_nonneg_left hm_lo.le hn_nonneg
    dsimp [D, y]
    linarith
  have hnX_ge : (283 * 10 ^ 8 : ℝ) * (n : ℝ) ≤ (n : ℝ) * X := by
    have hm := mul_le_mul_of_nonneg_left hX_gt_283.le hn_nonneg
    linarith
  have hn_lt_D : 10000000 * (n : ℝ) ≤ D := by linarith
  have hsize_le : 2 * (2 * C + 4 * C * k + (H0 + 6) * C + H0) + H0 + 4 ≤ n := by
    have h1_le : (1 : ℝ) ≤ (1 / 100 : ℝ) * (Real.log (n : ℝ)) ^ 2 := by linarith
    have hreal : ((2 * (2 * C + 4 * C * k + (H0 + 6) * C + H0) + H0 + 4 : ℕ) : ℝ) ≤ (n : ℝ) := by
      dsimp [C, H0, k]
      push_cast
      linarith
    exact_mod_cast hreal
  -- Bracket / wide primes `p_lo` and `p_hi`
  obtain ⟨p_lo, hplo_prime, hplo_odd, hplo_lo, hplo_hi⟩ :=
    odd_prime_in_interval_all_scales bmor imp (lo := y - D) (hi := y - D / 2)
      (by linarith) (by linarith) (by linarith)
  obtain ⟨p_hi, hphi_prime, hphi_odd, hphi_lo, hphi_hi⟩ :=
    odd_prime_in_interval_all_scales bmor imp (lo := y + D / 2) (hi := y + D)
      (by linarith) (by linarith) (by linarith)
  -- Mid-interval odd prime pool `P_mid = apInterval (y - D/4) (y + D/4) 2 1`
  let b_mid : ℝ := y - D / 4
  let c_mid : ℝ := y + D / 4
  let P_mid := apInterval b_mid c_mid 2 1
  have hb_mid_gt : (44 * 10 ^ 13 : ℝ) < b_mid := by dsimp [b_mid]; linarith
  have hlog_b_mid_gt : 30 < Real.log b_mid := by
    have h2_48 : (2 : ℝ) ^ 48 < b_mid := by linarith
    have hlog := Real.log_lt_log (by positivity) h2_48
    rw [Real.log_pow] at hlog
    push_cast at hlog
    linarith [Real.log_two_gt_d9]
  have hlog_c_le_b : Real.log c_mid ≤ (31 / 30 : ℝ) * Real.log b_mid := by
    have hc_le_2b : c_mid ≤ 2 * b_mid := by dsimp [b_mid, c_mid]; linarith
    have hc_pos : 0 < c_mid := by dsimp [c_mid]; linarith
    have hb_ne : b_mid ≠ 0 := ne_of_gt (by linarith : 0 < b_mid)
    have h1 := Real.log_le_log hc_pos hc_le_2b
    rw [Real.log_mul (by norm_num) hb_ne] at h1
    linarith [Real.log_two_lt_d9]
  have hlog_c_le_Ln : Real.log c_mid ≤ 4 * (Ln : ℝ) := by
    have h1 : Real.log c_mid ≤ Real.log (y + D) :=
      Real.log_le_log (by dsimp [c_mid]; linarith) (by dsimp [c_mid]; linarith)
    linarith
  have hP_mid_card_log : (13 / 30 : ℝ) * D ≤ (P_mid.card : ℝ) * Real.log c_mid := by
    have h := (div_le_iff₀ (Real.log_pos (by dsimp [c_mid]; linarith))).mp
      (apInterval_mod_two_card_lower_ge_5e9 bmor imp (b := b_mid) (c := c_mid) (X := c_mid)
        (by linarith) (by dsimp [b_mid, c_mid]; linarith) (le_refl _))
    have hba : (c_mid - b_mid) - (b_mid + c_mid) / 12000 = (13 / 30 : ℝ) * D := by
      dsimp [b_mid, c_mid]; rw [hy_eq]; ring
    linarith
  have hP_mid_card_Ln : (13 / 30 : ℝ) * D ≤ (P_mid.card : ℝ) * (4 * (Ln : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_left hlog_c_le_Ln (Nat.cast_nonneg P_mid.card)
    linarith
  have hP_mid_props : ∀ p ∈ P_mid, Nat.Prime p ∧ Odd p ∧ b_mid < (p : ℝ) ∧ (p : ℝ) ≤ c_mid := by
    intro p hp
    have ⟨hp_prime, hlo, hhi, hmod⟩ :=
      (mem_apInterval_iff b_mid c_mid 2 1 (by linarith) (by dsimp [b_mid, c_mid]; linarith) p).mp hp
    have hp_odd : Odd p := by
      rw [Nat.odd_iff]
      exact_mod_cast hmod
    exact ⟨hp_prime, hp_odd, hlo, hhi⟩
  -- Seed pair `(r0, r0 + 2 * h0)` from `P_mid` via spatial bins of width `2 * H0`
  let u_nat : ℕ := ⌊b_mid⌋₊
  let K_bins : ℕ := ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ + 2
  have hbin_range : ∀ p ∈ P_mid, (p - u_nat) / (2 * H0) < K_bins := by
    intro p hp
    have hp_p := hP_mid_props p hp
    have hu_le : (u_nat : ℝ) ≤ b_mid := Nat.floor_le (by linarith)
    have hu_gt : b_mid - 1 < (u_nat : ℝ) := Nat.sub_one_lt_floor b_mid
    have hp_ge_u : u_nat ≤ p := by
      have : (u_nat : ℝ) ≤ (p : ℝ) := by linarith [hp_p.2.2.1]
      exact_mod_cast this
    have hdiff_le : ((p - u_nat : ℕ) : ℝ) ≤ D / 2 + 1 := by
      rw [Nat.cast_sub hp_ge_u]
      dsimp [b_mid, c_mid] at hp_p hu_gt
      linarith [hp_p.2.2.2]
    have h2H0_pos : (0 : ℝ) < ((2 * H0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * H0)
    have h2H0_ge_1 : (1 : ℝ) ≤ ((2 * H0 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * H0)
    let q_bin := (p - u_nat) / (2 * H0)
    have hq_mul : q_bin * (2 * H0) ≤ p - u_nat := Nat.div_mul_le_self _ _
    have hq_real : (q_bin : ℝ) * ((2 * H0 : ℕ) : ℝ) ≤ D / 2 + ((2 * H0 : ℕ) : ℝ) := by
      have hc : ((q_bin * (2 * H0) : ℕ) : ℝ) ≤ ((p - u_nat : ℕ) : ℝ) := Nat.cast_le.mpr hq_mul
      rw [Nat.cast_mul] at hc
      linarith
    have hq_div : (q_bin : ℝ) ≤ (D / 2) / ((2 * H0 : ℕ) : ℝ) + 1 := by
      rw [div_add_one h2H0_pos.ne', le_div_iff₀ h2H0_pos]
      exact hq_real
    have hq_fl : q_bin ≤ ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ + 1 := by
      have h1 : ⌊(q_bin : ℝ)⌋₊ ≤ ⌊(D / 2) / ((2 * H0 : ℕ) : ℝ) + 1⌋₊ := Nat.floor_mono hq_div
      rw [Nat.floor_natCast, Nat.floor_add_one (by positivity)] at h1
      exact h1
    dsimp [K_bins]
    omega
  have hK_lt_P_mid : K_bins < P_mid.card := by
    have hfl : ((⌊(D / 2) / ((2 * H0 : ℕ) : ℝ)⌋₊ : ℕ) : ℝ) ≤ (D / 2) / ((2 * H0 : ℕ) : ℝ) :=
      Nat.floor_le (by positivity)
    have h2H0_eq : ((2 * H0 : ℕ) : ℝ) = 6 * (Ln : ℝ) := by dsimp [H0]; push_cast; ring
    have hLn_pos : (0 : ℝ) < (Ln : ℝ) := by positivity
    have hK_real : (K_bins : ℝ) * (4 * (Ln : ℝ)) < (13 / 30 : ℝ) * D := by
      dsimp [K_bins]
      rw [h2H0_eq] at hfl ⊢
      have hm := mul_le_mul_of_nonneg_right hfl (by positivity : (0 : ℝ) ≤ 6 * (Ln : ℝ))
      rw [div_mul_cancel₀ _ (by positivity)] at hm
      have hLn_D : (Ln : ℝ) < D / 1000 := by
        linarith [hLn1_le, hlog2_le, hn_lt_D]
      push_cast
      linarith
    have hlt_mul : (K_bins : ℝ) * (4 * (Ln : ℝ)) < (P_mid.card : ℝ) * (4 * (Ln : ℝ)) :=
      lt_of_lt_of_le hK_real hP_mid_card_Ln
    have hlt_real : (K_bins : ℝ) < (P_mid.card : ℝ) :=
      lt_of_mul_lt_mul_right hlt_mul (by positivity)
    exact_mod_cast hlt_real
  obtain ⟨r0, hr0_mem, r1, hr1_mem, hr0_lt_r1, hsame_bin⟩ :=
    exists_same_bin_pair_of_lt_card hbin_range hK_lt_P_mid
  have hr0_props := hP_mid_props r0 hr0_mem
  have hr1_props := hP_mid_props r1 hr1_mem
  have hu_le_r0 : u_nat ≤ r0 := by
    have hu_le : (u_nat : ℝ) ≤ b_mid := Nat.floor_le (by linarith)
    have : (u_nat : ℝ) ≤ (r0 : ℝ) := by linarith [hr0_props.2.2.1]
    exact_mod_cast this
  have hr1_sub_r0_lt : r1 - r0 < 2 * H0 := by
    let B := 2 * H0
    have hB_pos : 0 < B := by dsimp [B, H0]; omega
    have hd0 := Nat.div_add_mod (r0 - u_nat) B
    have hd1 := Nat.div_add_mod (r1 - u_nat) B
    have hmul_eq : B * ((r0 - u_nat) / B) = B * ((r1 - u_nat) / B) :=
      congrArg (B * ·) hsame_bin
    have hm0 : (r0 - u_nat) % B < B := Nat.mod_lt _ hB_pos
    have hm1 : (r1 - u_nat) % B < B := Nat.mod_lt _ hB_pos
    have hsub_eq : (r1 - r0) + (r0 - u_nat) = r1 - u_nat := by omega
    omega
  have hr1_sub_r0_even : 2 ∣ (r1 - r0) := by
    obtain ⟨m0, hm0⟩ := hr0_props.2.1
    obtain ⟨m1, hm1⟩ := hr1_props.2.1
    refine ⟨m1 - m0, ?_⟩
    omega
  let h0 : ℕ := (r1 - r0) / 2
  have hh0_pos : 0 < h0 := by
    obtain ⟨m, hm⟩ := hr1_sub_r0_even
    omega
  have hh0_le : h0 ≤ H0 := by omega
  have hr1_eq : r0 + 2 * h0 = r1 := by
    obtain ⟨m, hm⟩ := hr1_sub_r0_even
    dsimp [h0]; omega
  -- Central prime set `A ⊆ P_central` in a single residue class `b` modulo `2 * h0`
  let b_cen : ℝ := y - D / 2
  let c_cen : ℝ := y + D / 2
  let P_cen := apInterval b_cen c_cen 2 1
  have hP_cen_props : ∀ p ∈ P_cen, Nat.Prime p ∧ Odd p ∧ b_cen < (p : ℝ) ∧ (p : ℝ) ≤ c_cen := by
    intro p hp
    have ⟨hp_prime, hlo, hhi, hmod⟩ :=
      (mem_apInterval_iff b_cen c_cen 2 1 (by dsimp [b_cen]; linarith)
        (by dsimp [b_cen, c_cen]; linarith) p).mp hp
    have hp_odd : Odd p := by rw [Nat.odd_iff]; exact_mod_cast hmod
    exact ⟨hp_prime, hp_odd, hlo, hhi⟩
  have hP_cen_card_Ln : (14 / 15 : ℝ) * D ≤ (P_cen.card : ℝ) * (4 * (Ln : ℝ)) := by
    have h := (div_le_iff₀ (Real.log_pos (by dsimp [c_cen]; linarith))).mp
      (apInterval_mod_two_card_lower_ge_5e9 bmor imp (b := b_cen) (c := c_cen) (X := c_cen)
        (by dsimp [b_cen]; linarith) (by dsimp [b_cen, c_cen]; linarith) (le_refl _))
    have hba : (c_cen - b_cen) - (b_cen + c_cen) / 12000 = (14 / 15 : ℝ) * D := by
      dsimp [b_cen, c_cen]; rw [hy_eq]; ring
    have hlog_cen : Real.log c_cen ≤ 4 * (Ln : ℝ) := by
      have h1 : Real.log c_cen ≤ Real.log (y + D) :=
        Real.log_le_log (by dsimp [c_cen]; linarith) (by dsimp [c_cen]; linarith)
      linarith
    have hm := mul_le_mul_of_nonneg_left hlog_cen (Nat.cast_nonneg P_cen.card)
    linarith
  obtain ⟨b_res, _, hA_fiber_card⟩ :=
    exists_odd_residue_fiber_ge P_cen h0 hh0_pos (fun p hp => (hP_cen_props p hp).2.1)
  let A := P_cen.filter (fun p => p % (2 * h0) = b_res)
  have hA_prime : ∀ p ∈ A, Nat.Prime p ∧ Odd p := by
    intro p hp
    have hp_cen := hP_cen_props p (Finset.mem_filter.mp hp).1
    exact ⟨hp_cen.1, hp_cen.2.1⟩
  have hA_int : ∀ p ∈ A, y - D / 2 ≤ (p : ℝ) ∧ (p : ℝ) ≤ y + D / 2 := by
    intro p hp
    have hp_cen := hP_cen_props p (Finset.mem_filter.mp hp).1
    exact ⟨hp_cen.2.2.1.le, hp_cen.2.2.2⟩
  have hA_mod : ∀ p ∈ A, p % (2 * h0) = b_res :=
    fun p hp => (Finset.mem_filter.mp hp).2
  have hA_card : D < (C : ℝ) * ((2 * h0 : ℕ) : ℝ) * (A.card : ℝ) := by
    have h2_mul : 2 * P_cen.card ≤ (2 * h0) * A.card := by
      calc 2 * P_cen.card
          ≤ 2 * (h0 * A.card) := Nat.mul_le_mul_left 2 hA_fiber_card
        _ = (2 * h0) * A.card := (Nat.mul_assoc 2 h0 A.card).symm
    have h2_real : 2 * (P_cen.card : ℝ) ≤ ((2 * h0 : ℕ) : ℝ) * (A.card : ℝ) := by
      have hc : ((2 * P_cen.card : ℕ) : ℝ) ≤ (((2 * h0) * A.card : ℕ) : ℝ) :=
        Nat.cast_le.mpr h2_mul
      push_cast at hc ⊢
      exact hc
    have hm := mul_le_mul_of_nonneg_left h2_real (Nat.cast_nonneg C)
    dsimp [C] at hm ⊢
    push_cast at hm ⊢
    linarith [hP_cen_card_Ln]
  have hA_card_ge : 2 ≤ A.card := by
    have h2h0_le : ((2 * h0 : ℕ) : ℝ) ≤ 6 * (Ln : ℝ) := by
      have h6 : 2 * h0 ≤ 6 * Ln := by dsimp [H0] at hh0_le; omega
      exact_mod_cast h6
    have hLn_D : 36 * (Ln : ℝ) ^ 2 < D := by
      linarith [hLn2_le, hlog2_le, hn_lt_D]
    have hprod_le : (C : ℝ) * ((2 * h0 : ℕ) : ℝ) ≤ 18 * (Ln : ℝ) ^ 2 := by
      have hm := mul_le_mul_of_nonneg_left h2h0_le (Nat.cast_nonneg C)
      dsimp [C] at hm ⊢
      push_cast at hm ⊢
      linarith
    have hmul_A := mul_le_mul_of_nonneg_right hprod_le (Nat.cast_nonneg A.card)
    have hlt2 : 18 * (Ln : ℝ) ^ 2 * 2 < 18 * (Ln : ℝ) ^ 2 * (A.card : ℝ) := by
      linarith [hA_card, hLn_D, hmul_A]
    have hreal : (2 : ℝ) < (A.card : ℝ) :=
      lt_of_mul_lt_mul_left hlt2 (by positivity)
    exact (Nat.cast_lt.mp hreal).le
  -- Upper bound `D < 2 * C * (2 * h0) * 2 ^ k`
  have hD_upper : D < ((2 * C * (2 * h0) * 2 ^ k : ℕ) : ℝ) := by
    have hlog_lt : Real.log (y + D) < Real.log ((2 : ℝ) ^ k) := by
      rw [Real.log_pow]
      dsimp [k]
      push_cast
      have hlog2_lo : (693 / 1000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hLn_pos : (0 : ℝ) < (Ln : ℝ) := by exact_mod_cast (by omega : 0 < Ln)
      have hm := mul_lt_mul_of_pos_left hlog2_lo (by positivity : (0 : ℝ) < 6 * (Ln : ℝ))
      linarith [hlog_yD, hLn_ge, hlogn_gt]
    have hyD_lt_2k : y + D < (2 : ℝ) ^ k :=
      (Real.log_lt_log_iff (by linarith) (by positivity)).mp hlog_lt
    have h1_le : (1 : ℝ) ≤ ((2 * C * (2 * h0) : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos (by omega : 0 < 2 * C) (by omega : 0 < 2 * h0)
    have h2k_le : (2 : ℝ) ^ k ≤ ((2 * C * (2 * h0) * 2 ^ k : ℕ) : ℝ) := by
      have hm := mul_le_mul_of_nonneg_right h1_le (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      push_cast at hm ⊢
      linarith
    linarith
  -- Modulo-`h0` cover supply from `P_mid`
  have hmod_supply : ∀ p : ℕ, Nat.Prime p → p ∣ h0 →
      ∃ u g : ℕ,
        (Nat.Prime u ∧ Odd u ∧ Nat.Prime (u + g) ∧ Odd (u + g) ∧
          y - D / 2 ≤ (u : ℝ) ∧ ((u + g : ℕ) : ℝ) ≤ y + D / 2 ∧ (g : ℝ) ≤ D / 2) ∧
        2 ∣ g ∧ ¬ (p ∣ g / 2) := by
    intro p hp_prime hp_dvd
    have hp_le_h0 : p ≤ h0 := Nat.le_of_dvd hh0_pos hp_dvd
    have hp_le_H0 : p ≤ H0 := hp_le_h0.trans hh0_le
    have hp_real : (p : ℝ) ≤ 3 * (Ln : ℝ) := by dsimp [H0] at hp_le_H0; exact_mod_cast hp_le_H0
    have hp_pos_real : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp_prime.pos
    have hexp_cond : Real.exp ((3 / 5 : ℝ) * Real.log b_mid) ≤ (c_mid - b_mid) / (2 * (p : ℝ)) := by
      have hba : c_mid - b_mid = D / 2 := by dsimp [b_mid, c_mid]; ring
      rw [hba]
      apply exp_three_fifths_log_le_of_pow (by linarith) (by positivity)
      have hb_le_nX : b_mid ≤ (3 / 5 : ℝ) * ((n : ℝ) * X) := by
        have hy_hi : y ≤ (519 / 1000 : ℝ) * ((n : ℝ) * X) := by
          have hm := mul_le_mul_of_nonneg_left hm_hi.le hn_nonneg
          dsimp [y]; linarith
        dsimp [b_mid]; linarith [hD_pos]
      have hb3 : b_mid ^ 3 ≤ (27 / 125 : ℝ) * ((n : ℝ) * X) ^ 3 := by
        have hp3 := pow_le_pow_left₀ (by linarith) hb_le_nX 3
        linarith [show ((3 / 5 : ℝ) * ((n : ℝ) * X)) ^ 3 = (27 / 125 : ℝ) * ((n : ℝ) * X) ^ 3 by ring]
      have hLn3_le : (Ln : ℝ) ^ 3 ≤ (1 / 18 : ℝ) * (n : ℝ) := by
        have hp3 := pow_le_pow_left₀ (by positivity) hLn_ratio 3
        have hc : ((11 / 10 : ℝ) * Real.log (n : ℝ)) ^ 3 = (1331 / 1000 : ℝ) * (Real.log (n : ℝ)) ^ 3 := by ring
        linarith [hlogn3]
      have hLn6_le : (Ln : ℝ) ^ 6 ≤ (1 / 324 : ℝ) * (n : ℝ) ^ 2 := by
        have hp2 := pow_le_pow_left₀ (by positivity) hLn3_le 2
        linarith [show ((Ln : ℝ) ^ 3) ^ 2 = (Ln : ℝ) ^ 6 by ring,
                  show ((1 / 18 : ℝ) * (n : ℝ)) ^ 2 = (1 / 324 : ℝ) * (n : ℝ) ^ 2 by ring]
      have hLn5_le : (Ln : ℝ) ^ 5 ≤ (1 / 324 : ℝ) * (n : ℝ) ^ 2 := by
        have hLn1 : (1 : ℝ) ≤ (Ln : ℝ) := by exact_mod_cast (by omega : 1 ≤ Ln)
        have hm := mul_le_mul_of_nonneg_left hLn1 (by positivity : (0 : ℝ) ≤ (Ln : ℝ) ^ 5)
        linarith [show (Ln : ℝ) ^ 5 * (Ln : ℝ) = (Ln : ℝ) ^ 6 by ring]
      have hD2_ge : ((n : ℝ) * X) / 2000 ≤ D / 2 := by linarith [hD_ge_nX]
      have h2p_pos : (0 : ℝ) < 2 * (p : ℝ) := by exact_mod_cast Nat.mul_pos (by decide) hp_prime.pos
      have h2p_le : 2 * (p : ℝ) ≤ 6 * (Ln : ℝ) := by linarith [hp_real]
      have hquot_ge : ((n : ℝ) * X) / (12000 * (Ln : ℝ)) ≤ (D / 2) / (2 * (p : ℝ)) := by
        have h1 : (D / 2) / (6 * (Ln : ℝ)) ≤ (D / 2) / (2 * (p : ℝ)) :=
          div_le_div_of_nonneg_left (by positivity) h2p_pos h2p_le
        have h2 : (((n : ℝ) * X) / 2000) / (6 * (Ln : ℝ)) ≤ (D / 2) / (6 * (Ln : ℝ)) :=
          div_le_div_of_nonneg_right hD2_ge (by positivity)
        have heq : (((n : ℝ) * X) / 2000) / (6 * (Ln : ℝ)) = ((n : ℝ) * X) / (12000 * (Ln : ℝ)) := by ring
        linarith
      have hquot5 : (((n : ℝ) * X) / (12000 * (Ln : ℝ))) ^ 5 ≤ ((D / 2) / (2 * (p : ℝ))) ^ 5 :=
        pow_le_pow_left₀ (by positivity) hquot_ge 5
      have hX2_ge : (283 * 10 ^ 8 : ℝ) ^ 2 ≤ X ^ 2 :=
        pow_le_pow_left₀ (by norm_num) hX_gt_283.le 2
      have hnX2_ge : (283 * 10 ^ 8 : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤ ((n : ℝ) * X) ^ 2 := by
        have hm := mul_le_mul_of_nonneg_right hX2_ge (sq_nonneg (n : ℝ))
        linarith [show X ^ 2 * (n : ℝ) ^ 2 = ((n : ℝ) * X) ^ 2 by ring]
      have hkey : (27 / 125 : ℝ) * (12000 * (Ln : ℝ)) ^ 5 ≤ ((n : ℝ) * X) ^ 2 := by
        have hc : (27 / 125 : ℝ) * (12000 * (Ln : ℝ)) ^ 5 =
            ((27 / 125 : ℝ) * 12000 ^ 5) * (Ln : ℝ) ^ 5 := by ring
        have hm := mul_le_mul_of_nonneg_left hLn5_le (by norm_num : (0 : ℝ) ≤ (27 / 125 : ℝ) * 12000 ^ 5)
        have hnum : ((27 / 125 : ℝ) * 12000 ^ 5) * (1 / 324 : ℝ) ≤ (283 * 10 ^ 8 : ℝ) ^ 2 := by norm_num
        have hm2 := mul_le_mul_of_nonneg_right hnum (sq_nonneg (n : ℝ))
        linarith
      have hmul_key := mul_le_mul_of_nonneg_right hkey (by positivity : (0 : ℝ) ≤ ((n : ℝ) * X) ^ 3)
      have hden_pos : (0 : ℝ) < (12000 * (Ln : ℝ)) ^ 5 := by positivity
      have hmid5 : (27 / 125 : ℝ) * ((n : ℝ) * X) ^ 3 ≤ (((n : ℝ) * X) / (12000 * (Ln : ℝ))) ^ 5 := by
        rw [div_pow, le_div_iff₀ hden_pos]
        linarith [show ((n : ℝ) * X) ^ 2 * ((n : ℝ) * X) ^ 3 = ((n : ℝ) * X) ^ 5 by ring,
                  show (27 / 125 : ℝ) * ((n : ℝ) * X) ^ 3 * (12000 * (Ln : ℝ)) ^ 5 =
                    (27 / 125 : ℝ) * (12000 * (Ln : ℝ)) ^ 5 * ((n : ℝ) * X) ^ 3 by ring]
      exact hb3.trans (hmid5.trans hquot5)
    have hfilter_lt : ∀ c : ℕ, (P_mid.filter (fun x => x % (2 * p) = c)).card < P_mid.card := by
      intro c
      have hp_lt_b : (p : ℝ) < b_mid := by
        dsimp [b_mid]
        linarith [hp_real, hLn1_le, hlog2_le, hn_lt_D, hy_eq, hD_gt]
      have hexp_cond' : Real.exp ((3 / 5 : ℝ) * Real.log b_mid) ≤ (c_mid - b_mid) / (2 * p) := by
        simpa using hexp_cond
      have hup_div := apInterval_filter_mod_two_prime_le bmor imp hMV
        (b := b_mid) (c := c_mid) (p := p) (r := c) hp_prime
        (by linarith) (by dsimp [b_mid, c_mid]; rw [hy_eq]; linarith)
        (by dsimp [b_mid, c_mid]; linarith) hp_lt_b hexp_cond'
      have hup := (le_div_iff₀ (by linarith : 0 < Real.log b_mid)).mp hup_div
      have hba : (5 / 6 : ℝ) * (c_mid - b_mid) = (5 / 12 : ℝ) * D := by
        dsimp [b_mid, c_mid]; ring
      rw [hba] at hup
      have hlow : (13 / 31 : ℝ) * D ≤ (P_mid.card : ℝ) * Real.log b_mid := by
        have hm := mul_le_mul_of_nonneg_left hlog_c_le_b (Nat.cast_nonneg P_mid.card)
        linarith [hP_mid_card_log]
      have hlt_log : ((P_mid.filter (fun x => x % (2 * p) = c)).card : ℝ) * Real.log b_mid <
          (P_mid.card : ℝ) * Real.log b_mid := by linarith
      have hlt_real : ((P_mid.filter (fun x => x % (2 * p) = c)).card : ℝ) < (P_mid.card : ℝ) :=
        lt_of_mul_lt_mul_right hlt_log (by linarith)
      exact_mod_cast hlt_real
    obtain ⟨u, hu_mem, v, hv_mem, hu_lt_v, hne_mod⟩ :=
      exists_incongruent_pair_of_card_filter_lt (fun x => x % (2 * p)) ⟨r0, hr0_mem⟩ hfilter_lt
    have hu_p := hP_mid_props u hu_mem
    have hv_p := hP_mid_props v hv_mem
    let g : ℕ := v - u
    have hug : u + g = v := by omega
    have hg_even : 2 ∣ g := by
      obtain ⟨m1, hm1⟩ := hu_p.2.1
      obtain ⟨m2, hm2⟩ := hv_p.2.1
      refine ⟨m2 - m1, ?_⟩
      omega
    have hndvd : ¬ (p ∣ g / 2) :=
      not_dvd_half_gap_of_mod_two_mul_ne hu_p.2.1 hv_p.2.1 hu_lt_v.le hne_mod
    have hg_le : (g : ℝ) ≤ D / 2 := by
      have hcast : (g : ℝ) = (v : ℝ) - (u : ℝ) := Nat.cast_sub hu_lt_v.le
      dsimp [b_mid, c_mid] at hu_p hv_p
      linarith [hu_p.2.2.1, hv_p.2.2.2]
    refine ⟨u, g, ⟨hu_p.1, hu_p.2.1, ?_, ?_, ?_, ?_, hg_le⟩, hg_even, hndvd⟩
    · rw [hug]; exact hv_p.1
    · rw [hug]; exact hv_p.2.1
    · dsimp [b_mid] at hu_p; linarith [hu_p.2.2.1]
    · rw [hug]; dsimp [c_mid] at hv_p; linarith [hv_p.2.2.2]
  exact t75_targets_from_evenIntervalGrid_supplies hn_pos hn_odd hC_ge hh0_pos hh0_le hsize_le
    y D rfl hD_pos hD_upper p_lo p_hi
    ⟨hplo_prime, hplo_odd, hplo_lo.le, hplo_hi⟩
    ⟨hphi_prime, hphi_odd, hphi_lo.le, hphi_hi⟩
    r0 ⟨hr0_props.1, hr0_props.2.1, by rw [hr1_eq]; exact hr1_props.1, by rw [hr1_eq]; exact hr1_props.2.1⟩
    ⟨by dsimp [b_mid] at hr0_props; linarith [hr0_props.2.2.1],
     by rw [hr1_eq]; dsimp [c_mid] at hr1_props; linarith [hr1_props.2.2.2]⟩
    A hA_prime hA_int hA_mod hA_card_ge hA_card hmod_supply

end

end Sude
