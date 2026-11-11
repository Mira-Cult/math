import Sude.FWPhysicalRadiusCentering
import Sude.PackedReachablePrimeDiagonal
import Sude.BTGrowingInstalledGrid
import Mathlib.Data.Nat.Prime.Basic

/-!
# Even-Interval Subset-Sum Grids and Modular Residue Bridging (`EvenIntervalGrid`)

This module introduces `EvenIntervalGrid S gap A B` (realizing every even integer in `[A, B]` as
a subset sum of `gap` on `S`), proves its extension lemma for wide even gaps, proves the
natural-number stabilizer / `minFac` theorem on `Finset.range h0`, proves the majority-coloring
disjoint-pair extraction lemma, and provides adapters connecting `EvenIntervalGrid` to
`CompleteStepGrid`, two-network bounded integer flow realization, and packed prime diagonal repair.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false

/-- Every even integer `q` in the interval `[A, B]` is realized by a subset of `S`. -/
def EvenIntervalGrid {α : Type*} (S : Finset α) (gap : α → ℕ) (A B : ℕ) : Prop :=
  ∀ q : ℕ, A ≤ q → q ≤ B → 2 ∣ q → ∃ T : Finset α, T ⊆ S ∧ (∑ k ∈ T, gap k) = q

theorem evenIntervalGrid_of_completeEvenGrid {α : Type*} (S : Finset α) (gap : α → ℕ) (B : ℕ)
    (h : CompleteEvenGrid S gap B) : EvenIntervalGrid S gap 0 B := by
  intro q _ hqB hq2
  exact h q hqB hq2

theorem evenIntervalGrid_mono {α : Type*} {S : Finset α} {gap : α → ℕ} {A B A' B' : ℕ}
    (h : EvenIntervalGrid S gap A B) (hA : A ≤ A') (hB : B' ≤ B) :
    EvenIntervalGrid S gap A' B' := by
  intro q hqA hqB hq2
  exact h q (le_trans hA hqA) (le_trans hqB hB) hq2

theorem evenIntervalGrid_subset {α : Type*} {S S' : Finset α} {gap : α → ℕ} {A B : ℕ}
    (h : EvenIntervalGrid S gap A B) (hsub : S ⊆ S') :
    EvenIntervalGrid S' gap A B := by
  intro q hqA hqB hq2
  obtain ⟨T, hT, hsum⟩ := h q hqA hqB hq2
  exact ⟨T, hT.trans hsub, hsum⟩

/-- Appending a fresh even gap `gap z ≤ B - A + 2` extends `EvenIntervalGrid S gap A B`
to `EvenIntervalGrid (insert z S) gap A (B + gap z)`. -/
theorem evenIntervalGrid_insert {α : Type*} [DecidableEq α]
    (S : Finset α) (gap : α → ℕ) (A B : ℕ) (z : α)
    (hz : z ∉ S) (hB : 2 ∣ B) (hAB : A ≤ B) (hgap : 2 ∣ gap z)
    (hjoin : gap z ≤ B - A + 2) (hgrid : EvenIntervalGrid S gap A B) :
    EvenIntervalGrid (insert z S) gap A (B + gap z) := by
  intro q hqA hqB heven
  by_cases hsmall : q ≤ B
  · obtain ⟨T, hT, hsum⟩ := hgrid q hqA hsmall heven
    exact ⟨T, hT.trans (Finset.subset_insert z S), hsum⟩
  · have hBq : B + 2 ≤ q := by
      obtain ⟨b, hb⟩ := hB
      obtain ⟨m, hm⟩ := heven
      omega
    have hge : A + gap z ≤ q := by omega
    have hrestA : A ≤ q - gap z := by omega
    have hrestB : q - gap z ≤ B := by omega
    have hevenRest : 2 ∣ q - gap z := Nat.dvd_sub heven hgap
    obtain ⟨T, hT, hsum⟩ := hgrid (q - gap z) hrestA hrestB hevenRest
    have hnot : z ∉ T := fun hmem => hz (hT hmem)
    refine ⟨insert z T, Finset.insert_subset_insert z hT, ?_⟩
    rw [Finset.sum_insert hnot, hsum]
    omega

/-- Extending an `EvenIntervalGrid` by a disjoint finite set `W` of even gaps each bounded by
`B - A + 2`. -/
theorem evenIntervalGrid_extend_finset {α : Type*} [DecidableEq α]
    (base W : Finset α) (gap : α → ℕ) (A B : ℕ)
    (hB : 2 ∣ B) (hAB : A ≤ B) (hdisj : Disjoint base W)
    (hW : ∀ k ∈ W, 2 ∣ gap k ∧ gap k ≤ B - A + 2)
    (hbase : EvenIntervalGrid base gap A B) :
    EvenIntervalGrid (base ∪ W) gap A (B + ∑ k ∈ W, gap k) ∧
      2 ∣ (B + ∑ k ∈ W, gap k) := by
  induction W using Finset.induction with
  | empty =>
    simpa using ⟨hbase, hB⟩
  | @insert z s hz ih =>
    have hdisj_s : Disjoint base s := hdisj.mono_right (Finset.subset_insert z s)
    have hW_s : ∀ k ∈ s, 2 ∣ gap k ∧ gap k ≤ B - A + 2 :=
      fun k hk => hW k (Finset.mem_insert_of_mem hk)
    obtain ⟨hgrid_s, hB_s⟩ := ih hdisj_s hW_s
    have hz_not_base : z ∉ base :=
      Finset.disjoint_right.mp hdisj (Finset.mem_insert_self z s)
    have hz_not_union : z ∉ base ∪ s := by
      simp [hz_not_base, hz]
    have hz_props := hW z (Finset.mem_insert_self z s)
    have hAB_s : A ≤ B + ∑ k ∈ s, gap k := by omega
    have hjoin_s : gap z ≤ (B + ∑ k ∈ s, gap k) - A + 2 := by omega
    have hins := evenIntervalGrid_insert (base ∪ s) gap A (B + ∑ k ∈ s, gap k) z
      hz_not_union hB_s hAB_s hz_props.1 hjoin_s hgrid_s
    have hsum_ins : B + ∑ k ∈ insert z s, gap k = (B + ∑ k ∈ s, gap k) + gap z := by
      rw [Finset.sum_insert hz]
      omega
    have hunion_ins : base ∪ insert z s = insert z (base ∪ s) := by
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    refine ⟨?_, ?_⟩
    · rw [hunion_ins, hsum_ins]
      exact hins
    · rw [hsum_ins]
      exact dvd_add hB_s hz_props.1

/-- Combining a `CompleteStepGrid` of step `2 * h0` and radius `R_g` with a disjoint set `S_mod`
of even gaps whose subset sums cover all `h0` even residues modulo `2 * h0` and whose total sum
is at most `R_mod ≤ R_g` yields an `EvenIntervalGrid` on `[R_mod, R_g]`. -/
theorem evenIntervalGrid_of_stepGrid_and_modCover {α : Type*} [DecidableEq α]
    (S_g S_mod : Finset α) (gap : α → ℕ) (h0 R_mod R_g : ℕ)
    (hh0 : 0 < h0) (hdisj : Disjoint S_g S_mod)
    (hstep : CompleteStepGrid S_g gap (2 * h0) R_g)
    (hmod_even : ∀ k ∈ S_mod, 2 ∣ gap k)
    (hmod_sum : (∑ k ∈ S_mod, gap k) ≤ R_mod)
    (hcover : ∀ r < h0, ∃ T_m ⊆ S_mod, ((∑ k ∈ T_m, gap k) / 2) % h0 = r) :
    EvenIntervalGrid (S_g ∪ S_mod) gap R_mod R_g := by
  intro q hqA hqB hq2
  let r := (q / 2) % h0
  have hr_lt : r < h0 := Nat.mod_lt _ hh0
  obtain ⟨T_m, hTm_sub, hTm_mod⟩ := hcover r hr_lt
  have hTm_even : 2 ∣ ∑ k ∈ T_m, gap k := by
    apply Finset.dvd_sum
    intro k hk
    exact hmod_even k (hTm_sub hk)
  have hTm_le : (∑ k ∈ T_m, gap k) ≤ q := by
    have hle1 : (∑ k ∈ T_m, gap k) ≤ ∑ k ∈ S_mod, gap k :=
      Finset.sum_le_sum_of_subset hTm_sub
    omega
  have hdiv : 2 * h0 ∣ q - ∑ k ∈ T_m, gap k := by
    obtain ⟨m1, hm1⟩ := hq2
    obtain ⟨m2, hm2⟩ := hTm_even
    have hm1_div : q / 2 = m1 := by omega
    have hm2_div : (∑ k ∈ T_m, gap k) / 2 = m2 := by omega
    have hmod_eq : m2 % h0 = m1 % h0 := by
      simpa [r, hm1_div, hm2_div] using hTm_mod
    have hm2_le_m1 : m2 ≤ m1 := by omega
    have hdm1 : h0 * (m1 / h0) + m1 % h0 = m1 := Nat.div_add_mod m1 h0
    have hdm2 : h0 * (m2 / h0) + m2 % h0 = m2 := Nat.div_add_mod m2 h0
    have hsub_m : m1 - m2 = h0 * (m1 / h0) - h0 * (m2 / h0) := by omega
    have hmul_sub : h0 * (m1 / h0) - h0 * (m2 / h0) = h0 * (m1 / h0 - m2 / h0) :=
      (Nat.mul_sub_left_distrib h0 (m1 / h0) (m2 / h0)).symm
    refine ⟨m1 / h0 - m2 / h0, ?_⟩
    calc
      q - ∑ k ∈ T_m, gap k = 2 * (m1 - m2) := by omega
      _ = 2 * (h0 * (m1 / h0 - m2 / h0)) := by rw [hsub_m, hmul_sub]
      _ = (2 * h0) * (m1 / h0 - m2 / h0) := by ring
  have hrest_le : q - ∑ k ∈ T_m, gap k ≤ R_g := by omega
  obtain ⟨T_g, hTg_sub, hTg_sum⟩ := hstep (q - ∑ k ∈ T_m, gap k) hrest_le hdiv
  have hdisj_T : Disjoint T_g T_m := hdisj.mono hTg_sub hTm_sub
  refine ⟨T_g ∪ T_m, Finset.union_subset_union hTg_sub hTm_sub, ?_⟩
  rw [Finset.sum_union hdisj_T, hTg_sum]
  omega

/-! ## Natural-Number Period Stabilizer and `Nat.minFac` Residue-Growth Lemma -/

/-- `x` is an additive period of `A ⊆ Finset.range h0` modulo `h0`. -/
def IsModPeriod (h0 : ℕ) (A : Finset ℕ) (x : ℕ) : Prop :=
  ∀ a ∈ A, (a + x) % h0 ∈ A

instance decidableIsModPeriod (h0 : ℕ) (A : Finset ℕ) (x : ℕ) :
    Decidable (IsModPeriod h0 A x) := by
  unfold IsModPeriod
  infer_instance

theorem isModPeriod_zero {h0 : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range h0) :
    IsModPeriod h0 A 0 := by
  intro a ha
  have ha_lt : a < h0 := Finset.mem_range.mp (hA ha)
  simpa [Nat.mod_eq_of_lt ha_lt] using ha

theorem isModPeriod_self {h0 : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range h0) :
    IsModPeriod h0 A h0 := by
  intro a ha
  have ha_lt : a < h0 := Finset.mem_range.mp (hA ha)
  simpa [Nat.add_mod_right, Nat.mod_eq_of_lt ha_lt] using ha

theorem isModPeriod_add {h0 : ℕ} {A : Finset ℕ} {x y : ℕ}
    (hx : IsModPeriod h0 A x) (hy : IsModPeriod h0 A y) :
    IsModPeriod h0 A (x + y) := by
  intro a ha
  have h1 : (a + x) % h0 ∈ A := hx a ha
  have h2 : ((a + x) % h0 + y) % h0 ∈ A := hy _ h1
  have heq : ((a + x) % h0 + y) % h0 = (a + (x + y)) % h0 := by
    calc
      ((a + x) % h0 + y) % h0 = (a + x + y) % h0 :=
        Nat.ModEq.add_right y (Nat.mod_modEq (a + x) h0)
      _ = (a + (x + y)) % h0 := by rw [add_assoc]
  rwa [← heq]

theorem isModPeriod_mul {h0 : ℕ} {A : Finset ℕ} {x : ℕ}
    (hA : A ⊆ Finset.range h0) (hx : IsModPeriod h0 A x) :
    ∀ k : ℕ, IsModPeriod h0 A (k * x)
  | 0 => by simpa using isModPeriod_zero hA
  | k + 1 => by
    rw [Nat.succ_mul]
    exact isModPeriod_add (isModPeriod_mul hA hx k) hx

theorem isModPeriod_mod {h0 : ℕ} {A : Finset ℕ} {x y : ℕ}
    (hh0 : 0 < h0) (hA : A ⊆ Finset.range h0)
    (hx : IsModPeriod h0 A x) (hy : IsModPeriod h0 A y) :
    IsModPeriod h0 A (y % x) := by
  intro a ha
  let q := y / x
  have hdiv : y % x + x * q = y := Nat.mod_add_div y x
  have hmul : IsModPeriod h0 A ((q * (h0 - 1)) * x) :=
    isModPeriod_mul hA hx (q * (h0 - 1))
  have hsum : IsModPeriod h0 A (y + (q * (h0 - 1)) * x) :=
    isModPeriod_add hy hmul
  have hin : (a + (y + (q * (h0 - 1)) * x)) % h0 ∈ A := hsum a ha
  have hident : a + (y + (q * (h0 - 1)) * x) = (a + y % x) + h0 * (q * x) := by
    have h1 : 1 + (h0 - 1) = h0 := by omega
    calc
      a + (y + (q * (h0 - 1)) * x)
          = a + (y % x + x * q + (q * (h0 - 1)) * x) := by rw [hdiv]
      _ = (a + y % x) + (1 + (h0 - 1)) * (q * x) := by ring
      _ = (a + y % x) + h0 * (q * x) := by rw [h1]
  rwa [hident, Nat.add_mul_mod_self_left] at hin

theorem not_isModPeriod_one {h0 : ℕ} {A : Finset ℕ}
    (_hA : A ⊆ Finset.range h0) (h0_mem : 0 ∈ A) (hcard : A.card < h0) :
    ¬ IsModPeriod h0 A 1 := by
  intro h1
  have hall : ∀ r < h0, r ∈ A := by
    intro r
    induction r with
    | zero =>
      intro _
      exact h0_mem
    | succ r ih =>
      intro hr
      have hr' : r < h0 := by omega
      have hmem := h1 r (ih hr')
      rwa [Nat.mod_eq_of_lt hr] at hmem
  have hsub : Finset.range h0 ⊆ A := by
    intro r hr
    exact hall r (Finset.mem_range.mp hr)
  have hle : h0 ≤ A.card := by
    simpa using Finset.card_le_card hsub
  omega

/-- For any proper subset `A ⊂ Finset.range h0` containing `0`, there exists a prime `p ∣ h0`
such that any step `d` with `¬ (p ∣ d)` is NOT a period of `A` modulo `h0`, and hence
increases the size of `A` by at least 1 when translated by `d` modulo `h0`. -/
theorem exists_prime_dvd_step_increases_card {h0 : ℕ} {A : Finset ℕ}
    (hh0 : 0 < h0) (hA : A ⊆ Finset.range h0) (h0_mem : 0 ∈ A) (hcard : A.card < h0) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ h0 ∧
      ∀ d : ℕ, ¬ (p ∣ d) →
        A.card + 1 ≤ (A ∪ A.image (fun a => (a + d) % h0)).card ∧
        A ∪ A.image (fun a => (a + d) % h0) ⊆ Finset.range h0 := by
  have hex : ∃ s : ℕ, 0 < s ∧ IsModPeriod h0 A s := ⟨h0, hh0, isModPeriod_self hA⟩
  let s0 := Nat.find hex
  have hs0_spec : 0 < s0 ∧ IsModPeriod h0 A s0 := Nat.find_spec hex
  have hs0_dvd : ∀ d : ℕ, IsModPeriod h0 A d → s0 ∣ d := by
    intro d hd
    have hmod_per : IsModPeriod h0 A (d % s0) := isModPeriod_mod hh0 hA hs0_spec.2 hd
    have hlt : d % s0 < s0 := Nat.mod_lt d hs0_spec.1
    by_contra hndvd
    have hpos : 0 < d % s0 := Nat.pos_of_ne_zero (mt Nat.dvd_of_mod_eq_zero hndvd)
    exact Nat.find_min hex hlt ⟨hpos, hmod_per⟩
  have hs0_dvd_h0 : s0 ∣ h0 := hs0_dvd h0 (isModPeriod_self hA)
  have hs0_ne_one : s0 ≠ 1 := by
    intro heq
    have h1 : IsModPeriod h0 A 1 := heq ▸ hs0_spec.2
    exact not_isModPeriod_one hA h0_mem hcard h1
  let p := s0.minFac
  have hp_prime : Nat.Prime p := Nat.minFac_prime hs0_ne_one
  have hp_dvd_s0 : p ∣ s0 := Nat.minFac_dvd s0
  have hp_dvd_h0 : p ∣ h0 := dvd_trans hp_dvd_s0 hs0_dvd_h0
  refine ⟨p, hp_prime, hp_dvd_h0, ?_⟩
  intro d hndvd
  have hnot_per : ¬ IsModPeriod h0 A d := by
    intro hper
    exact hndvd (dvd_trans hp_dvd_s0 (hs0_dvd d hper))
  have ⟨a, haA, ha_not⟩ : ∃ a ∈ A, (a + d) % h0 ∉ A := by
    by_contra hall
    apply hnot_per
    intro a ha
    by_contra hna
    exact hall ⟨a, ha, hna⟩
  have hmem_img : (a + d) % h0 ∈ A.image (fun x => (x + d) % h0) :=
    Finset.mem_image_of_mem _ haA
  have hssub : A ⊂ A ∪ A.image (fun x => (x + d) % h0) := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_left, ?_⟩
    intro heq
    apply ha_not
    rw [heq]
    exact Finset.mem_union_right _ hmem_img
  have hcard_lt : A.card < (A ∪ A.image (fun x => (x + d) % h0)).card :=
    Finset.card_lt_card hssub
  have hsub_range : A ∪ A.image (fun x => (x + d) % h0) ⊆ Finset.range h0 := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxImg
    · exact hA hxA
    · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hxImg
      exact Finset.mem_range.mpr (Nat.mod_lt _ hh0)
  exact ⟨by omega, hsub_range⟩

/-- If `u ≤ v` are odd integers with `u % (2 * p) ≠ v % (2 * p)`, then `¬ (p ∣ (v - u) / 2)`. -/
theorem not_dvd_half_gap_of_mod_two_mul_ne {u v p : ℕ}
    (hu : Odd u) (hv : Odd v) (hle : u ≤ v) (hne : u % (2 * p) ≠ v % (2 * p)) :
    ¬ (p ∣ (v - u) / 2) := by
  intro hdvd
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  have hab : a ≤ b := by omega
  have hdiv : (v - u) / 2 = b - a := by omega
  have hba : b - a = p * k := by omega
  have hvu : v - u = (2 * p) * k := by
    calc
      v - u = 2 * (b - a) := by omega
      _ = 2 * (p * k) := by rw [hba]
      _ = (2 * p) * k := by ring
  have hv_eq : v = u + (2 * p) * k := by omega
  have hmod : v % (2 * p) = u % (2 * p) := by
    rw [hv_eq, Nat.add_mul_mod_self_left]
  exact hne hmod.symm

/-! ## Majority-Coloring Incongruent Pair Extraction -/

/-- If `S : Finset ℕ` has `1 ≤ S.card` and every color class under `f` has strictly fewer than
`S.card` elements, then `S` contains two elements `u < v` with `f u ≠ f v`. -/
theorem exists_incongruent_pair_of_card_filter_lt {S : Finset ℕ} (f : ℕ → ℕ)
    (hne : S.Nonempty)
    (hfilter : ∀ c : ℕ, (S.filter (fun x => f x = c)).card < S.card) :
    ∃ u ∈ S, ∃ v ∈ S, u < v ∧ f u ≠ f v := by
  obtain ⟨x1, hx1⟩ := hne
  have hlt : (S.filter (fun x => f x = f x1)).card < S.card := hfilter (f x1)
  have hsub : S.filter (fun x => f x = f x1) ⊂ S :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ S,
      fun heq => Nat.ne_of_lt hlt (congrArg Finset.card heq)⟩
  obtain ⟨x2, hx2S, hx2_not⟩ := Finset.exists_of_ssubset hsub
  have hfx2 : f x2 ≠ f x1 := by
    intro heq
    exact hx2_not (Finset.mem_filter.mpr ⟨hx2S, heq⟩)
  have hx_ne : x1 ≠ x2 := fun heq => hfx2 (heq ▸ rfl)
  rcases lt_or_gt_of_ne hx_ne with h12 | h21
  · exact ⟨x1, hx1, x2, hx2S, h12, hfx2.symm⟩
  · exact ⟨x2, hx2S, x1, hx1, h21, hfx2⟩

/-- Greedy extraction of `Q` pairwise-disjoint ordered pairs `(u_i, v_i)` from `S` with
heterogeneous colorings `f i` (`f i (u_i) ≠ f i (v_i)`) whenever `M + 2 * Q ≤ S.card` and
every color class of every `f i` in `S` has size at most `M`. -/
theorem exists_heterogeneous_incongruent_pairs {S : Finset ℕ} {Q : ℕ}
    (f : Fin Q → ℕ → ℕ) (M : ℕ)
    (hcard : M + 2 * Q ≤ S.card)
    (hfilter : ∀ (i : Fin Q) (c : ℕ), (S.filter (fun x => f i x = c)).card ≤ M) :
    ∃ (u v : Fin Q → ℕ),
      (∀ i, u i ∈ S ∧ v i ∈ S ∧ u i < v i ∧ f i (u i) ≠ f i (v i)) ∧
      (∀ i j, i ≠ j → Disjoint ({u i, v i} : Finset ℕ) {u j, v j}) := by
  induction Q generalizing S with
  | zero =>
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ Q ih =>
    have hS_pos : 0 < S.card := by omega
    have hne : S.Nonempty := Finset.card_pos.mp hS_pos
    have hlt : ∀ c : ℕ, (S.filter (fun x => f 0 x = c)).card < S.card := by
      intro c
      have := hfilter 0 c
      omega
    obtain ⟨u0, hu0S, v0, hv0S, huv0, hfuv0⟩ :=
      exists_incongruent_pair_of_card_filter_lt (f 0) hne hlt
    let S' := (S.erase u0).erase v0
    have hv0_in_erase : v0 ∈ S.erase u0 :=
      Finset.mem_erase.mpr ⟨ne_of_gt huv0, hv0S⟩
    have hcard_S' : S'.card = S.card - 2 := by
      have h1 : (S.erase u0).card = S.card - 1 := Finset.card_erase_of_mem hu0S
      have h2 : S'.card = (S.erase u0).card - 1 := Finset.card_erase_of_mem hv0_in_erase
      omega
    have hsub_S' : S' ⊆ S :=
      (Finset.erase_subset v0 (S.erase u0)).trans (Finset.erase_subset u0 S)
    have hcard' : M + 2 * Q ≤ S'.card := by omega
    have hfilter' : ∀ (i : Fin Q) (c : ℕ), (S'.filter (fun x => f i.succ x = c)).card ≤ M := by
      intro i c
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hsub_S')).trans (hfilter i.succ c)
    obtain ⟨u', v', hprops', hdisj'⟩ := ih (fun i => f i.succ) hcard' hfilter'
    let u : Fin (Q + 1) → ℕ := Fin.cons u0 u'
    let v : Fin (Q + 1) → ℕ := Fin.cons v0 v'
    have hnot_u0 : ∀ i : Fin Q, u' i ≠ u0 ∧ v' i ≠ u0 := by
      intro i
      have hu'_mem : u' i ∈ S' := (hprops' i).1
      have hv'_mem : v' i ∈ S' := (hprops' i).2.1
      have hu'_er : u' i ∈ S.erase u0 := Finset.erase_subset v0 (S.erase u0) hu'_mem
      have hv'_er : v' i ∈ S.erase u0 := Finset.erase_subset v0 (S.erase u0) hv'_mem
      exact ⟨(Finset.mem_erase.mp hu'_er).1, (Finset.mem_erase.mp hv'_er).1⟩
    have hnot_v0 : ∀ i : Fin Q, u' i ≠ v0 ∧ v' i ≠ v0 := by
      intro i
      have hu'_mem : u' i ∈ S' := (hprops' i).1
      have hv'_mem : v' i ∈ S' := (hprops' i).2.1
      exact ⟨(Finset.mem_erase.mp hu'_mem).1, (Finset.mem_erase.mp hv'_mem).1⟩
    refine ⟨u, v, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨hu0S, hv0S, huv0, hfuv0⟩
      · intro j
        obtain ⟨hu', hv', hlt', hf'⟩ := hprops' j
        exact ⟨hsub_S' hu', hsub_S' hv', hlt', hf'⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · intro j
        refine Fin.cases ?_ ?_ j
        · intro hij
          exact False.elim (hij rfl)
        · intro j' _
          apply Finset.disjoint_left.mpr
          intro x hx1 hx2
          simp only [u, v, Fin.cons_zero, Fin.cons_succ, Finset.mem_insert,
            Finset.mem_singleton] at hx1 hx2
          rcases hx1 with rfl | rfl <;> rcases hx2 with h1 | h2
          · exact (hnot_u0 j').1 h1.symm
          · exact (hnot_u0 j').2 h2.symm
          · exact (hnot_v0 j').1 h1.symm
          · exact (hnot_v0 j').2 h2.symm
      · intro i' j
        refine Fin.cases ?_ ?_ j
        · intro _
          apply Finset.disjoint_left.mpr
          intro x hx1 hx2
          simp only [u, v, Fin.cons_zero, Fin.cons_succ, Finset.mem_insert,
            Finset.mem_singleton] at hx1 hx2
          rcases hx1 with h1 | h2 <;> rcases hx2 with rfl | rfl
          · exact (hnot_u0 i').1 h1.symm
          · exact (hnot_v0 i').1 h1.symm
          · exact (hnot_u0 i').2 h2.symm
          · exact (hnot_v0 i').2 h2.symm
        · intro j' hij
          have hij' : i' ≠ j' := fun heq => hij (congrArg Fin.succ heq)
          simpa [u, v] using hdisj' i' j' hij'

/-- Homogeneous specialization of `exists_heterogeneous_incongruent_pairs`. -/
theorem exists_disjoint_incongruent_pairs {S : Finset ℕ} (f : ℕ → ℕ) (M Q : ℕ)
    (hcard : M + 2 * Q ≤ S.card)
    (hfilter : ∀ c : ℕ, (S.filter (fun x => f x = c)).card ≤ M) :
    ∃ (u v : Fin Q → ℕ),
      (∀ i, u i ∈ S ∧ v i ∈ S ∧ u i < v i ∧ f (u i) ≠ f (v i)) ∧
      (∀ i j, i ≠ j → Disjoint ({u i, v i} : Finset ℕ) {u j, v j}) :=
  exists_heterogeneous_incongruent_pairs (fun _ => f) M hcard (fun _ c => hfilter c)

/-! ## Modular Half-Gap Subset-Sum Coverage (`ModAchievable`) -/

/-- `A ⊆ Finset.range h0` is a set of half-gap subset-sum residues modulo `h0` achievable
using subsets of `S`. -/
def ModAchievable {α : Type*} (h0 : ℕ) (gap : α → ℕ) (S : Finset α) (A : Finset ℕ) : Prop :=
  A ⊆ Finset.range h0 ∧ 0 ∈ A ∧ (∀ k ∈ S, 2 ∣ gap k) ∧
    ∀ r ∈ A, ∃ T ⊆ S, ((∑ k ∈ T, gap k) / 2) % h0 = r

theorem modAchievable_empty {α : Type*} (h0 : ℕ) (gap : α → ℕ) (hh0 : 0 < h0) :
    ModAchievable h0 gap ∅ {0} := by
  refine ⟨?_, Finset.mem_singleton_self 0, fun _ hk => by simp at hk, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton.mp hx]
    exact Finset.mem_range.mpr hh0
  · intro r hr
    rw [Finset.mem_singleton.mp hr]
    exact ⟨∅, Finset.Subset.refl _, by simp⟩

theorem modAchievable_insert {α : Type*} [DecidableEq α]
    {h0 : ℕ} {gap : α → ℕ} {S : Finset α} {A : Finset ℕ} {z : α}
    (hh0 : 0 < h0) (hmod : ModAchievable h0 gap S A) (hz : z ∉ S) (heven : 2 ∣ gap z) :
    ModAchievable h0 gap (insert z S) (A ∪ A.image (fun a => (a + (gap z / 2)) % h0)) := by
  rcases hmod with ⟨hA_range, h0_A, hS_even, hA_ach⟩
  refine ⟨?_, Finset.mem_union_left _ h0_A, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxImg
    · exact hA_range hxA
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hxImg
      exact Finset.mem_range.mpr (Nat.mod_lt _ hh0)
  · intro k hk
    rcases Finset.mem_insert.mp hk with rfl | hkS
    · exact heven
    · exact hS_even k hkS
  · intro r hr
    rcases Finset.mem_union.mp hr with hrA | hrImg
    · obtain ⟨T, hT, hsum⟩ := hA_ach r hrA
      exact ⟨T, hT.trans (Finset.subset_insert z S), hsum⟩
    · obtain ⟨a, haA, rfl⟩ := Finset.mem_image.mp hrImg
      obtain ⟨T, hT, hsum⟩ := hA_ach a haA
      have hzT : z ∉ T := fun h => hz (hT h)
      have hT_even : 2 ∣ ∑ k ∈ T, gap k := by
        apply Finset.dvd_sum
        intro k hk
        exact hS_even k (hT hk)
      refine ⟨insert z T, Finset.insert_subset_insert z hT, ?_⟩
      rw [Finset.sum_insert hzT]
      obtain ⟨m1, hm1⟩ := heven
      obtain ⟨m2, hm2⟩ := hT_even
      have hdiv_sum : (gap z + ∑ k ∈ T, gap k) / 2 = (∑ k ∈ T, gap k) / 2 + gap z / 2 := by omega
      rw [hdiv_sum, ← hsum]
      exact (Nat.ModEq.add_right (gap z / 2) (Nat.mod_modEq ((∑ k ∈ T, gap k) / 2) h0)).symm

/-- Uniform single-step prime divisor choice for `ModAchievable`: for any `2 ≤ h0` and
`ModAchievable h0 gap S A`, there exists a prime `p ∣ h0` such that inserting any `z ∉ S`
with `2 ∣ gap z` and `¬ (p ∣ gap z / 2)` advances `A` to `A'` with
`min h0 (A.card + 1) ≤ A'.card`. -/
theorem modAchievable_step_prime {α : Type*} [DecidableEq α]
    {h0 : ℕ} {gap : α → ℕ} {S : Finset α} {A : Finset ℕ}
    (hh0 : 2 ≤ h0) (hmod : ModAchievable h0 gap S A) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ h0 ∧
      ∀ z : α, z ∉ S → 2 ∣ gap z → ¬ (p ∣ gap z / 2) →
        let A' := A ∪ A.image (fun a => (a + (gap z / 2)) % h0)
        ModAchievable h0 gap (insert z S) A' ∧ min h0 (A.card + 1) ≤ A'.card := by
  have hh0_pos : 0 < h0 := by omega
  by_cases hlt : A.card < h0
  · obtain ⟨p, hp_prime, hp_dvd, hstep⟩ :=
      exists_prime_dvd_step_increases_card hh0_pos hmod.1 hmod.2.1 hlt
    refine ⟨p, hp_prime, hp_dvd, ?_⟩
    intro z hz heven hndvd
    have hcard := (hstep (gap z / 2) hndvd).1
    exact ⟨modAchievable_insert hh0_pos hmod hz heven, le_trans (min_le_right _ _) hcard⟩
  · have hle : A.card ≤ h0 := by
      simpa using Finset.card_le_card hmod.1
    have heq : A.card = h0 := by omega
    let p := h0.minFac
    have hp_prime : Nat.Prime p := Nat.minFac_prime (by omega)
    have hp_dvd : p ∣ h0 := Nat.minFac_dvd h0
    refine ⟨p, hp_prime, hp_dvd, ?_⟩
    intro z hz heven _
    have hcard : h0 ≤ (A ∪ A.image (fun a => (a + (gap z / 2)) % h0)).card := by
      rw [← heq]
      exact Finset.card_le_card Finset.subset_union_left
    exact ⟨modAchievable_insert hh0_pos hmod hz heven, le_trans (min_le_left _ _) hcard⟩

/-- When `ModAchievable h0 gap S A` holds with `h0 ≤ A.card`, every residue `r < h0` is
achieved by a subset of `S`. -/
theorem modAchievable_full_cover {α : Type*}
    {h0 : ℕ} {gap : α → ℕ} {S : Finset α} {A : Finset ℕ}
    (hmod : ModAchievable h0 gap S A) (hcard : h0 ≤ A.card) :
    (∀ k ∈ S, 2 ∣ gap k) ∧
      ∀ r < h0, ∃ T ⊆ S, ((∑ k ∈ T, gap k) / 2) % h0 = r := by
  have hA_eq : A = Finset.range h0 :=
    Finset.eq_of_subset_of_card_le hmod.1 (by simpa using hcard)
  refine ⟨hmod.2.2.1, ?_⟩
  intro r hr
  exact hmod.2.2.2 r (hA_eq ▸ Finset.mem_range.mpr hr)

/-! ## Direct Diagonal Repair Adapter for `EvenIntervalGrid` -/

/-- Direct repair of both diagonals to a common odd prime target `p_diag` from two disjoint
`EvenIntervalGrid` families on `active.filter (choice · = true)` and `active.filter (choice · = false)`. -/
theorem packed_prime_diagonal_repair_of_evenIntervalGrid {L n : ℕ}
    (hs : 2 * L + 1 ≤ n) (hL : 3 ≤ L) (hn : Odd n)
    (choice : Fin L → Bool) (gap : Fin L → ℕ) (active : Finset (Fin L))
    (Am Rm Aa Ra : ℕ) (a b : Cell n ≃ Fin (n * n)) (keep : Finset (Cell n))
    (hm : EvenIntervalGrid (active.filter fun i => choice i = true) gap Am Rm)
    (ha : EvenIntervalGrid (active.filter fun i => choice i = false) gap Aa Ra)
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
    (p_diag : ℕ) (hprime : Nat.Prime p_diag) (hodd : Odd p_diag)
    (hreachm : (Am : ℤ) ≤ (p_diag : ℤ) - mainSum a ∧ (p_diag : ℤ) - mainSum a ≤ Rm)
    (hreacha : (Aa : ℤ) ≤ (p_diag : ℤ) - antiSum a ∧ (p_diag : ℤ) - antiSum a ≤ Ra) :
    ∃ result : Cell n ≃ Fin (n * n),
      (∀ r, rowSum result r = rowSum b r) ∧
      (∀ c, columnSum result c = columnSum b c) ∧
      mainSum result = p_diag ∧ antiSum result = p_diag ∧ Valid result ∧
      Set.range (entry result) = pool n ∧ Function.Injective (entry result) ∧
      (∀ z ∈ keep, entry result z = entry b z) := by
  have hnpos : 0 < n := by obtain ⟨k, hk⟩ := hn; omega
  have hmain_odd : Odd (mainSum a) := mainSum_odd_of_odd_order hn a
  have hanti_odd : Odd (antiSum a) := antiSum_odd_of_odd_order hn a
  let qm : ℕ := p_diag - mainSum a
  let qa : ℕ := p_diag - antiSum a
  have hqm_def : qm = p_diag - mainSum a := rfl
  have hqa_def : qa = p_diag - antiSum a := rfl
  have hqm_le : mainSum a ≤ p_diag := by omega
  have hqa_le : antiSum a ≤ p_diag := by omega
  have hqm_A : Am ≤ qm := by omega
  have hqm_R : qm ≤ Rm := by omega
  have hqa_A : Aa ≤ qa := by omega
  have hqa_R : qa ≤ Ra := by omega
  have hqm_even : 2 ∣ qm := by
    obtain ⟨k1, hk1⟩ := hodd
    obtain ⟨k2, hk2⟩ := hmain_odd
    exact ⟨k1 - k2, by omega⟩
  have hqa_even : 2 ∣ qa := by
    obtain ⟨k1, hk1⟩ := hodd
    obtain ⟨k2, hk2⟩ := hanti_odd
    exact ⟨k1 - k2, by omega⟩
  obtain ⟨Tm, hTm_sub, hTm_sum⟩ := hm qm hqm_A hqm_R hqm_even
  obtain ⟨Ta, hTa_sub, hTa_sum⟩ := ha qa hqa_A hqa_R hqa_even
  let after := Tm ∪ Ta
  have hafter_sub : after ⊆ active := by
    intro i hi
    rcases Finset.mem_union.mp hi with him | hia
    · exact (Finset.mem_filter.mp (hTm_sub him)).1
    · exact (Finset.mem_filter.mp (hTa_sub hia)).1
  have hdisj_ma : Disjoint Tm Ta := by
    apply Finset.disjoint_left.mpr
    intro i him hia
    have h1 : choice i = true := (Finset.mem_filter.mp (hTm_sub him)).2
    have h2 : choice i = false := (Finset.mem_filter.mp (hTa_sub hia)).2
    exact Bool.noConfusion (h1.symm.trans h2)
  have hgaps_b : ∀ i ∈ active,
      entry b (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i) =
        entry b (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i) + gap i ∧
      entry b (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i) =
        entry b (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i) + gap i := by
    intro i hi
    have h1 := hagree (RectanglePacking.firstRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    have h2 := hagree (RectanglePacking.firstRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    have h3 := hagree (RectanglePacking.secondRow hs i, RectanglePacking.firstColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    have h4 := hagree (RectanglePacking.secondRow hs i, RectanglePacking.secondColumn hs choice i)
      (Finset.mem_biUnion.mpr ⟨i, hi, by simp⟩)
    rw [h1, h2, h3, h4]
    exact hgaps i hi
  have hdiff := packed_orientation_difference hs hL hnpos choice gap b active ∅ after keep
    (Finset.empty_subset _) hafter_sub hgaps_b hprotect
  dsimp only at hdiff
  have hbase_eq : packedTradeSequence hs choice b (∅ : Finset (Fin L)).toList = b := by
    simp [packedTradeSequence]
  rw [hbase_eq] at hdiff
  let result := packedTradeSequence hs choice b after.toList
  have hsum_m : (∑ i ∈ after, if choice i then (gap i : ℤ) else 0) = (qm : ℤ) := by
    rw [Finset.sum_union hdisj_ma]
    have h1 : (∑ i ∈ Tm, if choice i then (gap i : ℤ) else 0) = ∑ i ∈ Tm, (gap i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp (hTm_sub hi)).2]
      simp
    have h2 : (∑ i ∈ Ta, if choice i then (gap i : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [(Finset.mem_filter.mp (hTa_sub hi)).2]
      simp
    rw [h1, h2, add_zero]
    exact_mod_cast hTm_sum
  have hsum_a : (∑ i ∈ after, if choice i then 0 else (gap i : ℤ)) = (qa : ℤ) := by
    rw [Finset.sum_union hdisj_ma]
    have h1 : (∑ i ∈ Tm, if choice i then 0 else (gap i : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [(Finset.mem_filter.mp (hTm_sub hi)).2]
      simp
    have h2 : (∑ i ∈ Ta, if choice i then 0 else (gap i : ℤ)) = ∑ i ∈ Ta, (gap i : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp (hTa_sub hi)).2]
      simp
    rw [h1, h2, zero_add]
    exact_mod_cast hTa_sum
  have hm_res : mainSum result = p_diag := by
    have h : (mainSum result : ℤ) - (mainSum b : ℤ) = (qm : ℤ) := by
      simpa [hsum_m] using hdiff.2.2.1
    rw [hmain] at h
    exact_mod_cast (by omega : (mainSum result : ℤ) = p_diag)
  have ha_res : antiSum result = p_diag := by
    have h : (antiSum result : ℤ) - (antiSum b : ℤ) = (qa : ℤ) := by
      simpa [hsum_a] using hdiff.2.2.2.1
    rw [hanti] at h
    exact_mod_cast (by omega : (antiSum result : ℤ) = p_diag)
  refine ⟨result, hdiff.1, hdiff.2.1, hm_res, ha_res, ?_, hdiff.2.2.2.2.1, hdiff.2.2.2.2.2.1,
    hdiff.2.2.2.2.2.2.2⟩
  exact ⟨fun r => by rw [hdiff.1 r]; exact hrows r,
    fun c => by rw [hdiff.2.1 c]; exact hcols c,
    by rw [hm_res]; exact hprime,
    by rw [ha_res]; exact hprime⟩

/-! ## Centered Window Realization from `EvenIntervalGrid` -/

/-- An `EvenIntervalGrid S gap A R` with `A + 2 * (N / 2) ≤ evenGridCenter R` realizes every
even signed transfer `2 * f` with `|f| ≤ N / 2` relative to `evenGridCenter R`. -/
theorem centered_evenIntervalGrid {α : Type*} (S : Finset α)
    (gap : α → ℕ) (A R N : ℕ)
    (hgrid : EvenIntervalGrid S gap A R)
    (hA : A + 2 * (N / 2) ≤ evenGridCenter R)
    (f : ℤ) (hlow : -((N / 2 : ℕ) : ℤ) ≤ f) (hhigh : f ≤ ((N / 2 : ℕ) : ℤ)) :
    ∃ T : Finset α, T ⊆ S ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter R = 2 * f := by
  have hc : 2 * evenGridCenter R ≤ R := evenGridCenter_twice_le R
  have hnonneg : 0 ≤ (evenGridCenter R : ℤ) + 2 * f := by omega
  let q := Int.toNat ((evenGridCenter R : ℤ) + 2 * f)
  have hq : (q : ℤ) = (evenGridCenter R : ℤ) + 2 * f := Int.toNat_of_nonneg hnonneg
  have hqA : A ≤ q := by omega
  have hqR : q ≤ R := by omega
  have hqEvenZ : (2 : ℤ) ∣ (q : ℤ) := by
    refine ⟨(R / 4 : ℕ) + f, ?_⟩
    dsimp [evenGridCenter] at hq
    omega
  have hqEven : 2 ∣ q := by exact_mod_cast hqEvenZ
  obtain ⟨T, hT, hsum⟩ := hgrid q hqA hqR hqEven
  refine ⟨T, hT, ?_⟩
  exact_mod_cast (show ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter R = 2 * f by
    rw [hsum, hq]
    omega)

/-- Simultaneous centered subset choices on disjoint reservoirs using `EvenIntervalGrid`. -/
theorem simultaneous_centered_evenIntervalGrid {E K : Type*} [Fintype E] [DecidableEq E] [DecidableEq K]
    (block : E → Finset K) (gap : K → ℕ) (A R : E → ℕ) (N : ℕ)
    (hdisj : ∀ e f, e ≠ f → Disjoint (block e) (block f))
    (hgrid : ∀ e, EvenIntervalGrid (block e) gap (A e) (R e))
    (hA : ∀ e, A e + 2 * (N / 2) ≤ evenGridCenter (R e)) :
    ∃ S₀ : Finset K,
      S₀ ⊆ Finset.univ.biUnion block ∧
      (∀ e, ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = evenGridCenter (R e)) ∧
      (∀ f : E → ℤ,
        (∀ e, -((N / 2 : ℕ) : ℤ) ≤ f e ∧ f e ≤ ((N / 2 : ℕ) : ℤ)) →
        ∃ S : Finset K, S ⊆ Finset.univ.biUnion block ∧
          ∀ e, ((∑ k ∈ S ∩ block e, gap k : ℕ) : ℤ) -
            ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = 2 * f e) := by
  have href : ∀ e, ∃ T : Finset K, T ⊆ block e ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter (R e) = 0 := by
    intro e
    simpa using centered_evenIntervalGrid (block e) gap (A e) (R e) N (hgrid e) (hA e) 0
      (by omega) (by omega)
  choose T₀ hT₀ hsum₀ using href
  let S₀ := Finset.univ.biUnion T₀
  have hS₀ : S₀ ⊆ Finset.univ.biUnion block := by
    intro k hk
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hT₀ e he⟩
  have hreference : ∀ e, ((∑ k ∈ S₀ ∩ block e, gap k : ℕ) : ℤ) = evenGridCenter (R e) := by
    intro e
    rw [biUnion_inter_block block T₀ hT₀ hdisj e]
    have hh := hsum₀ e
    omega
  refine ⟨S₀, hS₀, hreference, ?_⟩
  intro f hf
  have hex : ∀ e, ∃ T : Finset K, T ⊆ block e ∧
      ((∑ k ∈ T, gap k : ℕ) : ℤ) - evenGridCenter (R e) = 2 * f e := by
    intro e
    exact centered_evenIntervalGrid (block e) gap (A e) (R e) N (hgrid e) (hA e) (f e)
      (hf e).1 (hf e).2
  choose T hT hsum using hex
  let S := Finset.univ.biUnion T
  have hS : S ⊆ Finset.univ.biUnion block := by
    intro k hk
    obtain ⟨e, _, he⟩ := Finset.mem_biUnion.mp hk
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hT e he⟩
  refine ⟨S, hS, ?_⟩
  intro e
  rw [biUnion_inter_block block T hT hdisj e, hreference e]
  exact hsum e

/-- Two-network bounded integer flow realization from `EvenIntervalGrid` reservoirs,
preserving the exact reference-centering invoice `evenGridCenter (radius e)`. -/
theorem twoNetworks_realize_bounded_integer_flows_of_evenIntervalGrid {n : ℕ} {Er Ec : Type*}
    [Fintype Er] [DecidableEq Er] [Fintype Ec] [DecidableEq Ec]
    (a : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (rows cols : List (LayerPacking.Layer n))
    (hr : LayerPacking.PackedLayers reserved rows)
    (hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (reserved ∪ LayerPacking.layersSupport rows)) cols)
    (rowGap : Fin rows.length → Fin n → ℕ)
    (colGap : Fin cols.length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a ((rows.get i).1 e, (rows.get i).2 e) =
      entry a (e, (rows.get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a ((cols.get i).2 e, (cols.get i).1 e) =
      entry a ((cols.get i).2 e, e) + colGap i e)
    (rBlock : Er → Finset (Fin rows.length × Fin n))
    (cBlock : Ec → Finset (Fin cols.length × Fin n))
    (rA rRadius : Er → ℕ) (cA cRadius : Ec → ℕ)
    (rSource rTarget : Er → Fin n) (cSource cTarget : Ec → Fin n)
    (hrDisj : ∀ e f, e ≠ f → Disjoint (rBlock e) (rBlock f))
    (hcDisj : ∀ e f, e ≠ f → Disjoint (cBlock e) (cBlock f))
    (hrGrid : ∀ e, EvenIntervalGrid (rBlock e) (hr.rowPairs a rowGap hrowGap).gap (rA e) (rRadius e))
    (hcGrid : ∀ e, EvenIntervalGrid (cBlock e) (hc.columnPairs a colGap hcolGap).gap (cA e) (cRadius e))
    (hrEnd : ∀ e k, k ∈ rBlock e →
      (hr.rowPairs a rowGap hrowGap).low k = rSource e ∧
      (hr.rowPairs a rowGap hrowGap).high k = rTarget e)
    (hcEnd : ∀ e k, k ∈ cBlock e →
      (hc.columnPairs a colGap hcolGap).low k = cSource e ∧
      (hc.columnPairs a colGap hcolGap).high k = cTarget e)
    (N : ℕ)
    (hR : ∀ e, rA e + 2 * (N / 2) ≤ evenGridCenter (rRadius e))
    (hC : ∀ e, cA e + 2 * (N / 2) ≤ evenGridCenter (cRadius e)) :
    ∃ b₀ : Cell n ≃ Fin (n * n),
      (∀ r, (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
        ∑ e : Er, edgeTransfer rSource rTarget (fun e => evenGridCenter (rRadius e)) e r) ∧
      (∀ c, (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
        ∑ e : Ec, edgeTransfer cSource cTarget (fun e => evenGridCenter (cRadius e)) e c) ∧
      mainSum b₀ = mainSum a ∧ antiSum b₀ = antiSum a ∧
      (∀ c ∈ reserved, entry b₀ c = entry a c) ∧
      ∀ fr : Er → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fr e ∧ fr e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∀ fc : Ec → ℤ, (∀ e, -((N / 2 : ℕ) : ℤ) ≤ fc e ∧ fc e ≤ ((N / 2 : ℕ) : ℤ)) →
      ∃ b : Cell n ≃ Fin (n * n),
        (∀ r, (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
          2 * ∑ e : Er, edgeTransfer rSource rTarget fr e r) ∧
        (∀ c, (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
          2 * ∑ e : Ec, edgeTransfer cSource cTarget fc e c) ∧
        mainSum b = mainSum b₀ ∧ antiSum b = antiSum b₀ ∧
        (∀ c ∈ reserved, entry b c = entry b₀ c) ∧
        Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  let vr := hr.rowPairs a rowGap hrowGap
  let vc := hc.columnPairs a colGap hcolGap
  obtain ⟨Sr₀, hr₀, hrcenters, hrchoose⟩ :=
    simultaneous_centered_evenIntervalGrid rBlock vr.gap rA rRadius N hrDisj hrGrid hR
  obtain ⟨Sc₀, hc₀, hccenters, hcchoose⟩ :=
    simultaneous_centered_evenIntervalGrid cBlock vc.gap cA cRadius N hcDisj hcGrid hC
  obtain ⟨b₀, hbaseRows, hbaseCols, hbaseMain, hbaseAnti, hbaseFixed, _, _⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr₀ Sc₀
  have hrinvoice (r : Fin n) : (rowSum b₀ r : ℤ) - (rowSum a r : ℤ) =
      ∑ e : Er, edgeTransfer rSource rTarget (fun e => evenGridCenter (rRadius e)) e r := by
    rw [hbaseRows r]
    have hsum := rowNetwork_sum_by_reservoir vr rBlock rSource rTarget
      hrDisj hrEnd Sr₀ hr₀ r
    change (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e _
    have hcenter : (∑ k ∈ Sr₀ ∩ rBlock e, (vr.gap k : ℤ)) = evenGridCenter (rRadius e) := by
      exact_mod_cast hrcenters e
    simp only [hcenter, edgeTransfer]
  have hcinvoice (c : Fin n) : (columnSum b₀ c : ℤ) - (columnSum a c : ℤ) =
      ∑ e : Ec, edgeTransfer cSource cTarget (fun e => evenGridCenter (cRadius e)) e c := by
    rw [hbaseCols c]
    have hsum := rowNetwork_sum_by_reservoir vc cBlock cSource cTarget
      hcDisj hcEnd Sc₀ hc₀ c
    change (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro e _
    have hcenter : (∑ k ∈ Sc₀ ∩ cBlock e, (vc.gap k : ℤ)) = evenGridCenter (cRadius e) := by
      exact_mod_cast hccenters e
    simp only [hcenter, edgeTransfer]
  refine ⟨b₀, hrinvoice, hcinvoice, hbaseMain, hbaseAnti, hbaseFixed, ?_⟩
  intro fr hfr fc hfc
  obtain ⟨Sr, hrs, hrsums⟩ := hrchoose fr hfr
  obtain ⟨Sc, hcs, hcsums⟩ := hcchoose fc hfc
  obtain ⟨b, hrows, hcols, hm, ha, hfixed, hpool, hinj⟩ :=
    toggle_two_installed_networks a reserved rows cols hr hc rowGap colGap hrowGap hcolGap Sr Sc
  have hrsumsZ : ∀ e, (∑ k ∈ Sr ∩ rBlock e, (vr.gap k : ℤ)) -
      (∑ k ∈ Sr₀ ∩ rBlock e, (vr.gap k : ℤ)) = 2 * fr e := by
    intro e
    exact_mod_cast hrsums e
  have hcsumsZ : ∀ e, (∑ k ∈ Sc ∩ cBlock e, (vc.gap k : ℤ)) -
      (∑ k ∈ Sc₀ ∩ cBlock e, (vc.gap k : ℤ)) = 2 * fc e := by
    intro e
    exact_mod_cast hcsums e
  refine ⟨b, ?_, ?_, hm.trans hbaseMain.symm, ha.trans hbaseAnti.symm, ?_, hpool, hinj⟩
  · intro r
    have hdiff := rowNetwork_subset_difference vr rBlock rSource rTarget
      hrDisj hrEnd Sr Sr₀ hrs hr₀ (fun e => 2 * fr e) hrsumsZ r
    have hnew := hrows r
    have hbase := hbaseRows r
    change (∑ k ∈ Sr, layerTransfer rows rowGap k r) -
      (∑ k ∈ Sr₀, layerTransfer rows rowGap k r) = _ at hdiff
    have hlin : (rowSum b r : ℤ) - (rowSum b₀ r : ℤ) =
        ∑ e : Er, edgeTransfer rSource rTarget (fun e => 2 * fr e) e r := by omega
    exact hlin.trans (edgeTransfer_sum_scale_two rSource rTarget fr r)
  · intro c
    have hdiff := rowNetwork_subset_difference vc cBlock cSource cTarget
      hcDisj hcEnd Sc Sc₀ hcs hc₀ (fun e => 2 * fc e) hcsumsZ c
    have hnew := hcols c
    have hbase := hbaseCols c
    change (∑ k ∈ Sc, layerTransfer cols colGap k c) -
      (∑ k ∈ Sc₀, layerTransfer cols colGap k c) = _ at hdiff
    have hlin : (columnSum b c : ℤ) - (columnSum b₀ c : ℤ) =
        ∑ e : Ec, edgeTransfer cSource cTarget (fun e => 2 * fc e) e c := by omega
    exact hlin.trans (edgeTransfer_sum_scale_two cSource cTarget fc c)
  · intro c hc'
    exact (hfixed c hc').trans (hbaseFixed c hc').symm

/-! ## Equal-Gap Seed-Batch Extraction and Step-Grid Initialization -/

/-- If every element of `S` has gap equal to `g`, then `S` forms a `CompleteStepGrid`
of step `g` and radius `S.card * g`. -/
theorem completeStepGrid_of_equal_gaps {α : Type*}
    (S : Finset α) (gap : α → ℕ) (g : ℕ)
    (hgap : ∀ k ∈ S, gap k = g) :
    CompleteStepGrid S gap g (S.card * g) := by
  intro t ht hdvd
  rcases hdvd with ⟨m, rfl⟩
  by_cases hg : g = 0
  · subst hg
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  · have hm : m ≤ S.card := by
      have hpos : 0 < g := Nat.pos_of_ne_zero hg
      nlinarith
    obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq hm
    refine ⟨T, hT_sub, ?_⟩
    have hsum : ∑ k ∈ T, gap k = ∑ _k ∈ T, g :=
      Finset.sum_congr rfl (fun k hk => hgap k (hT_sub hk))
    rw [hsum, Finset.sum_const, smul_eq_mul, hT_card, mul_comm]

/-- If `K < S.card` and `bin` maps `S` into `Finset.range K`, then two distinct elements
of `S` fall in the same bin. -/
theorem exists_same_bin_pair_of_lt_card {S : Finset ℕ} {bin : ℕ → ℕ} {K : ℕ}
    (hbin : ∀ x ∈ S, bin x < K) (hcard : K < S.card) :
    ∃ u ∈ S, ∃ v ∈ S, u < v ∧ bin u = bin v := by
  have hsub : S ⊆ (Finset.range K).biUnion (fun b => S.filter (fun x => bin x = b)) := by
    intro x hx
    rw [Finset.mem_biUnion]
    exact ⟨bin x, Finset.mem_range.mpr (hbin x hx), Finset.mem_filter.mpr ⟨hx, rfl⟩⟩
  have hsum_lt : ∑ b ∈ Finset.range K, 1 < ∑ b ∈ Finset.range K, (S.filter (fun x => bin x = b)).card := by
    have h1 : ∑ b ∈ Finset.range K, 1 = K := by simp
    have h2 : S.card ≤ ∑ b ∈ Finset.range K, (S.filter (fun x => bin x = b)).card :=
      (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_lt_of_sum_lt hsum_lt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hb
  rw [Finset.mem_filter] at hx hy
  rcases lt_trichotomy x y with hlt | rfl | hgt
  · exact ⟨x, hx.1, y, hy.1, hlt, hx.2.trans hy.2.symm⟩
  · exact (hxy rfl).elim
  · exact ⟨y, hy.1, x, hx.1, hgt, hy.2.trans hx.2.symm⟩

/-- Extract `N` pairwise-disjoint ordered pairs in the same spatial bin when `K + 2 * N ≤ S.card`. -/
theorem exists_disjoint_same_bin_pairs (N : ℕ) :
    ∀ (S : Finset ℕ) (bin : ℕ → ℕ) (K : ℕ),
      (∀ x ∈ S, bin x < K) →
      K + 2 * N ≤ S.card →
      ∃ pairs : Fin N → ℕ × ℕ,
        (∀ i, (pairs i).1 ∈ S ∧ (pairs i).2 ∈ S ∧ (pairs i).1 < (pairs i).2 ∧
          bin (pairs i).1 = bin (pairs i).2) ∧
        (∀ i j, i ≠ j → Disjoint ({(pairs i).1, (pairs i).2} : Finset ℕ)
          ({(pairs j).1, (pairs j).2} : Finset ℕ)) := by
  induction N with
  | zero =>
    intro S bin K _ _
    exact ⟨fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ N ih =>
    intro S bin K hbin hcard
    have hlt : K < S.card := by omega
    obtain ⟨u, hu, v, hv, huv, hbin_uv⟩ := exists_same_bin_pair_of_lt_card hbin hlt
    let S' := (S.erase u).erase v
    have hne : u ≠ v := ne_of_lt huv
    have hv_er : v ∈ S.erase u := Finset.mem_erase.mpr ⟨hne.symm, hv⟩
    have hcard_S' : S'.card = S.card - 2 := by
      dsimp [S']
      rw [Finset.card_erase_of_mem hv_er, Finset.card_erase_of_mem hu]
      omega
    have hsub_S' : S' ⊆ S :=
      (Finset.erase_subset v (S.erase u)).trans (Finset.erase_subset u S)
    have hbin_S' : ∀ x ∈ S', bin x < K := fun x hx => hbin x (hsub_S' hx)
    have hcard' : K + 2 * N ≤ S'.card := by omega
    obtain ⟨rest, hrest, hdisj⟩ := ih S' bin K hbin_S' hcard'
    let pairs : Fin (N + 1) → ℕ × ℕ :=
      Fin.cons (u, v) rest
    refine ⟨pairs, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · exact ⟨hu, hv, huv, hbin_uv⟩
      · intro j
        have hj := hrest j
        exact ⟨hsub_S' hj.1, hsub_S' hj.2.1, hj.2.2.1, hj.2.2.2⟩
    · intro i j
      have hnotMem : ∀ k : Fin N, Disjoint ({u, v} : Finset ℕ) ({(rest k).1, (rest k).2} : Finset ℕ) := by
        intro k
        have hk1 : (rest k).1 ∈ S' := (hrest k).1
        have hk2 : (rest k).2 ∈ S' := (hrest k).2.1
        have hk1_ne_v : (rest k).1 ≠ v := (Finset.mem_erase.mp hk1).1
        have hk1_ne_u : (rest k).1 ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hk1).2).1
        have hk2_ne_v : (rest k).2 ≠ v := (Finset.mem_erase.mp hk2).1
        have hk2_ne_u : (rest k).2 ≠ u := (Finset.mem_erase.mp (Finset.mem_erase.mp hk2).2).1
        rw [Finset.disjoint_left]
        intro x hx hy
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl <;> rcases hy with h1 | h2
        · exact hk1_ne_u h1.symm
        · exact hk2_ne_u h2.symm
        · exact hk1_ne_v h1.symm
        · exact hk2_ne_v h2.symm
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · intro hij
          exact (hij rfl).elim
        · intro k _
          simpa [pairs] using hnotMem k
      · intro k
        refine Fin.cases ?_ ?_ j
        · intro _
          simpa [pairs] using (hnotMem k).symm
        · intro l hkl
          simpa [pairs] using hdisj k l (fun h => hkl (congrArg Fin.succ h))

/-- Equal-gap seed-batch pigeonhole: given a set `S` of odd integers in `[lo, lo + K * (2 * H0))`
with `K + 2 * (H0 * M) ≤ S.card`, there exist `h0 ∈ Finset.Icc 1 H0` and `M` pairwise-disjoint
pairs in `S` all having the exact same even gap `2 * h0`. -/
theorem exists_equal_gap_pairs_of_spatial_bins
    (S : Finset ℕ) (lo K H0 M : ℕ) (hH0 : 0 < H0)
    (hodd : ∀ x ∈ S, Odd x)
    (hinterval : ∀ x ∈ S, lo ≤ x ∧ x < lo + K * (2 * H0))
    (hcard : K + 2 * (H0 * M) ≤ S.card) :
    ∃ h0 ∈ Finset.Icc 1 H0, ∃ J : Finset (Fin (H0 * M)),
      ∃ pairs : Fin (H0 * M) → ℕ × ℕ,
        J.card = M ∧
        (∀ i ∈ J, (pairs i).1 ∈ S ∧ (pairs i).2 ∈ S ∧ (pairs i).1 < (pairs i).2 ∧
          (pairs i).2 - (pairs i).1 = 2 * h0) ∧
        (∀ i j, i ≠ j → Disjoint ({(pairs i).1, (pairs i).2} : Finset ℕ)
          ({(pairs j).1, (pairs j).2} : Finset ℕ)) := by
  let bin : ℕ → ℕ := fun x => (x - lo) / (2 * H0)
  have hbin : ∀ x ∈ S, bin x < K := by
    intro x hx
    have hx_int := hinterval x hx
    dsimp [bin]
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    omega
  obtain ⟨pairs, hpairs, hdisj⟩ := exists_disjoint_same_bin_pairs (H0 * M) S bin K hbin hcard
  let halfGap : Fin (H0 * M) → ℕ := fun i => ((pairs i).2 - (pairs i).1) / 2
  have hhalf_mem : ∀ i, halfGap i ∈ Finset.Icc 1 H0 := by
    intro i
    have hi := hpairs i
    obtain ⟨ku, hku⟩ := hodd (pairs i).1 hi.1
    obtain ⟨kv, hkv⟩ := hodd (pairs i).2 hi.2.1
    have hlt : (pairs i).1 < (pairs i).2 := hi.2.2.1
    have hbin_eq : ((pairs i).1 - lo) / (2 * H0) = ((pairs i).2 - lo) / (2 * H0) := hi.2.2.2
    have hlo1 : lo ≤ (pairs i).1 := (hinterval (pairs i).1 hi.1).1
    have hlo2 : lo ≤ (pairs i).2 := (hinterval (pairs i).2 hi.2.1).1
    have hdiff_lt : (pairs i).2 - (pairs i).1 < 2 * H0 := by
      have h1 := Nat.div_add_mod ((pairs i).1 - lo) (2 * H0)
      have h2 := Nat.div_add_mod ((pairs i).2 - lo) (2 * H0)
      rw [hbin_eq] at h1
      have hm1 : ((pairs i).1 - lo) % (2 * H0) < 2 * H0 := Nat.mod_lt _ (by omega)
      have hm2 : ((pairs i).2 - lo) % (2 * H0) < 2 * H0 := Nat.mod_lt _ (by omega)
      omega
    rw [Finset.mem_Icc]
    dsimp [halfGap]
    omega
  have hsum : ∑ h ∈ Finset.Icc 1 H0, M ≤
      ∑ h ∈ Finset.Icc 1 H0, (Finset.univ.filter (fun i : Fin (H0 * M) => halfGap i = h)).card := by
    have h1 : ∑ h ∈ Finset.Icc 1 H0, M = H0 * M := by
      simp [Nat.card_Icc]
    have h2 : ∑ h ∈ Finset.Icc 1 H0, (Finset.univ.filter (fun i : Fin (H0 * M) => halfGap i = h)).card =
        H0 * M := by
      rw [← Finset.card_biUnion]
      · have hbi : (Finset.Icc 1 H0).biUnion (fun h => Finset.univ.filter (fun i : Fin (H0 * M) => halfGap i = h)) =
            Finset.univ := by
          ext i
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
          exact ⟨halfGap i, hhalf_mem i, rfl⟩
        rw [hbi, Finset.card_univ, Fintype.card_fin]
      · intro h1 _ h2 _ hne
        change Disjoint _ _
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        rw [Finset.mem_filter] at hi1 hi2
        exact hne (hi1.2.symm.trans hi2.2)
    omega
  have hnonempty : (Finset.Icc 1 H0).Nonempty := Finset.nonempty_Icc.mpr hH0
  obtain ⟨h0, hh0, hle⟩ := Finset.exists_le_of_sum_le hnonempty hsum
  obtain ⟨J, hJ_sub, hJ_card⟩ := Finset.exists_subset_card_eq hle
  refine ⟨h0, hh0, J, pairs, hJ_card, ?_, hdisj⟩
  intro i hi
  have hi_filt := Finset.mem_filter.mp (hJ_sub hi)
  have hi_p := hpairs i
  obtain ⟨ku, hku⟩ := hodd (pairs i).1 hi_p.1
  obtain ⟨kv, hkv⟩ := hodd (pairs i).2 hi_p.2.1
  have hgap_eq : (pairs i).2 - (pairs i).1 = 2 * h0 := by
    have hh : ((pairs i).2 - (pairs i).1) / 2 = h0 := hi_filt.2
    omega
  exact ⟨hi_p.1, hi_p.2.1, hi_p.2.2.1, hgap_eq⟩

end
end Sude
