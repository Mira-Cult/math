import Sude.FastBinaryPrefixScan
import Sude.PrefixTruncation
import Sude.PrefixPairAllocation
import Sude.FC2KBridgeAndDiagonalHelpers
import Sude.BridgeChosenGrid
import Sude.BridgeOrdinaryNetworks
import Sude.FC2KWideInstallation

/-!
# FC2K Combined Role Selection & Even-Grid Extension (`FC2KRoleSelection`)

Combines:
1. Even-grid union and extension helpers (`completeEvenGrid_disjoint_union`,
   `completeEvenGrid_biUnion_fin`, `completeEvenGrid_extend_set`).
2. Pool lifting and multi-tile sliding-window intersection bounds on `GeneralPrefixProfile`.
3. Joint selection of Prefix (`P` stages), Bridge (`J ≤ J_max` stages), and Wide
   (`2 * W_diag` diagonal blocks + `W_ord` 3-layer stages) pool values, proving global
   endpoint injectivity and constructing both diagonal `CompleteEvenGrid`s and all `3 * n`
   ordinary edge `CompleteEvenGrid`s.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- Disjoint union of two `CompleteEvenGrid`s of even radii `R_A` and `R_B` is a
`CompleteEvenGrid` of even radius `R_A + R_B`. -/
theorem completeEvenGrid_disjoint_union {α : Type*} [DecidableEq α]
    {A B : Finset α} {g : α → ℕ} {R_A R_B : ℕ}
    (hdis : Disjoint A B) (hevenA : 2 ∣ R_A) (hevenB : 2 ∣ R_B)
    (hA : CompleteEvenGrid A g R_A) (hB : CompleteEvenGrid B g R_B) :
    CompleteEvenGrid (A ∪ B) g (R_A + R_B) ∧ 2 ∣ R_A + R_B := by
  refine ⟨?_, dvd_add hevenA hevenB⟩
  intro t ht heven_t
  by_cases hle : t ≤ R_A
  · obtain ⟨T₁, hT₁, hsum₁⟩ := hA t hle heven_t
    exact ⟨T₁, hT₁.trans Finset.subset_union_left, hsum₁⟩
  · have hgt : R_A < t := lt_of_not_ge hle
    have ht₂_le : t - R_A ≤ R_B := by omega
    have ht₂_even : 2 ∣ t - R_A := by
      obtain ⟨k₁, hk₁⟩ := hevenA
      obtain ⟨k₂, hk₂⟩ := heven_t
      exact ⟨k₂ - k₁, by omega⟩
    obtain ⟨T₁, hT₁, hsum₁⟩ := hA R_A le_rfl hevenA
    obtain ⟨T₂, hT₂, hsum₂⟩ := hB (t - R_A) ht₂_le ht₂_even
    have hdisT : Disjoint T₁ T₂ := hdis.mono hT₁ hT₂
    refine ⟨T₁ ∪ T₂, Finset.union_subset_union hT₁ hT₂, ?_⟩
    rw [Finset.sum_union hdisT, hsum₁, hsum₂]
    omega

/-- Pairwise-disjoint `Fin K` union of `CompleteEvenGrid`s of even radii `R u` forms a
`CompleteEvenGrid` of even radius `∑ u, R u`. -/
theorem completeEvenGrid_biUnion_fin {α : Type*} [DecidableEq α] {K : ℕ}
    (blocks : Fin K → Finset α) (g : α → ℕ) (R : Fin K → ℕ)
    (hdis : ∀ u v : Fin K, u ≠ v → Disjoint (blocks u) (blocks v))
    (heven : ∀ u : Fin K, 2 ∣ R u)
    (hgrid : ∀ u : Fin K, CompleteEvenGrid (blocks u) g (R u)) :
    CompleteEvenGrid (Finset.univ.biUnion blocks) g (∑ u : Fin K, R u) ∧
      2 ∣ ∑ u : Fin K, R u := by
  suffices haux : ∀ s : Finset (Fin K),
      CompleteEvenGrid (s.biUnion blocks) g (∑ u ∈ s, R u) ∧ 2 ∣ ∑ u ∈ s, R u from
    haux Finset.univ
  intro s
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, dvd_zero 2⟩
    intro t ht _
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    exact ⟨∅, Finset.empty_subset _, Finset.sum_empty⟩
  | @insert u s hu ih =>
    have hdis_us : Disjoint (blocks u) (s.biUnion blocks) := by
      apply Finset.disjoint_left.mpr
      intro x hxu hxs
      obtain ⟨v, hvs, hxv⟩ := Finset.mem_biUnion.mp hxs
      exact Finset.disjoint_left.mp (hdis u v (fun heq => hu (heq ▸ hvs))) hxu hxv
    obtain ⟨hg_u, he_u⟩ :=
      completeEvenGrid_disjoint_union hdis_us (heven u) ih.2 (hgrid u) ih.1
    rw [Finset.biUnion_insert, Finset.sum_insert hu]
    exact ⟨hg_u, he_u⟩

/-- Extending a `CompleteEvenGrid` `(A, R_A)` of even radius `R_A` by a disjoint finite set `B`
whose elements all have even gaps `≤ R_A` yields a `CompleteEvenGrid` of radius `R_A + ∑ x ∈ B, g x`. -/
theorem completeEvenGrid_extend_set {α : Type*} [DecidableEq α]
    {A B : Finset α} {g : α → ℕ} {R_A : ℕ}
    (hdis : Disjoint A B) (hevenA : 2 ∣ R_A) (hA : CompleteEvenGrid A g R_A)
    (hB : ∀ x ∈ B, 2 ∣ g x ∧ g x ≤ R_A) :
    CompleteEvenGrid (A ∪ B) g (R_A + ∑ x ∈ B, g x) ∧ 2 ∣ R_A + ∑ x ∈ B, g x := by
  induction B using Finset.induction_on with
  | empty =>
    simpa using ⟨hA, hevenA⟩
  | @insert x B hx ih =>
    have hdis_sub : Disjoint A B := hdis.mono_right (Finset.subset_insert x B)
    have hB_sub : ∀ y ∈ B, 2 ∣ g y ∧ g y ≤ R_A :=
      fun y hy => hB y (Finset.mem_insert_of_mem hy)
    obtain ⟨hgrid_prev, heven_prev⟩ := ih hdis_sub hB_sub
    have hx_not_A : x ∉ A :=
      fun hxA => Finset.disjoint_left.mp hdis hxA (Finset.mem_insert_self x B)
    have hx_fresh : x ∉ A ∪ B := by
      simp [hx_not_A, hx]
    have hxB := hB x (Finset.mem_insert_self x B)
    have hgx_le : g x ≤ R_A + ∑ y ∈ B, g y + 2 := by
      have : g x ≤ R_A := hxB.2
      omega
    have hstep := completeEvenGrid_insert (A ∪ B) g (R_A + ∑ y ∈ B, g y) x
      hx_fresh heven_prev hxB.1 hgx_le hgrid_prev
    have hunion_eq : A ∪ insert x B = insert x (A ∪ B) := by
      ext z; simp only [Finset.mem_union, Finset.mem_insert]; tauto
    rw [hunion_eq, Finset.sum_insert hx, ← Nat.add_assoc, Nat.add_right_comm R_A (g x)]
    exact ⟨hstep, dvd_add heven_prev hxB.1⟩

/-- Every value of a `GeneralPrefixProfile` with `maxHi ≤ poolMaximum n` lies in `pool n`. -/
theorem generalPrefixProfile_val_mem_pool {P qCert corrLo maxHi n : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hmaxHi : maxHi ≤ poolMaximum n)
    (x : (Fin P × Fin qCert) × Bool) :
    prof.values x ∈ pool n := by
  have hp5 := prof.prime_and_ge_five x
  have hb := prof.bounds x
  have hle : prof.values x ≤ poolMaximum n := le_trans hb.2 hmaxHi
  have hp_ne_2 : prof.values x ≠ 2 := by omega
  have hp_odd : prof.values x % 2 = 1 :=
    hp5.1.eq_two_or_odd.resolve_left hp_ne_2
  have hX0 : (0 : ℝ) ≤ (poolMaximum n : ℝ) := by positivity
  have hmem_ap : prof.values x ∈ apInterval 1 (poolMaximum n) 2 1 := by
    apply (mem_apInterval_iff 1 (poolMaximum n) 2 1 (by norm_num) hX0 _).mpr
    refine ⟨hp5.1, by exact_mod_cast (show 1 < prof.values x by omega),
      by exact_mod_cast hle, ?_⟩
    omega
  exact even_apInterval_subset_pool n 1 (poolMaximum n) 2 1 (by norm_num)
    hX0 le_rfl (by decide) (by decide) _ hmem_ap

/-- Lift `prof.values` into `pool n`. -/
def generalPrefixProfile_poolValues {P qCert corrLo maxHi n : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hmaxHi : maxHi ≤ poolMaximum n)
    (x : (Fin P × Fin qCert) × Bool) : pool n :=
  ⟨prof.values x, generalPrefixProfile_val_mem_pool prof hmaxHi x⟩

theorem generalPrefixProfile_poolValues_injective {P qCert corrLo maxHi n : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hmaxHi : maxHi ≤ poolMaximum n) :
    Function.Injective (generalPrefixProfile_poolValues prof hmaxHi) := by
  intro x y heq
  exact prof.injective (congrArg Subtype.val heq)

/-- Every prime in `apInterval lo hi 2 1` (`0 ≤ lo ≤ hi`) lies in `Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊`. -/
theorem apInterval_subset_Ioc_floor {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hbc : lo ≤ hi) :
    apInterval lo hi 2 1 ⊆ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ := by
  intro p hp
  have hp' := (mem_apInterval_iff lo hi 2 1 hlo0 (hlo0.trans hbc) p).mp hp
  exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hlo0).mpr hp'.2.1, Nat.le_floor hp'.2.2.1⟩

/-- Multi-tile 1-word (`49,152`-integer) sliding-window cap for `apInterval lo hi 2 1`. -/
theorem generalPrefixProfile_tiled_window_cap {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {wc : PrefixWindowCap} (hwc : wc ∈ prof.windowCaps) (hspan : 2 ≤ wc.spanWords)
    {V : Finset ℕ} (hV : V ⊆ Finset.univ.image prof.values)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hbc : lo ≤ hi) (tiles : ℕ)
    (hmin : corrLo + 49152 * wc.minWordIdx ≤ ⌊lo⌋₊)
    (hwidth : ⌊hi⌋₊ - ⌊lo⌋₊ ≤ tiles * ((wc.spanWords - 1) * 49152)) :
    (V ∩ apInterval lo hi 2 1).card ≤ tiles * wc.cap := by
  have hsub_ioc : V ∩ apInterval lo hi 2 1 ⊆
      (Finset.univ.image prof.values) ∩ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ :=
    Finset.inter_subset_inter hV (apInterval_subset_Ioc_floor hlo0 hbc)
  refine (Finset.card_le_card hsub_ioc).trans ?_
  set PSet := Finset.univ.image prof.values
  suffices haux : ∀ (t u v : ℕ), corrLo + 49152 * wc.minWordIdx ≤ u →
      v - u ≤ t * ((wc.spanWords - 1) * 49152) →
      (PSet ∩ Finset.Ioc u v).card ≤ t * wc.cap from
    haux tiles ⌊lo⌋₊ ⌊hi⌋₊ hmin hwidth
  intro t
  induction t with
  | zero =>
    intro u v _ hw
    have huv : v ≤ u := by omega
    have hemp : Finset.Ioc u v = ∅ := Finset.Ioc_eq_empty_of_le huv
    simp [hemp]
  | succ t ih =>
    intro u v hu hw
    set step := (wc.spanWords - 1) * 49152
    set mid := min v (u + step)
    have hsplit : Finset.Ioc u v ⊆ Finset.Ioc u mid ∪ Finset.Ioc mid v := by
      intro x hx
      have hx' := Finset.mem_Ioc.mp hx
      by_cases hxm : x ≤ mid
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨hx'.1, hxm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hxm, hx'.2⟩)
    have h1 : (PSet ∩ Finset.Ioc u mid).card ≤ wc.cap := by
      apply prof.window_cap wc hwc u mid hu
      have hmid_le : mid ≤ u + (wc.spanWords - 1) * 49152 := min_le_right _ _
      have hmul : (wc.spanWords - 1) * 49152 + 49152 = 49152 * wc.spanWords := by
        have : 1 ≤ wc.spanWords := by omega
        calc (wc.spanWords - 1) * 49152 + 49152
            = ((wc.spanWords - 1) + 1) * 49152 := by ring
          _ = 49152 * wc.spanWords := by rw [Nat.sub_add_cancel this, Nat.mul_comm]
      omega
    have h2 : (PSet ∩ Finset.Ioc mid v).card ≤ t * wc.cap := by
      by_cases hvm : v ≤ u + step
      · have hmid_v : mid = v := min_eq_left hvm
        rw [hmid_v, Finset.Ioc_self, Finset.inter_empty, Finset.card_empty]
        exact Nat.zero_le _
      · have hmid_u : mid = u + step := min_eq_right (le_of_not_ge hvm)
        apply ih mid v (by omega)
        rw [hmid_u]
        have : (t + 1) * step = step + t * step := by ring
        omega
    calc
      (PSet ∩ Finset.Ioc u v).card
          ≤ ((PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v)).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
            rcases Finset.mem_union.mp (hsplit hxI) with hL | hR
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, hL⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, hR⟩)
      _ ≤ (PSet ∩ Finset.Ioc u mid).card + (PSet ∩ Finset.Ioc mid v).card :=
            Finset.card_union_le _ _
      _ ≤ wc.cap + t * wc.cap := Nat.add_le_add h1 h2
      _ = (t + 1) * wc.cap := by ring

/-- Multi-tile 8-word (`393,216`-integer) sliding-window cap for `apInterval lo hi 2 1`. -/
theorem generalPrefixProfile_tiled_oct_window_cap {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {wc : PrefixWindowCap} (hwc : wc ∈ prof.octWindowCaps) (hspan : 2 ≤ wc.spanWords)
    {V : Finset ℕ} (hV : V ⊆ Finset.univ.image prof.values)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hbc : lo ≤ hi) (tiles : ℕ)
    (hmin : corrLo + 393216 * wc.minWordIdx ≤ ⌊lo⌋₊)
    (hwidth : ⌊hi⌋₊ - ⌊lo⌋₊ ≤ tiles * ((wc.spanWords - 1) * 393216)) :
    (V ∩ apInterval lo hi 2 1).card ≤ tiles * wc.cap := by
  have hsub_ioc : V ∩ apInterval lo hi 2 1 ⊆
      (Finset.univ.image prof.values) ∩ Finset.Ioc ⌊lo⌋₊ ⌊hi⌋₊ :=
    Finset.inter_subset_inter hV (apInterval_subset_Ioc_floor hlo0 hbc)
  refine (Finset.card_le_card hsub_ioc).trans ?_
  set PSet := Finset.univ.image prof.values
  suffices haux : ∀ (t u v : ℕ), corrLo + 393216 * wc.minWordIdx ≤ u →
      v - u ≤ t * ((wc.spanWords - 1) * 393216) →
      (PSet ∩ Finset.Ioc u v).card ≤ t * wc.cap from
    haux tiles ⌊lo⌋₊ ⌊hi⌋₊ hmin hwidth
  intro t
  induction t with
  | zero =>
    intro u v _ hw
    have huv : v ≤ u := by omega
    have hemp : Finset.Ioc u v = ∅ := Finset.Ioc_eq_empty_of_le huv
    simp [hemp]
  | succ t ih =>
    intro u v hu hw
    set step := (wc.spanWords - 1) * 393216
    set mid := min v (u + step)
    have hsplit : Finset.Ioc u v ⊆ Finset.Ioc u mid ∪ Finset.Ioc mid v := by
      intro x hx
      have hx' := Finset.mem_Ioc.mp hx
      by_cases hxm : x ≤ mid
      · exact Finset.mem_union_left _ (Finset.mem_Ioc.mpr ⟨hx'.1, hxm⟩)
      · exact Finset.mem_union_right _ (Finset.mem_Ioc.mpr ⟨lt_of_not_ge hxm, hx'.2⟩)
    have h1 : (PSet ∩ Finset.Ioc u mid).card ≤ wc.cap := by
      apply prof.oct_window_cap wc hwc u mid hu
      have hmid_le : mid ≤ u + (wc.spanWords - 1) * 393216 := min_le_right _ _
      have hmul : (wc.spanWords - 1) * 393216 + 393216 = 393216 * wc.spanWords := by
        have : 1 ≤ wc.spanWords := by omega
        calc (wc.spanWords - 1) * 393216 + 393216
            = ((wc.spanWords - 1) + 1) * 393216 := by ring
          _ = 393216 * wc.spanWords := by rw [Nat.sub_add_cancel this, Nat.mul_comm]
      omega
    have h2 : (PSet ∩ Finset.Ioc mid v).card ≤ t * wc.cap := by
      by_cases hvm : v ≤ u + step
      · have hmid_v : mid = v := min_eq_left hvm
        rw [hmid_v, Finset.Ioc_self, Finset.inter_empty, Finset.card_empty]
        exact Nat.zero_le _
      · have hmid_u : mid = u + step := min_eq_right (le_of_not_ge hvm)
        apply ih mid v (by omega)
        rw [hmid_u]
        have : (t + 1) * step = step + t * step := by ring
        omega
    calc
      (PSet ∩ Finset.Ioc u v).card
          ≤ ((PSet ∩ Finset.Ioc u mid) ∪ (PSet ∩ Finset.Ioc mid v)).card := by
            apply Finset.card_le_card
            intro x hx
            obtain ⟨hxP, hxI⟩ := Finset.mem_inter.mp hx
            rcases Finset.mem_union.mp (hsplit hxI) with hL | hR
            · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hxP, hL⟩)
            · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hxP, hR⟩)
      _ ≤ (PSet ∩ Finset.Ioc u mid).card + (PSet ∩ Finset.Ioc mid v).card :=
            Finset.card_union_le _ _
      _ ≤ wc.cap + t * wc.cap := Nat.add_le_add h1 h2
      _ = (t + 1) * wc.cap := by ring

/-- Zero overlap between `V ⊆ image prof.values` and `apInterval lo hi 2 1` when `(maxHi : ℝ) ≤ lo`. -/
theorem generalPrefixProfile_above_maxHi_cap {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    {V : Finset ℕ} (hV : V ⊆ Finset.univ.image prof.values)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hbc : lo ≤ hi)
    (habove : (maxHi : ℝ) ≤ lo) :
    (V ∩ apInterval lo hi 2 1).card = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨hvV, hvI⟩ := Finset.mem_inter.mp hv
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp (hV hvV)
  have hb : (prof.values x : ℝ) ≤ (maxHi : ℝ) := Nat.cast_le.mpr (prof.bounds x).2
  have hgt := ((mem_apInterval_iff lo hi 2 1 hlo0 (hlo0.trans hbc) (prof.values x)).mp hvI).2.1
  linarith

/-- Every selected Bridge endpoint at any stage `j < J` satisfies `X / 4 < p ≤ 3 * X / 4`
and each pair `(low, high)` satisfies `(97 / 100) * X < low + high ≤ (103 / 100) * X`
(in fact `(197 / 200) * X < low + high ≤ (203 / 200) * X`). -/
theorem bridgeStageBlock_pair_sum_and_window_bounds {n k J : ℕ}
    {initial : Finset ℕ} {radii : ℕ → ℝ} {batches : ℕ → List DoublePair}
    (hX : (0 : ℝ) < poolMaximum n)
    (hpos : ∀ j < J, 0 < radii j)
    (hvalid : ∀ j < J, bridgeStageValid n initial radii batches k j)
    (j : Fin J) (idx : Fin k) :
    let X : ℝ := poolMaximum n
    let b := bridgeStageBlock n initial radii batches k J hvalid j idx
    X / 4 < (b.low₁ : ℝ) ∧ (b.low₁ : ℝ) < X / 2 ∧
    X / 4 < (b.low₂ : ℝ) ∧ (b.low₂ : ℝ) < X / 2 ∧
    X / 2 < (b.high₁ : ℝ) ∧ (b.high₁ : ℝ) ≤ 3 * X / 4 ∧
    X / 2 < (b.high₂ : ℝ) ∧ (b.high₂ : ℝ) ≤ 3 * X / 4 ∧
    (197 / 200 : ℝ) * X < ((b.low₁ + b.high₁ : ℕ) : ℝ) ∧
    ((b.low₁ + b.high₁ : ℕ) : ℝ) ≤ (203 / 200 : ℝ) * X ∧
    (197 / 200 : ℝ) * X < ((b.low₂ + b.high₂ : ℕ) : ℝ) ∧
    ((b.low₂ + b.high₂ : ℕ) : ℝ) ≤ (203 / 200 : ℝ) * X := by
  let X : ℝ := poolMaximum n
  have hRj : 0 < radii j := hpos j j.isLt
  have hg := bridge_window_geometry X (radii j) hX hRj
  have hsp := bridgeSpan_properties X (radii j) hX hRj
  have hv := bridgeStageBlock_valid n initial radii batches k J hvalid j idx
  set b := bridgeStageBlock n initial radii batches k J hvalid j idx
  have hl₁ := (mem_apInterval_iff (bridgeLowStart X (radii j)) (bridgeLowEnd X (radii j)) 2 1
    (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) b.low₁).mp
    (Finset.mem_sdiff.mp hv.1).1
  have hl₂ := (mem_apInterval_iff (bridgeLowStart X (radii j)) (bridgeLowEnd X (radii j)) 2 1
    (by linarith [hg.2.2.1]) (by linarith [hg.2.2.1, hg.2.2.2.1]) b.low₂).mp
    (Finset.mem_sdiff.mp hv.2.1).1
  have hh₁ := (mem_apInterval_iff (bridgeHighStart X (radii j)) (bridgeHighEnd X (radii j)) 2 1
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b.high₁).mp
    (Finset.mem_sdiff.mp hv.2.2.1).1
  have hh₂ := (mem_apInterval_iff (bridgeHighStart X (radii j)) (bridgeHighEnd X (radii j)) 2 1
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1])
    (by linarith [hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2.1, hg.2.2.2.2.2.1]) b.high₂).mp
    (Finset.mem_sdiff.mp hv.2.2.2.1).1
  simp only [bridgeLowStart, bridgeLowEnd, bridgeHighStart, bridgeHighEnd, bridgeWidth] at hl₁ hl₂ hh₁ hh₂
  refine ⟨by linarith [hl₁.2.1, hsp.2.2], by linarith [hl₁.2.2.1, hsp.1],
    by linarith [hl₂.2.1, hsp.2.2], by linarith [hl₂.2.2.1, hsp.1],
    by linarith [hh₁.2.1, hsp.1], by linarith [hh₁.2.2.1, hsp.2.2],
    by linarith [hh₂.2.1, hsp.1], by linarith [hh₂.2.2.1, hsp.2.2],
    ?_, ?_, ?_, ?_⟩
  · rw [Nat.cast_add]; linarith [hl₁.2.1, hh₁.2.1, hsp.2.2]
  · rw [Nat.cast_add]; linarith [hl₁.2.2.1, hh₁.2.2.1, hsp.2.2]
  · rw [Nat.cast_add]; linarith [hl₂.2.1, hh₂.2.1, hsp.2.2]
  · rw [Nat.cast_add]; linarith [hl₂.2.2.1, hh₂.2.2.1, hsp.2.2]

/-- Prescribed-pool mean `(Lucas.poolTotal n : ℝ) / (n * n)`. -/
def fc2kPoolMean (n : ℕ) : ℝ :=
  (Lucas.poolTotal n : ℝ) / ((n * n : ℕ) : ℝ)

/-- Selected Prefix + Bridge + Wide role package before physical square placement. -/
structure FC2KSelectedRoles (n P qCert corrLo maxHi J_max W_ord W_diag N_bins : ℕ) (δ : ℝ)
    (prof : GeneralPrefixProfile P qCert corrLo maxHi) where
  J : ℕ
  hJ_le : J ≤ J_max
  rectVal : Fin (24 * P + 24 * J + 2 * W_diag) × Fin 4 → pool n
  rowVal : Fin ((P + J + W_ord) * 3) × (Fin n × Bool) → pool n
  colVal : Fin ((P + J + W_ord) * 3) × (Fin n × Bool) → pool n
  rectGap : Fin (24 * P + 24 * J + 2 * W_diag) → ℕ
  ordGap : Fin ((P + J + W_ord) * 3) → Fin n → ℕ
  hrect_inj : Function.Injective rectVal
  hrow_inj : Function.Injective rowVal
  hcol_inj : Function.Injective colVal
  hrow_ne_col : ∀ x y, (rowVal x).val ≠ (colVal y).val
  hrow_ne_rect : ∀ x y, (rowVal x).val ≠ (rectVal y).val
  hcol_ne_rect : ∀ x y, (colVal x).val ≠ (rectVal y).val
  hrect_gap : ∀ t : Fin (24 * P + 24 * J + 2 * W_diag),
    0 < rectGap t ∧ 2 ∣ rectGap t ∧
    (rectVal (t, 1)).val = (rectVal (t, 0)).val + rectGap t ∧
    (rectVal (t, 2)).val = (rectVal (t, 3)).val + rectGap t
  hrow_gap : ∀ i e, (rowVal (i, (e, true))).val = (rowVal (i, (e, false))).val + ordGap i e
  hcol_gap : ∀ i e, (colVal (i, (e, true))).val = (colVal (i, (e, false))).val + ordGap i e
  Rm : ℕ
  Ra : ℕ
  hm_grid : CompleteEvenGrid
    (Finset.univ.filter (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = true))
    rectGap Rm
  ha_grid : CompleteEvenGrid
    (Finset.univ.filter (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = false))
    rectGap Ra
  hRm_sum : Rm = ∑ t ∈ Finset.univ.filter
    (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = true), rectGap t
  hRa_sum : Ra = ∑ t ∈ Finset.univ.filter
    (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = false), rectGap t
  hRm_lower : 12 * (poolMaximum n : ℝ) +
    (W_diag : ℝ) * (2 * fc2kPoolMean n - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)) ≤
      (Rm : ℝ)
  hRa_lower : 12 * (poolMaximum n : ℝ) +
    (W_diag : ℝ) * (2 * fc2kPoolMean n - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)) ≤
      (Ra : ℝ)
  edgeRadius : Fin 3 × Fin n → ℕ
  hedge_grid : ∀ e : Fin 3 × Fin n,
    CompleteEvenGrid
      ((Finset.univ : Finset (Fin (P + J + W_ord))).image
        (fun s => (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2)))
      (fun k => ordGap k.1 k.2) (edgeRadius e)
  hedge_sum : ∀ e : Fin 3 × Fin n,
    (∑ k ∈ (Finset.univ : Finset (Fin (P + J + W_ord))).image
        (fun s => (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2)),
      ordGap k.1 k.2) = edgeRadius e
  hedge_lower : ∀ e : Fin 3 × Fin n,
    (poolMaximum n : ℝ) +
      (W_ord : ℝ) * (2 * fc2kPoolMean n - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)) ≤
        (edgeRadius e : ℝ)
  V_pref : Finset ℕ
  V_br : Finset ℕ
  V_wide : Finset ℕ
  hV_pref_sub : V_pref ⊆ Finset.univ.image prof.values
  hV_pref_card : V_pref.card = 12 * P * (n + 8)
  hV_br_card : V_br.card ≤ 4 * J * (24 + 3 * n)
  hV_wide_out : ∀ v ∈ V_wide,
    (v : ℝ) ≤ ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) ∨
      2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) < (v : ℝ)
  hrole_union :
    (Finset.univ.image (fun x => (rectVal x).val) ∪
      Finset.univ.image (fun x => (rowVal x).val) ∪
      Finset.univ.image (fun x => (colVal x).val)) = V_pref ∪ V_br ∪ V_wide
  hrole_sum_upper :
    ((∑ x, ((rectVal x).val : ℝ)) + (∑ x, ((rowVal x).val : ℝ)) + (∑ x, ((colVal x).val : ℝ))) ≤
      (12 * P * (n + 8) : ℝ) * (maxHi : ℝ) +
      (6 * J * (n + 8) : ℝ) * ((203 / 200 : ℝ) * (poolMaximum n : ℝ)) +
      ((2 * W_diag + W_ord * (3 * n)) : ℝ) * (4 * fc2kPoolMean n + 2 * δ * (poolMaximum n : ℝ))
  hrole_sum_lower :
    (12 * P * (n + 8) : ℝ) * (corrLo : ℝ) +
      (6 * J * (n + 8) : ℝ) * ((197 / 200 : ℝ) * (poolMaximum n : ℝ)) +
      ((2 * W_diag + W_ord * (3 * n)) : ℝ) * (4 * fc2kPoolMean n - 2 * δ * (poolMaximum n : ℝ)) ≤
      ((∑ x, ((rectVal x).val : ℝ)) + (∑ x, ((rowVal x).val : ℝ)) + (∑ x, ((colVal x).val : ℝ)))
  hrect_pair_bounds : ∀ t : Fin (24 * P + 24 * J + 2 * W_diag),
    let X : ℝ := poolMaximum n
    let m := fc2kPoolMean n
    let loB := min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))
    let hiB := max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))
    loB ≤ (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ∧
    (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ≤ hiB ∧
    loB ≤ (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ∧
    (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ≤ hiB
  hdiag_mid_diff :
    |(∑ t ∈ Finset.univ.filter
        (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = true),
        (((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) / 2)) -
     (∑ t ∈ Finset.univ.filter
        (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = false),
        (((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) / 2))| ≤
      ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 25 : ℝ) * (J : ℝ) * (poolMaximum n : ℝ) +
      (W_diag : ℝ) * δ * (poolMaximum n : ℝ)
  hord_stage_width : ∀ (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : Fin (P + J + W_ord) → Fin 3 → Fin n),
    |(∑ s : Fin (P + J + W_ord), ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
         ((((rowVal (idx, (a₁ s l, false))).val + (rowVal (idx, (a₁ s l, true))) : ℕ) : ℝ) +
          (((rowVal (idx, (b₁ s l, false))).val + (rowVal (idx, (b₁ s l, true))) : ℕ) : ℝ)) / 2 +
         ((((colVal (idx, (c₁ s l, false))).val + (colVal (idx, (c₁ s l, true))) : ℕ) : ℝ) +
          (((colVal (idx, (d₁ s l, false))).val + (colVal (idx, (d₁ s l, true))) : ℕ) : ℝ)) / 2)) -
     (∑ s : Fin (P + J + W_ord), ∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
         ((((rowVal (idx, (a₂ s l, false))).val + (rowVal (idx, (a₂ s l, true))) : ℕ) : ℝ) +
          (((rowVal (idx, (b₂ s l, false))).val + (rowVal (idx, (b₂ s l, true))) : ℕ) : ℝ)) / 2 +
         ((((colVal (idx, (c₂ s l, false))).val + (colVal (idx, (c₂ s l, true))) : ℕ) : ℝ) +
          (((colVal (idx, (d₂ s l, false))).val + (colVal (idx, (d₂ s l, true))) : ℕ) : ℝ)) / 2))| ≤
      ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
      (9 / 50 : ℝ) * (J : ℝ) * (poolMaximum n : ℝ) +
      12 * (W_ord : ℝ) * δ * (poolMaximum n : ℝ)

/-- Combined slot domain for all `L` diagonal rectangles and both `3 * S` ordinary layer networks. -/
abbrev FC2KSlotDomain (n P J W_ord W_diag : ℕ) :=
  (Fin (24 * P + 24 * J + 2 * W_diag) × Fin 4) ⊕
    ((Fin ((P + J + W_ord) * 3) × (Fin n × Bool)) ⊕
     (Fin ((P + J + W_ord) * 3) × (Fin n × Bool)))

/-- Combined source domain for Prefix (`6*(n+8)` pairs/stage), Bridge (`24+3*n` blocks/stage),
and Wide (`2*W_diag + W_ord*(3*n)` blocks). -/
abbrev FC2KSourceDomain (n P J W_ord W_diag : ℕ) :=
  ((Fin P × Fin (6 * (n + 8))) × Bool) ⊕
    (((Fin J × Fin (24 + 3 * n)) × Fin 4) ⊕
     (Fin (2 * W_diag + W_ord * (3 * n)) × Fin 4))

/-- Explicit corner index for row (`false`) or column (`true`) network ordinary pairs. -/
def fc2kOrdCorner (net side : Bool) : Fin 4 :=
  match net, side with
  | false, false => 0
  | false, true  => 1
  | true,  true  => 2
  | true,  false => 3

/-- Explicit slot-to-source map matching rectangle and ordinary network slots to Prefix, Bridge, and Wide sources. -/
def fc2kSlotToSource {n P J W_ord W_diag : ℕ} :
    FC2KSlotDomain n P J W_ord W_diag → FC2KSourceDomain n P J W_ord W_diag
  | .inl (t, side) =>
      if htP : t.val < 24 * P then
        let j : Fin P := ⟨t.val / 24, by omega⟩
        let v := t.val % 24
        let c := prefixCornerCode side
        .inl ((j, ⟨2 * v + c.1.val, by have := c.1.isLt; omega⟩), c.2)
      else if htB : t.val < 24 * P + 24 * J then
        let r := t.val - 24 * P
        let j : Fin J := ⟨r / 24, by omega⟩
        let v : Fin (24 + 3 * n) := ⟨r % 24, by omega⟩
        .inr (.inl ((j, v), side))
      else
        let w : Fin (2 * W_diag + W_ord * (3 * n)) := ⟨t.val - (24 * P + 24 * J), by omega⟩
        .inr (.inr (w, side))
  | .inr (.inl (i, (e, side))) =>
      let p : Fin (P + J + W_ord) × Fin 3 := finProdFinEquiv.symm i
      if hsP : p.1.val < P then
        .inl ((⟨p.1.val, hsP⟩, ⟨48 + p.2.val * n + e.val, by have := p.2.isLt; have := e.isLt; nlinarith⟩), side)
      else if hsB : p.1.val < P + J then
        .inr (.inl ((⟨p.1.val - P, by omega⟩, ⟨24 + p.2.val * n + e.val, by have := p.2.isLt; have := e.isLt; nlinarith⟩),
          fc2kOrdCorner false side))
      else
        .inr (.inr (⟨2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val, by
          have h1 : p.1.val - (P + J) + 1 ≤ W_ord := by have := p.1.isLt; omega
          have := p.2.isLt; have := e.isLt; nlinarith⟩,
          fc2kOrdCorner false side))
  | .inr (.inr (i, (e, side))) =>
      let p : Fin (P + J + W_ord) × Fin 3 := finProdFinEquiv.symm i
      if hsP : p.1.val < P then
        .inl ((⟨p.1.val, hsP⟩, ⟨48 + (3 + p.2.val) * n + e.val, by have := p.2.isLt; have := e.isLt; nlinarith⟩), side)
      else if hsB : p.1.val < P + J then
        .inr (.inl ((⟨p.1.val - P, by omega⟩, ⟨24 + p.2.val * n + e.val, by have := p.2.isLt; have := e.isLt; nlinarith⟩),
          fc2kOrdCorner true side))
      else
        .inr (.inr (⟨2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val, by
          have h1 : p.1.val - (P + J) + 1 ≤ W_ord := by have := p.1.isLt; omega
          have := p.2.isLt; have := e.isLt; nlinarith⟩,
          fc2kOrdCorner true side))

/-- Left-inverse helper from `FC2KSourceDomain` back to `FC2KSlotDomain` when `0 < n`. -/
private def fc2kSourceToSlot {n P J W_ord W_diag : ℕ} (hn : 0 < n) :
    FC2KSourceDomain n P J W_ord W_diag → FC2KSlotDomain n P J W_ord W_diag
  | .inl ((j, q), b) =>
      if hq : q.val < 48 then
        let c : Fin 4 := if q.val % 2 = 0 then (if b then 1 else 0) else (if b then 2 else 3)
        .inl (⟨24 * j.val + q.val / 2, by have := j.isLt; omega⟩, c)
      else
        let u := q.val - 48
        let kl := u / n
        let e : Fin n := ⟨u % n, Nat.mod_lt u hn⟩
        have hkl6 : kl < 6 := (Nat.div_lt_iff_lt_mul hn).mpr (by have := q.isLt; omega)
        if hkl3 : kl < 3 then
          .inr (.inl (finProdFinEquiv (⟨j.val, by have := j.isLt; omega⟩, ⟨kl, hkl3⟩), (e, b)))
        else
          .inr (.inr (finProdFinEquiv (⟨j.val, by have := j.isLt; omega⟩, ⟨kl - 3, by omega⟩), (e, b)))
  | .inr (.inl ((j, blk), c)) =>
      if hb : blk.val < 24 then
        .inl (⟨24 * P + 24 * j.val + blk.val, by have := j.isLt; omega⟩, c)
      else
        let u := blk.val - 24
        let l : Fin 3 := ⟨u / n, (Nat.div_lt_iff_lt_mul hn).mpr (by have := blk.isLt; omega)⟩
        let e : Fin n := ⟨u % n, Nat.mod_lt u hn⟩
        let idx := finProdFinEquiv (⟨P + j.val, by have := j.isLt; omega⟩, l)
        if c = 0 then .inr (.inl (idx, (e, false)))
        else if c = 1 then .inr (.inl (idx, (e, true)))
        else if c = 2 then .inr (.inr (idx, (e, true)))
        else .inr (.inr (idx, (e, false)))
  | .inr (.inr (w, c)) =>
      if hw : w.val < 2 * W_diag then
        .inl (⟨24 * P + 24 * J + w.val, by omega⟩, c)
      else
        let u := w.val - 2 * W_diag
        have h3n : 0 < 3 * n := by omega
        let wo : Fin W_ord := ⟨u / (3 * n), (Nat.div_lt_iff_lt_mul h3n).mpr (by have := w.isLt; omega)⟩
        let rem := u % (3 * n)
        let l : Fin 3 := ⟨rem / n, (Nat.div_lt_iff_lt_mul hn).mpr (Nat.mod_lt u h3n)⟩
        let e : Fin n := ⟨rem % n, Nat.mod_lt rem hn⟩
        let idx := finProdFinEquiv (⟨P + J + wo.val, by have := wo.isLt; omega⟩, l)
        if c = 0 then .inr (.inl (idx, (e, false)))
        else if c = 1 then .inr (.inl (idx, (e, true)))
        else if c = 2 then .inr (.inr (idx, (e, true)))
        else .inr (.inr (idx, (e, false)))

theorem fc2kSlotToSource_bijective {n : ℕ} (hn : 0 < n) (P J W_ord W_diag : ℕ) :
    Function.Bijective (fc2kSlotToSource (n := n) (P := P) (J := J) (W_ord := W_ord) (W_diag := W_diag)) := by
  have hleft : Function.LeftInverse
      (fc2kSourceToSlot (P := P) (J := J) (W_ord := W_ord) (W_diag := W_diag) hn)
      (fc2kSlotToSource (n := n) (P := P) (J := J) (W_ord := W_ord) (W_diag := W_diag)) := by
    intro x
    rcases x with ⟨t, side⟩ | (⟨i, e, side⟩ | ⟨i, e, side⟩)
    · dsimp only [fc2kSlotToSource]
      split_ifs with htP htB
      · dsimp only [fc2kSourceToSlot]
        have hq48 : 2 * (t.val % 24) + (prefixCornerCode side).1.val < 48 := by
          have := (prefixCornerCode side).1.isLt; omega
        rw [dif_pos hq48]
        apply congrArg Sum.inl; apply Prod.ext
        · apply Fin.ext; dsimp only
          fin_cases side <;> simp [prefixCornerCode] <;> omega
        · fin_cases side <;> simp [prefixCornerCode]
      · dsimp only [fc2kSourceToSlot]
        have hb24 : (t.val - 24 * P) % 24 < 24 := Nat.mod_lt _ (by decide)
        rw [dif_pos hb24]
        exact congrArg Sum.inl (Prod.ext (Fin.ext (by dsimp only; omega)) rfl)
      · dsimp only [fc2kSourceToSlot]
        have hw : t.val - (24 * P + 24 * J) < 2 * W_diag := by have := t.isLt; omega
        rw [dif_pos hw]
        exact congrArg Sum.inl (Prod.ext (Fin.ext (by dsimp only; omega)) rfl)
    · dsimp only [fc2kSlotToSource]
      let p := finProdFinEquiv.symm i
      have hp_eq : finProdFinEquiv p = i := finProdFinEquiv.apply_symm_apply i
      split_ifs with hsP hsB
      · dsimp only [fc2kSourceToSlot]
        have hnot48 : ¬ (48 + p.2.val * n + e.val < 48) := by omega
        rw [dif_neg hnot48]
        have hsub : 48 + p.2.val * n + e.val - 48 = e.val + n * p.2.val := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]; ring
        have hdiv : (48 + p.2.val * n + e.val - 48) / n = p.2.val := by
          rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have hmod : (48 + p.2.val * n + e.val - 48) % n = e.val := by
          rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        have hkl3 : (48 + p.2.val * n + e.val - 48) / n < 3 := by rw [hdiv]; exact p.2.isLt
        rw [dif_pos hkl3]
        apply congrArg Sum.inr; apply congrArg Sum.inl; apply Prod.ext
        · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
          exact Prod.ext (Fin.ext rfl) (Fin.ext hdiv)
        · exact Prod.ext (Fin.ext hmod) rfl
      · dsimp only [fc2kSourceToSlot]
        have hnot24 : ¬ (24 + p.2.val * n + e.val < 24) := by omega
        rw [dif_neg hnot24]
        have hsub : 24 + p.2.val * n + e.val - 24 = e.val + n * p.2.val := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]; ring
        have hdiv : (24 + p.2.val * n + e.val - 24) / n = p.2.val := by
          rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have hmod : (24 + p.2.val * n + e.val - 24) % n = e.val := by
          rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        cases side <;> simp only [fc2kOrdCorner, ↓reduceIte, show (1 : Fin 4) ≠ 0 by decide]
        · apply congrArg Sum.inr; apply congrArg Sum.inl; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p]; omega)) (Fin.ext hdiv)
          · exact Prod.ext (Fin.ext hmod) rfl
        · apply congrArg Sum.inr; apply congrArg Sum.inl; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p]; omega)) (Fin.ext hdiv)
          · exact Prod.ext (Fin.ext hmod) rfl
      · dsimp only [fc2kSourceToSlot]
        have hnotW : ¬ (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val < 2 * W_diag) := by omega
        rw [dif_neg hnotW]
        have h3n : 0 < 3 * n := by omega
        have hlt_rem : p.2.val * n + e.val < 3 * n := by have := p.2.isLt; have := e.isLt; nlinarith
        have hu_eq : 2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag =
            (p.2.val * n + e.val) + (3 * n) * (p.1.val - (P + J)) := by
          rw [Nat.add_assoc (2 * W_diag), Nat.add_assoc (2 * W_diag), Nat.add_sub_cancel_left]; ring
        have hwo : (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag) / (3 * n) =
            p.1.val - (P + J) := by
          rw [hu_eq, Nat.add_mul_div_left _ _ h3n, Nat.div_eq_of_lt hlt_rem, Nat.zero_add]
        have hrem : (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag) % (3 * n) =
            p.2.val * n + e.val := by
          rw [hu_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
        have hl_div : (p.2.val * n + e.val) / n = p.2.val := by
          rw [show p.2.val * n + e.val = e.val + n * p.2.val by ring,
            Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have he_mod : (p.2.val * n + e.val) % n = e.val := by
          rw [show p.2.val * n + e.val = e.val + n * p.2.val by ring,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        cases side <;> simp only [fc2kOrdCorner, ↓reduceIte, show (1 : Fin 4) ≠ 0 by decide]
        · apply congrArg Sum.inr; apply congrArg Sum.inl; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p] at hwo ⊢; rw [hwo]; omega))
              (Fin.ext (by dsimp only; rw [hrem, hl_div]))
          · exact Prod.ext (Fin.ext (by dsimp only; rw [hrem, he_mod])) rfl
        · apply congrArg Sum.inr; apply congrArg Sum.inl; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p] at hwo ⊢; rw [hwo]; omega))
              (Fin.ext (by dsimp only; rw [hrem, hl_div]))
          · exact Prod.ext (Fin.ext (by dsimp only; rw [hrem, he_mod])) rfl
    · dsimp only [fc2kSlotToSource]
      let p := finProdFinEquiv.symm i
      have hp_eq : finProdFinEquiv p = i := finProdFinEquiv.apply_symm_apply i
      split_ifs with hsP hsB
      · dsimp only [fc2kSourceToSlot]
        have hnot48 : ¬ (48 + (3 + p.2.val) * n + e.val < 48) := by omega
        rw [dif_neg hnot48]
        have hsub : 48 + (3 + p.2.val) * n + e.val - 48 = e.val + n * (3 + p.2.val) := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]; ring
        have hdiv : (48 + (3 + p.2.val) * n + e.val - 48) / n = 3 + p.2.val := by
          rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have hmod : (48 + (3 + p.2.val) * n + e.val - 48) % n = e.val := by
          rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        have hkl3 : ¬ ((48 + (3 + p.2.val) * n + e.val - 48) / n < 3) := by rw [hdiv]; omega
        rw [dif_neg hkl3]
        apply congrArg Sum.inr; apply congrArg Sum.inr; apply Prod.ext
        · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
          exact Prod.ext (Fin.ext rfl) (Fin.ext (by dsimp only; rw [hdiv]; omega))
        · exact Prod.ext (Fin.ext hmod) rfl
      · dsimp only [fc2kSourceToSlot]
        have hnot24 : ¬ (24 + p.2.val * n + e.val < 24) := by omega
        rw [dif_neg hnot24]
        have hsub : 24 + p.2.val * n + e.val - 24 = e.val + n * p.2.val := by
          rw [Nat.add_assoc, Nat.add_sub_cancel_left]; ring
        have hdiv : (24 + p.2.val * n + e.val - 24) / n = p.2.val := by
          rw [hsub, Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have hmod : (24 + p.2.val * n + e.val - 24) % n = e.val := by
          rw [hsub, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        cases side <;> simp only [fc2kOrdCorner, ↓reduceIte,
          show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide,
          show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
        · apply congrArg Sum.inr; apply congrArg Sum.inr; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p]; omega)) (Fin.ext hdiv)
          · exact Prod.ext (Fin.ext hmod) rfl
        · apply congrArg Sum.inr; apply congrArg Sum.inr; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p]; omega)) (Fin.ext hdiv)
          · exact Prod.ext (Fin.ext hmod) rfl
      · dsimp only [fc2kSourceToSlot]
        have hnotW : ¬ (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val < 2 * W_diag) := by omega
        rw [dif_neg hnotW]
        have h3n : 0 < 3 * n := by omega
        have hlt_rem : p.2.val * n + e.val < 3 * n := by have := p.2.isLt; have := e.isLt; nlinarith
        have hu_eq : 2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag =
            (p.2.val * n + e.val) + (3 * n) * (p.1.val - (P + J)) := by
          rw [Nat.add_assoc (2 * W_diag), Nat.add_assoc (2 * W_diag), Nat.add_sub_cancel_left]; ring
        have hwo : (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag) / (3 * n) =
            p.1.val - (P + J) := by
          rw [hu_eq, Nat.add_mul_div_left _ _ h3n, Nat.div_eq_of_lt hlt_rem, Nat.zero_add]
        have hrem : (2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val - 2 * W_diag) % (3 * n) =
            p.2.val * n + e.val := by
          rw [hu_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt_rem]
        have hl_div : (p.2.val * n + e.val) / n = p.2.val := by
          rw [show p.2.val * n + e.val = e.val + n * p.2.val by ring,
            Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt e.isLt, Nat.zero_add]
        have he_mod : (p.2.val * n + e.val) % n = e.val := by
          rw [show p.2.val * n + e.val = e.val + n * p.2.val by ring,
            Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
        cases side <;> simp only [fc2kOrdCorner, ↓reduceIte,
          show (3 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 1 by decide, show (3 : Fin 4) ≠ 2 by decide,
          show (2 : Fin 4) ≠ 0 by decide, show (2 : Fin 4) ≠ 1 by decide]
        · apply congrArg Sum.inr; apply congrArg Sum.inr; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p] at hwo ⊢; rw [hwo]; omega))
              (Fin.ext (by dsimp only; rw [hrem, hl_div]))
          · exact Prod.ext (Fin.ext (by dsimp only; rw [hrem, he_mod])) rfl
        · apply congrArg Sum.inr; apply congrArg Sum.inr; apply Prod.ext
          · refine Eq.trans (congrArg finProdFinEquiv ?_) hp_eq
            exact Prod.ext (Fin.ext (by dsimp only [p] at hwo ⊢; rw [hwo]; omega))
              (Fin.ext (by dsimp only; rw [hrem, hl_div]))
          · exact Prod.ext (Fin.ext (by dsimp only; rw [hrem, he_mod])) rfl
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨hleft.injective, ?_⟩
  simp only [FC2KSlotDomain, FC2KSourceDomain, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  ring

/-- Six-block monotone telescoping bound for one Prefix stage `j : Fin P`. -/
theorem fc2k_prefix_stage_six_blocks_width {P qCert corrLo maxHi n : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hq : 6 * (n + 8) ≤ qCert) (hn : 0 < n) (j : Fin P)
    (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : Fin 3 → Fin n) :
    let pairSum (idx : Fin (6 * (n + 8))) : ℝ :=
      ((prof.values ((j, Fin.castLE hq idx), false) +
        prof.values ((j, Fin.castLE hq idx), true) : ℕ) : ℝ)
    let rIdx (l : Fin 3) (e : Fin n) : Fin (6 * (n + 8)) :=
      ⟨48 + l.val * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
    let cIdx (l : Fin 3) (e : Fin n) : Fin (6 * (n + 8)) :=
      ⟨48 + (3 + l.val) * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
    |(∑ l : Fin 3, ((pairSum (rIdx l (a₁ l)) + pairSum (rIdx l (b₁ l))) / 2 +
        (pairSum (cIdx l (c₁ l)) + pairSum (cIdx l (d₁ l))) / 2)) -
     (∑ l : Fin 3, ((pairSum (rIdx l (a₂ l)) + pairSum (rIdx l (b₂ l))) / 2 +
        (pairSum (cIdx l (c₂ l)) + pairSum (cIdx l (d₂ l))) / 2))| ≤
      2 * ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
  let lowR (idx : Fin (6 * (n + 8))) : ℝ :=
    (prof.values ((j, Fin.castLE hq idx), false) : ℝ)
  have hmono : ∀ u v : Fin (6 * (n + 8)), u.val ≤ v.val → lowR u ≤ lowR v := by
    intro u v huv
    dsimp [lowR]
    rcases lt_or_eq_of_le huv with hlt | heq
    · have hlt' : Fin.castLE hq u < Fin.castLE hq v := hlt
      exact_mod_cast le_of_lt (prof.strictMono_low j hlt')
    · rw [Fin.ext heq]
  let pairSum (idx : Fin (6 * (n + 8))) : ℝ :=
    ((prof.values ((j, Fin.castLE hq idx), false) +
      prof.values ((j, Fin.castLE hq idx), true) : ℕ) : ℝ)
  have hpair_eq : ∀ idx : Fin (6 * (n + 8)),
      pairSum idx = 2 * lowR idx + ((2 ^ (j.val + 1) : ℕ) : ℝ) := by
    intro idx
    dsimp [pairSum, lowR]
    rw [prof.gap j (Fin.castLE hq idx)]
    push_cast
    ring
  have hn1_lt : n - 1 < n := by omega
  let blkLo (k : ℕ) : ℝ :=
    if hk : k < 6 then lowR ⟨48 + k * n, by nlinarith⟩ else 0
  let blkHi (k : ℕ) : ℝ :=
    if hk : k < 6 then lowR ⟨48 + k * n + (n - 1), by nlinarith⟩ else 0
  have hblk_mem : ∀ (k : ℕ) (hk : k < 6) (e : Fin n),
      let idx : Fin (6 * (n + 8)) := ⟨48 + k * n + e.val, by have := e.isLt; nlinarith⟩
      blkLo k ≤ lowR idx ∧ lowR idx ≤ blkHi k := by
    intro k hk e
    dsimp [blkLo, blkHi]
    rw [dif_pos hk, dif_pos hk]
    exact ⟨hmono _ _ (by dsimp only; omega), hmono _ _ (by have := e.isLt; dsimp only; omega)⟩
  have hblk_step : ∀ k : ℕ, k < 5 → blkHi k ≤ blkLo (k + 1) := by
    intro k hk
    dsimp [blkLo, blkHi]
    rw [dif_pos (by omega : k < 6), dif_pos (by omega : k + 1 < 6)]
    apply hmono
    dsimp only
    have hk_eq : (k + 1) * n = k * n + n := by ring
    omega
  have hspan_top : blkHi 5 - blkLo 0 ≤ ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
    let idx0 : Fin (6 * (n + 8)) := ⟨48 + 0 * n, by omega⟩
    let idx5 : Fin (6 * (n + 8)) := ⟨48 + 5 * n + (n - 1), by omega⟩
    have hle05 : prof.values ((j, Fin.castLE hq idx0), false) ≤
        prof.values ((j, Fin.castLE hq idx5), false) := by
      have hm := hmono idx0 idx5 (by change 48 + 0 * n ≤ 48 + 5 * n + (n - 1); omega)
      dsimp [lowR] at hm
      exact_mod_cast hm
    have hsp := prof.stage_span j (Fin.castLE hq idx0) (Fin.castLE hq idx5)
    have hcast : ((prof.values ((j, Fin.castLE hq idx5), false) -
        prof.values ((j, Fin.castLE hq idx0), false) : ℕ) : ℝ) = blkHi 5 - blkLo 0 := by
      dsimp [blkHi, blkLo]
      rw [Nat.cast_sub hle05]
    rw [← hcast]
    exact_mod_cast hsp
  have hs0 : blkHi 0 ≤ blkLo 1 := hblk_step 0 (by decide)
  have hs1 : blkHi 1 ≤ blkLo 2 := hblk_step 1 (by decide)
  have hs2 : blkHi 2 ≤ blkLo 3 := hblk_step 2 (by decide)
  have hs3 : blkHi 3 ≤ blkLo 4 := hblk_step 3 (by decide)
  have hs4 : blkHi 4 ≤ blkLo 5 := hblk_step 4 (by decide)
  let rIdx (l : Fin 3) (e : Fin n) : Fin (6 * (n + 8)) :=
    ⟨48 + l.val * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
  let cIdx (l : Fin 3) (e : Fin n) : Fin (6 * (n + 8)) :=
    ⟨48 + (3 + l.val) * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
  have hr_diff : ∀ l : Fin 3,
      |((pairSum (rIdx l (a₁ l)) + pairSum (rIdx l (b₁ l))) / 2) -
       ((pairSum (rIdx l (a₂ l)) + pairSum (rIdx l (b₂ l))) / 2)| ≤
        2 * (blkHi l.val - blkLo l.val) := by
    intro l
    rw [hpair_eq, hpair_eq, hpair_eq, hpair_eq, abs_le]
    have hl6 : l.val < 6 := by omega
    have h1 := hblk_mem l.val hl6 (a₁ l)
    have h2 := hblk_mem l.val hl6 (b₁ l)
    have h3 := hblk_mem l.val hl6 (a₂ l)
    have h4 := hblk_mem l.val hl6 (b₂ l)
    dsimp only [rIdx] at h1 h2 h3 h4 ⊢
    exact ⟨by linarith, by linarith⟩
  have hc_diff : ∀ l : Fin 3,
      |((pairSum (cIdx l (c₁ l)) + pairSum (cIdx l (d₁ l))) / 2) -
       ((pairSum (cIdx l (c₂ l)) + pairSum (cIdx l (d₂ l))) / 2)| ≤
        2 * (blkHi (3 + l.val) - blkLo (3 + l.val)) := by
    intro l
    rw [hpair_eq, hpair_eq, hpair_eq, hpair_eq, abs_le]
    have hl6 : 3 + l.val < 6 := by omega
    have h1 := hblk_mem (3 + l.val) hl6 (c₁ l)
    have h2 := hblk_mem (3 + l.val) hl6 (d₁ l)
    have h3 := hblk_mem (3 + l.val) hl6 (c₂ l)
    have h4 := hblk_mem (3 + l.val) hl6 (d₂ l)
    dsimp only [cIdx] at h1 h2 h3 h4 ⊢
    exact ⟨by linarith, by linarith⟩
  change |(∑ l : Fin 3, ((pairSum (rIdx l (a₁ l)) + pairSum (rIdx l (b₁ l))) / 2 +
      (pairSum (cIdx l (c₁ l)) + pairSum (cIdx l (d₁ l))) / 2)) -
   (∑ l : Fin 3, ((pairSum (rIdx l (a₂ l)) + pairSum (rIdx l (b₂ l))) / 2 +
      (pairSum (cIdx l (c₂ l)) + pairSum (cIdx l (d₂ l))) / 2))| ≤
    2 * ((prof.stageSpanWords j * 49152 : ℕ) : ℝ)
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have hr0 := hr_diff 0; have hr1 := hr_diff 1; have hr2 := hr_diff 2
  have hc0 := hc_diff 0; have hc1 := hc_diff 1; have hc2 := hc_diff 2
  change _ ≤ 2 * (blkHi 0 - blkLo 0) at hr0
  change _ ≤ 2 * (blkHi 1 - blkLo 1) at hr1
  change _ ≤ 2 * (blkHi 2 - blkLo 2) at hr2
  change _ ≤ 2 * (blkHi 3 - blkLo 3) at hc0
  change _ ≤ 2 * (blkHi 4 - blkLo 4) at hc1
  change _ ≤ 2 * (blkHi 5 - blkLo 5) at hc2
  rw [abs_le] at hr0 hr1 hr2 hc0 hc1 hc2 ⊢
  exact ⟨by linarith, by linarith⟩

/-- Diagonal 12-pair monotone telescoping bound for one Prefix stage `j : Fin P`. -/
theorem fc2k_prefix_diag_stage_diff {P qCert corrLo maxHi : ℕ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hq48 : 48 ≤ qCert) (j : Fin P) :
    |(∑ u : Fin 12,
        (((prof.values ((j, ⟨4 * u.val, by omega⟩), false) : ℝ) +
          ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2) -
         ((prof.values ((j, ⟨4 * u.val + 2, by omega⟩), false) : ℝ) +
          ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2)))| ≤
      ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
  let lowAt (k : ℕ) : ℝ :=
    if hk : k < qCert then (prof.values ((j, ⟨k, hk⟩), false) : ℝ) else 0
  have hmono : ∀ a b : ℕ, a ≤ b → b < qCert → lowAt a ≤ lowAt b := by
    intro a b hab hb
    have ha : a < qCert := lt_of_le_of_lt hab hb
    dsimp [lowAt]
    rw [dif_pos ha, dif_pos hb]
    rcases lt_or_eq_of_le hab with hlt | rfl
    · exact_mod_cast le_of_lt (prof.strictMono_low j (show (⟨a, ha⟩ : Fin qCert) < ⟨b, hb⟩ from hlt))
    · exact le_rfl
  have hterm_eq : ∀ u : Fin 12,
      ((prof.values ((j, ⟨4 * u.val, by omega⟩), false) : ℝ) + ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2) -
      ((prof.values ((j, ⟨4 * u.val + 2, by omega⟩), false) : ℝ) + ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2) =
        -(lowAt (4 * u.val + 2) - lowAt (4 * u.val)) := by
    intro u
    dsimp [lowAt]
    rw [dif_pos (by omega : 4 * u.val + 2 < qCert), dif_pos (by omega : 4 * u.val < qCert)]
    ring
  simp only [hterm_eq, Finset.sum_neg_distrib, abs_neg]
  rw [Fin.sum_univ_eq_sum_range (fun m => lowAt (4 * m + 2) - lowAt (4 * m)) 12]
  have hnonneg : 0 ≤ ∑ m ∈ Finset.range 12, (lowAt (4 * m + 2) - lowAt (4 * m)) := by
    apply Finset.sum_nonneg
    intro m hm
    have hm12 := Finset.mem_range.mp hm
    linarith [hmono (4 * m) (4 * m + 2) (by omega) (by omega)]
  rw [abs_of_nonneg hnonneg]
  have hind : ∀ k : ℕ, 1 ≤ k → k ≤ 12 →
      ∑ m ∈ Finset.range k, (lowAt (4 * m + 2) - lowAt (4 * m)) ≤
        lowAt (4 * (k - 1) + 2) - lowAt 0 := by
    intro k hk1 hk12
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with h1 | hgt1
      · have hk0 : k = 0 := by omega
        subst hk0; simp
      · rw [Finset.sum_range_succ]
        have hprev := ih (by omega) (by omega)
        have hstep := hmono (4 * (k - 1) + 2) (4 * k) (by omega) (by omega)
        have hksub : k + 1 - 1 = k := by omega
        rw [hksub]
        linarith
  have h12 := hind 12 (by decide) le_rfl
  have hspan : lowAt 46 - lowAt 0 ≤ ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
    dsimp [lowAt]
    rw [dif_pos (by omega : 46 < qCert), dif_pos (by omega : 0 < qCert)]
    have hle : prof.values ((j, ⟨0, by omega⟩), false) ≤ prof.values ((j, ⟨46, by omega⟩), false) :=
      le_of_lt (prof.strictMono_low j (show (0 : ℕ) < 46 by decide))
    have hsp := prof.stage_span j ⟨0, by omega⟩ ⟨46, by omega⟩
    rw [← Nat.cast_sub hle]
    exact_mod_cast hsp
  linarith [h12, hspan]

/-- Prefix (`Fin P`) + Bridge (`Fin J`) chain `CompleteEvenGrid` helper on any finite label type `α`. -/
theorem fc2k_pb_chain_grid {α : Type*} [DecidableEq α] {P J : ℕ}
    (_hP : 1 ≤ P) (X : ℝ)
    (fP : Fin P → α) (fB : Fin J → α) (gap : α → ℕ)
    (hfP_inj : Function.Injective fP)
    (hfB_inj : Function.Injective fB)
    (hdisj_PB : ∀ i j, fP i ≠ fB j)
    (hgapP : ∀ j : Fin P, gap (fP j) = 2 ^ (j.val + 1))
    (hbelow : ∀ j < J, bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < X)
    (hstop : X ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) J)
    (hgapB : ∀ j : Fin J, 2 ∣ gap (fB j) ∧
      bridgeGapLower X (bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val) < (gap (fB j) : ℝ) ∧
      (gap (fB j) : ℝ) ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val) :
    let init := (Finset.univ : Finset (Fin P)).image fP
    let brSet := (Finset.univ : Finset (Fin J)).image fB
    let R_pb := (2 ^ (P + 1) - 2) + ∑ j : Fin J, gap (fB j)
    CompleteEvenGrid (init ∪ brSet) gap R_pb ∧
      2 ∣ R_pb ∧
      R_pb = ∑ x ∈ init ∪ brSet, gap x ∧
      X ≤ (R_pb : ℝ) := by
  let R₀_nat : ℕ := 2 ^ (P + 1) - 2
  let R₀ : ℝ := (R₀_nat : ℝ)
  let init := (Finset.univ : Finset (Fin P)).image fP
  have hgrid0 : CompleteEvenGrid init gap R₀_nat := by
    have hp := prefixPairBlock_grid P (fun x : Unit × Fin P => fP x.2)
      (by rintro ⟨⟨⟩, i⟩ ⟨⟨⟩, j⟩ h; exact Prod.ext rfl (hfP_inj h))
      gap (by intro _ j; exact hgapP j) ()
    simpa [prefixPairBlock, init, R₀_nat] using hp
  have heven0 : 2 ∣ R₀_nat := by
    have hpow : 2 ^ (P + 1) = 2 * 2 ^ P := by ring
    have hp1 : 1 ≤ 2 ^ P := Nat.one_le_two_pow
    exact ⟨2 ^ P - 1, by dsimp [R₀_nat]; omega⟩
  have hsum_init : ∑ x ∈ init, gap x = R₀_nat := by
    rw [Finset.sum_image (fun i _ j _ h => hfP_inj h)]
    have hsum_pow : ∀ m : ℕ, ∑ k ∈ Finset.range m, 2 ^ (k + 1) = 2 ^ (m + 1) - 2 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        have : 2 ≤ 2 ^ (m + 1) := by
          have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
          omega
        have : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
        omega
    simp only [hgapP]
    rw [Fin.sum_univ_eq_sum_range (fun k => 2 ^ (k + 1)) P, hsum_pow P]
  have hind : ∀ k : ℕ, (hk : k ≤ J) →
      let subB := ((Finset.range k).attach).image (fun x => fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hk⟩)
      let Rk := R₀_nat + ∑ x ∈ (Finset.range k).attach, gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hk⟩)
      CompleteEvenGrid (init ∪ subB) gap Rk ∧
        2 ∣ Rk ∧
        bridgeIteration X R₀ k ≤ (Rk : ℝ) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_, ?_⟩
      · simpa using hgrid0
      · simpa using heven0
      · simp [bridgeIteration, R₀]
    | succ k ih =>
      have hkJ : k < J := Nat.lt_of_succ_le hk
      obtain ⟨hprevG, hprevE, hprevC⟩ := ih (le_of_lt hkJ)
      set prevB := ((Finset.range k).attach).image (fun x => fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) (le_of_lt hkJ)⟩)
      set prevR := R₀_nat + ∑ x ∈ (Finset.range k).attach, gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) (le_of_lt hkJ)⟩)
      let cur := fB ⟨k, hkJ⟩
      have hfresh : cur ∉ init ∪ prevB := by
        intro hmem
        rcases Finset.mem_union.mp hmem with hI | hB
        · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hI
          exact hdisj_PB i ⟨k, hkJ⟩ hi
        · obtain ⟨⟨m, hm_mem⟩, _, hm_eq⟩ := Finset.mem_image.mp hB
          have hmk : m = k := congrArg Fin.val (hfB_inj hm_eq)
          have hmlt : m < k := Finset.mem_range.mp hm_mem
          omega
      have hgB := hgapB ⟨k, hkJ⟩
      have hstep := bridge_extends_grid_from_lower_bound (init ∪ prevB) gap prevR cur
        X (bridgeIteration X R₀ k) hfresh hprevE hgB.1 hprevC hgB.2.1 hgB.2.2 hprevG
      have hset_eq : init ∪ ((Finset.range (k + 1)).attach).image
          (fun x => fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hk⟩) =
          insert cur (init ∪ prevB) := by
        ext z
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists,
          Finset.mem_range, Finset.mem_insert, prevB, cur]
        constructor
        · rintro (hz | ⟨m, hm, rfl⟩)
          · exact Or.inr (Or.inl hz)
          · rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hm) with rfl | hmlt
            · exact Or.inl rfl
            · exact Or.inr (Or.inr ⟨m, hmlt, rfl⟩)
        · rintro (rfl | hz | ⟨m, hm, rfl⟩)
          · exact Or.inr ⟨k, Nat.lt_succ_self k, rfl⟩
          · exact Or.inl hz
          · exact Or.inr ⟨m, Nat.lt_succ_of_lt hm, rfl⟩
      have hsum_eq : R₀_nat + ∑ x ∈ (Finset.range (k + 1)).attach,
          gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hk⟩) =
          prevR + gap cur := by
        have h1 : ∑ x ∈ (Finset.range (k + 1)).attach,
            gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) hk⟩) =
            ∑ m ∈ Finset.range (k + 1), (if hm : m < J then gap (fB ⟨m, hm⟩) else 0) := by
          rw [← Finset.sum_attach (Finset.range (k + 1))]
          apply Finset.sum_congr rfl
          intro x _
          rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp x.2) hk)]
        have h2 : ∑ x ∈ (Finset.range k).attach,
            gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) (le_of_lt hkJ)⟩) =
            ∑ m ∈ Finset.range k, (if hm : m < J then gap (fB ⟨m, hm⟩) else 0) := by
          rw [← Finset.sum_attach (Finset.range k)]
          apply Finset.sum_congr rfl
          intro x _
          rw [dif_pos (lt_of_lt_of_le (Finset.mem_range.mp x.2) (le_of_lt hkJ))]
        dsimp [prevR, cur]
        rw [h1, h2, Finset.sum_range_succ, dif_pos hkJ, Nat.add_assoc]
      refine ⟨?_, ?_, ?_⟩
      · rw [hset_eq, hsum_eq]; exact hstep.1
      · rw [hsum_eq]; exact dvd_add hprevE hgB.1
      · rw [hsum_eq]
        change bridgeNext X (bridgeIteration X R₀ k) ≤ _
        rw [bridgeNext, if_pos (hbelow k hkJ)]
        exact le_of_lt hstep.2
  have hJ := hind J le_rfl
  have hsubB_eq : ((Finset.range J).attach).image
      (fun x => fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) le_rfl⟩) =
      (Finset.univ : Finset (Fin J)).image fB := by
    ext z
    simp only [Finset.mem_image, Finset.mem_attach, Finset.mem_univ, true_and, Subtype.exists,
      Finset.mem_range]
    exact ⟨fun ⟨m, hm, h⟩ => ⟨⟨m, hm⟩, h⟩, fun ⟨j, h⟩ => ⟨j.val, j.isLt, h⟩⟩
  have hR_eq : R₀_nat + ∑ x ∈ (Finset.range J).attach,
      gap (fB ⟨x.1, lt_of_lt_of_le (Finset.mem_range.mp x.2) le_rfl⟩) =
      R₀_nat + ∑ j : Fin J, gap (fB j) := by
    congr 1
    refine Finset.sum_bij (fun x _ => (⟨x.1, Finset.mem_range.mp x.2⟩ : Fin J))
      (fun _ _ => Finset.mem_univ _)
      (fun a _ b _ h => Subtype.ext (congrArg Fin.val h))
      (fun j _ => ⟨⟨j.val, Finset.mem_range.mpr j.isLt⟩, Finset.mem_attach _ _, rfl⟩)
      (fun _ _ => rfl)
  change CompleteEvenGrid _ gap _ ∧ 2 ∣ _ ∧ bridgeIteration X R₀ J ≤ _ at hJ
  rw [hsubB_eq, hR_eq] at hJ
  have hdis_IB : Disjoint init ((Finset.univ : Finset (Fin J)).image fB) := by
    apply Finset.disjoint_left.mpr
    intro z hzI hzB
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzI
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hzB
    exact hdisj_PB i j hj.symm
  have hsum_tot : R₀_nat + ∑ j : Fin J, gap (fB j) =
      ∑ x ∈ init ∪ (Finset.univ : Finset (Fin J)).image fB, gap x := by
    rw [Finset.sum_union hdis_IB, hsum_init, Finset.sum_image (fun i _ j _ h => hfB_inj h)]
  exact ⟨hJ.1, hJ.2.1, hsum_tot, le_trans hstop hJ.2.2⟩

/-- Unified diagonal `CompleteEvenGrid` builder for `sideBit = 0` (`main`) and `sideBit = 1` (`anti`). -/
private theorem fc2k_diag_grid_half {P J W_diag : ℕ}
    (hP : 1 ≤ P) (sideBit : ℕ) (hbit : sideBit < 2)
    (X minWide : ℝ) (hXpos : 0 < X)
    (rectGap : Fin (24 * P + 24 * J + 2 * W_diag) → ℕ)
    (hgapP : ∀ (u : Fin 12) (j : Fin P),
      rectGap ⟨24 * j.val + (2 * u.val + sideBit), by omega⟩ = 2 ^ (j.val + 1))
    (hbelow : ∀ j < J, bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < X)
    (hstop : X ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) J)
    (hgapB : ∀ (u : Fin 12) (j : Fin J),
      let idx : Fin (24 * P + 24 * J + 2 * W_diag) :=
        ⟨24 * P + 24 * j.val + (2 * u.val + sideBit), by omega⟩
      2 ∣ rectGap idx ∧
        bridgeGapLower X (bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val) < (rectGap idx : ℝ) ∧
        (rectGap idx : ℝ) ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val)
    (hgapW : ∀ w : Fin W_diag,
      let idx : Fin (24 * P + 24 * J + 2 * W_diag) :=
        ⟨24 * P + 24 * J + (2 * w.val + sideBit), by omega⟩
      2 ∣ rectGap idx ∧ minWide ≤ (rectGap idx : ℝ) ∧ (rectGap idx : ℝ) < X) :
    let target := (Finset.univ : Finset (Fin (24 * P + 24 * J + 2 * W_diag))).filter
      (fun t => t.val % 2 = sideBit)
    let R := ∑ t ∈ target, rectGap t
    CompleteEvenGrid target rectGap R ∧
      12 * X + (W_diag : ℝ) * minWide ≤ (R : ℝ) := by
  let L := 24 * P + 24 * J + 2 * W_diag
  let fP (u : Fin 12) (j : Fin P) : Fin L := ⟨24 * j.val + (2 * u.val + sideBit), by omega⟩
  let fB (u : Fin 12) (j : Fin J) : Fin L := ⟨24 * P + 24 * j.val + (2 * u.val + sideBit), by omega⟩
  let fW (w : Fin W_diag) : Fin L := ⟨24 * P + 24 * J + (2 * w.val + sideBit), by omega⟩
  have hfP_inj : ∀ u, Function.Injective (fP u) := fun u i j h =>
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [fP] at hv; omega)
  have hfB_inj : ∀ u, Function.Injective (fB u) := fun u i j h =>
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [fB] at hv; omega)
  have hfW_inj : Function.Injective fW := fun i j h =>
    Fin.ext (by have hv := congrArg Fin.val h; dsimp [fW] at hv; omega)
  let copySet (u : Fin 12) : Finset (Fin L) :=
    Finset.univ.image (fP u) ∪ Finset.univ.image (fB u)
  let copyR (u : Fin 12) : ℕ :=
    (2 ^ (P + 1) - 2) + ∑ j : Fin J, rectGap (fB u j)
  have hcopy : ∀ u : Fin 12,
      CompleteEvenGrid (copySet u) rectGap (copyR u) ∧
      2 ∣ copyR u ∧
      copyR u = ∑ x ∈ copySet u, rectGap x ∧
      X ≤ (copyR u : ℝ) := fun u =>
    fc2k_pb_chain_grid hP X (fP u) (fB u) rectGap (hfP_inj u) (hfB_inj u)
      (fun i j h => by have hv := congrArg Fin.val h; dsimp [fP, fB] at hv; omega)
      (hgapP u) hbelow hstop (hgapB u)
  have hcopy_disj : ∀ u v : Fin 12, u ≠ v → Disjoint (copySet u) (copySet v) := by
    intro u v huv
    apply Finset.disjoint_left.mpr
    intro z hzu hzv
    have hne : u.val ≠ v.val := fun h => huv (Fin.ext h)
    rcases Finset.mem_union.mp hzu with hp1 | hb1 <;>
      rcases Finset.mem_union.mp hzv with hp2 | hb2
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp2
      have hv := congrArg Fin.val hj; dsimp [fP] at hv; omega
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb2
      have hv := congrArg Fin.val hj; dsimp [fP, fB] at hv; omega
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hp2
      have hv := congrArg Fin.val hj; dsimp [fP, fB] at hv; omega
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb2
      have hv := congrArg Fin.val hj; dsimp [fB] at hv; omega
  obtain ⟨hgrid12, heven12⟩ := completeEvenGrid_biUnion_fin copySet rectGap copyR
    hcopy_disj (fun u => (hcopy u).2.1) (fun u => (hcopy u).1)
  have hR12_ge : 12 * X ≤ ((∑ u : Fin 12, copyR u : ℕ) : ℝ) := by
    push_cast
    have h1 : (∑ _u : Fin 12, X) ≤ ∑ u : Fin 12, (copyR u : ℝ) :=
      Finset.sum_le_sum (fun u _ => (hcopy u).2.2.2)
    simpa using h1
  let wideSet : Finset (Fin L) := Finset.univ.image fW
  have hdis_W : Disjoint (Finset.univ.biUnion copySet) wideSet := by
    apply Finset.disjoint_left.mpr
    intro z hzC hzW
    obtain ⟨u, _, hzu⟩ := Finset.mem_biUnion.mp hzC
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hzW
    rcases Finset.mem_union.mp hzu with hp | hb
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      have hv := congrArg Fin.val hi; dsimp [fP, fW] at hv; omega
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      have hv := congrArg Fin.val hi; dsimp [fB, fW] at hv; omega
  have hW_bounds : ∀ z ∈ wideSet, 2 ∣ rectGap z ∧ rectGap z ≤ ∑ u : Fin 12, copyR u := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    have hw := hgapW w
    refine ⟨hw.1, ?_⟩
    have hltR : (rectGap (fW w) : ℝ) ≤ ((∑ u : Fin 12, copyR u : ℕ) : ℝ) := by
      linarith [hw.2.2, hR12_ge, hXpos]
    exact_mod_cast hltR
  obtain ⟨hgridAll, _⟩ := completeEvenGrid_extend_set hdis_W heven12 hgrid12 hW_bounds
  let target := (Finset.univ : Finset (Fin L)).filter (fun t => t.val % 2 = sideBit)
  have hset_eq : Finset.univ.biUnion copySet ∪ wideSet = target := by
    ext t
    simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, copySet, wideSet,
      Finset.mem_image, target, Finset.mem_filter]
    constructor
    · rintro (⟨u, ⟨j, rfl⟩ | ⟨j, rfl⟩⟩ | ⟨w, rfl⟩) <;> dsimp [fP, fB, fW] <;> omega
    · intro hmod
      by_cases ht1 : t.val < 24 * P
      · refine Or.inl ⟨⟨(t.val % 24) / 2, by omega⟩, Or.inl ⟨⟨t.val / 24, by omega⟩, ?_⟩⟩
        exact Fin.ext (by dsimp [fP]; omega)
      · by_cases ht2 : t.val < 24 * P + 24 * J
        · refine Or.inl ⟨⟨((t.val - 24 * P) % 24) / 2, by omega⟩,
            Or.inr ⟨⟨(t.val - 24 * P) / 24, by omega⟩, ?_⟩⟩
          exact Fin.ext (by dsimp [fB]; omega)
        · refine Or.inr ⟨⟨(t.val - (24 * P + 24 * J)) / 2, by have := t.isLt; omega⟩, ?_⟩
          exact Fin.ext (by dsimp [fW]; omega)
  have hsum12_eq : ∑ u : Fin 12, copyR u = ∑ z ∈ Finset.univ.biUnion copySet, rectGap z := by
    rw [Finset.sum_biUnion (fun u _ v _ h => hcopy_disj u v h)]
    exact Finset.sum_congr rfl (fun u _ => (hcopy u).2.2.1)
  have hR_eq : (∑ u : Fin 12, copyR u) + ∑ z ∈ wideSet, rectGap z = ∑ t ∈ target, rectGap t := by
    rw [hsum12_eq, ← Finset.sum_union hdis_W, hset_eq]
  have hW_ge : (W_diag : ℝ) * minWide ≤ ((∑ z ∈ wideSet, rectGap z : ℕ) : ℝ) := by
    rw [Finset.sum_image (fun i _ j _ h => hfW_inj h)]
    push_cast
    have h1 : (∑ _w : Fin W_diag, minWide) ≤ ∑ w : Fin W_diag, (rectGap (fW w) : ℝ) :=
      Finset.sum_le_sum (fun w _ => (hgapW w).2.1)
    simpa using h1
  refine ⟨?_, ?_⟩
  · change CompleteEvenGrid target rectGap (∑ t ∈ target, rectGap t)
    rw [← hR_eq, ← hset_eq]
    exact hgridAll
  · change 12 * X + (W_diag : ℝ) * minWide ≤ ((∑ t ∈ target, rectGap t : ℕ) : ℝ)
    rw [← hR_eq, Nat.cast_add]
    linarith [hR12_ge, hW_ge]

/-- Ordinary-edge `CompleteEvenGrid` builder across `P + J + W_ord` stages. -/
private theorem fc2k_ord_edge_grid {n P J W_ord : ℕ}
    (hP : 1 ≤ P) (X minWide : ℝ) (e : Fin 3 × Fin n)
    (ordGap : Fin ((P + J + W_ord) * 3) → Fin n → ℕ)
    (hgapP : ∀ j : Fin P,
      ordGap (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl ⟨j.val, by omega⟩ e.1) e.2 =
        2 ^ (j.val + 1))
    (hbelow : ∀ j < J, bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < X)
    (hstop : X ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) J)
    (hgapB : ∀ j : Fin J,
      let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl ⟨P + j.val, by omega⟩ e.1
      2 ∣ ordGap idx e.2 ∧
        bridgeGapLower X (bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val) < (ordGap idx e.2 : ℝ) ∧
        (ordGap idx e.2 : ℝ) ≤ bridgeIteration X ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j.val)
    (hgapW : ∀ w : Fin W_ord,
      let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl ⟨P + J + w.val, by omega⟩ e.1
      2 ∣ ordGap idx e.2 ∧ minWide ≤ (ordGap idx e.2 : ℝ) ∧ (ordGap idx e.2 : ℝ) < X) :
    let edgeSet := (Finset.univ : Finset (Fin (P + J + W_ord))).image
      (fun s => (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2))
    let g := fun k : Fin ((P + J + W_ord) * 3) × Fin n => ordGap k.1 k.2
    let R := ∑ k ∈ edgeSet, g k
    CompleteEvenGrid edgeSet g R ∧ X + (W_ord : ℝ) * minWide ≤ (R : ℝ) := by
  let slotOf (s : Fin (P + J + W_ord)) : Fin ((P + J + W_ord) * 3) × Fin n :=
    (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2)
  have hslot_inj : Function.Injective slotOf := by
    intro a b h
    exact bridgeStageLayerIndex_injective rfl e.1 (congrArg Prod.fst h)
  let fP (j : Fin P) := slotOf ⟨j.val, by omega⟩
  let fB (j : Fin J) := slotOf ⟨P + j.val, by omega⟩
  let fW (w : Fin W_ord) := slotOf ⟨P + J + w.val, by omega⟩
  have hfP_inj : Function.Injective fP := fun a b h =>
    Fin.ext (by simpa using congrArg Fin.val (hslot_inj h))
  have hfB_inj : Function.Injective fB := fun a b h =>
    Fin.ext (by have hv := congrArg Fin.val (hslot_inj h); dsimp only at hv; omega)
  have hfW_inj : Function.Injective fW := fun a b h =>
    Fin.ext (by have hv := congrArg Fin.val (hslot_inj h); dsimp only at hv; omega)
  let g := fun k : Fin ((P + J + W_ord) * 3) × Fin n => ordGap k.1 k.2
  have hpb := fc2k_pb_chain_grid hP X fP fB g hfP_inj hfB_inj
    (fun i j h => by have hv := congrArg Fin.val (hslot_inj h); dsimp only at hv; omega)
    hgapP hbelow hstop hgapB
  let pbSet := Finset.univ.image fP ∪ Finset.univ.image fB
  let R_pb := (2 ^ (P + 1) - 2) + ∑ j : Fin J, g (fB j)
  let wSet := Finset.univ.image fW
  have hdis_W : Disjoint pbSet wSet := by
    apply Finset.disjoint_left.mpr
    intro z hzPB hzW
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hzW
    rcases Finset.mem_union.mp hzPB with hp | hb
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hp
      have hv := congrArg Fin.val (hslot_inj hi); dsimp only at hv; omega
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hb
      have hv := congrArg Fin.val (hslot_inj hi); dsimp only at hv; omega
  have hW_bounds : ∀ z ∈ wSet, 2 ∣ g z ∧ g z ≤ R_pb := by
    intro z hz
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
    have hw := hgapW w
    refine ⟨hw.1, ?_⟩
    have hltR : (g (fW w) : ℝ) ≤ (R_pb : ℝ) := le_trans (le_of_lt hw.2.2) hpb.2.2.2
    exact_mod_cast hltR
  obtain ⟨hgridAll, _⟩ := completeEvenGrid_extend_set hdis_W hpb.2.1 hpb.1 hW_bounds
  let edgeSet := (Finset.univ : Finset (Fin (P + J + W_ord))).image slotOf
  have hset_eq : pbSet ∪ wSet = edgeSet := by
    ext z
    simp only [Finset.mem_union, pbSet, wSet, edgeSet, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨w, rfl⟩)
      · exact ⟨⟨i.val, by omega⟩, rfl⟩
      · exact ⟨⟨P + i.val, by omega⟩, rfl⟩
      · exact ⟨⟨P + J + w.val, by omega⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      by_cases hs1 : s.val < P
      · exact Or.inl (Or.inl ⟨⟨s.val, hs1⟩, rfl⟩)
      · by_cases hs2 : s.val < P + J
        · exact Or.inl (Or.inr ⟨⟨s.val - P, by omega⟩,
            congrArg slotOf (Fin.ext (by dsimp only; omega))⟩)
        · exact Or.inr ⟨⟨s.val - (P + J), by omega⟩,
            congrArg slotOf (Fin.ext (by dsimp only; omega))⟩
  have hR_eq : R_pb + ∑ z ∈ wSet, g z = ∑ k ∈ edgeSet, g k := by
    have hpb_sum : R_pb = ∑ x ∈ pbSet, g x := hpb.2.2.1
    rw [hpb_sum, ← Finset.sum_union hdis_W, hset_eq]
  have hW_ge : (W_ord : ℝ) * minWide ≤ ((∑ z ∈ wSet, g z : ℕ) : ℝ) := by
    rw [Finset.sum_image (fun i _ j _ h => hfW_inj h)]
    push_cast
    have h1 : (∑ _w : Fin W_ord, minWide) ≤ ∑ w : Fin W_ord, (g (fW w) : ℝ) :=
      Finset.sum_le_sum (fun w _ => (hgapW w).2.1)
    simpa using h1
  refine ⟨?_, ?_⟩
  · change CompleteEvenGrid edgeSet g (∑ k ∈ edgeSet, g k)
    rw [← hR_eq, ← hset_eq]
    exact hgridAll
  · change X + (W_ord : ℝ) * minWide ≤ ((∑ k ∈ edgeSet, g k : ℕ) : ℝ)
    rw [← hR_eq, Nat.cast_add]
    linarith [hpb.2.2.2, hW_ge]

/-- Construct the full `FC2KSelectedRoles` package from a verified `GeneralPrefixProfile`
and explicit Bridge and Wide analytic supply gates. -/
theorem fc2k_select_roles
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper)
    {n P qCert corrLo maxHi J_max W_ord W_diag N_bins W_bin : ℕ} {δ : ℝ}
    (prof : GeneralPrefixProfile P qCert corrLo maxHi)
    (hn : 2001 ≤ n) (hnmax : n ≤ 19483) (hP : 1 ≤ P)
    (hq : 6 * (n + 8) ≤ qCert) (hmaxHi : maxHi ≤ poolMaximum n)
    (hJ_cover : (poolMaximum n : ℝ) ≤
      bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) J_max)
    (M_br : ℕ → ℕ)
    (hbr_budget : ∀ j < J_max,
      bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ) j < poolMaximum n →
      bridgeGeometricStageBudget n
        ((Finset.univ : Finset ((Fin P × Fin (6 * (n + 8))) × Bool)).image
          (fun x => (truncatePrefixValues hq (generalPrefixProfile_poolValues prof hmaxHi) x).val))
        (bridgeIteration (poolMaximum n) ((2 ^ (P + 1) - 2 : ℕ) : ℝ)) (M_br j) (24 + 3 * n) j)
    (hδ : 0 < δ)
    (hsep_mid : ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) ≤ 2 * fc2kPoolMean n)
    (hm_hi : 2 * fc2kPoolMean n < (poolMaximum n : ℝ))
    (hW_bin : ∀ z : Fin N_bins × Bool, (W_bin : ℝ) ≤
      ((fc2kWideRight (fc2kPoolMean n) (poolMaximum n) δ z -
        fc2kWideLeft (fc2kPoolMean n) (poolMaximum n) δ z) -
       (518 / 125 : ℝ) *
        (Real.sqrt (fc2kWideLeft (fc2kPoolMean n) (poolMaximum n) δ z) +
         Real.sqrt (fc2kWideRight (fc2kPoolMean n) (poolMaximum n) δ z))) /
        Real.log (poolMaximum n : ℝ))
    (hwide_gate : (N_bins : ℝ) * (poolMaximum n : ℝ) <
      ((N_bins * W_bin - 2 * (2 * W_diag + W_ord * (3 * n)) : ℕ) : ℝ) ^ 2)
    (hpref_lo_wide : ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) < (corrLo : ℝ))
    (hpref_hi_wide : (maxHi : ℝ) ≤
      2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ))
    (hbr_lo_wide : ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ) < (poolMaximum n : ℝ) / 4)
    (hbr_hi_wide : 3 * (poolMaximum n : ℝ) / 4 ≤
      2 * fc2kPoolMean n - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * (poolMaximum n : ℝ)) :
    Nonempty (FC2KSelectedRoles n P qCert corrLo maxHi J_max W_ord W_diag N_bins δ prof) := by
  let X : ℝ := poolMaximum n
  let m : ℝ := fc2kPoolMean n
  have hn_pos : 0 < n := by omega
  have hn3 : 3 ≤ n := by omega
  have hn18 : n ≤ 2 ^ 18 := by omega
  have hX_pos : 0 < X := by
    dsimp [X]
    exact_mod_cast (poolMaximum_prime n).pos
  have hX500 : (500 : ℝ) ≤ X := by
    have hnn : n * n ≤ poolMaximum n :=
      (Nat.nth_strictMono Nat.infinite_setOfPred_prime).id_le (n * n)
    have h500 : 500 ≤ n * n := by nlinarith
    dsimp [X]
    exact_mod_cast le_trans h500 hnn
  let R₀_nat : ℕ := 2 ^ (P + 1) - 2
  let R₀ : ℝ := (R₀_nat : ℝ)
  have hR₀_pos : 0 < R₀ := by
    have hp2 : 4 ≤ 2 ^ (P + 1) := by
      have h1 : 2 ^ 2 ≤ 2 ^ (P + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using h1
    dsimp [R₀, R₀_nat]
    exact_mod_cast (show 0 < 2 ^ (P + 1) - 2 by omega)
  let poolProf := generalPrefixProfile_poolValues prof hmaxHi
  have hpoolProf_inj : Function.Injective poolProf :=
    generalPrefixProfile_poolValues_injective prof hmaxHi
  let prefValues := truncatePrefixValues hq poolProf
  have hpref_inj : Function.Injective prefValues :=
    truncatePrefixValues_injective hq poolProf hpoolProf_inj
  have hpref_gap : ∀ j i, (prefValues ((j, i), true)).val =
      (prefValues ((j, i), false)).val + 2 ^ (j.val + 1) :=
    truncatePrefixValues_gap hq poolProf (fun j i => prof.gap j i)
  let V_pref : Finset ℕ := Finset.univ.image (fun x => (prefValues x).val)
  have hV_pref_sub : V_pref ⊆ Finset.univ.image prof.values := by
    intro v hv
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv
    exact truncatePrefixValues_mem_full hq poolProf x
  have hV_pref_card : V_pref.card = 12 * P * (n + 8) := by
    have hc := truncatePrefixValues_card hq poolProf hpoolProf_inj
    change V_pref.card = 2 * (6 * (n + 8)) * P at hc
    rw [hc]; ring
  have hbr_all : ∀ j, bridgeIteration X R₀ j < X →
      bridgeGeometricStageBudget n V_pref (bridgeIteration X R₀) (M_br j) (24 + 3 * n) j := by
    intro j hj_lt
    have hj_max : j < J_max := by
      by_contra hge
      have hmono := bridgeIteration_mono X R₀ hX_pos hR₀_pos (Nat.le_of_not_lt hge)
      dsimp [X, R₀] at hJ_cover hj_lt hmono
      linarith
    exact hbr_budget j hj_max hj_lt
  obtain ⟨J, batches, hstop, hbelow, hvalid_br, _⟩ :=
    select_bridge_until_covered bmor upper n V_pref R₀ M_br (24 + 3 * n)
      hn3 hn18 hR₀_pos hbr_all
  have hJ_le : J ≤ J_max := by
    by_contra hgt
    have hj_lt := hbelow J_max (Nat.lt_of_not_le hgt)
    dsimp [X, R₀] at hJ_cover hj_lt
    linarith
  let radii := bridgeIteration X R₀
  have hradii_pos : ∀ j < J, 0 < radii j := fun j _ =>
    bridgeIteration_pos X R₀ hX_pos hR₀_pos j
  let brEnd := bridgeStageEndpoint n V_pref radii batches (24 + 3 * n) J hvalid_br
  have hbrEnd_inj : Function.Injective brEnd :=
    bridgeStageEndpoint_injective n V_pref radii batches (24 + 3 * n) J hvalid_br hradii_pos
  have hbrEnd_pool : ∀ y, brEnd y ∈ pool n ∧ brEnd y ∉ V_pref :=
    bridgeStageEndpoint_pool_avoids bmor upper n V_pref radii batches (24 + 3 * n) J hvalid_br
      hn3 hn18 hradii_pos
  let V_br : Finset ℕ := Finset.univ.image brEnd
  have hV_br_card : V_br.card ≤ 4 * J * (24 + 3 * n) := by
    rw [Finset.card_image_of_injective _ hbrEnd_inj, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring_nf; exact le_rfl
  -- Select Wide matched blocks
  let k_wide := 2 * W_diag + W_ord * (3 * n)
  let bL := fc2kWideLeft (N := N_bins) m X δ
  let bR := fc2kWideRight (N := N_bins) m X δ
  obtain ⟨hb1, hbc, hcX, hsep_w, hcross_w, _⟩ :=
    fc2kWide_interval_props (N := N_bins) m X δ hX500 hδ hsep_mid (le_of_lt hm_hi)
  obtain ⟨hdis_w, hlow_w, hhigh_w, horder_w, hdiff_w, hpoolL_w, hpoolH_w⟩ :=
    bmor_two_matched_bin_inputs bmor upper n W_bin bL bR hn3 hn18
      hb1 hbc hcX hsep_w hcross_w hW_bin
  obtain ⟨wideBlocks, hlen_w, hmatched_w, hpair_w, _⟩ :=
    select_matched_bin_double_pairs_paired_budget (k := k_wide)
      (bmorLowBins bL bR) (bmorHighBins bL bR) ∅ (Finset.range (poolMaximum n))
      hdis_w hlow_w hhigh_w horder_w hdiff_w (by simp)
      hwide_gate (by dsimp only [k_wide]; simp)
  have horder_all_w : ∀ a ∈ Finset.univ.biUnion (bmorLowBins bL bR),
      ∀ d ∈ Finset.univ.biUnion (bmorHighBins bL bR), a < d := by
    intro a ha d hd
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hd
    exact horder_w i j a hi d hj
  have hvalid_all_w : ∀ bl ∈ wideBlocks,
      bl.valid (Finset.univ.biUnion (bmorLowBins bL bR))
        (Finset.univ.biUnion (bmorHighBins bL bR)) :=
    fun bl hbl => (hmatched_w bl hbl).1
  have hwideEnd_inj : Function.Injective (doublePairSequenceEndpoint wideBlocks) :=
    doublePairSequenceEndpoint_injective wideBlocks _ _ horder_all_w hvalid_all_w hpair_w
  let wideCast (z : Fin k_wide × Fin 4) : Fin wideBlocks.length × Fin 4 :=
    (Fin.cast hlen_w.symm z.1, z.2)
  have hwideCast_inj : Function.Injective wideCast := by
    rintro ⟨i₁, s₁⟩ ⟨i₂, s₂⟩ h
    exact Prod.ext (Fin.cast_injective hlen_w.symm (congrArg Prod.fst h))
      (by simpa [wideCast] using congrArg Prod.snd h)
  let wideEnd (z : Fin k_wide × Fin 4) : ℕ :=
    doublePairSequenceEndpoint wideBlocks (wideCast z)
  have hwide_inj : Function.Injective wideEnd := hwideEnd_inj.comp hwideCast_inj
  have hwide_mem_bins : ∀ z : Fin k_wide × Fin 4,
      wideEnd z ∈ Finset.univ.biUnion (bmorLowBins bL bR) ∪
        Finset.univ.biUnion (bmorHighBins bL bR) := by
    intro ⟨wIdx, side⟩
    set bl := wideBlocks.get (Fin.cast hlen_w.symm wIdx)
    have hbl_mem : bl ∈ wideBlocks := List.get_mem _ _
    have hv := hvalid_all_w bl hbl_mem
    fin_cases side
    · exact Finset.mem_union_left _ hv.1
    · exact Finset.mem_union_right _ hv.2.2.1
    · exact Finset.mem_union_right _ hv.2.2.2.1
    · exact Finset.mem_union_left _ hv.2.1
  have hwide_pool : ∀ z : Fin k_wide × Fin 4, wideEnd z ∈ pool n := by
    intro z
    rcases Finset.mem_union.mp (hwide_mem_bins z) with hL | hH
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hL
      exact hpoolL_w i _ hi
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hH
      exact hpoolH_w i _ hi
  let V_wide : Finset ℕ := Finset.univ.image wideEnd
  have hV_wide_out : ∀ v ∈ V_wide,
      (v : ℝ) ≤ ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X ∨
        2 * m - ((1 / 500 : ℝ) + (N_bins : ℝ) * δ) * X < (v : ℝ) := by
    intro v hv
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hv
    have hδX : 0 < δ * X := by positivity
    rcases Finset.mem_union.mp (hwide_mem_bins z) with hL | hH
    · left
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hL
      have hint := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i, false)])
        (by linarith [hb1 (i, false), hbc (i, false)]) (wideEnd z)).mp hi
      have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N_bins : ℝ) := by exact_mod_cast i.isLt
      have hmul := mul_le_mul_of_nonneg_right hi1 hδX.le
      simp only [bR, fc2kWideRight, Bool.false_eq_true, ↓reduceIte] at hint
      nlinarith [hint.2.2.1]
    · right
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hH
      have hint := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i, true)])
        (by linarith [hb1 (i, true), hbc (i, true)]) (wideEnd z)).mp hi
      have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N_bins : ℝ) := by exact_mod_cast i.isLt
      have hmul := mul_le_mul_of_nonneg_right hi1 hδX.le
      simp only [bL, fc2kWideLeft, ↓reduceIte] at hint
      nlinarith [hint.2.1]
  -- Source-to-pool map and global injectivity
  let srcVal : FC2KSourceDomain n P J W_ord W_diag → pool n
    | .inl x => prefValues x
    | .inr (.inl y) => ⟨brEnd y, (hbrEnd_pool y).1⟩
    | .inr (.inr z) => ⟨wideEnd z, hwide_pool z⟩
  have hpref_not_wide : ∀ x, (prefValues x).val ∉
      Finset.univ.biUnion (bmorLowBins bL bR) ∪ Finset.univ.biUnion (bmorHighBins bL bR) := by
    intro x
    have hb := prof.bounds (prefixTruncationIndex hq x)
    have hval_eq : (prefValues x).val = prof.values (prefixTruncationIndex hq x) := rfl
    apply fc2kWide_not_mem_bins hX500 hδ hsep_mid (le_of_lt hm_hi)
    · rw [hval_eq]; linarith [hpref_lo_wide, show (corrLo : ℝ) ≤ prof.values (prefixTruncationIndex hq x) by exact_mod_cast hb.1]
    · rw [hval_eq]; linarith [hpref_hi_wide, show (prof.values (prefixTruncationIndex hq x) : ℝ) ≤ maxHi by exact_mod_cast hb.2]
  have hbr_not_wide : ∀ y, brEnd y ∉
      Finset.univ.biUnion (bmorLowBins bL bR) ∪ Finset.univ.biUnion (bmorHighBins bL bR) := by
    rintro ⟨⟨j, idx⟩, side⟩
    have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br j idx
    set blk := bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br j idx
    have hbounds : X / 4 < (brEnd ((j, idx), side) : ℝ) ∧ (brEnd ((j, idx), side) : ℝ) ≤ 3 * X / 4 := by
      change X / 4 < (blk.endpoint side : ℝ) ∧ (blk.endpoint side : ℝ) ≤ 3 * X / 4
      fin_cases side <;> dsimp [DoublePair.endpoint]
      · exact ⟨hb.1, le_trans (le_of_lt hb.2.1) (by linarith)⟩
      · exact ⟨lt_of_le_of_lt (by linarith) hb.2.2.2.2.1, hb.2.2.2.2.2.1⟩
      · exact ⟨lt_of_le_of_lt (by linarith) hb.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.1⟩
      · exact ⟨hb.2.2.1, le_trans (le_of_lt hb.2.2.2.1) (by linarith)⟩
    exact fc2kWide_not_mem_bins hX500 hδ hsep_mid (le_of_lt hm_hi)
      (lt_trans hbr_lo_wide hbounds.1) (le_trans hbounds.2 hbr_hi_wide)
  have hsrc_inj : Function.Injective srcVal := by
    intro a b heq
    have hv : (srcVal a).val = (srcVal b).val := congrArg Subtype.val heq
    rcases a with x₁ | (y₁ | z₁) <;> rcases b with x₂ | (y₂ | z₂) <;> dsimp [srcVal] at hv
    · exact congrArg Sum.inl (hpref_inj heq)
    · exfalso; exact (hbrEnd_pool y₂).2 (hv ▸ Finset.mem_image.mpr ⟨x₁, Finset.mem_univ _, rfl⟩)
    · exfalso; exact hpref_not_wide x₁ (hv.symm ▸ hwide_mem_bins z₂)
    · exfalso; exact (hbrEnd_pool y₁).2 (hv.symm ▸ Finset.mem_image.mpr ⟨x₂, Finset.mem_univ _, rfl⟩)
    · exact congrArg (Sum.inr ∘ Sum.inl) (hbrEnd_inj hv)
    · exfalso; exact hbr_not_wide y₁ (hv.symm ▸ hwide_mem_bins z₂)
    · exfalso; exact hpref_not_wide x₂ (hv ▸ hwide_mem_bins z₁)
    · exfalso; exact hbr_not_wide y₂ (hv ▸ hwide_mem_bins z₁)
    · exact congrArg (Sum.inr ∘ Sum.inr) (hwide_inj hv)
  have hslot_bij := fc2kSlotToSource_bijective hn_pos P J W_ord W_diag
  let slotEquiv := Equiv.ofBijective _ hslot_bij
  let slotVal := srcVal ∘ fc2kSlotToSource
  have hslot_inj : Function.Injective slotVal := hsrc_inj.comp hslot_bij.injective
  let rectVal (x : Fin (24 * P + 24 * J + 2 * W_diag) × Fin 4) := slotVal (.inl x)
  let rowVal (x : Fin ((P + J + W_ord) * 3) × (Fin n × Bool)) := slotVal (.inr (.inl x))
  let colVal (x : Fin ((P + J + W_ord) * 3) × (Fin n × Bool)) := slotVal (.inr (.inr x))
  let wideGapAt (wIdx : Fin k_wide) : ℕ :=
    let bl := wideBlocks.get (Fin.cast hlen_w.symm wIdx)
    bl.high₁ - bl.low₁
  have hwideBlock_props : ∀ wIdx : Fin k_wide,
      let bl := wideBlocks.get (Fin.cast hlen_w.symm wIdx)
      0 < wideGapAt wIdx ∧
      2 ∣ wideGapAt wIdx ∧
      2 * m - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * X < (wideGapAt wIdx : ℝ) ∧
      (wideGapAt wIdx : ℝ) < X ∧
      |((bl.low₁ + bl.high₁ : ℕ) : ℝ) - 2 * m| ≤ δ * X ∧
      |((bl.low₂ + bl.high₂ : ℕ) : ℝ) - 2 * m| ≤ δ * X ∧
      bl.high₁ = bl.low₁ + wideGapAt wIdx ∧
      bl.high₂ = bl.low₂ + wideGapAt wIdx := by
    intro wIdx
    let bl := wideBlocks.get (Fin.cast hlen_w.symm wIdx)
    have hbl_mem : bl ∈ wideBlocks := List.get_mem _ _
    have hm_bl := hmatched_w bl hbl_mem
    have hb_bl := fc2kWide_matched_block_bounds m δ hX500 hδ hsep_mid hm_hi hm_bl
    have hv_bl := hm_bl.1
    have ho₁ : bl.low₁ < bl.high₁ := hv_bl.2.2.2.2.2.2.1
    have ho₂ : bl.low₂ < bl.high₂ := hv_bl.2.2.2.2.2.2.2.1
    have heq_gap : bl.high₁ - bl.low₁ = bl.high₂ - bl.low₂ := hv_bl.2.2.2.2.2.2.2.2
    exact ⟨hb_bl.1, hb_bl.2.1, hb_bl.2.2.1, hb_bl.2.2.2.1, hb_bl.2.2.2.2.1, hb_bl.2.2.2.2.2,
      by change bl.high₁ = bl.low₁ + (bl.high₁ - bl.low₁); omega,
      by change bl.high₂ = bl.low₂ + (bl.high₁ - bl.low₁); omega⟩
  let rectGap (t : Fin (24 * P + 24 * J + 2 * W_diag)) : ℕ :=
    if htP : t.val < 24 * P then
      2 ^ ((t.val / 24) + 1)
    else if htB : t.val < 24 * P + 24 * J then
      selectedBridgeGap batches ((t.val - 24 * P) % 24) ((t.val - 24 * P) / 24)
    else
      wideGapAt ⟨t.val - (24 * P + 24 * J), by dsimp only [k_wide]; omega⟩
  let ordGap (i : Fin ((P + J + W_ord) * 3)) (e : Fin n) : ℕ :=
    let p : Fin (P + J + W_ord) × Fin 3 := finProdFinEquiv.symm i
    if hsP : p.1.val < P then
      2 ^ (p.1.val + 1)
    else if hsB : p.1.val < P + J then
      selectedBridgeGap batches (24 + p.2.val * n + e.val) (p.1.val - P)
    else
      wideGapAt ⟨2 * W_diag + (p.1.val - (P + J)) * (3 * n) + p.2.val * n + e.val, by
        have h1 : p.1.val - (P + J) + 1 ≤ W_ord := by have := p.1.isLt; omega
        dsimp only [k_wide]; have := p.2.isLt; have := e.isLt; nlinarith⟩
  -- Prove hrect_gap, hrow_gap, hcol_gap
  have hrect_gap : ∀ t : Fin (24 * P + 24 * J + 2 * W_diag),
      0 < rectGap t ∧ 2 ∣ rectGap t ∧
      (rectVal (t, 1)).val = (rectVal (t, 0)).val + rectGap t ∧
      (rectVal (t, 2)).val = (rectVal (t, 3)).val + rectGap t := by
    intro t
    dsimp only [rectVal, slotVal, Function.comp_apply, fc2kSlotToSource, rectGap]
    split_ifs with htP htB
    · have hpow_pos : 0 < 2 ^ ((t.val / 24) + 1) := by positivity
      have hpow_even : 2 ∣ 2 ^ ((t.val / 24) + 1) := ⟨2 ^ (t.val / 24), by ring⟩
      have hg0 := hpref_gap ⟨t.val / 24, by omega⟩ ⟨2 * (t.val % 24), by omega⟩
      have hg1 := hpref_gap ⟨t.val / 24, by omega⟩ ⟨2 * (t.val % 24) + 1, by omega⟩
      refine ⟨hpow_pos, hpow_even, ?_, ?_⟩
      · simpa [srcVal, prefixCornerCode] using hg0
      · simpa [srcVal, prefixCornerCode] using hg1
    · let jB : Fin J := ⟨(t.val - 24 * P) / 24, by omega⟩
      let vB : Fin (24 + 3 * n) := ⟨(t.val - 24 * P) % 24, by omega⟩
      have hsb := selectedBridgeGap_bounds n V_pref R₀ batches (24 + 3 * n) J hvalid_br vB jB.val jB.isLt
      have hv_blk := bridgeStageBlock_valid n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have hg_blk := bridgeStageBlock_gap n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have ho1 := hv_blk.2.2.2.2.2.2.1
      have ho2 := hv_blk.2.2.2.2.2.2.2.1
      have heq_b := hv_blk.2.2.2.2.2.2.2.2
      dsimp only [jB, vB] at hv_blk hg_blk ho1 ho2 heq_b
      refine ⟨by rw [hg_blk]; omega, hsb.1, ?_, ?_⟩
      · dsimp [srcVal, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
        rw [hg_blk]; omega
      · dsimp [srcVal, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
        rw [hg_blk]; omega
    · set wIdx : Fin k_wide := ⟨t.val - (24 * P + 24 * J), by dsimp only [k_wide]; omega⟩
      have hwp := hwideBlock_props wIdx
      refine ⟨hwp.1, hwp.2.1, ?_, ?_⟩
      · simpa [srcVal, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint] using hwp.2.2.2.2.2.2.1
      · simpa [srcVal, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint] using hwp.2.2.2.2.2.2.2
  have hrow_gap : ∀ i e, (rowVal (i, (e, true))).val = (rowVal (i, (e, false))).val + ordGap i e := by
    intro i e
    dsimp only [rowVal, slotVal, Function.comp_apply, fc2kSlotToSource, ordGap]
    split_ifs with hsP hsB
    · exact hpref_gap ⟨(finProdFinEquiv.symm i).1.val, hsP⟩
        ⟨48 + (finProdFinEquiv.symm i).2.val * n + e.val,
          by have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
    · let jB : Fin J := ⟨(finProdFinEquiv.symm i).1.val - P, by omega⟩
      let vB : Fin (24 + 3 * n) := ⟨24 + (finProdFinEquiv.symm i).2.val * n + e.val,
        by have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
      have hv_blk := bridgeStageBlock_valid n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have hg_blk := bridgeStageBlock_gap n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have ho1 := hv_blk.2.2.2.2.2.2.1
      dsimp [srcVal, fc2kOrdCorner, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
      change (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB).high₁ =
        (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB).low₁ +
        selectedBridgeGap batches vB.val jB.val
      dsimp only [jB, vB] at hv_blk hg_blk ho1 ⊢
      rw [hg_blk]; omega
    · set wIdx : Fin k_wide := ⟨2 * W_diag + ((finProdFinEquiv.symm i).1.val - (P + J)) * (3 * n) +
        (finProdFinEquiv.symm i).2.val * n + e.val, by
        have h1 : (finProdFinEquiv.symm i).1.val - (P + J) + 1 ≤ W_ord :=
          by have := (finProdFinEquiv.symm i).1.isLt; omega
        dsimp only [k_wide]; have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
      simpa [srcVal, fc2kOrdCorner, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint]
        using (hwideBlock_props wIdx).2.2.2.2.2.2.1
  have hcol_gap : ∀ i e, (colVal (i, (e, true))).val = (colVal (i, (e, false))).val + ordGap i e := by
    intro i e
    dsimp only [colVal, slotVal, Function.comp_apply, fc2kSlotToSource, ordGap]
    split_ifs with hsP hsB
    · exact hpref_gap ⟨(finProdFinEquiv.symm i).1.val, hsP⟩
        ⟨48 + (3 + (finProdFinEquiv.symm i).2.val) * n + e.val,
          by have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
    · let jB : Fin J := ⟨(finProdFinEquiv.symm i).1.val - P, by omega⟩
      let vB : Fin (24 + 3 * n) := ⟨24 + (finProdFinEquiv.symm i).2.val * n + e.val,
        by have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
      have hv_blk := bridgeStageBlock_valid n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have hg_blk := bridgeStageBlock_gap n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB
      have ho2 := hv_blk.2.2.2.2.2.2.2.1
      have heq_b := hv_blk.2.2.2.2.2.2.2.2
      dsimp [srcVal, fc2kOrdCorner, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
      change (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB).high₂ =
        (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br jB vB).low₂ +
        selectedBridgeGap batches vB.val jB.val
      dsimp only [jB, vB] at hv_blk hg_blk ho2 heq_b ⊢
      rw [hg_blk]; omega
    · set wIdx : Fin k_wide := ⟨2 * W_diag + ((finProdFinEquiv.symm i).1.val - (P + J)) * (3 * n) +
        (finProdFinEquiv.symm i).2.val * n + e.val, by
        have h1 : (finProdFinEquiv.symm i).1.val - (P + J) + 1 ≤ W_ord :=
          by have := (finProdFinEquiv.symm i).1.isLt; omega
        dsimp only [k_wide]; have := (finProdFinEquiv.symm i).2.isLt; have := e.isLt; nlinarith⟩
      simpa [srcVal, fc2kOrdCorner, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint]
        using (hwideBlock_props wIdx).2.2.2.2.2.2.2
  -- Diagonal grids Rm, Ra and ordinary edge grids
  let minWide := 2 * m - ((1 / 250 : ℝ) + 2 * (N_bins : ℝ) * δ) * X
  have hdiag_half : ∀ (sideBit : ℕ) (hbit : sideBit < 2),
      let target := (Finset.univ : Finset (Fin (24 * P + 24 * J + 2 * W_diag))).filter
        (fun t => t.val % 2 = sideBit)
      CompleteEvenGrid target rectGap (∑ t ∈ target, rectGap t) ∧
        12 * X + (W_diag : ℝ) * minWide ≤ ((∑ t ∈ target, rectGap t : ℕ) : ℝ) := by
    intro sideBit hbit
    apply fc2k_diag_grid_half hP sideBit hbit X minWide hX_pos rectGap
    · intro u j
      dsimp only [rectGap]
      have htP : 24 * j.val + (2 * u.val + sideBit) < 24 * P := by omega
      rw [dif_pos htP]
      have hdiv : (24 * j.val + (2 * u.val + sideBit)) / 24 = j.val := by omega
      rw [hdiv]
    · exact hbelow
    · exact hstop
    · intro u j
      dsimp only [rectGap]
      have hnotP : ¬ (24 * P + 24 * j.val + (2 * u.val + sideBit) < 24 * P) := by omega
      have htB : 24 * P + 24 * j.val + (2 * u.val + sideBit) < 24 * P + 24 * J := by omega
      rw [dif_neg hnotP, dif_pos htB]
      have hmod : (24 * P + 24 * j.val + (2 * u.val + sideBit) - 24 * P) % 24 = 2 * u.val + sideBit := by omega
      have hdiv : (24 * P + 24 * j.val + (2 * u.val + sideBit) - 24 * P) / 24 = j.val := by omega
      rw [hmod, hdiv]
      exact selectedBridgeGap_bounds n V_pref R₀ batches (24 + 3 * n) J hvalid_br
        ⟨2 * u.val + sideBit, by omega⟩ j.val j.isLt
    · intro w
      dsimp only [rectGap]
      have hnotP : ¬ (24 * P + 24 * J + (2 * w.val + sideBit) < 24 * P) := by omega
      have hnotB : ¬ (24 * P + 24 * J + (2 * w.val + sideBit) < 24 * P + 24 * J) := by omega
      rw [dif_neg hnotP, dif_neg hnotB]
      have hsub : 24 * P + 24 * J + (2 * w.val + sideBit) - (24 * P + 24 * J) = 2 * w.val + sideBit := by omega
      set wIdx : Fin k_wide := ⟨24 * P + 24 * J + (2 * w.val + sideBit) - (24 * P + 24 * J), by omega⟩
      have hwp := hwideBlock_props wIdx
      exact ⟨hwp.2.1, le_of_lt hwp.2.2.1, hwp.2.2.2.1⟩
  have hm_filter_eq : (Finset.univ : Finset (Fin (24 * P + 24 * J + 2 * W_diag))).filter
      (fun t => decide (t.val % 2 = 0) = true) =
      Finset.univ.filter (fun t => t.val % 2 = 0) := by
    ext t; simp
  have ha_filter_eq : (Finset.univ : Finset (Fin (24 * P + 24 * J + 2 * W_diag))).filter
      (fun t => decide (t.val % 2 = 0) = false) =
      Finset.univ.filter (fun t => t.val % 2 = 1) := by
    ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not]; omega
  have hm_res := hdiag_half 0 (by decide)
  have ha_res := hdiag_half 1 (by decide)
  let Rm := ∑ t ∈ Finset.univ.filter
    (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = true), rectGap t
  let Ra := ∑ t ∈ Finset.univ.filter
    (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = false), rectGap t
  have hedge_all : ∀ e : Fin 3 × Fin n,
      let edgeSet := (Finset.univ : Finset (Fin (P + J + W_ord))).image
        (fun s => (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2))
      let g := fun k : Fin ((P + J + W_ord) * 3) × Fin n => ordGap k.1 k.2
      CompleteEvenGrid edgeSet g (∑ k ∈ edgeSet, g k) ∧
        X + (W_ord : ℝ) * minWide ≤ ((∑ k ∈ edgeSet, g k : ℕ) : ℝ) := by
    intro e
    apply fc2k_ord_edge_grid hP X minWide e ordGap
    · intro j
      dsimp only [ordGap, bridgeStageLayerIndex]
      simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
      rw [dif_pos j.isLt]
    · exact hbelow
    · exact hstop
    · intro j
      dsimp only [ordGap, bridgeStageLayerIndex]
      simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
      have hnotP : ¬ (P + j.val < P) := by omega
      have hsB : P + j.val < P + J := by omega
      rw [dif_neg hnotP, dif_pos hsB]
      have hsub : P + j.val - P = j.val := by omega
      rw [hsub]
      exact selectedBridgeGap_bounds n V_pref R₀ batches (24 + 3 * n) J hvalid_br
        ⟨24 + e.1.val * n + e.2.val, by have := e.1.isLt; have := e.2.isLt; nlinarith⟩ j.val j.isLt
    · intro w
      dsimp only [ordGap, bridgeStageLayerIndex]
      simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
      have hnotP : ¬ (P + J + w.val < P) := by omega
      have hnotB : ¬ (P + J + w.val < P + J) := by omega
      rw [dif_neg hnotP, dif_neg hnotB]
      set wIdx : Fin k_wide := ⟨2 * W_diag + (P + J + w.val - (P + J)) * (3 * n) + e.1.val * n + e.2.val, by
        have hsub : P + J + w.val - (P + J) = w.val := by omega
        rw [hsub]; dsimp only [k_wide]; have := w.isLt; have := e.1.isLt; have := e.2.isLt; nlinarith⟩
      have hwp := hwideBlock_props wIdx
      exact ⟨hwp.2.1, le_of_lt hwp.2.2.1, hwp.2.2.2.1⟩
  let edgeRadius (e : Fin 3 × Fin n) : ℕ :=
    ∑ k ∈ (Finset.univ : Finset (Fin (P + J + W_ord))).image
      (fun s => (bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s e.1, e.2)),
      ordGap k.1 k.2
  -- Set equality hrole_union
  have hrole_union :
      (Finset.univ.image (fun x => (rectVal x).val) ∪
        Finset.univ.image (fun x => (rowVal x).val) ∪
        Finset.univ.image (fun x => (colVal x).val)) = V_pref ∪ V_br ∪ V_wide := by
    ext v
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and, V_pref, V_br, V_wide]
    constructor
    · rintro ((⟨x, rfl⟩ | ⟨x, rfl⟩) | ⟨x, rfl⟩)
      · rcases h : fc2kSlotToSource (.inl x) with a | (b | c)
        · exact Or.inl (Or.inl ⟨a, by dsimp [rectVal, slotVal]; rw [h]⟩)
        · exact Or.inl (Or.inr ⟨b, by dsimp [rectVal, slotVal]; rw [h]⟩)
        · exact Or.inr ⟨c, by dsimp [rectVal, slotVal]; rw [h]⟩
      · rcases h : fc2kSlotToSource (.inr (.inl x)) with a | (b | c)
        · exact Or.inl (Or.inl ⟨a, by dsimp [rowVal, slotVal]; rw [h]⟩)
        · exact Or.inl (Or.inr ⟨b, by dsimp [rowVal, slotVal]; rw [h]⟩)
        · exact Or.inr ⟨c, by dsimp [rowVal, slotVal]; rw [h]⟩
      · rcases h : fc2kSlotToSource (.inr (.inr x)) with a | (b | c)
        · exact Or.inl (Or.inl ⟨a, by dsimp [colVal, slotVal]; rw [h]⟩)
        · exact Or.inl (Or.inr ⟨b, by dsimp [colVal, slotVal]; rw [h]⟩)
        · exact Or.inr ⟨c, by dsimp [colVal, slotVal]; rw [h]⟩
    · have hsurj := hslot_bij.surjective
      rintro ((⟨a, rfl⟩ | ⟨b, rfl⟩) | ⟨c, rfl⟩)
      · obtain ⟨s, hs⟩ := hsurj (.inl a)
        rcases s with x | (x | x)
        · exact Or.inl (Or.inl ⟨x, by dsimp [rectVal, slotVal]; rw [hs]⟩)
        · exact Or.inl (Or.inr ⟨x, by dsimp [rowVal, slotVal]; rw [hs]⟩)
        · exact Or.inr ⟨x, by dsimp [colVal, slotVal]; rw [hs]⟩
      · obtain ⟨s, hs⟩ := hsurj (.inr (.inl b))
        rcases s with x | (x | x)
        · exact Or.inl (Or.inl ⟨x, by dsimp [rectVal, slotVal]; rw [hs]⟩)
        · exact Or.inl (Or.inr ⟨x, by dsimp [rowVal, slotVal]; rw [hs]⟩)
        · exact Or.inr ⟨x, by dsimp [colVal, slotVal]; rw [hs]⟩
      · obtain ⟨s, hs⟩ := hsurj (.inr (.inr c))
        rcases s with x | (x | x)
        · exact Or.inl (Or.inl ⟨x, by dsimp [rectVal, slotVal]; rw [hs]⟩)
        · exact Or.inl (Or.inr ⟨x, by dsimp [rowVal, slotVal]; rw [hs]⟩)
        · exact Or.inr ⟨x, by dsimp [colVal, slotVal]; rw [hs]⟩
  -- Sum identity across SlotDomain = SourceDomain
  have hsum_slot_eq_src :
      ((∑ x, ((rectVal x).val : ℝ)) + (∑ x, ((rowVal x).val : ℝ)) + (∑ x, ((colVal x).val : ℝ))) =
        (∑ x : (Fin P × Fin (6 * (n + 8))) × Bool, ((prefValues x).val : ℝ)) +
        (∑ y : (Fin J × Fin (24 + 3 * n)) × Fin 4, (brEnd y : ℝ)) +
        (∑ z : Fin k_wide × Fin 4, (wideEnd z : ℝ)) := by
    have h1 : ((∑ x, ((rectVal x).val : ℝ)) + (∑ x, ((rowVal x).val : ℝ)) + (∑ x, ((colVal x).val : ℝ))) =
        ∑ s : FC2KSlotDomain n P J W_ord W_diag, ((slotVal s).val : ℝ) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
    have h2 : (∑ s : FC2KSlotDomain n P J W_ord W_diag, ((slotVal s).val : ℝ)) =
        ∑ z : FC2KSourceDomain n P J W_ord W_diag, ((srcVal z).val : ℝ) :=
      Equiv.sum_comp slotEquiv (fun z => ((srcVal z).val : ℝ))
    have h3 : (∑ z : FC2KSourceDomain n P J W_ord W_diag, ((srcVal z).val : ℝ)) =
        (∑ x : (Fin P × Fin (6 * (n + 8))) × Bool, ((prefValues x).val : ℝ)) +
        (∑ y : (Fin J × Fin (24 + 3 * n)) × Fin 4, (brEnd y : ℝ)) +
        (∑ z : Fin k_wide × Fin 4, (wideEnd z : ℝ)) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sum_type, add_assoc]
    exact h1.trans (h2.trans h3)
  have hsum_pref_bounds :
      (12 * P * (n + 8) : ℝ) * (corrLo : ℝ) ≤
        (∑ x : (Fin P × Fin (6 * (n + 8))) × Bool, ((prefValues x).val : ℝ)) ∧
      (∑ x : (Fin P × Fin (6 * (n + 8))) × Bool, ((prefValues x).val : ℝ)) ≤
        (12 * P * (n + 8) : ℝ) * (maxHi : ℝ) := by
    have hlo : ∀ x : (Fin P × Fin (6 * (n + 8))) × Bool, (corrLo : ℝ) ≤ ((prefValues x).val : ℝ) := by
      intro x; exact_mod_cast (prof.bounds (prefixTruncationIndex hq x)).1
    have hhi : ∀ x : (Fin P × Fin (6 * (n + 8))) × Bool, ((prefValues x).val : ℝ) ≤ (maxHi : ℝ) := by
      intro x; exact_mod_cast (prof.bounds (prefixTruncationIndex hq x)).2
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hlo x)
    have h2 := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hhi x)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, nsmul_eq_mul] at h1 h2
    push_cast at h1 h2
    exact ⟨by linarith, by linarith⟩
  have hsum_br_bounds :
      (6 * J * (n + 8) : ℝ) * ((197 / 200 : ℝ) * X) ≤
        (∑ y : (Fin J × Fin (24 + 3 * n)) × Fin 4, (brEnd y : ℝ)) ∧
      (∑ y : (Fin J × Fin (24 + 3 * n)) × Fin 4, (brEnd y : ℝ)) ≤
        (6 * J * (n + 8) : ℝ) * ((203 / 200 : ℝ) * X) := by
    rw [Fintype.sum_prod_type]
    have hper : ∀ jb : Fin J × Fin (24 + 3 * n),
        2 * ((197 / 200 : ℝ) * X) ≤ (∑ side : Fin 4, (brEnd (jb, side) : ℝ)) ∧
        (∑ side : Fin 4, (brEnd (jb, side) : ℝ)) ≤ 2 * ((203 / 200 : ℝ) * X) := by
      rintro ⟨j, idx⟩
      rw [Fin.sum_univ_four]
      have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br j idx
      set blk := bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br j idx
      have h0 : brEnd ((j, idx), 0) = blk.low₁ := rfl
      have h1 : brEnd ((j, idx), 1) = blk.high₁ := rfl
      have h2 : brEnd ((j, idx), 2) = blk.high₂ := rfl
      have h3 : brEnd ((j, idx), 3) = blk.low₂ := rfl
      rw [h0, h1, h2, h3]
      have hp1 := hb.2.2.2.2.2.2.2.2.1
      have hp2 := hb.2.2.2.2.2.2.2.2.2.1
      have hp3 := hb.2.2.2.2.2.2.2.2.2.2.1
      have hp4 := hb.2.2.2.2.2.2.2.2.2.2.2
      rw [Nat.cast_add] at hp1 hp2 hp3 hp4
      exact ⟨by linarith, by linarith⟩
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun jb _ => (hper jb).1)
    have h2 := Finset.sum_le_sum (s := Finset.univ) (fun jb _ => (hper jb).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      nsmul_eq_mul] at h1 h2
    push_cast at h1 h2
    exact ⟨by nlinarith, by nlinarith⟩
  have hsum_wide_bounds :
      (k_wide : ℝ) * (4 * m - 2 * δ * X) ≤ (∑ z : Fin k_wide × Fin 4, (wideEnd z : ℝ)) ∧
      (∑ z : Fin k_wide × Fin 4, (wideEnd z : ℝ)) ≤ (k_wide : ℝ) * (4 * m + 2 * δ * X) := by
    rw [Fintype.sum_prod_type]
    have hper : ∀ wIdx : Fin k_wide,
        4 * m - 2 * δ * X ≤ (∑ side : Fin 4, (wideEnd (wIdx, side) : ℝ)) ∧
        (∑ side : Fin 4, (wideEnd (wIdx, side) : ℝ)) ≤ 4 * m + 2 * δ * X := by
      intro wIdx
      rw [Fin.sum_univ_four]
      have hwp := hwideBlock_props wIdx
      set bl := wideBlocks.get (Fin.cast hlen_w.symm wIdx)
      have h0 : wideEnd (wIdx, 0) = bl.low₁ := rfl
      have h1 : wideEnd (wIdx, 1) = bl.high₁ := rfl
      have h2 : wideEnd (wIdx, 2) = bl.high₂ := rfl
      have h3 : wideEnd (wIdx, 3) = bl.low₂ := rfl
      rw [h0, h1, h2, h3]
      have hm1 := abs_le.mp hwp.2.2.2.2.1
      have hm2 := abs_le.mp hwp.2.2.2.2.2.1
      rw [Nat.cast_add] at hm1 hm2
      exact ⟨by linarith, by linarith⟩
    have h1 := Finset.sum_le_sum (s := Finset.univ) (fun wIdx _ => (hper wIdx).1)
    have h2 := Finset.sum_le_sum (s := Finset.univ) (fun wIdx _ => (hper wIdx).2)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
    exact ⟨h1, h2⟩
  -- hrect_pair_bounds
  have hrect_pair_bounds : ∀ t : Fin (24 * P + 24 * J + 2 * W_diag),
      let loB := min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))
      let hiB := max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))
      loB ≤ (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) ≤ hiB ∧
      loB ≤ (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ∧
      (((rectVal (t, 3)).val + (rectVal (t, 2)).val : ℕ) : ℝ) ≤ hiB := by
    intro t
    let loB := min (2 * (corrLo : ℝ)) (min ((197 / 200 : ℝ) * X) (2 * m - δ * X))
    let hiB := max (2 * (maxHi : ℝ)) (max ((203 / 200 : ℝ) * X) (2 * m + δ * X))
    have hlo1 : loB ≤ 2 * (corrLo : ℝ) := min_le_left _ _
    have hlo2 : loB ≤ (197 / 200 : ℝ) * X := (min_le_right _ _).trans (min_le_left _ _)
    have hlo3 : loB ≤ 2 * m - δ * X := (min_le_right _ _).trans (min_le_right _ _)
    have hhi1 : 2 * (maxHi : ℝ) ≤ hiB := le_max_left _ _
    have hhi2 : (203 / 200 : ℝ) * X ≤ hiB := (le_max_left _ _).trans (le_max_right _ _)
    have hhi3 : 2 * m + δ * X ≤ hiB := (le_max_right _ _).trans (le_max_right _ _)
    dsimp only [rectVal, slotVal, Function.comp_apply, fc2kSlotToSource]
    split_ifs with htP htB
    · have hb0 := prof.bounds (prefixTruncationIndex hq ((⟨t.val / 24, by omega⟩, ⟨2 * (t.val % 24), by omega⟩), false))
      have hb1 := prof.bounds (prefixTruncationIndex hq ((⟨t.val / 24, by omega⟩, ⟨2 * (t.val % 24), by omega⟩), true))
      have hb3 := prof.bounds (prefixTruncationIndex hq ((⟨t.val / 24, by omega⟩, ⟨2 * (t.val % 24) + 1, by omega⟩), false))
      have hb2 := prof.bounds (prefixTruncationIndex hq ((⟨t.val / 24, by omega⟩, ⟨2 * (t.val % 24) + 1, by omega⟩), true))
      dsimp [srcVal, prefixCornerCode, prefValues, truncatePrefixValues, poolProf, generalPrefixProfile_poolValues]
      refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Nat.cast_add]
      · linarith [hlo1, Nat.cast_le (α := ℝ).mpr hb0.1, Nat.cast_le (α := ℝ).mpr hb1.1]
      · linarith [hhi1, Nat.cast_le (α := ℝ).mpr hb0.2, Nat.cast_le (α := ℝ).mpr hb1.2]
      · linarith [hlo1, Nat.cast_le (α := ℝ).mpr hb3.1, Nat.cast_le (α := ℝ).mpr hb2.1]
      · linarith [hhi1, Nat.cast_le (α := ℝ).mpr hb3.2, Nat.cast_le (α := ℝ).mpr hb2.2]
    · let jB : Fin J := ⟨(t.val - 24 * P) / 24, by omega⟩
      let vB : Fin (24 + 3 * n) := ⟨(t.val - 24 * P) % 24, by omega⟩
      have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br jB vB
      have hb1 := hb.2.2.2.2.2.2.2.2.1
      have hb2 := hb.2.2.2.2.2.2.2.2.2.1
      have hb3 := hb.2.2.2.2.2.2.2.2.2.2.1
      have hb4 := hb.2.2.2.2.2.2.2.2.2.2.2
      dsimp only [srcVal, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
      exact ⟨le_trans hlo2 (le_of_lt hb1), le_trans hb2 hhi2,
        le_trans hlo2 (le_of_lt hb3), le_trans hb4 hhi2⟩
    · let wIdx : Fin k_wide := ⟨t.val - (24 * P + 24 * J), by dsimp only [k_wide]; omega⟩
      have hwp := hwideBlock_props wIdx
      have hm1 := abs_le.mp hwp.2.2.2.2.1
      have hm2 := abs_le.mp hwp.2.2.2.2.2.1
      dsimp [srcVal, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint, wIdx] at hm1 hm2 ⊢
      exact ⟨by linarith [hlo3, hm1.1], by linarith [hhi3, hm1.2],
        by linarith [hlo3, hm2.1],
        by linarith [hhi3, hm2.2]⟩
  -- hdiag_mid_diff
  have hdiag_mid_diff :
      |(∑ t ∈ Finset.univ.filter
          (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = true),
          (((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) / 2)) -
       (∑ t ∈ Finset.univ.filter
          (fun t : Fin (24 * P + 24 * J + 2 * W_diag) => decide (t.val % 2 = 0) = false),
          (((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) / 2))| ≤
        ((prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 25 : ℝ) * (J : ℝ) * X +
        (W_diag : ℝ) * δ * X := by
    let K_half := 12 * P + 12 * J + W_diag
    let L_tot := 24 * P + 24 * J + 2 * W_diag
    let midAt (t : Fin L_tot) : ℝ := ((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) / 2
    let fEven (q : Fin K_half) : Fin L_tot := ⟨2 * q.val, by omega⟩
    let fOdd (q : Fin K_half) : Fin L_tot := ⟨2 * q.val + 1, by omega⟩
    have hfEven_inj : Function.Injective fEven := fun a b h =>
      Fin.ext (by have hv := congrArg Fin.val h; dsimp [fEven] at hv; omega)
    have hfOdd_inj : Function.Injective fOdd := fun a b h =>
      Fin.ext (by have hv := congrArg Fin.val h; dsimp [fOdd] at hv; omega)
    have hEven_set : Finset.univ.filter (fun t : Fin L_tot => decide (t.val % 2 = 0) = true) =
        Finset.univ.image fEven := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq, Finset.mem_image]
      exact ⟨fun h => ⟨⟨t.val / 2, by omega⟩, Fin.ext (by dsimp [fEven]; omega)⟩,
        fun ⟨q, hq⟩ => by rw [← hq]; dsimp [fEven]; omega⟩
    have hOdd_set : Finset.univ.filter (fun t : Fin L_tot => decide (t.val % 2 = 0) = false) =
        Finset.univ.image fOdd := by
      ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_false_iff_not, Finset.mem_image]
      exact ⟨fun h => ⟨⟨t.val / 2, by omega⟩, Fin.ext (by dsimp [fOdd]; omega)⟩,
        fun ⟨q, hq⟩ => by rw [← hq]; dsimp [fOdd]; omega⟩
    change |(∑ t ∈ Finset.univ.filter (fun t : Fin L_tot => decide (t.val % 2 = 0) = true), midAt t) -
      (∑ t ∈ Finset.univ.filter (fun t : Fin L_tot => decide (t.val % 2 = 0) = false), midAt t)| ≤ _
    rw [hEven_set, hOdd_set, Finset.sum_image (fun a _ b _ h => hfEven_inj h),
      Finset.sum_image (fun a _ b _ h => hfOdd_inj h), ← Finset.sum_sub_distrib]
    let dTerm (q : Fin K_half) : ℝ := midAt (fEven q) - midAt (fOdd q)
    let gP (ju : Fin P × Fin 12) : Fin K_half := ⟨12 * ju.1.val + ju.2.val, by omega⟩
    let gB (ju : Fin J × Fin 12) : Fin K_half := ⟨12 * P + 12 * ju.1.val + ju.2.val, by omega⟩
    let gW (w : Fin W_diag) : Fin K_half := ⟨12 * P + 12 * J + w.val, by omega⟩
    have hgP_inj : Function.Injective gP := by
      rintro ⟨j₁, u₁⟩ ⟨j₂, u₂⟩ h
      have hv : 12 * j₁.val + u₁.val = 12 * j₂.val + u₂.val := congrArg Fin.val h
      have := u₁.isLt; have := u₂.isLt
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    have hgB_inj : Function.Injective gB := by
      rintro ⟨j₁, u₁⟩ ⟨j₂, u₂⟩ h
      have hv : 12 * P + 12 * j₁.val + u₁.val = 12 * P + 12 * j₂.val + u₂.val := congrArg Fin.val h
      have := u₁.isLt; have := u₂.isLt
      exact Prod.mk.injEq _ _ _ _ |>.mpr ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    have hgW_inj : Function.Injective gW := fun a b h =>
      Fin.ext (by have hv := congrArg Fin.val h; dsimp [gW] at hv; omega)
    let sP : Finset (Fin K_half) := Finset.univ.image gP
    let sB : Finset (Fin K_half) := Finset.univ.image gB
    let sW : Finset (Fin K_half) := Finset.univ.image gW
    have hdisPB : Disjoint sP sB := by
      apply Finset.disjoint_left.mpr; intro q h1 h2
      obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h2
      have hv := congrArg Fin.val hb; dsimp [gP, gB] at hv; omega
    have hdisPW : Disjoint (sP ∪ sB) sW := by
      apply Finset.disjoint_left.mpr; intro q h12 h3
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h3
      rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp h1
        have hv := congrArg Fin.val ha; dsimp [gP, gW] at hv; omega
      · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp h2
        have hv := congrArg Fin.val hb; dsimp [gB, gW] at hv; omega
    have huniv_eq : (Finset.univ : Finset (Fin K_half)) = (sP ∪ sB) ∪ sW := by
      ext q; simp only [Finset.mem_univ, Finset.mem_union, sP, sB, sW, Finset.mem_image, true_and, true_iff]
      by_cases h1 : q.val < 12 * P
      · exact Or.inl (Or.inl ⟨(⟨q.val / 12, by omega⟩, ⟨q.val % 12, by omega⟩),
          Fin.ext (by dsimp [gP]; omega)⟩)
      · by_cases h2 : q.val < 12 * P + 12 * J
        · exact Or.inl (Or.inr ⟨(⟨(q.val - 12 * P) / 12, by omega⟩, ⟨(q.val - 12 * P) % 12, by omega⟩),
            Fin.ext (by dsimp [gB]; omega)⟩)
        · exact Or.inr ⟨⟨q.val - (12 * P + 12 * J), by omega⟩, Fin.ext (by dsimp [gW]; omega)⟩
    change |∑ q : Fin K_half, dTerm q| ≤ _
    rw [huniv_eq, Finset.sum_union hdisPW, Finset.sum_union hdisPB]
    have hbP : |∑ q ∈ sP, dTerm q| ≤ ((prof.totalSpanWords * 49152 : ℕ) : ℝ) := by
      rw [Finset.sum_image (fun a _ b _ h => hgP_inj h), Fintype.sum_prod_type]
      have hstage : ∀ j : Fin P,
          |∑ u : Fin 12, dTerm (gP (j, u))| ≤ ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
        intro j
        have heq_u : ∀ u : Fin 12,
            dTerm (gP (j, u)) =
              ((prof.values ((j, ⟨4 * u.val, by omega⟩), false) : ℝ) + ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2) -
              ((prof.values ((j, ⟨4 * u.val + 2, by omega⟩), false) : ℝ) + ((2 ^ (j.val + 1) : ℕ) : ℝ) / 2) := by
          intro u
          dsimp only [dTerm, midAt, fEven, fOdd, gP, rectVal, slotVal, Function.comp_apply,
            fc2kSlotToSource, rectGap]
          have ht1 : 2 * (12 * j.val + u.val) < 24 * P := by omega
          have ht2 : 2 * (12 * j.val + u.val) + 1 < 24 * P := by omega
          rw [dif_pos ht1, dif_pos ht2, dif_pos ht1, dif_pos ht2]
          have hd1 : 2 * (12 * j.val + u.val) / 24 = j.val := by omega
          have hm1 : 2 * (12 * j.val + u.val) % 24 = 2 * u.val := by omega
          have hd2 : (2 * (12 * j.val + u.val) + 1) / 24 = j.val := by omega
          have hm2 : (2 * (12 * j.val + u.val) + 1) % 24 = 2 * u.val + 1 := by omega
          dsimp only [srcVal, prefixCornerCode, prefValues, truncatePrefixValues, prefixTruncationIndex,
            generalPrefixProfile_poolValues]
          congr 1
          · congr 1
            · exact congrArg (fun x => (prof.values (x, false) : ℝ))
                (Prod.mk.injEq _ _ _ _ |>.mpr ⟨Fin.ext hd1, Fin.ext (by dsimp; rw [hm1]; ring)⟩)
            · rw [hd1]
          · congr 1
            · exact congrArg (fun x => (prof.values (x, false) : ℝ))
                (Prod.mk.injEq _ _ _ _ |>.mpr ⟨Fin.ext hd2, Fin.ext (by dsimp; rw [hm2]; ring)⟩)
            · rw [hd2]
        simp only [heq_u]
        exact fc2k_prefix_diag_stage_diff prof (by omega) j
      calc |∑ j : Fin P, ∑ u : Fin 12, dTerm (gP (j, u))|
          ≤ ∑ j : Fin P, |∑ u : Fin 12, dTerm (gP (j, u))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin P, ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) :=
            Finset.sum_le_sum (fun j _ => hstage j)
        _ = ((prof.totalSpanWords * 49152 : ℕ) : ℝ) := by
            rw [← prof.sum_stageSpanWords, Finset.sum_mul]
            push_cast; rfl
    have hbB : |∑ q ∈ sB, dTerm q| ≤ (9 / 25 : ℝ) * (J : ℝ) * X := by
      rw [Finset.sum_image (fun a _ b _ h => hgB_inj h)]
      have htermB : ∀ ju : Fin J × Fin 12, |dTerm (gB ju)| ≤ (3 / 100 : ℝ) * X := by
        rintro ⟨j, u⟩
        have hmid_eq : ∀ (bit : ℕ) (hbit : bit < 2),
            let t : Fin L_tot := ⟨2 * (12 * P + 12 * j.val + u.val) + bit, by omega⟩
            (197 / 400 : ℝ) * X ≤ midAt t ∧ midAt t ≤ (203 / 400 : ℝ) * X := by
          intro bit hbit t
          have h1 := (hrect_gap t).2.2.1
          have hcast : ((rectVal (t, 1)).val : ℝ) = ((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) := by
            exact_mod_cast h1
          have hmid_pair : midAt t = (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) / 2 := by
            dsimp [midAt]; rw [Nat.cast_add, hcast]; ring
          have hpair_eq : (rectVal (t, 0)).val + (rectVal (t, 1)).val =
              (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br
                ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) / 24, by omega⟩
                ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) % 24, by omega⟩).low₁ +
              (bridgeStageBlock n V_pref radii batches (24 + 3 * n) J hvalid_br
                ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) / 24, by omega⟩
                ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) % 24, by omega⟩).high₁ := by
            dsimp only [rectVal, slotVal, Function.comp_apply, fc2kSlotToSource, t]
            have hnotP : ¬ (2 * (12 * P + 12 * j.val + u.val) + bit < 24 * P) := by omega
            have htB : 2 * (12 * P + 12 * j.val + u.val) + bit < 24 * P + 24 * J := by omega
            rw [dif_neg hnotP, dif_pos htB, dif_neg hnotP, dif_pos htB]
            rfl
          have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br
            ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) / 24, by omega⟩
            ⟨(2 * (12 * P + 12 * j.val + u.val) + bit - 24 * P) % 24, by omega⟩
          have hb_lo := hb.2.2.2.2.2.2.2.2.1
          have hb_hi := hb.2.2.2.2.2.2.2.2.2.1
          rw [hmid_pair, hpair_eq]
          exact ⟨by linarith, by linarith⟩
        have hE := hmid_eq 0 (by decide)
        have hO := hmid_eq 1 (by decide)
        have hfE_eq : fEven (gB (j, u)) = ⟨2 * (12 * P + 12 * j.val + u.val) + 0, by omega⟩ :=
          Fin.ext (by dsimp [fEven, gB])
        have hfO_eq : fOdd (gB (j, u)) = ⟨2 * (12 * P + 12 * j.val + u.val) + 1, by omega⟩ :=
          Fin.ext (by dsimp [fOdd, gB])
        dsimp [dTerm]; rw [hfE_eq, hfO_eq, abs_le]
        exact ⟨by linarith [hE.1, hO.2], by linarith [hE.2, hO.1]⟩
      calc |∑ ju : Fin J × Fin 12, dTerm (gB ju)|
          ≤ ∑ ju : Fin J × Fin 12, |dTerm (gB ju)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ju : Fin J × Fin 12, (3 / 100 : ℝ) * X := Finset.sum_le_sum (fun ju _ => htermB ju)
        _ = (12 * (J : ℝ)) * ((3 / 100 : ℝ) * X) := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
            push_cast; ring
        _ = (9 / 25 : ℝ) * (J : ℝ) * X := by ring
    have hbW : |∑ q ∈ sW, dTerm q| ≤ (W_diag : ℝ) * δ * X := by
      rw [Finset.sum_image (fun a _ b _ h => hgW_inj h)]
      have htermW : ∀ w : Fin W_diag, |dTerm (gW w)| ≤ δ * X := by
        intro w
        have hmid_eq : ∀ (bit : ℕ) (hbit : bit < 2),
            let t : Fin L_tot := ⟨2 * (12 * P + 12 * J + w.val) + bit, by omega⟩
            m - (δ / 2) * X ≤ midAt t ∧ midAt t ≤ m + (δ / 2) * X := by
          intro bit hbit t
          have h1 := (hrect_gap t).2.2.1
          have hcast : ((rectVal (t, 1)).val : ℝ) = ((rectVal (t, 0)).val : ℝ) + (rectGap t : ℝ) := by
            exact_mod_cast h1
          have hmid_pair : midAt t = (((rectVal (t, 0)).val + (rectVal (t, 1)).val : ℕ) : ℝ) / 2 := by
            dsimp [midAt]; rw [Nat.cast_add, hcast]; ring
          let wIdx : Fin k_wide := ⟨2 * (12 * P + 12 * J + w.val) + bit - (24 * P + 24 * J),
            by dsimp only [k_wide]; omega⟩
          have hpair_eq : (rectVal (t, 0)).val + (rectVal (t, 1)).val =
              (wideBlocks.get (Fin.cast hlen_w.symm wIdx)).low₁ +
              (wideBlocks.get (Fin.cast hlen_w.symm wIdx)).high₁ := by
            dsimp only [rectVal, slotVal, Function.comp_apply, fc2kSlotToSource, t]
            have hnotP : ¬ (2 * (12 * P + 12 * J + w.val) + bit < 24 * P) := by omega
            have hnotB : ¬ (2 * (12 * P + 12 * J + w.val) + bit < 24 * P + 24 * J) := by omega
            rw [dif_neg hnotP, dif_neg hnotB, dif_neg hnotP, dif_neg hnotB]
            rfl
          have hm1 := abs_le.mp (hwideBlock_props wIdx).2.2.2.2.1
          rw [hmid_pair, hpair_eq]
          exact ⟨by linarith [hm1.1], by linarith [hm1.2]⟩
        have hE := hmid_eq 0 (by decide)
        have hO := hmid_eq 1 (by decide)
        have hfE_eq : fEven (gW w) = ⟨2 * (12 * P + 12 * J + w.val) + 0, by omega⟩ :=
          Fin.ext (by dsimp [fEven, gW])
        have hfO_eq : fOdd (gW w) = ⟨2 * (12 * P + 12 * J + w.val) + 1, by omega⟩ :=
          Fin.ext (by dsimp [fOdd, gW])
        dsimp [dTerm]; rw [hfE_eq, hfO_eq, abs_le]
        exact ⟨by linarith [hE.1, hO.2], by linarith [hE.2, hO.1]⟩
      calc |∑ w : Fin W_diag, dTerm (gW w)|
          ≤ ∑ w : Fin W_diag, |dTerm (gW w)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : Fin W_diag, δ * X := Finset.sum_le_sum (fun w _ => htermW w)
        _ = (W_diag : ℝ) * δ * X := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have habs1 := abs_add_le (∑ q ∈ sP, dTerm q + ∑ q ∈ sB, dTerm q) (∑ q ∈ sW, dTerm q)
    have habs2 := abs_add_le (∑ q ∈ sP, dTerm q) (∑ q ∈ sB, dTerm q)
    linarith [habs1, habs2, hbP, hbB, hbW]
  -- hord_stage_width
  have hord_stage_width : ∀ (a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ : Fin (P + J + W_ord) → Fin 3 → Fin n),
      |(∑ s : Fin (P + J + W_ord), ∑ l : Fin 3,
          (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
           ((((rowVal (idx, (a₁ s l, false))).val + (rowVal (idx, (a₁ s l, true))) : ℕ) : ℝ) +
            (((rowVal (idx, (b₁ s l, false))).val + (rowVal (idx, (b₁ s l, true))) : ℕ) : ℝ)) / 2 +
           ((((colVal (idx, (c₁ s l, false))).val + (colVal (idx, (c₁ s l, true))) : ℕ) : ℝ) +
            (((colVal (idx, (d₁ s l, false))).val + (colVal (idx, (d₁ s l, true))) : ℕ) : ℝ)) / 2)) -
       (∑ s : Fin (P + J + W_ord), ∑ l : Fin 3,
          (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
           ((((rowVal (idx, (a₂ s l, false))).val + (rowVal (idx, (a₂ s l, true))) : ℕ) : ℝ) +
            (((rowVal (idx, (b₂ s l, false))).val + (rowVal (idx, (b₂ s l, true))) : ℕ) : ℝ)) / 2 +
           ((((colVal (idx, (c₂ s l, false))).val + (colVal (idx, (c₂ s l, true))) : ℕ) : ℝ) +
            (((colVal (idx, (d₂ s l, false))).val + (colVal (idx, (d₂ s l, true))) : ℕ) : ℝ)) / 2))| ≤
        ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) +
        (9 / 50 : ℝ) * (J : ℝ) * X +
        12 * (W_ord : ℝ) * δ * X := by
    intro a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂
    rw [← Finset.sum_sub_distrib]
    let stageDiff (s : Fin (P + J + W_ord)) : ℝ :=
      (∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
         ((((rowVal (idx, (a₁ s l, false))).val + (rowVal (idx, (a₁ s l, true))) : ℕ) : ℝ) +
          (((rowVal (idx, (b₁ s l, false))).val + (rowVal (idx, (b₁ s l, true))) : ℕ) : ℝ)) / 2 +
         ((((colVal (idx, (c₁ s l, false))).val + (colVal (idx, (c₁ s l, true))) : ℕ) : ℝ) +
          (((colVal (idx, (d₁ s l, false))).val + (colVal (idx, (d₁ s l, true))) : ℕ) : ℝ)) / 2)) -
      (∑ l : Fin 3,
        (let idx := bridgeStageLayerIndex (r := 3) (J := P + J + W_ord) rfl s l
         ((((rowVal (idx, (a₂ s l, false))).val + (rowVal (idx, (a₂ s l, true))) : ℕ) : ℝ) +
          (((rowVal (idx, (b₂ s l, false))).val + (rowVal (idx, (b₂ s l, true))) : ℕ) : ℝ)) / 2 +
         ((((colVal (idx, (c₂ s l, false))).val + (colVal (idx, (c₂ s l, true))) : ℕ) : ℝ) +
          (((colVal (idx, (d₂ s l, false))).val + (colVal (idx, (d₂ s l, true))) : ℕ) : ℝ)) / 2))
    let fP (j : Fin P) : Fin (P + J + W_ord) := ⟨j.val, by omega⟩
    let fB (j : Fin J) : Fin (P + J + W_ord) := ⟨P + j.val, by omega⟩
    let fW (w : Fin W_ord) : Fin (P + J + W_ord) := ⟨P + J + w.val, by omega⟩
    have hfP_inj : Function.Injective fP := fun x y h => Fin.ext (by simpa [fP] using congrArg Fin.val h)
    have hfB_inj : Function.Injective fB := fun x y h =>
      Fin.ext (by have hv := congrArg Fin.val h; dsimp [fB] at hv; omega)
    have hfW_inj : Function.Injective fW := fun x y h =>
      Fin.ext (by have hv := congrArg Fin.val h; dsimp [fW] at hv; omega)
    let oP := Finset.univ.image fP
    let oB := Finset.univ.image fB
    let oW := Finset.univ.image fW
    have hdPB : Disjoint oP oB := by
      apply Finset.disjoint_left.mpr; intro s h1 h2
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h1
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
      have hv := congrArg Fin.val hj; dsimp [fP, fB] at hv; omega
    have hdPW : Disjoint (oP ∪ oB) oW := by
      apply Finset.disjoint_left.mpr; intro s h12 h3
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp h3
      rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h1
        have hv := congrArg Fin.val hi; dsimp [fP, fW] at hv; omega
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h2
        have hv := congrArg Fin.val hj; dsimp [fB, fW] at hv; omega
    have huniv_o : (Finset.univ : Finset (Fin (P + J + W_ord))) = (oP ∪ oB) ∪ oW := by
      ext s; simp only [Finset.mem_univ, Finset.mem_union, oP, oB, oW, Finset.mem_image, true_and, true_iff]
      by_cases hs1 : s.val < P
      · exact Or.inl (Or.inl ⟨⟨s.val, hs1⟩, rfl⟩)
      · by_cases hs2 : s.val < P + J
        · exact Or.inl (Or.inr ⟨⟨s.val - P, by omega⟩, Fin.ext (by dsimp [fB]; omega)⟩)
        · exact Or.inr ⟨⟨s.val - (P + J), by omega⟩, Fin.ext (by dsimp [fW]; omega)⟩
    change |∑ s : Fin (P + J + W_ord), stageDiff s| ≤ _
    rw [huniv_o, Finset.sum_union hdPW, Finset.sum_union hdPB]
    have hoP_bound : |∑ s ∈ oP, stageDiff s| ≤ ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) := by
      rw [Finset.sum_image (fun x _ y _ h => hfP_inj h)]
      have hstP : ∀ j : Fin P, |stageDiff (fP j)| ≤ 2 * ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) := by
        intro j
        have hr_eq : ∀ (l : Fin 3) (e : Fin n) (side : Bool),
            (rowVal (bridgeStageLayerIndex rfl (fP j) l, (e, side))).val =
              prof.values ((j, Fin.castLE hq ⟨48 + l.val * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩), side) := by
          intro l e side
          dsimp only [rowVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fP]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          rw [dif_pos j.isLt]
          rfl
        have hc_eq : ∀ (l : Fin 3) (e : Fin n) (side : Bool),
            (colVal (bridgeStageLayerIndex rfl (fP j) l, (e, side))).val =
              prof.values ((j, Fin.castLE hq ⟨48 + (3 + l.val) * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩), side) := by
          intro l e side
          dsimp only [colVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fP]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          rw [dif_pos j.isLt]
          rfl
        dsimp [stageDiff]
        simp only [hr_eq, hc_eq]
        exact fc2k_prefix_stage_six_blocks_width prof hq hn_pos j
          (a₁ (fP j)) (b₁ (fP j)) (a₂ (fP j)) (b₂ (fP j))
          (c₁ (fP j)) (d₁ (fP j)) (c₂ (fP j)) (d₂ (fP j))
      calc |∑ j : Fin P, stageDiff (fP j)|
          ≤ ∑ j : Fin P, |stageDiff (fP j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin P, 2 * ((prof.stageSpanWords j * 49152 : ℕ) : ℝ) :=
            Finset.sum_le_sum (fun j _ => hstP j)
        _ = ((2 * prof.totalSpanWords * 49152 : ℕ) : ℝ) := by
            rw [← Finset.mul_sum, ← prof.sum_stageSpanWords]
            push_cast
            rw [← Finset.sum_mul]
            ring
    have hoB_bound : |∑ s ∈ oB, stageDiff s| ≤ (9 / 50 : ℝ) * (J : ℝ) * X := by
      rw [Finset.sum_image (fun x _ y _ h => hfB_inj h)]
      have hstB : ∀ j : Fin J, |stageDiff (fB j)| ≤ (9 / 50 : ℝ) * X := by
        intro j
        have hr_b : ∀ (l : Fin 3) (e : Fin n),
            let idx := bridgeStageLayerIndex rfl (fB j) l
            (197 / 200 : ℝ) * X ≤ (((rowVal (idx, (e, false))).val + (rowVal (idx, (e, true))) : ℕ) : ℝ) ∧
            (((rowVal (idx, (e, false))).val + (rowVal (idx, (e, true))) : ℕ) : ℝ) ≤ (203 / 200 : ℝ) * X := by
          intro l e
          dsimp only [rowVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fB]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          have hnotP : ¬ (P + j.val < P) := by omega
          have hsB : P + j.val < P + J := by omega
          rw [dif_neg hnotP, dif_pos hsB, dif_neg hnotP, dif_pos hsB]
          let j' : Fin J := ⟨P + j.val - P, by omega⟩
          let v' : Fin (24 + 3 * n) := ⟨24 + l.val * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
          have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br j' v'
          dsimp only [srcVal, fc2kOrdCorner, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
          exact ⟨le_of_lt hb.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.1⟩
        have hc_b : ∀ (l : Fin 3) (e : Fin n),
            let idx := bridgeStageLayerIndex rfl (fB j) l
            (197 / 200 : ℝ) * X ≤ (((colVal (idx, (e, false))).val + (colVal (idx, (e, true))) : ℕ) : ℝ) ∧
            (((colVal (idx, (e, false))).val + (colVal (idx, (e, true))) : ℕ) : ℝ) ≤ (203 / 200 : ℝ) * X := by
          intro l e
          dsimp only [colVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fB]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          have hnotP : ¬ (P + j.val < P) := by omega
          have hsB : P + j.val < P + J := by omega
          rw [dif_neg hnotP, dif_pos hsB, dif_neg hnotP, dif_pos hsB]
          let j' : Fin J := ⟨P + j.val - P, by omega⟩
          let v' : Fin (24 + 3 * n) := ⟨24 + l.val * n + e.val, by have := l.isLt; have := e.isLt; nlinarith⟩
          have hb := bridgeStageBlock_pair_sum_and_window_bounds hX_pos hradii_pos hvalid_br j' v'
          dsimp only [srcVal, fc2kOrdCorner, brEnd, bridgeStageEndpoint, DoublePair.endpoint]
          exact ⟨le_of_lt hb.2.2.2.2.2.2.2.2.2.2.1, hb.2.2.2.2.2.2.2.2.2.2.2⟩
        dsimp [stageDiff]
        rw [← Finset.sum_sub_distrib, Fin.sum_univ_three, abs_le]
        have r0a := hr_b 0 (a₁ (fB j) 0); have r0b := hr_b 0 (b₁ (fB j) 0); have r0c := hr_b 0 (a₂ (fB j) 0); have r0d := hr_b 0 (b₂ (fB j) 0)
        have r1a := hr_b 1 (a₁ (fB j) 1); have r1b := hr_b 1 (b₁ (fB j) 1); have r1c := hr_b 1 (a₂ (fB j) 1); have r1d := hr_b 1 (b₂ (fB j) 1)
        have r2a := hr_b 2 (a₁ (fB j) 2); have r2b := hr_b 2 (b₁ (fB j) 2); have r2c := hr_b 2 (a₂ (fB j) 2); have r2d := hr_b 2 (b₂ (fB j) 2)
        have c0a := hc_b 0 (c₁ (fB j) 0); have c0b := hc_b 0 (d₁ (fB j) 0); have c0c := hc_b 0 (c₂ (fB j) 0); have c0d := hc_b 0 (d₂ (fB j) 0)
        have c1a := hc_b 1 (c₁ (fB j) 1); have c1b := hc_b 1 (d₁ (fB j) 1); have c1c := hc_b 1 (c₂ (fB j) 1); have c1d := hc_b 1 (d₂ (fB j) 1)
        have c2a := hc_b 2 (c₁ (fB j) 2); have c2b := hc_b 2 (d₁ (fB j) 2); have c2c := hc_b 2 (c₂ (fB j) 2); have c2d := hc_b 2 (d₂ (fB j) 2)
        dsimp only at r0a r0b r0c r0d r1a r1b r1c r1d r2a r2b r2c r2d c0a c0b c0c c0d c1a c1b c1c c1d c2a c2b c2c c2d
        exact ⟨by linarith, by linarith⟩
      calc |∑ j : Fin J, stageDiff (fB j)|
          ≤ ∑ j : Fin J, |stageDiff (fB j)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin J, (9 / 50 : ℝ) * X := Finset.sum_le_sum (fun j _ => hstB j)
        _ = (9 / 50 : ℝ) * (J : ℝ) * X := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have hoW_bound : |∑ s ∈ oW, stageDiff s| ≤ 12 * (W_ord : ℝ) * δ * X := by
      rw [Finset.sum_image (fun x _ y _ h => hfW_inj h)]
      have hstW : ∀ w : Fin W_ord, |stageDiff (fW w)| ≤ 12 * δ * X := by
        intro w
        have hr_w : ∀ (l : Fin 3) (e : Fin n),
            let idx := bridgeStageLayerIndex rfl (fW w) l
            2 * m - δ * X ≤ (((rowVal (idx, (e, false))).val + (rowVal (idx, (e, true))) : ℕ) : ℝ) ∧
            (((rowVal (idx, (e, false))).val + (rowVal (idx, (e, true))) : ℕ) : ℝ) ≤ 2 * m + δ * X := by
          intro l e
          dsimp only [rowVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fW]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          have hnotP : ¬ (P + J + w.val < P) := by omega
          have hnotB : ¬ (P + J + w.val < P + J) := by omega
          rw [dif_neg hnotP, dif_neg hnotB, dif_neg hnotP, dif_neg hnotB]
          let wIdx : Fin k_wide := ⟨2 * W_diag + (P + J + w.val - (P + J)) * (3 * n) + l.val * n + e.val, by
            have hsub : P + J + w.val - (P + J) = w.val := by omega
            rw [hsub]; dsimp only [k_wide]; have := w.isLt; have := l.isLt; have := e.isLt; nlinarith⟩
          have hm1 := abs_le.mp (hwideBlock_props wIdx).2.2.2.2.1
          dsimp [srcVal, fc2kOrdCorner, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint, wIdx] at hm1 ⊢
          exact ⟨by linarith [hm1.1], by linarith [hm1.2]⟩
        have hc_w : ∀ (l : Fin 3) (e : Fin n),
            let idx := bridgeStageLayerIndex rfl (fW w) l
            2 * m - δ * X ≤ (((colVal (idx, (e, false))).val + (colVal (idx, (e, true))) : ℕ) : ℝ) ∧
            (((colVal (idx, (e, false))).val + (colVal (idx, (e, true))) : ℕ) : ℝ) ≤ 2 * m + δ * X := by
          intro l e
          dsimp only [colVal, slotVal, Function.comp_apply, fc2kSlotToSource, bridgeStageLayerIndex, fW]
          simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
          have hnotP : ¬ (P + J + w.val < P) := by omega
          have hnotB : ¬ (P + J + w.val < P + J) := by omega
          rw [dif_neg hnotP, dif_neg hnotB, dif_neg hnotP, dif_neg hnotB]
          let wIdx : Fin k_wide := ⟨2 * W_diag + (P + J + w.val - (P + J)) * (3 * n) + l.val * n + e.val, by
            have hsub : P + J + w.val - (P + J) = w.val := by omega
            rw [hsub]; dsimp only [k_wide]; have := w.isLt; have := l.isLt; have := e.isLt; nlinarith⟩
          have hm2 := abs_le.mp (hwideBlock_props wIdx).2.2.2.2.2.1
          dsimp [srcVal, fc2kOrdCorner, wideEnd, wideCast, doublePairSequenceEndpoint, DoublePair.endpoint, wIdx] at hm2 ⊢
          exact ⟨by linarith [hm2.1], by linarith [hm2.2]⟩
        dsimp [stageDiff]
        rw [← Finset.sum_sub_distrib, Fin.sum_univ_three, abs_le]
        have r0a := hr_w 0 (a₁ (fW w) 0); have r0b := hr_w 0 (b₁ (fW w) 0); have r0c := hr_w 0 (a₂ (fW w) 0); have r0d := hr_w 0 (b₂ (fW w) 0)
        have r1a := hr_w 1 (a₁ (fW w) 1); have r1b := hr_w 1 (b₁ (fW w) 1); have r1c := hr_w 1 (a₂ (fW w) 1); have r1d := hr_w 1 (b₂ (fW w) 1)
        have r2a := hr_w 2 (a₁ (fW w) 2); have r2b := hr_w 2 (b₁ (fW w) 2); have r2c := hr_w 2 (a₂ (fW w) 2); have r2d := hr_w 2 (b₂ (fW w) 2)
        have c0a := hc_w 0 (c₁ (fW w) 0); have c0b := hc_w 0 (d₁ (fW w) 0); have c0c := hc_w 0 (c₂ (fW w) 0); have c0d := hc_w 0 (d₂ (fW w) 0)
        have c1a := hc_w 1 (c₁ (fW w) 1); have c1b := hc_w 1 (d₁ (fW w) 1); have c1c := hc_w 1 (c₂ (fW w) 1); have c1d := hc_w 1 (d₂ (fW w) 1)
        have c2a := hc_w 2 (c₁ (fW w) 2); have c2b := hc_w 2 (d₁ (fW w) 2); have c2c := hc_w 2 (c₂ (fW w) 2); have c2d := hc_w 2 (d₂ (fW w) 2)
        dsimp only at r0a r0b r0c r0d r1a r1b r1c r1d r2a r2b r2c r2d c0a c0b c0c c0d c1a c1b c1c c1d c2a c2b c2c c2d
        exact ⟨by linarith, by linarith⟩
      calc |∑ w : Fin W_ord, stageDiff (fW w)|
          ≤ ∑ w : Fin W_ord, |stageDiff (fW w)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _w : Fin W_ord, 12 * δ * X := Finset.sum_le_sum (fun w _ => hstW w)
        _ = 12 * (W_ord : ℝ) * δ * X := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    have habs_o1 := abs_add_le (∑ s ∈ oP, stageDiff s + ∑ s ∈ oB, stageDiff s) (∑ s ∈ oW, stageDiff s)
    have habs_o2 := abs_add_le (∑ s ∈ oP, stageDiff s) (∑ s ∈ oB, stageDiff s)
    linarith [habs_o1, habs_o2, hoP_bound, hoB_bound, hoW_bound]
  exact ⟨{
    J := J
    hJ_le := hJ_le
    rectVal := rectVal
    rowVal := rowVal
    colVal := colVal
    rectGap := rectGap
    ordGap := ordGap
    hrect_inj := fun x y h => Sum.inl.inj (hslot_inj h)
    hrow_inj := fun x y h => Sum.inl.inj (Sum.inr.inj (hslot_inj h))
    hcol_inj := fun x y h => Sum.inr.inj (Sum.inr.inj (hslot_inj h))
    hrow_ne_col := fun x y h => by have heq := hslot_inj (Subtype.ext h); cases heq
    hrow_ne_rect := fun x y h => by have heq := hslot_inj (Subtype.ext h); cases heq
    hcol_ne_rect := fun x y h => by have heq := hslot_inj (Subtype.ext h); cases heq
    hrect_gap := hrect_gap
    hrow_gap := hrow_gap
    hcol_gap := hcol_gap
    Rm := Rm
    Ra := Ra
    hm_grid := by dsimp [Rm]; rw [hm_filter_eq]; exact hm_res.1
    ha_grid := by dsimp [Ra]; rw [ha_filter_eq]; exact ha_res.1
    hRm_sum := rfl
    hRa_sum := rfl
    hRm_lower := by dsimp [Rm]; rw [hm_filter_eq]; exact hm_res.2
    hRa_lower := by dsimp [Ra]; rw [ha_filter_eq]; exact ha_res.2
    edgeRadius := edgeRadius
    hedge_grid := fun e => (hedge_all e).1
    hedge_sum := fun _ => rfl
    hedge_lower := fun e => (hedge_all e).2
    V_pref := V_pref
    V_br := V_br
    V_wide := V_wide
    hV_pref_sub := hV_pref_sub
    hV_pref_card := hV_pref_card
    hV_br_card := hV_br_card
    hV_wide_out := hV_wide_out
    hrole_union := hrole_union
    hrole_sum_upper := by
      rw [hsum_slot_eq_src]
      have hkw : (k_wide : ℝ) = 2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ)) := by
        dsimp only [k_wide]; push_cast; ring
      have hw_hi := hsum_wide_bounds.2
      rw [hkw] at hw_hi
      linarith [hsum_pref_bounds.2, hsum_br_bounds.2, hw_hi]
    hrole_sum_lower := by
      rw [hsum_slot_eq_src]
      have hkw : (k_wide : ℝ) = 2 * (W_diag : ℝ) + (W_ord : ℝ) * (3 * (n : ℝ)) := by
        dsimp only [k_wide]; push_cast; ring
      have hw_lo := hsum_wide_bounds.1
      rw [hkw] at hw_lo
      linarith [hsum_pref_bounds.1, hsum_br_bounds.1, hw_lo]
    hrect_pair_bounds := hrect_pair_bounds
    hdiag_mid_diff := hdiag_mid_diff
    hord_stage_width := hord_stage_width
  }⟩

end

end Sude
