import Sude.UpperTailSchedule
import Sude.NarrowScalarPhase
import Sude.NarrowSeedPhysical

/-!
# Unbounded Growth-Trace & Step-Grid Construction for the Open Upper Tail (`n ≥ 35,735`)

Executes the 5-part narrowed growth schedule for every `n ≥ 35,735` (unbounded above):
1. **Seed Extraction & Consecutive Sorted Narrowing** (`utSeedStages n` stages of equal gap
   `g = 2 * h0` with `6 ∣ g` and `1 ≤ h0 ≤ utH0Max n` from `Pool 2`),
2. **`AP_1` -> `AP_2` Two-Sub-Phase Crossing** on `Pool 1` up to `R_ap2 ≥ 12000 * utLn n * g`,
3. **Montgomery–Vaughan (`MV`) Crossing** on remaining `Pool 2` up to `R_mv ≥ (76 / 1000) * utX n`,
4. **`StepBoost` Iteration** (`utStepsBoost n` steps on remaining `Pool 2`) up to `R_last`
   satisfying `((h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) + (10 / 1000 : ℝ) * utX n ≤ (R_last : ℝ)`,
5. **`CompleteStepGrid` Assembly** of step `g = 2 * h0` and exact radius `R_last = (stages.map gap).sum`,
   with global pairwise disjointness in `Pool 1 ∪ Pool 2` and strict midpoint spread `< utMidWidth n`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Section 1: Residue-Class Helpers for `6 ∣ g` -/

/-- Residues below `g` congruent to `1` or `5` modulo `6`. -/
def utClassesSix (g : ℕ) : Finset ℕ :=
  (Finset.range g).filter (fun a => a % 6 = 1 ∨ a % 6 = 5)

/-- Coprime positive residues below `g`. -/
def utClassesCoprime (g : ℕ) : Finset ℕ :=
  (Finset.range g).filter (fun a => 0 < a ∧ Nat.Coprime g a)

theorem utClassesSix_card {g : ℕ} (hg6 : 6 ∣ g) :
    (utClassesSix g).card * 3 = g := by
  obtain ⟨m, rfl⟩ := hg6
  induction m with
  | zero =>
    dsimp [utClassesSix]
    rfl
  | succ k ih =>
    have hsplit : Finset.range (6 * (k + 1)) =
        Finset.range (6 * k) ∪ (Finset.range 6).image (fun j => 6 * k + j) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_union, Finset.mem_image]
      constructor
      · intro hx
        by_cases hlt : x < 6 * k
        · exact Or.inl hlt
        · exact Or.inr ⟨x - 6 * k, by omega, by omega⟩
      · rintro (hx | ⟨j, hj, rfl⟩)
        · omega
        · omega
    have hdisj : Disjoint (Finset.range (6 * k))
        ((Finset.range 6).image (fun j => 6 * k + j)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_range, Finset.mem_image] at hx1 hx2
      rcases hx2 with ⟨j, _, rfl⟩
      omega
    have htail_card : (((Finset.range 6).image (fun j => 6 * k + j)).filter
        (fun a => a % 6 = 1 ∨ a % 6 = 5)).card = 2 := by
      have hflt : (((Finset.range 6).image (fun j => 6 * k + j)).filter
          (fun a => a % 6 = 1 ∨ a % 6 = 5)) =
          ((Finset.range 6).filter (fun j => j % 6 = 1 ∨ j % 6 = 5)).image
            (fun j => 6 * k + j) := by
        ext a
        simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
        constructor
        · rintro ⟨⟨j, hj, rfl⟩, hmod⟩
          exact ⟨j, ⟨hj, by omega⟩, rfl⟩
        · rintro ⟨j, ⟨hj, hmod⟩, rfl⟩
          exact ⟨⟨j, hj, rfl⟩, by omega⟩
      rw [hflt, Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
      decide
    dsimp [utClassesSix] at ih ⊢
    rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint
      (hdisj.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)), htail_card]
    omega

theorem utClassesSix_card_real {g : ℕ} (hg6 : 6 ∣ g) :
    ((utClassesSix g).card : ℝ) = (g : ℝ) / 3 := by
  have h := utClassesSix_card hg6
  have hR : ((utClassesSix g).card : ℝ) * 3 = (g : ℝ) := by exact_mod_cast h
  linarith

theorem prime_gt_three_mod_mem_utClassesSix {p g : ℕ}
    (hp : Nat.Prime p) (hp3 : 3 < p) (hg_pos : 0 < g) (hg6 : 6 ∣ g) :
    p % g ∈ utClassesSix g := by
  rw [utClassesSix, Finset.mem_filter, Finset.mem_range]
  refine ⟨Nat.mod_lt p hg_pos, ?_⟩
  have hmod6 : (p % g) % 6 = p % 6 := Nat.mod_mod_of_dvd p hg6
  rw [hmod6]
  have hp2 : p % 2 = 1 := hp.eq_two_or_odd.resolve_left (by omega)
  have hp_not3 : ¬ (3 ∣ p) := fun hdvd => by
    have heq := (Nat.dvd_prime hp).mp hdvd
    omega
  have hp3_ne : p % 3 ≠ 0 := by rwa [Nat.dvd_iff_mod_eq_zero] at hp_not3
  omega

theorem utClassesCoprime_card {g : ℕ} (hg1 : 1 < g) :
    (utClassesCoprime g).card = Nat.totient g := by
  rw [Nat.totient_eq_card_coprime, utClassesCoprime]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨ha, _, hcop⟩
    exact ⟨ha, hcop⟩
  · rintro ⟨ha, hcop⟩
    refine ⟨ha, ?_, hcop⟩
    by_contra ha0
    have h0 : a = 0 := by omega
    subst h0
    rw [Nat.coprime_zero_right] at hcop
    omega

theorem prime_gt_gap_mod_mem_utClassesCoprime {p g : ℕ}
    (hp : Nat.Prime p) (hg1 : 1 < g) (hgp : g < p) :
    p % g ∈ utClassesCoprime g := by
  have hg_pos : 0 < g := by omega
  have hnot_dvd : ¬ (p ∣ g) := fun hdvd => by
    have hle := Nat.le_of_dvd hg_pos hdvd
    omega
  have hcop_pg : Nat.Coprime p g := (Nat.Prime.coprime_iff_not_dvd hp).mpr hnot_dvd
  have hcop_gp : Nat.Coprime g p := hcop_pg.symm
  have hcop_mod : Nat.Coprime g (p % g) := by
    rwa [Nat.coprime_iff_gcd_eq_one, Nat.gcd_rec, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_comm] at hcop_gp
  have hmod_pos : 0 < p % g := by
    by_contra h0
    have hz : p % g = 0 := by omega
    rw [hz, Nat.coprime_zero_right] at hcop_mod
    omega
  rw [utClassesCoprime, Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.mod_lt p hg_pos, hmod_pos, hcop_mod⟩

/-! ## Section 2: `StepGapChain` Concatenation & `CompleteStepGrid` Indexing -/

theorem stepGapChain_append {K : Type*} (gap : K → ℕ) (step : ℕ) :
    ∀ (L₁ L₂ : List K) (R : ℕ),
      StepGapChain gap step R L₁ →
      StepGapChain gap step (R + (L₁.map gap).sum) L₂ →
      StepGapChain gap step R (L₁ ++ L₂)
  | [], L₂, R, _, h2 => by simpa using h2
  | k :: ks, L₂, R, h1, h2 => by
    cases h1 with
    | cons _ _ _ hdiv hjoin htail =>
      apply StepGapChain.cons R k (ks ++ L₂) hdiv hjoin
      apply stepGapChain_append gap step ks L₂ (R + gap k) htail
      simpa [List.map_cons, List.sum_cons, add_assoc] using h2

theorem stepGapChain_finRange {K : Type*} (gap : K → ℕ) (step : ℕ)
    (L : List K) (R : ℕ) (hchain : StepGapChain gap step R L) :
    StepGapChain (fun i : Fin L.length => gap (L.get i)) step R (List.finRange L.length) := by
  induction hchain with
  | nil R =>
    simpa using StepGapChain.nil R
  | cons R k ks hdiv hjoin htail ih =>
    have hfr : List.finRange (ks.length + 1) = 0 :: (List.finRange ks.length).map Fin.succ := by
      apply List.ext_get
      · simp
      · intro m hm1 hm2
        cases m <;> simp
    change StepGapChain (fun i : Fin (ks.length + 1) => gap ((k :: ks).get i))
      step R (List.finRange (ks.length + 1))
    rw [hfr]
    refine StepGapChain.cons R 0 ((List.finRange ks.length).map Fin.succ) hdiv hjoin ?_
    have hmap : ∀ (m : List (Fin ks.length)) (R₀ : ℕ),
        StepGapChain (fun i : Fin ks.length => gap (ks.get i)) step R₀ m →
        StepGapChain (fun i : Fin (ks.length + 1) => gap ((k :: ks).get i)) step R₀ (m.map Fin.succ) := by
      intro m
      induction m with
      | nil =>
        intro R₀ _
        exact StepGapChain.nil R₀
      | cons a as ihm =>
        intro R₀ hm
        cases hm with
        | cons _ _ _ hd hj ht =>
          exact StepGapChain.cons R₀ a.succ (as.map Fin.succ) hd hj (ihm (R₀ + gap (ks.get a)) ht)
    exact hmap (List.finRange ks.length) (R + gap k) ih

theorem completeStepGrid_univ_of_stepGapChain {K : Type*} (gap : K → ℕ) (step : ℕ)
    (L : List K) (hs : 0 < step) (hchain : StepGapChain gap step 0 L) :
    CompleteStepGrid (Finset.univ : Finset (Fin L.length)) (fun i => gap (L.get i))
      step (L.map gap).sum := by
  let gapIdx : Fin L.length → ℕ := fun i => gap (L.get i)
  have hbase : CompleteStepGrid (∅ : Finset (Fin L.length)) gapIdx step 0 := by
    intro t ht _
    have ht0 : t = 0 := by omega
    subst ht0
    exact ⟨∅, Finset.empty_subset _, by simp⟩
  have hfin := stepGapChain_finRange gap step L 0 hchain
  have hext := extend_step_gap_chain gapIdx step ∅ 0 (List.finRange L.length)
    hs hbase (Nat.dvd_zero step) (List.nodup_finRange L.length) (fun _ _ => Finset.notMem_empty _) hfin
  have hunion : (∅ : Finset (Fin L.length)) ∪ (List.finRange L.length).toFinset = Finset.univ := by
    ext i
    simp
  have hsum : ((List.finRange L.length).map gapIdx).sum = (L.map gap).sum := by
    have hmap_eq : (List.finRange L.length).map gapIdx = L.map gap := by
      apply List.ext_get
      · simp
      · intro m hm1 hm2
        simp [gapIdx]
    rw [hmap_eq]
  rw [hunion, zero_add, hsum] at hext
  exact hext

/-! ## Section 3: Pool Membership & Interval Helpers -/

theorem ut_pool1_elem_props
    (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n p : ℕ} (hn : 35735 ≤ n) (hp : p ∈ apInterval (utPool1Lo n) (utPool1Hi n) 2 1) :
    Nat.Prime p ∧ Odd p ∧ p ∈ pool n ∧ 5 < p ∧
    utPool1Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool1Lo n + (255 / 1000 : ℝ) * utX n ∧
    (p : ℝ) < utPool1Lo n + 2 * utMidWidth n := by
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hlo_nn : 0 ≤ utPool1Lo n := by dsimp [utPool1Lo]; positivity
  have hhi_nn : 0 ≤ utPool1Hi n := by dsimp [utPool1Hi]; positivity
  obtain ⟨hprime, hgt, hle, hmod⟩ := (mem_apInterval_iff _ _ 2 1 hlo_nn hhi_nn p).mp hp
  have hodd : Odd p := by rw [Nat.odd_iff]; exact_mod_cast hmod
  have hpool : p ∈ pool n :=
    even_apInterval_subset_pool n (utPool1Lo n) (utPool1Hi n) 2 1
      (by dsimp [utPool1Lo]; linarith) (by dsimp [utPool1Lo, utPool1Hi]; linarith)
      (by dsimp [utPool1Hi, utX]; linarith) (by decide) (by decide) p hp
  have hp5R : (5 : ℝ) < (p : ℝ) := by dsimp [utPool1Lo] at hgt; linarith
  have hp5 : 5 < p := by exact_mod_cast hp5R
  have hhi_eq : utPool1Hi n = utPool1Lo n + (255 / 1000 : ℝ) * utX n := by
    dsimp [utPool1Lo, utPool1Hi]; ring
  have hlt_mid : (p : ℝ) < utPool1Lo n + 2 * utMidWidth n := by
    dsimp [utPool1Lo, utPool1Hi, utMidWidth] at hle ⊢; linarith
  exact ⟨hprime, hodd, hpool, hp5, hgt.le, by linarith, hlt_mid⟩

theorem ut_pool2_elem_props
    (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n p : ℕ} (hn : 35735 ≤ n) (hp : p ∈ apInterval (utPool2Lo n) (utPool2Hi n) 2 1) :
    Nat.Prime p ∧ Odd p ∧ p ∈ pool n ∧ 5 < p ∧ utSeedCap n < p ∧
    utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool2Hi n ∧
    (p : ℝ) ≤ utPool2Lo n + (255 / 1000 : ℝ) * utX n ∧
    (p : ℝ) < utPool2Lo n + 2 * utMidWidth n := by
  obtain ⟨_, hX_283, _, hlog23, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX : (283 * 10 ^ 8 : ℝ) ≤ utX n := by dsimp [utX]; exact hX_283.le
  have hlogX_pos : 0 < Real.log (utX n) := by dsimp [utX]; linarith
  have hlo_nn : 0 ≤ utPool2Lo n := by dsimp [utPool2Lo]; positivity
  have hhi_nn : 0 ≤ utPool2Hi n := by dsimp [utPool2Hi]; positivity
  obtain ⟨hprime, hgt, hle, hmod⟩ := (mem_apInterval_iff _ _ 2 1 hlo_nn hhi_nn p).mp hp
  have hodd : Odd p := by rw [Nat.odd_iff]; exact_mod_cast hmod
  have hpool : p ∈ pool n :=
    even_apInterval_subset_pool n (utPool2Lo n) (utPool2Hi n) 2 1
      (by dsimp [utPool2Lo]; linarith) (by dsimp [utPool2Lo, utPool2Hi]; linarith)
      (by dsimp [utPool2Hi, utX]; linarith) (by decide) (by decide) p hp
  have hp5R : (5 : ℝ) < (p : ℝ) := by dsimp [utPool2Lo] at hgt; linarith
  have hp5 : 5 < p := by exact_mod_cast hp5R
  have hcap_lt : (utSeedCap n : ℝ) < (p : ℝ) := by
    have h1 : 2 * utLn n ≤ utL2X n := by dsimp [utLn]; omega
    have h1R : 2 * (utLn n : ℝ) ≤ (utL2X n : ℝ) := by exact_mod_cast h1
    have h2 : (utL2X n : ℝ) ≤ 2 * Real.log (utX n) := Nat.floor_le (by linarith)
    have hlog_ub : Real.log (utX n) ≤ utX n / 1024 + 10 := by
      have hsplit : utX n = (2 : ℝ) ^ 10 * (utX n / 1024) := by ring
      have hsub := Real.log_le_sub_one_of_pos (by linarith : 0 < utX n / 1024)
      have hlog2 : Real.log 2 < 1 := lt_trans Real.log_two_lt_d9 (by norm_num)
      rw [hsplit, Real.log_mul (by positivity) (by linarith), Real.log_pow]
      push_cast; linarith
    have hcap_eq : (utSeedCap n : ℝ) = 6 * ((utLn n : ℝ) + 5) := by dsimp [utSeedCap]; push_cast; ring
    dsimp [utPool2Lo] at hgt
    linarith
  have hhi_eq : utPool2Hi n = utPool2Lo n + (255 / 1000 : ℝ) * utX n := by
    dsimp [utPool2Lo, utPool2Hi]; ring
  have hlt_mid : (p : ℝ) < utPool2Lo n + 2 * utMidWidth n := by
    dsimp [utPool2Lo, utPool2Hi, utMidWidth] at hle ⊢; linarith
  exact ⟨hprime, hodd, hpool, hp5, by exact_mod_cast hcap_lt, hgt.le, hle, by linarith, hlt_mid⟩

/-! ## Section 4: Seed Extraction & Consecutive Sorted Narrowing on `Pool 2` -/

private def seedGroupLows (candidates : Finset ℕ) (r Q : ℕ)
    (hcard : candidates.card = r * Q) (j : Fin r) : Finset ℕ :=
  Finset.univ.image (fun i : Fin Q => sortedSeedLower candidates r Q hcard (j, i))

private theorem seedGroupLows_props (candidates : Finset ℕ) (r Q g : ℕ)
    (_hQ : 0 < Q) (hg : 0 < g) (hcard : candidates.card = r * Q)
    (hmatch : PairwiseDisjointPairs candidates g) :
    (∀ j : Fin r, seedGroupLows candidates r Q hcard j ⊆ candidates) ∧
    (∀ j : Fin r, (seedGroupLows candidates r Q hcard j).card = Q) ∧
    (∀ j : Fin r, PairwiseDisjointPairs (seedGroupLows candidates r Q hcard j) g) ∧
    (∀ j : Fin r, (pairFootprint (seedGroupLows candidates r Q hcard j) g).card = 2 * Q) ∧
    (∀ j₁ j₂ : Fin r, j₁ ≠ j₂ →
      Disjoint (pairFootprint (seedGroupLows candidates r Q hcard j₁) g)
        (pairFootprint (seedGroupLows candidates r Q hcard j₂) g)) := by
  have hsub : ∀ j : Fin r, seedGroupLows candidates r Q hcard j ⊆ candidates := by
    intro j x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact sortedSeedLower_mem candidates r Q hcard (j, i)
  have hcard_j : ∀ j : Fin r, (seedGroupLows candidates r Q hcard j).card = Q := by
    intro j
    dsimp [seedGroupLows]
    rw [Finset.card_image_of_injective]
    · simp
    · intro i₁ i₂ h
      have heq := sortedSeedLower_injective candidates r Q hcard h
      exact (Prod.mk.inj heq).2
  have hmatch_j : ∀ j : Fin r, PairwiseDisjointPairs (seedGroupLows candidates r Q hcard j) g :=
    fun j p hp q hq hpq => hmatch p (hsub j hp) q (hsub j hq) hpq
  have hfoot_card : ∀ j : Fin r, (pairFootprint (seedGroupLows candidates r Q hcard j) g).card = 2 * Q := by
    intro j
    rw [pairFootprint_card _ g hg (hmatch_j j), hcard_j j]
  have hdisj : ∀ j₁ j₂ : Fin r, j₁ ≠ j₂ →
      Disjoint (pairFootprint (seedGroupLows candidates r Q hcard j₁) g)
        (pairFootprint (seedGroupLows candidates r Q hcard j₂) g) := by
    intro j₁ j₂ hj
    have hinj := sortedSeedEndpoint_injective candidates r Q g hcard hg hmatch
    have hmem_end : ∀ (j : Fin r) (z : ℕ),
        z ∈ pairFootprint (seedGroupLows candidates r Q hcard j) g →
        ∃ (i : Fin Q) (b : Bool), sortedSeedEndpoint candidates r Q g hcard ((j, i), b) = z := by
      intro j z hz
      rcases Finset.mem_union.mp hz with hzL | hzR
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hzL
        exact ⟨i, false, by simp [sortedSeedEndpoint, pairEndpoint]⟩
      · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hzR
        obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
        exact ⟨i, true, by simp [sortedSeedEndpoint, pairEndpoint]⟩
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    obtain ⟨i₁, b₁, he1⟩ := hmem_end j₁ z hz1
    obtain ⟨i₂, b₂, he2⟩ := hmem_end j₂ z hz2
    have heq := hinj (he1.trans he2.symm)
    exact hj (Prod.mk.inj (Prod.mk.inj heq).1).1
  exact ⟨hsub, hcard_j, hmatch_j, hfoot_card, hdisj⟩

/-- Extract `utSeedStages n` equal-gap narrowed stages from `Pool 2`, returning the common gap `g`
(`0 < g`, `6 ∣ g`, `g ≤ utSeedCap n`), the stage list `seedStages`, and the remaining stock `pool2_rem`. -/
theorem ut_seed_extraction
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    let pool2 := apInterval (utPool2Lo n) (utPool2Hi n) 2 1
    ∃ (g : ℕ) (seedStages : List BTSelectedStage) (pool2_rem : Finset ℕ),
      0 < g ∧ 6 ∣ g ∧ g ≤ utSeedCap n ∧
      seedStages.length = utSeedStages n ∧
      (∀ s ∈ seedStages, s.gap = g ∧ s.lows.card = utQ n ∧
        PairwiseDisjointPairs s.lows s.gap ∧ s.footprint ⊆ pool2) ∧
      seedStages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages (utMidWidth n) seedStages ∧
      StepGapChain BTSelectedStage.gap g 0 seedStages ∧
      (seedStages.map BTSelectedStage.gap).sum = utSeedStages n * g ∧
      pool2_rem ⊆ pool2 ∧
      (∀ s ∈ seedStages, Disjoint s.footprint pool2_rem) ∧
      pool2_rem.card + 2 * utSeedStages n * utQ n = pool2.card := by
  classical
  dsimp only
  let pool2 := apInterval (utPool2Lo n) (utPool2Hi n) 2 1
  obtain ⟨_, hpool2_card⟩ := ut_pool_card_lowers bmor imp sharp upper hn
  obtain ⟨hε, hR_cap, hwidth_pos, hBT5, hQ_lt_M⟩ := ut_seed_scalar_gates rs lower sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨_, _, hLn11, _, _, hY_gt, _, _, _, _⟩ := ut_sharp_scale_bounds rs lower sharp upper hn
  have hX_pos : 0 < utX n := by dsimp [utX]; linarith
  have hY_pos : 0 < utY n := by
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    linarith
  let M : ℝ := (509 / 2000 : ℝ) * utY n
  let r : ℕ := utSeedStages n + 4
  let Q : ℕ := utQ n
  have hQ_pos : 0 < Q := by dsimp [Q, utQ]; omega
  have hr_pos : 0 < r := by dsimp [r]; omega
  have hpool2_ne : pool2.Nonempty := by
    apply Finset.card_pos.mp
    have : (0 : ℝ) < (pool2.card : ℝ) := lt_of_lt_of_le (by positivity) hpool2_card
    exact_mod_cast this
  have hpool2_int : ∀ p ∈ pool2, utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool2Lo n + (255 / 1000 : ℝ) * utX n :=
    fun p hp => ⟨(ut_pool2_elem_props sharp upper hn hp).2.2.2.2.2.1,
      (ut_pool2_elem_props sharp upper hn hp).2.2.2.2.2.2.2.1⟩
  have hpool2_cls : ∀ p ∈ pool2, p % 6 ∈ utClassesSix 6 :=
    fun p hp => prime_gt_three_mod_mem_utClassesSix
      (ut_pool2_elem_props sharp upper hn hp).1
      (by have := (ut_pool2_elem_props sharp upper hn hp).2.2.2.1; omega)
      (by decide) (dvd_refl 6)
  have hcls6_card : ((utClassesSix 6).card : ℝ) ≤ 2 := by
    rw [utClassesSix_card_real (dvd_refl 6)]; norm_num
  have hR_pos : (0 : ℝ) < (utSeedCap n : ℝ) := by
    dsimp [utSeedCap]; exact_mod_cast (by omega : 0 < 6 * (utLn n + 5))
  let width_seed : ℝ := (6 : ℝ) * ((105 / 100 : ℝ) * M * (utSeedCap n : ℝ) / (2 * utX n) - 1 / 2)
  obtain ⟨g, candidates, hg_pos, hg6, hg_fl, _, hcand_card, hcand_match, hcand_foot, _, _⟩ :=
    ap_interval_stage_from_source_budget pool2 (utClassesSix 6)
      (utPool2Lo n) (255 / 1000 : ℝ) (utX n) 2 (utSeedCap n : ℝ) 1000 (105 / 100 : ℝ) M width_seed
      6 (r * Q) hpool2_ne hpool2_int hpool2_cls (by dsimp [M]; positivity) hpool2_card
      (by norm_num) hX_pos (by norm_num) hR_pos (by norm_num) (by decide) hcls6_card
      (by norm_num) hε hR_cap hwidth_pos rfl hBT5
  have hg_le : g ≤ utSeedCap n := by rwa [Nat.floor_natCast] at hg_fl
  let w := sortedSeedReal candidates r Q hcand_card
  have hw_bound : ∀ i < r * Q, utPool2Lo n ≤ w i ∧ w i ≤ utPool2Hi n := by
    intro i hi
    have hmem : candidates.orderEmbOfFin hcand_card ⟨i, hi⟩ ∈ pool2 :=
      hcand_foot (Finset.mem_union_left _ (candidates.orderEmbOfFin_mem hcand_card ⟨i, hi⟩))
    have hp := ut_pool2_elem_props sharp upper hn hmem
    simpa [w, sortedSeedReal, hi] using ⟨hp.2.2.2.2.2.1, hp.2.2.2.2.2.2.1⟩
  have hLU : utPool2Lo n ≤ utPool2Hi n := by dsimp [utPool2Lo, utPool2Hi]; linarith
  obtain ⟨hw_nn, hw_sum⟩ := sorted_seed_group_widths w r Q (utPool2Lo n) (utPool2Hi n)
    hQ_pos hLU (sortedSeedReal_mono candidates r Q hcand_card) hw_bound
  let groupWidth : Fin r → ℝ := fun j => w (j.val * Q + (Q - 1)) - w (j.val * Q)
  have hgw_nn : ∀ j : Fin r, 0 ≤ groupWidth j := fun j => hw_nn j.val j.isLt
  have hgw_sum : ∑ j : Fin r, groupWidth j < 5 * utMidWidth n := by
    have hsum_eq : (∑ j : Fin r, groupWidth j) =
        ∑ j ∈ Finset.range r, (w (j * Q + (Q - 1)) - w (j * Q)) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      simp [groupWidth, hj]
    have hdiff : utPool2Hi n - utPool2Lo n < 5 * utMidWidth n := by
      dsimp [utPool2Lo, utPool2Hi, utMidWidth]; linarith
    linarith
  let bad : Finset (Fin r) := Finset.univ.filter (fun j => utMidWidth n ≤ groupWidth j)
  have hbad_le_four : bad.card ≤ 4 := by
    by_contra hgt4
    have h5R : (5 : ℝ) ≤ (bad.card : ℝ) := by exact_mod_cast (show 5 ≤ bad.card by omega)
    have hmid_pos : 0 < utMidWidth n := by dsimp [utMidWidth]; positivity
    have hlow : (bad.card : ℝ) * utMidWidth n ≤ ∑ j ∈ bad, groupWidth j := by
      calc
        (bad.card : ℝ) * utMidWidth n = ∑ _j ∈ bad, utMidWidth n := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ j ∈ bad, groupWidth j :=
          Finset.sum_le_sum fun j hj => (Finset.mem_filter.mp hj).2
    have hhigh : ∑ j ∈ bad, groupWidth j ≤ ∑ j : Fin r, groupWidth j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => hgw_nn j
    nlinarith
  let good : Finset (Fin r) := Finset.univ.filter (fun j => groupWidth j < utMidWidth n)
  have hgood_ge : utSeedStages n ≤ good.card := by
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin r))) (fun j : Fin r => groupWidth j < utMidWidth n)
    have hnot_eq : Finset.univ.filter (fun j : Fin r => ¬ groupWidth j < utMidWidth n) = bad := by
      ext j; simp [bad, not_lt]
    rw [hnot_eq, Finset.card_univ, Fintype.card_fin] at hpart
    change good.card + bad.card = utSeedStages n + 4 at hpart
    omega
  obtain ⟨kept, hkept_sub, hkept_card⟩ := Finset.exists_subset_card_eq hgood_ge
  obtain ⟨hgrp_sub, hgrp_card, hgrp_match, hgrp_foot_card, hgrp_disj⟩ :=
    seedGroupLows_props candidates r Q g hQ_pos hg_pos hcand_card hcand_match
  let mkStage : Fin r → BTSelectedStage := fun j =>
    { gap := g, lows := seedGroupLows candidates r Q hcand_card j, minimum := 0 }
  let keptList : List (Fin r) := kept.toList
  have hkept_len : keptList.length = utSeedStages n := by
    rw [Finset.length_toList, hkept_card]
  have hkept_nodup : keptList.Nodup := Finset.nodup_toList kept
  let seedStages : List BTSelectedStage := keptList.map mkStage
  have hseed_len : seedStages.length = utSeedStages n := by simp [seedStages, hkept_len]
  have hseed_props : ∀ s ∈ seedStages, s.gap = g ∧ s.lows.card = utQ n ∧
      PairwiseDisjointPairs s.lows s.gap ∧ s.footprint ⊆ pool2 := by
    intro s hs
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hs
    refine ⟨rfl, hgrp_card j, hgrp_match j, ?_⟩
    exact (pairFootprint_subset_mono (hgrp_sub j) g).trans hcand_foot
  have hseed_disj : seedStages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
    dsimp [seedStages]
    rw [List.pairwise_map]
    exact hkept_nodup.imp (fun {j₁ j₂} hne => hgrp_disj j₁ j₂ hne)
  have hseed_narrow : NarrowedStages (utMidWidth n) seedStages := by
    intro s hs p hp q hq
    obtain ⟨j, hj_list, rfl⟩ := List.mem_map.mp hs
    have hj_kept : j ∈ kept := Finset.mem_toList.mp hj_list
    have hj_good : groupWidth j < utMidWidth n := (Finset.mem_filter.mp (hkept_sub hj_kept)).2
    obtain ⟨i₁, _, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨i₂, _, rfl⟩ := Finset.mem_image.mp hq
    have hs1 := sortedSeedReal_slot candidates r Q hcand_card j i₁
    have hs2 := sortedSeedReal_slot candidates r Q hcand_card j i₂
    have hm := sortedSeedReal_mono candidates r Q hcand_card
    have htop : j.val * Q + (Q - 1) < r * Q := by
      have hmul := Nat.mul_le_mul_right Q (show j.val + 1 ≤ r by omega)
      simp only [Nat.add_mul, one_mul] at hmul; omega
    have h1_lo : w (j.val * Q) ≤ w (j.val * Q + i₁.val) := hm _ _ (by omega) (by omega)
    have h1_hi : w (j.val * Q + i₁.val) ≤ w (j.val * Q + (Q - 1)) := hm _ _ (by omega) htop
    have h2_lo : w (j.val * Q) ≤ w (j.val * Q + i₂.val) := hm _ _ (by omega) (by omega)
    have h2_hi : w (j.val * Q + i₂.val) ≤ w (j.val * Q + (Q - 1)) := hm _ _ (by omega) htop
    dsimp only [mkStage]
    push_cast
    have hmid_eq : ((((sortedSeedLower candidates r Q hcand_card (j, i₁) : ℝ) +
        ((sortedSeedLower candidates r Q hcand_card (j, i₁) : ℝ) + (g : ℝ))) / 2) -
        (((sortedSeedLower candidates r Q hcand_card (j, i₂) : ℝ) +
        ((sortedSeedLower candidates r Q hcand_card (j, i₂) : ℝ) + (g : ℝ))) / 2)) =
        w (j.val * Q + i₁.val) - w (j.val * Q + i₂.val) := by
      rw [← hs1, ← hs2]; dsimp [w]; ring
    rw [hmid_eq, abs_lt]
    dsimp [groupWidth] at hj_good
    exact ⟨by linarith, by linarith⟩
  have hseed_chain : StepGapChain BTSelectedStage.gap g 0 seedStages := by
    have haux : ∀ (L : List (Fin r)) (R₀ : ℕ),
        StepGapChain BTSelectedStage.gap g R₀ (L.map mkStage) := by
      intro L
      induction L with
      | nil =>
        intro R₀; exact StepGapChain.nil R₀
      | cons j js ih =>
        intro R₀
        exact StepGapChain.cons R₀ (mkStage j) (js.map mkStage) (dvd_refl g) (by dsimp [mkStage]; omega)
          (ih (R₀ + g))
    exact haux keptList 0
  have hseed_sum : (seedStages.map BTSelectedStage.gap).sum = utSeedStages n * g := by
    have hmap : seedStages.map BTSelectedStage.gap = List.replicate keptList.length g := by
      dsimp [seedStages]
      rw [List.map_map]
      induction keptList with
      | nil => rfl
      | cons _ js ih => simp [mkStage, ih, List.replicate_succ]
    rw [hmap, List.sum_replicate, smul_eq_mul, hkept_len]
  let seedUsed : Finset ℕ := kept.biUnion (fun j => (mkStage j).footprint)
  have hseedUsed_sub : seedUsed ⊆ pool2 := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    exact (pairFootprint_subset_mono (hgrp_sub j) g).trans hcand_foot hxj
  have hseedUsed_card : seedUsed.card = 2 * utSeedStages n * utQ n := by
    dsimp [seedUsed]
    rw [Finset.card_biUnion]
    · have hconst : ∀ j ∈ kept, ((mkStage j).footprint).card = 2 * Q :=
        fun j _ => hgrp_foot_card j
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul, hkept_card]
      dsimp [Q]; ring
    · intro j₁ _ j₂ _ hne
      exact hgrp_disj j₁ j₂ hne
  let pool2_rem : Finset ℕ := pool2 \ seedUsed
  have hrem_disj : ∀ s ∈ seedStages, Disjoint s.footprint pool2_rem := by
    intro s hs
    obtain ⟨j, hj_list, rfl⟩ := List.mem_map.mp hs
    have hj_kept : j ∈ kept := Finset.mem_toList.mp hj_list
    rw [Finset.disjoint_left]
    intro x hxs hxrem
    exact (Finset.mem_sdiff.mp hxrem).2 (Finset.mem_biUnion.mpr ⟨j, hj_kept, hxs⟩)
  have hrem_card : pool2_rem.card + 2 * utSeedStages n * utQ n = pool2.card := by
    rw [← hseedUsed_card]
    exact Finset.card_sdiff_add_card_eq_card hseedUsed_sub
  exact ⟨g, seedStages, pool2_rem, hg_pos, hg6, hg_le, hseed_len, hseed_props,
    hseed_disj, hseed_narrow, hseed_chain, hseed_sum, Finset.sdiff_subset, hrem_disj, hrem_card⟩

where
  pairFootprint_subset_mono {A B : Finset ℕ} (hAB : A ⊆ B) (gap : ℕ) :
      pairFootprint A gap ⊆ pairFootprint B gap := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxL | hxR
    · exact Finset.mem_union_left _ (hAB hxL)
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxR
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨y, hAB hy, rfl⟩)

/-! ## Section 5: `Pool 1` Two-Sub-Phase Crossing (`AP_1` -> `AP_2`) -/

theorem ut_pool1_crossing
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg6 : 6 ∣ g) (hg_le : g ≤ utSeedCap n) :
    let pool1 := apInterval (utPool1Lo n) (utPool1Hi n) 2 1
    let R0 := utSeedStages n * g
    ∃ (apStages : List BTSelectedStage) (R_ap2 : ℕ),
      apStages.length ≤ utStepsAP n ∧
      (∀ s ∈ apStages, 0 < s.gap ∧ g ∣ s.gap ∧ s.lows.card = utQ n ∧
        PairwiseDisjointPairs s.lows s.gap ∧ s.footprint ⊆ pool1) ∧
      apStages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      NarrowedStages (utMidWidth n) apStages ∧
      StepGapChain BTSelectedStage.gap g R0 apStages ∧
      R_ap2 = R0 + (apStages.map BTSelectedStage.gap).sum ∧
      (12000 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤ (R_ap2 : ℝ) := by
  dsimp only
  let pool1 := apInterval (utPool1Lo n) (utPool1Hi n) 2 1
  obtain ⟨hpool1_card, _⟩ := ut_pool_card_lowers bmor imp sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨_, _, hLn11, _, _, hY_gt, _, _, _, _⟩ := ut_sharp_scale_bounds rs lower sharp upper hn
  have hX_pos : 0 < utX n := by dsimp [utX]; linarith
  have hY_pos : 0 < utY n := by
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    linarith
  have hg_posR : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr hg_pos
  have hLn_posR : (0 : ℝ) < (utLn n : ℝ) := by
    have : (11 : ℝ) ≤ (utLn n : ℝ) := by exact_mod_cast hLn11
    linarith
  have hmid_pos : 0 < utMidWidth n := by dsimp [utMidWidth]; positivity
  have hpool1_mid : ∀ p ∈ pool1, utPool1Lo n ≤ (p : ℝ) ∧ (p : ℝ) < utPool1Lo n + (2 : ℕ) * utMidWidth n := by
    intro p hp
    have h := ut_pool1_elem_props sharp upper hn hp
    exact ⟨h.2.2.2.2.1, by simpa using h.2.2.2.2.2.2⟩
  have hpool1_int : ∀ p ∈ pool1, utPool1Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool1Lo n + (255 / 1000 : ℝ) * utX n :=
    fun p hp => ⟨(ut_pool1_elem_props sharp upper hn hp).2.2.2.2.1,
      (ut_pool1_elem_props sharp upper hn hp).2.2.2.2.2.1⟩
  have hpool1_cls : ∀ p ∈ pool1, p % g ∈ utClassesSix g :=
    fun p hp => prime_gt_three_mod_mem_utClassesSix
      (ut_pool1_elem_props sharp upper hn hp).1
      (by have := (ut_pool1_elem_props sharp upper hn hp).2.2.2.1; omega)
      hg_pos hg6
  have hcls_card : ((utClassesSix g).card : ℝ) ≤ (g : ℝ) / 3 :=
    (utClassesSix_card_real hg6).le
  -- Sub-phase AP_1
  obtain ⟨hε1, hstk1, hflr1, hpair1, hsh1, hcap1, hbud1⟩ :=
    ut_ap1_scalar_gates rs lower sharp upper hn hg_pos hg6 hg_le
  have hstock1 : 2 * utQ n * utStepsAP1 n < pool1.card := by
    have hceil : ⌈(509 / 2000 : ℝ) * utY n⌉₊ ≤ pool1.card := Nat.ceil_le.mpr hpool1_card
    omega
  have hR0_pos : 0 < utSeedStages n * g := by
    dsimp [utSeedStages]; exact Nat.mul_pos (by omega) hg_pos
  obtain ⟨final1, R_ap1, stages1, htr1, hlen1, hsub1, hcard1, hdisj1, hnar1, htarg1⟩ :=
    ap_narrow_linear_phase_from_scalar pool1 (utClassesSix g)
      (utPool1Lo n) (255 / 1000 : ℝ) (utX n) ((g : ℝ) / 3) 200 (180 / 100 : ℝ)
      ((509 / 2000 : ℝ) * utY n) ((222 / 1000 : ℝ) * utY n)
      ((15 : ℝ) * (utLn n : ℝ) * (g : ℝ))
      (utSeedStages n * g) g (utQ n) (utStepsAP1 n) 2 (utPool1Lo n) (utMidWidth n)
      (by decide) hmid_pos hpool1_mid hpool1_int hpool1_cls
      (by norm_num) hX_pos (by positivity) (by norm_num) hg_pos
      (by norm_num) (by positivity) (by positivity) hpool1_card (by positivity)
      hε1 hR0_pos hcls_card hstock1 hflr1 hpair1 hsh1 hcap1 hbud1
  have hR1_ge : (15 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤ (R_ap1 : ℝ) := by
    have hnn : 0 ≤ ((g : ℝ) / 3) * utX n / (2 * (180 / 100 : ℝ) * ((222 / 1000 : ℝ) * utY n)) := by
      positivity
    linarith
  -- Sub-phase AP_2 on `final1`
  obtain ⟨hMa2_le, hε2, hstk2, hflr2, hpair2, hsh2, hcap2, hbud2⟩ :=
    ut_ap2_scalar_gates rs lower sharp upper hn hg_pos hg6 hg_le hR1_ge
  have hfinal1_card : (222 / 1000 : ℝ) * utY n ≤ (final1.card : ℝ) := by
    have hcardR : (final1.card : ℝ) + 2 * (utQ n : ℝ) * (stages1.length : ℝ) = (pool1.card : ℝ) := by
      exact_mod_cast hcard1
    have hlenR : (stages1.length : ℝ) ≤ (utStepsAP1 n : ℝ) := by exact_mod_cast hlen1
    have hmul_le : 2 * (utQ n : ℝ) * (stages1.length : ℝ) ≤ 2 * (utQ n : ℝ) * (utStepsAP1 n : ℝ) :=
      mul_le_mul_of_nonneg_left hlenR (by positivity)
    linarith
  have hstock2 : 2 * utQ n * utStepsAP2 n < final1.card := by
    have hceil : ⌈(222 / 1000 : ℝ) * utY n⌉₊ ≤ final1.card := Nat.ceil_le.mpr hfinal1_card
    omega
  have hR1_pos : 0 < R_ap1 := by
    have : (0 : ℝ) < (R_ap1 : ℝ) := lt_of_lt_of_le (by positivity) hR1_ge
    exact_mod_cast this
  obtain ⟨_final2, R_ap2, stages2, htr2, hlen2, _hsub2, _hcard2, hdisj2, hnar2, htarg2⟩ :=
    ap_narrow_linear_phase_from_scalar final1 (utClassesSix g)
      (utPool1Lo n) (255 / 1000 : ℝ) (utX n) ((g : ℝ) / 3) 200 (158 / 100 : ℝ)
      ((222 / 1000 : ℝ) * utY n) ((139 / 1000 : ℝ) * utY n)
      ((12000 : ℝ) * (utLn n : ℝ) * (g : ℝ))
      R_ap1 g (utQ n) (utStepsAP2 n) 2 (utPool1Lo n) (utMidWidth n)
      (by decide) hmid_pos
      (fun p hp => hpool1_mid p (hsub1 hp))
      (fun p hp => hpool1_int p (hsub1 hp))
      (fun p hp => hpool1_cls p (hsub1 hp))
      (by norm_num) hX_pos (by positivity) (by norm_num) hg_pos
      (by norm_num) (by positivity) (by positivity) hfinal1_card (by positivity)
      hε2 hR1_pos hcls_card hstock2 hflr2 hpair2 hsh2 hcap2 hbud2
  have hR2_ge : (12000 : ℝ) * (utLn n : ℝ) * (g : ℝ) ≤ (R_ap2 : ℝ) := by
    have hnn : 0 ≤ ((g : ℝ) / 3) * utX n / (2 * (158 / 100 : ℝ) * ((139 / 1000 : ℝ) * utY n)) := by
      positivity
    linarith
  refine ⟨stages1 ++ stages2, R_ap2, ?_, ?_, ?_, ?_, ?_, ?_, hR2_ge⟩
  · rw [List.length_append]
    dsimp [utStepsAP]
    omega
  · intro s hs
    rcases List.mem_append.mp hs with hs1 | hs2
    · obtain ⟨hg_s, hd_s, _, hc_s, hm_s⟩ := htr1.stage_properties s hs1
      exact ⟨hg_s, hd_s, hc_s, hm_s, htr1.footprints_subset s hs1⟩
    · obtain ⟨hg_s, hd_s, _, hc_s, hm_s⟩ := htr2.stage_properties s hs2
      exact ⟨hg_s, hd_s, hc_s, hm_s, (htr2.footprints_subset s hs2).trans hsub1⟩
  · rw [List.pairwise_append]
    refine ⟨hdisj1, hdisj2, ?_⟩
    intro s1 hs1 s2 hs2
    -- Wait: why is `s1 ∈ stages1` disjoint from `final1`? Let's prove `BTGrowingTrace` stages are disjoint from `final1`!
    exact btGrowingTrace_disjoint_final htr1 s1 hs1 |>.mono_right (htr2.footprints_subset s2 hs2)
  · intro s hs
    rcases List.mem_append.mp hs with hs1 | hs2
    · exact hnar1 s hs1
    · exact hnar2 s hs2
  · have hc1 := htr1.step_gap_chain
    have hc2 := htr2.step_gap_chain
    rw [htr1.final_accounting.2.2] at hc2
    exact stepGapChain_append BTSelectedStage.gap g stages1 stages2 (utSeedStages n * g) hc1 hc2
  · rw [List.map_append, List.sum_append, ← add_assoc, ← htr1.final_accounting.2.2]
    exact htr2.final_accounting.2.2

where
  btGrowingTrace_disjoint_final {g₀ Q₀ : ℕ} {u f : Finset ℕ} {r₀ rl : ℕ} {st : List BTSelectedStage}
      (htr : BTGrowingTrace g₀ Q₀ u r₀ f rl st) :
      ∀ s ∈ st, Disjoint s.footprint f := by
    induction htr with
    | nil => simp
    | cons unused radius stage final last tail _ _ _ _ _ _ _ hrest ih =>
      intro s hs
      rcases List.mem_cons.mp hs with rfl | hs_tail
      · have hf_sub := hrest.final_accounting.1
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp (hf_sub hx2)).2 hx1
      · exact ih s hs_tail

/-! ## Section 6: `Pool 2` Montgomery–Vaughan Crossing (`MV`) + `StepBoost` -/

private theorem btGrowingTrace_disjoint_final_pub {g₀ Q₀ : ℕ} {u f : Finset ℕ} {r₀ rl : ℕ}
    {st : List BTSelectedStage} (htr : BTGrowingTrace g₀ Q₀ u r₀ f rl st) :
    ∀ s ∈ st, Disjoint s.footprint f := by
  induction htr with
  | nil => simp
  | cons _ _ stage _ _ _ _ _ _ _ _ _ _ hrest ih =>
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs_tail
    · have hf_sub := hrest.final_accounting.1
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp (hf_sub hx2)).2 hx1
    · exact ih s hs_tail

/-- Execute `k` iterations of `ap_narrow_interval_stage` on remaining `Pool 2` once radius reaches `(76 / 1000) * utX n`. -/
theorem ut_boost_loop
    (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n g : ℕ} (hn : 35735 ≤ n) (hg_pos : 0 < g) (hg6 : 6 ∣ g) (hg_le : g ≤ utSeedCap n)
    (hε : (0 : ℝ) ≤ 1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ))
    (hBT5 : 2 * ((2 * utQ n : ℕ) : ℝ) * (Nat.totient g : ℝ) * utX n ≤
      (1 / (2 * ((255 / 1000 : ℝ) + 1 / (1000 / 76 : ℝ))) - (93 / 100 : ℝ)) *
        ((104 / 1000 : ℝ) * utY n) ^ 2 * (g : ℝ))
    (hwidth : (22 / 1000 : ℝ) * utY n ≤
      (g : ℝ) * ((93 / 100 : ℝ) * ((104 / 1000 : ℝ) * utY n) * ((76 / 1000 : ℝ) * utX n) /
        ((Nat.totient g : ℝ) * utX n) - 1 / 2))
    (hY_pos : 0 < utY n) :
    ∀ (k : ℕ) (S : Finset ℕ) (R : ℕ),
      S ⊆ apInterval (utPool2Lo n) (utPool2Hi n) 2 1 →
      (104 / 1000 : ℝ) * utY n + 2 * (utQ n : ℝ) * (k : ℝ) ≤ (S.card : ℝ) →
      (76 / 1000 : ℝ) * utX n ≤ (R : ℝ) →
      ∃ (boostStages : List BTSelectedStage),
        boostStages.length = k ∧
        (∀ s ∈ boostStages, 0 < s.gap ∧ g ∣ s.gap ∧ s.lows.card = utQ n ∧
          PairwiseDisjointPairs s.lows s.gap ∧ s.footprint ⊆ S) ∧
        boostStages.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
        NarrowedStages (utMidWidth n) boostStages ∧
        StepGapChain BTSelectedStage.gap g R boostStages ∧
        (k : ℝ) * ((22 / 1000 : ℝ) * utY n) ≤ ((boostStages.map BTSelectedStage.gap).sum : ℝ) := by
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  have hX_pos : 0 < utX n := by dsimp [utX]; linarith
  have hg1 : 1 < g := by obtain ⟨m, rfl⟩ := hg6; omega
  have hphi_pos : (0 : ℝ) < (Nat.totient g : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hg_pos)
  have hcls_card : ((utClassesCoprime g).card : ℝ) ≤ (Nat.totient g : ℝ) := by
    rw [utClassesCoprime_card hg1]
  have hmid_pos : 0 < utMidWidth n := by dsimp [utMidWidth]; positivity
  let M : ℝ := (104 / 1000 : ℝ) * utY n
  let R_cap : ℝ := (76 / 1000 : ℝ) * utX n
  let L_cap : ℝ := 1000 / 76
  let gapW : ℝ := (g : ℝ) * ((93 / 100 : ℝ) * M * R_cap / ((Nat.totient g : ℝ) * utX n) - 1 / 2)
  have hgapW_pos : 0 < gapW := lt_of_lt_of_le (by positivity) hwidth
  have hR_cap_le : R_cap ≤ utX n / L_cap := by dsimp [R_cap, L_cap]; linarith
  intro k
  induction k with
  | zero =>
    intro S R _ _ _
    refine ⟨[], rfl, by simp, List.Pairwise.nil, by simp [NarrowedStages], StepGapChain.nil R, by simp⟩
  | succ k ih =>
    intro S R hS_sub hS_card hR_lo
    have hM_le_S : M ≤ (S.card : ℝ) := by
      have : (0 : ℝ) ≤ 2 * (utQ n : ℝ) * ((k + 1 : ℕ) : ℝ) := by positivity
      dsimp [M]; linarith
    have hS_ne : S.Nonempty := by
      apply Finset.card_pos.mp
      have : (0 : ℝ) < (S.card : ℝ) := lt_of_lt_of_le (by dsimp [M]; positivity) hM_le_S
      exact_mod_cast this
    have hS_int : ∀ p ∈ S, utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool2Lo n + (255 / 1000 : ℝ) * utX n :=
      fun p hp => ⟨(ut_pool2_elem_props sharp upper hn (hS_sub hp)).2.2.2.2.2.1,
        (ut_pool2_elem_props sharp upper hn (hS_sub hp)).2.2.2.2.2.2.2.1⟩
    have hS_cls : ∀ p ∈ S, p % g ∈ utClassesCoprime g := by
      intro p hp
      have hp_props := ut_pool2_elem_props sharp upper hn (hS_sub hp)
      exact prime_gt_gap_mod_mem_utClassesCoprime hp_props.1 hg1 (lt_of_le_of_lt hg_le hp_props.2.2.2.2.1)
    have hS_mid : ∀ p ∈ S, utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) < utPool2Lo n + (2 : ℕ) * utMidWidth n :=
      fun p hp => ⟨(ut_pool2_elem_props sharp upper hn (hS_sub hp)).2.2.2.2.2.1,
        by simpa using (ut_pool2_elem_props sharp upper hn (hS_sub hp)).2.2.2.2.2.2.2.2⟩
    obtain ⟨h, chosen, hh_pos, hg_h, hh_fl, hgap_h, hch_card, hch_match, hch_foot, _, hrem_eq, hch_nar⟩ :=
      ap_narrow_interval_stage S (utClassesCoprime g)
        (utPool2Lo n) (255 / 1000 : ℝ) (utX n) (Nat.totient g : ℝ) R_cap L_cap (93 / 100 : ℝ) M gapW
        (utPool2Lo n) (utMidWidth n) g 2 (utQ n) hS_ne hS_int hS_cls
        (by dsimp [M]; positivity) hM_le_S (by norm_num) hX_pos hphi_pos
        (by dsimp [R_cap]; positivity) (by dsimp [L_cap]; norm_num) hg_pos hcls_card
        (by norm_num) hε hR_cap_le hgapW_pos rfl hBT5 (by decide) hmid_pos hS_mid
    let st0 : BTSelectedStage := { gap := h, lows := chosen, minimum := gapW }
    let S' : Finset ℕ := S \ st0.footprint
    have hS'_card : (104 / 1000 : ℝ) * utY n + 2 * (utQ n : ℝ) * (k : ℝ) ≤ (S'.card : ℝ) := by
      have hcR : (S'.card : ℝ) + 2 * (utQ n : ℝ) = (S.card : ℝ) := by exact_mod_cast hrem_eq
      push_cast at hS_card
      linarith
    have hh_le_R : h ≤ R := by
      have hfl_R : ⌊R_cap⌋₊ ≤ R := Nat.floor_le_of_le hR_lo
      exact hh_fl.trans hfl_R
    have hR'_lo : (76 / 1000 : ℝ) * utX n ≤ ((R + h : ℕ) : ℝ) := by
      push_cast; linarith
    obtain ⟨rest, hrest_len, hrest_props, hrest_disj, hrest_nar, hrest_chain, hrest_sum⟩ :=
      ih S' (R + h) (Finset.sdiff_subset.trans hS_sub) hS'_card hR'_lo
    refine ⟨st0 :: rest, by simp [hrest_len], ?_, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs_tl
      · exact ⟨hh_pos, hg_h, hch_card, hch_match, hch_foot⟩
      · obtain ⟨p1, p2, p3, p4, p5⟩ := hrest_props s hs_tl
        exact ⟨p1, p2, p3, p4, p5.trans Finset.sdiff_subset⟩
    · apply List.Pairwise.cons
      · intro s hs_tl
        have hs_sub : s.footprint ⊆ S \ st0.footprint := (hrest_props s hs_tl).2.2.2.2
        rw [Finset.disjoint_left]
        intro x hx0 hxs
        exact (Finset.mem_sdiff.mp (hs_sub hxs)).2 hx0
      · exact hrest_disj
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs_tl
      · exact hch_nar
      · exact hrest_nar s hs_tl
    · exact StepGapChain.cons R st0 rest hg_h (by dsimp [st0]; omega) hrest_chain
    · simp only [List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
      have hh_ge : (22 / 1000 : ℝ) * utY n ≤ (st0.gap : ℝ) := hwidth.trans hgap_h
      linarith

/-! ## Section 7: Combined `UTGrowthWitness` & `CompleteStepGrid` Assembly -/

/-- Complete growth-phase output bundle for `n ≥ 35,735`. -/
structure UTGrowthWitness (n : ℕ) where
  g : ℕ
  h0 : ℕ
  stages : List BTSelectedStage
  R_last : ℕ
  hg_eq : g = 2 * h0
  hg6 : 6 ∣ g
  hh0_pos : 0 < h0
  hh0_le : h0 ≤ utH0Max n
  hlen_pos : 0 < stages.length
  hlen_le : stages.length ≤ utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n
  hstage_props : ∀ s ∈ stages,
    0 < s.gap ∧ g ∣ s.gap ∧ s.lows.card = utQ n ∧ PairwiseDisjointPairs s.lows s.gap ∧
    (s.footprint ⊆ apInterval (utPool1Lo n) (utPool1Hi n) 2 1 ∨
     s.footprint ⊆ apInterval (utPool2Lo n) (utPool2Hi n) 2 1)
  hdisjoint : stages.Pairwise (fun x y => Disjoint x.footprint y.footprint)
  hnarrow : NarrowedStages (utMidWidth n) stages
  hR_eq_sum : R_last = (stages.map BTSelectedStage.gap).sum
  hR_div : g ∣ R_last
  hgrid : CompleteStepGrid (Finset.univ : Finset (Fin stages.length))
    (fun i => (stages.get i).gap) (2 * h0) R_last
  hR_lower : ((h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) + (10 / 1000 : ℝ) * utX n ≤ (R_last : ℝ)
  isPool1 : BTSelectedStage → Bool
  hisPool1 : ∀ s ∈ stages,
    if isPool1 s then s.footprint ⊆ apInterval (utPool1Lo n) (utPool1Hi n) 2 1
    else s.footprint ⊆ apInterval (utPool2Lo n) (utPool2Hi n) 2 1
  hp1_sum : (stages.map (fun s => if isPool1 s then (1 : ℕ) else 0)).sum ≤ utStepsAP n
  hp2_sum : (stages.map (fun s => if isPool1 s then (0 : ℕ) else 1)).sum ≤
    utSeedStages n + utStepsMV n + utStepsBoost n

/-- Construct the complete `UTGrowthWitness n` for every `n ≥ 35,735` from the exempt published inputs. -/
theorem ut_growth_witness
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    Nonempty (UTGrowthWitness n) := by
  classical
  let pool1 := apInterval (utPool1Lo n) (utPool1Hi n) 2 1
  let pool2 := apInterval (utPool2Lo n) (utPool2Hi n) 2 1
  obtain ⟨_, hpool2_card⟩ := ut_pool_card_lowers bmor imp sharp upper hn
  obtain ⟨_, hX_283, _, _, _⟩ := poolMaximum_bounds_ge_35735 sharp upper hn
  obtain ⟨_, _, hLn11, _, _, hY_gt, _, _, _, _⟩ := ut_sharp_scale_bounds rs lower sharp upper hn
  have hX_pos : 0 < utX n := by dsimp [utX]; linarith
  have hY_pos : 0 < utY n := by
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
    linarith
  -- 1. Seed extraction on Pool 2
  obtain ⟨g, seedStages, pool2_rem, hg_pos, hg6, hg_le, hseed_len, hseed_props,
      hseed_disj, hseed_nar, hseed_chain, hseed_sum, hrem_sub, hrem_disj, hrem_card⟩ :=
    ut_seed_extraction bmor imp rs lower sharp upper hn
  let h0 : ℕ := g / 2
  have hg_eq : g = 2 * h0 := by obtain ⟨m, rfl⟩ := hg6; dsimp [h0]; omega
  have hh0_pos : 0 < h0 := by omega
  have hh0_le : h0 ≤ utH0Max n := by
    have : 2 * h0 ≤ 2 * utH0Max n := by dsimp [utH0Max]; dsimp [utSeedCap] at hg_le; omega
    omega
  -- 2. AP_1 -> AP_2 crossing on Pool 1
  obtain ⟨apStages, R_ap2, hap_len, hap_props, hap_disj, hap_nar, hap_chain, hR_ap2_eq, hR_ap2_ge⟩ :=
    ut_pool1_crossing bmor imp rs lower sharp upper hn hg_pos hg6 hg_le
  -- 3. MV crossing on `pool2_rem`
  obtain ⟨hMa_mv_le, hε_mv, hstk_mv, hflr_mv, hpair_mv, hsh_mv, hcap_mv, hpaid_mv, hbud_mv⟩ :=
    ut_mv_scalar_gates rs lower sharp upper hn hg_pos hg6 hg_le hR_ap2_ge
  have hrem_cardR : (242 / 1000 : ℝ) * utY n ≤ (pool2_rem.card : ℝ) := by
    have hc : (pool2_rem.card : ℝ) + 2 * (utSeedStages n : ℝ) * (utQ n : ℝ) = (pool2.card : ℝ) := by
      exact_mod_cast hrem_card
    linarith
  have hstock_mv : 2 * utQ n * utStepsMV n < pool2_rem.card := by
    have hceil : ⌈(242 / 1000 : ℝ) * utY n⌉₊ ≤ pool2_rem.card := Nat.ceil_le.mpr hrem_cardR
    omega
  have hg1 : 1 < g := by omega
  have hphi_pos : (0 : ℝ) < (Nat.totient g : ℝ) := Nat.cast_pos.mpr (Nat.totient_pos.mpr hg_pos)
  have hcls_cop_card : ((utClassesCoprime g).card : ℝ) ≤ (Nat.totient g : ℝ) := by
    rw [utClassesCoprime_card hg1]
  have hcls_cop_red : ∀ a ∈ utClassesCoprime g, 0 < a ∧ Nat.Coprime g a :=
    fun a ha => (Finset.mem_filter.mp ha).2
  have hmid_pos : 0 < utMidWidth n := by dsimp [utMidWidth]; positivity
  have hrem_primes : ∀ p ∈ pool2_rem, Nat.Prime p :=
    fun p hp => (ut_pool2_elem_props sharp upper hn (hrem_sub hp)).1
  have hrem_int : ∀ p ∈ pool2_rem, utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) ≤ utPool2Lo n + (255 / 1000 : ℝ) * utX n :=
    fun p hp => ⟨(ut_pool2_elem_props sharp upper hn (hrem_sub hp)).2.2.2.2.2.1,
      (ut_pool2_elem_props sharp upper hn (hrem_sub hp)).2.2.2.2.2.2.2.1⟩
  have hrem_mid : ∀ p ∈ pool2_rem, utPool2Lo n ≤ (p : ℝ) ∧ (p : ℝ) < utPool2Lo n + (2 : ℕ) * utMidWidth n :=
    fun p hp => ⟨(ut_pool2_elem_props sharp upper hn (hrem_sub hp)).2.2.2.2.2.1,
      by simpa using (ut_pool2_elem_props sharp upper hn (hrem_sub hp)).2.2.2.2.2.2.2.2⟩
  have hrem_cls : ∀ p ∈ pool2_rem, p % g ∈ utClassesCoprime g := by
    intro p hp
    have hp_props := ut_pool2_elem_props sharp upper hn (hrem_sub hp)
    exact prime_gt_gap_mod_mem_utClassesCoprime hp_props.1 hg1 (lt_of_le_of_lt hg_le hp_props.2.2.2.2.1)
  have hR_ap2_pos : 0 < R_ap2 := by
    have hLn_posR : (0 : ℝ) < (utLn n : ℝ) := Nat.cast_pos.mpr (by omega)
    have hg_posR : (0 : ℝ) < (g : ℝ) := Nat.cast_pos.mpr hg_pos
    have : (0 : ℝ) < (R_ap2 : ℝ) := lt_of_lt_of_le (by positivity) hR_ap2_ge
    exact_mod_cast this
  obtain ⟨final_mv, R_mv, mvStages, htr_mv, hmv_len, hmv_sub, hmv_card, hmv_disj, hmv_nar, htarg_mv⟩ :=
    mv_narrow_linear_phase_from_scalar mv pool2_rem (utClassesCoprime g)
      (utPool2Lo n) (255 / 1000 : ℝ) (utX n) (Nat.totient g : ℝ) 13 (118 / 100 : ℝ) 7
      ((242 / 1000 : ℝ) * utY n) ((135 / 1000 : ℝ) * utY n) ((76 / 1000 : ℝ) * utX n)
      R_ap2 g (utQ n) (utStepsMV n) 2 (utPool2Lo n) (utMidWidth n)
      (by decide) hmid_pos hrem_mid hrem_primes hrem_int hrem_cls hcls_cop_red
      (by norm_num) hX_pos hphi_pos (by norm_num) hg_pos (by norm_num) (by norm_num)
      (by positivity) (by positivity) hrem_cardR (by positivity)
      hε_mv hR_ap2_pos hcls_cop_card hstock_mv hflr_mv hpair_mv hsh_mv hcap_mv hpaid_mv hbud_mv
  have hR_mv_ge : (76 / 1000 : ℝ) * utX n ≤ (R_mv : ℝ) := by
    have hnn : 0 ≤ (Nat.totient g : ℝ) * utX n / (2 * (118 / 100 : ℝ) * ((135 / 1000 : ℝ) * utY n)) := by
      positivity
    linarith
  have hfinal_mv_card : (135 / 1000 : ℝ) * utY n ≤ (final_mv.card : ℝ) := by
    have hc : (final_mv.card : ℝ) + 2 * (utQ n : ℝ) * (mvStages.length : ℝ) = (pool2_rem.card : ℝ) := by
      exact_mod_cast hmv_card
    have hlenR : (mvStages.length : ℝ) ≤ (utStepsMV n : ℝ) := by exact_mod_cast hmv_len
    have hmul_le : 2 * (utQ n : ℝ) * (mvStages.length : ℝ) ≤ 2 * (utQ n : ℝ) * (utStepsMV n : ℝ) :=
      mul_le_mul_of_nonneg_left hlenR (by positivity)
    linarith
  -- 4. StepBoost iteration on `final_mv`
  obtain ⟨hbst_stk, hbst_ε, hbst_BT5, hbst_w, hbst_gain⟩ :=
    ut_boost_scalar_gates rs lower sharp upper hn hg_pos hg6 hg_le hh0_le
  have hbst_card : (104 / 1000 : ℝ) * utY n + 2 * (utQ n : ℝ) * (utStepsBoost n : ℝ) ≤ (final_mv.card : ℝ) := by
    have : 0 ≤ 2 * (utQ n : ℝ) * (utStepsBoost n : ℝ) := by positivity
    linarith
  obtain ⟨boostStages, hbst_len, hbst_props, hbst_disj, hbst_nar, hbst_chain, hbst_sum⟩ :=
    ut_boost_loop sharp upper hn hg_pos hg6 hg_le hbst_ε hbst_BT5 hbst_w hY_pos
      (utStepsBoost n) final_mv R_mv (hmv_sub.trans hrem_sub) hbst_card hR_mv_ge
  -- 5. Disjointness between `Pool 1` and `Pool 2`
  have hpools_disj : Disjoint pool1 pool2 := by
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    have h1 := (ut_pool1_elem_props sharp upper hn hp1).2.2.2.2.2.1
    have h2 := (ut_pool2_elem_props sharp upper hn hp2).2.2.2.2.2.1
    dsimp [utPool1Lo, utPool2Lo] at h1 h2
    linarith
  -- 6. Concatenate all 4 stage lists: `seedStages ++ apStages ++ mvStages ++ boostStages`
  let p2Stages : List BTSelectedStage := mvStages ++ boostStages
  have hp2_disj : p2Stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
    rw [List.pairwise_append]
    refine ⟨hmv_disj, hbst_disj, ?_⟩
    intro s1 hs1 s2 hs2
    exact (btGrowingTrace_disjoint_final_pub htr_mv s1 hs1).mono_right (hbst_props s2 hs2).2.2.2.2
  have hp2_sub_rem : ∀ s ∈ p2Stages, s.footprint ⊆ pool2_rem := by
    intro s hs
    rcases List.mem_append.mp hs with hs1 | hs2
    · exact htr_mv.footprints_subset s hs1
    · exact (hbst_props s hs2).2.2.2.2.trans hmv_sub
  let allP2Stages : List BTSelectedStage := seedStages ++ p2Stages
  have hallP2_disj : allP2Stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
    rw [List.pairwise_append]
    refine ⟨hseed_disj, hp2_disj, ?_⟩
    intro s1 hs1 s2 hs2
    exact (hrem_disj s1 hs1).mono_right (hp2_sub_rem s2 hs2)
  let stages : List BTSelectedStage := seedStages ++ apStages ++ mvStages ++ boostStages
  have hstages_len_pos : 0 < stages.length := by
    simp only [stages, List.length_append, hseed_len]
    dsimp [utSeedStages]; omega
  have hstages_len_le : stages.length ≤ utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n := by
    simp only [stages, List.length_append, hseed_len, hbst_len]
    omega
  have hstages_props : ∀ s ∈ stages,
      0 < s.gap ∧ g ∣ s.gap ∧ s.lows.card = utQ n ∧ PairwiseDisjointPairs s.lows s.gap ∧
      (s.footprint ⊆ pool1 ∨ s.footprint ⊆ pool2) := by
    intro s hs
    simp only [stages, List.mem_append] at hs
    rcases hs with ((hs_seed | hs_ap) | hs_mv) | hs_bst
    · obtain ⟨h1, h2, h3, h4⟩ := hseed_props s hs_seed
      exact ⟨by rw [h1]; exact hg_pos, by rw [h1], h2, h3, Or.inr h4⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hap_props s hs_ap
      exact ⟨h1, h2, h3, h4, Or.inl h5⟩
    · obtain ⟨h1, h2, _, h3, h4⟩ := htr_mv.stage_properties s hs_mv
      exact ⟨h1, h2, h3, h4, Or.inr ((htr_mv.footprints_subset s hs_mv).trans hrem_sub)⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hbst_props s hs_bst
      exact ⟨h1, h2, h3, h4, Or.inr (h5.trans (hmv_sub.trans hrem_sub))⟩
  have hstages_disj : stages.Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
    have h12 : (seedStages ++ apStages).Pairwise (fun x y => Disjoint x.footprint y.footprint) := by
      rw [List.pairwise_append]
      refine ⟨hseed_disj, hap_disj, ?_⟩
      intro s1 hs1 s2 hs2
      exact hpools_disj.symm.mono (hseed_props s1 hs1).2.2.2 (hap_props s2 hs2).2.2.2.2
    have h1234 : ((seedStages ++ apStages) ++ p2Stages).Pairwise
        (fun x y => Disjoint x.footprint y.footprint) := by
      rw [List.pairwise_append]
      refine ⟨h12, hp2_disj, ?_⟩
      intro s1 hs1 s2 hs2
      rcases List.mem_append.mp hs1 with hs_seed | hs_ap
      · exact (hrem_disj s1 hs_seed).mono_right (hp2_sub_rem s2 hs2)
      · exact hpools_disj.mono (hap_props s1 hs_ap).2.2.2.2 ((hp2_sub_rem s2 hs2).trans hrem_sub)
    simpa [stages, p2Stages, List.append_assoc] using h1234
  have hstages_nar : NarrowedStages (utMidWidth n) stages := by
    intro s hs
    simp only [stages, List.mem_append] at hs
    rcases hs with ((hs_seed | hs_ap) | hs_mv) | hs_bst
    · exact hseed_nar s hs_seed
    · exact hap_nar s hs_ap
    · exact hmv_nar s hs_mv
    · exact hbst_nar s hs_bst
  -- 7. Concatenate `StepGapChain` from `0` to `R_last := (stages.map gap).sum`
  have hchain12 : StepGapChain BTSelectedStage.gap g 0 (seedStages ++ apStages) := by
    apply stepGapChain_append BTSelectedStage.gap g seedStages apStages 0 hseed_chain
    simpa [hseed_sum] using hap_chain
  have hsum12 : ((seedStages ++ apStages).map BTSelectedStage.gap).sum = R_ap2 := by
    rw [List.map_append, List.sum_append, hseed_sum, hR_ap2_eq]
  have hchain123 : StepGapChain BTSelectedStage.gap g 0 ((seedStages ++ apStages) ++ mvStages) := by
    apply stepGapChain_append BTSelectedStage.gap g (seedStages ++ apStages) mvStages 0 hchain12
    rw [zero_add, hsum12]
    exact htr_mv.step_gap_chain
  have hsum123 : (((seedStages ++ apStages) ++ mvStages).map BTSelectedStage.gap).sum = R_mv := by
    rw [List.map_append, List.sum_append, hsum12, htr_mv.final_accounting.2.2]
  have hchain_all : StepGapChain BTSelectedStage.gap g 0 stages := by
    dsimp [stages]
    apply stepGapChain_append BTSelectedStage.gap g ((seedStages ++ apStages) ++ mvStages) boostStages 0 hchain123
    rw [zero_add, hsum123]
    exact hbst_chain
  let R_last : ℕ := (stages.map BTSelectedStage.gap).sum
  have hR_last_eq : R_last = R_mv + (boostStages.map BTSelectedStage.gap).sum := by
    dsimp [R_last, stages]
    rw [List.map_append, List.sum_append, hsum123]
  have hR_div : g ∣ R_last := by
    dsimp [R_last]
    have hall_dvd : ∀ x ∈ stages.map BTSelectedStage.gap, g ∣ x := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      exact (hstages_props s hs).2.1
    exact List.dvd_sum hall_dvd
  have hgrid : CompleteStepGrid (Finset.univ : Finset (Fin stages.length))
      (fun i => (stages.get i).gap) (2 * h0) R_last := by
    rw [← hg_eq]
    exact completeStepGrid_univ_of_stepGapChain BTSelectedStage.gap g stages hg_pos hchain_all
  have hR_lower : ((h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) + (10 / 1000 : ℝ) * utX n ≤ (R_last : ℝ) := by
    rw [hR_last_eq, Nat.cast_add]
    linarith [hbst_gain, hR_mv_ge, hbst_sum]
  let isPool1 : BTSelectedStage → Bool := fun s => decide (s.footprint ⊆ pool1)
  have hisPool1 : ∀ s ∈ stages,
      if isPool1 s then s.footprint ⊆ pool1 else s.footprint ⊆ pool2 := by
    intro s hs
    by_cases hsub : s.footprint ⊆ pool1
    · simp [isPool1, hsub]
    · simp only [isPool1, hsub, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact (hstages_props s hs).2.2.2.2.resolve_left hsub
  have hp2_not_p1 : ∀ s : BTSelectedStage, s.lows.card = utQ n → s.footprint ⊆ pool2 →
      isPool1 s = false := by
    intro s hcard hsub2
    have hpos : 0 < s.lows.card := by rw [hcard]; dsimp [utQ]; omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    have hxf : x ∈ s.footprint := Finset.mem_union_left _ hx
    have hnsub : ¬ s.footprint ⊆ pool1 := fun hsub1 =>
      Finset.disjoint_left.mp hpools_disj (hsub1 hxf) (hsub2 hxf)
    simp [isPool1, hnsub]
  have hsum_zero_of_all : ∀ (L : List BTSelectedStage) (f : BTSelectedStage → ℕ),
      (∀ s ∈ L, f s = 0) → (L.map f).sum = 0 := by
    intro L f hf
    induction L with
    | nil => rfl
    | cons a as ih =>
      simp [hf a (by simp), ih (fun s hs => hf s (by simp [hs]))]
  have hsum_le_len : ∀ (L : List BTSelectedStage) (f : BTSelectedStage → ℕ),
      (∀ s ∈ L, f s ≤ 1) → (L.map f).sum ≤ L.length := by
    intro L f hf
    induction L with
    | nil => simp
    | cons a as ih =>
      have ha := hf a (by simp)
      have has := ih (fun s hs => hf s (by simp [hs]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      omega
  have hp1_sum : (stages.map (fun s => if isPool1 s then (1 : ℕ) else 0)).sum ≤ utStepsAP n := by
    let f1 : BTSelectedStage → ℕ := fun s => if isPool1 s then 1 else 0
    have hz_seed : (seedStages.map f1).sum = 0 := hsum_zero_of_all _ _ fun s hs => by
      simp [f1, hp2_not_p1 s (hseed_props s hs).2.1 (hseed_props s hs).2.2.2]
    have hz_mv : (mvStages.map f1).sum = 0 := hsum_zero_of_all _ _ fun s hs => by
      simp [f1, hp2_not_p1 s (htr_mv.stage_properties s hs).2.2.2.1
        ((htr_mv.footprints_subset s hs).trans hrem_sub)]
    have hz_bst : (boostStages.map f1).sum = 0 := hsum_zero_of_all _ _ fun s hs => by
      simp [f1, hp2_not_p1 s (hbst_props s hs).2.2.1
        ((hbst_props s hs).2.2.2.2.trans (hmv_sub.trans hrem_sub))]
    have hap_le : (apStages.map f1).sum ≤ apStages.length :=
      hsum_le_len _ _ fun s _ => by dsimp [f1]; split_ifs <;> omega
    change (stages.map f1).sum ≤ utStepsAP n
    dsimp [stages]
    simp only [List.map_append, List.sum_append, hz_seed, hz_mv, hz_bst]
    omega
  have hp2_sum : (stages.map (fun s => if isPool1 s then (0 : ℕ) else 1)).sum ≤
      utSeedStages n + utStepsMV n + utStepsBoost n := by
    let f2 : BTSelectedStage → ℕ := fun s => if isPool1 s then 0 else 1
    have hz_ap : (apStages.map f2).sum = 0 := hsum_zero_of_all _ _ fun s hs => by
      have hsub : s.footprint ⊆ pool1 := (hap_props s hs).2.2.2.2
      simp [f2, isPool1, hsub]
    have hs_le : (seedStages.map f2).sum ≤ utSeedStages n := by
      rw [← hseed_len]
      exact hsum_le_len _ _ fun s _ => by dsimp [f2]; split_ifs <;> omega
    have hm_le : (mvStages.map f2).sum ≤ mvStages.length :=
      hsum_le_len _ _ fun s _ => by dsimp [f2]; split_ifs <;> omega
    have hb_le : (boostStages.map f2).sum ≤ utStepsBoost n := by
      rw [← hbst_len]
      exact hsum_le_len _ _ fun s _ => by dsimp [f2]; split_ifs <;> omega
    change (stages.map f2).sum ≤ utSeedStages n + utStepsMV n + utStepsBoost n
    dsimp [stages]
    simp only [List.map_append, List.sum_append, hz_ap]
    omega
  exact ⟨{
    g := g
    h0 := h0
    stages := stages
    R_last := R_last
    hg_eq := hg_eq
    hg6 := hg6
    hh0_pos := hh0_pos
    hh0_le := hh0_le
    hlen_pos := hstages_len_pos
    hlen_le := hstages_len_le
    hstage_props := hstages_props
    hdisjoint := hstages_disj
    hnarrow := hstages_nar
    hR_eq_sum := rfl
    hR_div := hR_div
    hgrid := hgrid
    hR_lower := hR_lower
    isPool1 := isPool1
    hisPool1 := hisPool1
    hp1_sum := hp1_sum
    hp2_sum := hp2_sum
  }⟩

end

end Sude
