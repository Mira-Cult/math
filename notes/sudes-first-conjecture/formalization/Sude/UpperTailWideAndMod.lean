import Sude.UpperTailGrowth
import Sude.EvenIntervalGrid
import Sude.MatchedBinPairs
import Sude.T75CompactBinning

/-!
# Role Splitting, Modular Coverage, Doubling, and Wide Extension for `n ≥ 35,735`

Takes `UTGrowthWitness n` (`n ≥ 35,735`) and constructs the complete `UTRoleWitness n` bundle:
1. Splits every narrowed Growth stage (`6 * n + 4` disjoint prime pairs) into `6 * n` ordinary
   edge pairs (`UTEdge n`) and `2` sign-balanced diagonal `UTRectData` tuples.
2. Extracts `h0 - 1` ordinary `ModCover` stages across `ModBin 0..53` (covering all `h0` half-gap
   residues modulo `h0` on every edge `u : UTEdge n` simultaneously) and `2 * (h0 - 1)` diagonal
   `ModCover` `UTRectData` tuples from `ModBin 54` (covering all `h0` half-gap residues on both
   diagonals).
3. Extracts `10` `Doubling` stages (`utDblLow` / `utDblHigh`) and `utWOrd n` ordinary + `utWDiag n`
   sign-balanced diagonal `Wide` stages (`utWideLow` / `utWideHigh`).
4. Establishes global `pool n` membership and injectivity across all rectangles and ordinary pairs,
   Keepout `(0.355 * X, 0.578 * X]` avoidance, linear value-excess bounds for `[0.359 * X, 0.574 * X]`
   central-mean enclosure, and `EvenIntervalGrid` + sum/midpoint bounds on all `6 * n` ordinary
   edges and both diagonals.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

/-! ## Section 1: Edge Indexing, `UTRectData`, and Combinatorial Helpers -/

/-- The `6 * n` directed edges across both 3-layer permutation networks (`false` = row network,
`true` = column network). -/
abbrev UTEdge (n : ℕ) := Bool × (Fin 3 × Fin n)

/-- Canonical equivalence `UTEdge n ≃ Fin (6 * n)`. -/
def utEdgeEquiv (n : ℕ) : UTEdge n ≃ Fin (6 * n) :=
  Fintype.equivFinOfCardEq (by
    simp only [UTEdge, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin]
    ring)

/-- Equal-gap 4-tuple `(u1, v1, v2, u2)` of distinct natural numbers with `v1 = u1 + gap` and
`v2 = u2 + gap` (`0 < gap`, `2 ∣ gap`), matching `packedRectangleCorner` orientation `(0, 1, 2, 3)`. -/
structure UTRectData where
  u1 : ℕ
  v1 : ℕ
  v2 : ℕ
  u2 : ℕ
  gap : ℕ
  hgap_pos : 0 < gap
  hgap_even : 2 ∣ gap
  hv1 : v1 = u1 + gap
  hv2 : v2 = u2 + gap
  hinj : Function.Injective ![u1, v1, v2, u2]

def UTRectData.corners (r : UTRectData) : Fin 4 → ℕ :=
  ![r.u1, r.v1, r.v2, r.u2]

def UTRectData.support (r : UTRectData) : Finset ℕ :=
  {r.u1, r.v1, r.v2, r.u2}

theorem UTRectData.corners_mem_support (r : UTRectData) (c : Fin 4) :
    r.corners c ∈ r.support := by
  fin_cases c <;> simp [UTRectData.corners, UTRectData.support]

theorem UTRectData.mem_support_iff (r : UTRectData) (x : ℕ) :
    x ∈ r.support ↔ ∃ c : Fin 4, r.corners c = x := by
  constructor
  · intro hx
    simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · rintro ⟨c, rfl⟩
    exact r.corners_mem_support c

/-- Greedy sign balancing for `K` paired real values `(a k, b k)` with `|a k - b k| ≤ C`:
chooses `swap : Fin K → Bool` keeping the total difference bounded by `C`. -/
theorem greedy_sign_balance {K : ℕ} {C : ℝ} (hC : 0 ≤ C) (a b : Fin K → ℝ)
    (hdiff : ∀ k : Fin K, |a k - b k| ≤ C) :
    ∃ swap : Fin K → Bool,
      |(∑ k : Fin K, if swap k then b k else a k) -
        (∑ k : Fin K, if swap k then a k else b k)| ≤ C := by
  induction K with
  | zero =>
    refine ⟨fun k => k.elim0, ?_⟩
    simpa using hC
  | succ K ih =>
    obtain ⟨swap₀, hS⟩ := ih (fun k => a k.castSucc) (fun k => b k.castSucc)
      (fun k => hdiff k.castSucc)
    let S : ℝ :=
      (∑ k : Fin K, if swap₀ k then b k.castSucc else a k.castSucc) -
      (∑ k : Fin K, if swap₀ k then a k.castSucc else b k.castSucc)
    have hS_abs : |S| ≤ C := hS
    let d : ℝ := a (Fin.last K) - b (Fin.last K)
    have hd_abs : |d| ≤ C := hdiff (Fin.last K)
    have hS_bounds := abs_le.mp hS_abs
    have hd_bounds := abs_le.mp hd_abs
    by_cases hsame : (0 ≤ S ∧ 0 ≤ d) ∨ (S ≤ 0 ∧ d ≤ 0)
    · let swap : Fin (K + 1) → Bool := Fin.snoc swap₀ true
      refine ⟨swap, ?_⟩
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [swap, Fin.snoc_castSucc, Fin.snoc_last, ↓reduceIte]
      have hrew :
          ((∑ i : Fin K, if swap₀ i = true then b i.castSucc else a i.castSucc) + b (Fin.last K)) -
          ((∑ i : Fin K, if swap₀ i = true then a i.castSucc else b i.castSucc) + a (Fin.last K)) =
          S - d := by
        dsimp [S, d]; ring
      rw [hrew, abs_le]
      rcases hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> constructor <;> linarith
    · let swap : Fin (K + 1) → Bool := Fin.snoc swap₀ false
      refine ⟨swap, ?_⟩
      rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
      simp only [swap, Fin.snoc_castSucc, Fin.snoc_last, Bool.false_eq_true, ↓reduceIte]
      have hrew :
          ((∑ i : Fin K, if swap₀ i = true then b i.castSucc else a i.castSucc) + a (Fin.last K)) -
          ((∑ i : Fin K, if swap₀ i = true then a i.castSucc else b i.castSucc) + b (Fin.last K)) =
          S + d := by
        dsimp [S, d]; ring
      rw [hrew, abs_le]
      rcases le_total 0 S with hS0 | hS0 <;> rcases le_total 0 d with hd0 | hd0
      · exact False.elim (hsame (Or.inl ⟨hS0, hd0⟩))
      · constructor <;> linarith
      · constructor <;> linarith
      · exact False.elim (hsame (Or.inr ⟨hS0, hd0⟩))

/-- Choose a prime divisor `p ∣ h0` BEFORE selecting the next even gap: if `A.card < h0`, any
half-gap `d` with `¬ (p ∣ d)` strictly grows `A`; if `h0 ≤ A.card`, `A` already covers all `h0`
residues and `p = h0.minFac` preserves `h0 ≤ card`. -/
theorem exists_prime_step_for_set {h0 : ℕ} {A : Finset ℕ}
    (hh0 : 2 ≤ h0) (hA : A ⊆ Finset.range h0) (h0_mem : 0 ∈ A) :
    ∃ p : ℕ, Nat.Prime p ∧ p ∣ h0 ∧
      ∀ d : ℕ, ¬ (p ∣ d) →
        min h0 (A.card + 1) ≤ (A ∪ A.image (fun a => (a + d) % h0)).card := by
  by_cases hlt : A.card < h0
  · obtain ⟨p, hp, hdvd, hinc⟩ := exists_prime_dvd_step_increases_card (by omega) hA h0_mem hlt
    exact ⟨p, hp, hdvd, fun d hd => le_trans (Nat.min_le_right _ _) (hinc d hd).1⟩
  · refine ⟨h0.minFac, Nat.minFac_prime (by omega), Nat.minFac_dvd h0, ?_⟩
    intro d _
    have hsub := Finset.card_le_card (Finset.subset_union_left (s₁ := A)
      (s₂ := A.image (fun a => (a + d) % h0)))
    omega

/-- Enumeration of all `138` disjoint prime-supply zones in `(0, X]` outside Keepout `(0.355 X, 0.578 X]`. -/
inductive UTZone : Type
  | wideLow : Fin 30 → UTZone
  | pool1 : UTZone
  | pool2 : UTZone
  | modOrd : Fin 54 → UTZone
  | modDiagLo : UTZone
  | modDiagHi : UTZone
  | dblLow : Fin 10 → UTZone
  | dblHigh : Fin 10 → UTZone
  | wideHigh : Fin 30 → UTZone
  deriving DecidableEq

def UTZone.dblLowNat (k : Fin 10) : ℕ :=
  match k.val with
  | 0 => 8360 | 1 => 8370 | 2 => 8380 | 3 => 3230 | 4 => 3250
  | 5 => 8390 | 6 => 8400 | 7 => 3260 | 8 => 5780 | _ => 3510

def UTZone.dblHighNat (k : Fin 10) : ℕ :=
  match k.val with
  | 0 => 8440 | 1 => 8490 | 2 => 8510 | 3 => 3540 | 4 => 3530
  | 5 => 9250 | 6 => 9340 | 7 => 5790 | 8 => 9350 | _ => 9360

def UTZone.loNat : UTZone → ℕ
  | .wideLow m => 40 + 20 * m.val
  | .pool1 => 680
  | .pool2 => 5810
  | .modOrd m => 8520 + 12 * m.val
  | .modDiagLo => 9168
  | .modDiagHi => 9174
  | .dblLow k => UTZone.dblLowNat k
  | .dblHigh k => UTZone.dblHighNat k
  | .wideHigh m => 9380 + 20 * m.val

def UTZone.hiNat : UTZone → ℕ
  | .wideLow m => 40 + 20 * (m.val + 1)
  | .pool1 => 3230
  | .pool2 => 8360
  | .modOrd m => 8520 + 12 * (m.val + 1)
  | .modDiagLo => 9174
  | .modDiagHi => 9180
  | .dblLow k => UTZone.dblLowNat k + 10
  | .dblHigh k => UTZone.dblHighNat k + 10
  | .wideHigh m => 9380 + 20 * (m.val + 1)

def UTZone.finset (n : ℕ) : UTZone → Finset ℕ
  | .wideLow m => apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1
  | .pool1 => apInterval (utPool1Lo n) (utPool1Hi n) 2 1
  | .pool2 => apInterval (utPool2Lo n) (utPool2Hi n) 2 1
  | .modOrd m => apInterval (utModBinLo n m.val) (utModBinHi n m.val) 2 1
  | .modDiagLo => apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1
  | .modDiagHi => apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1
  | .dblLow k => apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1
  | .dblHigh k => apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1
  | .wideHigh m => apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1

private theorem apInterval_eq_of_endpoints {b₁ c₁ b₂ c₂ : ℝ} (hb : b₁ = b₂) (hc : c₁ = c₂) :
    apInterval b₁ c₁ 2 1 = apInterval b₂ c₂ 2 1 := by
  rw [hb, hc]

theorem UTZone.finset_eq_scaled (n : ℕ) (z : UTZone) :
    z.finset n = apInterval (((z.loNat : ℝ) / 10000) * utX n) (((z.hiNat : ℝ) / 10000) * utX n) 2 1 := by
  cases z with
  | wideLow m =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utWideLowLo]; push_cast; ring
    · dsimp [UTZone.hiNat, utWideLowHi]; push_cast; ring
  | pool1 =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utPool1Lo]; norm_num
    · dsimp [UTZone.hiNat, utPool1Hi]; norm_num
  | pool2 =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utPool2Lo]; norm_num
    · dsimp [UTZone.hiNat, utPool2Hi]; norm_num
  | modOrd m =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utModBinLo]; push_cast; ring
    · dsimp [UTZone.hiNat, utModBinHi]; push_cast; ring
  | modDiagLo =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utModBinLo]; norm_num
    · dsimp [UTZone.hiNat, utModBinMid]; norm_num
  | modDiagHi =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utModBinMid]; norm_num
    · dsimp [UTZone.hiNat, utModBinHi]; norm_num
  | dblLow k =>
    fin_cases k <;> (apply apInterval_eq_of_endpoints <;>
      [dsimp [UTZone.loNat, UTZone.dblLowNat, utDblLowLo, utDblLowFrac];
       dsimp [UTZone.hiNat, UTZone.dblLowNat, utDblLowHi, utDblLowFrac]] <;> norm_num)
  | dblHigh k =>
    fin_cases k <;> (apply apInterval_eq_of_endpoints <;>
      [dsimp [UTZone.loNat, UTZone.dblHighNat, utDblHighLo, utDblHighFrac];
       dsimp [UTZone.hiNat, UTZone.dblHighNat, utDblHighHi, utDblHighFrac]] <;> norm_num)
  | wideHigh m =>
    apply apInterval_eq_of_endpoints
    · dsimp [UTZone.loNat, utWideHighLo]; push_cast; ring
    · dsimp [UTZone.hiNat, utWideHighHi]; push_cast; ring

private theorem utZone_dblLow_regions :
    ∀ k : Fin 10,
      (3230 ≤ UTZone.dblLowNat k ∧ UTZone.dblLowNat k + 10 ≤ 3520) ∨
      (5780 ≤ UTZone.dblLowNat k ∧ UTZone.dblLowNat k + 10 ≤ 5790) ∨
      (8360 ≤ UTZone.dblLowNat k ∧ UTZone.dblLowNat k + 10 ≤ 8410) := by
  decide

private theorem utZone_dblHigh_regions :
    ∀ k : Fin 10,
      (3530 ≤ UTZone.dblHighNat k ∧ UTZone.dblHighNat k + 10 ≤ 3550) ∨
      (5790 ≤ UTZone.dblHighNat k ∧ UTZone.dblHighNat k + 10 ≤ 5800) ∨
      (8440 ≤ UTZone.dblHighNat k ∧ UTZone.dblHighNat k + 10 ≤ 8520) ∨
      (9250 ≤ UTZone.dblHighNat k ∧ UTZone.dblHighNat k + 10 ≤ 9370) := by
  decide

private theorem utZone_dbl_pair_sep :
    ∀ k₁ k₂ : Fin 10,
      (k₁ ≠ k₂ → UTZone.dblLowNat k₁ + 10 ≤ UTZone.dblLowNat k₂ ∨ UTZone.dblLowNat k₂ + 10 ≤ UTZone.dblLowNat k₁) ∧
      (k₁ ≠ k₂ → UTZone.dblHighNat k₁ + 10 ≤ UTZone.dblHighNat k₂ ∨ UTZone.dblHighNat k₂ + 10 ≤ UTZone.dblHighNat k₁) ∧
      (UTZone.dblLowNat k₁ + 10 ≤ UTZone.dblHighNat k₂ ∨ UTZone.dblHighNat k₂ + 10 ≤ UTZone.dblLowNat k₁) := by
  decide

theorem UTZone.bounds (z : UTZone) :
    40 ≤ z.loNat ∧ z.loNat < z.hiNat ∧ z.hiNat ≤ 9980 ∧ (z.hiNat ≤ 3550 ∨ 5780 ≤ z.loNat) := by
  cases z with
  | wideLow m => have := m.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | pool1 => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | pool2 => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modOrd m => have := m.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modDiagLo => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modDiagHi => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | dblLow k => have h := utZone_dblLow_regions k; dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | dblHigh k => have h := utZone_dblHigh_regions k; dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | wideHigh m => have := m.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega

theorem UTZone.sep {z₁ z₂ : UTZone} (hne : z₁ ≠ z₂) :
    z₁.hiNat ≤ z₂.loNat ∨ z₂.hiNat ≤ z₁.loNat := by
  cases z₁ with
  | wideLow m₁ =>
    have hm₁ := m₁.isLt
    cases z₂ with
    | wideLow m₂ =>
      have hm₂ := m₂.isLt
      have hne' : m₁.val ≠ m₂.val := fun h => hne (congrArg UTZone.wideLow (Fin.ext h))
      dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | pool1 =>
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | pool1 => exact False.elim (hne rfl)
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | pool2 =>
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | pool2 => exact False.elim (hne rfl)
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modOrd m₁ =>
    have hm₁ := m₁.isLt
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ =>
      have hm₂ := m₂.isLt
      have hne' : m₁.val ≠ m₂.val := fun h => hne (congrArg UTZone.modOrd (Fin.ext h))
      dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modDiagLo =>
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modDiagLo => exact False.elim (hne rfl)
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | modDiagHi =>
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modDiagHi => exact False.elim (hne rfl)
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | dblLow k₁ =>
    have hk₁ := utZone_dblLow_regions k₁
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblLow k₂ =>
      have hk := (utZone_dbl_pair_sep k₁ k₂).1 (fun h => hne (congrArg UTZone.dblLow h))
      dsimp [UTZone.loNat, UTZone.hiNat]; exact hk
    | dblHigh k₂ =>
      have hk := (utZone_dbl_pair_sep k₁ k₂).2.2
      dsimp [UTZone.loNat, UTZone.hiNat]; exact hk
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | dblHigh k₁ =>
    have hk₁ := utZone_dblHigh_regions k₁
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblLow k₂ =>
      have hk := (utZone_dbl_pair_sep k₂ k₁).2.2
      dsimp [UTZone.loNat, UTZone.hiNat]; exact hk.symm
    | dblHigh k₂ =>
      have hk := (utZone_dbl_pair_sep k₁ k₂).2.1 (fun h => hne (congrArg UTZone.dblHigh h))
      dsimp [UTZone.loNat, UTZone.hiNat]; exact hk
    | wideHigh m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega
  | wideHigh m₁ =>
    have hm₁ := m₁.isLt
    cases z₂ with
    | wideLow m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | modOrd m₂ => have hm₂ := m₂.isLt; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblLow k₂ => have hk₂ := utZone_dblLow_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | dblHigh k₂ => have hk₂ := utZone_dblHigh_regions k₂; dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | wideHigh m₂ =>
      have hm₂ := m₂.isLt
      have hne' : m₁.val ≠ m₂.val := fun h => hne (congrArg UTZone.wideHigh (Fin.ext h))
      dsimp [UTZone.loNat, UTZone.hiNat]; omega
    | _ => dsimp [UTZone.loNat, UTZone.hiNat]; omega

/-- Disjointness of `apInterval b₁ c₁ 2 1` and `apInterval b₂ c₂ 2 1` when `0 ≤ b₁ ≤ c₁ ≤ b₂ ≤ c₂`. -/
theorem apInterval_disjoint_of_le {b₁ c₁ b₂ c₂ : ℝ}
    (hb₁ : 0 ≤ b₁) (hc₁ : b₁ ≤ c₁) (hsep : c₁ ≤ b₂) (hc₂ : b₂ ≤ c₂) :
    Disjoint (apInterval b₁ c₁ 2 1) (apInterval b₂ c₂ 2 1) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  have h1 := (mem_apInterval_iff b₁ c₁ 2 1 hb₁ (hb₁.trans hc₁) p).mp hp1
  have h2 := (mem_apInterval_iff b₂ c₂ 2 1 (hb₁.trans (hc₁.trans hsep))
    ((hb₁.trans (hc₁.trans hsep)).trans hc₂) p).mp hp2
  linarith

theorem UTZone.disjoint (n : ℕ) {z₁ z₂ : UTZone} (hne : z₁ ≠ z₂) :
    Disjoint (z₁.finset n) (z₂.finset n) := by
  have hX_nn : 0 ≤ utX n := by dsimp [utX]; positivity
  obtain ⟨_, h12, _, _⟩ := z₁.bounds
  obtain ⟨_, h22, _, _⟩ := z₂.bounds
  rw [UTZone.finset_eq_scaled n z₁, UTZone.finset_eq_scaled n z₂]
  have hlo1 : (0 : ℝ) ≤ (z₁.loNat : ℝ) := Nat.cast_nonneg _
  have hlo2 : (0 : ℝ) ≤ (z₂.loNat : ℝ) := Nat.cast_nonneg _
  have hlt1 : (z₁.loNat : ℝ) ≤ (z₁.hiNat : ℝ) := by exact_mod_cast h12.le
  have hlt2 : (z₂.loNat : ℝ) ≤ (z₂.hiNat : ℝ) := by exact_mod_cast h22.le
  rcases UTZone.sep hne with hsep | hsep
  · have hsR : (z₁.hiNat : ℝ) ≤ (z₂.loNat : ℝ) := by exact_mod_cast hsep
    exact apInterval_disjoint_of_le (by positivity) (by nlinarith) (by nlinarith) (by nlinarith)
  · have hsR : (z₂.hiNat : ℝ) ≤ (z₁.loNat : ℝ) := by exact_mod_cast hsep
    exact (apInterval_disjoint_of_le (by positivity) (by nlinarith) (by nlinarith) (by nlinarith)).symm

theorem UTZone.elem_props {n : ℕ} (z : UTZone) {p : ℕ} (hp : p ∈ z.finset n) :
    Nat.Prime p ∧ Odd p ∧ p ∈ pool n ∧
    ((z.loNat : ℝ) / 10000) * utX n < (p : ℝ) ∧ (p : ℝ) ≤ ((z.hiNat : ℝ) / 10000) * utX n ∧
    ((p : ℝ) ≤ utKeepoutLo n ∨ utKeepoutHi n < (p : ℝ)) := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  obtain ⟨_, hlt, h9980, hkeep⟩ := z.bounds
  rw [UTZone.finset_eq_scaled n z] at hp
  have hlo_nn : 0 ≤ ((z.loNat : ℝ) / 10000) * utX n := by positivity
  have hhi_nn : 0 ≤ ((z.hiNat : ℝ) / 10000) * utX n := by positivity
  obtain ⟨hprime, hgt, hle, hmod⟩ := (mem_apInterval_iff _ _ 2 1 hlo_nn hhi_nn p).mp hp
  have hodd : Odd p := Nat.odd_iff.mpr (by exact_mod_cast hmod)
  have hne2 : p ≠ 2 := by intro h; subst p; obtain ⟨k, hk⟩ := hodd; omega
  have h9980R : (z.hiNat : ℝ) ≤ 9980 := by exact_mod_cast h9980
  have hp_le_max : p ≤ poolMaximum n := by
    have hR : (p : ℝ) ≤ (poolMaximum n : ℝ) := by dsimp [utX] at hle; nlinarith
    exact_mod_cast hR
  have hpool : p ∈ pool n := prime_mem_pool_of_le_max hprime hne2 hp_le_max
  have hk_out : (p : ℝ) ≤ utKeepoutLo n ∨ utKeepoutHi n < (p : ℝ) := by
    rcases hkeep with hk1 | hk2
    · left
      have hk1R : (z.hiNat : ℝ) ≤ 3550 := by exact_mod_cast hk1
      dsimp [utKeepoutLo]; nlinarith
    · right
      have hk2R : (5780 : ℝ) ≤ (z.loNat : ℝ) := by exact_mod_cast hk2
      dsimp [utKeepoutHi]; nlinarith
  exact ⟨hprime, hodd, hpool, hgt, hle, hk_out⟩

private theorem vec4_injective {u1 v1 v2 u2 : ℕ}
    (h01 : u1 ≠ v1) (h02 : u1 ≠ v2) (h03 : u1 ≠ u2)
    (h12 : v1 ≠ v2) (h13 : v1 ≠ u2) (h23 : v2 ≠ u2) :
    Function.Injective ![u1, v1, v2, u2] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega

/-- Build a `UTRectData` from a `DoublePair` valid on strictly separated odd sets `low`, `high`. -/
def utRectData_of_doublePair {low high : Finset ℕ}
    (hodd_lo : ∀ a ∈ low, Odd a) (hodd_hi : ∀ b ∈ high, Odd b)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (dp : DoublePair) (hv : dp.valid low high) : UTRectData where
  u1 := dp.low₁
  v1 := dp.high₁
  v2 := dp.high₂
  u2 := dp.low₂
  gap := dp.high₁ - dp.low₁
  hgap_pos := by
    have hlt1 := hv.2.2.2.2.2.2.1
    omega
  hgap_even := by
    obtain ⟨k1, hk1⟩ := hodd_lo dp.low₁ hv.1
    obtain ⟨k2, hk2⟩ := hodd_hi dp.high₁ hv.2.2.1
    have hlt1 := hv.2.2.2.2.2.2.1
    exact ⟨k2 - k1, by omega⟩
  hv1 := by
    have hlt1 := hv.2.2.2.2.2.2.1
    omega
  hv2 := by
    have hlt2 := hv.2.2.2.2.2.2.2.1
    have hdiff := hv.2.2.2.2.2.2.2.2
    omega
  hinj := by
    have h11 := hv.2.2.2.2.2.2.1
    have h22 := hv.2.2.2.2.2.2.2.1
    have h12 := horder _ hv.1 _ hv.2.2.2.1
    have h21 := horder _ hv.2.1 _ hv.2.2.1
    have hne_lo := hv.2.2.2.2.1
    have hne_hi := hv.2.2.2.2.2.1
    exact vec4_injective (by omega) (by omega) hne_lo hne_hi (by omega) (by omega)

/-- Extract `T` pairwise-disjoint `UTRectData` tuples from `(S_lo, S_hi)` when `2 * T ≤ U`
and `B < (S_lo.card - U) * (S_hi.card - U)`. -/
theorem exists_many_utRectData_of_product {S_lo S_hi : Finset ℕ} {B U : ℕ}
    (hodd_lo : ∀ a ∈ S_lo, Odd a) (hodd_hi : ∀ b ∈ S_hi, Odd b)
    (horder : ∀ a ∈ S_lo, ∀ b ∈ S_hi, a < b)
    (hspan : ∀ a ∈ S_lo, ∀ b ∈ S_hi, b - a < B)
    (hU_lo : U < S_lo.card) (hU_hi : U < S_hi.card)
    (hgate : B < (S_lo.card - U) * (S_hi.card - U)) :
    ∀ T : ℕ, 2 * T ≤ U →
      ∃ rects : Fin T → UTRectData,
        (∀ t, (rects t).u1 ∈ S_lo ∧ (rects t).u2 ∈ S_lo ∧
          (rects t).v1 ∈ S_hi ∧ (rects t).v2 ∈ S_hi) ∧
        (∀ t₁ t₂, t₁ ≠ t₂ → Disjoint (rects t₁).support (rects t₂).support) := by
  intro T hTU
  induction T with
  | zero =>
    exact ⟨fun t => t.elim0, fun t => t.elim0, fun t => t.elim0⟩
  | succ T ih =>
    obtain ⟨rects₀, hmem₀, hdisj₀⟩ := ih (by omega)
    let used_lo : Finset ℕ := Finset.univ.biUnion (fun t : Fin T => {(rects₀ t).u1, (rects₀ t).u2})
    let used_hi : Finset ℕ := Finset.univ.biUnion (fun t : Fin T => {(rects₀ t).v1, (rects₀ t).v2})
    have hused_lo_card : used_lo.card ≤ 2 * T := by
      calc
        used_lo.card ≤ ∑ _t : Fin T, 2 :=
          (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
        _ = 2 * T := by simp [Nat.mul_comm]
    have hused_hi_card : used_hi.card ≤ 2 * T := by
      calc
        used_hi.card ≤ ∑ _t : Fin T, 2 :=
          (Finset.card_biUnion_le).trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
        _ = 2 * T := by simp [Nat.mul_comm]
    let rem_lo := S_lo \ used_lo
    let rem_hi := S_hi \ used_hi
    have hrem_lo : S_lo.card - U ≤ rem_lo.card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_lo) (t := used_lo)
      dsimp [rem_lo] at *; omega
    have hrem_hi : S_hi.card - U ≤ rem_hi.card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_hi) (t := used_hi)
      dsimp [rem_hi] at *; omega
    have hcount : (Finset.range B).card < rem_lo.card * rem_hi.card := by
      rw [Finset.card_range]
      exact lt_of_lt_of_le hgate (Nat.mul_le_mul hrem_lo hrem_hi)
    obtain ⟨dp, hv⟩ := repeated_difference_double_pair rem_lo rem_hi (Finset.range B)
      (fun a ha b hb => horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      (fun a ha b hb => Finset.mem_range.mpr
        (hspan a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1))
      hcount
    let r_new := utRectData_of_doublePair
      (fun a ha => hodd_lo a (Finset.mem_sdiff.mp ha).1)
      (fun b hb => hodd_hi b (Finset.mem_sdiff.mp hb).1)
      (fun a ha b hb => horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      dp hv
    have hlo1_rem : r_new.u1 ∈ rem_lo := hv.1
    have hlo2_rem : r_new.u2 ∈ rem_lo := hv.2.1
    have hhi1_rem : r_new.v1 ∈ rem_hi := hv.2.2.1
    have hhi2_rem : r_new.v2 ∈ rem_hi := hv.2.2.2.1
    let rects : Fin (T + 1) → UTRectData := Fin.snoc rects₀ r_new
    refine ⟨rects, ?_, ?_⟩
    · intro t
      refine Fin.lastCases ?_ ?_ t
      · simp only [rects, Fin.snoc_last]
        exact ⟨(Finset.mem_sdiff.mp hlo1_rem).1, (Finset.mem_sdiff.mp hlo2_rem).1,
          (Finset.mem_sdiff.mp hhi1_rem).1, (Finset.mem_sdiff.mp hhi2_rem).1⟩
      · intro t₀
        simpa [rects] using hmem₀ t₀
    · have hdisj_new : ∀ t₀ : Fin T, Disjoint (rects₀ t₀).support r_new.support := by
        intro t₀
        rw [Finset.disjoint_left]
        intro x hx0 hxn
        have h0_mem := hmem₀ t₀
        have hx0_cases : (x = (rects₀ t₀).u1 ∨ x = (rects₀ t₀).u2) ∨
            (x = (rects₀ t₀).v1 ∨ x = (rects₀ t₀).v2) := by
          simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx0
          tauto
        have hxn_cases : (x = r_new.u1 ∨ x = r_new.u2) ∨ (x = r_new.v1 ∨ x = r_new.v2) := by
          simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hxn
          tauto
        rcases hx0_cases with h0_lo | h0_hi <;> rcases hxn_cases with hn_lo | hn_hi
        · have hx_used : x ∈ used_lo := Finset.mem_biUnion.mpr ⟨t₀, Finset.mem_univ _, by simp [h0_lo]⟩
          rcases hn_lo with rfl | rfl
          · exact (Finset.mem_sdiff.mp hlo1_rem).2 hx_used
          · exact (Finset.mem_sdiff.mp hlo2_rem).2 hx_used
        · have hxl : x ∈ S_lo := by rcases h0_lo with rfl | rfl <;> [exact h0_mem.1; exact h0_mem.2.1]
          have hxh : x ∈ S_hi := by
            rcases hn_hi with rfl | rfl
            · exact (Finset.mem_sdiff.mp hhi1_rem).1
            · exact (Finset.mem_sdiff.mp hhi2_rem).1
          exact Nat.lt_irrefl x (horder x hxl x hxh)
        · have hxl : x ∈ S_lo := by
            rcases hn_lo with rfl | rfl
            · exact (Finset.mem_sdiff.mp hlo1_rem).1
            · exact (Finset.mem_sdiff.mp hlo2_rem).1
          have hxh : x ∈ S_hi := by rcases h0_hi with rfl | rfl <;> [exact h0_mem.2.2.1; exact h0_mem.2.2.2]
          exact Nat.lt_irrefl x (horder x hxl x hxh)
        · have hx_used : x ∈ used_hi := Finset.mem_biUnion.mpr ⟨t₀, Finset.mem_univ _, by simp [h0_hi]⟩
          rcases hn_hi with rfl | rfl
          · exact (Finset.mem_sdiff.mp hhi1_rem).2 hx_used
          · exact (Finset.mem_sdiff.mp hhi2_rem).2 hx_used
      intro t₁ t₂
      refine Fin.lastCases ?_ (fun j₁ => ?_) t₁
      · refine Fin.lastCases ?_ (fun j₂ => ?_) t₂
        · intro hne; exact False.elim (hne rfl)
        · intro _; simpa [rects] using (hdisj_new j₂).symm
      · refine Fin.lastCases ?_ (fun j₂ => ?_) t₂
        · intro _; simpa [rects] using hdisj_new j₁
        · intro hne
          have hne' : j₁ ≠ j₂ := fun h => hne (congrArg Fin.castSucc h)
          simpa [rects] using hdisj₀ j₁ j₂ hne'

/-- Extract one `UTRectData` from `(rem_A, rem_B)` whose half-gap is NOT divisible by `p`,
by applying pigeonhole on the residue-filtered cross product
`{(a, b) ∈ rem_A ×ˢ rem_B | b % (2 * p) ≠ a % (2 * p)}`. -/
theorem exists_incongruent_utRectData_of_product {rem_A rem_B : Finset ℕ} {B M_B p : ℕ}
    (hodd_A : ∀ a ∈ rem_A, Odd a) (hodd_B : ∀ b ∈ rem_B, Odd b)
    (horder : ∀ a ∈ rem_A, ∀ b ∈ rem_B, a < b)
    (hspan : ∀ a ∈ rem_A, ∀ b ∈ rem_B, b - a < B)
    (hfilter : ∀ r : ℕ, (rem_B.filter (fun b => b % (2 * p) = r)).card ≤ M_B)
    (hgate : B < rem_A.card * (rem_B.card - M_B)) :
    ∃ rect : UTRectData,
      rect.u1 ∈ rem_A ∧ rect.u2 ∈ rem_A ∧ rect.v1 ∈ rem_B ∧ rect.v2 ∈ rem_B ∧
      ¬ (p ∣ rect.gap / 2) := by
  let P_good := (rem_A ×ˢ rem_B).filter (fun ab => ab.2 % (2 * p) ≠ ab.1 % (2 * p))
  have hcard_good : rem_A.card * (rem_B.card - M_B) ≤ P_good.card := by
    let fiber (a : ℕ) : Finset (ℕ × ℕ) :=
      (rem_B.filter (fun b => b % (2 * p) ≠ a % (2 * p))).image (fun b => (a, b))
    have hbij : P_good = rem_A.biUnion fiber := by
      ext ⟨a, b⟩
      simp [P_good, fiber, and_assoc]
    rw [hbij, Finset.card_biUnion]
    · calc
        rem_A.card * (rem_B.card - M_B) = ∑ _a ∈ rem_A, (rem_B.card - M_B) := by
          rw [Finset.sum_const, smul_eq_mul]
        _ ≤ ∑ a ∈ rem_A, (fiber a).card := by
          apply Finset.sum_le_sum
          intro a _
          dsimp [fiber]
          rw [Finset.card_image_of_injective _ (fun b₁ b₂ h => (Prod.mk.inj h).2)]
          have hpart : (rem_B.filter (fun b => b % (2 * p) = a % (2 * p))).card +
              (rem_B.filter (fun b => ¬(b % (2 * p) = a % (2 * p)))).card = rem_B.card :=
            Finset.card_filter_add_card_filter_not (fun b => b % (2 * p) = a % (2 * p))
          have hflt_eq : rem_B.filter (fun b => b % (2 * p) ≠ a % (2 * p)) =
              rem_B.filter (fun b => ¬(b % (2 * p) = a % (2 * p))) := rfl
          rw [hflt_eq]
          have hle := hfilter (a % (2 * p))
          omega
    · intro a₁ _ a₂ _ hne
      change Disjoint (fiber a₁) (fiber a₂)
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      dsimp [fiber] at hx1 hx2
      simp only [Finset.mem_image] at hx1 hx2
      obtain ⟨b₁, _, rfl⟩ := hx1
      obtain ⟨b₂, _, heq⟩ := hx2
      exact hne (Prod.mk.inj heq).1.symm
  have hcount : (Finset.range B).card < P_good.card := by
    rw [Finset.card_range]
    exact lt_of_lt_of_le hgate hcard_good
  obtain ⟨x, hx, y, hy, hxy, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcount
      (f := fun ab : ℕ × ℕ => ab.2 - ab.1) (by
        intro ab hab
        have hp := Finset.mem_product.mp (Finset.mem_filter.mp hab).1
        exact Finset.mem_range.mpr (hspan ab.1 hp.1 ab.2 hp.2))
  obtain ⟨a₁, b₁⟩ := x
  obtain ⟨a₂, b₂⟩ := y
  have hx_f := Finset.mem_filter.mp hx
  have hy_f := Finset.mem_filter.mp hy
  have hx_p := Finset.mem_product.mp hx_f.1
  have hy_p := Finset.mem_product.mp hy_f.1
  have ho₁ := horder a₁ hx_p.1 b₁ hx_p.2
  have ho₂ := horder a₂ hy_p.1 b₂ hy_p.2
  have ha : a₁ ≠ a₂ := by
    intro h; subst a₂
    have : b₁ = b₂ := by omega
    subst b₂; exact hxy rfl
  have hb : b₁ ≠ b₂ := by
    intro h; subst b₂
    have : a₁ = a₂ := by omega
    exact ha this
  have hv : DoublePair.valid ⟨a₁, a₂, b₁, b₂⟩ rem_A rem_B :=
    ⟨hx_p.1, hy_p.1, hx_p.2, hy_p.2, ha, hb, ho₁, ho₂, heq⟩
  let rect := utRectData_of_doublePair hodd_A hodd_B horder ⟨a₁, a₂, b₁, b₂⟩ hv
  refine ⟨rect, hx_p.1, hy_p.1, hx_p.2, hy_p.2, ?_⟩
  change ¬ (p ∣ (b₁ - a₁) / 2)
  exact not_dvd_half_gap_of_mod_two_mul_ne (hodd_A a₁ hx_p.1) (hodd_B b₁ hx_p.2) ho₁.le hx_f.2.symm

/-- Extract `K` pairwise-disjoint ordered odd pairs `(u k, v k)` from strictly separated sets `A`, `B`
with `K ≤ A.card` and `K ≤ B.card`. -/
theorem exists_disjoint_pairs_of_cards {A B : Finset ℕ} (K : ℕ)
    (hodd_A : ∀ a ∈ A, Odd a) (hodd_B : ∀ b ∈ B, Odd b)
    (horder : ∀ a ∈ A, ∀ b ∈ B, a < b)
    (hA : K ≤ A.card) (hB : K ≤ B.card) :
    ∃ u v : Fin K → ℕ,
      (∀ k, u k ∈ A ∧ v k ∈ B ∧ u k < v k ∧ 2 ∣ (v k - u k)) ∧
      (∀ k₁ k₂, k₁ ≠ k₂ → Disjoint ({u k₁, v k₁} : Finset ℕ) {u k₂, v k₂}) := by
  obtain ⟨A', hA'_sub, hA'_card⟩ := Finset.exists_subset_card_eq hA
  obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq hB
  let eA : Fin K ≃ A' := (A'.equivFinOfCardEq hA'_card).symm
  let eB : Fin K ≃ B' := (B'.equivFinOfCardEq hB'_card).symm
  refine ⟨fun k => (eA k).1, fun k => (eB k).1, ?_, ?_⟩
  · intro k
    have ha : (eA k).1 ∈ A := hA'_sub (eA k).2
    have hb : (eB k).1 ∈ B := hB'_sub (eB k).2
    have hlt : (eA k).1 < (eB k).1 := horder _ ha _ hb
    obtain ⟨m1, hm1⟩ := hodd_A _ ha
    obtain ⟨m2, hm2⟩ := hodd_B _ hb
    dsimp only
    exact ⟨ha, hb, hlt, ⟨m2 - m1, by omega⟩⟩
  · intro k₁ k₂ hne
    have ha1 : (eA k₁).1 ∈ A := hA'_sub (eA k₁).2
    have ha2 : (eA k₂).1 ∈ A := hA'_sub (eA k₂).2
    have hb1 : (eB k₁).1 ∈ B := hB'_sub (eB k₁).2
    have hb2 : (eB k₂).1 ∈ B := hB'_sub (eB k₂).2
    have hneA : (eA k₁).1 ≠ (eA k₂).1 := fun h => hne (eA.injective (Subtype.ext h))
    have hneB : (eB k₁).1 ≠ (eB k₂).1 := fun h => hne (eB.injective (Subtype.ext h))
    have h12 : (eA k₁).1 < (eB k₂).1 := horder _ ha1 _ hb2
    have h21 : (eA k₂).1 < (eB k₁).1 := horder _ ha2 _ hb1
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx1 hx2
    rcases hx1 with rfl | rfl <;> rcases hx2 with h | h <;> omega

/-! ## Section 2: Phase-by-Phase Extraction Lemmas -/

/-- Split a `UTGrowthWitness n` (`G := gw.stages.length`) into `6 * n` ordinary pairs per stage
plus `G` pairs of sign-balanced diagonal `UTRectData`s. -/
theorem ut_split_growth_stages {n : ℕ} (gw : UTGrowthWitness n) :
    let G := gw.stages.length
    ∃ (ord : Fin G → UTEdge n → Bool → ℕ) (diag : Fin G → Bool → UTRectData),
      (∀ (s : Fin G) (u : UTEdge n),
        ord s u true = ord s u false + (gw.stages.get s).gap ∧
        ord s u false ∈ (gw.stages.get s).lows ∧
        ord s u false ∈ (gw.stages.get s).footprint ∧
        ord s u true ∈ (gw.stages.get s).footprint) ∧
      (∀ (s : Fin G) (b : Bool),
        (diag s b).gap = (gw.stages.get s).gap ∧
        (diag s b).u1 ∈ (gw.stages.get s).lows ∧
        (diag s b).support ⊆ (gw.stages.get s).footprint) ∧
      (∀ (s : Fin G) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
        (u₁, b₁) ≠ (u₂, b₂) → ord s u₁ b₁ ≠ ord s u₂ b₂) ∧
      (∀ (s : Fin G), Disjoint (diag s true).support (diag s false).support) ∧
      (∀ (s : Fin G) (u : UTEdge n) (b₁ b₂ : Bool),
        ord s u b₁ ∉ (diag s b₂).support) ∧
      |(∑ s : Fin G, (((diag s true).u1 : ℝ) + ((diag s true).gap : ℝ) / 2)) -
        (∑ s : Fin G, (((diag s false).u1 : ℝ) + ((diag s false).gap : ℝ) / 2))| ≤
        utMidWidth n := by
  classical
  let G := gw.stages.length
  have hstage_split : ∀ s : Fin G,
      ∃ (ord_s : UTEdge n → Bool → ℕ) (r0 r1 : UTRectData),
        (∀ u : UTEdge n,
          ord_s u true = ord_s u false + (gw.stages.get s).gap ∧
          ord_s u false ∈ (gw.stages.get s).lows ∧
          ord_s u false ∈ (gw.stages.get s).footprint ∧
          ord_s u true ∈ (gw.stages.get s).footprint) ∧
        r0.gap = (gw.stages.get s).gap ∧ r1.gap = (gw.stages.get s).gap ∧
        r0.u1 ∈ (gw.stages.get s).lows ∧ r1.u1 ∈ (gw.stages.get s).lows ∧
        r0.support ⊆ (gw.stages.get s).footprint ∧ r1.support ⊆ (gw.stages.get s).footprint ∧
        (∀ u₁ u₂ : UTEdge n, ∀ b₁ b₂ : Bool, (u₁, b₁) ≠ (u₂, b₂) → ord_s u₁ b₁ ≠ ord_s u₂ b₂) ∧
        Disjoint r0.support r1.support ∧
        (∀ u : UTEdge n, ∀ b : Bool, ord_s u b ∉ r0.support ∧ ord_s u b ∉ r1.support) := by
    intro s
    let st := gw.stages.get s
    have hst_mem : st ∈ gw.stages := List.get_mem _ _
    obtain ⟨hgap_pos, hg_dvd, hcard, hmatch, _⟩ := gw.hstage_props st hst_mem
    have hgap_even : 2 ∣ st.gap := by
      have h2g : 2 ∣ gw.g := by rw [gw.hg_eq]; exact dvd_mul_right 2 _
      exact dvd_trans h2g hg_dvd
    have hcard6 : st.lows.card = 6 * n + 4 := by simpa [utQ] using hcard
    let eLows : Fin (6 * n + 4) ≃ st.lows := (st.lows.equivFinOfCardEq hcard6).symm
    let pAt : Fin (6 * n + 4) → ℕ := fun i => (eLows i).1
    have hpAt_mem : ∀ i, pAt i ∈ st.lows := fun i => (eLows i).2
    have hpAt_foot0 : ∀ i, pAt i ∈ st.footprint :=
      fun i => Finset.mem_union_left _ (hpAt_mem i)
    have hpAt_foot1 : ∀ i, pAt i + st.gap ∈ st.footprint :=
      fun i => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨pAt i, hpAt_mem i, rfl⟩)
    have hpAt_disj : ∀ i j : Fin (6 * n + 4), i ≠ j →
        Disjoint ({pAt i, pAt i + st.gap} : Finset ℕ) {pAt j, pAt j + st.gap} := by
      intro i j hij
      have hne : pAt i ≠ pAt j := fun h => hij (eLows.injective (Subtype.ext h))
      exact hmatch (pAt i) (hpAt_mem i) (pAt j) (hpAt_mem j) hne
    let mkRect (i₁ i₂ : Fin (6 * n + 4)) (hne_idx : i₁ ≠ i₂) : UTRectData := {
      u1 := pAt i₁
      v1 := pAt i₁ + st.gap
      v2 := pAt i₂ + st.gap
      u2 := pAt i₂
      gap := st.gap
      hgap_pos := hgap_pos
      hgap_even := hgap_even
      hv1 := rfl
      hv2 := rfl
      hinj := by
        have hd := Finset.disjoint_left.mp (hpAt_disj i₁ i₂ hne_idx)
        exact vec4_injective
          (by omega)
          (fun h => @hd (pAt i₁) (by simp) (by simp [h]))
          (fun h => @hd (pAt i₁) (by simp) (by simp [h]))
          (fun h => @hd (pAt i₁ + st.gap) (by simp) (by simp [h]))
          (fun h => @hd (pAt i₁ + st.gap) (by simp) (by simp [← h]))
          (by omega)
    }
    have hmk_sup : ∀ {i₁ i₂ : Fin (6 * n + 4)} (h : i₁ ≠ i₂),
        (mkRect i₁ i₂ h).support = {pAt i₁, pAt i₁ + st.gap} ∪ {pAt i₂, pAt i₂ + st.gap} := by
      intro i₁ i₂ h
      ext x
      simp only [mkRect, UTRectData.support, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    let idxOrd (u : UTEdge n) : Fin (6 * n + 4) := ⟨(utEdgeEquiv n u).val, by omega⟩
    let i0 : Fin (6 * n + 4) := ⟨6 * n, by omega⟩
    let i1 : Fin (6 * n + 4) := ⟨6 * n + 1, by omega⟩
    let i2 : Fin (6 * n + 4) := ⟨6 * n + 2, by omega⟩
    let i3 : Fin (6 * n + 4) := ⟨6 * n + 3, by omega⟩
    let ord_s : UTEdge n → Bool → ℕ := fun u b =>
      if b then pAt (idxOrd u) + st.gap else pAt (idxOrd u)
    have hi01 : i0 ≠ i1 := by intro h; simp [i0, i1, Fin.ext_iff] at h
    have hi23 : i2 ≠ i3 := by intro h; simp [i2, i3, Fin.ext_iff] at h
    let r0 := mkRect i0 i1 hi01
    let r1 := mkRect i2 i3 hi23
    have hr0_sup : r0.support = {pAt i0, pAt i0 + st.gap} ∪ {pAt i1, pAt i1 + st.gap} :=
      hmk_sup hi01
    have hr1_sup : r1.support = {pAt i2, pAt i2 + st.gap} ∪ {pAt i3, pAt i3 + st.gap} :=
      hmk_sup hi23
    have hr0_sub : r0.support ⊆ st.footprint := by
      intro x hx
      simp only [r0, mkRect, UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hpAt_foot0 i0
      · exact hpAt_foot1 i0
      · exact hpAt_foot1 i1
      · exact hpAt_foot0 i1
    have hr1_sub : r1.support ⊆ st.footprint := by
      intro x hx
      simp only [r1, mkRect, UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · exact hpAt_foot0 i2
      · exact hpAt_foot1 i2
      · exact hpAt_foot1 i3
      · exact hpAt_foot0 i3
    refine ⟨ord_s, r0, r1, ?_, rfl, rfl, hpAt_mem i0, hpAt_mem i2, hr0_sub, hr1_sub, ?_, ?_, ?_⟩
    · intro u
      exact ⟨rfl, hpAt_mem (idxOrd u), hpAt_foot0 (idxOrd u), hpAt_foot1 (idxOrd u)⟩
    · intro u₁ u₂ b₁ b₂ hne heq
      by_cases hu : u₁ = u₂
      · subst u₂
        cases b₁ <;> cases b₂
        · exact hne rfl
        · dsimp [ord_s] at heq; omega
        · dsimp [ord_s] at heq; omega
        · exact hne rfl
      · have hidx_ne : idxOrd u₁ ≠ idxOrd u₂ := by
          intro h
          have hv : (idxOrd u₁).val = (idxOrd u₂).val := congrArg Fin.val h
          exact hu ((utEdgeEquiv n).injective (Fin.ext hv))
        have hd := Finset.disjoint_left.mp (hpAt_disj (idxOrd u₁) (idxOrd u₂) hidx_ne)
        have hm1 : ord_s u₁ b₁ ∈ ({pAt (idxOrd u₁), pAt (idxOrd u₁) + st.gap} : Finset ℕ) := by
          cases b₁ <;> simp [ord_s]
        have hm2 : ord_s u₂ b₂ ∈ ({pAt (idxOrd u₂), pAt (idxOrd u₂) + st.gap} : Finset ℕ) := by
          cases b₂ <;> simp [ord_s]
        exact hd hm1 (heq ▸ hm2)
    · rw [hr0_sup, hr1_sup]
      have hd02 := hpAt_disj i0 i2 (by intro h; simp [i0, i2, Fin.ext_iff] at h)
      have hd03 := hpAt_disj i0 i3 (by intro h; simp [i0, i3, Fin.ext_iff] at h)
      have hd12 := hpAt_disj i1 i2 (by intro h; simp [i1, i2, Fin.ext_iff] at h)
      have hd13 := hpAt_disj i1 i3 (by intro h; simp [i1, i3, Fin.ext_iff] at h)
      exact Finset.disjoint_union_left.mpr
        ⟨Finset.disjoint_union_right.mpr ⟨hd02, hd03⟩,
         Finset.disjoint_union_right.mpr ⟨hd12, hd13⟩⟩
    · intro u b
      have hu_lt : (idxOrd u).val < 6 * n := (utEdgeEquiv n u).isLt
      have hd0 := hpAt_disj (idxOrd u) i0 (by intro h; have := congrArg Fin.val h; dsimp [i0] at this; omega)
      have hd1 := hpAt_disj (idxOrd u) i1 (by intro h; have := congrArg Fin.val h; dsimp [i1] at this; omega)
      have hd2 := hpAt_disj (idxOrd u) i2 (by intro h; have := congrArg Fin.val h; dsimp [i2] at this; omega)
      have hd3 := hpAt_disj (idxOrd u) i3 (by intro h; have := congrArg Fin.val h; dsimp [i3] at this; omega)
      have hm : ord_s u b ∈ ({pAt (idxOrd u), pAt (idxOrd u) + st.gap} : Finset ℕ) := by
        cases b <;> simp [ord_s]
      refine ⟨?_, ?_⟩
      · rw [hr0_sup]
        exact Finset.disjoint_left.mp (Finset.disjoint_union_right.mpr ⟨hd0, hd1⟩) hm
      · rw [hr1_sup]
        exact Finset.disjoint_left.mp (Finset.disjoint_union_right.mpr ⟨hd2, hd3⟩) hm
  choose ord r0 r1 hord_props hr0_gap hr1_gap hr0_low hr1_low hr0_sub hr1_sub hord_inj hr01_disj hord_nmem
    using hstage_split
  have hmid_nn : 0 ≤ utMidWidth n := by
    dsimp [utMidWidth, utX]; positivity
  have hpair_diff : ∀ s : Fin G,
      |(((r0 s).u1 : ℝ) + ((r0 s).gap : ℝ) / 2) -
        (((r1 s).u1 : ℝ) + ((r1 s).gap : ℝ) / 2)| ≤ utMidWidth n := by
    intro s
    have hnar := gw.hnarrow (gw.stages.get s) (List.get_mem _ _)
      (r0 s).u1 (hr0_low s) (r1 s).u1 (hr1_low s)
    rw [hr0_gap s, hr1_gap s]
    have heq : (((r0 s).u1 : ℝ) + ((gw.stages.get s).gap : ℝ) / 2) -
        (((r1 s).u1 : ℝ) + ((gw.stages.get s).gap : ℝ) / 2) =
        (((r0 s).u1 : ℝ) + (((r0 s).u1 + (gw.stages.get s).gap : ℕ) : ℝ)) / 2 -
        (((r1 s).u1 : ℝ) + (((r1 s).u1 + (gw.stages.get s).gap : ℕ) : ℝ)) / 2 := by
      push_cast; ring
    rw [heq]
    exact hnar.le
  obtain ⟨swap, hbal⟩ := greedy_sign_balance hmid_nn
    (fun s => ((r0 s).u1 : ℝ) + ((r0 s).gap : ℝ) / 2)
    (fun s => ((r1 s).u1 : ℝ) + ((r1 s).gap : ℝ) / 2) hpair_diff
  let diag : Fin G → Bool → UTRectData := fun s b =>
    if b then (if swap s then r1 s else r0 s)
    else (if swap s then r0 s else r1 s)
  refine ⟨ord, diag, hord_props, ?_, hord_inj, ?_, ?_, ?_⟩
  · intro s b
    have hdiag_eq : diag s b = r0 s ∨ diag s b = r1 s := by
      cases b <;> cases hsw : swap s <;> simp [diag, hsw]
    rcases hdiag_eq with h | h <;> rw [h]
    · exact ⟨hr0_gap s, hr0_low s, hr0_sub s⟩
    · exact ⟨hr1_gap s, hr1_low s, hr1_sub s⟩
  · intro s
    cases hsw : swap s
    · simpa [diag, hsw] using hr01_disj s
    · simpa [diag, hsw] using (hr01_disj s).symm
  · intro s u b₁ b₂
    cases b₂ <;> cases hsw : swap s <;>
      simp [diag, hsw, (hord_nmem s u b₁).1, (hord_nmem s u b₁).2]
  · have htrue : (∑ s : Fin G, (((diag s true).u1 : ℝ) + ((diag s true).gap : ℝ) / 2)) =
        ∑ s : Fin G, if swap s then (((r1 s).u1 : ℝ) + ((r1 s).gap : ℝ) / 2)
        else (((r0 s).u1 : ℝ) + ((r0 s).gap : ℝ) / 2) := by
      apply Finset.sum_congr rfl; intro s _; cases hsw : swap s <;> simp [diag, hsw]
    have hfalse : (∑ s : Fin G, (((diag s false).u1 : ℝ) + ((diag s false).gap : ℝ) / 2)) =
        ∑ s : Fin G, if swap s then (((r0 s).u1 : ℝ) + ((r0 s).gap : ℝ) / 2)
        else (((r1 s).u1 : ℝ) + ((r1 s).gap : ℝ) / 2) := by
      apply Finset.sum_congr rfl; intro s _; cases hsw : swap s <;> simp [diag, hsw]
    rw [htrue, hfalse]
    exact hbal

/-- Extract `h0 - 1` ordinary `ModCover` stages across `ModBin 0..53`, achieving full modular
half-gap coverage modulo `h0` simultaneously on every edge `u : UTEdge n`. -/
theorem ut_extract_ordinary_modcover
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n h0 : ℕ} (hn : 35735 ≤ n) (hh0_ge2 : 2 ≤ h0) (hh0_le : h0 ≤ utH0Max n) :
    ∃ modOrd : Fin (h0 - 1) → UTEdge n → Bool → ℕ,
      (∀ (j : Fin (h0 - 1)) (u : UTEdge n),
        modOrd j u false ∈ apInterval (utModBinLo n (j.val % 54)) (utModBinHi n (j.val % 54)) 2 1 ∧
        modOrd j u true ∈ apInterval (utModBinLo n (j.val % 54)) (utModBinHi n (j.val % 54)) 2 1 ∧
        modOrd j u false < modOrd j u true ∧
        2 ∣ (modOrd j u true - modOrd j u false)) ∧
      (∀ (j₁ j₂ : Fin (h0 - 1)) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
        (j₁, u₁, b₁) ≠ (j₂, u₂, b₂) → modOrd j₁ u₁ b₁ ≠ modOrd j₂ u₂ b₂) ∧
      (∀ (u : UTEdge n) (r : ℕ), r < h0 →
        ∃ T : Finset (Fin (h0 - 1)),
          ((∑ j ∈ T, (modOrd j u true - modOrd j u false)) / 2) % h0 = r) := by
  classical
  have hcard_edge : Fintype.card (UTEdge n) = 6 * n := by
    rw [Fintype.card_congr (utEdgeEquiv n), Fintype.card_fin]
  suffices hloop : ∀ K : ℕ, K ≤ h0 - 1 →
      ∃ (modOrd : ℕ → UTEdge n → Bool → ℕ) (A : UTEdge n → Finset ℕ),
        (∀ j < K, ∀ u : UTEdge n,
          modOrd j u false ∈ apInterval (utModBinLo n (j % 54)) (utModBinHi n (j % 54)) 2 1 ∧
          modOrd j u true ∈ apInterval (utModBinLo n (j % 54)) (utModBinHi n (j % 54)) 2 1 ∧
          modOrd j u false < modOrd j u true ∧
          2 ∣ (modOrd j u true - modOrd j u false)) ∧
        (∀ j₁ < K, ∀ j₂ < K, ∀ (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
          (j₁, u₁, b₁) ≠ (j₂, u₂, b₂) → modOrd j₁ u₁ b₁ ≠ modOrd j₂ u₂ b₂) ∧
        (∀ u : UTEdge n,
          ModAchievable h0 (fun j => modOrd j u true - modOrd j u false) (Finset.range K) (A u) ∧
          min h0 (K + 1) ≤ (A u).card) by
    obtain ⟨modOrd, A, hprops, hinj, hach⟩ := hloop (h0 - 1) le_rfl
    refine ⟨fun j => modOrd j.val, fun j u => hprops j.val j.isLt u, ?_, ?_⟩
    · intro j₁ j₂ u₁ u₂ b₁ b₂ hne
      apply hinj j₁.val j₁.isLt j₂.val j₂.isLt u₁ u₂ b₁ b₂
      intro heq
      rcases Prod.mk.inj heq with ⟨hj, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hu, hb⟩
      exact hne (by ext <;> simp [hj, hu, hb])
    · intro u r hr
      have hcard : h0 ≤ (A u).card := by
        have hm := (hach u).2
        have : min h0 (h0 - 1 + 1) = h0 := by omega
        rwa [this] at hm
      obtain ⟨_, hcov⟩ := modAchievable_full_cover (hach u).1 hcard
      obtain ⟨T0, hT0_sub, hT0_mod⟩ := hcov r hr
      let T : Finset (Fin (h0 - 1)) := T0.attach.map
        ⟨fun x => ⟨x.1, Finset.mem_range.mp (hT0_sub x.2)⟩,
         fun x₁ x₂ h => Subtype.ext (congrArg Fin.val h)⟩
      refine ⟨T, ?_⟩
      have hsum_eq : (∑ j ∈ T, (modOrd j.val u true - modOrd j.val u false)) =
          ∑ j ∈ T0, (modOrd j u true - modOrd j u false) := by
        dsimp [T]
        rw [Finset.sum_map]
        conv_rhs => rw [← Finset.sum_attach T0]
        rfl
      rw [hsum_eq, hT0_mod]
  intro K hK
  induction K with
  | zero =>
    refine ⟨fun _ _ _ => 0, fun _ => {0}, ?_, ?_, ?_⟩
    · intro j hj; omega
    · intro j₁ hj₁; omega
    · intro u
      exact ⟨modAchievable_empty h0 _ (by omega), by simp⟩
  | succ K ih =>
    obtain ⟨modOrd₀, A₀, hprops₀, hinj₀, hach₀⟩ := ih (by omega)
    choose p hp_prime hp_dvd hp_step using
      fun u => exists_prime_step_for_set hh0_ge2 (hach₀ u).1.1 (hach₀ u).1.2.1
    have hp_le : ∀ u : UTEdge n, p u ≤ utH0Max n :=
      fun u => le_trans (Nat.le_of_dvd (by omega) (hp_dvd u)) hh0_le
    let m : ℕ := K % 54
    have hm : m < 54 := Nat.mod_lt K (by decide)
    obtain ⟨M, hM_card, hM_flt⟩ := ut_mod_bin_supply bmor imp mv rs lower sharp upper hn hm
    let Bin := apInterval (utModBinLo n m) (utModBinHi n m) 2 1
    let J_prev := (Finset.range K).filter (fun j => j % 54 = m)
    have hJ_card : J_prev.card ≤ utModRounds n - 1 := by
      have hsub := Finset.card_le_card_of_injOn (fun j => j / 54)
        (s := J_prev) (t := Finset.range (utModRounds n - 1))
        (by
          intro j hj
          rw [Finset.mem_coe] at hj ⊢
          obtain ⟨hjK, hjm⟩ := Finset.mem_filter.mp hj
          rw [Finset.mem_range] at hjK ⊢
          have hK_lt : K < utH0Max n := by omega
          dsimp [m] at hjm
          dsimp [utModRounds]
          omega)
        (by
          intro j₁ hj₁ j₂ hj₂ hdiv
          rw [Finset.mem_coe] at hj₁ hj₂
          have h1 : j₁ % 54 = m := (Finset.mem_filter.mp hj₁).2
          have h2 : j₂ % 54 = m := (Finset.mem_filter.mp hj₂).2
          dsimp only at hdiv
          omega)
      simpa using hsub
    let used := J_prev.biUnion (fun j =>
      Finset.univ.biUnion (fun u : UTEdge n => {modOrd₀ j u false, modOrd₀ j u true}))
    have hused_card : used.card ≤ (utModRounds n - 1) * (2 * (6 * n)) := by
      have hinner : ∀ j : ℕ,
          (Finset.univ.biUnion (fun u : UTEdge n => {modOrd₀ j u false, modOrd₀ j u true})).card ≤
            2 * (6 * n) := by
        intro j
        calc
          (Finset.univ.biUnion (fun u : UTEdge n => {modOrd₀ j u false, modOrd₀ j u true})).card
              ≤ ∑ _u : UTEdge n, 2 :=
            Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
          _ = Fintype.card (UTEdge n) * 2 := by simp
          _ = 2 * (6 * n) := by rw [hcard_edge]; ring
      calc
        used.card ≤ ∑ _j ∈ J_prev, (2 * (6 * n)) :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => hinner j)
        _ = J_prev.card * (2 * (6 * n)) := by simp
        _ ≤ (utModRounds n - 1) * (2 * (6 * n)) := Nat.mul_le_mul_right _ hJ_card
    have hrnd_pos : 1 ≤ utModRounds n := by dsimp [utModRounds]; omega
    have hrem_card : M + 2 * (6 * n) ≤ (Bin \ used).card := by
      have hsdiff := Finset.card_le_card_sdiff_add_card (s := Bin) (t := used)
      have hBin_card : M + 2 * utModRounds n * (6 * n) ≤ Bin.card := hM_card
      have hmul : (utModRounds n - 1) * (2 * (6 * n)) + 2 * (6 * n) = 2 * utModRounds n * (6 * n) := by
        zify [hrnd_pos]; ring
      have hle1 : M + 2 * (6 * n) + used.card ≤ Bin.card := by omega
      omega
    let colFn : Fin (6 * n) → ℕ → ℕ := fun i x => x % (2 * p ((utEdgeEquiv n).symm i))
    obtain ⟨u_new, v_new, huv_props, huv_disj⟩ :=
      exists_heterogeneous_incongruent_pairs colFn M hrem_card (by
        intro i c
        calc
          ((Bin \ used).filter (fun x => colFn i x = c)).card
              ≤ (Bin.filter (fun x => colFn i x = c)).card :=
            Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)
          _ ≤ M := hM_flt _ c (hp_prime _) (hp_le _))
    let modOrd : ℕ → UTEdge n → Bool → ℕ := fun j u b =>
      if j = K then (if b then v_new (utEdgeEquiv n u) else u_new (utEdgeEquiv n u))
      else modOrd₀ j u b
    let A : UTEdge n → Finset ℕ := fun u =>
      A₀ u ∪ (A₀ u).image (fun a => (a + (modOrd K u true - modOrd K u false) / 2) % h0)
    have hBin_zone : Bin = (UTZone.modOrd ⟨m, hm⟩).finset n := rfl
    have huv_bin : ∀ u : UTEdge n,
        u_new (utEdgeEquiv n u) ∈ Bin ∧ v_new (utEdgeEquiv n u) ∈ Bin ∧
        u_new (utEdgeEquiv n u) < v_new (utEdgeEquiv n u) ∧
        2 ∣ (v_new (utEdgeEquiv n u) - u_new (utEdgeEquiv n u)) ∧
        u_new (utEdgeEquiv n u) ∉ used ∧ v_new (utEdgeEquiv n u) ∉ used := by
      intro u
      obtain ⟨hu_s, hv_s, hlt, _⟩ := huv_props (utEdgeEquiv n u)
      have hu_b := (Finset.mem_sdiff.mp hu_s).1
      have hv_b := (Finset.mem_sdiff.mp hv_s).1
      obtain ⟨k1, hk1⟩ := (UTZone.elem_props (UTZone.modOrd ⟨m, hm⟩) (hBin_zone ▸ hu_b)).2.1
      obtain ⟨k2, hk2⟩ := (UTZone.elem_props (UTZone.modOrd ⟨m, hm⟩) (hBin_zone ▸ hv_b)).2.1
      exact ⟨hu_b, hv_b, hlt, ⟨k2 - k1, by omega⟩,
        (Finset.mem_sdiff.mp hu_s).2, (Finset.mem_sdiff.mp hv_s).2⟩
    have hmodOrd_lt : ∀ {j : ℕ}, j < K → ∀ (u : UTEdge n) (b : Bool),
        modOrd j u b = modOrd₀ j u b := fun hj _ _ => if_neg (ne_of_lt hj)
    have hmodOrd_eq : ∀ (u : UTEdge n) (b : Bool),
        modOrd K u b = if b then v_new (utEdgeEquiv n u) else u_new (utEdgeEquiv n u) :=
      fun _ _ => if_pos rfl
    refine ⟨modOrd, A, ?_, ?_, ?_⟩
    · intro j hj u
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | rfl
      · rw [hmodOrd_lt hjK u false, hmodOrd_lt hjK u true]
        exact hprops₀ j hjK u
      · rw [hmodOrd_eq u false, hmodOrd_eq u true]
        obtain ⟨h1, h2, h3, h4, _, _⟩ := huv_bin u
        exact ⟨h1, h2, h3, h4⟩
    · intro j₁ hj₁ j₂ hj₂ u₁ u₂ b₁ b₂ hne heq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj₁ with h1K | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj₂ with h2K | rfl
      · simp only [modOrd, ne_of_lt h1K, ne_of_lt h2K, ↓reduceIte] at heq
        exact hinj₀ j₁ h1K j₂ h2K u₁ u₂ b₁ b₂ hne heq
      · simp only [modOrd, ne_of_lt h1K, ↓reduceIte] at heq
        by_cases hmod : j₁ % 54 = m
        · have hmem_used : modOrd₀ j₁ u₁ b₁ ∈ used := by
            apply Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h1K, hmod⟩, ?_⟩
            exact Finset.mem_biUnion.mpr ⟨u₁, Finset.mem_univ _, by cases b₁ <;> simp⟩
          rw [heq] at hmem_used
          cases b₂
          · exact (huv_bin u₂).2.2.2.2.1 hmem_used
          · exact (huv_bin u₂).2.2.2.2.2 hmem_used
        · have hz_ne : UTZone.modOrd ⟨j₁ % 54, Nat.mod_lt _ (by decide)⟩ ≠ UTZone.modOrd ⟨m, hm⟩ :=
            fun h => hmod (congrArg Fin.val (UTZone.modOrd.inj h))
          have hd := Finset.disjoint_left.mp (UTZone.disjoint n hz_ne)
          have hm1 : modOrd₀ j₁ u₁ b₁ ∈ (UTZone.modOrd ⟨j₁ % 54, Nat.mod_lt _ (by decide)⟩).finset n := by
            cases b₁
            · exact (hprops₀ j₁ h1K u₁).1
            · exact (hprops₀ j₁ h1K u₁).2.1
          have hm2 : (if b₂ = true then v_new (utEdgeEquiv n u₂) else u_new (utEdgeEquiv n u₂)) ∈
              (UTZone.modOrd ⟨m, hm⟩).finset n := by
            cases b₂
            · exact (huv_bin u₂).1
            · exact (huv_bin u₂).2.1
          exact hd hm1 (heq ▸ hm2)
      · simp only [modOrd, ne_of_lt h2K, ↓reduceIte] at heq
        by_cases hmod : j₂ % 54 = m
        · have hmem_used : modOrd₀ j₂ u₂ b₂ ∈ used := by
            apply Finset.mem_biUnion.mpr ⟨j₂, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr h2K, hmod⟩, ?_⟩
            exact Finset.mem_biUnion.mpr ⟨u₂, Finset.mem_univ _, by cases b₂ <;> simp⟩
          rw [← heq] at hmem_used
          cases b₁
          · exact (huv_bin u₁).2.2.2.2.1 hmem_used
          · exact (huv_bin u₁).2.2.2.2.2 hmem_used
        · have hz_ne : UTZone.modOrd ⟨j₂ % 54, Nat.mod_lt _ (by decide)⟩ ≠ UTZone.modOrd ⟨m, hm⟩ :=
            fun h => hmod (congrArg Fin.val (UTZone.modOrd.inj h))
          have hd := Finset.disjoint_left.mp (UTZone.disjoint n hz_ne)
          have hm2 : modOrd₀ j₂ u₂ b₂ ∈ (UTZone.modOrd ⟨j₂ % 54, Nat.mod_lt _ (by decide)⟩).finset n := by
            cases b₂
            · exact (hprops₀ j₂ h2K u₂).1
            · exact (hprops₀ j₂ h2K u₂).2.1
          have hm1 : (if b₁ = true then v_new (utEdgeEquiv n u₁) else u_new (utEdgeEquiv n u₁)) ∈
              (UTZone.modOrd ⟨m, hm⟩).finset n := by
            cases b₁
            · exact (huv_bin u₁).1
            · exact (huv_bin u₁).2.1
          exact hd hm2 (heq.symm ▸ hm1)
      · simp only [modOrd, ↓reduceIte] at heq
        by_cases hu : u₁ = u₂
        · subst u₂
          cases b₁ <;> cases b₂
          · exact hne rfl
          · have hlt := (huv_props (utEdgeEquiv n u₁)).2.2.1
            simp only [Bool.false_eq_true, ↓reduceIte] at heq; omega
          · have hlt := (huv_props (utEdgeEquiv n u₁)).2.2.1
            simp only [Bool.false_eq_true, ↓reduceIte] at heq; omega
          · exact hne rfl
        · have hi_ne : utEdgeEquiv n u₁ ≠ utEdgeEquiv n u₂ :=
            fun h => hu ((utEdgeEquiv n).injective h)
          have hd := Finset.disjoint_left.mp (huv_disj _ _ hi_ne)
          have hm1 : (if b₁ = true then v_new (utEdgeEquiv n u₁) else u_new (utEdgeEquiv n u₁)) ∈
              ({u_new (utEdgeEquiv n u₁), v_new (utEdgeEquiv n u₁)} : Finset ℕ) := by
            cases b₁ <;> simp
          have hm2 : (if b₂ = true then v_new (utEdgeEquiv n u₂) else u_new (utEdgeEquiv n u₂)) ∈
              ({u_new (utEdgeEquiv n u₂), v_new (utEdgeEquiv n u₂)} : Finset ℕ) := by
            cases b₂ <;> simp
          exact hd hm1 (heq ▸ hm2)
    · intro u
      have hmod_K : ModAchievable h0 (fun j => modOrd j u true - modOrd j u false)
          (Finset.range K) (A₀ u) := by
        rcases (hach₀ u).1 with ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, ?_, ?_⟩
        · intro j hj
          simpa [modOrd, ne_of_lt (Finset.mem_range.mp hj)] using h3 j hj
        · intro r hr
          obtain ⟨T, hT, hsum⟩ := h4 r hr
          refine ⟨T, hT, ?_⟩
          have heq : (∑ j ∈ T, (modOrd j u true - modOrd j u false)) =
              ∑ j ∈ T, (modOrd₀ j u true - modOrd₀ j u false) :=
            Finset.sum_congr rfl fun j hj => by
              simp [modOrd, ne_of_lt (Finset.mem_range.mp (hT hj))]
          rw [heq, hsum]
      have hrange_eq : Finset.range (K + 1) = insert K (Finset.range K) := by
        ext j; simp [le_iff_lt_or_eq, or_comm]
      have hins := modAchievable_insert (by omega : 0 < h0) hmod_K
        (by simp : K ∉ Finset.range K) (by simpa [modOrd] using (huv_bin u).2.2.2.1)
      rw [← hrange_eq] at hins
      have hndvd : ¬ (p u ∣ (modOrd K u true - modOrd K u false) / 2) := by
        obtain ⟨hu_s, hv_s, hlt, hcol_ne⟩ := huv_props (utEdgeEquiv n u)
        have hcol_ne' : u_new (utEdgeEquiv n u) % (2 * p u) ≠ v_new (utEdgeEquiv n u) % (2 * p u) := by
          simpa [colFn, Equiv.symm_apply_apply] using hcol_ne
        have hu_odd := (UTZone.elem_props (UTZone.modOrd ⟨m, hm⟩)
          (hBin_zone ▸ (Finset.mem_sdiff.mp hu_s).1)).2.1
        have hv_odd := (UTZone.elem_props (UTZone.modOrd ⟨m, hm⟩)
          (hBin_zone ▸ (Finset.mem_sdiff.mp hv_s).1)).2.1
        simpa [modOrd] using not_dvd_half_gap_of_mod_two_mul_ne hu_odd hv_odd hlt.le hcol_ne'
      have hcard_inc := hp_step u _ hndvd
      have hcard0 := (hach₀ u).2
      exact ⟨hins, by dsimp [A]; omega⟩

private def dummyUTRectData : UTRectData where
  u1 := 0
  v1 := 2
  v2 := 3
  u2 := 1
  gap := 2
  hgap_pos := by decide
  hgap_even := ⟨1, rfl⟩
  hv1 := rfl
  hv2 := rfl
  hinj := vec4_injective (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem card_cur_le_four_mul {c u k h0 H : ℕ}
    (hc : c ≤ u + 2 * k) (hu : u ≤ 2 * (h0 - 1)) (hk : k + 1 ≤ h0 - 1) (hh : h0 ≤ H) :
    c ≤ 4 * H := by
  omega

private theorem sub_four_mul_le_sdiff {s r c H : ℕ}
    (hs : s ≤ r + c) (hc : c ≤ 4 * H) :
    s - 4 * H ≤ r := by
  omega

private theorem sub_four_mul_sub_le_sdiff {s r c H M : ℕ}
    (hs : s ≤ r + c) (hc : c ≤ 4 * H) :
    s - 4 * H - M ≤ r - M := by
  omega

private theorem min_succ_le_of_min_le {h0 k a0 a1 : ℕ}
    (h0_le : min h0 (k + 1) ≤ a0) (h1_le : min h0 (a0 + 1) ≤ a1) :
    min h0 (k + 1 + 1) ≤ a1 := by
  omega

/-- Extract one diagonal `ModCover` family of `h0 - 1` pairwise-disjoint `UTRectData`s in `ModBin 54`
disjoint from a given `(used_A, used_B)` of size `≤ 2 * (h0 - 1)`. -/
private theorem ut_extract_single_diag_modcover
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n h0 : ℕ} (hn : 35735 ≤ n) (hh0_ge2 : 2 ≤ h0) (hh0_le : h0 ≤ utH0Max n)
    (used_A used_B : Finset ℕ) (huA : used_A.card ≤ 2 * (h0 - 1)) (huB : used_B.card ≤ 2 * (h0 - 1)) :
    let S_A := apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1
    let S_B := apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1
    ∃ rects : Fin (h0 - 1) → UTRectData,
      (∀ j : Fin (h0 - 1),
        (rects j).u1 ∈ S_A \ used_A ∧ (rects j).u2 ∈ S_A \ used_A ∧
        (rects j).v1 ∈ S_B \ used_B ∧ (rects j).v2 ∈ S_B \ used_B) ∧
      (∀ j₁ j₂ : Fin (h0 - 1), j₁ ≠ j₂ → Disjoint (rects j₁).support (rects j₂).support) ∧
      (∀ r : ℕ, r < h0 → ∃ T : Finset (Fin (h0 - 1)), ((∑ j ∈ T, (rects j).gap) / 2) % h0 = r) := by
  classical
  dsimp only
  have hh0_pos : 0 < h0 := Nat.lt_of_lt_of_le (by decide : 0 < 2) hh0_ge2
  let S_A := apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1
  let S_B := apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1
  obtain ⟨M_B, hSA_gt, hSB_gt, hprod_gt, hMB_flt⟩ :=
    ut_mod_diag_half_bin_supply bmor imp mv rs lower sharp upper hn
  have hZA : S_A = UTZone.modDiagLo.finset n := rfl
  have hZB : S_B = UTZone.modDiagHi.finset n := rfl
  have hodd_A : ∀ a ∈ S_A, Odd a := fun a ha => (UTZone.elem_props UTZone.modDiagLo (hZA ▸ ha)).2.1
  have hodd_B : ∀ b ∈ S_B, Odd b := fun b hb => (UTZone.elem_props UTZone.modDiagHi (hZB ▸ hb)).2.1
  have horder : ∀ a ∈ S_A, ∀ b ∈ S_B, a < b := by
    intro a ha b hb
    have ha_le := (UTZone.elem_props UTZone.modDiagLo (hZA ▸ ha)).2.2.2.2.1
    have hb_gt := (UTZone.elem_props UTZone.modDiagHi (hZB ▸ hb)).2.2.2.1
    have hltR : (a : ℝ) < (b : ℝ) := by dsimp [UTZone.loNat, UTZone.hiNat] at ha_le hb_gt; linarith
    exact_mod_cast hltR
  let B_span : ℕ := ⌊utModBinHi n 54 - utModBinLo n 54⌋₊ + 1
  have hspan : ∀ a ∈ S_A, ∀ b ∈ S_B, b - a < B_span := by
    intro a ha b hb
    have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
    have ha_gt : utModBinLo n 54 < (a : ℝ) := by
      have h := (UTZone.elem_props UTZone.modDiagLo (hZA ▸ ha)).2.2.2.1
      dsimp [UTZone.loNat, utModBinLo] at h ⊢; linarith
    have hb_le : (b : ℝ) ≤ utModBinHi n 54 := by
      have h := (UTZone.elem_props UTZone.modDiagHi (hZB ▸ hb)).2.2.2.2.1
      dsimp [UTZone.hiNat, utModBinHi] at h ⊢; linarith
    have hab : a ≤ b := (horder a ha b hb).le
    have hsub_lt : ((b - a : ℕ) : ℝ) < (B_span : ℝ) := by
      rw [Nat.cast_sub hab]
      have hfl := Nat.lt_floor_add_one (utModBinHi n 54 - utModBinLo n 54)
      dsimp [B_span]; push_cast; linarith
    exact_mod_cast hsub_lt
  suffices hloop : ∀ K : ℕ, K ≤ h0 - 1 →
      ∃ (rects : ℕ → UTRectData) (A : Finset ℕ),
        (∀ j < K,
          (rects j).u1 ∈ S_A \ used_A ∧ (rects j).u2 ∈ S_A \ used_A ∧
          (rects j).v1 ∈ S_B \ used_B ∧ (rects j).v2 ∈ S_B \ used_B) ∧
        (∀ j₁ < K, ∀ j₂ < K, j₁ ≠ j₂ → Disjoint (rects j₁).support (rects j₂).support) ∧
        ModAchievable h0 (fun j => (rects j).gap) (Finset.range K) A ∧
        min h0 (K + 1) ≤ A.card by
    obtain ⟨rects, A, hmem, hdisj, hach, hcard_min⟩ := hloop (h0 - 1) le_rfl
    refine ⟨fun j => rects j.val, fun j => hmem j.val j.isLt,
      fun j₁ j₂ hne => hdisj j₁.val j₁.isLt j₂.val j₂.isLt (fun h => hne (Fin.ext h)), ?_⟩
    intro r hr
    have hcard : h0 ≤ A.card := by
      have : min h0 (h0 - 1 + 1) = h0 := by omega
      rwa [this] at hcard_min
    obtain ⟨_, hcov⟩ := modAchievable_full_cover hach hcard
    obtain ⟨T0, hT0_sub, hT0_mod⟩ := hcov r hr
    let T : Finset (Fin (h0 - 1)) := T0.attach.map
      ⟨fun x => ⟨x.1, Finset.mem_range.mp (hT0_sub x.2)⟩,
       fun x₁ x₂ h => Subtype.ext (congrArg Fin.val h)⟩
    refine ⟨T, ?_⟩
    have hsum_eq : (∑ j ∈ T, (rects j.val).gap) = ∑ j ∈ T0, (rects j).gap := by
      dsimp [T]; rw [Finset.sum_map]; conv_rhs => rw [← Finset.sum_attach T0]
      rfl
    rw [hsum_eq, hT0_mod]
  intro K hK
  induction K with
  | zero =>
    refine ⟨fun _ => dummyUTRectData, {0}, by intro j hj; exact absurd hj (Nat.not_lt_zero j),
      by intro j₁ hj₁; exact absurd hj₁ (Nat.not_lt_zero j₁),
      modAchievable_empty h0 _ hh0_pos, by simp⟩
  | succ K ih =>
    obtain ⟨rects₀, A₀, hmem₀, hdisj₀, hach₀, hcard₀⟩ := ih (Nat.le_of_succ_le hK)
    obtain ⟨p, hp_prime, hp_dvd, hp_step⟩ := exists_prime_step_for_set hh0_ge2 hach₀.1 hach₀.2.1
    have hp_le : p ≤ utH0Max n := le_trans (Nat.le_of_dvd hh0_pos hp_dvd) hh0_le
    let cur_A := used_A ∪ (Finset.range K).biUnion (fun j => {(rects₀ j).u1, (rects₀ j).u2})
    let cur_B := used_B ∪ (Finset.range K).biUnion (fun j => {(rects₀ j).v1, (rects₀ j).v2})
    have hcur_A : cur_A.card ≤ 4 * utH0Max n := by
      have hb : ((Finset.range K).biUnion (fun j => {(rects₀ j).u1, (rects₀ j).u2})).card ≤ 2 * K := by
        calc
          _ ≤ ∑ _j ∈ Finset.range K, 2 :=
            Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
          _ = 2 * K := by simp [Nat.mul_comm]
      have hu := Finset.card_union_le used_A ((Finset.range K).biUnion (fun j => {(rects₀ j).u1, (rects₀ j).u2}))
      exact card_cur_le_four_mul (hu.trans (Nat.add_le_add_left hb _)) huA hK hh0_le
    have hcur_B : cur_B.card ≤ 4 * utH0Max n := by
      have hb : ((Finset.range K).biUnion (fun j => {(rects₀ j).v1, (rects₀ j).v2})).card ≤ 2 * K := by
        calc
          _ ≤ ∑ _j ∈ Finset.range K, 2 :=
            Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
          _ = 2 * K := by simp [Nat.mul_comm]
      have hu := Finset.card_union_le used_B ((Finset.range K).biUnion (fun j => {(rects₀ j).v1, (rects₀ j).v2}))
      exact card_cur_le_four_mul (hu.trans (Nat.add_le_add_left hb _)) huB hK hh0_le
    let rem_A := S_A \ cur_A
    let rem_B := S_B \ cur_B
    have hremA_ge : S_A.card - 4 * utH0Max n ≤ rem_A.card :=
      sub_four_mul_le_sdiff (Finset.card_le_card_sdiff_add_card (s := S_A) (t := cur_A)) hcur_A
    have hremB_ge : S_B.card - 4 * utH0Max n - M_B ≤ rem_B.card - M_B :=
      sub_four_mul_sub_le_sdiff (Finset.card_le_card_sdiff_add_card (s := S_B) (t := cur_B)) hcur_B
    obtain ⟨r_new, hu1_r, hu2_r, hv1_r, hv2_r, hndvd⟩ :=
      exists_incongruent_utRectData_of_product (p := p) (M_B := M_B) (B := B_span)
        (fun a ha => hodd_A a (Finset.mem_sdiff.mp ha).1)
        (fun b hb => hodd_B b (Finset.mem_sdiff.mp hb).1)
        (fun a ha b hb => horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
        (fun a ha b hb => hspan a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
        (fun r => (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans
          (hMB_flt p r hp_prime hp_le))
        (lt_of_lt_of_le hprod_gt (Nat.mul_le_mul hremA_ge hremB_ge))
    let rects : ℕ → UTRectData := fun j => if j = K then r_new else rects₀ j
    let A := A₀ ∪ A₀.image (fun a => (a + r_new.gap / 2) % h0)
    have hdisj_new : ∀ j < K, Disjoint (rects₀ j).support r_new.support := by
      intro j hj
      rw [Finset.disjoint_left]
      intro x hx0 hxn
      have hm0 := hmem₀ j hj
      have hx0_c : (x = (rects₀ j).u1 ∨ x = (rects₀ j).u2) ∨ (x = (rects₀ j).v1 ∨ x = (rects₀ j).v2) := by
        simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx0; tauto
      have hxn_c : (x = r_new.u1 ∨ x = r_new.u2) ∨ (x = r_new.v1 ∨ x = r_new.v2) := by
        simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hxn; tauto
      rcases hx0_c with h0_lo | h0_hi <;> rcases hxn_c with hn_lo | hn_hi
      · have hxc : x ∈ cur_A := Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, by simp [h0_lo]⟩)
        rcases hn_lo with rfl | rfl
        · exact (Finset.mem_sdiff.mp hu1_r).2 hxc
        · exact (Finset.mem_sdiff.mp hu2_r).2 hxc
      · have hxl : x ∈ S_A := by
          rcases h0_lo with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hm0.1).1; exact (Finset.mem_sdiff.mp hm0.2.1).1]
        have hxh : x ∈ S_B := by
          rcases hn_hi with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hv1_r).1; exact (Finset.mem_sdiff.mp hv2_r).1]
        exact Nat.lt_irrefl x (horder x hxl x hxh)
      · have hxl : x ∈ S_A := by
          rcases hn_lo with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hu1_r).1; exact (Finset.mem_sdiff.mp hu2_r).1]
        have hxh : x ∈ S_B := by
          rcases h0_hi with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hm0.2.2.1).1; exact (Finset.mem_sdiff.mp hm0.2.2.2).1]
        exact Nat.lt_irrefl x (horder x hxl x hxh)
      · have hxc : x ∈ cur_B := Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj, by simp [h0_hi]⟩)
        rcases hn_hi with rfl | rfl
        · exact (Finset.mem_sdiff.mp hv1_r).2 hxc
        · exact (Finset.mem_sdiff.mp hv2_r).2 hxc
    refine ⟨rects, A, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hjK | rfl
      · simpa [rects, ne_of_lt hjK] using hmem₀ j hjK
      · simp only [rects, ↓reduceIte]
        exact ⟨Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left hu1_r,
          Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left hu2_r,
          Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left hv1_r,
          Finset.sdiff_subset_sdiff Finset.Subset.rfl Finset.subset_union_left hv2_r⟩
    · intro j₁ hj₁ j₂ hj₂ hne
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj₁ with h1K | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj₂ with h2K | rfl
      · simpa [rects, ne_of_lt h1K, ne_of_lt h2K] using hdisj₀ j₁ h1K j₂ h2K hne
      · simpa [rects, ne_of_lt h1K] using hdisj_new j₁ h1K
      · simpa [rects, ne_of_lt h2K] using (hdisj_new j₂ h2K).symm
      · exact False.elim (hne rfl)
    · have hmod_K : ModAchievable h0 (fun j => (rects j).gap) (Finset.range K) A₀ := by
        rcases hach₀ with ⟨h1, h2, h3, h4⟩
        refine ⟨h1, h2, fun j hj => by simpa [rects, ne_of_lt (Finset.mem_range.mp hj)] using h3 j hj, ?_⟩
        intro r hr
        obtain ⟨T, hT, hsum⟩ := h4 r hr
        refine ⟨T, hT, ?_⟩
        have heq : (∑ j ∈ T, (rects j).gap) = ∑ j ∈ T, (rects₀ j).gap :=
          Finset.sum_congr rfl fun j hj => by simp [rects, ne_of_lt (Finset.mem_range.mp (hT hj))]
        rw [heq, hsum]
      have hrange_eq : Finset.range (K + 1) = insert K (Finset.range K) := by
        ext j; simp [le_iff_lt_or_eq, or_comm]
      have hins := modAchievable_insert hh0_pos hmod_K
        (by simp : K ∉ Finset.range K) (by simp [rects, r_new.hgap_even])
      rw [← hrange_eq] at hins
      simpa [rects, A] using hins
    · exact min_succ_le_of_min_le hcard₀ (hp_step _ hndvd)

/-- Extract `2 * (h0 - 1)` pairwise-disjoint diagonal `ModCover` `UTRectData`s from `ModBin 54`,
giving full modular half-gap coverage modulo `h0` on both `true` (main) and `false` (anti). -/
theorem ut_extract_diagonal_modcover
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n h0 : ℕ} (hn : 35735 ≤ n) (hh0_ge2 : 2 ≤ h0) (hh0_le : h0 ≤ utH0Max n) :
    let S_A := apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1
    let S_B := apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1
    ∃ modDiag : Bool → Fin (h0 - 1) → UTRectData,
      (∀ (b : Bool) (j : Fin (h0 - 1)),
        (modDiag b j).u1 ∈ S_A ∧ (modDiag b j).u2 ∈ S_A ∧
        (modDiag b j).v1 ∈ S_B ∧ (modDiag b j).v2 ∈ S_B) ∧
      (∀ (b₁ b₂ : Bool) (j₁ j₂ : Fin (h0 - 1)),
        (b₁, j₁) ≠ (b₂, j₂) → Disjoint (modDiag b₁ j₁).support (modDiag b₂ j₂).support) ∧
      (∀ (b : Bool) (r : ℕ), r < h0 →
        ∃ T : Finset (Fin (h0 - 1)), ((∑ j ∈ T, (modDiag b j).gap) / 2) % h0 = r) := by
  classical
  dsimp only
  obtain ⟨dT, hmemT, hdisjT, hcovT⟩ :=
    ut_extract_single_diag_modcover bmor imp mv rs lower sharp upper hn hh0_ge2 hh0_le ∅ ∅
      (by simp) (by simp)
  let used_A := Finset.univ.biUnion (fun j : Fin (h0 - 1) => {(dT j).u1, (dT j).u2})
  let used_B := Finset.univ.biUnion (fun j : Fin (h0 - 1) => {(dT j).v1, (dT j).v2})
  have huA : used_A.card ≤ 2 * (h0 - 1) := by
    calc
      used_A.card ≤ ∑ _j : Fin (h0 - 1), 2 :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
      _ = 2 * (h0 - 1) := by simp [Nat.mul_comm]
  have huB : used_B.card ≤ 2 * (h0 - 1) := by
    calc
      used_B.card ≤ ∑ _j : Fin (h0 - 1), 2 :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
      _ = 2 * (h0 - 1) := by simp [Nat.mul_comm]
  obtain ⟨dF, hmemF, hdisjF, hcovF⟩ :=
    ut_extract_single_diag_modcover bmor imp mv rs lower sharp upper hn hh0_ge2 hh0_le used_A used_B huA huB
  let modDiag : Bool → Fin (h0 - 1) → UTRectData := fun b => if b then dT else dF
  have hcross_disj : ∀ j₁ j₂ : Fin (h0 - 1), Disjoint (dT j₁).support (dF j₂).support := by
    intro j₁ j₂
    rw [Finset.disjoint_left]
    intro x hxT hxF
    have hmT := hmemT j₁
    have hmF := hmemF j₂
    have hAB_disj := Finset.disjoint_left.mp (UTZone.disjoint n (by decide : UTZone.modDiagLo ≠ UTZone.modDiagHi))
    have hxT_c : (x = (dT j₁).u1 ∨ x = (dT j₁).u2) ∨ (x = (dT j₁).v1 ∨ x = (dT j₁).v2) := by
      simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hxT; tauto
    have hxF_c : (x = (dF j₂).u1 ∨ x = (dF j₂).u2) ∨ (x = (dF j₂).v1 ∨ x = (dF j₂).v2) := by
      simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hxF; tauto
    rcases hxT_c with hT_lo | hT_hi <;> rcases hxF_c with hF_lo | hF_hi
    · have hxu : x ∈ used_A := Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _, by simp [hT_lo]⟩
      rcases hF_lo with rfl | rfl <;>
        [exact (Finset.mem_sdiff.mp hmF.1).2 hxu; exact (Finset.mem_sdiff.mp hmF.2.1).2 hxu]
    · have h1 : x ∈ UTZone.modDiagLo.finset n := by
        rcases hT_lo with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hmT.1).1; exact (Finset.mem_sdiff.mp hmT.2.1).1]
      have h2 : x ∈ UTZone.modDiagHi.finset n := by
        rcases hF_hi with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hmF.2.2.1).1; exact (Finset.mem_sdiff.mp hmF.2.2.2).1]
      exact hAB_disj h1 h2
    · have h1 : x ∈ UTZone.modDiagLo.finset n := by
        rcases hF_lo with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hmF.1).1; exact (Finset.mem_sdiff.mp hmF.2.1).1]
      have h2 : x ∈ UTZone.modDiagHi.finset n := by
        rcases hT_hi with rfl | rfl <;> [exact (Finset.mem_sdiff.mp hmT.2.2.1).1; exact (Finset.mem_sdiff.mp hmT.2.2.2).1]
      exact hAB_disj h1 h2
    · have hxu : x ∈ used_B := Finset.mem_biUnion.mpr ⟨j₁, Finset.mem_univ _, by simp [hT_hi]⟩
      rcases hF_hi with rfl | rfl <;>
        [exact (Finset.mem_sdiff.mp hmF.2.2.1).2 hxu; exact (Finset.mem_sdiff.mp hmF.2.2.2).2 hxu]
  refine ⟨modDiag, ?_, ?_, ?_⟩
  · intro b j
    cases b
    · obtain ⟨h1, h2, h3, h4⟩ := hmemF j
      exact ⟨(Finset.mem_sdiff.mp h1).1, (Finset.mem_sdiff.mp h2).1,
        (Finset.mem_sdiff.mp h3).1, (Finset.mem_sdiff.mp h4).1⟩
    · obtain ⟨h1, h2, h3, h4⟩ := hmemT j
      exact ⟨(Finset.mem_sdiff.mp h1).1, (Finset.mem_sdiff.mp h2).1,
        (Finset.mem_sdiff.mp h3).1, (Finset.mem_sdiff.mp h4).1⟩
  · intro b₁ b₂ j₁ j₂ hne
    cases b₁ <;> cases b₂
    · exact hdisjF j₁ j₂ (fun h => hne (Prod.ext rfl h))
    · exact (hcross_disj j₂ j₁).symm
    · exact hcross_disj j₁ j₂
    · exact hdisjT j₁ j₂ (fun h => hne (Prod.ext rfl h))
  · intro b r hr
    cases b
    · exact hcovF r hr
    · exact hcovT r hr

/-- Extract all `10` Doubling stages (`6 * n` ordinary pairs + `2` diagonal `UTRectData`s per stage). -/
theorem ut_extract_doubling
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    ∃ (dblOrd : Fin 10 → UTEdge n → Bool → ℕ) (dblDiag : Fin 10 → Bool → UTRectData),
      (∀ (k : Fin 10) (u : UTEdge n),
        dblOrd k u false ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
        dblOrd k u true ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1 ∧
        dblOrd k u false < dblOrd k u true ∧
        2 ∣ (dblOrd k u true - dblOrd k u false)) ∧
      (∀ (k : Fin 10) (b : Bool),
        (dblDiag k b).u1 ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
        (dblDiag k b).u2 ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
        (dblDiag k b).v1 ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1 ∧
        (dblDiag k b).v2 ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1) ∧
      (∀ (k : Fin 10) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
        (u₁, b₁) ≠ (u₂, b₂) → dblOrd k u₁ b₁ ≠ dblOrd k u₂ b₂) ∧
      (∀ k : Fin 10, Disjoint (dblDiag k true).support (dblDiag k false).support) ∧
      (∀ (k : Fin 10) (u : UTEdge n) (b₁ b₂ : Bool), dblOrd k u b₁ ∉ (dblDiag k b₂).support) := by
  classical
  have hper_k : ∀ k : Fin 10,
      ∃ (ord_k : UTEdge n → Bool → ℕ) (diag_k : Bool → UTRectData),
        (∀ u : UTEdge n,
          ord_k u false ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
          ord_k u true ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1 ∧
          ord_k u false < ord_k u true ∧
          2 ∣ (ord_k u true - ord_k u false)) ∧
        (∀ b : Bool,
          (diag_k b).u1 ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
          (diag_k b).u2 ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1 ∧
          (diag_k b).v1 ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1 ∧
          (diag_k b).v2 ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1) ∧
        (∀ (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
          (u₁, b₁) ≠ (u₂, b₂) → ord_k u₁ b₁ ≠ ord_k u₂ b₂) ∧
        Disjoint (diag_k true).support (diag_k false).support ∧
        (∀ (u : UTEdge n) (b₁ b₂ : Bool), ord_k u b₁ ∉ (diag_k b₂).support) := by
    intro k
    obtain ⟨hlo_card, hhi_card, hprod⟩ := ut_dbl_bin_supply bmor imp rs lower sharp upper hn k
    let S_lo := apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1
    let S_hi := apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1
    have hZ_lo : S_lo = (UTZone.dblLow k).finset n := rfl
    have hZ_hi : S_hi = (UTZone.dblHigh k).finset n := rfl
    have hodd_lo : ∀ a ∈ S_lo, Odd a := fun a ha => (UTZone.elem_props (UTZone.dblLow k) (hZ_lo ▸ ha)).2.1
    have hodd_hi : ∀ b ∈ S_hi, Odd b := fun b hb => (UTZone.elem_props (UTZone.dblHigh k) (hZ_hi ▸ hb)).2.1
    have horder : ∀ a ∈ S_lo, ∀ b ∈ S_hi, a < b := by
      intro a ha b hb
      have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
      have ha_le := (UTZone.elem_props (UTZone.dblLow k) (hZ_lo ▸ ha)).2.2.2.2.1
      have hb_gt := (UTZone.elem_props (UTZone.dblHigh k) (hZ_hi ▸ hb)).2.2.2.1
      have hfrac := (ut_dbl_frac_recurrence.1 k).2.1
      have h1 : ((UTZone.dblLow k).hiNat : ℝ) / 10000 = utDblLowFrac k + 1 / 1000 := by
        fin_cases k <;> norm_num [UTZone.hiNat, UTZone.dblLowNat, utDblLowFrac]
      have h2 : ((UTZone.dblHigh k).loNat : ℝ) / 10000 = utDblHighFrac k := by
        fin_cases k <;> norm_num [UTZone.loNat, UTZone.dblHighNat, utDblHighFrac]
      rw [h1] at ha_le; rw [h2] at hb_gt
      have hltR : (a : ℝ) < (b : ℝ) := by nlinarith
      exact_mod_cast hltR
    have hspan : ∀ a ∈ S_lo, ∀ b ∈ S_hi, b - a < ⌊utX n⌋₊ + 1 := by
      intro a ha b hb
      have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
      have hb_le := (UTZone.elem_props (UTZone.dblHigh k) (hZ_hi ▸ hb)).2.2.2.2.1
      have h9980 : ((UTZone.dblHigh k).hiNat : ℝ) ≤ 9980 := by exact_mod_cast (UTZone.dblHigh k).bounds.2.2.1
      have hab : a ≤ b := (horder a ha b hb).le
      have hltR : ((b - a : ℕ) : ℝ) < ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hab]; push_cast
        have hfl := Nat.lt_floor_add_one (utX n)
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        nlinarith
      exact_mod_cast hltR
    obtain ⟨rects, hrmem, hrdisj⟩ :=
      exists_many_utRectData_of_product hodd_lo hodd_hi horder hspan hlo_card hhi_card hprod 2 (by omega)
    let used_lo : Finset ℕ := {(rects 0).u1, (rects 0).u2, (rects 1).u1, (rects 1).u2}
    let used_hi : Finset ℕ := {(rects 0).v1, (rects 0).v2, (rects 1).v1, (rects 1).v2}
    have hulo : used_lo.card ≤ 4 := by
      dsimp [used_lo]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_le_two 1)) 1)
    have huhi : used_hi.card ≤ 4 := by
      dsimp [used_hi]
      exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right
        ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_le_two 1)) 1)
    have hrem_lo : 6 * n ≤ (S_lo \ used_lo).card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_lo) (t := used_lo)
      dsimp [S_lo] at *; omega
    have hrem_hi : 6 * n ≤ (S_hi \ used_hi).card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_hi) (t := used_hi)
      dsimp [S_hi] at *; omega
    obtain ⟨u_arr, v_arr, huv_p, huv_d⟩ := exists_disjoint_pairs_of_cards (6 * n)
      (fun a ha => hodd_lo a (Finset.mem_sdiff.mp ha).1)
      (fun b hb => hodd_hi b (Finset.mem_sdiff.mp hb).1)
      (fun a ha b hb => horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      hrem_lo hrem_hi
    let ord_k : UTEdge n → Bool → ℕ := fun u b =>
      if b then v_arr (utEdgeEquiv n u) else u_arr (utEdgeEquiv n u)
    let diag_k : Bool → UTRectData := fun b => if b then rects 0 else rects 1
    refine ⟨ord_k, diag_k, ?_, ?_, ?_, ?_, ?_⟩
    · intro u
      obtain ⟨hu_m, hv_m, hlt, hev⟩ := huv_p (utEdgeEquiv n u)
      exact ⟨(Finset.mem_sdiff.mp hu_m).1, (Finset.mem_sdiff.mp hv_m).1, hlt, hev⟩
    · intro b
      cases b <;> [exact hrmem 1; exact hrmem 0]
    · intro u₁ u₂ b₁ b₂ hne heq
      by_cases hu : u₁ = u₂
      · subst u₂
        cases b₁ <;> cases b₂
        · exact hne rfl
        · have hlt := (huv_p (utEdgeEquiv n u₁)).2.2.1; dsimp [ord_k] at heq; omega
        · have hlt := (huv_p (utEdgeEquiv n u₁)).2.2.1; dsimp [ord_k] at heq; omega
        · exact hne rfl
      · have hd := Finset.disjoint_left.mp (huv_d _ _ (fun h => hu ((utEdgeEquiv n).injective h)))
        have hm1 : ord_k u₁ b₁ ∈ ({u_arr (utEdgeEquiv n u₁), v_arr (utEdgeEquiv n u₁)} : Finset ℕ) := by
          cases b₁ <;> simp [ord_k]
        have hm2 : ord_k u₂ b₂ ∈ ({u_arr (utEdgeEquiv n u₂), v_arr (utEdgeEquiv n u₂)} : Finset ℕ) := by
          cases b₂ <;> simp [ord_k]
        exact hd hm1 (heq ▸ hm2)
    · exact hrdisj 0 1 (by decide)
    · intro u b₁ b₂ hx
      obtain ⟨hu_m, hv_m, _, _⟩ := huv_p (utEdgeEquiv n u)
      have hm0 := hrmem 0
      have hm1 := hrmem 1
      cases b₁ <;> cases b₂
      · simp only [ord_k, Bool.false_eq_true, ↓reduceIte, diag_k, UTRectData.support,
          Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · exact (Finset.mem_sdiff.mp hu_m).2 (by simp [used_lo, h])
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hm1.2.2.1))
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hm1.2.2.2))
        · exact (Finset.mem_sdiff.mp hu_m).2 (by simp [used_lo, h])
      · simp only [ord_k, Bool.false_eq_true, ↓reduceIte, diag_k, UTRectData.support,
          Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · exact (Finset.mem_sdiff.mp hu_m).2 (by simp [used_lo, h])
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hm0.2.2.1))
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hm0.2.2.2))
        · exact (Finset.mem_sdiff.mp hu_m).2 (by simp [used_lo, h])
      · simp only [ord_k, ↓reduceIte, Bool.false_eq_true, diag_k, UTRectData.support,
          Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hm1.1) _ (Finset.mem_sdiff.mp hv_m).1)
        · exact (Finset.mem_sdiff.mp hv_m).2 (by simp [used_hi, h])
        · exact (Finset.mem_sdiff.mp hv_m).2 (by simp [used_hi, h])
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hm1.2.1) _ (Finset.mem_sdiff.mp hv_m).1)
      · simp only [ord_k, ↓reduceIte, diag_k, UTRectData.support,
          Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hm0.1) _ (Finset.mem_sdiff.mp hv_m).1)
        · exact (Finset.mem_sdiff.mp hv_m).2 (by simp [used_hi, h])
        · exact (Finset.mem_sdiff.mp hv_m).2 (by simp [used_hi, h])
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hm0.2.1) _ (Finset.mem_sdiff.mp hv_m).1)
  choose dblOrd dblDiag h1 h2 h3 h4 h5 using hper_k
  exact ⟨dblOrd, dblDiag, h1, h2, h3, h4, h5⟩

/-- Extract `utWOrd n` ordinary `Wide` stages and `utWDiag n` pairs of sign-balanced diagonal
`Wide` `UTRectData`s across the `30` matched `(utWideLow, utWideHigh)` bin pairs. -/
theorem ut_extract_wide
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    ∃ (wideOrd : Fin (utWOrd n) → UTEdge n → Bool → ℕ)
      (wideDiag : Fin (utWDiag n) → Bool → UTRectData),
      (∀ (w : Fin (utWOrd n)) (u : UTEdge n),
        wideOrd w u false ∈ apInterval (utWideLowLo n (w.val % 30)) (utWideLowHi n (w.val % 30)) 2 1 ∧
        wideOrd w u true ∈ apInterval (utWideHighLo n (w.val % 30)) (utWideHighHi n (w.val % 30)) 2 1 ∧
        wideOrd w u false < wideOrd w u true ∧
        2 ∣ (wideOrd w u true - wideOrd w u false)) ∧
      (∀ (d : Fin (utWDiag n)) (b : Bool),
        (wideDiag d b).u1 ∈ apInterval (utWideLowLo n (d.val % 30)) (utWideLowHi n (d.val % 30)) 2 1 ∧
        (wideDiag d b).u2 ∈ apInterval (utWideLowLo n (d.val % 30)) (utWideLowHi n (d.val % 30)) 2 1 ∧
        (wideDiag d b).v1 ∈ apInterval (utWideHighLo n (d.val % 30)) (utWideHighHi n (d.val % 30)) 2 1 ∧
        (wideDiag d b).v2 ∈ apInterval (utWideHighLo n (d.val % 30)) (utWideHighHi n (d.val % 30)) 2 1) ∧
      (∀ (w₁ w₂ : Fin (utWOrd n)) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
        (w₁, u₁, b₁) ≠ (w₂, u₂, b₂) → wideOrd w₁ u₁ b₁ ≠ wideOrd w₂ u₂ b₂) ∧
      (∀ (d₁ d₂ : Fin (utWDiag n)) (b₁ b₂ : Bool),
        (d₁, b₁) ≠ (d₂, b₂) → Disjoint (wideDiag d₁ b₁).support (wideDiag d₂ b₂).support) ∧
      (∀ (w : Fin (utWOrd n)) (u : UTEdge n) (b₁ : Bool) (d : Fin (utWDiag n)) (b₂ : Bool),
        wideOrd w u b₁ ∉ (wideDiag d b₂).support) ∧
      |(∑ d : Fin (utWDiag n), (((wideDiag d true).u1 : ℝ) + ((wideDiag d true).gap : ℝ) / 2)) -
        (∑ d : Fin (utWDiag n), (((wideDiag d false).u1 : ℝ) + ((wideDiag d false).gap : ℝ) / 2))| ≤
        (2 / 1000 : ℝ) * utX n := by
  classical
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  let K_o := utWideOrdPerBin n
  let K_d := utWideDiagPerBin n
  have hper_bin : ∀ m : Fin 30,
      ∃ (ord_m : Fin K_o → UTEdge n → Bool → ℕ) (rects_m : Fin (2 * K_d) → UTRectData),
        (∀ (s : Fin K_o) (u : UTEdge n),
          ord_m s u false ∈ apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1 ∧
          ord_m s u true ∈ apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1 ∧
          ord_m s u false < ord_m s u true ∧
          2 ∣ (ord_m s u true - ord_m s u false)) ∧
        (∀ t : Fin (2 * K_d),
          (rects_m t).u1 ∈ apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1 ∧
          (rects_m t).u2 ∈ apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1 ∧
          (rects_m t).v1 ∈ apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1 ∧
          (rects_m t).v2 ∈ apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1) ∧
        (∀ (s₁ s₂ : Fin K_o) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
          (s₁, u₁, b₁) ≠ (s₂, u₂, b₂) → ord_m s₁ u₁ b₁ ≠ ord_m s₂ u₂ b₂) ∧
        (∀ t₁ t₂ : Fin (2 * K_d), t₁ ≠ t₂ → Disjoint (rects_m t₁).support (rects_m t₂).support) ∧
        (∀ (s : Fin K_o) (u : UTEdge n) (b : Bool) (t : Fin (2 * K_d)),
          ord_m s u b ∉ (rects_m t).support) := by
    intro m
    obtain ⟨hlo_c, hhi_c, hprod⟩ := ut_wide_bin_supply bmor imp rs lower sharp upper hn m.isLt
    let S_lo := apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1
    let S_hi := apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1
    have hZ_lo : S_lo = (UTZone.wideLow m).finset n := rfl
    have hZ_hi : S_hi = (UTZone.wideHigh m).finset n := rfl
    have hodd_lo : ∀ a ∈ S_lo, Odd a := fun a ha => (UTZone.elem_props (UTZone.wideLow m) (hZ_lo ▸ ha)).2.1
    have hodd_hi : ∀ b ∈ S_hi, Odd b := fun b hb => (UTZone.elem_props (UTZone.wideHigh m) (hZ_hi ▸ hb)).2.1
    have horder : ∀ a ∈ S_lo, ∀ b ∈ S_hi, a < b := by
      intro a ha b hb
      have ha_le := (UTZone.elem_props (UTZone.wideLow m) (hZ_lo ▸ ha)).2.2.2.2.1
      have hb_gt := (UTZone.elem_props (UTZone.wideHigh m) (hZ_hi ▸ hb)).2.2.2.1
      have hm_lt := m.isLt
      have h1 : ((UTZone.wideLow m).hiNat : ℝ) ≤ 640 := by dsimp [UTZone.hiNat]; exact_mod_cast (show 40 + 20 * (m.val + 1) ≤ 640 by omega)
      have h2 : (9380 : ℝ) ≤ ((UTZone.wideHigh m).loNat : ℝ) := by dsimp [UTZone.loNat]; exact_mod_cast (show 9380 ≤ 9380 + 20 * m.val by omega)
      have hltR : (a : ℝ) < (b : ℝ) := by nlinarith
      exact_mod_cast hltR
    have hspan : ∀ a ∈ S_lo, ∀ b ∈ S_hi, b - a < ⌊utX n⌋₊ + 1 := by
      intro a ha b hb
      have hb_le := (UTZone.elem_props (UTZone.wideHigh m) (hZ_hi ▸ hb)).2.2.2.2.1
      have h9980 : ((UTZone.wideHigh m).hiNat : ℝ) ≤ 9980 := by exact_mod_cast (UTZone.wideHigh m).bounds.2.2.1
      have hab : a ≤ b := (horder a ha b hb).le
      have hltR : ((b - a : ℕ) : ℝ) < ((⌊utX n⌋₊ + 1 : ℕ) : ℝ) := by
        rw [Nat.cast_sub hab]; push_cast
        have hfl := Nat.lt_floor_add_one (utX n)
        have ha_nn : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
        nlinarith
      exact_mod_cast hltR
    obtain ⟨rects_m, hrmem, hrdisj⟩ :=
      exists_many_utRectData_of_product hodd_lo hodd_hi horder hspan hlo_c hhi_c hprod
        (2 * K_d) (by dsimp [K_o, K_d]; omega)
    let used_lo := Finset.univ.biUnion (fun t : Fin (2 * K_d) => {(rects_m t).u1, (rects_m t).u2})
    let used_hi := Finset.univ.biUnion (fun t : Fin (2 * K_d) => {(rects_m t).v1, (rects_m t).v2})
    have hulo : used_lo.card ≤ 4 * K_d := by
      calc
        used_lo.card ≤ ∑ _t : Fin (2 * K_d), 2 :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
        _ = 4 * K_d := by simp; ring
    have huhi : used_hi.card ≤ 4 * K_d := by
      calc
        used_hi.card ≤ ∑ _t : Fin (2 * K_d), 2 :=
          Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_le_two)
        _ = 4 * K_d := by simp; ring
    have hrem_lo : 6 * n * K_o ≤ (S_lo \ used_lo).card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_lo) (t := used_lo)
      have hlt : 6 * n * K_o + 4 * K_d < S_lo.card := hlo_c
      omega
    have hrem_hi : 6 * n * K_o ≤ (S_hi \ used_hi).card := by
      have h := Finset.card_le_card_sdiff_add_card (s := S_hi) (t := used_hi)
      have hlt : 6 * n * K_o + 4 * K_d < S_hi.card := hhi_c
      omega
    obtain ⟨u_arr, v_arr, huv_p, huv_d⟩ := exists_disjoint_pairs_of_cards (6 * n * K_o)
      (fun a ha => hodd_lo a (Finset.mem_sdiff.mp ha).1)
      (fun b hb => hodd_hi b (Finset.mem_sdiff.mp hb).1)
      (fun a ha b hb => horder a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1)
      hrem_lo hrem_hi
    let flatIdx : Fin K_o × UTEdge n ≃ Fin (6 * n * K_o) :=
      (Equiv.prodComm _ _).trans ((Equiv.prodCongr (utEdgeEquiv n) (Equiv.refl _)).trans finProdFinEquiv)
    let ord_m : Fin K_o → UTEdge n → Bool → ℕ := fun s u b =>
      if b then v_arr (flatIdx (s, u)) else u_arr (flatIdx (s, u))
    refine ⟨ord_m, rects_m, ?_, hrmem, ?_, hrdisj, ?_⟩
    · intro s u
      obtain ⟨hu_m, hv_m, hlt, hev⟩ := huv_p (flatIdx (s, u))
      exact ⟨(Finset.mem_sdiff.mp hu_m).1, (Finset.mem_sdiff.mp hv_m).1, hlt, hev⟩
    · intro s₁ s₂ u₁ u₂ b₁ b₂ hne heq
      by_cases hsu : (s₁, u₁) = (s₂, u₂)
      · rcases Prod.mk.inj hsu with ⟨rfl, rfl⟩
        cases b₁ <;> cases b₂
        · exact hne rfl
        · have hlt := (huv_p (flatIdx (s₁, u₁))).2.2.1; dsimp [ord_m] at heq; omega
        · have hlt := (huv_p (flatIdx (s₁, u₁))).2.2.1; dsimp [ord_m] at heq; omega
        · exact hne rfl
      · have hd := Finset.disjoint_left.mp (huv_d _ _ (fun h => hsu (flatIdx.injective h)))
        have hm1 : ord_m s₁ u₁ b₁ ∈ ({u_arr (flatIdx (s₁, u₁)), v_arr (flatIdx (s₁, u₁))} : Finset ℕ) := by
          cases b₁ <;> simp [ord_m]
        have hm2 : ord_m s₂ u₂ b₂ ∈ ({u_arr (flatIdx (s₂, u₂)), v_arr (flatIdx (s₂, u₂))} : Finset ℕ) := by
          cases b₂ <;> simp [ord_m]
        exact hd hm1 (heq ▸ hm2)
    · intro s u b t hx
      obtain ⟨hu_m, hv_m, _, _⟩ := huv_p (flatIdx (s, u))
      have hmt := hrmem t
      simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx
      cases b
      · dsimp [ord_m] at hx
        rcases hx with h | h | h | h
        · exact (Finset.mem_sdiff.mp hu_m).2 (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simp [h]⟩)
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hmt.2.2.1))
        · exact Nat.lt_irrefl _ (horder _ (Finset.mem_sdiff.mp hu_m).1 _ (h ▸ hmt.2.2.2))
        · exact (Finset.mem_sdiff.mp hu_m).2 (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simp [h]⟩)
      · dsimp [ord_m] at hx
        rcases hx with h | h | h | h
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hmt.1) _ (Finset.mem_sdiff.mp hv_m).1)
        · exact (Finset.mem_sdiff.mp hv_m).2 (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simp [h]⟩)
        · exact (Finset.mem_sdiff.mp hv_m).2 (Finset.mem_biUnion.mpr ⟨t, Finset.mem_univ _, by simp [h]⟩)
        · exact Nat.lt_irrefl _ (horder _ (h ▸ hmt.2.1) _ (Finset.mem_sdiff.mp hv_m).1)
  choose ord_m rects_m hord_m hrects_m hord_m_inj hrects_m_disj hord_m_nmem using hper_bin
  have hko (w : Fin (utWOrd n)) : w.val / 30 < K_o := by
    have := w.isLt; change w.val / 30 < (utWOrd n + 29) / 30; omega
  have hkd0 (d : Fin (utWDiag n)) : 2 * (d.val / 30) < 2 * K_d := by
    have := d.isLt; change 2 * (d.val / 30) < 2 * ((utWDiag n + 29) / 30); omega
  have hkd1 (d : Fin (utWDiag n)) : 2 * (d.val / 30) + 1 < 2 * K_d := by
    have := d.isLt; change 2 * (d.val / 30) + 1 < 2 * ((utWDiag n + 29) / 30); omega
  let wideOrd : Fin (utWOrd n) → UTEdge n → Bool → ℕ := fun w u b =>
    ord_m ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩ ⟨w.val / 30, hko w⟩ u b
  let rawR0 : Fin (utWDiag n) → UTRectData := fun d =>
    rects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ ⟨2 * (d.val / 30), hkd0 d⟩
  let rawR1 : Fin (utWDiag n) → UTRectData := fun d =>
    rects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ ⟨2 * (d.val / 30) + 1, hkd1 d⟩
  have hraw_diff : ∀ d : Fin (utWDiag n),
      |(((rawR0 d).u1 : ℝ) + ((rawR0 d).gap : ℝ) / 2) -
        (((rawR1 d).u1 : ℝ) + ((rawR1 d).gap : ℝ) / 2)| ≤ (2 / 1000 : ℝ) * utX n := by
    intro d
    let m : Fin 30 := ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩
    have hm0 := hrects_m m ⟨2 * (d.val / 30), hkd0 d⟩
    have hm1 := hrects_m m ⟨2 * (d.val / 30) + 1, hkd1 d⟩
    have hu0 := UTZone.elem_props (UTZone.wideLow m) hm0.1
    have hv0 := UTZone.elem_props (UTZone.wideHigh m) hm0.2.2.1
    have hu1 := UTZone.elem_props (UTZone.wideLow m) hm1.1
    have hv1 := UTZone.elem_props (UTZone.wideHigh m) hm1.2.2.1
    have hg0 : ((rawR0 d).v1 : ℝ) = ((rawR0 d).u1 : ℝ) + ((rawR0 d).gap : ℝ) := by exact_mod_cast (rawR0 d).hv1
    have hg1 : ((rawR1 d).v1 : ℝ) = ((rawR1 d).u1 : ℝ) + ((rawR1 d).gap : ℝ) := by exact_mod_cast (rawR1 d).hv1
    have hlo_w : ((UTZone.wideLow m).hiNat : ℝ) / 10000 * utX n =
        ((UTZone.wideLow m).loNat : ℝ) / 10000 * utX n + (2 / 1000 : ℝ) * utX n := by
      dsimp [UTZone.loNat, UTZone.hiNat]; push_cast; ring
    have hhi_w : ((UTZone.wideHigh m).hiNat : ℝ) / 10000 * utX n =
        ((UTZone.wideHigh m).loNat : ℝ) / 10000 * utX n + (2 / 1000 : ℝ) * utX n := by
      dsimp [UTZone.loNat, UTZone.hiNat]; push_cast; ring
    have hu0_lo : ((UTZone.wideLow m).loNat : ℝ) / 10000 * utX n < ((rawR0 d).u1 : ℝ) := hu0.2.2.2.1
    have hu0_hi : ((rawR0 d).u1 : ℝ) ≤ ((UTZone.wideLow m).hiNat : ℝ) / 10000 * utX n := hu0.2.2.2.2.1
    have hv0_lo : ((UTZone.wideHigh m).loNat : ℝ) / 10000 * utX n < ((rawR0 d).v1 : ℝ) := hv0.2.2.2.1
    have hv0_hi : ((rawR0 d).v1 : ℝ) ≤ ((UTZone.wideHigh m).hiNat : ℝ) / 10000 * utX n := hv0.2.2.2.2.1
    have hu1_lo : ((UTZone.wideLow m).loNat : ℝ) / 10000 * utX n < ((rawR1 d).u1 : ℝ) := hu1.2.2.2.1
    have hu1_hi : ((rawR1 d).u1 : ℝ) ≤ ((UTZone.wideLow m).hiNat : ℝ) / 10000 * utX n := hu1.2.2.2.2.1
    have hv1_lo : ((UTZone.wideHigh m).loNat : ℝ) / 10000 * utX n < ((rawR1 d).v1 : ℝ) := hv1.2.2.2.1
    have hv1_hi : ((rawR1 d).v1 : ℝ) ≤ ((UTZone.wideHigh m).hiNat : ℝ) / 10000 * utX n := hv1.2.2.2.2.1
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨swap, hbal⟩ := greedy_sign_balance (by positivity : (0 : ℝ) ≤ (2 / 1000 : ℝ) * utX n)
    (fun d => ((rawR0 d).u1 : ℝ) + ((rawR0 d).gap : ℝ) / 2)
    (fun d => ((rawR1 d).u1 : ℝ) + ((rawR1 d).gap : ℝ) / 2) hraw_diff
  let wideDiag : Fin (utWDiag n) → Bool → UTRectData := fun d b =>
    if b then (if swap d then rawR1 d else rawR0 d)
    else (if swap d then rawR0 d else rawR1 d)
  have hzone_wide_ord : ∀ (w : Fin (utWOrd n)) (u : UTEdge n) (b : Bool),
      wideOrd w u b ∈ (if b then UTZone.wideHigh ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
        else UTZone.wideLow ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩).finset n := by
    intro w u b
    cases b
    · exact (hord_m _ _ u).1
    · exact (hord_m _ _ u).2.1
  refine ⟨wideOrd, wideDiag, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w u
    exact hord_m ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩ _ u
  · intro d b
    have hwd_eq : wideDiag d b = rawR0 d ∨ wideDiag d b = rawR1 d := by
      cases b <;> cases hsw : swap d <;> simp [wideDiag, hsw]
    rcases hwd_eq with h | h <;> rw [h]
    · exact hrects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ ⟨2 * (d.val / 30), hkd0 d⟩
    · exact hrects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ ⟨2 * (d.val / 30) + 1, hkd1 d⟩
  · intro w₁ w₂ u₁ u₂ b₁ b₂ hne heq
    by_cases hm_eq : w₁.val % 30 = w₂.val % 30
    · let m : Fin 30 := ⟨w₁.val % 30, Nat.mod_lt _ (by decide)⟩
      have hm2 : (⟨w₂.val % 30, Nat.mod_lt _ (by decide)⟩ : Fin 30) = m := Fin.ext hm_eq.symm
      dsimp [wideOrd] at heq
      rw [hm2] at heq
      apply hord_m_inj m _ _ u₁ u₂ b₁ b₂ _ heq
      intro hsub
      rcases Prod.mk.inj hsub with ⟨hs_eq, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hu_eq, hb_eq⟩
      have hdiv_eq : w₁.val / 30 = w₂.val / 30 := congrArg Fin.val hs_eq
      have hw_eq : w₁ = w₂ := Fin.ext (by omega)
      exact hne (by simp [hw_eq, hu_eq, hb_eq])
    · have hz1 := hzone_wide_ord w₁ u₁ b₁
      have hz2 := hzone_wide_ord w₂ u₂ b₂
      have hzne : (if b₁ then UTZone.wideHigh ⟨w₁.val % 30, Nat.mod_lt _ (by decide)⟩
          else UTZone.wideLow ⟨w₁.val % 30, Nat.mod_lt _ (by decide)⟩) ≠
          (if b₂ then UTZone.wideHigh ⟨w₂.val % 30, Nat.mod_lt _ (by decide)⟩
          else UTZone.wideLow ⟨w₂.val % 30, Nat.mod_lt _ (by decide)⟩) := by
        cases b₁ <;> cases b₂ <;> intro h
        · exact hm_eq (congrArg Fin.val (UTZone.wideLow.inj h))
        · cases h
        · cases h
        · exact hm_eq (congrArg Fin.val (UTZone.wideHigh.inj h))
      exact Finset.disjoint_left.mp (UTZone.disjoint n hzne) hz1 (heq ▸ hz2)
  · intro d₁ d₂ b₁ b₂ hne
    let slotOf (d : Fin (utWDiag n)) (b : Bool) : Fin (2 * K_d) :=
      if (if b then swap d else !swap d) then
        ⟨2 * (d.val / 30) + 1, hkd1 d⟩
      else
        ⟨2 * (d.val / 30), hkd0 d⟩
    have hslot_val : ∀ d b, (slotOf d b).val =
        if (if b then swap d else !swap d) then 2 * (d.val / 30) + 1 else 2 * (d.val / 30) := by
      intro d b; cases b <;> cases hsw : swap d <;> simp [slotOf, hsw]
    have hrect_eq : ∀ d b, wideDiag d b = rects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ (slotOf d b) := by
      intro d b; cases b <;> cases hsw : swap d <;> simp [wideDiag, slotOf, hsw, rawR0, rawR1]
    rw [hrect_eq d₁ b₁, hrect_eq d₂ b₂]
    by_cases hm_eq : d₁.val % 30 = d₂.val % 30
    · let m : Fin 30 := ⟨d₁.val % 30, Nat.mod_lt _ (by decide)⟩
      have hm2 : (⟨d₂.val % 30, Nat.mod_lt _ (by decide)⟩ : Fin 30) = m := Fin.ext hm_eq.symm
      rw [hm2]
      apply hrects_m_disj m
      intro hs_eq
      have hv_eq := congrArg Fin.val hs_eq
      rw [hslot_val, hslot_val] at hv_eq
      by_cases hd_eq : d₁ = d₂
      · subst d₂
        cases b₁ <;> cases b₂ <;> cases hsw : swap d₁ <;> simp_all
      · have hd_val_ne : d₁.val ≠ d₂.val := fun h => hd_eq (Fin.ext h)
        have hdiv_ne : d₁.val / 30 ≠ d₂.val / 30 := by omega
        split_ifs at hv_eq <;> omega
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      let m₁ : Fin 30 := ⟨d₁.val % 30, Nat.mod_lt _ (by decide)⟩
      let m₂ : Fin 30 := ⟨d₂.val % 30, Nat.mod_lt _ (by decide)⟩
      have hm1 := hrects_m m₁ (slotOf d₁ b₁)
      have hm2 := hrects_m m₂ (slotOf d₂ b₂)
      have hx1_z : x ∈ (UTZone.wideLow m₁).finset n ∨ x ∈ (UTZone.wideHigh m₁).finset n := by
        simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx1
        rcases hx1 with rfl | rfl | rfl | rfl
        · exact Or.inl hm1.1
        · exact Or.inr hm1.2.2.1
        · exact Or.inr hm1.2.2.2
        · exact Or.inl hm1.2.1
      have hx2_z : x ∈ (UTZone.wideLow m₂).finset n ∨ x ∈ (UTZone.wideHigh m₂).finset n := by
        simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx2
        rcases hx2 with rfl | rfl | rfl | rfl
        · exact Or.inl hm2.1
        · exact Or.inr hm2.2.2.1
        · exact Or.inr hm2.2.2.2
        · exact Or.inl hm2.2.1
      rcases hx1_z with h1 | h1 <;> rcases hx2_z with h2 | h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (fun h => hm_eq (congrArg Fin.val (UTZone.wideLow.inj h)))) h1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (by intro h; cases h)) h1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (by intro h; cases h)) h1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (fun h => hm_eq (congrArg Fin.val (UTZone.wideHigh.inj h)))) h1 h2
  · intro w u b₁ d b₂ hx
    let slot_d : Fin (2 * K_d) :=
      if (if b₂ then swap d else !swap d) then
        ⟨2 * (d.val / 30) + 1, hkd1 d⟩
      else
        ⟨2 * (d.val / 30), hkd0 d⟩
    have hrect_eq : wideDiag d b₂ = rects_m ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ slot_d := by
      cases b₂ <;> cases hsw : swap d <;> simp [wideDiag, slot_d, hsw, rawR0, rawR1]
    rw [hrect_eq] at hx
    by_cases hm_eq : w.val % 30 = d.val % 30
    · let m : Fin 30 := ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
      have hm_d : (⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ : Fin 30) = m := Fin.ext hm_eq.symm
      rw [hm_d] at hx
      exact hord_m_nmem m _ u b₁ slot_d hx
    · let m₁ : Fin 30 := ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
      let m₂ : Fin 30 := ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩
      have hz1 := hzone_wide_ord w u b₁
      have hmd := hrects_m m₂ slot_d
      have hz2 : wideOrd w u b₁ ∈ (UTZone.wideLow m₂).finset n ∨
          wideOrd w u b₁ ∈ (UTZone.wideHigh m₂).finset n := by
        simp only [UTRectData.support, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with h | h | h | h
        · exact Or.inl (h ▸ hmd.1)
        · exact Or.inr (h ▸ hmd.2.2.1)
        · exact Or.inr (h ▸ hmd.2.2.2)
        · exact Or.inl (h ▸ hmd.2.1)
      cases b₁ <;> rcases hz2 with h2 | h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (fun h => hm_eq (congrArg Fin.val (UTZone.wideLow.inj h)))) hz1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (by intro h; cases h)) hz1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (by intro h; cases h)) hz1 h2
      · exact Finset.disjoint_left.mp (UTZone.disjoint n (fun h => hm_eq (congrArg Fin.val (UTZone.wideHigh.inj h)))) hz1 h2
  · have htrue : (∑ d : Fin (utWDiag n), (((wideDiag d true).u1 : ℝ) + ((wideDiag d true).gap : ℝ) / 2)) =
        ∑ d : Fin (utWDiag n), if swap d then (((rawR1 d).u1 : ℝ) + ((rawR1 d).gap : ℝ) / 2)
        else (((rawR0 d).u1 : ℝ) + ((rawR0 d).gap : ℝ) / 2) := by
      apply Finset.sum_congr rfl; intro d _; cases hsw : swap d <;> simp [wideDiag, hsw]
    have hfalse : (∑ d : Fin (utWDiag n), (((wideDiag d false).u1 : ℝ) + ((wideDiag d false).gap : ℝ) / 2)) =
        ∑ d : Fin (utWDiag n), if swap d then (((rawR0 d).u1 : ℝ) + ((rawR0 d).gap : ℝ) / 2)
        else (((rawR1 d).u1 : ℝ) + ((rawR1 d).gap : ℝ) / 2) := by
      apply Finset.sum_congr rfl; intro d _; cases hsw : swap d <;> simp [wideDiag, hsw]
    rw [htrue, hfalse]
    exact hbal

/-! ## Section 3: Generic Reservoir `EvenIntervalGrid` Assembly -/

/-- Transfer an `EvenIntervalGrid` along an injective relabeling `f : α → β`. -/
theorem evenIntervalGrid_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {gapα : α → ℕ} {gapβ : β → ℕ} {A B : ℕ}
    (f : α → β) (hf : Function.Injective f)
    (hgap : ∀ x ∈ S, gapβ (f x) = gapα x)
    (hgrid : EvenIntervalGrid S gapα A B) :
    EvenIntervalGrid (S.image f) gapβ A B := by
  intro q hqA hqB hev
  obtain ⟨T, hTS, hsum⟩ := hgrid q hqA hqB hev
  refine ⟨T.image f, Finset.image_subset_image hTS, ?_⟩
  rw [Finset.sum_image (fun x _ y _ h => hf h)]
  exact (Finset.sum_congr rfl fun x hx => hgap x (hTS hx)).trans hsum

/-- Transfer a `CompleteStepGrid` along an injective relabeling `f : α → β`. -/
theorem completeStepGrid_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    {S : Finset α} {gapα : α → ℕ} {gapβ : β → ℕ} {g R : ℕ}
    (f : α → β) (hf : Function.Injective f)
    (hgap : ∀ x ∈ S, gapβ (f x) = gapα x)
    (hgrid : CompleteStepGrid S gapα g R) :
    CompleteStepGrid (S.image f) gapβ g R := by
  intro q hqR hdiv
  obtain ⟨T, hTS, hsum⟩ := hgrid q hqR hdiv
  refine ⟨T.image f, Finset.image_subset_image hTS, ?_⟩
  rw [Finset.sum_image (fun x _ y _ h => hf h)]
  exact (Finset.sum_congr rfl fun x hx => hgap x (hTS hx)).trans hsum

/-- Combine `CompleteStepGrid` (`S_g`), `ModCover` (`S_mod`), `10` Doubling elements (`dblIdx`),
and `Wide` (`S_wide`) into a single `EvenIntervalGrid` on `[R_mod, R_g + R_dbl + R_wide]`,
recording both the exact total-gap sum `R_mod + B_tot` and the span lower bound. -/
theorem ut_assemble_reservoir_grid {α : Type*} [DecidableEq α]
    {n h0 R_mod R_g : ℕ} (S_g S_mod S_wide : Finset α) (dblIdx : Fin 10 → α) (gap : α → ℕ)
    (hh0_pos : 0 < h0)
    (hdisj_gm : Disjoint S_g S_mod)
    (hdbl_inj : Function.Injective dblIdx)
    (hdbl_disj : ∀ k : Fin 10, dblIdx k ∉ S_g ∪ S_mod)
    (hwide_disj : Disjoint (S_g ∪ S_mod ∪ Finset.univ.image dblIdx) S_wide)
    (hstep : CompleteStepGrid S_g gap (2 * h0) R_g)
    (hg_sum : (∑ x ∈ S_g, gap x) = R_g)
    (hRg_even : 2 ∣ R_g)
    (hmod_even : ∀ x ∈ S_mod, 2 ∣ gap x)
    (hmod_sum : (∑ x ∈ S_mod, gap x) = R_mod)
    (hcover : ∀ r < h0, ∃ T ⊆ S_mod, ((∑ x ∈ T, gap x) / 2) % h0 = r)
    (hspan0 : (R_mod : ℝ) + (100 / 10000 : ℝ) * utX n ≤ (R_g : ℝ))
    (hdbl_props : ∀ k : Fin 10,
      2 ∣ gap (dblIdx k) ∧
      utDblHighLo n k - utDblLowHi n k ≤ (gap (dblIdx k) : ℝ) ∧
      (gap (dblIdx k) : ℝ) ≤ utDblHighHi n k - utDblLowLo n k)
    (hwide_props : ∀ w ∈ S_wide,
      2 ∣ gap w ∧
      (932 / 1000 : ℝ) * utX n ≤ (gap w : ℝ) ∧
      (gap w : ℝ) ≤ (994 / 1000 : ℝ) * utX n) :
    let B_tot := R_g + (∑ k : Fin 10, gap (dblIdx k)) + ∑ w ∈ S_wide, gap w
    EvenIntervalGrid (S_g ∪ S_mod ∪ Finset.univ.image dblIdx ∪ S_wide) gap R_mod B_tot ∧
    2 ∣ B_tot ∧ R_mod ≤ B_tot ∧
    R_mod + B_tot = (∑ x ∈ S_g ∪ S_mod ∪ Finset.univ.image dblIdx ∪ S_wide, gap x) ∧
    (1467 / 1000 + (932 / 1000 : ℝ) * (S_wide.card : ℝ)) * utX n ≤ (B_tot : ℝ) - (R_mod : ℝ) := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hRm_le_Rg : R_mod ≤ R_g := by
    have : (R_mod : ℝ) ≤ (R_g : ℝ) := by linarith
    exact_mod_cast this
  have hgrid0 : EvenIntervalGrid (S_g ∪ S_mod) gap R_mod R_g :=
    evenIntervalGrid_of_stepGrid_and_modCover S_g S_mod gap h0 R_mod R_g hh0_pos hdisj_gm
      hstep hmod_even hmod_sum.le hcover
  have hdbl_loop : ∀ m : ℕ, m ≤ 10 →
      let F_m := (Finset.univ : Finset (Fin 10)).filter (fun i => i.val < m)
      let B_m := R_g + ∑ i ∈ F_m, gap (dblIdx i)
      EvenIntervalGrid ((S_g ∪ S_mod) ∪ F_m.image dblIdx) gap R_mod B_m ∧
      2 ∣ B_m ∧ R_mod ≤ B_m ∧
      ((if hm10 : m < 10 then utDblSpanFrac ⟨m, hm10⟩ else (14670 / 10000 : ℝ)) * utX n ≤
        (B_m : ℝ) - (R_mod : ℝ)) := by
    intro m hm
    induction m with
    | zero =>
      have hF0 : (Finset.univ : Finset (Fin 10)).filter (fun i => i.val < 0) = ∅ := by ext i; simp
      dsimp only
      rw [hF0]
      simp only [Finset.image_empty, Finset.union_empty, Finset.sum_empty, add_zero]
      refine ⟨hgrid0, hRg_even, hRm_le_Rg, ?_⟩
      rw [dif_pos (by decide : 0 < 10)]
      have h0 : utDblSpanFrac ⟨0, by decide⟩ = 100 / 10000 := rfl
      rw [h0]
      linarith
    | succ m ih =>
      obtain ⟨hgrid_m, hBm_ev, hRm_le_Bm, hspan_m⟩ := ih (by omega)
      have hm_lt : m < 10 := by omega
      let k : Fin 10 := ⟨m, hm_lt⟩
      rw [dif_pos hm_lt] at hspan_m
      let F_m := (Finset.univ : Finset (Fin 10)).filter (fun i => i.val < m)
      let F_succ := (Finset.univ : Finset (Fin 10)).filter (fun i => i.val < m + 1)
      let B_m := R_g + ∑ i ∈ F_m, gap (dblIdx i)
      have hk_nmem_Fm : k ∉ F_m := by simp [F_m, k]
      have hF_ins : F_succ = insert k F_m := by
        ext i; simp only [F_succ, F_m, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert, k, Fin.ext_iff]
        omega
      have hk_nmem_S : dblIdx k ∉ (S_g ∪ S_mod) ∪ F_m.image dblIdx := by
        rw [Finset.mem_union, not_or]
        refine ⟨hdbl_disj k, ?_⟩
        rw [Finset.mem_image]
        rintro ⟨i, hi, heq⟩
        exact hk_nmem_Fm (hdbl_inj heq ▸ hi)
      have hjoin_R : (gap (dblIdx k) : ℝ) ≤ ((B_m - R_mod : ℕ) : ℝ) := by
        rw [Nat.cast_sub hRm_le_Bm]
        have hrec := (ut_dbl_frac_recurrence.1 k).2.2.2
        have hhi_lo : utDblHighHi n k - utDblLowLo n k =
            ((utDblHighFrac k + 1 / 1000) - utDblLowFrac k) * utX n := by
          dsimp [utDblHighHi, utDblLowLo]; ring
        have h1 : utDblHighHi n k - utDblLowLo n k ≤ utDblSpanFrac k * utX n := by
          rw [hhi_lo]; exact mul_le_mul_of_nonneg_right hrec hX_pos.le
        exact (hdbl_props k).2.2.trans (h1.trans hspan_m)
      have hjoin_N : gap (dblIdx k) ≤ B_m - R_mod + 2 := by
        have hle : gap (dblIdx k) ≤ B_m - R_mod := by exact_mod_cast hjoin_R
        omega
      have hins := evenIntervalGrid_insert ((S_g ∪ S_mod) ∪ F_m.image dblIdx) gap R_mod B_m
        (dblIdx k) hk_nmem_S hBm_ev hRm_le_Bm (hdbl_props k).1 hjoin_N hgrid_m
      have hunion_eq : (S_g ∪ S_mod) ∪ F_succ.image dblIdx =
          insert (dblIdx k) ((S_g ∪ S_mod) ∪ F_m.image dblIdx) := by
        rw [hF_ins, Finset.image_insert]
        ext x; simp [or_left_comm]
      have hB_succ_eq : R_g + (∑ i ∈ F_succ, gap (dblIdx i)) = B_m + gap (dblIdx k) := by
        rw [hF_ins, Finset.sum_insert hk_nmem_Fm]; dsimp [B_m]; omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hunion_eq, hB_succ_eq]; exact hins
      · rw [hB_succ_eq]; exact dvd_add hBm_ev (hdbl_props k).1
      · rw [hB_succ_eq]; omega
      · rw [hB_succ_eq, Nat.cast_add]
        have hgap_lo : (utDblHighFrac k - (utDblLowFrac k + 1 / 1000)) * utX n ≤ (gap (dblIdx k) : ℝ) := by
          have hlo : utDblHighLo n k - utDblLowHi n k =
              (utDblHighFrac k - (utDblLowFrac k + 1 / 1000)) * utX n := by
            dsimp [utDblHighLo, utDblLowHi]; ring
          rw [← hlo]; exact (hdbl_props k).2.1
        by_cases hm1 : m + 1 < 10
        · rw [dif_pos hm1]
          let k9 : Fin 9 := ⟨m, by omega⟩
          have hstep9 := ut_dbl_frac_recurrence.2.1 k9
          have hk_eq : (⟨m + 1, hm1⟩ : Fin 10) = k9.succ := rfl
          have hkc_eq : k = k9.castSucc := rfl
          rw [hk_eq, hstep9, ← hkc_eq, add_mul]
          linarith
        · rw [dif_neg hm1]
          have hm9 : m = 9 := by omega
          have hk9_eq : k = ⟨9, by decide⟩ := Fin.ext hm9
          have hspan9 : utDblSpanFrac ⟨9, by decide⟩ * utX n ≤ (B_m : ℝ) - (R_mod : ℝ) := by
            rw [← hk9_eq]; exact hspan_m
          have hstep_end := ut_dbl_frac_recurrence.2.2
          have hstep_mul := congrArg (· * utX n) hstep_end
          rw [add_mul] at hstep_mul
          rw [hk9_eq] at hgap_lo ⊢
          linarith
  obtain ⟨hgrid10, hB10_ev, hRm_le_B10, hspan10⟩ := hdbl_loop 10 le_rfl
  rw [dif_neg (by decide : ¬ (10 < 10))] at hspan10
  have hF10_eq : (Finset.univ : Finset (Fin 10)).filter (fun i => i.val < 10) = Finset.univ := by
    ext i; simp
  rw [hF10_eq] at hgrid10 hB10_ev hRm_le_B10 hspan10
  let B_10 := R_g + ∑ k : Fin 10, gap (dblIdx k)
  have hwide_join : ∀ w ∈ S_wide, 2 ∣ gap w ∧ gap w ≤ B_10 - R_mod + 2 := by
    intro w hw
    obtain ⟨hev, _, hub⟩ := hwide_props w hw
    have hle_R : (gap w : ℝ) ≤ ((B_10 - R_mod : ℕ) : ℝ) := by
      rw [Nat.cast_sub hRm_le_B10]; linarith
    have hle_N : gap w ≤ B_10 - R_mod := by exact_mod_cast hle_R
    exact ⟨hev, by omega⟩
  obtain ⟨hgrid_fin, hBfin_ev⟩ :=
    evenIntervalGrid_extend_finset ((S_g ∪ S_mod) ∪ Finset.univ.image dblIdx) S_wide gap R_mod B_10
      hB10_ev hRm_le_B10 hwide_disj hwide_join hgrid10
  have hd_dbl : Disjoint (S_g ∪ S_mod) (Finset.univ.image dblIdx) := by
    rw [Finset.disjoint_right]
    intro x hx
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
    exact hdbl_disj k
  have htot_sum : R_mod + (B_10 + ∑ w ∈ S_wide, gap w) =
      ∑ x ∈ S_g ∪ S_mod ∪ Finset.univ.image dblIdx ∪ S_wide, gap x := by
    rw [Finset.sum_union hwide_disj, Finset.sum_union hd_dbl, Finset.sum_union hdisj_gm,
      Finset.sum_image (fun i _ j _ h => hdbl_inj h), hg_sum, hmod_sum]
    dsimp [B_10]
    omega
  have hw_lo : (S_wide.card : ℝ) * ((932 / 1000 : ℝ) * utX n) ≤ ∑ w ∈ S_wide, (gap w : ℝ) := by
    calc
      (S_wide.card : ℝ) * ((932 / 1000 : ℝ) * utX n)
          = ∑ _w ∈ S_wide, (932 / 1000 : ℝ) * utX n := by simp [nsmul_eq_mul]
      _ ≤ ∑ w ∈ S_wide, (gap w : ℝ) := Finset.sum_le_sum fun w hw => (hwide_props w hw).2.1
  have hspan_fin : (1467 / 1000 + (932 / 1000 : ℝ) * (S_wide.card : ℝ)) * utX n ≤
      ((B_10 + ∑ w ∈ S_wide, gap w : ℕ) : ℝ) - (R_mod : ℝ) := by
    push_cast
    linarith [hspan10, hw_lo]
  exact ⟨hgrid_fin, hBfin_ev, by omega, htot_sum, hspan_fin⟩

/-! ## Section 4: Complete `UTRoleWitness` Assembly & Central-Mean Enclosure -/

/-- Sharp linear bound `(utLn n : ℝ) ≤ (11 / 35735) * n` across all `n ≥ 35,735`. -/
theorem ut_ln_le_linear_11
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    (utLn n : ℝ) ≤ (11 / 35735 : ℝ) * (n : ℝ) := by
  by_cases h11 : utLn n ≤ 11
  · have h1 : (utLn n : ℝ) ≤ 11 := by exact_mod_cast h11
    have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  · have h12 : 12 ≤ utLn n := by omega
    have h28 : 28 * utLn n ≤ utStepsMV n := by
      dsimp [utStepsMV]
      have hsub : 1 ≤ utLn n - 11 := by omega
      nlinarith
    have h28R : 28 * (utLn n : ℝ) ≤ (utStepsMV n : ℝ) := by exact_mod_cast h28
    obtain ⟨_, hcomb⟩ := ut_quadratic_step_bounds rs lower sharp upper hn
    linarith

private theorem list_map_sum_eq_fin_sum {α : Type*} (L : List α) (f : α → ℕ) :
    (L.map f).sum = ∑ i : Fin L.length, f (L.get i) := by
  induction L with
  | nil => simp
  | cons a as ih =>
    dsimp only [List.length_cons]
    rw [List.map_cons, List.sum_cons, ih, Fin.sum_univ_succ]
    rfl

private theorem list_pairwise_get {α : Type*} {R : α → α → Prop} (hR : ∀ x y, R x y → R y x) :
    ∀ {L : List α}, L.Pairwise R → ∀ (i j : Fin L.length), i ≠ j → R (L.get i) (L.get j)
  | [], _, i, _ => i.elim0
  | _ :: as, hp, i, j => by
    obtain ⟨ha, has⟩ := List.pairwise_cons.mp hp
    refine Fin.cases ?_ (fun i' => ?_) i
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro hij; exact (hij rfl).elim
      · intro _; exact ha _ (List.get_mem as j')
    · refine Fin.cases ?_ (fun j' => ?_) j
      · intro _; exact hR _ _ (ha _ (List.get_mem as i'))
      · intro hij
        exact list_pairwise_get hR has i' j' (fun heq => hij (congrArg Fin.succ heq))

/-- 4-phase stage index sum `(Growth, ModCover, Doubling, Wide)` for clean finite-sum and grid splitting. -/
inductive UTStageTag (G M W : ℕ) : Type
  | growth : Fin G → UTStageTag G M W
  | mod : Fin M → UTStageTag G M W
  | dbl : Fin 10 → UTStageTag G M W
  | wide : Fin W → UTStageTag G M W
  deriving DecidableEq

def utStageTagSumEquiv (G M W : ℕ) :
    UTStageTag G M W ≃ (((Fin G ⊕ Fin M) ⊕ Fin 10) ⊕ Fin W) where
  toFun
    | .growth g => Sum.inl (Sum.inl (Sum.inl g))
    | .mod j => Sum.inl (Sum.inl (Sum.inr j))
    | .dbl k => Sum.inl (Sum.inr k)
    | .wide w => Sum.inr w
  invFun
    | Sum.inl (Sum.inl (Sum.inl g)) => .growth g
    | Sum.inl (Sum.inl (Sum.inr j)) => .mod j
    | Sum.inl (Sum.inr k) => .dbl k
    | Sum.inr w => .wide w
  left_inv x := by cases x <;> rfl
  right_inv y := by rcases y with ((g | j) | k) | w <;> rfl

instance instFintypeUTStageTag (G M W : ℕ) : Fintype (UTStageTag G M W) :=
  Fintype.ofEquiv _ (utStageTagSumEquiv G M W).symm

def utStageTagEquiv (G M W : ℕ) : UTStageTag G M W ≃ Fin (G + M + 10 + W) :=
  (utStageTagSumEquiv G M W).trans
    ((Equiv.sumCongr (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 10))) (Equiv.refl (Fin W))).trans
      ((Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin W))).trans finSumFinEquiv))

theorem utStageTagEquiv_growth_val {G M W : ℕ} (g : Fin G) :
    (utStageTagEquiv G M W (.growth g)).val = g.val := by
  simp [utStageTagEquiv, utStageTagSumEquiv, finSumFinEquiv_apply_left]

theorem utStageTagEquiv_symm_of_lt {G M W : ℕ} {s : Fin (G + M + 10 + W)} (hs : s.val < G) :
    (utStageTagEquiv G M W).symm s = .growth ⟨s.val, hs⟩ := by
  apply (utStageTagEquiv G M W).injective
  rw [Equiv.apply_symm_apply]
  exact Fin.ext (utStageTagEquiv_growth_val (G := G) (M := M) (W := W) ⟨s.val, hs⟩).symm

theorem utStageTagEquiv_symm_not_growth_of_ge {G M W : ℕ} {s : Fin (G + M + 10 + W)}
    (hs : G ≤ s.val) (g : Fin G) :
    (utStageTagEquiv G M W).symm s ≠ .growth g := by
  intro h
  have hv := congrArg (fun x => (utStageTagEquiv G M W x).val) h
  rw [Equiv.apply_symm_apply, utStageTagEquiv_growth_val] at hv
  omega

theorem utStageTag_sum {G M W : ℕ} {β : Type*} [AddCommMonoid β] (f : UTStageTag G M W → β) :
    (∑ t : UTStageTag G M W, f t) =
      (∑ g : Fin G, f (.growth g)) + (∑ j : Fin M, f (.mod j)) +
      (∑ k : Fin 10, f (.dbl k)) + (∑ w : Fin W, f (.wide w)) := by
  rw [← Equiv.sum_comp (utStageTagSumEquiv G M W).symm]
  simp only [Fintype.sum_sum_type, utStageTagSumEquiv, Equiv.coe_fn_symm_mk]

theorem utStageTag_univ_eq (G M W : ℕ) :
    (Finset.univ.image (UTStageTag.growth (G := G) (M := M) (W := W))) ∪
      (Finset.univ.image UTStageTag.mod) ∪
      (Finset.univ.image UTStageTag.dbl) ∪
      (Finset.univ.image UTStageTag.wide) = Finset.univ := by
  ext t
  cases t <;> simp

/-- Half-split diagonal designation `decide (i.val < L_half)` on `Fin (2 * L_half)`. -/
def utDiagChoice (L_half : ℕ) (i : Fin (2 * L_half)) : Bool :=
  decide (i.val < L_half)

/-- Embedding `Fin L_half → Fin (2 * L_half)` for branch `b = true` (`[0, L_half)`)
and `b = false` (`[L_half, 2 * L_half)`). -/
def utDiagEmb (L_half : ℕ) (b : Bool) (q : Fin L_half) : Fin (2 * L_half) :=
  if b then ⟨q.val, by omega⟩ else ⟨L_half + q.val, by omega⟩

theorem utDiagEmb_injective (L_half : ℕ) (b : Bool) :
    Function.Injective (utDiagEmb L_half b) := by
  intro q₁ q₂ h
  have hv := congrArg Fin.val h
  cases b <;> dsimp [utDiagEmb] at hv <;> exact Fin.ext (by omega)

theorem utDiagChoice_filter_eq (L_half : ℕ) (b : Bool) :
    (Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = b) =
      Finset.univ.image (utDiagEmb L_half b) := by
  ext i
  cases b
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, utDiagChoice,
      decide_eq_false_iff_not, not_lt, Finset.mem_image, utDiagEmb, Bool.false_eq_true, ↓reduceIte,
      Fin.ext_iff]
    exact ⟨fun h => ⟨⟨i.val - L_half, by omega⟩, by dsimp; omega⟩,
      fun ⟨q, hq⟩ => by omega⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, utDiagChoice,
      decide_eq_true_eq, Finset.mem_image, utDiagEmb, ↓reduceIte, Fin.ext_iff]
    exact ⟨fun h => ⟨⟨i.val, h⟩, rfl⟩,
      fun ⟨q, hq⟩ => by rw [← hq]; exact q.isLt⟩

theorem utDiagChoice_card (L_half : ℕ) (b : Bool) :
    ((Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = b)).card =
      L_half := by
  rw [utDiagChoice_filter_eq, Finset.card_image_of_injective _ (utDiagEmb_injective L_half b),
    Finset.card_univ, Fintype.card_fin]

theorem utDiag_univ_sum {β : Type*} [AddCommMonoid β] (L_half : ℕ) (f : Fin (2 * L_half) → β) :
    (∑ i : Fin (2 * L_half), f i) =
      (∑ q : Fin L_half, f (utDiagEmb L_half true q)) +
      (∑ q : Fin L_half, f (utDiagEmb L_half false q)) := by
  have hdisj : Disjoint
      ((Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = true))
      ((Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = false)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    have e1 := (Finset.mem_filter.mp h1).2
    have e2 := (Finset.mem_filter.mp h2).2
    exact Bool.noConfusion (e1.symm.trans e2)
  have hunion :
      ((Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = true)) ∪
      ((Finset.univ : Finset (Fin (2 * L_half))).filter (fun i => utDiagChoice L_half i = false)) =
      Finset.univ := by
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    cases utDiagChoice L_half i <;> simp
  conv_lhs => rw [← hunion]
  rw [Finset.sum_union hdisj, utDiagChoice_filter_eq, utDiagChoice_filter_eq,
    Finset.sum_image (fun _ _ _ _ h => utDiagEmb_injective L_half true h),
    Finset.sum_image (fun _ _ _ _ h => utDiagEmb_injective L_half false h)]

/-- Complete upper-tail role witness (`n ≥ 35,735`), bundling all diagonal rectangles,
ordinary edge pairs, `EvenIntervalGrid` reservoirs on both diagonals and all `6 * n` edges,
global `pool n` injectivity, Keepout avoidance, and `[0.3566 * X, 0.5764 * X]` central-mean enclosure. -/
structure UTRoleWitness (n : ℕ) where
  G : ℕ
  h0 : ℕ
  S : ℕ
  L_half : ℕ
  L : ℕ
  hG_pos : 0 < G
  hh0_ge2 : 2 ≤ h0
  hh0_le : h0 ≤ utH0Max n
  hS_def : S = G + (h0 - 1) + 10 + utWOrd n
  hL_half_def : L_half = G + (h0 - 1) + 10 + utWDiag n
  hL_def : L = 2 * L_half
  hGS : G ≤ S
  hpack_ord : 4 * (12 * S + 4) + 8 < n
  hs : 2 * L + 1 ≤ n
  hL_ge3 : 3 ≤ L
  hres_quarter : 4 * (12 * n * S + 4 * L) ≤ n * n
  choice : Fin L → Bool
  hchoice_true_card : ((Finset.univ : Finset (Fin L)).filter (fun i => choice i = true)).card = L_half
  hchoice_false_card : ((Finset.univ : Finset (Fin L)).filter (fun i => choice i = false)).card = L_half
  diagRect : Fin L → UTRectData
  ordRaw : Fin S → UTEdge n → Bool → ℕ
  ordGap : Fin S → UTEdge n → ℕ
  hord_pair : ∀ (s : Fin S) (u : UTEdge n),
    ordRaw s u true = ordRaw s u false + ordGap s u ∧ 0 < ordGap s u ∧ 2 ∣ ordGap s u
  hordGap_growth : ∀ (s : Fin S), s.val < G → ∀ (u₁ u₂ : UTEdge n), ordGap s u₁ = ordGap s u₂
  hgrowth_mid_spread : ∀ (g : Fin G) (u₁ u₂ : UTEdge n),
    ((((ordRaw ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₂ false : ℝ) +
      (ordGap ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₂ : ℝ) / 2)) -
     (((ordRaw ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₁ false : ℝ) +
      (ordGap ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₁ : ℝ) / 2))) ≤ utMidWidth n
  ordNongrowthAnchor : Fin S → ℝ
  ordNongrowthHalfWidth : Fin S → ℝ
  hnongrowth_width_nn : ∀ s : Fin S, 0 ≤ ordNongrowthHalfWidth s
  hnongrowth_pair_bound : ∀ (s : Fin S), G ≤ s.val → ∀ (u : UTEdge n),
    |(((ordRaw s u false + ordRaw s u true : ℕ) : ℝ) - ordNongrowthAnchor s)| ≤
      ordNongrowthHalfWidth s
  hnongrowth_width_sum :
    (∑ s : Fin S, 6 * ordNongrowthHalfWidth s) ≤
      ((60 / 1000 : ℝ) + (72 / 10000 : ℝ) * (utH0Max n : ℝ) + (12 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n
  V_res : Finset ℕ
  hV_sub : ∀ v ∈ V_res, v ∈ pool n
  hV_card : V_res.card = 4 * L + 12 * n * S
  hV_keepout : ∀ v ∈ V_res, (v : ℝ) ≤ utKeepoutLo n ∨ utKeepoutHi n < (v : ℝ)
  hV_mean_lo :
    (∑ v ∈ V_res, ((v : ℝ) - (3566 / 10000 : ℝ) * utX n)) ≤
      (Lucas.poolTotal n : ℝ) - ((n * n : ℕ) : ℝ) * ((3566 / 10000 : ℝ) * utX n)
  hV_mean_hi :
    (∑ v ∈ V_res, ((5764 / 10000 : ℝ) * utX n - (v : ℝ))) ≤
      ((n * n : ℕ) : ℝ) * ((5764 / 10000 : ℝ) * utX n) - (Lucas.poolTotal n : ℝ)
  hdiag_mem : ∀ (t : Fin L) (c : Fin 4), (diagRect t).corners c ∈ V_res
  hord_mem : ∀ (s : Fin S) (u : UTEdge n) (b : Bool), ordRaw s u b ∈ V_res
  hdiag_inj : Function.Injective (fun x : Fin L × Fin 4 => (diagRect x.1).corners x.2)
  hord_inj : Function.Injective (fun y : Fin S × UTEdge n × Bool => ordRaw y.1 y.2.1 y.2.2)
  hdiag_ord_disj : ∀ (x : Fin L × Fin 4) (y : Fin S × UTEdge n × Bool),
    (diagRect x.1).corners x.2 ≠ ordRaw y.1 y.2.1 y.2.2
  hV_union :
    Finset.univ.image (fun x : Fin L × Fin 4 => (diagRect x.1).corners x.2) ∪
    Finset.univ.image (fun y : Fin S × UTEdge n × Bool => ordRaw y.1 y.2.1 y.2.2) = V_res
  Am : ℕ
  Rm : ℕ
  Aa : ℕ
  Ra : ℕ
  hm_grid : EvenIntervalGrid ((Finset.univ : Finset (Fin L)).filter (fun i => choice i = true))
    (fun i => (diagRect i).gap) Am Rm
  ha_grid : EvenIntervalGrid ((Finset.univ : Finset (Fin L)).filter (fun i => choice i = false))
    (fun i => (diagRect i).gap) Aa Ra
  hRm_even : 2 ∣ Rm
  hRa_even : 2 ∣ Ra
  hAm_le_Rm : Am ≤ Rm
  hAa_le_Ra : Aa ≤ Ra
  hm_tot : Am + Rm = ∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = true), (diagRect i).gap
  ha_tot : Aa + Ra = ∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = false), (diagRect i).gap
  hm_span : (1467 / 1000 + (932 / 1000 : ℝ) * (utWDiag n : ℝ)) * utX n ≤ (Rm : ℝ) - (Am : ℝ)
  ha_span : (1467 / 1000 + (932 / 1000 : ℝ) * (utWDiag n : ℝ)) * utX n ≤ (Ra : ℝ) - (Aa : ℝ)
  hdiag_mid_bal :
    |(∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = true),
        (((diagRect i).u1 : ℝ) + ((diagRect i).gap : ℝ) / 2)) -
     (∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = false),
        (((diagRect i).u1 : ℝ) + ((diagRect i).gap : ℝ) / 2))| ≤
      ((140 / 1000 : ℝ) + (6 / 10000 : ℝ) * (utH0Max n : ℝ)) * utX n
  edgeA : UTEdge n → ℕ
  edgeRadius : UTEdge n → ℕ
  hedge_grid : ∀ u : UTEdge n,
    EvenIntervalGrid (Finset.univ : Finset (Fin S)) (fun s => ordGap s u) (edgeA u) (edgeRadius u)
  hedge_even : ∀ u : UTEdge n, 2 ∣ edgeRadius u
  hedge_le : ∀ u : UTEdge n, edgeA u ≤ edgeRadius u
  hedge_tot : ∀ u : UTEdge n, edgeA u + edgeRadius u = ∑ s : Fin S, ordGap s u
  hedgeA_ub : ∀ u : UTEdge n, (edgeA u : ℝ) ≤ (12 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n
  hedge_span : ∀ u : UTEdge n,
    (1467 / 1000 + (932 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n ≤ (edgeRadius u : ℝ) - (edgeA u : ℝ)

/-- Stage-preserving Growth permutation of `ordRaw`, leaving all non-Growth stages, all gaps
`ordGap`, and `V_res` invariant. -/
def UTRoleWitness.ordPerm {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n))
    (s : Fin rw.S) (u : UTEdge n) (b : Bool) : ℕ :=
  if hs : s.val < rw.G then rw.ordRaw s (permG ⟨s.val, hs⟩ u) b
  else rw.ordRaw s u b

theorem UTRoleWitness.ordPerm_pair {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n)) (s : Fin rw.S) (u : UTEdge n) :
    rw.ordPerm permG s u true = rw.ordPerm permG s u false + rw.ordGap s u := by
  dsimp [UTRoleWitness.ordPerm]
  split_ifs with hs
  · rw [(rw.hord_pair s (permG ⟨s.val, hs⟩ u)).1, rw.hordGap_growth s hs _ u]
  · exact (rw.hord_pair s u).1

theorem UTRoleWitness.ordPerm_mem {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n)) (s : Fin rw.S) (u : UTEdge n) (b : Bool) :
    rw.ordPerm permG s u b ∈ rw.V_res := by
  dsimp [UTRoleWitness.ordPerm]
  split_ifs with hs
  · exact rw.hord_mem s _ b
  · exact rw.hord_mem s u b

theorem UTRoleWitness.ordPerm_inj {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n)) :
    Function.Injective (fun y : Fin rw.S × UTEdge n × Bool => rw.ordPerm permG y.1 y.2.1 y.2.2) := by
  intro ⟨s₁, u₁, b₁⟩ ⟨s₂, u₂, b₂⟩ heq
  dsimp [UTRoleWitness.ordPerm] at heq
  let u₁' : UTEdge n := if hs : s₁.val < rw.G then permG ⟨s₁.val, hs⟩ u₁ else u₁
  let u₂' : UTEdge n := if hs : s₂.val < rw.G then permG ⟨s₂.val, hs⟩ u₂ else u₂
  have heq' : (fun y : Fin rw.S × UTEdge n × Bool => rw.ordRaw y.1 y.2.1 y.2.2) (s₁, u₁', b₁) =
      (fun y : Fin rw.S × UTEdge n × Bool => rw.ordRaw y.1 y.2.1 y.2.2) (s₂, u₂', b₂) := by
    dsimp only [u₁', u₂']
    by_cases h1 : s₁.val < rw.G <;> by_cases h2 : s₂.val < rw.G <;>
      simp only [dif_pos, dif_neg, h1, h2, not_false_eq_true] at heq ⊢ <;> exact heq
  have hinj := rw.hord_inj heq'
  rcases Prod.mk.inj hinj with ⟨rfl, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hu_eq, rfl⟩
  dsimp [u₁', u₂'] at hu_eq
  by_cases hs : s₁.val < rw.G
  · rw [dif_pos hs, dif_pos hs] at hu_eq
    have hu : u₁ = u₂ := (permG ⟨s₁.val, hs⟩).injective hu_eq
    subst u₂; rfl
  · rw [dif_neg hs, dif_neg hs] at hu_eq
    subst u₂; rfl

theorem UTRoleWitness.diag_ordPerm_disj {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n))
    (x : Fin rw.L × Fin 4) (y : Fin rw.S × UTEdge n × Bool) :
    (rw.diagRect x.1).corners x.2 ≠ rw.ordPerm permG y.1 y.2.1 y.2.2 := by
  dsimp [UTRoleWitness.ordPerm]
  split_ifs with hs
  · exact rw.hdiag_ord_disj x (y.1, permG ⟨y.1.val, hs⟩ y.2.1, y.2.2)
  · exact rw.hdiag_ord_disj x y

theorem UTRoleWitness.ordPerm_union {n : ℕ} (rw : UTRoleWitness n)
    (permG : Fin rw.G → Equiv.Perm (UTEdge n)) :
    Finset.univ.image (fun x : Fin rw.L × Fin 4 => (rw.diagRect x.1).corners x.2) ∪
    Finset.univ.image (fun y : Fin rw.S × UTEdge n × Bool => rw.ordPerm permG y.1 y.2.1 y.2.2) =
      rw.V_res := by
  have himg_eq :
      Finset.univ.image (fun y : Fin rw.S × UTEdge n × Bool => rw.ordPerm permG y.1 y.2.1 y.2.2) =
      Finset.univ.image (fun y : Fin rw.S × UTEdge n × Bool => rw.ordRaw y.1 y.2.1 y.2.2) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨s, u, b⟩, rfl⟩
      dsimp [UTRoleWitness.ordPerm]
      split_ifs with hs
      · exact ⟨(s, permG ⟨s.val, hs⟩ u, b), rfl⟩
      · exact ⟨(s, u, b), rfl⟩
    · rintro ⟨⟨s, u, b⟩, rfl⟩
      by_cases hs : s.val < rw.G
      · refine ⟨(s, (permG ⟨s.val, hs⟩).symm u, b), ?_⟩
        simp [UTRoleWitness.ordPerm, hs]
      · refine ⟨(s, u, b), ?_⟩
        simp [UTRoleWitness.ordPerm, hs]
  rw [himg_eq, rw.hV_union]

private theorem ut_dbl_pair_bounds {n : ℕ} (k : Fin 10) {a b : ℕ}
    (ha : a ∈ apInterval (utDblLowLo n k) (utDblLowHi n k) 2 1)
    (hb : b ∈ apInterval (utDblHighLo n k) (utDblHighHi n k) 2 1) :
    utDblHighLo n k - utDblLowHi n k ≤ (b : ℝ) - (a : ℝ) ∧
    (b : ℝ) - (a : ℝ) ≤ utDblHighHi n k - utDblLowLo n k ∧
    |(((a + b : ℕ) : ℝ) - (utDblLowLo n k + utDblHighLo n k + (1 / 1000 : ℝ) * utX n))| ≤
      (1 / 1000 : ℝ) * utX n ∧
    (677 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧
    ((a + b : ℕ) : ℝ) ≤ (1776 / 1000 : ℝ) * utX n := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hza := UTZone.elem_props (UTZone.dblLow k) ha
  have hzb := UTZone.elem_props (UTZone.dblHigh k) hb
  have hlo1 : ((UTZone.dblLow k).loNat : ℝ) / 10000 * utX n = utDblLowLo n k := by
    fin_cases k <;> dsimp [UTZone.loNat, UTZone.dblLowNat, utDblLowLo, utDblLowFrac] <;> push_cast <;> ring
  have hhi1 : ((UTZone.dblLow k).hiNat : ℝ) / 10000 * utX n = utDblLowHi n k := by
    fin_cases k <;> dsimp [UTZone.hiNat, UTZone.dblLowNat, utDblLowHi, utDblLowFrac] <;> push_cast <;> ring
  have hlo2 : ((UTZone.dblHigh k).loNat : ℝ) / 10000 * utX n = utDblHighLo n k := by
    fin_cases k <;> dsimp [UTZone.loNat, UTZone.dblHighNat, utDblHighLo, utDblHighFrac] <;> push_cast <;> ring
  have hhi2 : ((UTZone.dblHigh k).hiNat : ℝ) / 10000 * utX n = utDblHighHi n k := by
    fin_cases k <;> dsimp [UTZone.hiNat, UTZone.dblHighNat, utDblHighHi, utDblHighFrac] <;> push_cast <;> ring
  have ha_gt : utDblLowLo n k < (a : ℝ) := hlo1 ▸ hza.2.2.2.1
  have ha_le : (a : ℝ) ≤ utDblLowHi n k := hhi1 ▸ hza.2.2.2.2.1
  have hb_gt : utDblHighLo n k < (b : ℝ) := hlo2 ▸ hzb.2.2.2.1
  have hb_le : (b : ℝ) ≤ utDblHighHi n k := hhi2 ▸ hzb.2.2.2.2.1
  have hw1 : utDblLowHi n k = utDblLowLo n k + (1 / 1000 : ℝ) * utX n := by
    dsimp [utDblLowHi, utDblLowLo]; ring
  have hw2 : utDblHighHi n k = utDblHighLo n k + (1 / 1000 : ℝ) * utX n := by
    dsimp [utDblHighHi, utDblHighLo]; ring
  have hsum_lo : (677 / 1000 : ℝ) ≤ utDblLowFrac k + utDblHighFrac k := by
    fin_cases k <;> norm_num [utDblLowFrac, utDblHighFrac]
  have hsum_hi : utDblLowFrac k + utDblHighFrac k + 2 / 1000 ≤ 1776 / 1000 := by
    fin_cases k <;> norm_num [utDblLowFrac, utDblHighFrac]
  have hfl : utDblLowLo n k + utDblHighLo n k = (utDblLowFrac k + utDblHighFrac k) * utX n := by
    dsimp [utDblLowLo, utDblHighLo]; ring
  push_cast
  refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · nlinarith
  · nlinarith

private theorem ut_wide_pair_bounds {n : ℕ} (m : Fin 30) {a b : ℕ}
    (ha : a ∈ apInterval (utWideLowLo n m.val) (utWideLowHi n m.val) 2 1)
    (hb : b ∈ apInterval (utWideHighLo n m.val) (utWideHighHi n m.val) 2 1) :
    (932 / 1000 : ℝ) * utX n ≤ (b : ℝ) - (a : ℝ) ∧
    (b : ℝ) - (a : ℝ) ≤ (994 / 1000 : ℝ) * utX n ∧
    |(((a + b : ℕ) : ℝ) - (utWideLowLo n m.val + utWideHighLo n m.val + (2 / 1000 : ℝ) * utX n))| ≤
      (2 / 1000 : ℝ) * utX n ∧
    (942 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧
    ((a + b : ℕ) : ℝ) ≤ (1062 / 1000 : ℝ) * utX n := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hza := UTZone.elem_props (UTZone.wideLow m) ha
  have hzb := UTZone.elem_props (UTZone.wideHigh m) hb
  have hm_nn : (0 : ℝ) ≤ (m.val : ℝ) := Nat.cast_nonneg _
  have hm_le : (m.val : ℝ) ≤ 29 := by exact_mod_cast (show m.val ≤ 29 by omega)
  have hlo1 : ((UTZone.wideLow m).loNat : ℝ) / 10000 * utX n = utWideLowLo n m.val := by
    dsimp [UTZone.loNat, utWideLowLo]; push_cast; ring
  have hhi1 : ((UTZone.wideLow m).hiNat : ℝ) / 10000 * utX n = utWideLowHi n m.val := by
    dsimp [UTZone.hiNat, utWideLowHi]; push_cast; ring
  have hlo2 : ((UTZone.wideHigh m).loNat : ℝ) / 10000 * utX n = utWideHighLo n m.val := by
    dsimp [UTZone.loNat, utWideHighLo]; push_cast; ring
  have hhi2 : ((UTZone.wideHigh m).hiNat : ℝ) / 10000 * utX n = utWideHighHi n m.val := by
    dsimp [UTZone.hiNat, utWideHighHi]; push_cast; ring
  have ha_gt : utWideLowLo n m.val < (a : ℝ) := hlo1 ▸ hza.2.2.2.1
  have ha_le : (a : ℝ) ≤ utWideLowHi n m.val := hhi1 ▸ hza.2.2.2.2.1
  have hb_gt : utWideHighLo n m.val < (b : ℝ) := hlo2 ▸ hzb.2.2.2.1
  have hb_le : (b : ℝ) ≤ utWideHighHi n m.val := hhi2 ▸ hzb.2.2.2.2.1
  have hw1 : utWideLowHi n m.val = utWideLowLo n m.val + (2 / 1000 : ℝ) * utX n := by
    dsimp [utWideLowHi, utWideLowLo]; ring
  have hw2 : utWideHighHi n m.val = utWideHighLo n m.val + (2 / 1000 : ℝ) * utX n := by
    dsimp [utWideHighHi, utWideHighLo]; ring
  have hbase_diff : utWideHighLo n m.val - utWideLowLo n m.val = (934 / 1000 : ℝ) * utX n := by
    dsimp [utWideHighLo, utWideLowLo]; ring
  have hbase_sum : utWideLowLo n m.val + utWideHighLo n m.val =
      (942 / 1000 + (4 / 1000 : ℝ) * (m.val : ℝ)) * utX n := by
    dsimp [utWideLowLo, utWideHighLo]; ring
  push_cast
  refine ⟨by linarith, by linarith, abs_le.mpr ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · nlinarith
  · nlinarith

private theorem ut_mod_ord_pair_bounds {n : ℕ} (m : Fin 54) {a b : ℕ}
    (ha : a ∈ apInterval (utModBinLo n m.val) (utModBinHi n m.val) 2 1)
    (hb : b ∈ apInterval (utModBinLo n m.val) (utModBinHi n m.val) 2 1) :
    (b : ℝ) - (a : ℝ) ≤ (12 / 10000 : ℝ) * utX n ∧
    |(((a + b : ℕ) : ℝ) - (utModBinLo n m.val + utModBinHi n m.val))| ≤
      (12 / 10000 : ℝ) * utX n ∧
    (1704 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧
    ((a + b : ℕ) : ℝ) ≤ (1836 / 1000 : ℝ) * utX n := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hza := UTZone.elem_props (UTZone.modOrd m) ha
  have hzb := UTZone.elem_props (UTZone.modOrd m) hb
  have hm_nn : (0 : ℝ) ≤ (m.val : ℝ) := Nat.cast_nonneg _
  have hm_le : (m.val : ℝ) ≤ 53 := by exact_mod_cast (show m.val ≤ 53 by omega)
  have hlo : ((UTZone.modOrd m).loNat : ℝ) / 10000 * utX n = utModBinLo n m.val := by
    dsimp [UTZone.loNat, utModBinLo]; push_cast; ring
  have hhi : ((UTZone.modOrd m).hiNat : ℝ) / 10000 * utX n = utModBinHi n m.val := by
    dsimp [UTZone.hiNat, utModBinHi]; push_cast; ring
  have ha_gt : utModBinLo n m.val < (a : ℝ) := hlo ▸ hza.2.2.2.1
  have ha_le : (a : ℝ) ≤ utModBinHi n m.val := hhi ▸ hza.2.2.2.2.1
  have hb_gt : utModBinLo n m.val < (b : ℝ) := hlo ▸ hzb.2.2.2.1
  have hb_le : (b : ℝ) ≤ utModBinHi n m.val := hhi ▸ hzb.2.2.2.2.1
  have hw : utModBinHi n m.val = utModBinLo n m.val + (12 / 10000 : ℝ) * utX n := by
    dsimp [utModBinHi, utModBinLo]; ring
  have hlo_ge : (852 / 1000 : ℝ) * utX n ≤ utModBinLo n m.val := by
    dsimp [utModBinLo]; nlinarith
  have hhi_le : utModBinHi n m.val ≤ (918 / 1000 : ℝ) * utX n := by
    dsimp [utModBinHi]; nlinarith
  push_cast
  exact ⟨by linarith, abs_le.mpr ⟨by linarith, by linarith⟩, by linarith, by linarith⟩

private theorem ut_mod_diag_pair_bounds {n a b : ℕ}
    (ha : a ∈ apInterval (utModBinLo n 54) (utModBinMid n 54) 2 1)
    (hb : b ∈ apInterval (utModBinMid n 54) (utModBinHi n 54) 2 1) :
    (b : ℝ) - (a : ℝ) ≤ (12 / 10000 : ℝ) * utX n ∧
    utModBinLo n 54 + (3 / 10000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) / 2 ∧
    ((a + b : ℕ) : ℝ) / 2 ≤ utModBinLo n 54 + (9 / 10000 : ℝ) * utX n ∧
    (1704 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧
    ((a + b : ℕ) : ℝ) ≤ (1836 / 1000 : ℝ) * utX n := by
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hza := UTZone.elem_props UTZone.modDiagLo ha
  have hzb := UTZone.elem_props UTZone.modDiagHi hb
  have ha_gt : (9168 / 10000 : ℝ) * utX n < (a : ℝ) := by dsimp [UTZone.loNat] at hza; exact hza.2.2.2.1
  have ha_le : (a : ℝ) ≤ (9174 / 10000 : ℝ) * utX n := by dsimp [UTZone.hiNat] at hza; exact hza.2.2.2.2.1
  have hb_gt : (9174 / 10000 : ℝ) * utX n < (b : ℝ) := by dsimp [UTZone.loNat] at hzb; exact hzb.2.2.2.1
  have hb_le : (b : ℝ) ≤ (9180 / 10000 : ℝ) * utX n := by dsimp [UTZone.hiNat] at hzb; exact hzb.2.2.2.2.1
  have h54 : utModBinLo n 54 = (9168 / 10000 : ℝ) * utX n := by
    dsimp [utModBinLo]; norm_num
  push_cast
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Assemble an `EvenIntervalGrid` on `Finset.univ : Finset (UTStageTag G M W)` directly from
a `UTGrowthWitness n` and phase-indexed gap bounds. -/
private theorem ut_assemble_tag_grid {n W : ℕ} (gw : UTGrowthWitness n)
    (gapF : UTStageTag gw.stages.length (gw.h0 - 1) W → ℕ)
    (hg_gap : ∀ g : Fin gw.stages.length, gapF (.growth g) = (gw.stages.get g).gap)
    (hmod_gap : ∀ j : Fin (gw.h0 - 1),
      2 ∣ gapF (.mod j) ∧ (gapF (.mod j) : ℝ) ≤ (12 / 10000 : ℝ) * utX n)
    (hmod_cov : ∀ r < gw.h0, ∃ T : Finset (Fin (gw.h0 - 1)),
      ((∑ j ∈ T, gapF (.mod j)) / 2) % gw.h0 = r)
    (hdbl_gap : ∀ k : Fin 10,
      2 ∣ gapF (.dbl k) ∧
      utDblHighLo n k - utDblLowHi n k ≤ (gapF (.dbl k) : ℝ) ∧
      (gapF (.dbl k) : ℝ) ≤ utDblHighHi n k - utDblLowLo n k)
    (hwide_gap : ∀ w : Fin W,
      2 ∣ gapF (.wide w) ∧
      (932 / 1000 : ℝ) * utX n ≤ (gapF (.wide w) : ℝ) ∧
      (gapF (.wide w) : ℝ) ≤ (994 / 1000 : ℝ) * utX n) :
    ∃ A B : ℕ,
      EvenIntervalGrid (Finset.univ : Finset (UTStageTag gw.stages.length (gw.h0 - 1) W)) gapF A B ∧
      2 ∣ B ∧ A ≤ B ∧
      A + B = (∑ t : UTStageTag gw.stages.length (gw.h0 - 1) W, gapF t) ∧
      (A : ℝ) ≤ (12 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n ∧
      (1467 / 1000 + (932 / 1000 : ℝ) * (W : ℝ)) * utX n ≤ (B : ℝ) - (A : ℝ) := by
  let G := gw.stages.length
  let M := gw.h0 - 1
  let S_g : Finset (UTStageTag G M W) := Finset.univ.image UTStageTag.growth
  let S_mod : Finset (UTStageTag G M W) := Finset.univ.image UTStageTag.mod
  let S_wide : Finset (UTStageTag G M W) := Finset.univ.image UTStageTag.wide
  let dblIdx : Fin 10 → UTStageTag G M W := UTStageTag.dbl
  have hg_inj : Function.Injective (UTStageTag.growth (G := G) (M := M) (W := W)) :=
    fun _ _ h => UTStageTag.growth.inj h
  have hm_inj : Function.Injective (UTStageTag.mod (G := G) (M := M) (W := W)) :=
    fun _ _ h => UTStageTag.mod.inj h
  have hd_inj : Function.Injective dblIdx := fun _ _ h => UTStageTag.dbl.inj h
  have hw_inj : Function.Injective (UTStageTag.wide (G := G) (M := M) (W := W)) :=
    fun _ _ h => UTStageTag.wide.inj h
  have hdisj_gm : Disjoint S_g S_mod := by
    rw [Finset.disjoint_left]; intro x hx1 hx2
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx1
    obtain ⟨_, _, h⟩ := Finset.mem_image.mp hx2
    cases h
  have hdbl_disj : ∀ k : Fin 10, dblIdx k ∉ S_g ∪ S_mod := by
    intro k hk
    rcases Finset.mem_union.mp hk with h1 | h2
    · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h1; cases h
    · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2; cases h
  have hwide_disj : Disjoint (S_g ∪ S_mod ∪ Finset.univ.image dblIdx) S_wide := by
    rw [Finset.disjoint_right]; intro x hx_w hx_l
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp hx_w
    rcases Finset.mem_union.mp hx_l with h12 | h3
    · rcases Finset.mem_union.mp h12 with h1 | h2
      · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h1; cases h
      · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h2; cases h
    · obtain ⟨_, _, h⟩ := Finset.mem_image.mp h3; cases h
  have hstep : CompleteStepGrid S_g gapF (2 * gw.h0) gw.R_last :=
    completeStepGrid_image UTStageTag.growth hg_inj (fun g _ => hg_gap g) gw.hgrid
  have hg_sum : (∑ x ∈ S_g, gapF x) = gw.R_last := by
    rw [Finset.sum_image (fun _ _ _ _ h => hg_inj h)]
    have h1 : (∑ g : Fin G, gapF (.growth g)) = ∑ g : Fin G, (gw.stages.get g).gap :=
      Finset.sum_congr rfl fun g _ => hg_gap g
    rw [h1, ← list_map_sum_eq_fin_sum, gw.hR_eq_sum]
  have hRg_even : 2 ∣ gw.R_last := by
    have h2g : 2 ∣ gw.g := by rw [gw.hg_eq]; exact dvd_mul_right 2 _
    exact dvd_trans h2g gw.hR_div
  let R_mod : ℕ := ∑ x ∈ S_mod, gapF x
  have hR_mod_ub1 : (R_mod : ℝ) ≤ ((gw.h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) := by
    dsimp [R_mod]
    rw [Finset.sum_image (fun _ _ _ _ h => hm_inj h), Nat.cast_sum]
    calc
      (∑ j : Fin M, (gapF (.mod j) : ℝ))
          ≤ ∑ _j : Fin M, (12 / 10000 : ℝ) * utX n :=
        Finset.sum_le_sum fun j _ => (hmod_gap j).2
      _ = ((gw.h0 - 1 : ℕ) : ℝ) * ((12 / 10000 : ℝ) * utX n) := by simp [M, nsmul_eq_mul]
  have hR_mod_ub2 : (R_mod : ℝ) ≤ (12 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n := by
    have hX_nn : 0 ≤ utX n := by dsimp [utX]; positivity
    have hh0_leR : ((gw.h0 - 1 : ℕ) : ℝ) ≤ (utH0Max n : ℝ) := by
      exact_mod_cast (show gw.h0 - 1 ≤ utH0Max n by have := gw.hh0_le; omega)
    nlinarith
  have hspan0 : (R_mod : ℝ) + (100 / 10000 : ℝ) * utX n ≤ (gw.R_last : ℝ) := by
    linarith [gw.hR_lower, hR_mod_ub1]
  have hmod_even : ∀ x ∈ S_mod, 2 ∣ gapF x := by
    intro x hx; obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx; exact (hmod_gap j).1
  have hcover : ∀ r < gw.h0, ∃ T ⊆ S_mod, ((∑ x ∈ T, gapF x) / 2) % gw.h0 = r := by
    intro r hr
    obtain ⟨T0, hT0⟩ := hmod_cov r hr
    refine ⟨T0.image UTStageTag.mod, Finset.image_subset_image (Finset.subset_univ _), ?_⟩
    rwa [Finset.sum_image (fun _ _ _ _ h => hm_inj h)]
  have hw_props : ∀ x ∈ S_wide,
      2 ∣ gapF x ∧ (932 / 1000 : ℝ) * utX n ≤ (gapF x : ℝ) ∧ (gapF x : ℝ) ≤ (994 / 1000 : ℝ) * utX n := by
    intro x hx; obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx; exact hwide_gap w
  obtain ⟨hgrid, hB_ev, hAB, htot, hspan⟩ :=
    ut_assemble_reservoir_grid (n := n) S_g S_mod S_wide dblIdx gapF gw.hh0_pos
      hdisj_gm hd_inj hdbl_disj hwide_disj hstep hg_sum hRg_even hmod_even rfl hcover
      hspan0 hdbl_gap hw_props
  have huniv : S_g ∪ S_mod ∪ Finset.univ.image dblIdx ∪ S_wide = Finset.univ :=
    utStageTag_univ_eq G M W
  have hw_card : S_wide.card = W := by
    dsimp [S_wide]
    rw [Finset.card_image_of_injective _ hw_inj, Finset.card_univ, Fintype.card_fin]
  rw [huniv] at hgrid htot
  rw [hw_card] at hspan
  exact ⟨R_mod, _, hgrid, hB_ev, hAB, htot, hR_mod_ub2, hspan⟩

/-- Construct the complete `UTRoleWitness n` for every `n ≥ 35,735` from the exempt published inputs. -/
theorem ut_role_witness
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports) (mv : MVBrunTitchmarsh)
    (rs : RSPrimeCountImports) (lower : RSIndexLower) (sharp : RSIndexLowerSharp) (upper : RSIndexUpper)
    {n : ℕ} (hn : 35735 ≤ n) :
    Nonempty (UTRoleWitness n) := by
  classical
  have hX_pos : 0 < utX n := by dsimp [utX]; exact_mod_cast (poolMaximum_prime n).pos
  have hcard_edge : Fintype.card (UTEdge n) = 6 * n := by
    rw [Fintype.card_congr (utEdgeEquiv n), Fintype.card_fin]
  obtain ⟨gw⟩ := ut_growth_witness bmor imp mv rs lower sharp upper hn
  let G := gw.stages.length
  let h0 := gw.h0
  let M := h0 - 1
  have hh0_ge2 : 2 ≤ h0 := by
    obtain ⟨k, hk⟩ := gw.hg6
    have hg := gw.hg_eq
    have hp := gw.hh0_pos
    omega
  have hh0_le : h0 ≤ utH0Max n := gw.hh0_le
  let S := G + M + 10 + utWOrd n
  let L_half := G + M + 10 + utWDiag n
  let L := 2 * L_half
  have hS_ub : S ≤ utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWOrd n := by
    have := gw.hlen_le; dsimp [S, G, M, h0]; omega
  have hL_ub : L ≤ 2 * (utSeedStages n + utStepsAP n + utStepsMV n + utStepsBoost n + utH0Max n + 10 + utWDiag n) := by
    have := gw.hlen_le; dsimp [L, L_half, G, M, h0]; omega
  obtain ⟨hpack_ord, hs, hres_quarter⟩ :=
    ut_packing_and_keepout_gates rs lower sharp upper hn hS_ub hL_ub
  have hGS : G ≤ S := by dsimp [S]; omega
  have hL_ge3 : 3 ≤ L := by dsimp [L, L_half]; omega
  -- Extract all 5 families
  obtain ⟨gOrd, gDiag, hgOrd_props, hgDiag_props, hgOrd_inj, hgDiag_disj, hgOrd_nmem, hgDiag_bal⟩ :=
    ut_split_growth_stages gw
  obtain ⟨mOrd, hmOrd_props, hmOrd_inj, hmOrd_cov⟩ :=
    ut_extract_ordinary_modcover bmor imp mv rs lower sharp upper hn hh0_ge2 hh0_le
  obtain ⟨mDiag, hmDiag_props, hmDiag_disj, hmDiag_cov⟩ :=
    ut_extract_diagonal_modcover bmor imp mv rs lower sharp upper hn hh0_ge2 hh0_le
  obtain ⟨dblOrd, dblDiag, hdblOrd_props, hdblDiag_props, hdblOrd_inj, hdblDiag_disj, hdblOrd_nmem⟩ :=
    ut_extract_doubling bmor imp rs lower sharp upper hn
  obtain ⟨wideOrd, wideDiag, hwideOrd_props, hwideDiag_props, hwideOrd_inj, hwideDiag_disj, hwideOrd_nmem, hwideDiag_bal⟩ :=
    ut_extract_wide bmor imp rs lower sharp upper hn
  -- Phase-tagged arrays
  let ordByTag : UTStageTag G M (utWOrd n) → UTEdge n → Bool → ℕ
    | .growth g, u, b => gOrd g u b
    | .mod j, u, b => mOrd j u b
    | .dbl k, u, b => dblOrd k u b
    | .wide w, u, b => wideOrd w u b
  let ordGapByTag : UTStageTag G M (utWOrd n) → UTEdge n → ℕ
    | .growth g, _ => (gw.stages.get g).gap
    | .mod j, u => mOrd j u true - mOrd j u false
    | .dbl k, u => dblOrd k u true - dblOrd k u false
    | .wide w, u => wideOrd w u true - wideOrd w u false
  let diagByTag (br : Bool) : UTStageTag G M (utWDiag n) → UTRectData
    | .growth g => gDiag g br
    | .mod j => mDiag br j
    | .dbl k => dblDiag k br
    | .wide d => wideDiag d br
  let tagOrd := utStageTagEquiv G M (utWOrd n)
  let tagDiag := utStageTagEquiv G M (utWDiag n)
  let choice : Fin L → Bool := utDiagChoice L_half
  let diagRect (i : Fin L) : UTRectData :=
    if hi : i.val < L_half then diagByTag true (tagDiag.symm ⟨i.val, hi⟩)
    else diagByTag false (tagDiag.symm ⟨i.val - L_half, by omega⟩)
  have hdiagRect_emb : ∀ (br : Bool) (q : Fin L_half),
      diagRect (utDiagEmb L_half br q) = diagByTag br (tagDiag.symm q) := by
    intro br q
    cases br
    · have hnot : ¬ ((utDiagEmb L_half false q).val < L_half) := by dsimp [utDiagEmb]; omega
      dsimp [diagRect]
      rw [dif_neg hnot]
      have hq : (⟨(utDiagEmb L_half false q).val - L_half, by dsimp [utDiagEmb]; omega⟩ : Fin L_half) = q := by
        ext; dsimp [utDiagEmb]; omega
      rw [hq]
    · have hlt : (utDiagEmb L_half true q).val < L_half := by dsimp [utDiagEmb]; exact q.isLt
      dsimp [diagRect]
      rw [dif_pos hlt]
      rfl
  let ordRaw (s : Fin S) (u : UTEdge n) (b : Bool) : ℕ := ordByTag (tagOrd.symm s) u b
  let ordGap (s : Fin S) (u : UTEdge n) : ℕ := ordGapByTag (tagOrd.symm s) u
  -- Pair & growth properties on `ordRaw` / `ordGap`
  have hordByTag_pair : ∀ (t : UTStageTag G M (utWOrd n)) (u : UTEdge n),
      ordByTag t u true = ordByTag t u false + ordGapByTag t u ∧
      0 < ordGapByTag t u ∧ 2 ∣ ordGapByTag t u := by
    intro t u
    cases t with
    | growth g =>
      have hp := gw.hstage_props (gw.stages.get g) (List.get_mem _ _)
      have h2g : 2 ∣ gw.g := by rw [gw.hg_eq]; exact dvd_mul_right 2 _
      exact ⟨(hgOrd_props g u).1, hp.1, dvd_trans h2g hp.2.1⟩
    | mod j =>
      obtain ⟨_, _, hlt, hev⟩ := hmOrd_props j u
      exact ⟨by dsimp [ordByTag, ordGapByTag]; omega, by dsimp [ordGapByTag]; omega, hev⟩
    | dbl k =>
      obtain ⟨_, _, hlt, hev⟩ := hdblOrd_props k u
      exact ⟨by dsimp [ordByTag, ordGapByTag]; omega, by dsimp [ordGapByTag]; omega, hev⟩
    | wide w =>
      obtain ⟨_, _, hlt, hev⟩ := hwideOrd_props w u
      exact ⟨by dsimp [ordByTag, ordGapByTag]; omega, by dsimp [ordGapByTag]; omega, hev⟩
  have hord_pair : ∀ (s : Fin S) (u : UTEdge n),
      ordRaw s u true = ordRaw s u false + ordGap s u ∧ 0 < ordGap s u ∧ 2 ∣ ordGap s u :=
    fun s u => hordByTag_pair (tagOrd.symm s) u
  have hordGap_growth : ∀ (s : Fin S), s.val < G → ∀ (u₁ u₂ : UTEdge n), ordGap s u₁ = ordGap s u₂ := by
    intro s hs_lt u₁ u₂
    dsimp [ordGap, tagOrd]
    rw [utStageTagEquiv_symm_of_lt hs_lt]
  have hgrowth_mid_spread : ∀ (g : Fin G) (u₁ u₂ : UTEdge n),
      ((((ordRaw ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₂ false : ℝ) +
        (ordGap ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₂ : ℝ) / 2)) -
       (((ordRaw ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₁ false : ℝ) +
        (ordGap ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ u₁ : ℝ) / 2))) ≤ utMidWidth n := by
    intro g u₁ u₂
    have hsymm : tagOrd.symm ⟨g.val, lt_of_lt_of_le g.isLt hGS⟩ = .growth g :=
      utStageTagEquiv_symm_of_lt g.isLt
    dsimp [ordRaw, ordGap]
    rw [hsymm]
    dsimp [ordByTag, ordGapByTag]
    have hnar := gw.hnarrow (gw.stages.get g) (List.get_mem _ _)
      (gOrd g u₂ false) (hgOrd_props g u₂).2.1 (gOrd g u₁ false) (hgOrd_props g u₁).2.1
    have h1 := (abs_le.mp hnar.le).2
    push_cast at h1
    linarith
  -- Non-growth ordinary pair-sum anchors
  let anchorByTag : UTStageTag G M (utWOrd n) → ℝ
    | .growth _ => 0
    | .mod j => utModBinLo n (j.val % 54) + utModBinHi n (j.val % 54)
    | .dbl k => utDblLowLo n k + utDblHighLo n k + (1 / 1000 : ℝ) * utX n
    | .wide w => utWideLowLo n (w.val % 30) + utWideHighLo n (w.val % 30) + (2 / 1000 : ℝ) * utX n
  let widthByTag : UTStageTag G M (utWOrd n) → ℝ
    | .growth _ => 0
    | .mod _ => (12 / 10000 : ℝ) * utX n
    | .dbl _ => (1 / 1000 : ℝ) * utX n
    | .wide _ => (2 / 1000 : ℝ) * utX n
  let ordNongrowthAnchor (s : Fin S) : ℝ := anchorByTag (tagOrd.symm s)
  let ordNongrowthHalfWidth (s : Fin S) : ℝ := widthByTag (tagOrd.symm s)
  have hnongrowth_width_nn : ∀ s : Fin S, 0 ≤ ordNongrowthHalfWidth s := by
    intro s; dsimp [ordNongrowthHalfWidth]
    cases tagOrd.symm s <;> dsimp [widthByTag] <;> positivity
  have hnongrowth_pair_bound : ∀ (s : Fin S), G ≤ s.val → ∀ (u : UTEdge n),
      |(((ordRaw s u false + ordRaw s u true : ℕ) : ℝ) - ordNongrowthAnchor s)| ≤
        ordNongrowthHalfWidth s := by
    intro s hs_ge u
    dsimp [ordRaw, ordNongrowthAnchor, ordNongrowthHalfWidth]
    cases ht : tagOrd.symm s with
    | growth g =>
      exact False.elim (utStageTagEquiv_symm_not_growth_of_ge hs_ge g ht)
    | mod j =>
      exact (ut_mod_ord_pair_bounds ⟨j.val % 54, Nat.mod_lt _ (by decide)⟩
        (hmOrd_props j u).1 (hmOrd_props j u).2.1).2.1
    | dbl k =>
      exact (ut_dbl_pair_bounds k (hdblOrd_props k u).1 (hdblOrd_props k u).2.1).2.2.1
    | wide w =>
      exact (ut_wide_pair_bounds ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
        (hwideOrd_props w u).1 (hwideOrd_props w u).2.1).2.2.1
  have hnongrowth_width_sum :
      (∑ s : Fin S, 6 * ordNongrowthHalfWidth s) ≤
        ((60 / 1000 : ℝ) + (72 / 10000 : ℝ) * (utH0Max n : ℝ) + (12 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n := by
    rw [← Equiv.sum_comp tagOrd]
    have hcongr : (∑ t : UTStageTag G M (utWOrd n), 6 * ordNongrowthHalfWidth (tagOrd t)) =
        ∑ t : UTStageTag G M (utWOrd n), 6 * widthByTag t :=
      Finset.sum_congr rfl fun t _ => by simp [ordNongrowthHalfWidth, tagOrd]
    rw [hcongr, utStageTag_sum]
    simp only [widthByTag, mul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hM_le : (M : ℝ) ≤ (utH0Max n : ℝ) := by
      exact_mod_cast (show M ≤ utH0Max n by dsimp [M]; omega)
    nlinarith
  -- Zone assignment and global injectivity
  let gZone (g : Fin G) : UTZone := if gw.isPool1 (gw.stages.get g) then .pool1 else .pool2
  have hgFoot_zone : ∀ (g : Fin G) {x : ℕ}, x ∈ (gw.stages.get g).footprint → x ∈ (gZone g).finset n := by
    intro g x hx
    have his := gw.hisPool1 (gw.stages.get g) (List.get_mem _ _)
    dsimp [gZone]
    cases h : gw.isPool1 (gw.stages.get g) <;> simp only [h, Bool.false_eq_true, ↓reduceIte] at his ⊢ <;>
      exact his hx
  let ordZone : UTStageTag G M (utWOrd n) → Bool → UTZone
    | .growth g, _ => gZone g
    | .mod j, _ => .modOrd ⟨j.val % 54, Nat.mod_lt _ (by decide)⟩
    | .dbl k, b => if b then .dblHigh k else .dblLow k
    | .wide w, b => if b then .wideHigh ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
        else .wideLow ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
  let diagZone : UTStageTag G M (utWDiag n) → Fin 4 → UTZone
    | .growth g, _ => gZone g
    | .mod _, c => if c = 0 ∨ c = 3 then .modDiagLo else .modDiagHi
    | .dbl k, c => if c = 0 ∨ c = 3 then .dblLow k else .dblHigh k
    | .wide d, c => if c = 0 ∨ c = 3 then .wideLow ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩
        else .wideHigh ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩
  have hord_zone : ∀ t u b, ordByTag t u b ∈ (ordZone t b).finset n := by
    intro t u b
    cases t with
    | growth g =>
      cases b
      · exact hgFoot_zone g (hgOrd_props g u).2.2.1
      · exact hgFoot_zone g (hgOrd_props g u).2.2.2
    | mod j =>
      cases b
      · exact (hmOrd_props j u).1
      · exact (hmOrd_props j u).2.1
    | dbl k =>
      cases b
      · exact (hdblOrd_props k u).1
      · exact (hdblOrd_props k u).2.1
    | wide w =>
      cases b
      · exact (hwideOrd_props w u).1
      · exact (hwideOrd_props w u).2.1
  have hdiag_zone : ∀ br t c, (diagByTag br t).corners c ∈ (diagZone t c).finset n := by
    intro br t c
    cases t with
    | growth g =>
      exact hgFoot_zone g ((hgDiag_props g br).2.2 ((gDiag g br).corners_mem_support c))
    | mod j =>
      have hm := hmDiag_props br j
      fin_cases c <;> dsimp [diagByTag, UTRectData.corners, diagZone]
      · exact hm.1
      · exact hm.2.2.1
      · exact hm.2.2.2
      · exact hm.2.1
    | dbl k =>
      have hm := hdblDiag_props k br
      fin_cases c <;> dsimp [diagByTag, UTRectData.corners, diagZone]
      · exact hm.1
      · exact hm.2.2.1
      · exact hm.2.2.2
      · exact hm.2.1
    | wide d =>
      have hm := hwideDiag_props d br
      fin_cases c <;> dsimp [diagByTag, UTRectData.corners, diagZone]
      · exact hm.1
      · exact hm.2.2.1
      · exact hm.2.2.2
      · exact hm.2.1
  let zoneFam : UTZone → ℕ
    | .pool1 | .pool2 => 0
    | .modOrd _ => 1
    | .modDiagLo | .modDiagHi => 2
    | .dblLow _ | .dblHigh _ => 3
    | .wideLow _ | .wideHigh _ => 4
  have hordZone_fam : ∀ t b, zoneFam (ordZone t b) =
      match t with | .growth _ => 0 | .mod _ => 1 | .dbl _ => 3 | .wide _ => 4 := by
    intro t b; cases t <;> cases b <;> dsimp [ordZone, gZone, zoneFam] <;> split_ifs <;> rfl
  have hdiagZone_fam : ∀ t c, zoneFam (diagZone t c) =
      match t with | .growth _ => 0 | .mod _ => 2 | .dbl _ => 3 | .wide _ => 4 := by
    intro t c; cases t <;> fin_cases c <;> dsimp [diagZone, gZone, zoneFam] <;> split_ifs <;> rfl
  have hzone_eq_of_mem : ∀ {z₁ z₂ : UTZone} {x : ℕ},
      x ∈ z₁.finset n → x ∈ z₂.finset n → z₁ = z₂ := by
    intro z₁ z₂ x h1 h2
    by_contra hne
    exact Finset.disjoint_left.mp (UTZone.disjoint n hne) h1 h2
  have hg_disj_idx : ∀ (g₁ g₂ : Fin G), g₁ ≠ g₂ →
      Disjoint (gw.stages.get g₁).footprint (gw.stages.get g₂).footprint :=
    list_pairwise_get (fun _ _ h => h.symm) gw.hdisjoint
  have hdiagByTag_inj : ∀ (br₁ br₂ : Bool) (t₁ t₂ : UTStageTag G M (utWDiag n)) (c₁ c₂ : Fin 4),
      (diagByTag br₁ t₁).corners c₁ = (diagByTag br₂ t₂).corners c₂ →
      br₁ = br₂ ∧ t₁ = t₂ ∧ c₁ = c₂ := by
    intro br₁ br₂ t₁ t₂ c₁ c₂ heq
    have hz_eq := hzone_eq_of_mem (hdiag_zone br₁ t₁ c₁) (heq ▸ hdiag_zone br₂ t₂ c₂)
    have hfam_eq : zoneFam (diagZone t₁ c₁) = zoneFam (diagZone t₂ c₂) := congrArg zoneFam hz_eq
    rw [hdiagZone_fam, hdiagZone_fam] at hfam_eq
    cases t₁ <;> cases t₂ <;> try (dsimp at hfam_eq; omega)
    case growth.growth g₁ g₂ =>
      by_cases hg : g₁ = g₂
      · subst g₂
        by_cases hbr : br₁ = br₂
        · subst br₂
          exact ⟨rfl, rfl, (gDiag g₁ br₁).hinj heq⟩
        · have hd : Disjoint (gDiag g₁ br₁).support (gDiag g₁ br₂).support := by
            cases br₁ <;> cases br₂
            · exact (hbr rfl).elim
            · exact (hgDiag_disj g₁).symm
            · exact hgDiag_disj g₁
            · exact (hbr rfl).elim
          exact False.elim (Finset.disjoint_left.mp hd
            ((gDiag g₁ br₁).corners_mem_support c₁) (heq ▸ (gDiag g₁ br₂).corners_mem_support c₂))
      · have hf1 := (hgDiag_props g₁ br₁).2.2 ((gDiag g₁ br₁).corners_mem_support c₁)
        have hf2 := (hgDiag_props g₂ br₂).2.2 ((gDiag g₂ br₂).corners_mem_support c₂)
        exact False.elim (Finset.disjoint_left.mp (hg_disj_idx g₁ g₂ hg) hf1 (heq ▸ hf2))
    case mod.mod j₁ j₂ =>
      by_cases hbj : (br₁, j₁) = (br₂, j₂)
      · rcases Prod.mk.inj hbj with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, (mDiag br₁ j₁).hinj heq⟩
      · exact False.elim (Finset.disjoint_left.mp (hmDiag_disj br₁ br₂ j₁ j₂ hbj)
          ((mDiag br₁ j₁).corners_mem_support c₁) (heq ▸ (mDiag br₂ j₂).corners_mem_support c₂))
    case dbl.dbl k₁ k₂ =>
      have hk_eq : k₁ = k₂ := by
        fin_cases c₁ <;> fin_cases c₂ <;> dsimp [diagZone] at hz_eq <;> cases hz_eq <;> rfl
      subst k₂
      by_cases hbr : br₁ = br₂
      · subst br₂
        exact ⟨rfl, rfl, (dblDiag k₁ br₁).hinj heq⟩
      · have hd : Disjoint (dblDiag k₁ br₁).support (dblDiag k₁ br₂).support := by
          cases br₁ <;> cases br₂
          · exact (hbr rfl).elim
          · exact (hdblDiag_disj k₁).symm
          · exact hdblDiag_disj k₁
          · exact (hbr rfl).elim
        exact False.elim (Finset.disjoint_left.mp hd
          ((dblDiag k₁ br₁).corners_mem_support c₁) (heq ▸ (dblDiag k₁ br₂).corners_mem_support c₂))
    case wide.wide d₁ d₂ =>
      by_cases hdb : (d₁, br₁) = (d₂, br₂)
      · rcases Prod.mk.inj hdb with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, (wideDiag d₁ br₁).hinj heq⟩
      · exact False.elim (Finset.disjoint_left.mp (hwideDiag_disj d₁ d₂ br₁ br₂ hdb)
          ((wideDiag d₁ br₁).corners_mem_support c₁) (heq ▸ (wideDiag d₂ br₂).corners_mem_support c₂))
  have hordByTag_inj : ∀ (t₁ t₂ : UTStageTag G M (utWOrd n)) (u₁ u₂ : UTEdge n) (b₁ b₂ : Bool),
      ordByTag t₁ u₁ b₁ = ordByTag t₂ u₂ b₂ →
      t₁ = t₂ ∧ u₁ = u₂ ∧ b₁ = b₂ := by
    intro t₁ t₂ u₁ u₂ b₁ b₂ heq
    have hz_eq := hzone_eq_of_mem (hord_zone t₁ u₁ b₁) (heq ▸ hord_zone t₂ u₂ b₂)
    have hfam_eq : zoneFam (ordZone t₁ b₁) = zoneFam (ordZone t₂ b₂) := congrArg zoneFam hz_eq
    rw [hordZone_fam, hordZone_fam] at hfam_eq
    cases t₁ <;> cases t₂ <;> try (dsimp at hfam_eq; omega)
    case growth.growth g₁ g₂ =>
      by_cases hg : g₁ = g₂
      · subst g₂
        by_cases hub : (u₁, b₁) = (u₂, b₂)
        · rcases Prod.mk.inj hub with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl⟩
        · exact False.elim (hgOrd_inj g₁ u₁ u₂ b₁ b₂ hub heq)
      · have hf1 : gOrd g₁ u₁ b₁ ∈ (gw.stages.get g₁).footprint := by
          cases b₁ <;> [exact (hgOrd_props g₁ u₁).2.2.1; exact (hgOrd_props g₁ u₁).2.2.2]
        have hf2 : gOrd g₂ u₂ b₂ ∈ (gw.stages.get g₂).footprint := by
          cases b₂ <;> [exact (hgOrd_props g₂ u₂).2.2.1; exact (hgOrd_props g₂ u₂).2.2.2]
        dsimp [ordByTag] at heq
        rw [heq] at hf1
        exact False.elim (Finset.disjoint_left.mp (hg_disj_idx g₁ g₂ hg) hf1 hf2)
    case mod.mod j₁ j₂ =>
      by_cases hjub : (j₁, u₁, b₁) = (j₂, u₂, b₂)
      · rcases Prod.mk.inj hjub with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · exact False.elim (hmOrd_inj j₁ j₂ u₁ u₂ b₁ b₂ hjub heq)
    case dbl.dbl k₁ k₂ =>
      have hk_eq : k₁ = k₂ := by
        cases b₁ <;> cases b₂ <;> dsimp [ordZone] at hz_eq <;> cases hz_eq <;> rfl
      subst k₂
      by_cases hub : (u₁, b₁) = (u₂, b₂)
      · rcases Prod.mk.inj hub with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · exact False.elim (hdblOrd_inj k₁ u₁ u₂ b₁ b₂ hub heq)
    case wide.wide w₁ w₂ =>
      by_cases hwub : (w₁, u₁, b₁) = (w₂, u₂, b₂)
      · rcases Prod.mk.inj hwub with ⟨rfl, hrest⟩
        rcases Prod.mk.inj hrest with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl⟩
      · exact False.elim (hwideOrd_inj w₁ w₂ u₁ u₂ b₁ b₂ hwub heq)
  have hdiag_ord_tag_disj : ∀ (br : Bool) (td : UTStageTag G M (utWDiag n)) (c : Fin 4)
      (to_ : UTStageTag G M (utWOrd n)) (u : UTEdge n) (b : Bool),
      (diagByTag br td).corners c ≠ ordByTag to_ u b := by
    intro br td c to_ u b heq
    have hz_eq := hzone_eq_of_mem (hdiag_zone br td c) (heq ▸ hord_zone to_ u b)
    have hfam_eq : zoneFam (diagZone td c) = zoneFam (ordZone to_ b) := congrArg zoneFam hz_eq
    rw [hdiagZone_fam, hordZone_fam] at hfam_eq
    cases td <;> cases to_ <;> try (dsimp at hfam_eq; omega)
    case growth.growth g₁ g₂ =>
      by_cases hg : g₁ = g₂
      · subst g₂
        have hm : (gDiag g₁ br).corners c ∈ (gDiag g₁ br).support := (gDiag g₁ br).corners_mem_support c
        rw [heq] at hm
        exact hgOrd_nmem g₁ u b br hm
      · have hf1 := (hgDiag_props g₁ br).2.2 ((gDiag g₁ br).corners_mem_support c)
        have hf2 : gOrd g₂ u b ∈ (gw.stages.get g₂).footprint := by
          cases b <;> [exact (hgOrd_props g₂ u).2.2.1; exact (hgOrd_props g₂ u).2.2.2]
        dsimp [diagByTag, ordByTag] at heq
        rw [← heq] at hf2
        exact Finset.disjoint_left.mp (hg_disj_idx g₁ g₂ hg) hf1 hf2
    case dbl.dbl k₁ k₂ =>
      have hk_eq : k₁ = k₂ := by
        fin_cases c <;> cases b <;> dsimp [diagZone, ordZone] at hz_eq <;> cases hz_eq <;> rfl
      subst k₂
      have hm : (dblDiag k₁ br).corners c ∈ (dblDiag k₁ br).support := (dblDiag k₁ br).corners_mem_support c
      rw [heq] at hm
      exact hdblOrd_nmem k₁ u b br hm
    case wide.wide d w =>
      have hm : (wideDiag d br).corners c ∈ (wideDiag d br).support := (wideDiag d br).corners_mem_support c
      rw [heq] at hm
      exact hwideOrd_nmem w u b d br hm
  -- Lift injectivity & disjointness to `diagRect` (`Fin L × Fin 4`) and `ordRaw` (`Fin S × UTEdge n × Bool`)
  have hdiagRect_decomp : ∀ i : Fin L,
      ∃ (br : Bool) (q : Fin L_half), i = utDiagEmb L_half br q := by
    intro i
    by_cases hi : i.val < L_half
    · exact ⟨true, ⟨i.val, hi⟩, rfl⟩
    · exact ⟨false, ⟨i.val - L_half, by omega⟩, Fin.ext (by dsimp [utDiagEmb]; omega)⟩
  have hdiag_inj : Function.Injective (fun x : Fin L × Fin 4 => (diagRect x.1).corners x.2) := by
    rintro ⟨i₁, c₁⟩ ⟨i₂, c₂⟩ heq
    dsimp only at heq
    obtain ⟨br₁, q₁, rfl⟩ := hdiagRect_decomp i₁
    obtain ⟨br₂, q₂, rfl⟩ := hdiagRect_decomp i₂
    rw [hdiagRect_emb, hdiagRect_emb] at heq
    obtain ⟨rfl, ht_eq, rfl⟩ := hdiagByTag_inj br₁ br₂ _ _ c₁ c₂ heq
    have hq_eq := tagDiag.symm.injective ht_eq
    subst q₂; rfl
  have hord_inj : Function.Injective (fun y : Fin S × UTEdge n × Bool => ordRaw y.1 y.2.1 y.2.2) := by
    rintro ⟨s₁, u₁, b₁⟩ ⟨s₂, u₂, b₂⟩ heq
    dsimp only at heq
    obtain ⟨ht_eq, rfl, rfl⟩ := hordByTag_inj _ _ u₁ u₂ b₁ b₂ heq
    have hs_eq := tagOrd.symm.injective ht_eq
    subst s₂; rfl
  have hdiag_ord_disj : ∀ (x : Fin L × Fin 4) (y : Fin S × UTEdge n × Bool),
      (diagRect x.1).corners x.2 ≠ ordRaw y.1 y.2.1 y.2.2 := by
    rintro ⟨i, c⟩ ⟨s, u, b⟩
    obtain ⟨br, q, rfl⟩ := hdiagRect_decomp i
    rw [hdiagRect_emb]
    exact hdiag_ord_tag_disj br (tagDiag.symm q) c (tagOrd.symm s) u b
  -- Define `V_res` and prove cardinality, pool membership, Keepout avoidance
  let img_diag := Finset.univ.image (fun x : Fin L × Fin 4 => (diagRect x.1).corners x.2)
  let img_ord := Finset.univ.image (fun y : Fin S × UTEdge n × Bool => ordRaw y.1 y.2.1 y.2.2)
  let V_res := img_diag ∪ img_ord
  have himg_disj : Disjoint img_diag img_ord := by
    rw [Finset.disjoint_left]
    intro v hv1 hv2
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hv1
    obtain ⟨y, _, heq⟩ := Finset.mem_image.mp hv2
    exact hdiag_ord_disj x y heq.symm
  have hV_card : V_res.card = 4 * L + 12 * n * S := by
    dsimp [V_res]
    rw [Finset.card_union_of_disjoint himg_disj]
    have hc1 : img_diag.card = 4 * L := by
      dsimp [img_diag]
      rw [Finset.card_image_of_injective _ hdiag_inj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Fintype.card_fin]
      ring
    have hc2 : img_ord.card = 12 * n * S := by
      dsimp [img_ord]
      rw [Finset.card_image_of_injective _ hord_inj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_prod, Fintype.card_fin, hcard_edge, Fintype.card_bool]
      ring
    rw [hc1, hc2]
  have hV_elem_zone : ∀ v ∈ V_res, ∃ z : UTZone, v ∈ z.finset n := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv_d | hv_o
    · obtain ⟨⟨i, c⟩, _, rfl⟩ := Finset.mem_image.mp hv_d
      obtain ⟨br, q, rfl⟩ := hdiagRect_decomp i
      rw [hdiagRect_emb]
      exact ⟨diagZone (tagDiag.symm q) c, hdiag_zone br (tagDiag.symm q) c⟩
    · obtain ⟨⟨s, u, b⟩, _, rfl⟩ := Finset.mem_image.mp hv_o
      exact ⟨ordZone (tagOrd.symm s) b, hord_zone (tagOrd.symm s) u b⟩
  have hV_sub : ∀ v ∈ V_res, v ∈ pool n := by
    intro v hv
    obtain ⟨z, hz⟩ := hV_elem_zone v hv
    exact (UTZone.elem_props z hz).2.2.1
  have hV_keepout : ∀ v ∈ V_res, (v : ℝ) ≤ utKeepoutLo n ∨ utKeepoutHi n < (v : ℝ) := by
    intro v hv
    obtain ⟨z, hz⟩ := hV_elem_zone v hv
    exact (UTZone.elem_props z hz).2.2.2.2.2
  -- Central-mean enclosure (`μ_lo = 0.3566 * X`, `μ_hi = 0.5764 * X`)
  have hV_sum_eq : ∀ f : ℕ → ℝ,
      (∑ v ∈ V_res, f v) =
        (∑ br : Bool, ∑ t : UTStageTag G M (utWDiag n),
          ((f (diagByTag br t).u1 + f (diagByTag br t).v1) +
           (f (diagByTag br t).u2 + f (diagByTag br t).v2))) +
        (∑ t : UTStageTag G M (utWOrd n), ∑ u : UTEdge n,
          (f (ordByTag t u false) + f (ordByTag t u true))) := by
    intro f
    dsimp only [V_res]
    rw [Finset.sum_union himg_disj]
    have hs_d : (∑ v ∈ img_diag, f v) =
        ∑ br : Bool, ∑ t : UTStageTag G M (utWDiag n),
          ((f (diagByTag br t).u1 + f (diagByTag br t).v1) +
           (f (diagByTag br t).u2 + f (diagByTag br t).v2)) := by
      dsimp only [img_diag]
      rw [Finset.sum_image (fun _ _ _ _ h => hdiag_inj h), Fintype.sum_prod_type, utDiag_univ_sum]
      dsimp only
      have hbranch : ∀ br : Bool,
          (∑ q : Fin L_half, ∑ c : Fin 4, f ((diagRect (utDiagEmb L_half br q)).corners c)) =
          ∑ t : UTStageTag G M (utWDiag n),
            ((f (diagByTag br t).u1 + f (diagByTag br t).v1) +
             (f (diagByTag br t).u2 + f (diagByTag br t).v2)) := by
        intro br
        rw [← Equiv.sum_comp tagDiag]
        apply Finset.sum_congr rfl; intro t _
        rw [hdiagRect_emb, tagDiag.symm_apply_apply, Fin.sum_univ_four]
        dsimp [UTRectData.corners]; ring
      rw [hbranch true, hbranch false, Fintype.sum_bool]
    have hs_o : (∑ v ∈ img_ord, f v) =
        ∑ t : UTStageTag G M (utWOrd n), ∑ u : UTEdge n,
          (f (ordByTag t u false) + f (ordByTag t u true)) := by
      dsimp only [img_ord]
      rw [Finset.sum_image (fun _ _ _ _ h => hord_inj h), Fintype.sum_prod_type,
        ← Equiv.sum_comp tagOrd]
      apply Finset.sum_congr rfl; intro t _
      rw [Fintype.sum_prod_type]
      dsimp only [ordRaw]
      rw [tagOrd.symm_apply_apply]
      apply Finset.sum_congr rfl; intro u _
      rw [Fintype.sum_bool]; ring
    rw [hs_d, hs_o]
  have hg_pair_bounds : ∀ (g : Fin G) {a b : ℕ},
      a ∈ (gw.stages.get g).footprint → b ∈ (gw.stages.get g).footprint →
      (if gw.isPool1 (gw.stages.get g) then
        (136 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧ ((a + b : ℕ) : ℝ) ≤ (646 / 1000 : ℝ) * utX n
      else
        (1162 / 1000 : ℝ) * utX n ≤ ((a + b : ℕ) : ℝ) ∧ ((a + b : ℕ) : ℝ) ≤ (1672 / 1000 : ℝ) * utX n) := by
    intro g a b ha hb
    have hza := hgFoot_zone g ha
    have hzb := hgFoot_zone g hb
    by_cases hp : gw.isPool1 (gw.stages.get g) = true
    · have hzone : gZone g = UTZone.pool1 := if_pos hp
      rw [hzone] at hza hzb
      rw [if_pos hp]
      have pa := UTZone.elem_props UTZone.pool1 hza
      have pb := UTZone.elem_props UTZone.pool1 hzb
      dsimp [UTZone.loNat, UTZone.hiNat] at pa pb
      push_cast; exact ⟨by linarith [pa.2.2.2.1, pb.2.2.2.1], by linarith [pa.2.2.2.2.1, pb.2.2.2.2.1]⟩
    · have hzone : gZone g = UTZone.pool2 := if_neg hp
      rw [hzone] at hza hzb
      rw [if_neg hp]
      have pa := UTZone.elem_props UTZone.pool2 hza
      have pb := UTZone.elem_props UTZone.pool2 hzb
      dsimp [UTZone.loNat, UTZone.hiNat] at pa pb
      push_cast; exact ⟨by linarith [pa.2.2.2.1, pb.2.2.2.1], by linarith [pa.2.2.2.2.1, pb.2.2.2.2.1]⟩
  obtain ⟨hpool_lo, hpool_hi⟩ := global_pool_mean_bounds rs sharp (by omega : 2001 ≤ n)
  have hn_sq_pos : (0 : ℝ) < ((n * n : ℕ) : ℝ) := by positivity
  have hpoolTotal_lo : (449 / 1000 : ℝ) * ((n * n : ℕ) : ℝ) * utX n < (Lucas.poolTotal n : ℝ) := by
    have h1 := (lt_div_iff₀ hX_pos).mp hpool_lo
    have h2 := (lt_div_iff₀ hn_sq_pos).mp h1
    linarith [show (449 / 1000 : ℝ) * utX n * ((n * n : ℕ) : ℝ) =
      (449 / 1000 : ℝ) * ((n * n : ℕ) : ℝ) * utX n by ring]
  have hpoolTotal_hi : (Lucas.poolTotal n : ℝ) < (519 / 1000 : ℝ) * ((n * n : ℕ) : ℝ) * utX n := by
    have h1 := (div_lt_iff₀ hX_pos).mp hpool_hi
    have h2 := (div_lt_iff₀ hn_sq_pos).mp h1
    linarith [show (519 / 1000 : ℝ) * utX n * ((n * n : ℕ) : ℝ) =
      (519 / 1000 : ℝ) * ((n * n : ℕ) : ℝ) * utX n by ring]
  have hLn11_lin := ut_ln_le_linear_11 rs lower sharp upper hn
  obtain ⟨hmv_lin, _⟩ := ut_quadratic_step_bounds rs lower sharp upper hn
  obtain ⟨_, _, hbst_lin, _⟩ := ut_ln14_step_bounds rs lower sharp upper hn
  have hnR : (35735 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hp1_count : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (1 : ℝ) else 0) ≤ (utStepsAP n : ℝ) := by
    have hnat : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (1 : ℕ) else 0) ≤ utStepsAP n := by
      dsimp only [G]
      rw [← list_map_sum_eq_fin_sum gw.stages (fun s => if gw.isPool1 s then (1 : ℕ) else 0)]
      exact gw.hp1_sum
    have hcast : ((∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (1 : ℕ) else 0 : ℕ) : ℝ) ≤ (utStepsAP n : ℝ) := by
      exact_mod_cast hnat
    refine le_trans ?_ hcast
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum; intro g _; split_ifs <;> simp
  have hp2_count : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (0 : ℝ) else 1) ≤
      ((utSeedStages n + utStepsMV n + utStepsBoost n : ℕ) : ℝ) := by
    have hnat : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (0 : ℕ) else 1) ≤
        utSeedStages n + utStepsMV n + utStepsBoost n := by
      dsimp only [G]
      rw [← list_map_sum_eq_fin_sum gw.stages (fun s => if gw.isPool1 s then (0 : ℕ) else 1)]
      exact gw.hp2_sum
    have hcast : ((∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (0 : ℕ) else 1 : ℕ) : ℝ) ≤
        ((utSeedStages n + utStepsMV n + utStepsBoost n : ℕ) : ℝ) := by
      exact_mod_cast hnat
    refine le_trans ?_ hcast
    rw [Nat.cast_sum]
    apply Finset.sum_le_sum; intro g _; split_ifs <;> simp
  have hW_ord_lin : (utWOrd n : ℝ) ≤ (n : ℝ) / 430 + 12 := by
    have h1 : utWOrd n * 430 ≤ n + 12 * 430 := by dsimp [utWOrd]; omega
    have h1R : (utWOrd n : ℝ) * 430 ≤ (n : ℝ) + 12 * 430 := by exact_mod_cast h1
    linarith
  have hW_diag_lin : (utWDiag n : ℝ) ≤ (n : ℝ) / 2000 + (utLn n : ℝ) := by
    have h1 : utWDiag n * 2000 ≤ n + 2000 * utLn n := by dsimp [utWDiag]; omega
    have h1R : (utWDiag n : ℝ) * 2000 ≤ (n : ℝ) + 2000 * (utLn n : ℝ) := by exact_mod_cast h1
    linarith
  have hM_lin : (M : ℝ) ≤ 3 * (utLn n : ℝ) + 14 := by
    have h1 : M ≤ 3 * utLn n + 14 := by dsimp [M, utH0Max] at hh0_le ⊢; omega
    exact_mod_cast h1
  -- Low central-mean bound (`μ_lo = 3566 / 10000 * utX n`)
  have hV_mean_lo :
      (∑ v ∈ V_res, ((v : ℝ) - (3566 / 10000 : ℝ) * utX n)) ≤
        (Lucas.poolTotal n : ℝ) - ((n * n : ℕ) : ℝ) * ((3566 / 10000 : ℝ) * utX n) := by
    let f_lo (v : ℕ) : ℝ := (v : ℝ) - (3566 / 10000 : ℝ) * utX n
    have hf_pair : ∀ a b : ℕ, f_lo a + f_lo b = ((a + b : ℕ) : ℝ) - (7132 / 10000 : ℝ) * utX n := by
      intro a b; dsimp [f_lo]; push_cast; ring
    change (∑ v ∈ V_res, f_lo v) ≤ _
    rw [hV_sum_eq f_lo, Fintype.sum_bool, utStageTag_sum, utStageTag_sum, utStageTag_sum]
    have hg_d : ∀ (br : Bool) (g : Fin G),
        (f_lo (gDiag g br).u1 + f_lo (gDiag g br).v1) + (f_lo (gDiag g br).u2 + f_lo (gDiag g br).v2) ≤
          2 * ((9588 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 0 else 1) := by
      intro br g
      have hsub := (hgDiag_props g br).2.2
      have hb1 := hg_pair_bounds g (a := (gDiag g br).u1) (b := (gDiag g br).v1)
        (hsub (by simp [UTRectData.support])) (hsub (by simp [UTRectData.support]))
      have hb2 := hg_pair_bounds g (a := (gDiag g br).u2) (b := (gDiag g br).v2)
        (hsub (by simp [UTRectData.support])) (hsub (by simp [UTRectData.support]))
      rw [hf_pair, hf_pair]
      cases hp : gw.isPool1 (gw.stages.get g) <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hb1 hb2 ⊢ <;> linarith
    have hg_o : ∀ g : Fin G,
        (∑ u : UTEdge n, (f_lo (gOrd g u false) + f_lo (gOrd g u true))) ≤
          (6 * (n : ℝ)) * ((9588 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 0 else 1) := by
      intro g
      calc
        (∑ u : UTEdge n, (f_lo (gOrd g u false) + f_lo (gOrd g u true)))
            ≤ ∑ _u : UTEdge n, ((9588 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 0 else 1) := by
          apply Finset.sum_le_sum; intro u _
          have hb := hg_pair_bounds g (hgOrd_props g u).2.2.1 (hgOrd_props g u).2.2.2
          rw [hf_pair]
          cases hp : gw.isPool1 (gw.stages.get g) <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;> linarith
        _ = (6 * (n : ℝ)) * ((9588 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 0 else 1) := by
          simp [hcard_edge, nsmul_eq_mul]
    have hm_d : ∀ (br : Bool) (j : Fin M),
        (f_lo (mDiag br j).u1 + f_lo (mDiag br j).v1) + (f_lo (mDiag br j).u2 + f_lo (mDiag br j).v2) ≤
          2 * ((11228 / 10000 : ℝ) * utX n) := by
      intro br j
      have hm := hmDiag_props br j
      have b1 := (ut_mod_diag_pair_bounds hm.1 hm.2.2.1).2.2.2.2
      have b2 := (ut_mod_diag_pair_bounds hm.2.1 hm.2.2.2).2.2.2.2
      rw [hf_pair, hf_pair]; linarith
    have hm_o : ∀ j : Fin M,
        (∑ u : UTEdge n, (f_lo (mOrd j u false) + f_lo (mOrd j u true))) ≤
          (6 * (n : ℝ)) * ((11228 / 10000 : ℝ) * utX n) := by
      intro j
      calc
        _ ≤ ∑ _u : UTEdge n, (11228 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_mod_ord_pair_bounds ⟨j.val % 54, Nat.mod_lt _ (by decide)⟩
            (hmOrd_props j u).1 (hmOrd_props j u).2.1).2.2.2
          rw [hf_pair]; linarith
        _ = (6 * (n : ℝ)) * ((11228 / 10000 : ℝ) * utX n) := by simp [hcard_edge, nsmul_eq_mul]
    have hd_d : ∀ (br : Bool) (k : Fin 10),
        (f_lo (dblDiag k br).u1 + f_lo (dblDiag k br).v1) + (f_lo (dblDiag k br).u2 + f_lo (dblDiag k br).v2) ≤
          2 * ((10628 / 10000 : ℝ) * utX n) := by
      intro br k
      have hm := hdblDiag_props k br
      have b1 := (ut_dbl_pair_bounds k hm.1 hm.2.2.1).2.2.2.2
      have b2 := (ut_dbl_pair_bounds k hm.2.1 hm.2.2.2).2.2.2.2
      rw [hf_pair, hf_pair]; linarith
    have hd_o : ∀ k : Fin 10,
        (∑ u : UTEdge n, (f_lo (dblOrd k u false) + f_lo (dblOrd k u true))) ≤
          (6 * (n : ℝ)) * ((10628 / 10000 : ℝ) * utX n) := by
      intro k
      calc
        _ ≤ ∑ _u : UTEdge n, (10628 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_dbl_pair_bounds k (hdblOrd_props k u).1 (hdblOrd_props k u).2.1).2.2.2.2
          rw [hf_pair]; linarith
        _ = (6 * (n : ℝ)) * ((10628 / 10000 : ℝ) * utX n) := by simp [hcard_edge, nsmul_eq_mul]
    have hw_d : ∀ (br : Bool) (d : Fin (utWDiag n)),
        (f_lo (wideDiag d br).u1 + f_lo (wideDiag d br).v1) + (f_lo (wideDiag d br).u2 + f_lo (wideDiag d br).v2) ≤
          2 * ((3488 / 10000 : ℝ) * utX n) := by
      intro br d
      have hm := hwideDiag_props d br
      have b1 := (ut_wide_pair_bounds ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ hm.1 hm.2.2.1).2.2.2.2
      have b2 := (ut_wide_pair_bounds ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ hm.2.1 hm.2.2.2).2.2.2.2
      rw [hf_pair, hf_pair]; linarith
    have hw_o : ∀ w : Fin (utWOrd n),
        (∑ u : UTEdge n, (f_lo (wideOrd w u false) + f_lo (wideOrd w u true))) ≤
          (6 * (n : ℝ)) * ((3488 / 10000 : ℝ) * utX n) := by
      intro w
      calc
        _ ≤ ∑ _u : UTEdge n, (3488 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_wide_pair_bounds ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
            (hwideOrd_props w u).1 (hwideOrd_props w u).2.1).2.2.2.2
          rw [hf_pair]; linarith
        _ = (6 * (n : ℝ)) * ((3488 / 10000 : ℝ) * utX n) := by simp [hcard_edge, nsmul_eq_mul]
    have hs_gt := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_d true g
    have hs_gf := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_d false g
    have hs_go := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_o g
    have hs_mt := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_d true j
    have hs_mf := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_d false j
    have hs_mo := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_o j
    have hs_dt := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_d true k
    have hs_df := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_d false k
    have hs_do := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_o k
    have hs_wt := Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hw_d true d
    have hs_wf := Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hw_d false d
    have hs_wo := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hw_o w
    rw [← Finset.mul_sum] at hs_gt hs_gf hs_go
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs_mt hs_mf hs_mo hs_dt hs_df
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs_do hs_wt hs_wf hs_wo
    dsimp [diagByTag, ordByTag]
    have hp2_lin : ((utSeedStages n + utStepsMV n + utStepsBoost n : ℕ) : ℝ) ≤ (979 / 100000 : ℝ) * (n : ℝ) := by
      dsimp [utSeedStages]; push_cast; linarith [hLn11_lin, hmv_lin, hbst_lin, hnR]
    have hp2_sum_le : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (0 : ℝ) else 1) ≤
        (979 / 100000 : ℝ) * (n : ℝ) := hp2_count.trans hp2_lin
    have hM_lin2 : (M : ℝ) ≤ (47 / 35735 : ℝ) * (n : ℝ) := by linarith [hM_lin, hLn11_lin, hnR]
    have hWd_lin2 : (utWDiag n : ℝ) ≤ (1 / 2000 + 11 / 35735 : ℝ) * (n : ℝ) := by
      linarith [hW_diag_lin, hLn11_lin]
    have hWo_lin2 : (utWOrd n : ℝ) ≤ (1 / 430 + 12 / 35735 : ℝ) * (n : ℝ) := by
      linarith [hW_ord_lin, hnR]
    have hs_gt' := hs_gt.trans (mul_le_mul_of_nonneg_left hp2_sum_le (by positivity))
    have hs_gf' := hs_gf.trans (mul_le_mul_of_nonneg_left hp2_sum_le (by positivity))
    have hs_go' := hs_go.trans (mul_le_mul_of_nonneg_left hp2_sum_le (by positivity))
    have hs_mt' := hs_mt.trans (mul_le_mul_of_nonneg_right hM_lin2 (by positivity))
    have hs_mf' := hs_mf.trans (mul_le_mul_of_nonneg_right hM_lin2 (by positivity))
    have hs_mo' := hs_mo.trans (mul_le_mul_of_nonneg_right hM_lin2 (by positivity))
    have hs_wt' := hs_wt.trans (mul_le_mul_of_nonneg_right hWd_lin2 (by positivity))
    have hs_wf' := hs_wf.trans (mul_le_mul_of_nonneg_right hWd_lin2 (by positivity))
    have hs_wo' := hs_wo.trans (mul_le_mul_of_nonneg_right hWo_lin2 (by positivity))
    have hnx : (35735 : ℝ) * utX n ≤ (n : ℝ) * utX n :=
      mul_le_mul_of_nonneg_right hnR hX_pos.le
    have hn2x : (35735 : ℝ) * ((n : ℝ) * utX n) ≤ (n : ℝ) ^ 2 * utX n := by
      have hn2 : (35735 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      linarith [mul_le_mul_of_nonneg_right hn2 hX_pos.le]
    have hnn_eq : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
    rw [hnn_eq] at hpoolTotal_lo ⊢
    norm_num at hs_dt hs_df hs_do
    ring_nf at hs_gt' hs_gf' hs_go' hs_mt' hs_mf' hs_mo' hs_wt' hs_wf' hs_wo' hs_dt hs_df hs_do hnx hn2x hpoolTotal_lo ⊢
    linarith [hX_pos]
  -- High central-mean bound (`μ_hi = 5764 / 10000 * utX n`)
  have hV_mean_hi :
      (∑ v ∈ V_res, ((5764 / 10000 : ℝ) * utX n - (v : ℝ))) ≤
        ((n * n : ℕ) : ℝ) * ((5764 / 10000 : ℝ) * utX n) - (Lucas.poolTotal n : ℝ) := by
    let f_hi (v : ℕ) : ℝ := (5764 / 10000 : ℝ) * utX n - (v : ℝ)
    have hf_pair : ∀ a b : ℕ, f_hi a + f_hi b = (11528 / 10000 : ℝ) * utX n - ((a + b : ℕ) : ℝ) := by
      intro a b; dsimp [f_hi]; push_cast; ring
    change (∑ v ∈ V_res, f_hi v) ≤ _
    rw [hV_sum_eq f_hi, Fintype.sum_bool, utStageTag_sum, utStageTag_sum, utStageTag_sum]
    have hg_d : ∀ (br : Bool) (g : Fin G),
        (f_hi (gDiag g br).u1 + f_hi (gDiag g br).v1) + (f_hi (gDiag g br).u2 + f_hi (gDiag g br).v2) ≤
          2 * ((10168 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 1 else 0) := by
      intro br g
      have hsub := (hgDiag_props g br).2.2
      have hb1 := hg_pair_bounds g (a := (gDiag g br).u1) (b := (gDiag g br).v1)
        (hsub (by simp [UTRectData.support])) (hsub (by simp [UTRectData.support]))
      have hb2 := hg_pair_bounds g (a := (gDiag g br).u2) (b := (gDiag g br).v2)
        (hsub (by simp [UTRectData.support])) (hsub (by simp [UTRectData.support]))
      rw [hf_pair, hf_pair]
      cases hp : gw.isPool1 (gw.stages.get g) <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hb1 hb2 ⊢ <;> linarith
    have hg_o : ∀ g : Fin G,
        (∑ u : UTEdge n, (f_hi (gOrd g u false) + f_hi (gOrd g u true))) ≤
          (6 * (n : ℝ)) * ((10168 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 1 else 0) := by
      intro g
      calc
        (∑ u : UTEdge n, (f_hi (gOrd g u false) + f_hi (gOrd g u true)))
            ≤ ∑ _u : UTEdge n, ((10168 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 1 else 0) := by
          apply Finset.sum_le_sum; intro u _
          have hb := hg_pair_bounds g (hgOrd_props g u).2.2.1 (hgOrd_props g u).2.2.2
          rw [hf_pair]
          cases hp : gw.isPool1 (gw.stages.get g) <;> simp only [hp, Bool.false_eq_true, ↓reduceIte] at hb ⊢ <;> linarith
        _ = (6 * (n : ℝ)) * ((10168 / 10000 : ℝ) * utX n) * (if gw.isPool1 (gw.stages.get g) then 1 else 0) := by
          simp [hcard_edge, nsmul_eq_mul]
    have hm_d : ∀ (br : Bool) (j : Fin M),
        (f_hi (mDiag br j).u1 + f_hi (mDiag br j).v1) + (f_hi (mDiag br j).u2 + f_hi (mDiag br j).v2) ≤ 0 := by
      intro br j
      have hm := hmDiag_props br j
      have b1 := (ut_mod_diag_pair_bounds hm.1 hm.2.2.1).2.2.2.1
      have b2 := (ut_mod_diag_pair_bounds hm.2.1 hm.2.2.2).2.2.2.1
      rw [hf_pair, hf_pair]; linarith
    have hm_o : ∀ j : Fin M,
        (∑ u : UTEdge n, (f_hi (mOrd j u false) + f_hi (mOrd j u true))) ≤ 0 := by
      intro j
      calc
        _ ≤ ∑ _u : UTEdge n, (0 : ℝ) := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_mod_ord_pair_bounds ⟨j.val % 54, Nat.mod_lt _ (by decide)⟩
            (hmOrd_props j u).1 (hmOrd_props j u).2.1).2.2.1
          rw [hf_pair]; linarith
        _ = 0 := by simp
    have hd_d : ∀ (br : Bool) (k : Fin 10),
        (f_hi (dblDiag k br).u1 + f_hi (dblDiag k br).v1) + (f_hi (dblDiag k br).u2 + f_hi (dblDiag k br).v2) ≤
          2 * ((4758 / 10000 : ℝ) * utX n) := by
      intro br k
      have hm := hdblDiag_props k br
      have b1 := (ut_dbl_pair_bounds k hm.1 hm.2.2.1).2.2.2.1
      have b2 := (ut_dbl_pair_bounds k hm.2.1 hm.2.2.2).2.2.2.1
      rw [hf_pair, hf_pair]; linarith
    have hd_o : ∀ k : Fin 10,
        (∑ u : UTEdge n, (f_hi (dblOrd k u false) + f_hi (dblOrd k u true))) ≤
          (6 * (n : ℝ)) * ((4758 / 10000 : ℝ) * utX n) := by
      intro k
      calc
        _ ≤ ∑ _u : UTEdge n, (4758 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_dbl_pair_bounds k (hdblOrd_props k u).1 (hdblOrd_props k u).2.1).2.2.2.1
          rw [hf_pair]; linarith
        _ = (6 * (n : ℝ)) * ((4758 / 10000 : ℝ) * utX n) := by simp [hcard_edge, nsmul_eq_mul]
    have hw_d : ∀ (br : Bool) (d : Fin (utWDiag n)),
        (f_hi (wideDiag d br).u1 + f_hi (wideDiag d br).v1) + (f_hi (wideDiag d br).u2 + f_hi (wideDiag d br).v2) ≤
          2 * ((2108 / 10000 : ℝ) * utX n) := by
      intro br d
      have hm := hwideDiag_props d br
      have b1 := (ut_wide_pair_bounds ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ hm.1 hm.2.2.1).2.2.2.1
      have b2 := (ut_wide_pair_bounds ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ hm.2.1 hm.2.2.2).2.2.2.1
      rw [hf_pair, hf_pair]; linarith
    have hw_o : ∀ w : Fin (utWOrd n),
        (∑ u : UTEdge n, (f_hi (wideOrd w u false) + f_hi (wideOrd w u true))) ≤
          (6 * (n : ℝ)) * ((2108 / 10000 : ℝ) * utX n) := by
      intro w
      calc
        _ ≤ ∑ _u : UTEdge n, (2108 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro u _
          have b := (ut_wide_pair_bounds ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩
            (hwideOrd_props w u).1 (hwideOrd_props w u).2.1).2.2.2.1
          rw [hf_pair]; linarith
        _ = (6 * (n : ℝ)) * ((2108 / 10000 : ℝ) * utX n) := by simp [hcard_edge, nsmul_eq_mul]
    have hs_gt := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_d true g
    have hs_gf := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_d false g
    have hs_go := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hg_o g
    have hs_mt := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_d true j
    have hs_mf := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_d false j
    have hs_mo := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hm_o j
    have hs_dt := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_d true k
    have hs_df := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_d false k
    have hs_do := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hd_o k
    have hs_wt := Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hw_d true d
    have hs_wf := Finset.sum_le_sum fun d (_ : d ∈ Finset.univ) => hw_d false d
    have hs_wo := Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hw_o w
    rw [← Finset.mul_sum] at hs_gt hs_gf hs_go
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_zero] at hs_mt hs_mf hs_mo hs_dt hs_df
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs_do hs_wt hs_wf hs_wo
    dsimp [diagByTag, ordByTag]
    have hp1_lin : (utStepsAP n : ℝ) ≤ (286 / 35735 : ℝ) * (n : ℝ) := by
      dsimp [utStepsAP, utStepsAP1, utStepsAP2]; push_cast; linarith [hLn11_lin]
    have hp1_sum_le : (∑ g : Fin G, if gw.isPool1 (gw.stages.get g) then (1 : ℝ) else 0) ≤
        (286 / 35735 : ℝ) * (n : ℝ) := hp1_count.trans hp1_lin
    have hs_gt' := hs_gt.trans (mul_le_mul_of_nonneg_left hp1_sum_le (by positivity))
    have hs_gf' := hs_gf.trans (mul_le_mul_of_nonneg_left hp1_sum_le (by positivity))
    have hs_go' := hs_go.trans (mul_le_mul_of_nonneg_left hp1_sum_le (by positivity))
    have hWd_lin2 : (utWDiag n : ℝ) ≤ (1 / 2000 + 11 / 35735 : ℝ) * (n : ℝ) := by
      linarith [hW_diag_lin, hLn11_lin]
    have hWo_lin2 : (utWOrd n : ℝ) ≤ (1 / 430 + 12 / 35735 : ℝ) * (n : ℝ) := by
      linarith [hW_ord_lin, hnR]
    have hs_wt' := hs_wt.trans (mul_le_mul_of_nonneg_right hWd_lin2 (by positivity))
    have hs_wf' := hs_wf.trans (mul_le_mul_of_nonneg_right hWd_lin2 (by positivity))
    have hs_wo' := hs_wo.trans (mul_le_mul_of_nonneg_right hWo_lin2 (by positivity))
    have hnx : (35735 : ℝ) * utX n ≤ (n : ℝ) * utX n :=
      mul_le_mul_of_nonneg_right hnR hX_pos.le
    have hn2x : (35735 : ℝ) * ((n : ℝ) * utX n) ≤ (n : ℝ) ^ 2 * utX n := by
      have hn2 : (35735 : ℝ) * (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
      linarith [mul_le_mul_of_nonneg_right hn2 hX_pos.le]
    have hnn_eq : ((n * n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
    rw [hnn_eq] at hpoolTotal_hi ⊢
    norm_num at hs_dt hs_df hs_do
    ring_nf at hs_gt' hs_gf' hs_go' hs_wt' hs_wf' hs_wo' hs_dt hs_df hs_do hs_mt hs_mf hs_mo hnx hn2x hpoolTotal_hi ⊢
    linarith [hX_pos]
  -- Assemble diagonal `EvenIntervalGrid`s for `true` and `false`
  have hdiag_tag_grid : ∀ br : Bool,
      ∃ A B : ℕ,
        EvenIntervalGrid ((Finset.univ : Finset (Fin L)).filter (fun i => choice i = br))
          (fun i => (diagRect i).gap) A B ∧
        2 ∣ B ∧ A ≤ B ∧
        A + B = (∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = br), (diagRect i).gap) ∧
        (A : ℝ) ≤ (12 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n ∧
        (1467 / 1000 + (932 / 1000 : ℝ) * (utWDiag n : ℝ)) * utX n ≤ (B : ℝ) - (A : ℝ) := by
    intro br
    obtain ⟨A, B, hgrid0, hB_ev, hAB, htot0, hA_ub, hspan⟩ :=
      ut_assemble_tag_grid (W := utWDiag n) gw (fun t => (diagByTag br t).gap)
        (fun g => (hgDiag_props g br).1)
        (fun j => by
          have hm := hmDiag_props br j
          have hb := (ut_mod_diag_pair_bounds hm.1 hm.2.2.1).1
          have hg_eq : ((mDiag br j).gap : ℝ) = ((mDiag br j).v1 : ℝ) - ((mDiag br j).u1 : ℝ) := by
            rw [(mDiag br j).hv1]; push_cast; ring
          exact ⟨(mDiag br j).hgap_even, hg_eq ▸ hb⟩)
        (fun r hr => hmDiag_cov br r hr)
        (fun k => by
          have hm := hdblDiag_props k br
          have hb := ut_dbl_pair_bounds k hm.1 hm.2.2.1
          have hg_eq : ((dblDiag k br).gap : ℝ) = ((dblDiag k br).v1 : ℝ) - ((dblDiag k br).u1 : ℝ) := by
            rw [(dblDiag k br).hv1]; push_cast; ring
          exact ⟨(dblDiag k br).hgap_even, hg_eq ▸ hb.1, hg_eq ▸ hb.2.1⟩)
        (fun d => by
          have hm := hwideDiag_props d br
          have hb := ut_wide_pair_bounds ⟨d.val % 30, Nat.mod_lt _ (by decide)⟩ hm.1 hm.2.2.1
          have hg_eq : ((wideDiag d br).gap : ℝ) = ((wideDiag d br).v1 : ℝ) - ((wideDiag d br).u1 : ℝ) := by
            rw [(wideDiag d br).hv1]; push_cast; ring
          exact ⟨(wideDiag d br).hgap_even, hg_eq ▸ hb.1, hg_eq ▸ hb.2.1⟩)
    let fEmb : UTStageTag G M (utWDiag n) → Fin L := fun t => utDiagEmb L_half br (tagDiag t)
    have hfEmb_inj : Function.Injective fEmb :=
      (utDiagEmb_injective L_half br).comp tagDiag.injective
    have hfEmb_img : Finset.univ.image fEmb =
        (Finset.univ : Finset (Fin L)).filter (fun i => choice i = br) := by
      dsimp [choice]
      rw [utDiagChoice_filter_eq]
      ext i; simp only [Finset.mem_image, Finset.mem_univ, true_and, fEmb]
      exact ⟨fun ⟨t, ht⟩ => ⟨tagDiag t, ht⟩, fun ⟨q, hq⟩ => ⟨tagDiag.symm q, by simpa using hq⟩⟩
    have hfEmb_gap : ∀ t : UTStageTag G M (utWDiag n), (diagRect (fEmb t)).gap = (diagByTag br t).gap := by
      intro t; dsimp [fEmb]; rw [hdiagRect_emb, tagDiag.symm_apply_apply]
    have hgrid1 := evenIntervalGrid_image (gapβ := fun i => (diagRect i).gap)
      fEmb hfEmb_inj (fun t _ => hfEmb_gap t) hgrid0
    rw [hfEmb_img] at hgrid1
    have htot1 : A + B = ∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = br), (diagRect i).gap := by
      rw [← hfEmb_img, Finset.sum_image (fun _ _ _ _ h => hfEmb_inj h)]
      exact htot0.trans (Finset.sum_congr rfl fun t _ => (hfEmb_gap t).symm)
    exact ⟨A, B, hgrid1, hB_ev, hAB, htot1, hA_ub, hspan⟩
  obtain ⟨Am, Rm, hm_grid, hRm_even, hAm_le_Rm, hm_tot, _, hm_span⟩ := hdiag_tag_grid true
  obtain ⟨Aa, Ra, ha_grid, hRa_even, hAa_le_Ra, ha_tot, _, ha_span⟩ := hdiag_tag_grid false
  -- Diagonal midpoint balance
  have hdiag_mid_bal :
      |(∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = true),
          (((diagRect i).u1 : ℝ) + ((diagRect i).gap : ℝ) / 2)) -
       (∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = false),
          (((diagRect i).u1 : ℝ) + ((diagRect i).gap : ℝ) / 2))| ≤
        ((140 / 1000 : ℝ) + (6 / 10000 : ℝ) * (utH0Max n : ℝ)) * utX n := by
    have hsum_br : ∀ br : Bool,
        (∑ i ∈ (Finset.univ : Finset (Fin L)).filter (fun i => choice i = br),
          (((diagRect i).u1 : ℝ) + ((diagRect i).gap : ℝ) / 2)) =
        ∑ t : UTStageTag G M (utWDiag n), (((diagByTag br t).u1 : ℝ) + ((diagByTag br t).gap : ℝ) / 2) := by
      intro br
      dsimp [choice]
      rw [utDiagChoice_filter_eq, Finset.sum_image (fun _ _ _ _ h => utDiagEmb_injective L_half br h),
        ← Equiv.sum_comp tagDiag]
      apply Finset.sum_congr rfl; intro t _
      rw [hdiagRect_emb, tagDiag.symm_apply_apply]
    rw [hsum_br true, hsum_br false, utStageTag_sum, utStageTag_sum]
    dsimp [diagByTag]
    have hmod_bal : |(∑ j : Fin M, (((mDiag true j).u1 : ℝ) + ((mDiag true j).gap : ℝ) / 2)) -
        (∑ j : Fin M, (((mDiag false j).u1 : ℝ) + ((mDiag false j).gap : ℝ) / 2))| ≤
        (6 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ j : Fin M, ((((mDiag true j).u1 : ℝ) + ((mDiag true j).gap : ℝ) / 2) -
            (((mDiag false j).u1 : ℝ) + ((mDiag false j).gap : ℝ) / 2))|
            ≤ ∑ j : Fin M, |(((mDiag true j).u1 : ℝ) + ((mDiag true j).gap : ℝ) / 2) -
                (((mDiag false j).u1 : ℝ) + ((mDiag false j).gap : ℝ) / 2)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : Fin M, (6 / 10000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro j _
          have hmT := hmDiag_props true j
          have hmF := hmDiag_props false j
          have bT := ut_mod_diag_pair_bounds hmT.1 hmT.2.2.1
          have bF := ut_mod_diag_pair_bounds hmF.1 hmF.2.2.1
          have h1 : (((mDiag true j).u1 + (mDiag true j).v1 : ℕ) : ℝ) / 2 =
              ((mDiag true j).u1 : ℝ) + ((mDiag true j).gap : ℝ) / 2 := by
            have := (mDiag true j).hv1; push_cast [this]; ring
          have h2 : (((mDiag false j).u1 + (mDiag false j).v1 : ℕ) : ℝ) / 2 =
              ((mDiag false j).u1 : ℝ) + ((mDiag false j).gap : ℝ) / 2 := by
            have := (mDiag false j).hv1; push_cast [this]; ring
          rw [h1] at bT; rw [h2] at bF
          exact abs_le.mpr ⟨by linarith [bT.2.1, bF.2.2.1], by linarith [bT.2.2.1, bF.2.1]⟩
        _ = (M : ℝ) * ((6 / 10000 : ℝ) * utX n) := by simp [nsmul_eq_mul]
        _ ≤ (6 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n := by
          have hM_le : (M : ℝ) ≤ (utH0Max n : ℝ) := by exact_mod_cast (show M ≤ utH0Max n by dsimp [M]; omega)
          nlinarith
    have hdbl_bal : |(∑ k : Fin 10, (((dblDiag k true).u1 : ℝ) + ((dblDiag k true).gap : ℝ) / 2)) -
        (∑ k : Fin 10, (((dblDiag k false).u1 : ℝ) + ((dblDiag k false).gap : ℝ) / 2))| ≤
        (10 / 1000 : ℝ) * utX n := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k : Fin 10, ((((dblDiag k true).u1 : ℝ) + ((dblDiag k true).gap : ℝ) / 2) -
            (((dblDiag k false).u1 : ℝ) + ((dblDiag k false).gap : ℝ) / 2))|
            ≤ ∑ k : Fin 10, |(((dblDiag k true).u1 : ℝ) + ((dblDiag k true).gap : ℝ) / 2) -
                (((dblDiag k false).u1 : ℝ) + ((dblDiag k false).gap : ℝ) / 2)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin 10, (1 / 1000 : ℝ) * utX n := by
          apply Finset.sum_le_sum; intro k _
          have hmT := hdblDiag_props k true
          have hmF := hdblDiag_props k false
          have bT := abs_le.mp (ut_dbl_pair_bounds k hmT.1 hmT.2.2.1).2.2.1
          have bF := abs_le.mp (ut_dbl_pair_bounds k hmF.1 hmF.2.2.1).2.2.1
          have h1 : (((dblDiag k true).u1 + (dblDiag k true).v1 : ℕ) : ℝ) =
              2 * (((dblDiag k true).u1 : ℝ) + ((dblDiag k true).gap : ℝ) / 2) := by
            have := (dblDiag k true).hv1; push_cast [this]; ring
          have h2 : (((dblDiag k false).u1 + (dblDiag k false).v1 : ℕ) : ℝ) =
              2 * (((dblDiag k false).u1 : ℝ) + ((dblDiag k false).gap : ℝ) / 2) := by
            have := (dblDiag k false).hv1; push_cast [this]; ring
          rw [h1] at bT; rw [h2] at bF
          exact abs_le.mpr ⟨by linarith, by linarith⟩
        _ = (10 / 1000 : ℝ) * utX n := by simp [nsmul_eq_mul]; ring
    have hg_abs := abs_le.mp hgDiag_bal
    have hm_abs := abs_le.mp hmod_bal
    have hd_abs := abs_le.mp hdbl_bal
    have hw_abs := abs_le.mp hwideDiag_bal
    have hmid_def : utMidWidth n = (128 / 1000 : ℝ) * utX n := rfl
    rw [hmid_def] at hg_abs
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- Assemble ordinary `EvenIntervalGrid`s across all `u : UTEdge n`
  have hord_tag_grid : ∀ u : UTEdge n,
      ∃ A B : ℕ,
        EvenIntervalGrid (Finset.univ : Finset (Fin S)) (fun s => ordGap s u) A B ∧
        2 ∣ B ∧ A ≤ B ∧
        A + B = (∑ s : Fin S, ordGap s u) ∧
        (A : ℝ) ≤ (12 / 10000 : ℝ) * (utH0Max n : ℝ) * utX n ∧
        (1467 / 1000 + (932 / 1000 : ℝ) * (utWOrd n : ℝ)) * utX n ≤ (B : ℝ) - (A : ℝ) := by
    intro u
    obtain ⟨A, B, hgrid0, hB_ev, hAB, htot0, hA_ub, hspan⟩ :=
      ut_assemble_tag_grid (W := utWOrd n) gw (fun t => ordGapByTag t u)
        (fun _ => rfl)
        (fun j => by
          obtain ⟨h1, h2, hlt, hev⟩ := hmOrd_props j u
          have hb := (ut_mod_ord_pair_bounds ⟨j.val % 54, Nat.mod_lt _ (by decide)⟩ h1 h2).1
          have hg_eq : ((mOrd j u true - mOrd j u false : ℕ) : ℝ) = (mOrd j u true : ℝ) - (mOrd j u false : ℝ) :=
            Nat.cast_sub hlt.le
          exact ⟨hev, hg_eq ▸ hb⟩)
        (fun r hr => hmOrd_cov u r hr)
        (fun k => by
          obtain ⟨h1, h2, hlt, hev⟩ := hdblOrd_props k u
          have hb := ut_dbl_pair_bounds k h1 h2
          have hg_eq : ((dblOrd k u true - dblOrd k u false : ℕ) : ℝ) = (dblOrd k u true : ℝ) - (dblOrd k u false : ℝ) :=
            Nat.cast_sub hlt.le
          exact ⟨hev, hg_eq ▸ hb.1, hg_eq ▸ hb.2.1⟩)
        (fun w => by
          obtain ⟨h1, h2, hlt, hev⟩ := hwideOrd_props w u
          have hb := ut_wide_pair_bounds ⟨w.val % 30, Nat.mod_lt _ (by decide)⟩ h1 h2
          have hg_eq : ((wideOrd w u true - wideOrd w u false : ℕ) : ℝ) = (wideOrd w u true : ℝ) - (wideOrd w u false : ℝ) :=
            Nat.cast_sub hlt.le
          exact ⟨hev, hg_eq ▸ hb.1, hg_eq ▸ hb.2.1⟩)
    have hgap_eq : ∀ t : UTStageTag G M (utWOrd n), ordGap (tagOrd t) u = ordGapByTag t u := by
      intro t; dsimp [ordGap]; rw [tagOrd.symm_apply_apply]
    have hgrid1 := evenIntervalGrid_image (gapβ := fun s => ordGap s u)
      tagOrd tagOrd.injective (fun t _ => hgap_eq t) hgrid0
    have himg : Finset.univ.image tagOrd = Finset.univ := by
      ext s; simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
      exact ⟨tagOrd.symm s, tagOrd.apply_symm_apply s⟩
    rw [himg] at hgrid1
    have htot1 : A + B = ∑ s : Fin S, ordGap s u := by
      rw [← Equiv.sum_comp tagOrd]
      exact htot0.trans (Finset.sum_congr rfl fun t _ => (hgap_eq t).symm)
    exact ⟨A, B, hgrid1, hB_ev, hAB, htot1, hA_ub, hspan⟩
  choose edgeA edgeRadius hedge_grid hedge_even hedge_le hedge_tot hedgeA_ub hedge_span using hord_tag_grid
  exact ⟨{
    G := G
    h0 := h0
    S := S
    L_half := L_half
    L := L
    hG_pos := gw.hlen_pos
    hh0_ge2 := hh0_ge2
    hh0_le := hh0_le
    hS_def := rfl
    hL_half_def := rfl
    hL_def := rfl
    hGS := hGS
    hpack_ord := hpack_ord
    hs := hs
    hL_ge3 := hL_ge3
    hres_quarter := hres_quarter
    choice := choice
    hchoice_true_card := utDiagChoice_card L_half true
    hchoice_false_card := utDiagChoice_card L_half false
    diagRect := diagRect
    ordRaw := ordRaw
    ordGap := ordGap
    hord_pair := hord_pair
    hordGap_growth := hordGap_growth
    hgrowth_mid_spread := hgrowth_mid_spread
    ordNongrowthAnchor := ordNongrowthAnchor
    ordNongrowthHalfWidth := ordNongrowthHalfWidth
    hnongrowth_width_nn := hnongrowth_width_nn
    hnongrowth_pair_bound := hnongrowth_pair_bound
    hnongrowth_width_sum := hnongrowth_width_sum
    V_res := V_res
    hV_sub := hV_sub
    hV_card := hV_card
    hV_keepout := hV_keepout
    hV_mean_lo := hV_mean_lo
    hV_mean_hi := hV_mean_hi
    hdiag_mem := fun t c => Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(t, c), Finset.mem_univ _, rfl⟩)
    hord_mem := fun s u b => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(s, u, b), Finset.mem_univ _, rfl⟩)
    hdiag_inj := hdiag_inj
    hord_inj := hord_inj
    hdiag_ord_disj := hdiag_ord_disj
    hV_union := rfl
    Am := Am
    Rm := Rm
    Aa := Aa
    Ra := Ra
    hm_grid := hm_grid
    ha_grid := ha_grid
    hRm_even := hRm_even
    hRa_even := hRa_even
    hAm_le_Rm := hAm_le_Rm
    hAa_le_Ra := hAa_le_Ra
    hm_tot := hm_tot
    ha_tot := ha_tot
    hm_span := hm_span
    ha_span := ha_span
    hdiag_mid_bal := hdiag_mid_bal
    edgeA := edgeA
    edgeRadius := edgeRadius
    hedge_grid := hedge_grid
    hedge_even := hedge_even
    hedge_le := hedge_le
    hedge_tot := hedge_tot
    hedgeA_ub := hedgeA_ub
    hedge_span := hedge_span
  }⟩






end

end Sude
