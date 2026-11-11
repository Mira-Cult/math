import Sude.MatchedBinPairedDepletion
import Sude.FWWidePhysicalGrid
import Sude.FWJointLayerPacking

/-!
# Generalized FC2K Wide Role Installation & Grid Extension

Parameterizes Wide matched-bin selection, physical rectangle/ordinary-layer placement,
midpoint concentration (`|low + high - 2 * m| ≤ δ * X`), gap lower/upper bounds, and
`CompleteEvenGrid` extension for arbitrary `(W_ord, W_diag_extra, N, δ)` across `[2001, 19483]`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Left endpoint of FC2K reflected Wide bin `(i, side)` (`false` = low, `true` = high). -/
def fc2kWideLeft (m X δ : ℝ) {N : ℕ} (z : Fin N × Bool) : ℝ :=
  if z.2 then
    (2 * m - (1 / 500 : ℝ) * X) - ((z.1.val + 1 : ℕ) : ℝ) * (δ * X)
  else
    (1 / 500 : ℝ) * X + (z.1.val : ℝ) * (δ * X)

/-- Right endpoint of FC2K reflected Wide bin `(i, side)` (`false` = low, `true` = high). -/
def fc2kWideRight (m X δ : ℝ) {N : ℕ} (z : Fin N × Bool) : ℝ :=
  if z.2 then
    (2 * m - (1 / 500 : ℝ) * X) - (z.1.val : ℝ) * (δ * X)
  else
    (1 / 500 : ℝ) * X + ((z.1.val + 1 : ℕ) : ℝ) * (δ * X)

/-- Interval width, positivity, separation, cross-ordering, and BMOR stock lower bound for
`fc2kWideLeft` / `fc2kWideRight`. -/
theorem fc2kWide_interval_props {N : ℕ} (m X δ : ℝ)
    (hX : (500 : ℝ) ≤ X) (hδ : 0 < δ)
    (hsep_mid : ((1 / 250 : ℝ) + 2 * (N : ℝ) * δ) * X ≤ 2 * m)
    (hm_hi : 2 * m ≤ X) :
    (∀ z : Fin N × Bool, 1 ≤ fc2kWideLeft m X δ z) ∧
    (∀ z : Fin N × Bool, fc2kWideLeft m X δ z ≤ fc2kWideRight m X δ z) ∧
    (∀ z : Fin N × Bool, fc2kWideRight m X δ z ≤ X) ∧
    (∀ z t : Fin N × Bool, z ≠ t →
      fc2kWideRight m X δ z ≤ fc2kWideLeft m X δ t ∨
        fc2kWideRight m X δ t ≤ fc2kWideLeft m X δ z) ∧
    (∀ i j : Fin N, fc2kWideRight m X δ (i, false) ≤ fc2kWideLeft m X δ (j, true)) ∧
    (∀ z : Fin N × Bool, fc2kWideRight m X δ z - fc2kWideLeft m X δ z = δ * X) := by
  have hδX : 0 < δ * X := by positivity
  have hcross_all : ∀ i j : Fin N, fc2kWideRight m X δ (i, false) ≤ fc2kWideLeft m X δ (j, true) := by
    intro i j
    have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i.isLt
    have hj1 : ((j.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast j.isLt
    have hmul_i := mul_le_mul_of_nonneg_right hi1 hδX.le
    have hmul_j := mul_le_mul_of_nonneg_right hj1 hδX.le
    simp only [fc2kWideRight, fc2kWideLeft, Bool.false_eq_true, ↓reduceIte]
    nlinarith
  refine ⟨?_, ?_, ?_, ?_, hcross_all, ?_⟩
  · rintro ⟨i, side⟩
    cases side
    · have hi0 : (0 : ℝ) ≤ (i.val : ℝ) * (δ * X) := by positivity
      simp only [fc2kWideLeft, Bool.false_eq_true, ↓reduceIte]
      linarith
    · have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i.isLt
      have hmul := mul_le_mul_of_nonneg_right hi1 hδX.le
      have hN0 : (0 : ℝ) ≤ (N : ℝ) * (δ * X) := by positivity
      simp only [fc2kWideLeft, ↓reduceIte]
      nlinarith
  · rintro ⟨i, side⟩
    cases side <;> simp only [fc2kWideLeft, fc2kWideRight, Bool.false_eq_true, ↓reduceIte] <;>
      push_cast <;> linarith
  · rintro ⟨i, side⟩
    cases side
    · have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i.isLt
      have hmul := mul_le_mul_of_nonneg_right hi1 hδX.le
      have hN0 : (0 : ℝ) ≤ (N : ℝ) * (δ * X) := by positivity
      simp only [fc2kWideRight, Bool.false_eq_true, ↓reduceIte]
      nlinarith
    · have hi0 : (0 : ℝ) ≤ (i.val : ℝ) * (δ * X) := by positivity
      simp only [fc2kWideRight, ↓reduceIte]
      linarith
  · rintro ⟨i, s₁⟩ ⟨j, s₂⟩ hne
    cases s₁ <;> cases s₂
    · have hij : i.val ≠ j.val := fun h => hne (Prod.ext (Fin.ext h) rfl)
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · left
        have hle : ((i.val + 1 : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hlt
        have hm := mul_le_mul_of_nonneg_right hle hδX.le
        simp only [fc2kWideRight, fc2kWideLeft, Bool.false_eq_true, ↓reduceIte]
        linarith
      · right
        have hle : ((j.val + 1 : ℕ) : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hgt
        have hm := mul_le_mul_of_nonneg_right hle hδX.le
        simp only [fc2kWideRight, fc2kWideLeft, Bool.false_eq_true, ↓reduceIte]
        linarith
    · exact Or.inl (hcross_all i j)
    · exact Or.inr (hcross_all j i)
    · have hij : i.val ≠ j.val := fun h => hne (Prod.ext (Fin.ext h) rfl)
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · right
        have hle : ((i.val + 1 : ℕ) : ℝ) ≤ (j.val : ℝ) := by exact_mod_cast hlt
        have hm := mul_le_mul_of_nonneg_right hle hδX.le
        simp only [fc2kWideRight, fc2kWideLeft, ↓reduceIte]
        linarith
      · left
        have hle : ((j.val + 1 : ℕ) : ℝ) ≤ (i.val : ℝ) := by exact_mod_cast hgt
        have hm := mul_le_mul_of_nonneg_right hle hδX.le
        simp only [fc2kWideRight, fc2kWideLeft, ↓reduceIte]
        linarith
  · rintro ⟨i, side⟩
    cases side <;> simp only [fc2kWideLeft, fc2kWideRight, Bool.false_eq_true, ↓reduceIte] <;>
      push_cast <;> ring

/-- Every `MatchedValid` block in `fc2kWideLeft`/`fc2kWideRight` has positive even gap strictly
above `2 * m - ((1 / 250) + 2 * N * δ) * X`, strictly below `X`, and both pair sums within `δ * X` of `2 * m`. -/
theorem fc2kWide_matched_block_bounds {n N : ℕ} (m δ : ℝ)
    (hX : (500 : ℝ) ≤ (poolMaximum n : ℝ)) (hδ : 0 < δ)
    (hsep_mid : ((1 / 250 : ℝ) + 2 * (N : ℝ) * δ) * (poolMaximum n : ℝ) ≤ 2 * m)
    (hm_hi : 2 * m < (poolMaximum n : ℝ))
    {block : DoublePair}
    (hmatched : block.MatchedValid
      (bmorLowBins (fc2kWideLeft (N := N) m (poolMaximum n) δ) (fc2kWideRight (N := N) m (poolMaximum n) δ))
      (bmorHighBins (fc2kWideLeft (N := N) m (poolMaximum n) δ) (fc2kWideRight (N := N) m (poolMaximum n) δ))) :
    let X : ℝ := poolMaximum n
    0 < block.high₁ - block.low₁ ∧
      2 ∣ block.high₁ - block.low₁ ∧
      2 * m - ((1 / 250 : ℝ) + 2 * (N : ℝ) * δ) * X < ((block.high₁ - block.low₁ : ℕ) : ℝ) ∧
      ((block.high₁ - block.low₁ : ℕ) : ℝ) < X ∧
      |((block.low₁ + block.high₁ : ℕ) : ℝ) - 2 * m| ≤ δ * X ∧
      |((block.low₂ + block.high₂ : ℕ) : ℝ) - 2 * m| ≤ δ * X := by
  let X : ℝ := poolMaximum n
  have hδX : 0 < δ * X := by dsimp [X]; positivity
  obtain ⟨hb1, hbc, hcX, _, _, _⟩ :=
    fc2kWide_interval_props (N := N) m X δ hX hδ hsep_mid (le_of_lt hm_hi)
  rcases hmatched with ⟨hval, ⟨i₁, hl₁, hh₁⟩, ⟨i₂, hl₂, hh₂⟩⟩
  have hl₁_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i₁, false)])
    (by linarith [hb1 (i₁, false), hbc (i₁, false)]) block.low₁).mp hl₁
  have hh₁_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i₁, true)])
    (by linarith [hb1 (i₁, true), hbc (i₁, true)]) block.high₁).mp hh₁
  have hl₂_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i₂, false)])
    (by linarith [hb1 (i₂, false), hbc (i₂, false)]) block.low₂).mp hl₂
  have hh₂_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i₂, true)])
    (by linarith [hb1 (i₂, true), hbc (i₂, true)]) block.high₂).mp hh₂
  have ho₁ : block.low₁ < block.high₁ := hval.2.2.2.2.2.2.1
  have hl₁_odd : Odd block.low₁ := by
    have hm2 : block.low₁ % 2 = 1 := by exact_mod_cast hl₁_int.2.2.2
    exact Nat.odd_iff.mpr hm2
  have hh₁_odd : Odd block.high₁ := by
    have hm2 : block.high₁ % 2 = 1 := by exact_mod_cast hh₁_int.2.2.2
    exact Nat.odd_iff.mpr hm2
  have heven : 2 ∣ block.high₁ - block.low₁ := by
    obtain ⟨u, hu⟩ := hl₁_odd
    obtain ⟨v, hv⟩ := hh₁_odd
    apply Nat.dvd_of_mod_eq_zero
    omega
  have hsub_cast : ((block.high₁ - block.low₁ : ℕ) : ℝ) = (block.high₁ : ℝ) - block.low₁ :=
    Nat.cast_sub (le_of_lt ho₁)
  have hi₁_le : ((i₁.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i₁.isLt
  have hmul_i₁ := mul_le_mul_of_nonneg_right hi₁_le hδX.le
  simp only [fc2kWideLeft, fc2kWideRight, Bool.false_eq_true, ↓reduceIte] at hl₁_int hh₁_int hl₂_int hh₂_int
  refine ⟨by omega, heven, ?_, ?_, ?_, ?_⟩
  · rw [hsub_cast]
    nlinarith [hl₁_int.2.2.1, hh₁_int.2.1]
  · rw [hsub_cast]
    have hl₁_pos : (0 : ℝ) < block.low₁ := by exact_mod_cast hl₁_int.1.pos
    have hi0 : (0 : ℝ) ≤ (i₁.val : ℝ) * (δ * X) := by positivity
    linarith [hh₁_int.2.2.1]
  · rw [Nat.cast_add, abs_le]
    push_cast at hl₁_int hh₁_int
    exact ⟨by linarith [hl₁_int.2.1, hh₁_int.2.1], by linarith [hl₁_int.2.2.1, hh₁_int.2.2.1]⟩
  · rw [Nat.cast_add, abs_le]
    push_cast at hl₂_int hh₂_int
    exact ⟨by linarith [hl₂_int.2.1, hh₂_int.2.1], by linarith [hl₂_int.2.2.1, hh₂_int.2.2.1]⟩

/-- Any integer `v` satisfying `((1 / 500) + N * δ) * X < v` and `v ≤ 2 * m - ((1 / 500) + N * δ) * X`
lies outside every `fc2kWideLeft`/`fc2kWideRight` bin. -/
theorem fc2kWide_not_mem_bins {N : ℕ} {m X δ : ℝ}
    (hX : (500 : ℝ) ≤ X) (hδ : 0 < δ)
    (hsep_mid : ((1 / 250 : ℝ) + 2 * (N : ℝ) * δ) * X ≤ 2 * m)
    (hm_hi : 2 * m ≤ X) {v : ℕ}
    (hv_lo : ((1 / 500 : ℝ) + (N : ℝ) * δ) * X < (v : ℝ))
    (hv_hi : (v : ℝ) ≤ 2 * m - ((1 / 500 : ℝ) + (N : ℝ) * δ) * X) :
    v ∉ Finset.univ.biUnion (bmorLowBins (fc2kWideLeft (N := N) m X δ) (fc2kWideRight m X δ)) ∪
      Finset.univ.biUnion (bmorHighBins (fc2kWideLeft (N := N) m X δ) (fc2kWideRight m X δ)) := by
  have hδX : 0 < δ * X := by positivity
  obtain ⟨hb1, hbc, _, _, _, _⟩ := fc2kWide_interval_props (N := N) m X δ hX hδ hsep_mid hm_hi
  intro hmem
  rcases Finset.mem_union.mp hmem with hlow | hhigh
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hlow
    have hv_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i, false)])
      (by linarith [hb1 (i, false), hbc (i, false)]) v).mp hi
    have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i.isLt
    have hm := mul_le_mul_of_nonneg_right hi1 hδX.le
    simp only [fc2kWideRight, Bool.false_eq_true, ↓reduceIte] at hv_int
    nlinarith [hv_int.2.2.1]
  · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hhigh
    have hv_int := (mem_apInterval_iff _ _ 2 1 (by linarith [hb1 (i, true)])
      (by linarith [hb1 (i, true), hbc (i, true)]) v).mp hi
    have hi1 : ((i.val + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast i.isLt
    have hm := mul_le_mul_of_nonneg_right hi1 hδX.le
    simp only [fc2kWideLeft, ↓reduceIte] at hv_int
    nlinarith [hv_int.2.1]

/-- Role index type for `2 * W_diag` Wide diagonal rectangles and `W_ord` 3-layer Wide stages. -/
abbrev FC2KWideInputs (W_ord W_diag n : ℕ) :=
  (Fin (2 * W_diag) × Fin 4) ⊕ ((Fin W_ord × (Fin 3 × Fin n)) × (Bool × Bool))

/-- Corner index for an ordinary double-block slot (`false` = row network pair 0, `true` = col network pair 1). -/
def fc2kWideOrdCorner : Bool → Bool → Fin 4
  | false, false => 0
  | false, true  => 1
  | true,  false => 3
  | true,  true  => 2

theorem fc2kWideOrdCorner_injective {n₁ n₂ s₁ s₂ : Bool}
    (h : fc2kWideOrdCorner n₁ s₁ = fc2kWideOrdCorner n₂ s₂) : n₁ = n₂ ∧ s₁ = s₂ := by
  cases n₁ <;> cases n₂ <;> cases s₁ <;> cases s₂ <;> simp_all [fc2kWideOrdCorner]

/-- Bijection from `FC2KWideInputs W_ord W_diag n` onto `Fin (2 * W_diag + W_ord * (3 * n)) × Fin 4`. -/
def fc2kWideFlatSlot {W_ord W_diag n : ℕ} (x : FC2KWideInputs W_ord W_diag n) :
    Fin (2 * W_diag + W_ord * (3 * n)) × Fin 4 :=
  match x with
  | .inl (t, side) => (⟨t.val, by omega⟩, side)
  | .inr ((j, (l, e)), (net, side)) =>
      let ordIdx := finProdFinEquiv (j, finProdFinEquiv (l, e))
      (⟨2 * W_diag + ordIdx.val, by have := ordIdx.isLt; omega⟩, fc2kWideOrdCorner net side)

theorem fc2kWideFlatSlot_bijective (W_ord W_diag n : ℕ) :
    Function.Bijective (fc2kWideFlatSlot (W_ord := W_ord) (W_diag := W_diag) (n := n)) := by
  have hinj : Function.Injective (fc2kWideFlatSlot (W_ord := W_ord) (W_diag := W_diag) (n := n)) := by
    rintro (⟨t₁, c₁⟩ | ⟨⟨j₁, l₁, e₁⟩, net₁, s₁⟩) (⟨t₂, c₂⟩ | ⟨⟨j₂, l₂, e₂⟩, net₂, s₂⟩) heq
    · have ht : t₁ = t₂ := Fin.ext (congrArg (fun z => z.1.val) heq)
      have hc : c₁ = c₂ := congrArg Prod.snd heq
      subst ht hc; rfl
    · have hv := congrArg (fun z => z.1.val) heq
      dsimp [fc2kWideFlatSlot] at hv
      omega
    · have hv := congrArg (fun z => z.1.val) heq
      dsimp [fc2kWideFlatSlot] at hv
      omega
    · have hv := congrArg (fun z => z.1.val) heq
      have hc := congrArg Prod.snd heq
      dsimp [fc2kWideFlatSlot] at hv hc
      obtain ⟨hnet, hs⟩ := fc2kWideOrdCorner_injective hc
      have hord : finProdFinEquiv (j₁, finProdFinEquiv (l₁, e₁)) =
          finProdFinEquiv (j₂, finProdFinEquiv (l₂, e₂)) := Fin.ext (by omega)
      have hp1 := finProdFinEquiv.injective hord
      have hj : j₁ = j₂ := congrArg Prod.fst hp1
      have hp2 := finProdFinEquiv.injective (congrArg Prod.snd hp1)
      have hl : l₁ = l₂ := congrArg Prod.fst hp2
      have he : e₁ = e₂ := congrArg Prod.snd hp2
      subst hj hl he hnet hs; rfl
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨hinj, ?_⟩
  simp only [FC2KWideInputs, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

/-- Offset rectangle label in `Fin L` for Wide diagonal index `t : Fin (2 * W_diag)`. -/
def fc2kWideRectLabel {offset W_diag L : ℕ} (hoff : offset + 2 * W_diag ≤ L)
    (t : Fin (2 * W_diag)) : Fin L :=
  ⟨offset + t.val, by omega⟩

theorem fc2kWideRectLabel_injective {offset W_diag L : ℕ} (hoff : offset + 2 * W_diag ≤ L) :
    Function.Injective (fc2kWideRectLabel hoff) := by
  intro a b h
  have hv := congrArg Fin.val h
  dsimp [fc2kWideRectLabel] at hv
  exact Fin.ext (by omega)

/-- Layer/edge/side index in `Fin m × (Fin n × Bool)` for `m = W_ord * 3`. -/
def fc2kWideLayerSlot {W_ord n m : ℕ} (hlen : m = W_ord * 3)
    (x : (Fin W_ord × (Fin 3 × Fin n)) × Bool) : Fin m × (Fin n × Bool) :=
  (Fin.cast hlen.symm (finProdFinEquiv (x.1.1, x.1.2.1)), (x.1.2.2, x.2))

theorem fc2kWideLayerSlot_injective {W_ord n m : ℕ} (hlen : m = W_ord * 3) :
    Function.Injective (fc2kWideLayerSlot (n := n) hlen) := by
  rintro ⟨⟨j₁, l₁, e₁⟩, s₁⟩ ⟨⟨j₂, l₂, e₂⟩, s₂⟩ h
  have hi := congrArg Prod.fst h
  have he := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.1) h
  have hs := congrArg (fun z : Fin m × (Fin n × Bool) => z.2.2) h
  have hjl := finProdFinEquiv.injective (Fin.cast_injective hlen.symm hi)
  cases hjl; cases he; cases hs; rfl

/-- Physical cell in `Cell n` assigned to each `FC2KWideInputs W_ord W_diag n` role. -/
def fc2kWidePhysicalCells {W_ord W_diag offset L n : ℕ}
    (hoff : offset + 2 * W_diag ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = W_ord * 3) (hwc : wc.length = W_ord * 3) :
    FC2KWideInputs W_ord W_diag n → Cell n
  | .inl (t, side) => packedRectangleCorner hs choice (fc2kWideRectLabel hoff t, side)
  | .inr (x, (net, side)) =>
      if net then (LayerPacking.sequenceCell wc (fc2kWideLayerSlot hwc (x, side))).swap
      else LayerPacking.sequenceCell wr (fc2kWideLayerSlot hwr (x, side))

theorem fc2kWidePhysicalCells_geometry {W_ord W_diag offset L n : ℕ}
    (hoff : offset + 2 * W_diag ≤ L) (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (base prior : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base)
    (hprior : prior ⊆ base)
    (hdiagfree : ∀ x : Fin (2 * W_diag) × Fin 4,
      packedRectangleCorner hs choice (fc2kWideRectLabel hoff x.1, x.2) ∉ prior)
    (wr wc : List (LayerPacking.Layer n))
    (hwr : wr.length = W_ord * 3) (hwc : wc.length = W_ord * 3)
    (hrows : LayerPacking.PackedLayers base wr)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport wr)) wc)
    (hdisjoint : Disjoint (LayerPacking.layersSupport wr)
      (LayerPacking.transposeCells (LayerPacking.layersSupport wc))) :
    Function.Injective (fc2kWidePhysicalCells hoff hs choice wr wc hwr hwc) ∧
      (∀ x, fc2kWidePhysicalCells hoff hs choice wr wc hwr hwc x ∉ prior) := by
  have hrmem : ∀ x, LayerPacking.sequenceCell wr x ∈ LayerPacking.layersSupport wr := by
    intro x
    exact LayerPacking.layerSupport_subset (wr.get x.1) wr (List.get_mem wr x.1)
      (LayerPacking.sequenceCell_mem wr x.1 x.2)
  have hcmem : ∀ x, (LayerPacking.sequenceCell wc x).swap ∈
      LayerPacking.transposeCells (LayerPacking.layersSupport wc) := by
    intro x
    exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset (wc.get x.1) wc
      (List.get_mem wc x.1) (LayerPacking.sequenceCell_mem wc x.1 x.2), rfl⟩
  have hordFree : ∀ (a : Fin W_ord × (Fin 3 × Fin n)) (net side : Bool),
      fc2kWidePhysicalCells hoff hs choice wr wc hwr hwc (.inr (a, (net, side))) ∉ base := by
    intro a net side
    cases net
    · exact hrows.sequenceCell_unreserved _
    · intro hm
      exact (hcols.transposed_support_safe _ (hcmem _)).1 (Finset.mem_union_left _ hm)
  have hdiagInBase : ∀ x : Fin (2 * W_diag) × Fin 4,
      packedRectangleCorner hs choice (fc2kWideRectLabel hoff x.1, x.2) ∈ base := by
    intro x
    apply hrectbase
    exact Finset.mem_image.mpr ⟨(fc2kWideRectLabel hoff x.1, x.2), Finset.mem_univ _, rfl⟩
  refine ⟨?_, ?_⟩
  · rintro (x | ⟨a₁, net₁, s₁⟩) (y | ⟨a₂, net₂, s₂⟩) heq
    · dsimp [fc2kWidePhysicalCells] at heq
      have hpc := packedRectangleCorner_injective hs choice heq
      exact congrArg Sum.inl (Prod.ext
        (fc2kWideRectLabel_injective hoff (Prod.mk.inj hpc).1) (Prod.mk.inj hpc).2)
    · exact False.elim (hordFree a₂ net₂ s₂ (heq ▸ hdiagInBase x))
    · exact False.elim (hordFree a₁ net₁ s₁ (heq.symm ▸ hdiagInBase y))
    · cases net₁ <;> cases net₂
      · dsimp [fc2kWidePhysicalCells] at heq
        have hidx := (fc2kWideLayerSlot_injective hwr) (hrows.sequenceCell_injective heq)
        cases hidx; rfl
      · dsimp [fc2kWidePhysicalCells] at heq
        exact False.elim (Finset.disjoint_left.mp hdisjoint (hrmem _) (heq ▸ hcmem _))
      · dsimp [fc2kWidePhysicalCells] at heq
        exact False.elim (Finset.disjoint_left.mp hdisjoint (heq ▸ hrmem _) (hcmem _))
      · dsimp [fc2kWidePhysicalCells] at heq
        have heq' : LayerPacking.sequenceCell wc (fc2kWideLayerSlot hwc (a₁, s₁)) =
            LayerPacking.sequenceCell wc (fc2kWideLayerSlot hwc (a₂, s₂)) := by
          simpa only [Prod.swap_swap] using congrArg Prod.swap heq
        have hidx := (fc2kWideLayerSlot_injective hwc) (hcols.sequenceCell_injective heq')
        cases hidx; rfl
  · rintro (x | ⟨a, net, s⟩)
    · exact hdiagfree x
    · exact fun hp => hordFree a net s (hprior hp)

end

end Sude
