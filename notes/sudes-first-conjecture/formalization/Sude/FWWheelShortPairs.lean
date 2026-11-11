import Sude.FWWheelEnumeration

/-! Exact wheel bounds on supplied finite collections of screened pairs.
The wheel cutoff is from WW1--WW2; WW3 uses these bounds when subtracting
short same-class pairs. This module does not assert a pair supply or trace. -/
namespace Sude
noncomputable section

/-- Upper endpoints of positive same-parity differences strictly below h. -/
def fwWheelShortNeighbors (S : Finset ℕ) (p h : ℕ) : Finset ℕ :=
  S.filter (fun q => p < q ∧ q - p < h ∧ q % 2 = p % 2)

/-- A screened unit p determines an actual natural representative a of p/2
modulo an odd wheel. This does not require choosing a modular inverse. -/
theorem fw_wheel_half_unit {W p : ℕ} (hWodd : W % 2 = 1)
    (hpodd : p % 2 = 1) (hp : Nat.Coprime p W) :
    ∃ a : ℕ, 2 * a = p + W ∧ Nat.Coprime a W ∧
      ∀ j : ℕ, Nat.Coprime (p + 2 * j) W → Nat.Coprime (a + j) W := by
  let a := (p + W) / 2
  have heq : 2 * a = p + W := by dsimp [a]; omega
  have ha' : Nat.Coprime (2 * a) W := by
    rw [heq, Nat.coprime_add_self_left]
    exact hp
  have ha : Nat.Coprime a W := (Nat.coprime_mul_iff_left.mp ha').2
  refine ⟨a, heq, ha, ?_⟩
  intro j hq
  have hq' : Nat.Coprime (2 * (a + j)) W := by
    have heq' : 2 * (a + j) = (p + 2 * j) + W := by omega
    rw [heq', Nat.coprime_add_self_left]
    exact hq
  exact (Nat.coprime_mul_iff_left.mp hq').2

/-- At a supplied odd, wheel-coprime lower endpoint, there are at most T
wheel-coprime, same-parity upper endpoints with difference `< h`, provided
`h ≤ 2*k_W(T)`. Endpoints at equality are not counted as short. -/
theorem fw_wheel_short_neighbors_bound (S : Finset ℕ) (p W T h : ℕ)
    (hW : 0 < W) (hWodd : W % 2 = 1) (hpodd : p % 2 = 1)
    (hp : Nat.Coprime p W) (hS : ∀ q ∈ S, Nat.Coprime q W)
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)) :
    (fwWheelShortNeighbors S p h).card ≤ T := by
  obtain ⟨a, _, ha, htranslate⟩ := fw_wheel_half_unit hWodd hpodd hp
  let window := (Finset.Ico 1 (fwWheelWindowCutoff (fwWheelUnit W) W
      (Nat.totient W) T (Nat.totient_pos.mpr hW))).filter
        (fun j => Nat.Coprime (a + j) W)
  have hinj : (fwWheelShortNeighbors S p h).card ≤ window.card := by
    apply Finset.card_le_card_of_injOn (fun q => (q - p) / 2)
    · intro q hq
      have hq' := Finset.mem_filter.mp hq
      obtain ⟨hpq, hshort, hparity⟩ := hq'.2
      have heq : p + 2 * ((q - p) / 2) = q := by omega
      have hunit : Nat.Coprime (a + (q - p) / 2) W := by
        apply htranslate
        simpa [heq] using hS q hq'.1
      change (q - p) / 2 ∈ window
      simp only [window, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩, hunit⟩
    · intro q hq r hr heq
      change (q - p) / 2 = (r - p) / 2 at heq
      have hq' := (Finset.mem_filter.mp hq).2
      have hr' := (Finset.mem_filter.mp hr).2
      have hqeq : p + 2 * ((q - p) / 2) = q := by omega
      have hreq : p + 2 * ((r - p) / 2) = r := by omega
      omega
  exact hinj.trans (fw_wheel_window_bound_of_pos W T a hW ha)

/-- Ordered pairs in S with same parity and positive difference below h. -/
def fwWheelShortPairs (S : Finset ℕ) (h : ℕ) : Finset (ℕ × ℕ) :=
  S.biUnion (fun p => (fwWheelShortNeighbors S p h).image (fun q => (p, q)))

/-- The full short-pair charge is at most `|S|*T`, without requiring
independence or disjointness between possible pairs. -/
theorem fw_wheel_short_pairs_bound (S : Finset ℕ) (W T h : ℕ)
    (hW : 0 < W) (hWodd : W % 2 = 1)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)) :
    (fwWheelShortPairs S h).card ≤ S.card * T := by
  unfold fwWheelShortPairs
  apply Finset.card_biUnion_le_card_mul S _ T
  intro p hp
  exact Finset.card_image_le.trans (fw_wheel_short_neighbors_bound S p W T h hW hWodd
    (hS p hp).1 (hS p hp).2 (fun q hq => (hS q hq).2) hcut)

/-- Every prime greater than the prime factors in a supplied wheel product is
a unit; no prime-distribution estimate is used. -/
theorem fw_screened_prime_coprime_wheel (factors : List ℕ) (p : ℕ)
    (hp : Nat.Prime p) (hlarge : 43 < p)
    (hfactors : ∀ q ∈ factors, Nat.Prime q ∧ q ≤ 43) :
    Nat.Coprime p factors.prod := by
  apply Nat.coprime_list_prod_right_iff.mpr
  intro q hq
  exact (Nat.coprime_primes hp (hfactors q hq).1).2 (by have := (hfactors q hq).2; omega)

/-- The first frozen exact-window wheel has product 15015. -/
theorem fw_screened_prime_coprime_15015 (p : ℕ) (hp : Nat.Prime p) (hlarge : 43 < p) :
    Nat.Coprime p 15015 := by
  have hfactors : ∀ q ∈ ([3, 5, 7, 11, 13] : List ℕ), Nat.Prime q ∧ q ≤ 43 := by decide
  simpa using fw_screened_prime_coprime_wheel [3, 5, 7, 11, 13] p hp hlarge hfactors

/-- An actual screened prime set, including any subset obtained by deletions,
has at most `|S|*T` short ordered pairs for the first FW wheel. -/
theorem fw_screened_wheel_short_pairs (S : Finset ℕ) (T h : ℕ)
    (hS : ∀ p ∈ S, 43 < p ∧ Nat.Prime p)
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit 15015) 15015
      (Nat.totient 15015) T (Nat.totient_pos.mpr (by decide))) :
    (fwWheelShortPairs S h).card ≤ S.card * T := by
  apply fw_wheel_short_pairs_bound S 15015 T h (by decide) (by decide) _ hcut
  intro p hp
  obtain ⟨hbig, hprime⟩ := hS p hp
  exact ⟨(hprime.mod_two_eq_one_iff_ne_two).2 (by omega),
    fw_screened_prime_coprime_15015 p hprime hbig⟩

/-- Subtracting the short pairs from any supplied finite ordered pair set
leaves at least its cardinality minus `|S|*T` pairs of difference at least h.
The endpoint conditions are explicit; this asserts no lower bound on P. -/
theorem fw_wheel_long_pairs_after_short_removal (S : Finset ℕ) (P : Finset (ℕ × ℕ))
    (W T h : ℕ) (hW : 0 < W) (hWodd : W % 2 = 1)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hP : ∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧ x.2 % 2 = x.1 % 2)
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)) :
    P.card ≤ (P.filter (fun x => h ≤ x.2 - x.1)).card + S.card * T := by
  classical
  have hsub : P.filter (fun x => x.2 - x.1 < h) ⊆ fwWheelShortPairs S h := by
    intro x hx
    obtain ⟨hxP, hshort⟩ := Finset.mem_filter.mp hx
    obtain ⟨hp, hq, hpq, hparity⟩ := hP x hxP
    apply Finset.mem_biUnion.mpr
    refine ⟨x.1, hp, Finset.mem_image.mpr ?_⟩
    refine ⟨x.2, Finset.mem_filter.mpr ⟨hq, hpq, hshort, hparity⟩, ?_⟩
    exact Prod.eta x
  have hshort : (P.filter (fun x => x.2 - x.1 < h)).card ≤ S.card * T :=
    (Finset.card_le_card hsub).trans (fw_wheel_short_pairs_bound S W T h hW hWodd hS hcut)
  have hsplit := Finset.card_filter_add_card_filter_not (s := P) (fun x => x.2 - x.1 < h)
  have hlong : P.filter (fun x => ¬ x.2 - x.1 < h) =
      P.filter (fun x => h ≤ x.2 - x.1) := by
    congr 1
    funext x
    exact propext (not_lt)
  rw [hlong] at hsplit
  omega

/-- The source WW5 integer cutoff is positive and no larger than the even
current certified radius; the actual selected gap need only be at least it. -/
theorem fw_wheel_ww5_cutoff_geometry (W T R : ℕ) (hW : 0 < W)
    (hR : 0 < R) (heven : 2 ∣ R) :
    let k := fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)
    let h := 2 * min k (R / 2)
    0 < h ∧ h ≤ R ∧ 2 ∣ h ∧ h ≤ 2 * k := by
  dsimp only
  have hk := fw_wheel_cutoff_pos_of_pos W T hW
  have hRhalf : 0 < R / 2 := by omega
  have hmin : 0 < min (fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)) (R / 2) := lt_min hk hRhalf
  have hminL := Nat.min_le_left (fwWheelWindowCutoff (fwWheelUnit W) W
      (Nat.totient W) T (Nat.totient_pos.mpr hW)) (R / 2)
  have hminR := Nat.min_le_right (fwWheelWindowCutoff (fwWheelUnit W) W
      (Nat.totient W) T (Nat.totient_pos.mpr hW)) (R / 2)
  refine ⟨by omega, by omega, ⟨_, rfl⟩, by omega⟩


end
end Sude
