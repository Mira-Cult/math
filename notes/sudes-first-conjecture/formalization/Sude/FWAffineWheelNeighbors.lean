import Sude.FWWheelShortPairs

/-! Conditional AW2 transfer from uniform finite wheel discrepancy to actual
screened-prime short neighbors. See `problems/prime-line-sums/manuscripts/
cutoff2_affine_wheel_prefix.md`, AW1--AW2. This proves neither discrepancy
for a particular wheel nor a pair-supply or growth-trace assertion. -/
namespace Sude
noncomputable section

/-- An upper discrepancy bound on each initial positive unit interval. -/
def FWAffineWheelDiscrepancy (W : ℕ) (rho C : ℝ) : Prop :=
  ∀ a K : ℕ, Nat.Coprime a W →
    (((Finset.Icc 1 K).filter (fun j => Nat.Coprime (a + j) W)).card : ℝ) ≤
      rho * K + C

/-- Actual same-parity upper endpoints whose strictly positive gap is `< D`. -/
def fwAffineShortNeighbors (S : Finset ℕ) (p : ℕ) (D : ℝ) : Finset ℕ :=
  S.filter (fun q => p < q ∧ ((q - p : ℕ) : ℝ) < D ∧ q % 2 = p % 2)

/-- AW2 for `g=2`: the strict real endpoint is preserved, including when
`D/2` is integral. The discrepancy premise is explicit. -/
theorem fw_affine_short_neighbors_bound
    (S : Finset ℕ) (p W : ℕ) (D rho C : ℝ)
    (hWodd : W % 2 = 1) (hpodd : p % 2 = 1) (hp : Nat.Coprime p W)
    (hS : ∀ q ∈ S, Nat.Coprime q W)
    (hD : 0 < D) (hrho : 0 < rho) (hdisc : FWAffineWheelDiscrepancy W rho C) :
    ((fwAffineShortNeighbors S p D).card : ℝ) < rho * D / 2 + C := by
  obtain ⟨a, _, ha, htranslate⟩ := fw_wheel_half_unit hWodd hpodd hp
  let K : ℕ := ⌈D / 2⌉₊ - 1
  let window := (Finset.Icc 1 K).filter (fun j => Nat.Coprime (a + j) W)
  have hinj : (fwAffineShortNeighbors S p D).card ≤ window.card := by
    apply Finset.card_le_card_of_injOn (fun q => (q - p) / 2)
    · intro q hq
      obtain ⟨hqS, hpq, hqD, hparity⟩ := Finset.mem_filter.mp hq
      have heq : p + 2 * ((q - p) / 2) = q := by omega
      have hj : (((q - p) / 2 : ℕ) : ℝ) < D / 2 := by
        have heq' : (2 * ((q - p) / 2) : ℕ) = q - p := by omega
        have heqr : (2 : ℝ) * (((q - p) / 2 : ℕ) : ℝ) = ((q - p : ℕ) : ℝ) := by exact_mod_cast heq'
        linarith
      have hjlt : (q - p) / 2 < ⌈D / 2⌉₊ := Nat.lt_ceil.mpr hj
      have hunit : Nat.Coprime (a + (q - p) / 2) W := by
        apply htranslate
        simpa [heq] using hS q hqS
      change (q - p) / 2 ∈ window
      simp only [window, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by dsimp [K]; omega⟩, hunit⟩
    · intro q hq r hr heq
      change (q - p) / 2 = (r - p) / 2 at heq
      have hq' := (Finset.mem_filter.mp hq).2
      have hr' := (Finset.mem_filter.mp hr).2
      have hqeq : p + 2 * ((q - p) / 2) = q := by omega
      have hreq : p + 2 * ((r - p) / 2) = r := by omega
      omega
  have hKpos : 0 < ⌈D / 2⌉₊ := Nat.ceil_pos.mpr (by linarith)
  have hKlt : (K : ℝ) < D / 2 := by
    have hn : K < ⌈D / 2⌉₊ := by dsimp [K]; omega
    exact Nat.lt_ceil.mp hn
  have hb := hdisc a K ha
  have hc : ((fwAffineShortNeighbors S p D).card : ℝ) ≤ (window.card : ℝ) := by exact_mod_cast hinj
  have hmul : rho * (K : ℝ) < rho * (D / 2) := mul_lt_mul_of_pos_left hKlt hrho
  dsimp [window] at hc
  linarith

/-- AW2 summed over the actual finite pair population. The nonempty premise
is needed only for the strict total inequality. -/
theorem fw_affine_short_pair_count
    (S : Finset ℕ) (P : Finset (ℕ × ℕ)) (W : ℕ) (D rho C : ℝ)
    (hne : S.Nonempty) (hWodd : W % 2 = 1)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hP : ∀ z ∈ P, z.1 ∈ S ∧ z.2 ∈ S ∧ z.1 < z.2 ∧ z.2 % 2 = z.1 % 2)
    (hD : 0 < D) (hrho : 0 < rho) (hdisc : FWAffineWheelDiscrepancy W rho C) :
    (((P.filter fun z => ((z.2 - z.1 : ℕ) : ℝ) < D).card : ℝ)) <
      (S.card : ℝ) * (rho * D / 2 + C) := by
  classical
  let short := P.filter fun z => ((z.2 - z.1 : ℕ) : ℝ) < D
  let fiber : ℕ → Finset (ℕ × ℕ) := fun p => short.filter fun z => z.1 = p
  have hmap : ∀ z ∈ short, z.1 ∈ S := by
    intro z hz
    exact (hP z (Finset.mem_filter.mp hz).1).1
  have hcount : short.card = ∑ p ∈ S, (fiber p).card :=
    Finset.card_eq_sum_card_fiberwise (s := short) (t := S) (f := Prod.fst) hmap
  have hfiber : ∀ p ∈ S, (fiber p).card ≤ (fwAffineShortNeighbors S p D).card := by
    intro p hp
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro z hz
      have hzshort := (Finset.mem_filter.mp hz).1
      have hfirst := (Finset.mem_filter.mp hz).2
      obtain ⟨_, hzu, hlt, hparity⟩ := hP z (Finset.mem_filter.mp hzshort).1
      have hgap := (Finset.mem_filter.mp hzshort).2
      apply Finset.mem_filter.mpr
      subst p
      exact ⟨hzu, hlt, hgap, hparity⟩
    · intro x hx y hy heq
      have hxfirst := (Finset.mem_filter.mp hx).2
      have hyfirst := (Finset.mem_filter.mp hy).2
      exact Prod.ext (hxfirst.trans hyfirst.symm) heq
  have hlt : ∀ p ∈ S, ((fiber p).card : ℝ) < rho * D / 2 + C := by
    intro p hp
    have hc : ((fiber p).card : ℝ) ≤ (fwAffineShortNeighbors S p D).card := by
      exact_mod_cast hfiber p hp
    exact hc.trans_lt (fw_affine_short_neighbors_bound S p W D rho C hWodd
      (hS p hp).1 (hS p hp).2 (fun q hq => (hS q hq).2) hD hrho hdisc)
  have hsum := Finset.sum_lt_sum_of_nonempty hne hlt
  have hcountR : (short.card : ℝ) = ∑ p ∈ S, ((fiber p).card : ℝ) := by
    exact_mod_cast hcount
  rw [← hcountR] at hsum
  simpa [short, mul_add] using hsum

/-- All remaining screened pool primes are units for the first affine wheel
of the frozen recipe, obtained by adjoining 17 to 15015. -/
theorem fw_screened_prime_coprime_255255 (p : ℕ) (hp : Nat.Prime p) (hlarge : 43 < p) :
    Nat.Coprime p 255255 := by
  have hfactors : ∀ q ∈ ([3, 5, 7, 11, 13, 17] : List ℕ), Nat.Prime q ∧ q ≤ 43 := by decide
  simpa using fw_screened_prime_coprime_wheel [3, 5, 7, 11, 13, 17] p hp hlarge hfactors

end
end Sude
