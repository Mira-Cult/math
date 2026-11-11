import Sude.BTClassifiedPairs

/-! Concrete half-open spatial bins crossed with residue classes. -/
namespace Sude
noncomputable section

/-- Natural spatial-bin index and exact residue class. -/
def progressionBinKey (lo radius : ℝ) (g : ℕ) (p : ℕ) : ℕ × ℕ :=
  (⌊((p : ℝ) - lo) / radius⌋₊, p % g)

/-- Two ordered points in one bin have gap less than its real radius,
with the floor domain and the endpoints made explicit. -/
theorem same_spatial_bin_gap {lo radius : ℝ} {p q : ℕ}
    (hR : 0 < radius) (hp : lo ≤ p)
    (hbin : ⌊((p : ℝ) - lo) / radius⌋₊ = ⌊((q : ℝ) - lo) / radius⌋₊) :
    (q : ℝ) - p < radius := by
  have hp0 : 0 ≤ ((p : ℝ) - lo) / radius := div_nonneg (by linarith) hR.le
  have hlow := Nat.floor_le hp0
  have hhigh := Nat.lt_floor_add_one (((q : ℝ) - lo) / radius)
  rw [← hbin] at hhigh
  have hp' := (le_div_iff₀ hR).1 hlow
  have hq' := (div_lt_iff₀ hR).1 hhigh
  nlinarith

/-- A concrete bin/residue key has at most the product of the number of
spatial bins and the number of allowed residue classes. -/
theorem progression_bin_key_card (S classes : Finset ℕ) (lo W radius : ℝ) (g : ℕ)
    (hR : 0 < radius)
    (hinterval : ∀ p ∈ S, lo ≤ p ∧ (p : ℝ) ≤ lo + W)
    (hclasses : ∀ p ∈ S, p % g ∈ classes) :
    (S.image (progressionBinKey lo radius g)).card ≤ (⌊W / radius⌋₊ + 1) * classes.card := by
  classical
  let bins := Finset.range (⌊W / radius⌋₊ + 1)
  have hsub : S.image (progressionBinKey lo radius g) ⊆ bins.product classes := by
    intro z hz
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hp' := (hinterval p hp).2
      have hquot : ((p : ℝ) - lo) / radius ≤ W / radius := by
        exact div_le_div_of_nonneg_right (by linarith) hR.le
      have hfloor := Nat.floor_le_floor hquot
      change ⌊((p : ℝ) - lo) / radius⌋₊ < ⌊W / radius⌋₊ + 1
      omega
    · exact hclasses p hp
  calc
    _ ≤ (bins.product classes).card := Finset.card_le_card hsub
    _ = _ := by simp [bins, Finset.card_product]

/-- Same concrete key means a positive gap is divisible by the modulus,
no larger than the floor of the real radius, and lies in the same residue. -/
theorem progression_bin_key_pair {lo radius : ℝ} {g p q : ℕ}
    (hR : 0 < radius) (hp : lo ≤ p) (hpq : p < q)
    (hkey : progressionBinKey lo radius g p = progressionBinKey lo radius g q) :
    g ∣ q - p ∧ q - p ≤ ⌊radius⌋₊ ∧ (q : ℤ) % g = ((p % g : ℕ) : ℤ) % g := by
  have hbin := congrArg Prod.fst hkey
  have hmod := congrArg Prod.snd hkey
  have hgap := same_spatial_bin_gap hR hp hbin
  have hgapR : ((q - p : ℕ) : ℝ) ≤ radius := by
    rw [Nat.cast_sub (le_of_lt hpq)]
    linarith
  have hbound : q - p ≤ ⌊radius⌋₊ := (Nat.le_floor_iff hR.le).2 hgapR
  have hm : p ≡ q [MOD g] := hmod
  have hd : (g : ℤ) ∣ (q : ℤ) - p := hm.dvd
  rw [← Nat.cast_sub (le_of_lt hpq)] at hd
  have hdiv : g ∣ q - p := by exact_mod_cast hd
  have hres : (q : ℤ) % g = ((p % g : ℕ) : ℤ) % g := by
    rw [Int.natCast_mod]
    simp only [Int.emod_emod]
    exact_mod_cast hmod.symm
  exact ⟨hdiv, hbound, hres⟩

/-- BT2--BT5 on an actual interval and finite reduced residue classes.
The floor of the real bin radius is used only where an integer gap is
required; the number of bins is bounded with the original real radius. -/
theorem mv_common_gap_from_interval_classes (mv : MVBrunTitchmarsh)
    (unused classes : Finset ℕ) (lo W radius width ell : ℝ) (g Q : ℕ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + W)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hg : 0 < g) (hR : 0 < radius) (hwidth : (g : ℝ) < width)
    (hell : 0 < ell) (hexp : Real.exp ell ≤ width / g)
    (hgate : (((⌊radius⌋₊ / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient g : ℝ) * ell)) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊W / radius⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊radius⌋₊ ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  let key := progressionBinKey lo radius g
  let B := (⌊W / radius⌋₊ + 1) * classes.card
  have hB : (unused.image key).card ≤ B := progression_bin_key_card unused classes lo W radius g hR hinterval hclasses
  have hne' : unused.Nonempty := hne
  obtain ⟨p₀, hp₀⟩ := hne'
  have hclassespos : 0 < classes.card := Finset.card_pos.mpr ⟨p₀ % g, hclasses p₀ hp₀⟩
  have hBpos : 0 < B := Nat.mul_pos (by omega) hclassespos
  have hres : ∀ p ∈ unused, 0 < p % g ∧ Nat.Coprime g (p % g) := fun p hp => hreduced _ (hclasses p hp)
  have hkey : ∀ p ∈ unused, ∀ q ∈ unused, p < q → key p = key q →
      g ∣ q - p ∧ q - p ≤ ⌊radius⌋₊ ∧ (q : ℤ) % g = ((p % g : ℕ) : ℤ) % g := by
    intro p hp q hq hpq heq
    exact progression_bin_key_pair hR (hinterval p hp).1 hpq heq
  obtain ⟨h, T, hh, hdiv, hRbound, hDbound, hQ, hT, hmatch⟩ :=
    mv_common_gap_from_fiber_partition mv unused key g g ⌊radius⌋₊ Q B (fun p => p % g) width ell
      hne hprimes hres hkey hB hBpos hg hg hwidth hell hexp hgate
  exact ⟨h, T, hh, hdiv, hRbound, hDbound, hQ, fun p hp => ⟨(hT p hp).1, (hT p hp).2.1⟩, hmatch⟩

end
end Sude
