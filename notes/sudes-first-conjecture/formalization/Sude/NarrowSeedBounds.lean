import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! NS1–NS3: exact width estimates for the retained seed groups. -/
namespace Sude
noncomputable section

/-- The retained widths and the discarded widths have the source's budget
whenever every discarded width is at least the maximum retained width.
`kept` and `dropped` are the actual selected group labels. -/
theorem narrow_seed_width_budget {ι : Type*} (kept dropped : Finset ι)
    (width : ι → ℝ) (X z : ℝ) (t : ℕ)
    (ht : 2 ≤ t) (hz : 0 ≤ z)
    (hk : ∀ i ∈ kept, 0 ≤ width i ∧ width i ≤ z)
    (hd : ∀ i ∈ dropped, z ≤ width i)
    (hdcard : dropped.card = t - 1)
    (hmax : ∃ i ∈ kept, width i = z)
    (hsum : (∑ i ∈ kept, width i) + (∑ i ∈ dropped, width i) ≤ X) :
    (∑ i ∈ kept, width i ^ 2) ≤ X ^ 2 / (4 * ((t : ℝ) - 1)) ∧
      z ^ 2 ≤ X ^ 2 / (t : ℝ) ^ 2 := by
  classical
  have htR : (1 : ℝ) < t := by exact_mod_cast ht
  have htminus : (0 : ℝ) < t - 1 := by linarith
  have htdiff : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hdrop : ((t : ℝ) - 1) * z ≤ ∑ i ∈ dropped, width i := by
    have h := Finset.sum_le_sum hd
    simpa [hdcard, htdiff, mul_comm] using h
  have hksum : 0 ≤ ∑ i ∈ kept, width i :=
    Finset.sum_nonneg fun i hi => (hk i hi).1
  have hbudget : (∑ i ∈ kept, width i) + ((t : ℝ) - 1) * z ≤ X := by linarith
  have hsumz : z ≤ ∑ i ∈ kept, width i := by
    obtain ⟨i, hi, heq⟩ := hmax
    rw [← heq]
    exact Finset.single_le_sum (fun j hj => (hk j hj).1) hi
  have htz : (t : ℝ) * z ≤ X := by nlinarith
  have hsq : (∑ i ∈ kept, width i ^ 2) ≤ z * (∑ i ∈ kept, width i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := hk i hi
    nlinarith
  have hsq2 : (∑ i ∈ kept, width i ^ 2) ≤ z * (X - ((t : ℝ) - 1) * z) :=
    hsq.trans (mul_le_mul_of_nonneg_left (by linarith : (∑ i ∈ kept, width i) ≤ X - ((t : ℝ) - 1) * z) hz)
  have hX : 0 ≤ X := by nlinarith
  have h1 : (∑ i ∈ kept, width i ^ 2) ≤ X ^ 2 / (4 * ((t : ℝ) - 1)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((t : ℝ) - 1))).2
    have hmul := mul_le_mul_of_nonneg_left hsq2 (show (0 : ℝ) ≤ 4 * ((t : ℝ) - 1) by positivity)
    have hsquare := sq_nonneg (X - 2 * ((t : ℝ) - 1) * z)
    nlinarith
  have h2 : z ^ 2 ≤ X ^ 2 / (t : ℝ) ^ 2 := by
    have htpos : (0 : ℝ) < t := by linarith
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (t : ℝ) ^ 2)).2
    have hprod : (t : ℝ) * z ≤ X := htz
    have hsq' := sq_le_sq₀ (mul_nonneg htpos.le hz) hX |>.2 hprod
    nlinarith
  exact ⟨h1, h2⟩

/-- Select exactly `k` group labels of least width, including ties. -/
theorem exists_narrowest_seed_groups {ι : Type*} [DecidableEq ι] (all : Finset ι)
    (width : ι → ℝ) (k : ℕ) (hk : k ≤ all.card) :
    ∃ kept : Finset ι, kept ⊆ all ∧ kept.card = k ∧
      ∀ i ∈ kept, ∀ j ∈ all \ kept, width i ≤ width j := by
  classical
  have hnon : (all.powersetCard k).Nonempty := Finset.powersetCard_nonempty.mpr hk
  obtain ⟨kept, hkept, hmin⟩ := Finset.exists_min_image (all.powersetCard k)
    (fun group => ∑ i ∈ group, width i) hnon
  have hinfo := Finset.mem_powersetCard.mp hkept
  refine ⟨kept, hinfo.1, hinfo.2, ?_⟩
  intro i hi j hj
  have hjall : j ∈ all := (Finset.mem_sdiff.mp hj).1
  have hjnot : j ∉ kept := (Finset.mem_sdiff.mp hj).2
  let swapped := insert j (kept.erase i)
  have hjnoterase : j ∉ kept.erase i := by
    intro h
    exact hjnot (Finset.mem_erase.mp h).2
  have hswapcard : swapped.card = k := by
    dsimp [swapped]
    rw [Finset.card_insert_of_notMem hjnoterase]
    have h := Finset.card_erase_add_one hi
    omega
  have hswapsub : swapped ⊆ all := by
    intro x hx
    simp only [swapped, Finset.mem_insert, Finset.mem_erase] at hx
    rcases hx with rfl | ⟨_, hx⟩
    · exact hjall
    · exact hinfo.1 hx
  have hs := hmin swapped (Finset.mem_powersetCard.mpr ⟨hswapsub, hswapcard⟩)
  dsimp [swapped] at hs
  rw [Finset.sum_insert hjnoterase] at hs
  have he := Finset.sum_erase_add kept width hi
  linarith

/-- NS selection and squared-width bound for actual labelled groups. This
retains exactly `s` groups and permits equal widths. -/
theorem narrowest_seed_groups_bound {ι : Type*} [DecidableEq ι]
    (all : Finset ι) (width : ι → ℝ) (X : ℝ) (s t : ℕ)
    (hs : 0 < s) (ht : 2 ≤ t) (hcard : all.card = s + t - 1)
    (hnonneg : ∀ i ∈ all, 0 ≤ width i)
    (hsum : (∑ i ∈ all, width i) ≤ X) :
    ∃ kept : Finset ι, kept ⊆ all ∧ kept.card = s ∧
      (∑ i ∈ kept, width i ^ 2) ≤ X ^ 2 / (4 * ((t : ℝ) - 1)) ∧
      ∀ i ∈ kept, width i ^ 2 ≤ X ^ 2 / (t : ℝ) ^ 2 := by
  classical
  have hsle : s ≤ all.card := by omega
  obtain ⟨kept, hsub, hkept, horder⟩ := exists_narrowest_seed_groups all width s hsle
  have hnon : kept.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image kept width hnon
  let z := width i
  have hz : 0 ≤ z := hnonneg i (hsub hi)
  have hk : ∀ j ∈ kept, 0 ≤ width j ∧ width j ≤ z := by
    intro j hj
    exact ⟨hnonneg j (hsub hj), hmax j hj⟩
  have hd : ∀ j ∈ all \ kept, z ≤ width j := by
    intro j hj
    exact horder i hi j hj
  have hdropcard : (all \ kept).card = t - 1 := by
    have h := Finset.card_sdiff_add_card_eq_card hsub
    omega
  have hsum' : (∑ j ∈ kept, width j) + (∑ j ∈ all \ kept, width j) ≤ X := by
    have h := Finset.sum_sdiff (f := width) hsub
    linarith
  obtain ⟨hbound, hmaxbound⟩ := narrow_seed_width_budget kept (all \ kept) width X z t
    ht hz hk hd hdropcard ⟨i, hi, rfl⟩ hsum'
  refine ⟨kept, hsub, hkept, hbound, ?_⟩
  intro j hj
  have hj := hk j hj
  have hsquare := (sq_le_sq₀ hj.1 hz).2 hj.2
  exact hsquare.trans hmaxbound

/-- NS4's exact weighted variance invoice, with the largest retained width
witnessed by a real selected group. -/
theorem narrowest_seed_variance_bound {ι : Type*} [DecidableEq ι]
    (all : Finset ι) (width : ι → ℝ) (X d : ℝ) (s t : ℕ)
    (hs : 0 < s) (ht : 2 ≤ t) (hd : 0 ≤ d)
    (hcard : all.card = s + t - 1)
    (hnonneg : ∀ i ∈ all, 0 ≤ width i)
    (hsum : (∑ i ∈ all, width i) ≤ X) :
    ∃ kept : Finset ι, kept ⊆ all ∧ kept.card = s ∧
      ∃ z : ℝ, (∃ i ∈ kept, z = width i) ∧
        (∀ i ∈ kept, width i ≤ z) ∧
        3 * d * (∑ i ∈ kept, width i ^ 2) + 4 * z ^ 2 ≤
          (3 * d / (4 * ((t : ℝ) - 1)) + 4 / (t : ℝ) ^ 2) * X ^ 2 := by
  classical
  obtain ⟨kept, hsub, hcard', hsumBound, hpoint⟩ :=
    narrowest_seed_groups_bound all width X s t hs ht hcard hnonneg hsum
  have hnon : kept.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image kept width hnon
  refine ⟨kept, hsub, hcard', width i, ⟨i, hi, rfl⟩, hmax, ?_⟩
  have h1 := mul_le_mul_of_nonneg_left hsumBound (show (0 : ℝ) ≤ 3 * d by positivity)
  have h2 := mul_le_mul_of_nonneg_left (hpoint i hi) (show (0 : ℝ) ≤ 4 by norm_num)
  calc
    3 * d * (∑ i ∈ kept, width i ^ 2) + 4 * width i ^ 2 ≤
        3 * d * (X ^ 2 / (4 * ((t : ℝ) - 1))) + 4 * (X ^ 2 / (t : ℝ) ^ 2) := add_le_add h1 h2
    _ = (3 * d / (4 * ((t : ℝ) - 1)) + 4 / (t : ℝ) ^ 2) * X ^ 2 := by ring

end
end Sude
