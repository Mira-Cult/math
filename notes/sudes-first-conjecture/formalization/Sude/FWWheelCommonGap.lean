import Sude.FWWheelShortPairs
import Sude.FixedGapMatching

/-! A conditional source WW4 common-gap matching, including equality in the
pair-count gate. No numerical pair supply or growth trace is asserted. -/
namespace Sude
noncomputable section

/-- The source weak (non-strict) pigeonhole gate and path matching. -/
theorem fw_weak_common_gap_matching_from_pairs (P : Finset (ℕ × ℕ)) (g R Q : ℕ) (D : ℝ)
    (hg : 0 < g) (hR : g ≤ R) (hQpos : 0 < Q)
    (hvalid : ∀ z ∈ P, z.1 < z.2 ∧ g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R ∧ D ≤ (z.2 - z.1 : ℕ))
    (hcount : (R / g) * (2 * Q) ≤ P.card) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ D ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, (p, p + h) ∈ P) ∧ PairwiseDisjointPairs T h := by
  classical
  let index : ℕ × ℕ → ℕ := fun z => (z.2 - z.1) / g
  let gaps := Finset.Icc 1 (R / g)
  have hmap : ∀ z ∈ P, index z ∈ gaps := by
    intro z hz
    obtain ⟨hpos, hdvd, hmax, _⟩ := hvalid z hz
    have hgap : 0 < z.2 - z.1 := by omega
    have hg_le := Nat.le_of_dvd hgap hdvd
    have hindexpos : 0 < (z.2 - z.1) / g := Nat.div_pos hg_le hg
    have hindexmax : (z.2 - z.1) / g ≤ R / g := Nat.div_le_div_right hmax
    exact Finset.mem_Icc.mpr ⟨hindexpos, hindexmax⟩
  have hgaps : gaps.card ≤ R / g := by
    simp [gaps, Nat.card_Icc]
  have hlarge : gaps.card * (2 * Q) ≤ P.card := by
    exact (Nat.mul_le_mul_right _ hgaps).trans hcount
  have hne : gaps.Nonempty := by
    refine ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, ?_⟩⟩
    exact Nat.div_pos hR hg
  obtain ⟨j, hj, hjcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := P) (t := gaps) (f := index) (n := 2 * Q) hmap hne hlarge
  let bucket := P.filter (fun z => index z = j)
  let S := bucket.image Prod.fst
  have hbucket : ∀ z ∈ bucket, z.2 = z.1 + g * j := by
    intro z hz
    have hp := (Finset.mem_filter.mp hz).1
    have hi := (Finset.mem_filter.mp hz).2
    obtain ⟨hpos, hdvd, _, _⟩ := hvalid z hp
    have hm := Nat.div_mul_cancel hdvd
    change (z.2 - z.1) / g = j at hi
    rw [hi] at hm
    have hm' : g * j = z.2 - z.1 := by simpa [Nat.mul_comm] using hm
    omega
  have hinj : Set.InjOn Prod.fst (↑bucket : Set (ℕ × ℕ)) := by
    intro x hx y hy hxy
    apply Prod.ext hxy
    have hx' := hbucket x hx
    have hy' := hbucket y hy
    omega
  have hScard : S.card = bucket.card := Finset.card_image_iff.mpr hinj
  have hjpos : 0 < j := (Finset.mem_Icc.mp hj).1
  have hpos : 0 < g * j := Nat.mul_pos hg hjpos
  obtain ⟨T, hTS, hmatchcard, hmatch⟩ := fixed_gap_half_matching S (g * j) hpos
  have hQ : Q ≤ T.card := by
    have hc : 2 * Q ≤ bucket.card := hjcard
    omega
  have hP : ∀ p ∈ T, (p, p + g * j) ∈ P := by
    intro p hp
    obtain ⟨z, hz, hzfirst⟩ := Finset.mem_image.mp (hTS hp)
    have hzpair := hbucket z hz
    have heq : z = (p, p + g * j) := Prod.ext hzfirst (by omega)
    rw [← heq]
    exact (Finset.mem_filter.mp hz).1
  have hnonempty : 0 < T.card := by
    have hc : 2 * Q ≤ bucket.card := hjcard
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hnonempty
  have hpvalid := hvalid (p, p + g * j) (hP p hp)
  have hmax : g * j ≤ R := by simpa using hpvalid.2.2.1
  have hD : D ≤ ((g * j : ℕ) : ℝ) := by simpa using hpvalid.2.2.2
  exact ⟨g * j, T, hpos, dvd_mul_right g j, hmax, hD, hQ, hP, hmatch⟩


/-- A supplied even-gap pair population pays the exact WW short-pair charge,
then yields zQ disjoint pairs at one actual gap in the closed interval [h,R].
All pair and count hypotheses refer to the actual finite population. -/
theorem fw_wheel_common_gap_from_pair_population
    (S : Finset ℕ) (P : Finset (ℕ × ℕ)) (W T h R z Q : ℕ)
    (hW : 0 < W) (hWodd : W % 2 = 1) (hR : 2 ≤ R) (hzQ : 0 < z * Q)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hP : ∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧
      x.2 % 2 = x.1 % 2 ∧ x.2 - x.1 ≤ R)
    (hcut : h ≤ 2 * fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW))
    (hpopulation : S.card * T + (R / 2) * (2 * (z * Q)) ≤ P.card) :
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ h ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  classical
  let long := P.filter (fun x => h ≤ x.2 - x.1)
  have hpair : ∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧ x.2 % 2 = x.1 % 2 := by
    intro x hx
    exact ⟨(hP x hx).1, (hP x hx).2.1, (hP x hx).2.2.1, (hP x hx).2.2.2.1⟩
  have hcharge := fw_wheel_long_pairs_after_short_removal S P W T h hW hWodd hS hpair hcut
  have hlongcount : (R / 2) * (2 * (z * Q)) ≤ long.card := by
    dsimp [long]
    omega
  have hvalid : ∀ x ∈ long, x.1 < x.2 ∧ 2 ∣ x.2 - x.1 ∧
      x.2 - x.1 ≤ R ∧ (h : ℝ) ≤ ((x.2 - x.1 : ℕ) : ℝ) := by
    intro x hx
    have hxP := (Finset.mem_filter.mp hx).1
    obtain ⟨_, _, hpq, hparity, hmax⟩ := hP x hxP
    have hdiv : 2 ∣ x.2 - x.1 := by omega
    have hlow : h ≤ x.2 - x.1 := (Finset.mem_filter.mp hx).2
    exact ⟨hpq, hdiv, hmax, by exact_mod_cast hlow⟩
  obtain ⟨gap, chosen, hgap, hdiv, hmax, hlow, hcard, hmem, hmatching⟩ :=
    fw_weak_common_gap_matching_from_pairs long 2 R (z * Q) h (by decide) hR hzQ hvalid hlongcount
  refine ⟨gap, chosen, hgap, hdiv, by exact_mod_cast hlow, hmax, hcard, ?_, ?_, hmatching⟩
  · intro p hp
    exact (Finset.mem_filter.mp (hmem p hp)).1
  · intro p hp
    have hpP := (Finset.mem_filter.mp (hmem p hp)).1
    exact ⟨(hP (p, p + gap) hpP).1, (hP (p, p + gap) hpP).2.1⟩

/-- The same result at the literal WW5 cutoff `2*min(k_W(T),R/2)`.
The source's separate hypotheses relating T to its real floor and supplying
P remain assumptions outside this theorem. -/
theorem fw_wheel_ww5_common_gap_from_pair_population
    (S : Finset ℕ) (P : Finset (ℕ × ℕ)) (W T R z Q : ℕ)
    (hW : 0 < W) (hWodd : W % 2 = 1) (hR : 0 < R) (heven : 2 ∣ R) (hzQ : 0 < z * Q)
    (hS : ∀ p ∈ S, p % 2 = 1 ∧ Nat.Coprime p W)
    (hP : ∀ x ∈ P, x.1 ∈ S ∧ x.2 ∈ S ∧ x.1 < x.2 ∧
      x.2 % 2 = x.1 % 2 ∧ x.2 - x.1 ≤ R)
    (hpopulation : S.card * T + (R / 2) * (2 * (z * Q)) ≤ P.card) :
    let k := fwWheelWindowCutoff (fwWheelUnit W) W (Nat.totient W) T
      (Nat.totient_pos.mpr hW)
    let h := 2 * min k (R / 2)
    ∃ (gap : ℕ) (chosen : Finset ℕ),
      0 < gap ∧ 2 ∣ gap ∧ h ≤ gap ∧ gap ≤ R ∧ z * Q ≤ chosen.card ∧
      (∀ p ∈ chosen, (p, p + gap) ∈ P) ∧
      (∀ p ∈ chosen, p ∈ S ∧ p + gap ∈ S) ∧ PairwiseDisjointPairs chosen gap := by
  dsimp only
  have hcut := (fw_wheel_ww5_cutoff_geometry W T R hW hR heven).2.2.2
  exact fw_wheel_common_gap_from_pair_population S P W T _ R z Q hW hWodd
    (by omega) hzQ hS hP hcut hpopulation


end
end Sude
