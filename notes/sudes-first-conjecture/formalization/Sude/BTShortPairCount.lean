import Sude.MontgomeryVaughan
import Sude.FixedGapMatching

/-! BT3 short-pair depletion on actual finite prime sets. -/
namespace Sude
noncomputable section

/-- Candidate ordered pairs with a gap strictly below the chosen width. -/
def shortPairSet (P : Finset (ℕ × ℕ)) (width : ℝ) : Finset (ℕ × ℕ) :=
  P.filter fun z => ((z.2 - z.1 : ℕ) : ℝ) < width

/-- The published progression bound controls the total number of short
candidate pairs by summing actual surviving neighbours over lower endpoints. -/
theorem mv_short_pair_count (mv : MVBrunTitchmarsh)
    (unused : Finset ℕ) (P : Finset (ℕ × ℕ)) (k a : ℕ) (width ell : ℝ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      (z.2 : ℤ) % k = (a : ℤ) % k)
    (hk : 0 < k) (ha : 0 < a) (hcoprime : Nat.Coprime k a)
    (hwidth : (k : ℝ) < width) (hell : 0 < ell)
    (hexp : Real.exp ell ≤ width / k) :
    ((shortPairSet P width).card : ℝ) <
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) := by
  classical
  let short := shortPairSet P width
  let fiber : ℕ → Finset (ℕ × ℕ) := fun p => short.filter fun z => z.1 = p
  let C : ℝ := 2 * width / ((Nat.totient k : ℝ) * ell)
  have hmap : ∀ z ∈ short, z.1 ∈ unused := by
    intro z hz
    exact (hpairs z (Finset.mem_filter.mp hz).1).1
  have hcount : short.card = ∑ p ∈ unused, (fiber p).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := short) (t := unused) (f := Prod.fst) hmap
  have hfiber : ∀ p ∈ unused, (fiber p).card ≤ (shortClassNeighbours unused p k a width).card := by
    intro p hp
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro z hz
      have hzshort := (Finset.mem_filter.mp hz).1
      have hfirst := (Finset.mem_filter.mp hz).2
      have hzP := (Finset.mem_filter.mp hzshort).1
      have hgap := (Finset.mem_filter.mp hzshort).2
      obtain ⟨_, hzu, hlt, hres⟩ := hpairs z hzP
      have hgapR : (z.2 : ℝ) - z.1 < width := by
        simpa only [Nat.cast_sub (le_of_lt hlt)] using hgap
      apply Finset.mem_filter.mpr
      refine ⟨hzu, ?_, ?_, hres⟩
      · omega
      · have heq : (z.1 : ℝ) = p := by exact_mod_cast hfirst
        linarith
    · intro x hx y hy heq
      have hxfirst := (Finset.mem_filter.mp hx).2
      have hyfirst := (Finset.mem_filter.mp hy).2
      exact Prod.ext (hxfirst.trans hyfirst.symm) heq
  have hlt : ∀ p ∈ unused, ((fiber p).card : ℝ) < C := by
    intro p hp
    have hp0 := (hprimes p hp).pos
    have hnbr := mv_depleted_neighbour_bound mv unused p k a width ell hprimes hp0 hk ha hcoprime
      hwidth hell hexp
    have hc : ((fiber p).card : ℝ) ≤ (shortClassNeighbours unused p k a width).card := by
      exact_mod_cast hfiber p hp
    exact hc.trans_lt hnbr
  have hsum := Finset.sum_lt_sum_of_nonempty hne hlt
  have hcountR : (short.card : ℝ) = ∑ p ∈ unused, ((fiber p).card : ℝ) := by exact_mod_cast hcount
  rw [← hcountR] at hsum
  simpa [short, C] using hsum

/-- The published progression bound controls the total number of short
candidate pairs by summing actual surviving neighbours over lower endpoints. -/
theorem mv_short_pair_count_multiclass (mv : MVBrunTitchmarsh)
    (unused : Finset ℕ) (P : Finset (ℕ × ℕ)) (k : ℕ) (residue : ℕ → ℕ) (width ell : ℝ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      (z.2 : ℤ) % k = (residue z.1 : ℤ) % k)
    (hk : 0 < k) (hclasses : ∀ p ∈ unused, 0 < residue p ∧ Nat.Coprime k (residue p))
    (hwidth : (k : ℝ) < width) (hell : 0 < ell)
    (hexp : Real.exp ell ≤ width / k) :
    ((shortPairSet P width).card : ℝ) <
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) := by
  classical
  let short := shortPairSet P width
  let fiber : ℕ → Finset (ℕ × ℕ) := fun p => short.filter fun z => z.1 = p
  let C : ℝ := 2 * width / ((Nat.totient k : ℝ) * ell)
  have hmap : ∀ z ∈ short, z.1 ∈ unused := by
    intro z hz
    exact (hpairs z (Finset.mem_filter.mp hz).1).1
  have hcount : short.card = ∑ p ∈ unused, (fiber p).card := by
    exact Finset.card_eq_sum_card_fiberwise (s := short) (t := unused) (f := Prod.fst) hmap
  have hfiber : ∀ p ∈ unused, (fiber p).card ≤ (shortClassNeighbours unused p k (residue p) width).card := by
    intro p hp
    apply Finset.card_le_card_of_injOn Prod.snd
    · intro z hz
      have hzshort := (Finset.mem_filter.mp hz).1
      have hfirst := (Finset.mem_filter.mp hz).2
      have hzP := (Finset.mem_filter.mp hzshort).1
      have hgap := (Finset.mem_filter.mp hzshort).2
      obtain ⟨_, hzu, hlt, hres⟩ := hpairs z hzP
      have hgapR : (z.2 : ℝ) - z.1 < width := by
        simpa only [Nat.cast_sub (le_of_lt hlt)] using hgap
      apply Finset.mem_filter.mpr
      refine ⟨hzu, ?_, ?_, ?_⟩
      · omega
      · have heq : (z.1 : ℝ) = p := by exact_mod_cast hfirst
        linarith
      · simpa [hfirst] using hres
    · intro x hx y hy heq
      have hxfirst := (Finset.mem_filter.mp hx).2
      have hyfirst := (Finset.mem_filter.mp hy).2
      exact Prod.ext (hxfirst.trans hyfirst.symm) heq
  have hlt : ∀ p ∈ unused, ((fiber p).card : ℝ) < C := by
    intro p hp
    have hp0 := (hprimes p hp).pos
    have hclass := hclasses p hp
    have hnbr := mv_depleted_neighbour_bound mv unused p k (residue p) width ell hprimes hp0 hk hclass.1 hclass.2
      hwidth hell hexp
    have hc : ((fiber p).card : ℝ) ≤ (shortClassNeighbours unused p k (residue p) width).card := by
      exact_mod_cast hfiber p hp
    exact hc.trans_lt hnbr
  have hsum := Finset.sum_lt_sum_of_nonempty hne hlt
  have hcountR : (short.card : ℝ) = ∑ p ∈ unused, ((fiber p).card : ℝ) := by exact_mod_cast hcount
  rw [← hcountR] at hsum
  simpa [short, C] using hsum

/-- BT3--BT5 from an explicit actual candidate-pair count. Short pairs are
charged using Montgomery--Vaughan, then one positive common gap and a
physical matching are selected. This does not assume the BT2 pair count. -/
theorem mv_common_gap_from_pair_population (mv : MVBrunTitchmarsh)
    (unused : Finset ℕ) (P : Finset (ℕ × ℕ)) (k a g R Q : ℕ) (width ell : ℝ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      (z.2 : ℤ) % k = (a : ℤ) % k)
    (hgaps : ∀ z ∈ P, g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R)
    (hk : 0 < k) (ha : 0 < a) (hg : 0 < g) (hcoprime : Nat.Coprime k a)
    (hwidth : (k : ℝ) < width) (hell : 0 < ell)
    (hexp : Real.exp ell ≤ width / k)
    (hpopulation : (((R / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) ≤ P.card) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, (p, p + h) ∈ P ∧ p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  classical
  let short := shortPairSet P width
  let long := P.filter fun z => width ≤ ((z.2 - z.1 : ℕ) : ℝ)
  have hpartition : short.card + long.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := P)
      (fun z => ((z.2 - z.1 : ℕ) : ℝ) < width)
    have heq : P.filter (fun z => ¬ ((z.2 - z.1 : ℕ) : ℝ) < width) = long := by
      ext z
      simp [long, not_lt]
    rw [heq] at h
    exact h
  have hpartitionR : (short.card : ℝ) + long.card = P.card := by exact_mod_cast hpartition
  have hshort := mv_short_pair_count mv unused P k a width ell hne hprimes hpairs hk ha hcoprime
    hwidth hell hexp
  have hcountR : (((R / g) * (2 * Q) : ℕ) : ℝ) < long.card := by linarith
  have hcount : (R / g) * (2 * Q) < long.card := by exact_mod_cast hcountR
  have hvalid : ∀ z ∈ long, z.1 < z.2 ∧ g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R ∧
      width ≤ ((z.2 - z.1 : ℕ) : ℝ) := by
    intro z hz
    have hzP := (Finset.mem_filter.mp hz).1
    exact ⟨(hpairs z hzP).2.2.1, (hgaps z hzP).1, (hgaps z hzP).2,
      (Finset.mem_filter.mp hz).2⟩
  obtain ⟨h, T, hh, hdiv, hR, hD, hQ, hT, hmatch⟩ :=
    common_gap_matching_from_pairs long g R Q width hg hvalid hcount
  refine ⟨h, T, hh, hdiv, hR, hD, hQ, ?_, hmatch⟩
  intro p hp
  have hpLong := hT p hp
  have hpP := (Finset.mem_filter.mp hpLong).1
  exact ⟨hpP, (hpairs (p, p + h) hpP).1, (hpairs (p, p + h) hpP).2.1⟩
/-- BT3--BT5 from an explicit actual candidate-pair count. Short pairs are
charged using Montgomery--Vaughan, then one positive common gap and a
physical matching are selected. This does not assume the BT2 pair count. -/
theorem mv_multiclass_common_gap_from_pair_population (mv : MVBrunTitchmarsh)
    (unused : Finset ℕ) (P : Finset (ℕ × ℕ)) (k g R Q : ℕ) (residue : ℕ → ℕ) (width ell : ℝ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hpairs : ∀ z ∈ P, z.1 ∈ unused ∧ z.2 ∈ unused ∧ z.1 < z.2 ∧
      (z.2 : ℤ) % k = (residue z.1 : ℤ) % k)
    (hgaps : ∀ z ∈ P, g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R)
    (hk : 0 < k) (hg : 0 < g) (hclasses : ∀ p ∈ unused, 0 < residue p ∧ Nat.Coprime k (residue p))
    (hwidth : (k : ℝ) < width) (hell : 0 < ell)
    (hexp : Real.exp ell ≤ width / k)
    (hpopulation : (((R / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient k : ℝ) * ell)) ≤ P.card) :
    ∃ (h : ℕ) (T : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ R ∧ width ≤ h ∧ Q ≤ T.card ∧
      (∀ p ∈ T, (p, p + h) ∈ P ∧ p ∈ unused ∧ p + h ∈ unused) ∧ PairwiseDisjointPairs T h := by
  classical
  let short := shortPairSet P width
  let long := P.filter fun z => width ≤ ((z.2 - z.1 : ℕ) : ℝ)
  have hpartition : short.card + long.card = P.card := by
    have h := Finset.card_filter_add_card_filter_not (s := P)
      (fun z => ((z.2 - z.1 : ℕ) : ℝ) < width)
    have heq : P.filter (fun z => ¬ ((z.2 - z.1 : ℕ) : ℝ) < width) = long := by
      ext z
      simp [long, not_lt]
    rw [heq] at h
    exact h
  have hpartitionR : (short.card : ℝ) + long.card = P.card := by exact_mod_cast hpartition
  have hshort := mv_short_pair_count_multiclass mv unused P k residue width ell hne hprimes hpairs hk hclasses
    hwidth hell hexp
  have hcountR : (((R / g) * (2 * Q) : ℕ) : ℝ) < long.card := by linarith
  have hcount : (R / g) * (2 * Q) < long.card := by exact_mod_cast hcountR
  have hvalid : ∀ z ∈ long, z.1 < z.2 ∧ g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R ∧
      width ≤ ((z.2 - z.1 : ℕ) : ℝ) := by
    intro z hz
    have hzP := (Finset.mem_filter.mp hz).1
    exact ⟨(hpairs z hzP).2.2.1, (hgaps z hzP).1, (hgaps z hzP).2,
      (Finset.mem_filter.mp hz).2⟩
  obtain ⟨h, T, hh, hdiv, hR, hD, hQ, hT, hmatch⟩ :=
    common_gap_matching_from_pairs long g R Q width hg hvalid hcount
  refine ⟨h, T, hh, hdiv, hR, hD, hQ, ?_, hmatch⟩
  intro p hp
  have hpLong := hT p hp
  have hpP := (Finset.mem_filter.mp hpLong).1
  exact ⟨hpP, (hpairs (p, p + h) hpP).1, (hpairs (p, p + h) hpP).2.1⟩

end
end Sude
