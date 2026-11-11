import Sude.PrimePairMatching
import Mathlib.Combinatorics.Pigeonhole

/-! Every positive fixed-gap graph has a large physical matching. -/
namespace Sude
noncomputable section

/-- One parity class of lower endpoints contains no overlapping pairs.
This uses no primality assumption and works for every positive gap. -/
theorem fixed_gap_parity_disjoint (S : Finset ℕ) (h : ℕ) (hh : 0 < h) (parity : ℕ) :
    PairwiseDisjointPairs (S.filter (fun p => (p / h) % 2 = parity)) h := by
  intro p hp q hq hpq
  have hpp := (Finset.mem_filter.mp hp).2
  have hqp := (Finset.mem_filter.mp hq).2
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
  rcases hz with hz | hz <;> rcases hz' with hz' | hz'
  · exact hpq (hz.symm.trans hz')
  · have he : p = q + h := hz.symm.trans hz'
    rw [he, Nat.add_div_right q hh] at hpp
    omega
  · have he : q = p + h := hz'.symm.trans hz
    rw [he, Nat.add_div_right p hh] at hqp
    omega
  · have he : p + h = q + h := hz.symm.trans hz'
    exact hpq (Nat.add_right_cancel he)

/-- At least half of any collection of fixed-gap edges can be retained with
pairwise-disjoint physical endpoints. -/
theorem fixed_gap_half_matching (S : Finset ℕ) (h : ℕ) (hh : 0 < h) :
    ∃ T : Finset ℕ, T ⊆ S ∧ S.card ≤ 2 * T.card ∧ PairwiseDisjointPairs T h := by
  classical
  let T₀ := S.filter (fun p => (p / h) % 2 = 0)
  let T₁ := S.filter (fun p => (p / h) % 2 = 1)
  have hpartition : T₀.card + T₁.card = S.card := by
    have hp := Finset.card_filter_add_card_filter_not (s := S) (fun p => (p / h) % 2 = 0)
    have heq : S.filter (fun p => ¬ (p / h) % 2 = 0) = T₁ := by
      apply Finset.ext
      intro p
      dsimp [T₁]
      simp only [Finset.mem_filter]
      have hevenodd (t : ℕ) : (¬ t % 2 = 0) ↔ t % 2 = 1 := by omega
      rw [hevenodd]
    rw [heq] at hp
    exact hp
  by_cases hb : T₀.card ≥ T₁.card
  · exact ⟨T₀, Finset.filter_subset _ _, by omega, fixed_gap_parity_disjoint S h hh 0⟩
  · exact ⟨T₁, Finset.filter_subset _ _, by omega, fixed_gap_parity_disjoint S h hh 1⟩

/-- Pigeonhole a finite set of actual ordered pairs by their common gap,
then retain a disjoint matching of at least `Q` pairs. The numeric count
and all endpoint supplies are explicit hypotheses. -/
theorem common_gap_matching_from_pairs (P : Finset (ℕ × ℕ)) (g R Q : ℕ) (D : ℝ)
    (hg : 0 < g)
    (hvalid : ∀ z ∈ P, z.1 < z.2 ∧ g ∣ z.2 - z.1 ∧ z.2 - z.1 ≤ R ∧ D ≤ (z.2 - z.1 : ℕ))
    (hcount : (R / g) * (2 * Q) < P.card) :
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
  have hlarge : gaps.card * (2 * Q) < P.card := by
    exact lt_of_le_of_lt (Nat.mul_le_mul_right _ hgaps) hcount
  obtain ⟨j, hj, hjcard⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := P) (t := gaps) (f := index) (n := 2 * Q) hmap hlarge
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
    have hc : 2 * Q < bucket.card := hjcard
    omega
  have hP : ∀ p ∈ T, (p, p + g * j) ∈ P := by
    intro p hp
    obtain ⟨z, hz, hzfirst⟩ := Finset.mem_image.mp (hTS hp)
    have hzpair := hbucket z hz
    have heq : z = (p, p + g * j) := Prod.ext hzfirst (by omega)
    rw [← heq]
    exact (Finset.mem_filter.mp hz).1
  have hnonempty : 0 < T.card := by
    have hc : 2 * Q < bucket.card := hjcard
    omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hnonempty
  have hpvalid := hvalid (p, p + g * j) (hP p hp)
  have hmax : g * j ≤ R := by simpa using hpvalid.2.2.1
  have hD : D ≤ ((g * j : ℕ) : ℝ) := by simpa using hpvalid.2.2.2
  exact ⟨g * j, T, hpos, dvd_mul_right g j, hmax, hD, hQ, hP, hmatch⟩

end
end Sude
