import Sude.PairReservoir
import Sude.PrefixCount
import Mathlib.Tactic.IntervalCases

/-! FPF2's exact fixed-gap matching principle. These results do not certify
any of the five numerical populations, or cross-stage disjointness. -/
namespace Sude

/-- A prime strictly above three is not divisible by three. -/
theorem prime_above_three_mod_ne_zero {p : ℕ} (hp : Nat.Prime p) (h : 3 < p) :
    p % 3 ≠ 0 := by
  intro hm
  have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hm
  have : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hd
  omega

/-- For three terms in an arithmetic progression, if the step is not a
multiple of three, one of the terms is a multiple of three. -/
theorem three_term_multiple_three (p h : ℕ) (hh : h % 3 ≠ 0) :
    p % 3 = 0 ∨ (p + h) % 3 = 0 ∨ (p + h + h) % 3 = 0 := by
  have hp : p % 3 < 3 := Nat.mod_lt _ (by decide)
  have hh' : h % 3 < 3 := Nat.mod_lt _ (by decide)
  have h1 : (p + h) % 3 = (p % 3 + h % 3) % 3 := Nat.add_mod p h 3
  have h2 : (p + h + h) % 3 = ((p % 3 + h % 3) % 3 + h % 3) % 3 := by
    rw [Nat.add_mod (p + h) h 3, Nat.add_mod p h 3]
  interval_cases hpv : p % 3 <;> interval_cases hhv : h % 3 <;>
    norm_num at * <;> omega

/-- No three primes strictly above three are equally spaced with step
not divisible by three. This includes every power of two. -/
theorem no_prime_triple_of_mod_three {p h : ℕ} (hp : 3 < p)
    (hstep : h % 3 ≠ 0) (h0 : Nat.Prime p) (h1 : Nat.Prime (p + h))
    (h2 : Nat.Prime (p + h + h)) : False := by
  rcases three_term_multiple_three p h hstep with h | h | h
  · exact prime_above_three_mod_ne_zero h0 hp h
  · exact prime_above_three_mod_ne_zero h1 (by omega) h
  · exact prime_above_three_mod_ne_zero h2 (by omega) h

/-- Distinct candidate pairs with one fixed positive gap not divisible by
three cannot share an endpoint, as long as every endpoint is prime above 3. -/
theorem prime_pair_endpoints_disjoint {p q h : ℕ} (hp : 3 < p) (hq : 3 < q)
    (_hh : 0 < h) (hstep : h % 3 ≠ 0)
    (hp0 : Nat.Prime p) (hp1 : Nat.Prime (p + h))
    (hq0 : Nat.Prime q) (hq1 : Nat.Prime (q + h)) (hpq : p ≠ q) :
    Disjoint ({p, p + h} : Finset ℕ) {q, q + h} := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hpq (hx.symm.trans hy)
  · have : p = q + h := hx.symm.trans hy
    have hlast : Nat.Prime (q + h + h) := by simpa [this] using hp1
    exact no_prime_triple_of_mod_three hq hstep hq0 hq1 hlast
  · have : p + h = q := hx.symm.trans hy
    have hlast : Nat.Prime (p + h + h) := by simpa [← this] using hq1
    exact no_prime_triple_of_mod_three hp hstep hp0 hp1 hlast
  · have : p + h = q + h := hx.symm.trans hy
    exact hpq (Nat.add_right_cancel this)

/-- Every power of two is nonzero modulo three. -/
theorem two_pow_mod_three_ne_zero (j : ℕ) : 2 ^ j % 3 ≠ 0 := by
  intro hm
  have hd : 3 ∣ 2 ^ j := Nat.dvd_of_mod_eq_zero hm
  have : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
  norm_num at this

/-- The exact matching property used for each fixed-gap FPF stage. -/
theorem binary_prime_pair_endpoints_disjoint {p q j : ℕ} (hp : 3 < p) (hq : 3 < q)
    (hp0 : Nat.Prime p) (hp1 : Nat.Prime (p + 2 ^ j))
    (hq0 : Nat.Prime q) (hq1 : Nat.Prime (q + 2 ^ j)) (hpq : p ≠ q) :
    Disjoint ({p, p + 2 ^ j} : Finset ℕ) {q, q + 2 ^ j} :=
  prime_pair_endpoints_disjoint hp hq (Nat.two_pow_pos j) (two_pow_mod_three_ne_zero j)
    hp0 hp1 hq0 hq1 hpq

/-- The actual endpoints of a collection of fixed-gap pairs. -/
def pairFootprint (S : Finset ℕ) (h : ℕ) : Finset ℕ :=
  S ∪ S.image (fun p => p + h)

/-- A labelled candidate family has no shared endpoints across distinct pairs. -/
def PairwiseDisjointPairs (S : Finset ℕ) (h : ℕ) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint ({p, p + h} : Finset ℕ) {q, q + h}

/-- FPF candidates with a binary gap satisfy the pairwise matching property. -/
theorem binary_prime_family_disjoint (S : Finset ℕ) (j : ℕ)
    (hprime : ∀ p ∈ S, 3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2 ^ j)) :
    PairwiseDisjointPairs S (2 ^ j) := by
  intro p hp q hq hpq
  obtain ⟨hpl, hp0, hp1⟩ := hprime p hp
  obtain ⟨hql, hq0, hq1⟩ := hprime q hq
  exact binary_prime_pair_endpoints_disjoint hpl hql hp0 hp1 hq0 hq1 hpq

/-- An actual matching of positive-gap pairs consumes exactly two entries
per retained lower endpoint. -/
theorem pairFootprint_card (S : Finset ℕ) (h : ℕ) (hpos : 0 < h)
    (hmatch : PairwiseDisjointPairs S h) :
    (pairFootprint S h).card = 2 * S.card := by
  have hdisj : Disjoint S (S.image (fun p => p + h)) := by
    apply Finset.disjoint_left.mpr
    intro p hp himage
    obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp himage
    have hpq : p ≠ q := by omega
    have hpair := hmatch p hp q hq hpq
    exact Finset.disjoint_left.mp hpair (by simp : p ∈ ({p, p + h} : Finset ℕ))
      (by simp [← heq] : p ∈ ({q, q + h} : Finset ℕ))
  unfold pairFootprint
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_iff.mpr]
  · omega
  · intro p hp q hq heq
    exact Nat.add_right_cancel heq

/-- Candidates whose two endpoints avoid an earlier reservation. -/
def availablePairs (S reserved : Finset ℕ) (h : ℕ) : Finset ℕ :=
  S.filter (fun p => p ∉ reserved ∧ p + h ∉ reserved)

/-- Each previously reserved entry can destroy at most one candidate of a
fixed-gap matching, even if several entries were reserved elsewhere. -/
theorem availablePairs_card_lower (S reserved : Finset ℕ) (h : ℕ)
    (hmatch : PairwiseDisjointPairs S h) :
    S.card ≤ (availablePairs S reserved h).card + reserved.card := by
  classical
  let good : ℕ → Prop := fun p => p ∉ reserved ∧ p + h ∉ reserved
  let bad : Finset ℕ := S.filter (fun p => ¬ good p)
  let hit : ℕ → ℕ := fun p => if p ∈ reserved then p else p + h
  have hhit_mem : ∀ p ∈ bad, hit p ∈ reserved := by
    intro p hp
    have hpbad : ¬ good p := (Finset.mem_filter.mp hp).2
    dsimp [good] at hpbad
    dsimp [hit]
    by_cases hm : p ∈ reserved
    · simp [hm]
    · simp only [hm, if_false]
      push Not at hpbad
      exact hpbad hm
  have hhit_pair : ∀ p, hit p ∈ ({p, p + h} : Finset ℕ) := by
    intro p
    dsimp [hit]
    split_ifs <;> simp
  have hhit_inj : Set.InjOn hit (↑bad : Set ℕ) := by
    intro p hp q hq heq
    by_contra hpq
    have hps : p ∈ S := (Finset.mem_filter.mp hp).1
    have hqs : q ∈ S := (Finset.mem_filter.mp hq).1
    have hd := hmatch p hps q hqs hpq
    have hpHit := hhit_pair p
    have hqHit := hhit_pair q
    rw [← heq] at hqHit
    exact Finset.disjoint_left.mp hd hpHit hqHit
  have hbad : bad.card ≤ reserved.card :=
    Finset.card_le_card_of_injOn hit hhit_mem hhit_inj
  have hpartition := Finset.card_filter_add_card_filter_not (s := S) good
  change (availablePairs S reserved h).card + bad.card = S.card at hpartition
  omega

/-- If the candidate population pays for all earlier reserved entries, choose
exactly Q disjoint pairs whose endpoints avoid every such entry. -/
theorem select_available_pairs (S reserved : Finset ℕ) (h Q : ℕ)
    (hmatch : PairwiseDisjointPairs S h)
    (hcapacity : Q + reserved.card ≤ S.card) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = Q ∧
      (∀ p ∈ T, p ∉ reserved ∧ p + h ∉ reserved) ∧ PairwiseDisjointPairs T h := by
  have havail := availablePairs_card_lower S reserved h hmatch
  have hQ : Q ≤ (availablePairs S reserved h).card := by omega
  obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq hQ
  refine ⟨T, ?_, hcard, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp (hT hp)).1
  · intro p hp
    exact (Finset.mem_filter.mp (hT hp)).2
  · intro p hp q hq hpq
    exact hmatch p (Finset.mem_filter.mp (hT hp)).1
      q (Finset.mem_filter.mp (hT hq)).1 hpq

/-- A pair label and side choose an actual endpoint. -/
def pairEndpoint (S : Finset ℕ) (h : ℕ) (x : {p // p ∈ S} × Bool) : ℕ :=
  if x.2 then x.1.val + h else x.1.val

theorem pairEndpoint_mem (S : Finset ℕ) (h : ℕ) (x : {p // p ∈ S} × Bool) :
    pairEndpoint S h x ∈ ({x.1.val, x.1.val + h} : Finset ℕ) := by
  rcases x with ⟨⟨p, hp⟩, b⟩
  cases b <;> simp [pairEndpoint]

/-- Distinct pair/side labels yield distinct actual numbers. -/
theorem pairEndpoint_injective (S : Finset ℕ) (h : ℕ) (hpos : 0 < h)
    (hmatch : PairwiseDisjointPairs S h) : Function.Injective (pairEndpoint S h) := by
  rintro ⟨⟨p, hp⟩, u⟩ ⟨⟨q, hq⟩, v⟩ heq
  by_cases hpq : p = q
  · subst q
    cases u <;> cases v <;> simp [pairEndpoint] at heq ⊢ <;> omega
  · have hd := hmatch p hp q hq hpq
    have hp' := pairEndpoint_mem S h (⟨p, hp⟩, u)
    have hq' := pairEndpoint_mem S h (⟨q, hq⟩, v)
    rw [← heq] at hq'
    exact False.elim (Finset.disjoint_left.mp hd hp' hq')

/-- Install a supplied fixed-gap matching in supplied distinct physical cells,
without changing earlier reserved cells. The caller provides actual pool
membership and cell geometry; no numerical pair supply is assumed here. -/
theorem place_pair_family_preserving {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (S : Finset ℕ) (h : ℕ) (hpos : 0 < h) (hmatch : PairwiseDisjointPairs S h)
    (hpool : ∀ p ∈ S, p ∈ pool n ∧ p + h ∈ pool n)
    (cells : ({p // p ∈ S} × Bool) → Cell n) (reserved : Finset (Cell n))
    (hcells : Function.Injective cells) (hnew : ∀ x, cells x ∉ reserved)
    (havoid : ∀ p ∈ S, ∀ c ∈ reserved, p ≠ entry a c ∧ p + h ≠ entry a c) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ x, entry b (cells x) = pairEndpoint S h x) ∧
      (∀ c ∈ reserved, entry b c = entry a c) := by
  let values : ({p // p ∈ S} × Bool) → pool n := fun x =>
    ⟨pairEndpoint S h x, by
      rcases x with ⟨⟨p, hp⟩, side⟩
      cases side
      · simpa [pairEndpoint] using (hpool p hp).1
      · simpa [pairEndpoint] using (hpool p hp).2⟩
  have hv : Function.Injective values := by
    intro x y heq
    apply pairEndpoint_injective S h hpos hmatch
    exact congrArg Subtype.val heq
  have ha : ∀ x c, c ∈ reserved → (values x).val ≠ entry a c := by
    intro ⟨⟨p, hp⟩, side⟩ c hc
    cases side
    · simpa [values, pairEndpoint] using (havoid p hp c hc).1
    · simpa [values, pairEndpoint] using (havoid p hp c hc).2
  exact place_distinct_pool_entries_preserving a cells values reserved hcells hv hnew ha

/-- Composes the FPF counting, matching and depletion interfaces: a sufficiently
large candidate set with a certified odd-prime prefix bound yields Q disjoint
actual-pool pairs avoiding all prior reserved values. -/
theorem select_binary_pool_pairs {n B j Q : ℕ} (S reserved : Finset ℕ)
    (hB : 2 ≤ B) (hcount : (oddPrimePrefix B).card ≤ n * n)
    (hprime : ∀ p ∈ S, 3 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2 ^ j) ∧ p + 2 ^ j ≤ B)
    (hcapacity : Q + reserved.card ≤ S.card) :
    ∃ T : Finset ℕ, T ⊆ S ∧ T.card = Q ∧
      (∀ p ∈ T, p ∈ pool n ∧ p + 2 ^ j ∈ pool n ∧
        p ∉ reserved ∧ p + 2 ^ j ∉ reserved) ∧
      PairwiseDisjointPairs T (2 ^ j) ∧ (pairFootprint T (2 ^ j)).card = 2 * Q := by
  have hmatch : PairwiseDisjointPairs S (2 ^ j) := by
    apply binary_prime_family_disjoint
    intro p hp
    obtain ⟨hp3, hp0, hp1, _⟩ := hprime p hp
    exact ⟨hp3, hp0, hp1⟩
  obtain ⟨T, hT, hcard, hav, hmatchT⟩ :=
    select_available_pairs S reserved (2 ^ j) Q hmatch hcapacity
  refine ⟨T, hT, hcard, ?_, hmatchT, ?_⟩
  · intro p hp
    obtain ⟨hp3, hp0, hp1, hpB⟩ := hprime p (hT hp)
    have hpow : 0 < 2 ^ j := Nat.two_pow_pos j
    have hp0B : p ≤ B := (Nat.le_add_right p (2 ^ j)).trans hpB
    have h0 := prime_mem_pool_of_oddPrefix_card_le hB hcount hp0 (by omega) hp0B
    have h1 := prime_mem_pool_of_oddPrefix_card_le hB hcount hp1 (by omega) hpB
    exact ⟨h0, h1, (hav p hp).1, (hav p hp).2⟩
  · rw [pairFootprint_card T (2 ^ j) (Nat.two_pow_pos j) hmatchT, hcard]

end Sude
