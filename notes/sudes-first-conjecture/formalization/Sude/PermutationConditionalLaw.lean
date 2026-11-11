import Sude.PermutationSampling

/-! Exact conditional sampling law for a uniformly chosen permutation. -/
namespace Sude
noncomputable section

/-- Permutations agreeing with the already revealed positions of `reference`. -/
def permutationHistory {n : ℕ} (positions : Finset (Fin n)) (reference : Equiv.Perm (Fin n)) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter (fun p => ∀ i ∈ positions, p i = reference i)

/-- The history fiber refined by one further prescribed output. -/
def permutationHistoryNext {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i a : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  (permutationHistory positions reference).filter (fun p => p i = a)

/-- Any two unused outputs have equally many completions of the same history. -/
theorem permutationHistoryNext_card_eq {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i a b : Fin n)
    (ha : a ∉ positions.image reference) (hb : b ∉ positions.image reference) :
    (permutationHistoryNext positions reference i a).card =
      (permutationHistoryNext positions reference i b).card := by
  classical
  let σ := Equiv.swap a b
  have hfix (j : Fin n) (hj : j ∈ positions) : σ (reference j) = reference j := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h
      exact ha (Finset.mem_image.mpr ⟨j, hj, h⟩)
    · intro h
      exact hb (Finset.mem_image.mpr ⟨j, hj, h⟩)
  refine Finset.card_bij' (fun p _ => p.trans σ) (fun p _ => p.trans σ) ?_ ?_ ?_ ?_
  · intro p hp
    simp only [permutationHistoryNext, permutationHistory, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp ⊢
    constructor
    · intro j hj
      change σ (p j) = reference j
      rw [hp.1 j hj, hfix j hj]
    · change σ (p i) = b
      rw [hp.2]
      simp [σ]
  · intro p hp
    simp only [permutationHistoryNext, permutationHistory, Finset.mem_filter,
      Finset.mem_univ, true_and] at hp ⊢
    constructor
    · intro j hj
      change σ (p j) = reference j
      rw [hp.1 j hj, hfix j hj]
    · change σ (p i) = a
      rw [hp.2]
      simp [σ]
  · intro p hp
    ext j
    simp [σ]
  · intro p hp
    ext j
    simp [σ]

/-- For a fixed realizable history, the next image is uniform over the
remaining outputs. The integer identity retains the exact finite sampling
law without division or an independence assumption. -/
theorem permutationHistory_next_uniform {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i a : Fin n)
    (hi : i ∉ positions) (ha : a ∉ positions.image reference) :
    (n - positions.card) * (permutationHistoryNext positions reference i a).card =
      (permutationHistory positions reference).card := by
  classical
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  let history := permutationHistory positions reference
  have hmap : ∀ p ∈ history, p i ∈ available := by
    intro p hp
    have hp' : ∀ j ∈ positions, p j = reference j := by
      simpa [history, permutationHistory] using hp
    simp only [available, Finset.mem_compl]
    intro hmem
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
    have hij : i = j := p.injective (heq.symm.trans (hp' j hj).symm)
    exact hi (hij ▸ hj)
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  have hfiber (b : Fin n) (hb : b ∈ available) :
      (history.filter (fun p => p i = b)).card =
        (permutationHistoryNext positions reference i a).card := by
    change (permutationHistoryNext positions reference i b).card = _
    apply permutationHistoryNext_card_eq positions reference i b a
    · simpa [available] using hb
    · exact ha
  have havcard : available.card = n - positions.card := by
    simp [available, Finset.card_compl, Finset.card_image_of_injective _ reference.injective]
  calc
    (n - positions.card) * (permutationHistoryNext positions reference i a).card =
        available.card * (permutationHistoryNext positions reference i a).card := by rw [havcard]
    _ = ∑ b ∈ available, (history.filter (fun p => p i = b)).card := by
      symm
      calc
        _ = ∑ _b ∈ available, (permutationHistoryNext positions reference i a).card := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hfiber b hb
        _ = _ := by simp
    _ = (permutationHistory positions reference).card := hsum.symm

/-- A realizable history with an unused output has a positive next fiber. -/
theorem permutationHistoryNext_card_pos {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i a : Fin n)
    (hi : i ∉ positions) (ha : a ∉ positions.image reference) :
    0 < (permutationHistoryNext positions reference i a).card := by
  have hh : 0 < (permutationHistory positions reference).card := by
    apply Finset.card_pos.mpr
    exact ⟨reference, by simp [permutationHistory]⟩
  have heq := permutationHistory_next_uniform positions reference i a hi ha
  by_contra h
  have hz : (permutationHistoryNext positions reference i a).card = 0 := by omega
  rw [hz, Nat.mul_zero] at heq
  omega

/-- Completions of a fixed history whose next output belongs to a set. -/
def permutationHistoryEvent {n : ℕ} (positions targets : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) : Finset (Equiv.Perm (Fin n)) :=
  (permutationHistory positions reference).filter (fun p => p i ∈ targets)

/-- Exact conditional distribution of an arbitrary event on the next output.
No factorization into independent draws is used. -/
theorem permutationHistory_event_uniform {n : ℕ} (positions targets : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (htargets : Disjoint targets (positions.image reference)) :
    (n - positions.card) * (permutationHistoryEvent positions targets reference i).card =
      targets.card * (permutationHistory positions reference).card := by
  classical
  let a := reference i
  have ha : a ∉ positions.image reference := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have hij : j = i := reference.injective heq
    exact hi (hij ▸ hj)
  have hmap : ∀ p ∈ permutationHistoryEvent positions targets reference i, p i ∈ targets := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hsum := Finset.card_eq_sum_card_fiberwise hmap
  have hfiber (b : Fin n) (hb : b ∈ targets) :
      ((permutationHistoryEvent positions targets reference i).filter (fun p => p i = b)).card =
        (permutationHistoryNext positions reference i a).card := by
    have hset : (permutationHistoryEvent positions targets reference i).filter (fun p => p i = b) =
        permutationHistoryNext positions reference i b := by
      ext p
      simp only [permutationHistoryEvent, permutationHistoryNext, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hp, _⟩, heq⟩
        exact ⟨hp, heq⟩
      · rintro ⟨hp, heq⟩
        exact ⟨⟨hp, heq.symm ▸ hb⟩, heq⟩
    rw [hset]
    apply permutationHistoryNext_card_eq positions reference i b a
    · exact (Finset.disjoint_left.mp htargets) hb
    · exact ha
  have hevent : (permutationHistoryEvent positions targets reference i).card =
      targets.card * (permutationHistoryNext positions reference i a).card := by
    calc
      _ = ∑ b ∈ targets, ((permutationHistoryEvent positions targets reference i).filter
          (fun p => p i = b)).card := hsum
      _ = ∑ _b ∈ targets, (permutationHistoryNext positions reference i a).card := by
        apply Finset.sum_congr rfl
        intro b hb
        exact hfiber b hb
      _ = _ := by simp
  have hone := permutationHistory_next_uniform positions reference i a hi ha
  rw [hevent, ← hone]
  ring

/-- Any extension of the revealed history sends a new position to an unused
output. -/
theorem permutationHistory_next_unused {n : ℕ} (positions : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (hp : p ∈ permutationHistory positions reference) :
    p i ∉ positions.image reference := by
  have hp' : ∀ j ∈ positions, p j = reference j := by
    simpa [permutationHistory] using hp
  intro hmem
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hmem
  have hij : i = j := p.injective (heq.symm.trans (hp' j hj).symm)
  exact hi (hij ▸ hj)

/-- Conditional event law for an arbitrary output set: already-used values
contribute zero, and all remaining values have equal mass. -/
theorem permutationHistory_event_uniform_all {n : ℕ} (positions targets : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions) :
    (n - positions.card) * (permutationHistoryEvent positions targets reference i).card =
      (targets \ positions.image reference).card * (permutationHistory positions reference).card := by
  have hdis : Disjoint (targets \ positions.image reference) (positions.image reference) :=
    Finset.sdiff_disjoint
  have hevent : permutationHistoryEvent positions targets reference i =
      permutationHistoryEvent positions (targets \ positions.image reference) reference i := by
    ext p
    simp only [permutationHistoryEvent, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hp, ht⟩
      exact ⟨hp, ht, permutationHistory_next_unused positions reference p i hi hp⟩
    · rintro ⟨hp, ht, _⟩
      exact ⟨hp, ht⟩
  rw [hevent]
  exact permutationHistory_event_uniform positions _ reference i hi hdis

/-- For a uniformly weighted history, the next-value sum is the uniform sum
on unused outputs, in denominator-free form. This is the conditional
expectation law used to compute a permutation exposure martingale. -/
theorem permutationHistory_next_sum {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (f : Fin n → ℝ) :
    ((n - positions.card : ℕ) : ℝ) *
        (∑ p ∈ permutationHistory positions reference, f (p i)) =
      ((permutationHistory positions reference).card : ℝ) *
        (∑ b ∈ (positions.image reference)ᶜ, f b) := by
  classical
  let history := permutationHistory positions reference
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  let a := reference i
  have ha : a ∉ positions.image reference := by
    intro h
    obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
    have hij : j = i := reference.injective heq
    exact hi (hij ▸ hj)
  have hmap : ∀ p ∈ history, p i ∈ available := by
    intro p hp
    simpa [available] using permutationHistory_next_unused positions reference p i hi hp
  have hcount (b : Fin n) (hb : b ∈ available) :
      ((history.filter (fun p => p i = b)).card : ℝ) =
        ((permutationHistoryNext positions reference i a).card : ℝ) := by
    congr 1
    change (permutationHistoryNext positions reference i b).card = _
    exact permutationHistoryNext_card_eq positions reference i b a (by simpa [available] using hb) ha
  have hsum : (∑ p ∈ history, f (p i)) =
      ∑ b ∈ available, ((permutationHistoryNext positions reference i a).card : ℝ) * f b := by
    rw [← Finset.sum_fiberwise_of_maps_to' hmap f]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [Finset.sum_const, nsmul_eq_mul, hcount b hb]
  have hone : ((n - positions.card : ℕ) : ℝ) *
      ((permutationHistoryNext positions reference i a).card : ℝ) = (history.card : ℝ) := by
    exact_mod_cast permutationHistory_next_uniform positions reference i a hi ha
  change ((n - positions.card : ℕ) : ℝ) * (∑ p ∈ history, f (p i)) =
    (history.card : ℝ) * (∑ b ∈ available, f b)
  rw [hsum, ← Finset.mul_sum, ← mul_assoc, hone]

/-- Conditional weighted sum over any unrevealed positions. The sample is one
permutation, and the formula uses its common unused-value mean. -/
theorem permutationHistory_weighted_sum {n : ℕ} (positions remaining : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (hdis : Disjoint remaining positions)
    (weights values : Fin n → ℝ) :
    ((n - positions.card : ℕ) : ℝ) *
        (∑ p ∈ permutationHistory positions reference, ∑ j ∈ remaining, weights j * values (p j)) =
      ((permutationHistory positions reference).card : ℝ) * (∑ j ∈ remaining, weights j) *
        (∑ b ∈ (positions.image reference)ᶜ, values b) := by
  let history := permutationHistory positions reference
  let available := (positions.image reference)ᶜ
  let K : ℝ := (n - positions.card : ℕ)
  let H : ℝ := history.card
  let V : ℝ := ∑ b ∈ available, values b
  have hnext (j : Fin n) (hj : j ∈ remaining) :
      K * (∑ p ∈ history, values (p j)) = H * V := by
    have hj' : j ∉ positions := (Finset.disjoint_left.mp hdis) hj
    exact permutationHistory_next_sum positions reference j hj' values
  change K * (∑ p ∈ history, ∑ j ∈ remaining, weights j * values (p j)) =
    H * (∑ j ∈ remaining, weights j) * V
  calc
    _ = ∑ j ∈ remaining, weights j * (K * (∑ p ∈ history, values (p j))) := by
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro p hp
      ring
    _ = ∑ j ∈ remaining, weights j * (H * V) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hnext j hj]
    _ = H * (∑ j ∈ remaining, weights j) * V := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- Algebra of the change in a weighted remaining-mean prediction after one
value is revealed. The one-remaining-slot case is treated separately. -/
theorem weightedReveal_increment (r w W z m : ℝ) (hr : r ≠ 1) :
    w * z + (W - w) * ((r * m - z) / (r - 1)) - W * m =
      (w - (W - w) / (r - 1)) * (z - m) := by
  have hr' : r - 1 ≠ 0 := sub_ne_zero.mpr hr
  field_simp
  ring

/-- Decreasing nonnegative weights put the conditional coefficient between
zero and the exposed weight. -/
theorem weightedReveal_coefficient (r w W : ℝ)
    (hr : 1 < r) (hlo : 0 ≤ W - w) (hhi : W - w ≤ (r - 1) * w) :
    0 ≤ w - (W - w) / (r - 1) ∧ w - (W - w) / (r - 1) ≤ w := by
  have hd : 0 < r - 1 := by linarith
  have hdiv0 : 0 ≤ (W - w) / (r - 1) := div_nonneg hlo (le_of_lt hd)
  have hdivw : (W - w) / (r - 1) ≤ w :=
    (div_le_iff₀ hd).2 (by simpa [mul_comm] using hhi)
  constructor <;> linarith

/-- With a single value left, it equals the remaining mean and the reveal
increment vanishes; no zero denominator is introduced. -/
theorem weightedReveal_last (w z m : ℝ) (hz : z = m) : w * z - w * m = 0 := by
  rw [hz]
  ring

/-- Concrete weight bounds for the remaining finite slots. -/
theorem weightedRemaining_sum_bounds {α : Type*} (s : Finset α)
    (weights : α → ℝ) (w : ℝ) (hlo : ∀ j ∈ s, 0 ≤ weights j)
    (hhi : ∀ j ∈ s, weights j ≤ w) :
    0 ≤ ∑ j ∈ s, weights j ∧ (∑ j ∈ s, weights j) ≤ (s.card : ℝ) * w := by
  constructor
  · exact Finset.sum_nonneg hlo
  · calc
      _ ≤ ∑ _j ∈ s, w := Finset.sum_le_sum hhi
      _ = _ := by simp

/-- A nonempty next-value fiber is exactly the history obtained by adding
that reveal. This permits the conditional law to be iterated. -/
theorem permutationHistoryNext_eq_insert {n : ℕ} (positions : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i a : Fin n)
    (hp : p ∈ permutationHistoryNext positions reference i a) :
    permutationHistoryNext positions reference i a = permutationHistory (insert i positions) p := by
  have hp' : (∀ j ∈ positions, p j = reference j) ∧ p i = a := by
    simpa [permutationHistoryNext, permutationHistory] using hp
  ext q
  simp only [permutationHistoryNext, permutationHistory, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.forall_mem_insert]
  constructor
  · rintro ⟨hq, hqi⟩
    refine ⟨hqi.trans hp'.2.symm, ?_⟩
    intro j hj
    exact (hq j hj).trans (hp'.1 j hj).symm
  · rintro ⟨hqi, hq⟩
    refine ⟨?_, hqi.trans hp'.2⟩
    intro j hj
    exact (hq j hj).trans (hp'.1 j hj)

/-- The new history removes precisely the newly observed output from the
available set. -/
theorem permutationHistoryNext_image_insert {n : ℕ} (positions : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i a : Fin n)
    (hp : p ∈ permutationHistoryNext positions reference i a) :
    (insert i positions).image p = insert a (positions.image reference) := by
  have hp' : (∀ j ∈ positions, p j = reference j) ∧ p i = a := by
    simpa [permutationHistoryNext, permutationHistory] using hp
  have heq : positions.image p = positions.image reference := by
    apply Finset.image_congr
    intro j hj
    exact hp'.1 j hj
  rw [Finset.image_insert, hp'.2, heq]

end
end Sude
