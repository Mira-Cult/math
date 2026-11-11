import Sude.DoublePairStock
import Sude.TargetRouting

/-! Sequential FC2K5 selection with the entire same-side deletion budget paid. -/
namespace Sude
noncomputable section

theorem DoublePair.valid_mono {b : DoublePair} {low high low' high' : Finset ℕ}
    (h : b.valid low' high') (hlow : low' ⊆ low) (hhigh : high' ⊆ high) :
    b.valid low high := by
  rcases h with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩
  exact ⟨hlow h₁, hlow h₂, hhigh h₃, hhigh h₄, h₅, h₆, h₇, h₈, h₉⟩

/-- The footprint of a later block is disjoint from an earlier block once
its two lower and two upper endpoints have been removed from their own sides. -/
theorem DoublePair.disjoint_after_removal (b c : DoublePair) (low high : Finset ℕ)
    (horder : ∀ a ∈ low, ∀ d ∈ high, a < d)
    (hb : b.valid low high)
    (hc : c.valid (low \ {b.low₁, b.low₂}) (high \ {b.high₁, b.high₂})) :
    Disjoint b.footprint c.footprint := by
  rcases hb with ⟨bl₁, bl₂, bh₁, bh₂, _, _, _, _, _⟩
  rcases hc with ⟨cl₁, cl₂, ch₁, ch₂, _, _, _, _, _⟩
  have hbLow : ({b.low₁, b.low₂} : Finset ℕ) ⊆ low := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hbHigh : ({b.high₁, b.high₂} : Finset ℕ) ⊆ high := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcLow : ({c.low₁, c.low₂} : Finset ℕ) ⊆ low \ {b.low₁, b.low₂} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  have hcHigh : ({c.high₁, c.high₂} : Finset ℕ) ⊆ high \ {b.high₁, b.high₂} := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' : x ∈ ({b.low₁, b.low₂} : Finset ℕ) ∨
      x ∈ ({b.high₁, b.high₂} : Finset ℕ) := by
    simpa [DoublePair.footprint, or_assoc] using hx
  have hy' : x ∈ ({c.low₁, c.low₂} : Finset ℕ) ∨
      x ∈ ({c.high₁, c.high₂} : Finset ℕ) := by
    simpa [DoublePair.footprint, or_assoc] using hy
  rcases hx' with hl | hh <;> rcases hy' with hl' | hh'
  · exact (Finset.mem_sdiff.mp (hcLow hl')).2 hl
  · exact (lt_irrefl x) (horder x (hbLow hl) x (Finset.mem_sdiff.mp (hcHigh hh')).1)
  · exact (lt_irrefl x) (horder x (Finset.mem_sdiff.mp (hcLow hl')).1 x (hbHigh hh))
  · exact (Finset.mem_sdiff.mp (hcHigh hh')).2 hh

/-- If 2k entries on each side can be paid in advance in addition to M,
then k mutually disjoint same-gap double blocks can be selected. Different
blocks may have different gaps. -/
theorem select_disjoint_double_pairs (low high differences : Finset ℕ) (M K k : ℕ)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hdiff : ∀ a ∈ low, ∀ b ∈ high, b - a ∈ differences)
    (hlow : M + 2 * k ≤ low.card) (hhigh : M + 2 * k ≤ high.card)
    (hspan : differences.card ≤ K) (hgate : K < M * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid low high) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) := by
  induction k generalizing low high with
  | zero => exact ⟨[], rfl, by simp, by simp⟩
  | succ k ih =>
    have hlM : M ≤ low.card := by omega
    have hhM : M ≤ high.card := by omega
    obtain ⟨b, hb⟩ := repeated_difference_of_square_gate low high differences M K
      horder hdiff hlM hhM hspan hgate
    let low' := low \ {b.low₁, b.low₂}
    let high' := high \ {b.high₁, b.high₂}
    have hlow' : M + 2 * k ≤ low'.card := by
      have hdel : ({b.low₁, b.low₂} : Finset ℕ).card = 2 := by simp [hb.2.2.2.2.1]
      have h := Finset.card_le_card_sdiff_add_card (s := low) (t := {b.low₁, b.low₂})
      change low.card ≤ low'.card + ({b.low₁, b.low₂} : Finset ℕ).card at h
      omega
    have hhigh' : M + 2 * k ≤ high'.card := by
      have hdel : ({b.high₁, b.high₂} : Finset ℕ).card = 2 := by simp [hb.2.2.2.2.2.1]
      have h := Finset.card_le_card_sdiff_add_card (s := high) (t := {b.high₁, b.high₂})
      change high.card ≤ high'.card + ({b.high₁, b.high₂} : Finset ℕ).card at h
      omega
    have hlowSub : low' ⊆ low := Finset.sdiff_subset
    have hhighSub : high' ⊆ high := Finset.sdiff_subset
    have ho' : ∀ a ∈ low', ∀ d ∈ high', a < d :=
      fun a ha d hd => horder a (hlowSub ha) d (hhighSub hd)
    have hd' : ∀ a ∈ low', ∀ d ∈ high', d - a ∈ differences :=
      fun a ha d hd => hdiff a (hlowSub ha) d (hhighSub hd)
    obtain ⟨blocks, hlen, hvalid, hpair⟩ :=
      ih low' high' ho' hd' hlow' hhigh'
    refine ⟨b :: blocks, by simp [hlen], ?_, ?_⟩
    · intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact hb
      · exact DoublePair.valid_mono (hvalid c hc) hlowSub hhighSub
    · apply List.pairwise_cons.mpr
      refine ⟨?_, hpair⟩
      intro c hc
      exact DoublePair.disjoint_after_removal b c low high horder hb (hvalid c hc)

/-- FC2K5 for actual prescribed-pool entries after prior deletions. Paying
2k entries on each side selects k disjoint double blocks. The bounds on the
stocks and the difference span remain explicit controller obligations. -/
theorem select_pool_double_pairs_after_deletions {n : ℕ}
    (low high removedLow removedHigh : Finset ℕ) (M lower H k : ℕ)
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ b ∈ high, b ∈ pool n)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hspan : ∀ a ∈ low, ∀ b ∈ high,
      lower ≤ b - a ∧ b - a ≤ lower + 2 * H)
    (hlow : M + 2 * k + removedLow.card ≤ low.card)
    (hhigh : M + 2 * k + removedHigh.card ≤ high.card)
    (hgate : H + 1 < M * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (low \ removedLow) (high \ removedHigh)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) := by
  let L := low \ removedLow
  let U := high \ removedHigh
  let differences := (L ×ˢ U).image (fun p : ℕ × ℕ => p.2 - p.1)
  have hL : L ⊆ low := Finset.sdiff_subset
  have hU : U ⊆ high := Finset.sdiff_subset
  have hLcard : M + 2 * k ≤ L.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := low) (t := removedLow)
    change low.card ≤ L.card + removedLow.card at h
    omega
  have hUcard : M + 2 * k ≤ U.card := by
    have h := Finset.card_le_card_sdiff_add_card (s := high) (t := removedHigh)
    change high.card ≤ U.card + removedHigh.card at h
    omega
  have hodd : ∀ x ∈ low ∪ high, Odd x := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, rfl⟩ := hpoolLow x hx
      exact oddPrime_odd i.val
    · obtain ⟨i, rfl⟩ := hpoolHigh x hx
      exact oddPrime_odd i.val
  have heven : ∀ a ∈ L, ∀ b ∈ U, (b - a) % 2 = 0 := by
    intro a ha b hb
    have haodd := hodd a (Finset.mem_union_left high (hL ha))
    have hbodd := hodd b (Finset.mem_union_right low (hU hb))
    obtain ⟨i, hi⟩ := haodd
    obtain ⟨j, hj⟩ := hbodd
    have hab := horder a (hL ha) b (hU hb)
    omega
  have hdiff : ∀ a ∈ L, ∀ b ∈ U, b - a ∈ differences := by
    intro a ha b hb
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩
  have hcard : differences.card ≤ H + 1 := by
    apply even_span_card_le differences lower H
    · intro d hd
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
      exact hspan a (hL (Finset.mem_product.mp hab).1) b (hU (Finset.mem_product.mp hab).2)
    · intro d hd
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hd
      exact heven a (Finset.mem_product.mp hab).1 b (Finset.mem_product.mp hab).2
  exact select_disjoint_double_pairs L U differences M (H + 1) k
    (fun a ha b hb => horder a (hL ha) b (hU hb)) hdiff hLcard hUcard hcard hgate

/-- The same selection directly accepts the source's real difference window
of length 2h, with the exact floor(h)+1 pigeonhole gate. -/
theorem select_pool_double_pairs_real_window {n : ℕ}
    (low high removedLow removedHigh : Finset ℕ) (M k : ℕ) (lower h : ℝ)
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ b ∈ high, b ∈ pool n)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hspan : ∀ a ∈ low, ∀ b ∈ high,
      lower < ((b - a : ℕ) : ℝ) ∧ ((b - a : ℕ) : ℝ) ≤ lower + 2 * h)
    (hlow : M + 2 * k + removedLow.card ≤ low.card)
    (hhigh : M + 2 * k + removedHigh.card ≤ high.card)
    (hgate : ⌊h⌋₊ + 1 < M * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (low \ removedLow) (high \ removedHigh)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) := by
  let differences := (low ×ˢ high).image (fun p : ℕ × ℕ => p.2 - p.1)
  have hM : 0 < M := by
    by_contra h
    have : M = 0 := by omega
    simp [this] at hgate
  have hL : low.Nonempty := Finset.card_pos.mp (by omega)
  have hU : high.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hL
  obtain ⟨b, hb⟩ := hU
  have hn : differences.Nonempty := by
    exact ⟨b - a, Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩⟩
  have hreal : ∀ d ∈ differences, lower < (d : ℝ) ∧ (d : ℝ) ≤ lower + 2 * h := by
    intro d hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
    exact hspan x (Finset.mem_product.mp hxy).1 y (Finset.mem_product.mp hxy).2
  have heven : ∀ d ∈ differences, d % 2 = 0 := by
    intro d hd
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hd
    have hx := (Finset.mem_product.mp hxy).1
    have hy := (Finset.mem_product.mp hxy).2
    have hxodd : Odd x := by
      obtain ⟨i, rfl⟩ := hpoolLow x hx
      exact oddPrime_odd i.val
    have hyodd : Odd y := by
      obtain ⟨i, rfl⟩ := hpoolHigh y hy
      exact oddPrime_odd i.val
    obtain ⟨i, hi⟩ := hxodd
    obtain ⟨j, hj⟩ := hyodd
    have hxy' := horder x hx y hy
    omega
  obtain ⟨least, hbounds⟩ := even_real_span_int_bounds differences lower h hreal heven hn
  apply select_pool_double_pairs_after_deletions low high removedLow removedHigh M least ⌊h⌋₊ k
    hpoolLow hpoolHigh horder
  · intro x hx y hy
    apply hbounds
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩
  · exact hlow
  · exact hhigh
  · exact hgate

/-- FC2K5 in its real-width form, retaining the exact side-deletion budget. -/
theorem select_pool_double_pairs_fc2k {n : ℕ}
    (low high removedLow removedHigh : Finset ℕ) (M k : ℕ) (lower h : ℝ)
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ b ∈ high, b ∈ pool n)
    (horder : ∀ a ∈ low, ∀ b ∈ high, a < b)
    (hspan : ∀ a ∈ low, ∀ b ∈ high,
      lower < ((b - a : ℕ) : ℝ) ∧ ((b - a : ℕ) : ℝ) ≤ lower + 2 * h)
    (hlow : M + 2 * k + removedLow.card ≤ low.card)
    (hhigh : M + 2 * k + removedHigh.card ≤ high.card)
    (hwidth : 0 ≤ h) (hgate : h + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (low \ removedLow) (high \ removedHigh)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) :=
  select_pool_double_pairs_real_window low high removedLow removedHigh M k lower h
    hpoolLow hpoolHigh horder hspan hlow hhigh (real_square_gate_implies_floor_gate M h hwidth hgate)

end
end Sude
