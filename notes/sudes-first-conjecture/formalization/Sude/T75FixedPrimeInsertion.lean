import Sude.T75UnitBracketTargets
namespace Sude
noncomputable section

/-- Inserting a fresh zero-gap coordinate uses at most the available `D/4`
midpoint slack. No primality, grid, endpoint, or target existence is asserted. -/
private theorem t75_insert_zero_gap_margin {β : Type*} [DecidableEq β]
    (S : Finset β) (low gap : β → ℕ) (z : β) (y D : ℝ)
    (hz : z ∉ S) (hgap : gap z = 0)
    (hnear : |(low z : ℝ) - y| ≤ D/4)
    (hslack : |((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 -
      (S.card : ℝ)*y| + D + D/4 ≤ ((∑ i ∈ S, gap i : ℕ) : ℝ)/2) :
    |((∑ i ∈ insert z S, low i : ℕ) : ℝ) + ((∑ i ∈ insert z S, gap i : ℕ) : ℝ)/2 -
      ((insert z S).card : ℝ)*y| + D ≤ ((∑ i ∈ insert z S, gap i : ℕ) : ℝ)/2 := by
  classical
  have hcentre : ((∑ i ∈ insert z S, low i : ℕ) : ℝ) +
      ((∑ i ∈ insert z S, gap i : ℕ) : ℝ)/2 - ((insert z S).card : ℝ)*y =
      (((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 - (S.card : ℝ)*y) +
      ((low z : ℝ) - y) := by
    simp [Finset.sum_insert, Finset.card_insert_of_notMem, hz, hgap]
    ring
  have hgaps : ((∑ i ∈ insert z S, gap i : ℕ) : ℝ) = ((∑ i ∈ S, gap i : ℕ) : ℝ) := by
    simp [Finset.sum_insert, hz, hgap]
  rw [hcentre, hgaps]
  have ha := abs_add_le (((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 - (S.card : ℝ)*y)
    ((low z : ℝ) - y)
  linarith

end
end Sude

namespace Sude
noncomputable section

private theorem t75_zero_gap_selected_index {β : Type*} [DecidableEq β]
    (S : Finset β) (low gap : β → ℕ) (z : β)
    (hz : z ∈ S) (hzero : gap z = 0)
    (values : List ℕ) (chosen : Finset β) {n : ℕ}
    (ht : (values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)).length = n)
    (f : Fin n → ℕ)
    (hget : ∀ i, f i = (values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)).get ((finCongr ht.symm) i)) :
    ∃ i, f i = low z := by
  classical
  let targets := values ++ S.toList.map (fun i => if i ∈ chosen then low i + gap i else low i)
  have hmem : low z ∈ targets := by
    apply List.mem_append.mpr
    right
    apply List.mem_map.mpr
    exact ⟨z, Finset.mem_toList.mpr hz, by simp [hzero]⟩
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hmem
  let i : Fin n := (finCongr ht) j
  refine ⟨i, ?_⟩
  rw [hget i]
  simpa [i, finCongr] using hj
end
end Sude

namespace Sude
noncomputable section
set_option maxHeartbeats 2000000

/-- A supplied zero-gap prime can be inserted into a controlled grid without
changing its radius; the D/4 slack pays its midpoint deviation. The prime,
its window, and all other supplied target data remain explicit hypotheses. -/
theorem t75_fixed_prime_insertion {β : Type*} [DecidableEq β]
    {n m h : ℕ} (hn : Odd n) (hm : 2 ≤ m) (hh : h ∈ t75FavorableGaps)
    (S : Finset β) (z : β) (low gap : β → ℕ)
    (hz : z ∉ S) (hzero : gap z = 0) (hqprime : Nat.Prime (low z))
    (hlen : m + S.card + 1 = n) (y D : ℝ) (hD : 0 ≤ D)
    (hq : |(low z : ℝ) - y| ≤ D/4)
    (hsupply : ∀ r : ℕ, r < h → Nat.Coprime r h →
      ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p % h = r ∧ q % h = r ∧
        y-D ≤ (p : ℝ) ∧ (p : ℝ) ≤ y ∧ y ≤ (q : ℝ) ∧ (q : ℝ) ≤ y+D)
    (hcontrolledPrime : ∀ i ∈ S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i))
    (hwindow : ∀ i ∈ S, y-D ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ y+D)
    (hgrid : CompleteStepGrid S gap h (∑ i ∈ S, gap i))
    (hcenter : (Lucas.poolTotal n : ℝ) = (n : ℝ)*y)
    (hmargin : |((∑ i ∈ S, low i : ℕ) : ℝ) + ((∑ i ∈ S, gap i : ℕ) : ℝ)/2 -
      (S.card : ℝ)*y| + D + D/4 ≤ ((∑ i ∈ S, gap i : ℕ) : ℝ)/2)
    (habove : (2 : ℝ) < y-D) :
    ∃ (xs : List {r : ℕ // r < h ∧ Nat.Coprime r h})
      (lo hi : {r : ℕ // r < h ∧ Nat.Coprime r h} → ℕ)
      (values : List ℕ) (chosen : Finset β),
      xs.length = m ∧ chosen ⊆ insert z S ∧
      List.Forall₂ (fun x v => v = lo x ∨ v = hi x) xs values ∧
      let targets := values ++ (insert z S).toList.map (fun i => if i ∈ chosen then low i+gap i else low i)
      ∃ ht : targets.length = n, ∃ target : Fin n → ℕ,
        (∀ i, target i = targets.get ((finCongr ht.symm) i)) ∧
        (∑ i, target i) = Lucas.poolTotal n ∧
        (∀ i, Nat.Prime (target i) ∧ Odd (target i) ∧ |(target i : ℝ)-y| ≤ D) ∧
        ∃ i, target i = low z := by
  classical
  have hlen' : m + (insert z S).card = n := by simp [hz]; omega
  have hsumgap : (∑ i ∈ insert z S, gap i) = ∑ i ∈ S, gap i := by simp [hz, hzero]
  have hgrid' : CompleteStepGrid (insert z S) gap h (∑ i ∈ insert z S, gap i) := by
    rw [hsumgap]
    intro t ht hd
    obtain ⟨T, hT, hs⟩ := hgrid t ht hd
    exact ⟨T, hT.trans (Finset.subset_insert z S), hs⟩
  have hprime' : ∀ i ∈ insert z S, Nat.Prime (low i) ∧ Nat.Prime (low i + gap i) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simpa [hzero] using And.intro hqprime hqprime
    · exact hcontrolledPrime i hi
  have hwindow' : ∀ i ∈ insert z S, y-D ≤ (low i : ℝ) ∧ ((low i+gap i : ℕ) : ℝ) ≤ y+D := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hhq := abs_le.mp hq
      simp only [hzero, Nat.add_zero]
      constructor <;> linarith
    · exact hwindow i hi
  have hmargin' : |((∑ i ∈ insert z S, low i : ℕ) : ℝ) +
      ((∑ i ∈ insert z S, gap i : ℕ) : ℝ)/2 - ((insert z S).card : ℝ)*y| + D ≤
      ((∑ i ∈ insert z S, gap i : ℕ) : ℝ)/2 := by
    exact t75_insert_zero_gap_margin S low gap z y D hz hzero hq hmargin
  obtain ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert⟩ :=
    t75_targets_from_unit_bracket_supply hn hm hh (insert z S) low gap hlen' y D hD hsupply
      hprime' hwindow' hgrid' hcenter hmargin' habove
  refine ⟨xs, lo, hi, values, chosen, hxs, hchosen, hchoices, ht, target, hget, hsum, hcert, ?_⟩
  exact t75_zero_gap_selected_index (insert z S) low gap z (Finset.mem_insert_self z S)
    hzero values chosen ht target hget
end
end Sude
