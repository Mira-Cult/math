import Sude.PrefixLabelSelectionAdapter
import Sude.PrefixSelectionMeanShift
import Sude.PrefixSelectionBudgetStrict
import Sude.PrefixThreeSelectionArithmetic

/-! Joint diagonal and partner selections from the original labelled stage
populations. The selected sets are all in the same stage populations. -/
namespace Sude
noncomputable section

/-- Select three disjoint stage families with the PD3--PD6 aggregate errors.
This is selection only; it does not place the labels or prove a line bound. -/
theorem prefix_three_global_selections {J α : Type*} [Fintype J] [DecidableEq J]
    [DecidableEq α] (A : J → Finset α) (v : J → α → ℝ) (n d : ℕ) (C : ℝ)
    (hn : 3 ≤ n) (hd : 2 ≤ d) (hC : 0 ≤ C)
    (hcard : ∀ j, (A j).card = d * (n+8))
    (hwidth : ∀ j, ∀ a ∈ A j, ∀ b ∈ A j, v j b - v j a ≤ C) :
    ∃ T U V : J → Finset α,
      (∀ j, T j ⊆ A j ∧ U j ⊆ A j \ T j ∧ V j ⊆ A j \ (T j ∪ U j) ∧
        (T j).card = 2*d ∧ (U j).card = 2*d ∧ (V j).card = 4*d) ∧
      let μ := fun j => (∑ a ∈ A j, v j a) / (d * (n+8) : ℕ)
      let E1 := (∑ j, ∑ a ∈ T j, v j a) - ((2*d : ℕ) : ℝ) * ∑ j, μ j
      let D2 := (∑ j, ∑ a ∈ U j, v j a) - ((2*d : ℕ) : ℝ) * ∑ j, μ j
      let E2 := (∑ j, ∑ a ∈ T j ∪ U j, v j a) - ((4*d : ℕ) : ℝ) * ∑ j, μ j
      let E3 := (∑ j, ∑ a ∈ (T j ∪ U j) ∪ V j, v j a) - ((8*d : ℕ) : ℝ) * ∑ j, μ j
      |E1| ≤ C/2 ∧ |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*C ∧
        |E2| ≤ ((n+5 : ℝ)/(n+6))*C ∧ |E3| ≤ (3/2:ℝ)*C ∧
        (0 < C → |E3| < (3/2:ℝ)*C) := by
  classical
  let M := d * (n+8)
  let r := 2*d
  let q := 4*d
  obtain ⟨hrM, hrrem, hqM, hpos1, hpos2, hrem1eq, hrem2eq⟩ :=
    prefix_three_selection_natural_arithmetic n d hn hd
  obtain ⟨T, hT, hE1⟩ := prefix_global_finset_select A r v C hC (fun j => by rw [hcard]; exact hrM) hwidth
  have hrem1 : ∀ j, (A j \ T j).card = M-r := by
    intro j
    rw [Finset.card_sdiff_of_subset (hT j).1, hcard j, (hT j).2]
  have hw1 : ∀ j, ∀ a ∈ A j \ T j, ∀ b ∈ A j \ T j, v j b - v j a ≤ C := by
    intro j a ha b hb
    exact hwidth j a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  obtain ⟨U, hU, heps2⟩ := prefix_global_finset_select (fun j => A j \ T j) r v C hC
    (fun j => by rw [hrem1]; exact hrrem) hw1
  have hdis : ∀ j, Disjoint (T j) (U j) := by
    intro j
    exact Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp ((hU j).1 hb)).2 ha)
  have hTU : ∀ j, T j ∪ U j ⊆ A j := by
    intro j a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (hT j).1 ha
    · exact (Finset.mem_sdiff.mp ((hU j).1 ha)).1
  have hcardTU : ∀ j, (T j ∪ U j).card = r+r := by
    intro j
    rw [Finset.card_union_of_disjoint (hdis j), (hT j).2, (hU j).2]
  have hrem2 : ∀ j, (A j \ (T j ∪ U j)).card = M-(r+r) := by
    intro j
    rw [Finset.card_sdiff_of_subset (hTU j), hcard j, hcardTU j]
  have hw2 : ∀ j, ∀ a ∈ A j \ (T j ∪ U j), ∀ b ∈ A j \ (T j ∪ U j), v j b - v j a ≤ C := by
    intro j a ha b hb
    exact hwidth j a (Finset.mem_sdiff.mp ha).1 b (Finset.mem_sdiff.mp hb).1
  obtain ⟨V, hV, heps3⟩ := prefix_global_finset_select (fun j => A j \ (T j ∪ U j)) q v C hC
    (fun j => by rw [hrem2]; exact hqM) hw2
  refine ⟨T, U, V, ?_, ?_⟩
  · intro j
    exact ⟨(hT j).1, (hU j).1, (hV j).1, (hT j).2, (hU j).2, (hV j).2⟩
  · let μ : J → ℝ := fun j => (∑ a ∈ A j, v j a) / M
    let μ1 : J → ℝ := fun j => (∑ a ∈ A j \ T j, v j a) / ((M-r : ℕ) : ℝ)
    let μ2 : J → ℝ := fun j => (∑ a ∈ A j \ (T j ∪ U j), v j a) / ((M-(r+r) : ℕ) : ℝ)
    let E1 : ℝ := (∑ j, ∑ a ∈ T j, v j a) - (r : ℝ) * ∑ j, μ j
    let D2 : ℝ := (∑ j, ∑ a ∈ U j, v j a) - (r : ℝ) * ∑ j, μ j
    let E2 : ℝ := (∑ j, ∑ a ∈ T j ∪ U j, v j a) - ((r+r : ℕ) : ℝ) * ∑ j, μ j
    let E3 : ℝ := (∑ j, ∑ a ∈ (T j ∪ U j) ∪ V j, v j a) - ((r+r+q : ℕ) : ℝ) * ∑ j, μ j
    let eps2 : ℝ := (∑ j, ∑ a ∈ U j, v j a) - (r : ℝ) * ∑ j, μ1 j
    let eps3 : ℝ := (∑ j, ∑ a ∈ V j, v j a) - (q : ℝ) * ∑ j, μ2 j
    have he1 : |E1| ≤ C/2 := by
      simpa [E1, μ, M, r, hcard] using hE1
    have he2 : |eps2| ≤ C/2 := by
      simpa [eps2, μ1, hrem1] using heps2
    have he3 : |eps3| ≤ C/2 := by
      simpa [eps3, μ2, hrem2] using heps3
    have hsecond := prefix_second_selection_deviation Finset.univ A T U v M r r
      (fun j _ => (hT j).1) (fun j _ => hcard j) (fun j _ => (hT j).2)
      (fun j _ => (hU j).1) (fun j _ => (hU j).2) hpos1
    have hcumulative := prefix_cumulative_selection_deviation Finset.univ A T U v M r r
      (fun j _ => (hT j).1) (fun j _ => hcard j) (fun j _ => (hT j).2)
      (fun j _ => (hU j).1) (fun j _ => (hU j).2) hpos1
    have hthird := prefix_cumulative_selection_deviation Finset.univ A (fun j => T j ∪ U j) V v M (r+r) q
      (fun j _ => hTU j) (fun j _ => hcard j) (fun j _ => hcardTU j)
      (fun j _ => (hV j).1) (fun j _ => (hV j).2) hpos2
    have hD2 : D2 = eps2 - ((r : ℝ) / ((M-r : ℕ) : ℝ)) * E1 := by
      simpa [D2, eps2, E1, μ, μ1] using hsecond
    have hE2 : E2 = (1 - ((r : ℝ) / ((M-r : ℕ) : ℝ))) * E1 + eps2 := by
      simpa [E2, E1, eps2, μ, μ1] using hcumulative.2
    have hE3 : E3 = (1 - ((q : ℝ) / ((M-(r+r) : ℕ) : ℝ))) * E2 + eps3 := by
      simpa [E3, E2, eps3, μ, μ2] using hthird.2
    obtain ⟨hrat1, hrat2⟩ := prefix_three_selection_real_ratios n d hn hd
    obtain ⟨hw1, hw2⟩ := prefix_three_selection_weight_identities n
    change (r : ℝ) / ((M-r : ℕ) : ℝ) = _ at hrat1
    change (q : ℝ) / ((M-(r+r) : ℕ) : ℝ) = _ at hrat2
    rw [hrat1] at hD2 hE2
    rw [hrat2] at hE3
    rw [hw1] at hE2
    rw [hw2] at hE3
    have hb := prefix_three_selection_budget (n : ℝ) C E1 eps2 eps3 (by positivity) hC he1 he2 he3
    rw [hE2] at hE3
    have hD2' : D2 = -(2/((n : ℝ)+6))*E1 + eps2 := by
      rw [hD2]
      ring
    have hbD : |D2| ≤ ((n+8 : ℝ)/(2*(n+6)))*C := by
      rw [hD2']
      exact hb.1
    have hbE2 : |E2| ≤ ((n+5 : ℝ)/(n+6))*C := by rw [hE2]; exact hb.2.1
    have hbE3 : |E3| ≤ (3/2:ℝ)*C := by rw [hE3]; exact hb.2.2
    have hbE3strict : 0 < C → |E3| < (3/2:ℝ)*C := by
      intro hCpos
      rw [hE3]
      exact prefix_three_selection_budget_strict (n : ℝ) C E1 eps2 eps3
        (by positivity) hCpos he1 he2 he3
    have hrr : r+r = 4*d := by dsimp [r]; omega
    have hrrq : r+r+q = 8*d := by dsimp [r, q]; omega
    dsimp only [E2] at hbE2
    rw [hrr] at hbE2
    dsimp only [E3] at hbE3
    rw [hrrq] at hbE3
    dsimp only [E3] at hbE3strict
    rw [hrrq] at hbE3strict
    dsimp only
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [E1, μ, M, r] using he1
    · simpa only [D2, μ, M, r] using hbD
    · simpa only [μ, M] using hbE2
    · simpa only [μ, M] using hbE3
    · simpa only [μ, M] using hbE3strict

end
end Sude
