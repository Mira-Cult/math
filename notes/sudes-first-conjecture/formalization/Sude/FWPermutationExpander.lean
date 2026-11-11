import Sude.FWPermutationSmallUnion
import Sude.FWPermutationLargeBudget

/-! A degree-six FW expansion graph from the two proved finite cut budgets. -/
namespace Sude
noncomputable section

/-- At every order in the stated domain there are three derangements whose
labelled edge occurrences satisfy the exact FW `519/500` cut expansion.
The strict small/large split includes its equality boundary on the large
side; the existing complement reductions cover every named cut, including
the empty and full cuts. This proves only the graph property. -/
theorem fw_permutation_expander_exists {n : ℕ} (hn : 19485 ≤ n) :
    ∃ p : Fin 3 → Equiv.Perm (Fin n),
      (∀ i v, p i v ≠ v) ∧
      ∀ S : Finset (Fin n),
        519 * min S.card (n - S.card) ≤
          500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card := by
  classical
  have hsmall := fw_small_cut_union_integer_budget (show 0 < n by omega)
  have hlarge := fw_large_cut_union_integer_budget hn
  have htotal : Fintype.card (Fin 3 → Equiv.Perm (Fin n)) = (n.factorial)^3 := by
    simp [Fintype.card_perm]
  have hbudget : 27 * ((fwPermutationSmallCutBad n).card + (fwPermutationLargeCutBad n).card) <
      Fintype.card (Fin 3 → Equiv.Perm (Fin n)) := by
    rw [htotal]
    omega
  obtain ⟨p, hderange, hsmallAvoid, hlargeAvoid⟩ :=
    exists_derangement_triple_avoiding_two (show 2 ≤ n by omega)
      (fwPermutationSmallCutBad n) (fwPermutationLargeCutBad n) hbudget
  refine ⟨p, ?_, ?_⟩
  · intro i v
    exact hderange i v
  · intro S
    by_contra hnot
    have hfail : fwPermutationCutFailure p S := by
      unfold fwPermutationCutFailure
      omega
    by_cases hsize : 256 * min S.card (n - S.card) < n
    · exact hsmallAvoid (fw_small_cut_mem_of_failure S hsize hfail)
    · exact hlargeAvoid (fw_large_cut_mem_of_failure S (by omega) hfail)

end
end Sude
