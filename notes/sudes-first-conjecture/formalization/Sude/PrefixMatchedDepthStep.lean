import Sude.PrefixDepthMeanSplit
import Sude.PrefixRefinedGroupFibers

/-! A single common slot/value key refinement from supplied lower labels and
child means. It does not construct the lower value sets or iterate depths. -/
namespace Sude
noncomputable section

/-- One simultaneous DP3 depth preserves every matched slot/value fiber,
provides balanced child sizes and gives one global mean increment per line.
The lower labelled set and its associated child means are supplied. -/
theorem prefix_matched_depth_step {S V K L : Type*}
    [DecidableEq S] [DecidableEq V] [DecidableEq K] [DecidableEq L]
    (U : Finset S) (A : Finset V) (ks : S → K) (kv : V → K)
    (lower : Finset V) (lines : Finset L) (w : L → S → ℝ)
    (lo hi mean : K → ℝ) (C : ℝ) (d : ℕ)
    (hC : 0 ≤ C)
    (hparent : ∀ k, (U.filter (fun s => ks s = k)).card =
      (A.filter (fun v => kv v = k)).card)
    (hchosen : ∀ k, ((A.filter (fun v => kv v = k)).filter (fun v => v ∈ lower)).card =
      (U.filter (fun s => ks s = k)).card / 2)
    (hsize : ∀ k, (U.filter (fun s => ks s = k)).card ≤ 2 ^ (d+1))
    (hw : ∀ l ∈ lines, ∀ s ∈ U, 0 ≤ w l s)
    (hweight : ∀ s ∈ U, (∑ l ∈ lines, w l s) ≤ 5)
    (hgap : ∀ s ∈ U, 0 ≤ hi (ks s) - lo (ks s) ∧ hi (ks s) - lo (ks s) ≤ C)
    (hmean : ∀ s ∈ U, mean (ks s) =
      prefixGroupInitial U ks (fun k => (U.filter (fun s => ks s = k)).card / 2) s * lo (ks s) +
        (1 - prefixGroupInitial U ks (fun k => (U.filter (fun s => ks s = k)).card / 2) s) * hi (ks s)) :
    ∃ T : Finset S, T ⊆ U ∧
      (∀ p : K × Bool,
        (U.filter (fun s => (ks s, decide (s ∈ T)) = p)).card =
        (A.filter (fun v => (kv v, decide (v ∈ lower)) = p)).card) ∧
      (∀ p : K × Bool, (U.filter (fun s => (ks s, decide (s ∈ T)) = p)).card ≤ 2 ^ d) ∧
      (∀ l ∈ lines,
        |(∑ s ∈ U, w l s * (if s ∈ T then lo (ks s) else hi (ks s))) -
          ∑ s ∈ U, w l s * mean (ks s)| ≤ 10 * C) := by
  classical
  let m : K → ℕ := fun k => (U.filter (fun s => ks s = k)).card / 2
  have hm : ∀ k, m k ≤ (U.filter (fun s => ks s = k)).card := fun k => Nat.div_le_self _ _
  obtain ⟨T, hTU, hTcard, hbound⟩ := prefix_simultaneous_depth_mean_split
    U ks m lines w lo hi mean C hC hm hw hweight hgap hmean
  have hTcard' : ∀ k, ((U.filter (fun s => ks s = k)).filter (fun s => s ∈ T)).card = m k := by
    intro k
    by_cases hk : k ∈ U.image ks
    · have heq : (U.filter (fun s => ks s = k)).filter (fun s => s ∈ T) =
          T.filter (fun s => ks s = k) := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hsU, hsk⟩, hsT⟩
          exact ⟨hsT, hsk⟩
        · rintro ⟨hsT, hsk⟩
          exact ⟨⟨hTU hsT, hsk⟩, hsT⟩
      rw [heq]
      exact hTcard k hk
    · have hf : U.filter (fun s => ks s = k) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        exact hk (Finset.mem_image.mpr ⟨s, (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩)
      simp [hf, m]
  refine ⟨T, hTU, ?_, ?_, hbound⟩
  · apply prefix_refined_group_fibers U A ks kv T lower hparent
    intro k
    exact (hTcard' k).trans (by simpa [m] using (hchosen k).symm)
  · intro ⟨k, b⟩
    exact prefix_refined_balanced_child_card_le U ks T k d (by simpa [m] using hTcard' k) (hsize k) b

end
end Sude
