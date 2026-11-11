import Sude.PrefixSplitStateSequence
import Sude.PrefixGlobalLowerMeans
import Sude.PrefixRefinementHalfBound
import Sude.PrefixChildStateMean
import Sude.PrefixDepthMeanSplit

/-! Constructing one common DP3 state step. -/
namespace Sude
noncomputable section

/-- The input value widths are controlled within each original stage. The
resulting next state uses one common slot split for all lines. -/
theorem prefix_construct_state_step {S V G L : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G] [DecidableEq L]
    (slots : Finset S) (values : Finset V) (lines : Finset L)
    (slotStage : S → G) (valueStage : V → G) (x : V → ℝ) (w : L → S → ℝ)
    (C : ℝ) (Q k : ℕ) (st : PrefixSplitKeyState S V G)
    (hC : 0 ≤ C)
    (hw : ∀ l ∈ lines, ∀ s ∈ slots, 0 ≤ w l s)
    (hweight : ∀ s ∈ slots, (∑ l ∈ lines, w l s) ≤ 5)
    (hwidth : ∀ u ∈ values, ∀ v ∈ values, valueStage u = valueStage v → x v - x u ≤ C)
    (hvalid : PrefixSplitStateValid slots values slotStage valueStage Q k st) :
    ∃ next, PrefixSplitStateValid slots values slotStage valueStage Q (k+1) next ∧
      PrefixSplitStateStep slots values lines x w C st next := by
  classical
  obtain ⟨hstageS, hstageV, hparent, hcap⟩ := hvalid
  have hwkey : ∀ p, ∀ a ∈ prefixValueFiber values st.valueKey p,
      ∀ b ∈ prefixValueFiber values st.valueKey p, x b - x a ≤ C := by
    intro p a ha b hb
    have ha' := Finset.mem_filter.mp ha
    have hb' := Finset.mem_filter.mp hb
    have hstages : valueStage a = valueStage b := by
      rw [← hstageV a ha'.1, ← hstageV b hb'.1]
      rw [ha'.2, hb'.2]
    exact hwidth a ha'.1 b hb'.1 hstages
  obtain ⟨lower, lo, hi, hlower, hlowercard, hlo, hhi, hgap, hmean⟩ :=
    prefix_global_lower_means values st.valueKey x C hC hwkey
  let m : G × List Bool → ℕ := fun p => (slots.filter (fun s => st.slotKey s = p)).card / 2
  let mean : G × List Bool → ℝ := fun p => prefixFiberMean (prefixValueFiber values st.valueKey p) x
  have hm : ∀ p, m p ≤ (slots.filter (fun s => st.slotKey s = p)).card := fun p => Nat.div_le_self _ _
  have hgap' : ∀ s ∈ slots, 0 ≤ hi (st.slotKey s) - lo (st.slotKey s) ∧
      hi (st.slotKey s) - lo (st.slotKey s) ≤ C := fun s _ => hgap (st.slotKey s)
  have hmean' : ∀ s ∈ slots, mean (st.slotKey s) =
      prefixGroupInitial slots st.slotKey m s * lo (st.slotKey s) +
        (1 - prefixGroupInitial slots st.slotKey m s) * hi (st.slotKey s) := by
    intro s hs
    have hc := hparent (st.slotKey s)
    simpa [mean, prefixGroupInitial, prefixValueFiber, m, hc] using hmean (st.slotKey s)
  obtain ⟨T, hTU, hTcard, hbound⟩ := prefix_simultaneous_depth_mean_split
    slots st.slotKey m lines w lo hi mean C hC hm hw hweight hgap' hmean'
  have hTcard' : ∀ p, ((slots.filter (fun s => st.slotKey s = p)).filter (fun s => s ∈ T)).card = m p := by
    intro p
    by_cases hp : p ∈ slots.image st.slotKey
    · have heq : (slots.filter (fun s => st.slotKey s = p)).filter (fun s => s ∈ T) =
          T.filter (fun s => st.slotKey s = p) := by
        ext s
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨⟨hsU, hsk⟩, hsT⟩
          exact ⟨hsT, hsk⟩
        · rintro ⟨hsT, hsk⟩
          exact ⟨⟨hTU hsT, hsk⟩, hsT⟩
      rw [heq]
      exact hTcard p hp
    · have hf : slots.filter (fun s => st.slotKey s = p) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro s hs
        exact hp (Finset.mem_image.mpr ⟨s, (Finset.mem_filter.mp hs).1, (Finset.mem_filter.mp hs).2⟩)
      simp [hf, m]
  have hchosen : ∀ p, ((slots.filter (fun s => st.slotKey s = p)).filter (fun s => s ∈ T)).card =
      ((values.filter (fun v => st.valueKey v = p)).filter (fun v => v ∈ lower)).card := by
    intro p
    have hh := hlowercard p
    change ((values.filter (fun v => st.valueKey v = p)).filter (fun v => v ∈ lower)).card =
      (values.filter (fun v => st.valueKey v = p)).card / 2 at hh
    rw [← hparent p] at hh
    exact (hTcard' p).trans (by simpa [m] using hh.symm)
  let next : PrefixSplitKeyState S V G :=
    ⟨fun s => prefixHistoryChild (st.slotKey s, decide (s ∈ T)),
      fun v => prefixHistoryChild (st.valueKey v, decide (v ∈ lower))⟩
  have hnextcard := prefix_history_refined_equal_fibers slots values st.slotKey st.valueKey T lower hparent hchosen
  have hnextcap := prefix_history_refined_balanced_max slots st.slotKey T Q k
    (by intro p; simpa [m] using hTcard' p) hcap
  have hnvalid : PrefixSplitStateValid slots values slotStage valueStage Q (k+1) next := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      simpa [next, prefixHistoryChild] using hstageS s hs
    · intro v hv
      simpa [next, prefixHistoryChild] using hstageV v hv
    · simpa [next] using hnextcard
    · simpa [next] using hnextcap
  refine ⟨next, hnvalid, ?_⟩
  refine ⟨T, lower, hTU, hlower, ?_, ?_, ?_⟩
  · intro s hs; rfl
  · intro v hv; rfl
  · intro l hl
    have hchild : ∀ s ∈ slots,
        prefixFiberMean (values.filter (fun v => next.valueKey v = next.slotKey s)) x =
          if s ∈ T then lo (st.slotKey s) else hi (st.slotKey s) := by
      intro s hs
      exact prefix_occupied_child_state_mean slots values lower st.slotKey st.valueKey T x lo hi
        hnextcard hlo hhi s hs
    have hsum : prefixSplitStateLineMean slots values x w next l =
        ∑ s ∈ slots, w l s * (if s ∈ T then lo (st.slotKey s) else hi (st.slotKey s)) := by
      unfold prefixSplitStateLineMean
      apply Finset.sum_congr rfl
      intro s hs
      change w l s * prefixFiberMean (values.filter (fun v => next.valueKey v = next.slotKey s)) x = _
      rw [hchild s hs]
    have hold : prefixSplitStateLineMean slots values x w st l =
        ∑ s ∈ slots, w l s * mean (st.slotKey s) := by
      rfl
    rw [hsum, hold]
    exact hbound l hl

end
end Sude
