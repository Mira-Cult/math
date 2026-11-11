import Sude.PrefixGlobalLowerMeans
import Sude.PrefixHistoryKeyRefinement

/-! The conditional mean of an occupied child history equals its supplied
lower or upper value mean. This is a one-step identity, not an allocation. -/
namespace Sude
noncomputable section

/-- The actual value fiber of a child key is exactly the lower part of the
parent fiber when its slot was chosen, and the upper complement otherwise. -/
theorem prefix_child_value_fiber {S V G : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G] (values lower : Finset V)
    (gs : S → G × List Bool) (gv : V → G × List Bool)
    (chosen : Finset S) (s : S) :
    (values.filter (fun v => prefixHistoryChild (gv v, decide (v ∈ lower)) =
      prefixHistoryChild (gs s, decide (s ∈ chosen)))) =
    if s ∈ chosen then prefixLowerFiber values lower gv (gs s)
    else prefixValueFiber values gv (gs s) \ prefixLowerFiber values lower gv (gs s) := by
  classical
  by_cases hs : s ∈ chosen
  · simp only [hs, if_pos, prefixLowerFiber, prefixValueFiber]
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hv, he⟩
      have h := prefix_history_child_injective he
      have hk : gv v = gs s := congrArg Prod.fst h
      have hb := congrArg Prod.snd h
      have hvl : v ∈ lower := by simpa using hb
      exact ⟨⟨hv, hk⟩, hvl⟩
    · rintro ⟨⟨hv, hk⟩, hvl⟩
      refine ⟨hv, ?_⟩
      rw [hk]
      simp [hvl]
  · simp only [hs, if_false, prefixLowerFiber, prefixValueFiber]
    ext v
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hv, he⟩
      have h := prefix_history_child_injective he
      have hk : gv v = gs s := congrArg Prod.fst h
      have hb := congrArg Prod.snd h
      have hvl : v ∉ lower := by simpa using hb
      exact ⟨⟨hv, hk⟩, fun h => hvl h.2⟩
    · rintro ⟨⟨hv, hk⟩, hnot⟩
      have hvl : v ∉ lower := by intro h; exact hnot ⟨⟨hv, hk⟩, h⟩
      refine ⟨hv, ?_⟩
      rw [hk]
      simp [hvl]

/-- For a slot in the finite population, matched child-fiber cardinalities
make its value fiber nonempty. Hence the actual child mean agrees with the
corresponding lower/upper mean, even when unused child means are arbitrary. -/
theorem prefix_occupied_child_state_mean {S V G : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G] (slots : Finset S) (values lower : Finset V)
    (gs : S → G × List Bool) (gv : V → G × List Bool)
    (chosen : Finset S) (x : V → ℝ) (lo hi : G × List Bool → ℝ)
    (hmatch : ∀ k,
      (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k)).card =
      (values.filter (fun v => prefixHistoryChild (gv v, decide (v ∈ lower)) = k)).card)
    (hlo : ∀ k, (prefixLowerFiber values lower gv k).Nonempty →
      lo k = prefixFiberMean (prefixLowerFiber values lower gv k) x)
    (hhi : ∀ k, (prefixValueFiber values gv k \ prefixLowerFiber values lower gv k).Nonempty →
      hi k = prefixFiberMean (prefixValueFiber values gv k \ prefixLowerFiber values lower gv k) x)
    (s : S) (hs : s ∈ slots) :
    prefixFiberMean (values.filter (fun v => prefixHistoryChild (gv v, decide (v ∈ lower)) =
      prefixHistoryChild (gs s, decide (s ∈ chosen)))) x =
      if s ∈ chosen then lo (gs s) else hi (gs s) := by
  classical
  let key := prefixHistoryChild (gs s, decide (s ∈ chosen))
  have hpos : 0 < (slots.filter (fun t => prefixHistoryChild (gs t, decide (t ∈ chosen)) = key)).card := by
    apply Finset.card_pos.mpr
    exact ⟨s, Finset.mem_filter.mpr ⟨hs, rfl⟩⟩
  have hnonempty : (values.filter (fun v => prefixHistoryChild (gv v, decide (v ∈ lower)) = key)).Nonempty := by
    apply Finset.card_pos.mp
    rw [← hmatch key]
    exact hpos
  have hfiber := prefix_child_value_fiber values lower gs gv chosen s
  rw [hfiber] at hnonempty ⊢
  by_cases hsc : s ∈ chosen
  · simp only [hsc, if_pos] at hnonempty ⊢
    exact (hlo (gs s) hnonempty).symm
  · simp only [hsc, if_false] at hnonempty ⊢
    exact (hhi (gs s) hnonempty).symm

end
end Sude
