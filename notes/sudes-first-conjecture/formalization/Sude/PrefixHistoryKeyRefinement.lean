import Sude.PrefixRefinedGroupFibers

/-! Recode each refined binary key as a stage and a longer Boolean history.
This is a key/fiber invariant, not a recursive allocation construction. -/
namespace Sude
noncomputable section

/-- Retain the stage and append the current binary split to the history. -/
def prefixHistoryChild {G : Type*} : (G × List Bool) × Bool → G × List Bool
  | ((g,h),b) => (g,h.concat b)

/-- Histories remember both the previous key and the latest split bit. -/
theorem prefix_history_child_injective {G : Type*} :
    Function.Injective (@prefixHistoryChild G) := by
  intro ⟨⟨g,h⟩,b⟩ ⟨⟨g',h'⟩,b'⟩ he
  have hh : (g,h.concat b) = (g',h'.concat b') := he
  obtain ⟨hgg, hll⟩ := Prod.mk.inj hh
  obtain ⟨hhs, hbb⟩ := List.concat_inj.mp hll
  subst g'; subst h'; subst b'
  rfl

/-- A child key preserves its original stage. -/
theorem prefix_history_child_stage {G : Type*} (p : (G × List Bool) × Bool) :
    (prefixHistoryChild p).1 = p.1.1 := by
  rcases p with ⟨⟨g,h⟩,b⟩
  rfl

/-- Injective recoding of a key leaves every corresponding fiber unchanged. -/
theorem prefix_injective_recode_fiber {S K J : Type*} [DecidableEq K]
    [DecidableEq J] (U : Finset S) (key : S → K) (f : K → J)
    (hf : Function.Injective f) (k : K) :
    (U.filter (fun s => f (key s) = f k)) = U.filter (fun s => key s = k) := by
  classical
  ext s
  simp [hf.eq_iff]

/-- Equal fibers remain equal under injective recoding, including target
keys outside the image, where both fibers are empty. -/
theorem prefix_injective_recode_equal_fibers {S V K J : Type*}
    [DecidableEq K] [DecidableEq J] (U : Finset S) (Vset : Finset V)
    (ks : S → K) (kv : V → K) (f : K → J) (hf : Function.Injective f)
    (hcard : ∀ k, (U.filter (fun s => ks s = k)).card =
      (Vset.filter (fun v => kv v = k)).card) :
    ∀ j, (U.filter (fun s => f (ks s) = j)).card =
      (Vset.filter (fun v => f (kv v) = j)).card := by
  classical
  intro j
  by_cases hj : ∃ k, f k = j
  · obtain ⟨k, rfl⟩ := hj
    rw [prefix_injective_recode_fiber U ks f hf k,
      prefix_injective_recode_fiber Vset kv f hf k]
    exact hcard k
  · have hu : U.filter (fun s => f (ks s) = j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs he
      exact hj ⟨ks s, he⟩
    have hv : Vset.filter (fun v => f (kv v) = j) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro v hv he
      exact hj ⟨kv v, he⟩
    simp [hu, hv]

/-- After a supplied equal-cardinality binary split, appending the split bit
to both histories preserves matching fibers for every history key. -/
theorem prefix_history_refined_equal_fibers {S V G : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G]
    (slots : Finset S) (values : Finset V) (gs : S → G × List Bool)
    (gv : V → G × List Bool) (chosen : Finset S) (lower : Finset V)
    (hparent : ∀ g, (slots.filter (fun s => gs s = g)).card =
      (values.filter (fun v => gv v = g)).card)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      ((values.filter (fun v => gv v = g)).filter (fun v => v ∈ lower)).card) :
    ∀ g, (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = g)).card =
      (values.filter (fun v => prefixHistoryChild (gv v, decide (v ∈ lower)) = g)).card := by
  exact prefix_injective_recode_equal_fibers slots values
    (fun s => (gs s, decide (s ∈ chosen))) (fun v => (gv v, decide (v ∈ lower)))
    prefixHistoryChild prefix_history_child_injective
    (prefix_refined_group_fibers slots values gs gv chosen lower hparent hchosen)

/-- A balanced binary split has the desired power-of-two size bound after
history recoding; out-of-image keys have empty fibers. -/
theorem prefix_history_refined_balanced_bound {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G × List Bool)
    (chosen : Finset S) (d : ℕ)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : ∀ g, (slots.filter (fun s => gs s = g)).card ≤ 2 ^ (d+1)) :
    ∀ k, (slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k)).card ≤ 2 ^ d := by
  classical
  intro k
  by_cases hk : ∃ p, prefixHistoryChild p = k
  · obtain ⟨⟨g,b⟩, rfl⟩ := hk
    rw [prefix_injective_recode_fiber slots
      (fun s => (gs s, decide (s ∈ chosen))) prefixHistoryChild
      prefix_history_child_injective (g,b)]
    exact prefix_refined_balanced_child_card_le slots gs chosen g d (hchosen g) (hsize g) b
  · have h : slots.filter (fun s => prefixHistoryChild (gs s, decide (s ∈ chosen)) = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro s hs he
      exact hk ⟨(gs s, decide (s ∈ chosen)), he⟩
    simp [h]


/-- A width bound in each parent value group also holds in every recoded
child group, because equal child histories have equal parent keys. -/
theorem prefix_history_refined_width {V G : Type*} [DecidableEq V] [DecidableEq G]
    (values : Finset V) (gv : V → G × List Bool) (lower : Finset V)
    (x : V → ℝ) (C : ℝ)
    (hwidth : ∀ g, ∀ u ∈ values, ∀ v ∈ values,
      gv u = g → gv v = g → x v - x u ≤ C) :
    ∀ k, ∀ u ∈ values, ∀ v ∈ values,
      prefixHistoryChild (gv u, decide (u ∈ lower)) = k →
      prefixHistoryChild (gv v, decide (v ∈ lower)) = k → x v - x u ≤ C := by
  intro k u hu v hv hku hkv
  have hp : (gv u, decide (u ∈ lower)) = (gv v, decide (v ∈ lower)) :=
    prefix_history_child_injective (hku.trans hkv.symm)
  exact hwidth (gv u) u hu v hv rfl (congrArg Prod.fst hp).symm

end
end Sude
