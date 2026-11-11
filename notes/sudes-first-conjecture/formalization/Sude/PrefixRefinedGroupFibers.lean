import Sude.CentralWindow

/-! Refining matched labelled-value and slot groups by a supplied binary
selection. This is a state invariant, not a selection or allocation theorem. -/
namespace Sude
noncomputable section

/-- Equal parent counts and equal selected counts imply equal counts in both
Boolean-refined child groups. Selection sets may contain elements outside the
finite populations; only their intersections with those populations matter. -/
theorem prefix_refined_group_fibers {S V G : Type*} [DecidableEq S]
    [DecidableEq V] [DecidableEq G]
    (slots : Finset S) (values : Finset V) (gs : S → G) (gv : V → G)
    (chosen : Finset S) (lower : Finset V)
    (hparent : ∀ g, (slots.filter (fun s => gs s = g)).card =
      (values.filter (fun v => gv v = g)).card)
    (hchosen : ∀ g, ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      ((values.filter (fun v => gv v = g)).filter (fun v => v ∈ lower)).card) :
    ∀ p : G × Bool,
      (slots.filter (fun s => (gs s, decide (s ∈ chosen)) = p)).card =
      (values.filter (fun v => (gv v, decide (v ∈ lower)) = p)).card := by
  classical
  rintro ⟨g, b⟩
  cases b with
  | false =>
    have hs := Finset.card_filter_add_card_filter_not (s := slots.filter (fun s => gs s = g))
      (fun s => s ∈ chosen)
    have hv := Finset.card_filter_add_card_filter_not (s := values.filter (fun v => gv v = g))
      (fun v => v ∈ lower)
    have hp := hparent g
    have hc := hchosen g
    have he : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∉ chosen)).card =
        ((values.filter (fun v => gv v = g)).filter (fun v => v ∉ lower)).card := by omega
    simpa [Finset.filter_filter] using he
  | true =>
    simpa [Finset.filter_filter] using hchosen g

/-- Splitting cannot increase the size of a parent slot fiber. In particular,
a singleton parent has singleton-or-empty children. -/
theorem prefix_refined_group_slot_card_le {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G) (chosen : Finset S)
    (g : G) (b : Bool) :
    (slots.filter (fun s => (gs s, decide (s ∈ chosen)) = (g,b))).card ≤
      (slots.filter (fun s => gs s = g)).card := by
  classical
  apply Finset.card_le_card
  intro s hs
  have h := (Finset.mem_filter.mp hs).2
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, (Prod.mk.inj h).1⟩

/-- A balanced split of a parent of size at most `2^(d+1)` has each
child of size at most `2^d`. -/
theorem prefix_refined_balanced_child_card_le {S G : Type*} [DecidableEq S]
    [DecidableEq G] (slots : Finset S) (gs : S → G) (chosen : Finset S)
    (g : G) (d : ℕ)
    (hchosen : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card =
      (slots.filter (fun s => gs s = g)).card / 2)
    (hsize : (slots.filter (fun s => gs s = g)).card ≤ 2 ^ (d+1)) :
    ∀ b : Bool, (slots.filter (fun s => (gs s, decide (s ∈ chosen)) = (g,b))).card ≤ 2 ^ d := by
  classical
  let q := (slots.filter (fun s => gs s = g)).card
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := slots.filter (fun s => gs s = g)) (fun s => s ∈ chosen)
  have hp : 2 ^ (d+1) = 2 ^ d * 2 := by rw [pow_succ]
  have hm := Nat.mod_lt q (by norm_num : 0 < 2)
  have hdiv := Nat.mod_add_div q 2
  intro b
  cases b with
  | false =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∉ chosen)).card ≤ 2 ^ d := by
      omega
    simpa [Finset.filter_filter] using hchild
  | true =>
    have hchild : ((slots.filter (fun s => gs s = g)).filter (fun s => s ∈ chosen)).card ≤ 2 ^ d := by
      omega
    simpa [Finset.filter_filter] using hchild

/-- A numerical width bound for every parent value group is inherited by each
refined child. Labels remain distinct even when numerical values coincide. -/
theorem prefix_refined_group_width {V G : Type*} [DecidableEq V] [DecidableEq G]
    (values : Finset V) (gv : V → G) (lower : Finset V) (x : V → ℝ) (C : ℝ)
    (hwidth : ∀ g, ∀ u ∈ values, ∀ v ∈ values,
      gv u = g → gv v = g → x v - x u ≤ C) :
    ∀ p : G × Bool, ∀ u ∈ values, ∀ v ∈ values,
      (gv u, decide (u ∈ lower)) = p →
      (gv v, decide (v ∈ lower)) = p → x v - x u ≤ C := by
  intro p u hu v hv hpu hpv
  exact hwidth p.1 u hu v hv (congrArg Prod.fst hpu) (congrArg Prod.fst hpv)

end
end Sude
