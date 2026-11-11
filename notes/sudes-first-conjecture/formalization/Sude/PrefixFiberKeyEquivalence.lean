import Sude.CentralWindow
import Mathlib.Logic.Equiv.Basic

/-! Final key-preserving assignment from matched finite group fibers.
The result does not construct the matching group keys or line bounds. -/
namespace Sude
noncomputable section

/-- Equal cardinalities in every group give an exact bijection between labelled
slots and values which preserves the group key. In particular, if the key
includes the original stage, the assignment stays in that stage. -/
theorem prefix_key_fiber_equivalence {S T G : Type*} [DecidableEq S] [DecidableEq T]
    [DecidableEq G] (slots : Finset S) (labels : Finset T)
    (slotKey : S → G) (labelKey : T → G)
    (hcard : ∀ g, (slots.filter (fun s => slotKey s = g)).card =
      (labels.filter (fun t => labelKey t = g)).card) :
    ∃ e : {s // s ∈ slots} ≃ {t // t ∈ labels},
      ∀ s, labelKey (e s).val = slotKey s.val := by
  classical
  let f : {s // s ∈ slots} → G := fun s => slotKey s.val
  let g : {t // t ∈ labels} → G := fun t => labelKey t.val
  have hc (k : G) : Fintype.card {s // f s = k} = Fintype.card {t // g t = k} := by
    let es : {s // f s = k} ≃ {s // s ∈ slots.filter (fun s => slotKey s = k)} :=
      ⟨fun s => ⟨s.val.val, Finset.mem_filter.mpr ⟨s.val.property, s.property⟩⟩,
       fun s => ⟨⟨s.val, (Finset.mem_filter.mp s.property).1⟩, (Finset.mem_filter.mp s.property).2⟩,
       fun s => by cases s; rfl, fun s => by cases s; rfl⟩
    let et : {t // g t = k} ≃ {t // t ∈ labels.filter (fun t => labelKey t = k)} :=
      ⟨fun t => ⟨t.val.val, Finset.mem_filter.mpr ⟨t.val.property, t.property⟩⟩,
       fun t => ⟨⟨t.val, (Finset.mem_filter.mp t.property).1⟩, (Finset.mem_filter.mp t.property).2⟩,
       fun t => by cases t; rfl, fun t => by cases t; rfl⟩
    calc
      Fintype.card {s // f s = k} = (slots.filter (fun s => slotKey s = k)).card := by
        simpa using Fintype.card_congr es
      _ = (labels.filter (fun t => labelKey t = k)).card := hcard k
      _ = Fintype.card {t // g t = k} := by
        simpa using (Fintype.card_congr et).symm
  let e : ∀ k, {s // f s = k} ≃ {t // g t = k} := fun k => Fintype.equivOfCardEq (hc k)
  exact ⟨Equiv.ofFiberEquiv e, fun s => Equiv.ofFiberEquiv_map e s⟩


/-- The value of an occupied singleton label fiber equals its mean. The
statement also permits empty fibers, whose totalized mean is never used by
a slot because the key-preserving bijection has no slot in such a fiber. -/
theorem prefix_singleton_key_fiber_value_mean {S T G : Type*}
    [DecidableEq S] [DecidableEq T] [DecidableEq G]
    (slots : Finset S) (labels : Finset T) (slotKey : S → G) (labelKey : T → G)
    (value : T → ℝ)
    (hcard : ∀ g, (slots.filter (fun s => slotKey s = g)).card =
      (labels.filter (fun t => labelKey t = g)).card)
    (hsmall : ∀ g, (labels.filter (fun t => labelKey t = g)).card ≤ 1) :
    ∃ e : {s // s ∈ slots} ≃ {t // t ∈ labels},
      (∀ s, labelKey (e s).val = slotKey s.val) ∧
      (∀ s, value (e s).val =
        (∑ t ∈ labels.filter (fun t => labelKey t = slotKey s.val), value t) /
          ((labels.filter (fun t => labelKey t = slotKey s.val)).card : ℝ)) := by
  classical
  obtain ⟨e, he⟩ := prefix_key_fiber_equivalence slots labels slotKey labelKey hcard
  refine ⟨e, he, ?_⟩
  intro s
  let B := labels.filter (fun t => labelKey t = slotKey s.val)
  have hm : (e s).val ∈ B := Finset.mem_filter.mpr ⟨(e s).property, he s⟩
  have hc : B.card = 1 := by
    have hp : 0 < B.card := Finset.card_pos.mpr ⟨(e s).val, hm⟩
    have hb : B.card ≤ 1 := hsmall (slotKey s.val)
    omega
  obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hc
  rw [ht] at hm
  have heq : (e s).val = t := by simpa using hm
  change value (e s).val = (∑ t ∈ B, value t) / (B.card : ℝ)
  rw [ht]
  simp [heq]

end
end Sude
