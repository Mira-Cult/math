import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactScopedAlphaInvariant

/-! Capture-sensitive syntax ingredients for an addition term node whose
private blocks have been rebased. No K proof transport is claimed here. -/
namespace PASoundness.PAtoCompactAddTermBody

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactFreeNames PASoundness.PAtoCompactTermGraphBinderRange
open PASoundness.PAtoCompactTermGraphReplace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactScopedAlphaInvariant

/-- The body of an addition node with its private blocks allocated at `base`
and its two output witnesses retained separately. -/
def rebasedBody {α : Type} (v : α → Nat) (l r : Peano.language.Term α)
    (w0 w1 base out : Nat) : Formula :=
  andF (termGraph v l w0 (base + 64))
    (andF (termGraph v r w1 (base + 64 + termCost l)) (addAt base w0 w1 out))

theorem addAt_below_not_binder (base a b out x : Nat) (hx : x < base + 2) :
    x ∉ (addAt base a b out).binders := by
  intro h
  have hl := addAt_private base a b out x h
  omega

/-- Below its private block, replacement changes only the addition template's
input labels; the destination's capture safety is a separate condition. -/
theorem replace_addAt (base a b out x y : Nat) (hx : x < base + 2) :
    replace x y (addAt base a b out) =
      addAt base (rename x y a) (rename x y b) (rename x y out) := by
  rw [← map_eq_replace x y (addAt base a b out) (addAt_below_not_binder base a b out x hx)]
  unfold addAt
  rw [mapNames_compose]
  congr 1
  funext z
  by_cases h0 : z = 30
  · simp [threeMap, h0]
  · by_cases h1 : z = 31
    · simp [threeMap, h1]
    · by_cases h2 : z = 32
      · simp [threeMap, h2]
      · have hne : base + 2 + z ≠ x := by omega
        simp [threeMap, h0, h1, h2, rename, hne]

/-- Every binder in the rebased body is at least `base + 2`. -/
theorem body_below_not_binder {α : Type} (v : α → Nat) (l r : Peano.language.Term α)
    (w0 w1 base out x : Nat) (hx : x < base + 2) :
    x ∉ (rebasedBody v l r w0 w1 base out).binders := by
  intro h
  simp only [rebasedBody, andF_binders, Finset.mem_union] at h
  rcases h with hl | hr | ha
  · have hh := termGraph_binder_range v l w0 (base + 64) x hl
    omega
  · have hh := termGraph_binder_range v r w1 (base + 64 + termCost l) x hr
    omega
  · exact addAt_below_not_binder base w0 w1 out x hx ha

/-- A small name absent from the source-variable image, witnesses and output
is absent from every named node of the body. -/
theorem small_not_body_names {α : Type} [DecidableEq α]
    (v : α → Nat) (l r : Peano.language.Term α) (w0 w1 base out x : Nat)
    (hx : x < base + 2) (h0 : x ≠ w0) (h1 : x ≠ w1) (hout : x ≠ out)
    (hl : ∀ a ∈ l.varFinset, x ≠ v a) (hr : ∀ a ∈ r.varFinset, x ≠ v a) :
    x ∉ (rebasedBody v l r w0 w1 base out).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with hf | hb
  · simp only [rebasedBody, andF_free, Finset.mem_union] at hf
    rcases hf with hf | hf | hf
    · have hh := termGraph_free_subset v l w0 (base + 64) hf
      rcases Finset.mem_union.mp hh with hm | hm
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
        exact hl a ha he.symm
      · exact h0 (Finset.mem_singleton.mp hm)
    · have hh := termGraph_free_subset v r w1 (base + 64 + termCost l) hf
      rcases Finset.mem_union.mp hh with hm | hm
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hm
        exact hr a ha he.symm
      · exact h1 (Finset.mem_singleton.mp hm)
    · have hh := addAt_free base w0 w1 out hf
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with h | h | h
      · exact h0 h
      · exact h1 h
      · exact hout h
  · exact body_below_not_binder v l r w0 w1 base out x hx hb

/-- Replacement commutes with the rebased body when the source name lies
below all private binders. Both child name maps and all operands are updated. -/
theorem replace_rebasedBody {α : Type} [DecidableEq α]
    (v : α → Nat) (l r : Peano.language.Term α) (w0 w1 base out x y : Nat)
    (hx : x < base + 2) :
    replace x y (rebasedBody v l r w0 w1 base out) =
      rebasedBody (rename x y ∘ v) l r (rename x y w0) (rename x y w1) base
        (rename x y out) := by
  unfold rebasedBody andF
  simp only [CompactNamed.Formula.not, replace]
  rw [replace_termGraph v l w0 (base + 64) x y (by omega)]
  rw [replace_termGraph v r w1 (base + 64 + termCost l) x y (by omega)]
  rw [replace_addAt base w0 w1 out x y hx]

/-- First move of the inner witness; input labels and output remain fixed. -/
theorem replace_inner_witness {α : Type} [DecidableEq α]
    (v : α → Nat) (l r : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (hl : ∀ a ∈ l.varFinset, v a < old) (hr : ∀ a ∈ r.varFinset, v a < old) :
    replace (old + 1) (base + 1) (rebasedBody v l r old (old + 1) base out) =
      rebasedBody v l r old (base + 1) base out := by
  rw [replace_rebasedBody v l r old (old + 1) base out (old + 1) (base + 1) (by omega)]
  have hleft : ∀ a ∈ l.varFinset, (rename (old + 1) (base + 1) ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old + 1 by have := hl a ha; omega]
  have hright : ∀ a ∈ r.varFinset, (rename (old + 1) (base + 1) ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old + 1 by have := hr a ha; omega]
  unfold rebasedBody
  rw [termGraph_name_agree l _ v hleft, termGraph_name_agree r _ v hright]
  simp [rename, show out ≠ old + 1 by omega]

/-- Then move the outer witness while keeping the new inner witness fixed. -/
theorem replace_outer_witness {α : Type} [DecidableEq α]
    (v : α → Nat) (l r : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (hl : ∀ a ∈ l.varFinset, v a < old) (hr : ∀ a ∈ r.varFinset, v a < old) :
    replace old base (rebasedBody v l r old (base + 1) base out) =
      rebasedBody v l r base (base + 1) base out := by
  rw [replace_rebasedBody v l r old (base + 1) base out old base (by omega)]
  have hleft : ∀ a ∈ l.varFinset, (rename old base ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old by have := hl a ha; omega]
  have hright : ∀ a ∈ r.varFinset, (rename old base ∘ v) a = v a := by
    intro a ha
    simp [rename, show v a ≠ old by have := hr a ha; omega]
  unfold rebasedBody
  rw [termGraph_name_agree l _ v hleft, termGraph_name_agree r _ v hright]
  simp [rename, show base + 1 ≠ old by omega, show out ≠ old by omega]

/-- Capture-safe K alpha conversion of the two existential output witnesses,
with both child terms and the addition graph already rebased. -/
def rebased_exists_alpha {α : Type} [DecidableEq α]
    (v : α → Nat) (l r : Peano.language.Term α) (old base out : Nat)
    (ho : old + 1 < base) (hout : out < old)
    (hl : ∀ a ∈ l.varFinset, v a < old) (hr : ∀ a ∈ r.varFinset, v a < old) :
    ProofEquiv (.ex old (.ex (old + 1) (rebasedBody v l r old (old + 1) base out)))
      (.ex base (.ex (base + 1) (rebasedBody v l r base (base + 1) base out))) := by
  have hinner := ProofEquiv.alphaExists (old + 1) (base + 1)
    (rebasedBody v l r old (old + 1) base out) (by omega)
    (body_below_not_binder v l r old (old + 1) base out (old + 1) (by omega))
    (small_not_body_names v l r old (old + 1) base out (base + 1) (by omega)
      (by omega) (by omega) (by omega)
      (by intro a ha; have := hl a ha; omega) (by intro a ha; have := hr a ha; omega))
  rw [replace_inner_witness v l r old base out ho hout hl hr] at hinner
  have houter := ProofEquiv.alphaExists old base
    (.ex (base + 1) (rebasedBody v l r old (base + 1) base out)) (by omega)
    (by simp only [Formula.binders, Finset.mem_insert, not_or];
        exact ⟨by omega, body_below_not_binder v l r old (base + 1) base out old (by omega)⟩)
    (by simp only [Formula.names, Finset.mem_insert, not_or];
        exact ⟨by omega, small_not_body_names v l r old (base + 1) base out base (by omega)
          (by omega) (by omega) (by omega)
          (by intro a ha; have := hl a ha; omega) (by intro a ha; have := hr a ha; omega)⟩)
  simp only [replace, replace_outer_witness v l r old base out ho hout hl hr] at houter
  exact (ProofEquiv.existential old hinner).trans houter

end PASoundness.PAtoCompactAddTermBody

#print axioms PASoundness.PAtoCompactAddTermBody.addAt_below_not_binder
#print axioms PASoundness.PAtoCompactAddTermBody.replace_addAt
#print axioms PASoundness.PAtoCompactAddTermBody.body_below_not_binder
#print axioms PASoundness.PAtoCompactAddTermBody.small_not_body_names
#print axioms PASoundness.PAtoCompactAddTermBody.replace_rebasedBody
#print axioms PASoundness.PAtoCompactAddTermBody.replace_inner_witness
#print axioms PASoundness.PAtoCompactAddTermBody.replace_outer_witness
#print axioms PASoundness.PAtoCompactAddTermBody.rebased_exists_alpha
