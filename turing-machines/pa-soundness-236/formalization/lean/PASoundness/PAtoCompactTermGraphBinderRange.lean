import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactAlphaMapOne

/-! Binder-allocation bounds for the concrete term-graph translator. This is
a syntactic invariant; it does not assert alpha equivalence or K derivability. -/
namespace PASoundness.PAtoCompactTermGraphBinderRange

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactMultiplicationCandidate

theorem andF_binders (a b : Formula) : (andF a b).binders = a.binders ∪ b.binders := by
  simp [andF, PASoundness.CompactNamed.Formula.not, Formula.binders]

theorem domainAt_private (base x w : Nat) (h : w ∈ (domainAt base x).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  oneMap_private (domainTemplate 0) base 0 x templates_inputs_unbound.1
    templates_names_bounded.1 w h

theorem equivAt_private (base x y w : Nat) (h : w ∈ (equivAt base x y).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  twoMap_private _ base 0 1 x y templates_inputs_unbound.2.1
    templates_inputs_unbound.2.2.1 templates_names_bounded.2.1 w h

theorem zeroAt_private (base x w : Nat) (h : w ∈ (zeroAt base x).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  oneMap_private _ base 0 x templates_inputs_unbound.2.2.2.1
    templates_names_bounded.2.2.1 w h

theorem succAt_private (base x y w : Nat) (h : w ∈ (succAt base x y).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  twoMap_private _ base 0 1 x y templates_inputs_unbound.2.2.2.2.1
    templates_inputs_unbound.2.2.2.2.2.1 templates_names_bounded.2.2.2.1 w h

theorem addAt_private (base x y z w : Nat) (h : w ∈ (addAt base x y z).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  threeMap_private _ base 30 31 32 x y z templates_inputs_unbound.2.2.2.2.2.2.1
    templates_inputs_unbound.2.2.2.2.2.2.2.1 templates_inputs_unbound.2.2.2.2.2.2.2.2.1
    templates_names_bounded.2.2.2.2.1 w h

theorem mulAt_private (base x y z w : Nat) (h : w ∈ (mulAt base x y z).binders) :
    base + 2 ≤ w ∧ w < base + 64 :=
  threeMap_private _ base 0 1 2 x y z templates_inputs_unbound.2.2.2.2.2.2.2.2.2.1
    templates_inputs_unbound.2.2.2.2.2.2.2.2.2.2.1
    templates_inputs_unbound.2.2.2.2.2.2.2.2.2.2.2 templates_names_bounded.2.2.2.2.2 w h

/-- All graph binders occur in the allocated half-open block. No bound or
distinctness assumption is made on input or output labels. -/
theorem termGraph_binder_range {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) : ∀ out base w,
    w ∈ (termGraph varName t out base).binders →
      base ≤ w ∧ w < base + termCost t := by
  induction t with
  | var a =>
      intro out base w h
      simp only [termGraph, andF_binders, Finset.mem_union] at h
      rcases h with hd | he
      · have := domainAt_private base out w hd; simp only [termCost]; omega
      · have := equivAt_private base (varName a) out w he; simp only [termCost]; omega
  | @func l f ts ih =>
      cases f with
      | zero =>
          intro out base w h
          simp only [termGraph, andF_binders, Finset.mem_union] at h
          rcases h with hd | hz
          · have := domainAt_private base out w hd; simp only [termCost]; omega
          · have := zeroAt_private base out w hz; simp only [termCost]; omega
      | succ =>
          intro out base w h
          simp only [termGraph, andF_binders, Formula.binders, Finset.mem_union,
            Finset.mem_insert] at h
          rcases h with hd | rfl | hc | hs
          · have := domainAt_private base out w hd; simp only [termCost]; omega
          · simp only [termCost]; omega
          · have := ih 0 base (base + 64) w hc; simp only [termCost]; omega
          · have := succAt_private base base out w hs; simp only [termCost]; omega
      | add =>
          intro out base w h
          simp only [termGraph, andF_binders, Formula.binders, Finset.mem_union,
            Finset.mem_insert] at h
          rcases h with hd | rfl | rfl | hl | hr | ha
          · have := domainAt_private base out w hd; simp only [termCost]; omega
          · simp only [termCost]; omega
          · simp only [termCost]; omega
          · have := ih 0 base (base + 64) w hl; simp only [termCost]; omega
          · have := ih 1 (base + 1) (base + 64 + termCost (ts 0)) w hr; simp only [termCost]; omega
          · have := addAt_private base base (base + 1) out w ha; simp only [termCost]; omega
      | mul =>
          intro out base w h
          simp only [termGraph, andF_binders, Formula.binders, Finset.mem_union,
            Finset.mem_insert] at h
          rcases h with hd | rfl | rfl | hl | hr | hm
          · have := domainAt_private base out w hd; simp only [termCost]; omega
          · simp only [termCost]; omega
          · simp only [termCost]; omega
          · have := ih 0 base (base + 64) w hl; simp only [termCost]; omega
          · have := ih 1 (base + 1) (base + 64 + termCost (ts 0)) w hr; simp only [termCost]; omega
          · have := mulAt_private base base (base + 1) out w hm; simp only [termCost]; omega

/-- A name below the allocated block is not bound by the graph. -/
theorem termGraph_below_not_binder {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) (out base x : Nat) (hx : x < base) :
    x ∉ (termGraph varName t out base).binders := by
  intro h
  have hb := termGraph_binder_range varName t out base x h
  omega

/-- On a source name below the allocation, renaming all named nodes is
literally the same as the named-IR replacement operation. No claim is made
here that the target name avoids existing binders or capture. -/
theorem termGraph_map_eq_replace_below {α : Type} (varName : α → Nat)
    (t : Peano.language.Term α) (out base x y : Nat) (hx : x < base) :
    mapNames (rename x y) (termGraph varName t out base) =
      replace x y (termGraph varName t out base) :=
  PAtoCompactAlphaMapOne.map_eq_replace x y _
    (termGraph_below_not_binder varName t out base x hx)

end PASoundness.PAtoCompactTermGraphBinderRange

#print axioms PASoundness.PAtoCompactTermGraphBinderRange.andF_binders
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.domainAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.equivAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.zeroAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.succAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.addAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.mulAt_private
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.termGraph_binder_range
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.termGraph_below_not_binder
#print axioms PASoundness.PAtoCompactTermGraphBinderRange.termGraph_map_eq_replace_below
