import PASoundness.PAtoCompactFreshenReplace
import PASoundness.PAtoCompactReplaceCancellation

/-! Freshening erases one capture-safe change of bound name. This establishes
literal equality of the freshened syntax, including shadowed inner binders. -/
namespace PASoundness.PAtoCompactFreshenSingleAlpha

open PASoundness.CompactNamed
open PASoundness.PAtoCompactFreshenReplace PASoundness.PAtoCompactReplaceCancellation

/-- Body allocation endpoints and the outer-binder replacements agree. -/
theorem bodies_align (x y : Nat) (f : Formula) (start : Nat)
    (hxs : x < start) (hys : y < start)
    (hx : x ∉ f.binders) (hy : y ∉ f.names)
    (hn : ∀ v ∈ f.names, v < start)
    (hnr : ∀ v ∈ (replace x y f).names, v < start) :
    (freshen (replace x y f) start hnr).next = (freshen f start hn).next ∧
    replace y (freshen (replace x y f) start hnr).next
        (freshen (replace x y f) start hnr).formula =
      replace x (freshen f start hn).next (freshen f start hn).formula := by
  have hybind : y ∉ f.binders := fun h => hy (f.binders_subset_names h)
  have he := freshen_replace x y f start hxs hys hx hybind hn hnr
  have hyfresh : y ∉ (freshen f start hn).formula.names := by
    intro h
    exact hy ((freshen f start hn).old_names y h hys)
  refine ⟨he.1, ?_⟩
  rw [he.1, he.2]
  exact replace_cancel x y (freshen f start hn).next _ hyfresh

/-- A capture-safe bound-name change has exactly the same universally
quantified freshened output when both source name bounds hold. -/
theorem freshen_all_alpha (x y : Nat) (f : Formula) (start : Nat)
    (hx : x ∉ f.binders) (hy : y ∉ f.names)
    (hl : ∀ v ∈ (Formula.all x f).names, v < start)
    (hr : ∀ v ∈ (Formula.all y (replace x y f)).names, v < start) :
    (freshen (.all x f) start hl).formula =
      (freshen (.all y (replace x y f)) start hr).formula := by
  have hxs : x < start := hl x (Finset.mem_insert_self ..)
  have hys : y < start := hr y (Finset.mem_insert_self ..)
  let hn : ∀ v ∈ f.names, v < start := fun v hv => hl v (Finset.mem_insert_of_mem hv)
  let hnr : ∀ v ∈ (replace x y f).names, v < start :=
    fun v hv => hr v (Finset.mem_insert_of_mem hv)
  have h := bodies_align x y f start hxs hys hx hy hn hnr
  change Formula.all (freshen f start hn).next
      (replace x (freshen f start hn).next (freshen f start hn).formula) =
    Formula.all (freshen (replace x y f) start hnr).next
      (replace y (freshen (replace x y f) start hnr).next
        (freshen (replace x y f) start hnr).formula)
  exact congrArg₂ Formula.all h.1.symm h.2.symm

/-- Existential counterpart of the literal freshened-output equality. -/
theorem freshen_ex_alpha (x y : Nat) (f : Formula) (start : Nat)
    (hx : x ∉ f.binders) (hy : y ∉ f.names)
    (hl : ∀ v ∈ (Formula.ex x f).names, v < start)
    (hr : ∀ v ∈ (Formula.ex y (replace x y f)).names, v < start) :
    (freshen (.ex x f) start hl).formula =
      (freshen (.ex y (replace x y f)) start hr).formula := by
  have hxs : x < start := hl x (Finset.mem_insert_self ..)
  have hys : y < start := hr y (Finset.mem_insert_self ..)
  let hn : ∀ v ∈ f.names, v < start := fun v hv => hl v (Finset.mem_insert_of_mem hv)
  let hnr : ∀ v ∈ (replace x y f).names, v < start :=
    fun v hv => hr v (Finset.mem_insert_of_mem hv)
  have h := bodies_align x y f start hxs hys hx hy hn hnr
  change Formula.ex (freshen f start hn).next
      (replace x (freshen f start hn).next (freshen f start hn).formula) =
    Formula.ex (freshen (replace x y f) start hnr).next
      (replace y (freshen (replace x y f) start hnr).next
        (freshen (replace x y f) start hnr).formula)
  exact congrArg₂ Formula.ex h.1.symm h.2.symm

/-- Alpha-renaming an outer universal binder also leaves the next allocation
label unchanged, allowing canonicalization to continue into a later branch. -/
theorem freshen_all_alpha_next (x y : Nat) (f : Formula) (start : Nat)
    (hx : x ∉ f.binders) (hy : y ∉ f.names)
    (hl : ∀ v ∈ (Formula.all x f).names, v < start)
    (hr : ∀ v ∈ (Formula.all y (replace x y f)).names, v < start) :
    (freshen (.all x f) start hl).next =
      (freshen (.all y (replace x y f)) start hr).next := by
  have hxs : x < start := hl x (Finset.mem_insert_self ..)
  have hys : y < start := hr y (Finset.mem_insert_self ..)
  let hn : ∀ v ∈ f.names, v < start := fun v hv => hl v (Finset.mem_insert_of_mem hv)
  let hnr : ∀ v ∈ (replace x y f).names, v < start :=
    fun v hv => hr v (Finset.mem_insert_of_mem hv)
  have h := bodies_align x y f start hxs hys hx hy hn hnr
  change (freshen f start hn).next + 1 = (freshen (replace x y f) start hnr).next + 1
  rw [h.1]

/-- Existential counterpart of allocation-endpoint invariance. -/
theorem freshen_ex_alpha_next (x y : Nat) (f : Formula) (start : Nat)
    (hx : x ∉ f.binders) (hy : y ∉ f.names)
    (hl : ∀ v ∈ (Formula.ex x f).names, v < start)
    (hr : ∀ v ∈ (Formula.ex y (replace x y f)).names, v < start) :
    (freshen (.ex x f) start hl).next =
      (freshen (.ex y (replace x y f)) start hr).next := by
  have hxs : x < start := hl x (Finset.mem_insert_self ..)
  have hys : y < start := hr y (Finset.mem_insert_self ..)
  let hn : ∀ v ∈ f.names, v < start := fun v hv => hl v (Finset.mem_insert_of_mem hv)
  let hnr : ∀ v ∈ (replace x y f).names, v < start :=
    fun v hv => hr v (Finset.mem_insert_of_mem hv)
  have h := bodies_align x y f start hxs hys hx hy hn hnr
  change (freshen f start hn).next + 1 = (freshen (replace x y f) start hnr).next + 1
  rw [h.1]

end PASoundness.PAtoCompactFreshenSingleAlpha

#print axioms PASoundness.PAtoCompactFreshenSingleAlpha.bodies_align
#print axioms PASoundness.PAtoCompactFreshenSingleAlpha.freshen_all_alpha
#print axioms PASoundness.PAtoCompactFreshenSingleAlpha.freshen_ex_alpha
#print axioms PASoundness.PAtoCompactFreshenSingleAlpha.freshen_all_alpha_next
#print axioms PASoundness.PAtoCompactFreshenSingleAlpha.freshen_ex_alpha_next
