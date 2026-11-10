import PASoundness.CompactFreshen
import PASoundness.PAtoCompactReplaceCommutation

/-! Syntactic freshener/replacement alignment under explicit nonbinding and
name-bound hypotheses. No soundness theorem or K proof is used. -/
namespace PASoundness.PAtoCompactFreshenReplace

open PASoundness.CompactNamed
open PASoundness.PAtoCompactReplaceCommutation

theorem freshen_start_congr (f : Formula) (s t : Nat) (hst : s = t)
    (hs : ∀ v ∈ f.names, v < s) (ht : ∀ v ∈ f.names, v < t) :
    (freshen f s hs).next = (freshen f t ht).next ∧
    (freshen f s hs).formula = (freshen f t ht).formula := by
  subst t
  exact ⟨rfl, rfl⟩

theorem freshen_replace_of_commute (x y : Nat)
    (hcomm : ∀ q z f, q ≠ x → q ≠ y → z ≠ x → z ≠ y →
      replace q z (replace x y f) = replace x y (replace q z f))
    (f : Formula) (start : Nat) (hxs : x < start) (hys : y < start)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders)
    (hn : ∀ v ∈ f.names, v < start)
    (hnr : ∀ v ∈ (replace x y f).names, v < start) :
    (freshen (replace x y f) start hnr).next = (freshen f start hn).next ∧
    (freshen (replace x y f) start hnr).formula = replace x y (freshen f start hn).formula := by
  induction f generalizing start with
  | truth | bottom | member | equal => exact ⟨rfl, rfl⟩
  | imp a b ia ib =>
      have hx' : x ∉ a.binders ∧ x ∉ b.binders := by simpa [Formula.binders] using hx
      have hy' : y ∉ a.binders ∧ y ∉ b.binders := by simpa [Formula.binders] using hy
      have hxa := hx'.1
      have hxb := hx'.2
      have hya := hy'.1
      have hyb := hy'.2
      let ha : ∀ v ∈ a.names, v < start := fun v hv => hn v (Finset.mem_union_left _ hv)
      let har : ∀ v ∈ (replace x y a).names, v < start :=
        fun v hv => hnr v (Finset.mem_union_left _ hv)
      let fa := freshen a start ha
      let far := freshen (replace x y a) start har
      have h1 := ia start hxs hys hxa hya ha har
      have hnext : far.next = fa.next := h1.1
      let hb : ∀ v ∈ b.names, v < fa.next :=
        fun v hv => (hn v (Finset.mem_union_right _ hv)).trans_le fa.next_ge
      let hbr : ∀ v ∈ (replace x y b).names, v < far.next :=
        fun v hv => (hnr v (Finset.mem_union_right _ hv)).trans_le far.next_ge
      have h2 := ib far.next (by have := far.next_ge; omega)
        (by have := far.next_ge; omega) hxb hyb (by simpa [hnext] using hb) hbr
      change (freshen (replace x y b) far.next hbr).next = (freshen b fa.next hb).next ∧
        Formula.imp far.formula (freshen (replace x y b) far.next hbr).formula =
          replace x y (Formula.imp fa.formula (freshen b fa.next hb).formula)
      have h3 := freshen_start_congr b far.next fa.next hnext (by simpa [hnext] using hb) hb
      exact ⟨h2.1.trans h3.1,
        congrArg₂ Formula.imp h1.2 (h2.2.trans (congrArg (replace x y) h3.2))⟩
  | all q a ia | ex q a ia =>
      have hx' : x ≠ q ∧ x ∉ a.binders := by simpa [Formula.binders] using hx
      have hy' : y ≠ q ∧ y ∉ a.binders := by simpa [Formula.binders] using hy
      let ha : ∀ v ∈ a.names, v < start := fun v hv => hn v (Finset.mem_insert_of_mem hv)
      let har : ∀ v ∈ (replace x y a).names, v < start :=
        fun v hv => hnr v (Finset.mem_insert_of_mem hv)
      let fa := freshen a start ha
      let far := freshen (replace x y a) start har
      have h1 := ia start hxs hys hx'.2 hy'.2 ha har
      have hnext : far.next = fa.next := h1.1
      have hbody : far.formula = replace x y fa.formula := h1.2
      have hz_x : fa.next ≠ x := by have := fa.next_ge; omega
      have hz_y : fa.next ≠ y := by have := fa.next_ge; omega
      have hc := hcomm q fa.next fa.formula (Ne.symm hx'.1) (Ne.symm hy'.1) hz_x hz_y
      first
      | change far.next + 1 = fa.next + 1 ∧
          Formula.all far.next (replace q far.next far.formula) =
            replace x y (Formula.all fa.next (replace q fa.next fa.formula))
        constructor
        · omega
        · simp only [replace, hnext, hbody, hc]
      | change far.next + 1 = fa.next + 1 ∧
          Formula.ex far.next (replace q far.next far.formula) =
            replace x y (Formula.ex fa.next (replace q fa.next fa.formula))
        constructor
        · omega
        · simp only [replace, hnext, hbody, hc]

/-- Freshening commutes literally with a replacement when both names are
below the allocation start and neither is a source binder. The source and
replacement name bounds are explicit; the equalities preserve allocation
endpoints and the actual generated named formula. -/
theorem freshen_replace (x y : Nat) (f : Formula) (start : Nat)
    (hxs : x < start) (hys : y < start)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders)
    (hn : ∀ v ∈ f.names, v < start)
    (hnr : ∀ v ∈ (replace x y f).names, v < start) :
    (freshen (replace x y f) start hnr).next = (freshen f start hn).next ∧
    (freshen (replace x y f) start hnr).formula = replace x y (freshen f start hn).formula := by
  apply freshen_replace_of_commute x y
  · intro q z a hqx hqy hzx _hzy
    exact replace_commute q z x y a hqx hzx (Ne.symm hqy)
  · exact hxs
  · exact hys
  · exact hx
  · exact hy
end PASoundness.PAtoCompactFreshenReplace

#print axioms PASoundness.PAtoCompactFreshenReplace.freshen_start_congr
#print axioms PASoundness.PAtoCompactFreshenReplace.freshen_replace_of_commute
#print axioms PASoundness.PAtoCompactFreshenReplace.freshen_replace
