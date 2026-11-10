import PASoundness.PAtoCompactTermGraphReplace
import PASoundness.PAtoCompactScopedAlphaInvariant
import PASoundness.PAtoCompactFreeNames
import PASoundness.PAtoCompactSuccTermReplacement

/-! Alpha-aligning the successor term's existential witness to an explicitly
fresh spare name. This does not construct a child graph base transport. -/
namespace PASoundness.PAtoCompactSuccTermSpareAlpha

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTermGraphReplace
open PASoundness.PAtoCompactScopedAlphaInvariant PASoundness.PAtoCompactSuccTermReplacement

def succBody {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (out b : Nat) : Formula :=
  andF (termGraph v t b (b + 64)) (succAt b b out)

def spareBody {α : Type} (v : α → Nat) (t : Peano.language.Term α)
    (out b w : Nat) : Formula :=
  andF (termGraph v t w (b + 64)) (succAt b w out)

theorem original_not_body_binder {α : Type} (v : α → Nat)
    (t : Peano.language.Term α) (out b : Nat) : b ∉ (succBody v t out b).binders := by
  intro h
  simp only [succBody, andF_binders, Finset.mem_union] at h
  rcases h with hc | hs
  · have hh := termGraph_binder_range v t b (b + 64) b hc
    omega
  · have hh := succAt_private b b out b hs
    omega

theorem spare_not_body_names {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a ≠ w) : w ∉ (succBody v t out b).names := by
  intro h
  rw [Formula.names_eq_free_union_binders] at h
  rcases Finset.mem_union.mp h with hf | hb
  · simp only [succBody, andF_free, Finset.mem_union] at hf
    rcases hf with hc | hs
    · have hh := termGraph_free_subset v t b (b + 64) hc
      rcases Finset.mem_union.mp hh with hi | ho
      · obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hi
        exact hvars a ha he
      · have he := Finset.mem_singleton.mp ho
        omega
    · have hh := succAt_free b b out hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with he | he
      · omega
      · exact hwo he
  · simp only [succBody, andF_binders, Finset.mem_union] at hb
    rcases hb with hc | hs
    · have hh := termGraph_binder_range v t b (b + 64) w hc
      omega
    · have hh := succAt_private b b out w hs
      omega

/-- A fresh spare witness gives a capture-safe K alpha-conversion of the
successor term body. The names associated with child source variables may
alias each other; each must be below the original base and distinct from the
spare witness. -/
def succBody_spare_alpha {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hout : out < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a < b ∧ v a ≠ w) :
    ProofEquiv (.ex b (succBody v t out b)) (.ex w (spareBody v t out b w)) := by
  have hbw : b ≠ w := by omega
  have halpha := ProofEquiv.alphaExists b w (succBody v t out b) hbw
    (original_not_body_binder v t out b)
    (spare_not_body_names v t out b w hw hwo (fun a ha => (hvars a ha).2))
  have hchild : replace b w (termGraph v t b (b + 64)) =
      termGraph v t w (b + 64) := by
    rw [replace_termGraph v t b (b + 64) b w (by omega)]
    simp only [rename, if_pos]
    apply termGraph_name_agree
    intro a ha
    simp [rename, show v a ≠ b by have := (hvars a ha).1; omega]
  -- `replace_succAt` from the sibling module supplies the exact successor
  -- placeholder substitution; it is not an open-formula equivalence.
  have hsucc : replace b w (succAt b b out) = succAt b w out := by
    rw [replace_succAt b b out b w (by omega)]
    simp [rename, show out ≠ b by omega]
  have hbody : replace b w (succBody v t out b) = spareBody v t out b w := by
    simp only [succBody, spareBody, andF, CompactNamed.Formula.not, replace]
    rw [hchild, hsucc]
  simpa only [hbody] using halpha

theorem succBody_spare_alpha_forward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hout : out < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a < b ∧ v a ≠ w) :
    theoremCode (certificate (succBody_spare_alpha v t out b w hw hout hwo hvars).forward) =
      imp (CompactNamed.Formula.ex b (succBody v t out b)).encode
        (CompactNamed.Formula.ex w (spareBody v t out b w)).encode := certificate_correct _

theorem succBody_spare_alpha_backward_certificate {α : Type} [DecidableEq α] (v : α → Nat)
    (t : Peano.language.Term α) (out b w : Nat)
    (hw : w < b) (hout : out < b) (hwo : w ≠ out)
    (hvars : ∀ a ∈ t.varFinset, v a < b ∧ v a ≠ w) :
    theoremCode (certificate (succBody_spare_alpha v t out b w hw hout hwo hvars).backward) =
      imp (CompactNamed.Formula.ex w (spareBody v t out b w)).encode
        (CompactNamed.Formula.ex b (succBody v t out b)).encode := certificate_correct _

end PASoundness.PAtoCompactSuccTermSpareAlpha

#print axioms PASoundness.PAtoCompactSuccTermSpareAlpha.original_not_body_binder
#print axioms PASoundness.PAtoCompactSuccTermSpareAlpha.spare_not_body_names
#print axioms PASoundness.PAtoCompactSuccTermSpareAlpha.succBody_spare_alpha
#print axioms PASoundness.PAtoCompactSuccTermSpareAlpha.succBody_spare_alpha_forward_certificate
#print axioms PASoundness.PAtoCompactSuccTermSpareAlpha.succBody_spare_alpha_backward_certificate
