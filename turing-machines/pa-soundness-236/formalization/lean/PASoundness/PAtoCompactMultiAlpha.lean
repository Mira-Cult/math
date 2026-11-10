import PASoundness.PAtoCompactAlphaMapOne

/-! Finite K alpha conversion of a list of selected named binders. Every
step's freshness and shadow conditions are explicit; no concrete template
transport is claimed. -/
namespace PASoundness.PAtoCompactMultiAlpha

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactTermTranslation

/-- Mapping preserves a selected no-shadow property if its binder image is
distinct from the images of all other source binders. No injectivity on free
labels is required. -/
theorem noShadow_map (a : Formula) (g : Nat → Nat) (i : Nat)
    (h : NoShadow i a)
    (hinj : ∀ j ∈ a.binders, g j = g i → j = i) :
    NoShadow (g i) (mapNames g a) := by
  induction a with
  | truth | bottom | member | equal => trivial
  | imp a b ia ib =>
      simp only [mapNames, NoShadow] at h ⊢
      refine ⟨ia h.1 ?_, ib h.2 ?_⟩
      · intro j hj he
        exact hinj j (by simpa [Formula.binders] using Finset.mem_union_left b.binders hj) he
      · intro j hj he
        exact hinj j (by simpa [Formula.binders] using Finset.mem_union_right a.binders hj) he
  | all z a ih | ex z a ih =>
      simp only [mapNames, NoShadow] at h ⊢
      refine ⟨?_, ih h.2 ?_⟩
      · intro he hm
        have hz : z = i := hinj z (by simp [Formula.binders]) he
        have hi := h.1 hz
        rw [mapNames_binders] at hm
        obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp hm
        have hji : j = i := hinj j (by simp [Formula.binders, hj]) heq
        exact hi (hji ▸ hj)
      · intro j hj he
        exact hinj j (by simp [Formula.binders, hj]) he

/-- Apply binder-name replacements in list order to the named syntax. -/
def renameSteps : List (Nat × Nat) → Formula → Formula
  | [], f => f
  | (x, y) :: rest, f => renameSteps rest (mapNames (rename x y) f)

/-- Each selected source name is not free or nested-shadowed, and its target
is distinct and absent from the complete current syntax at that step. -/
def SafeSteps : List (Nat × Nat) → Formula → Prop
  | [], _ => True
  | (x, y) :: rest, f =>
      x ≠ y ∧ x ∉ f.free ∧ y ∉ f.names ∧ NoShadow x f ∧
        SafeSteps rest (mapNames (rename x y) f)

/-- Compose the actual forward and backward K derivations for all listed
alpha moves, under the explicit per-step side conditions. -/
def multiAlpha : (steps : List (Nat × Nat)) → (f : Formula) →
    SafeSteps steps f → ProofEquiv f (renameSteps steps f)
  | [], f, _ => ProofEquiv.refl f
  | (x, y) :: rest, f, h =>
      (alpha_map_one x y f h.1 h.2.1 h.2.2.1 h.2.2.2.1).trans
        (multiAlpha rest (mapNames (rename x y) f) h.2.2.2.2)

theorem multiAlpha_forward_certificate (steps : List (Nat × Nat)) (f : Formula)
    (h : SafeSteps steps f) :
    theoremCode (certificate (multiAlpha steps f h).forward) =
      imp f.encode (renameSteps steps f).encode := certificate_correct _

theorem multiAlpha_backward_certificate (steps : List (Nat × Nat)) (f : Formula)
    (h : SafeSteps steps f) :
    theoremCode (certificate (multiAlpha steps f h).backward) =
      imp (renameSteps steps f).encode f.encode := certificate_correct _

end PASoundness.PAtoCompactMultiAlpha

#print axioms PASoundness.PAtoCompactMultiAlpha.noShadow_map
#print axioms PASoundness.PAtoCompactMultiAlpha.multiAlpha
#print axioms PASoundness.PAtoCompactMultiAlpha.multiAlpha_forward_certificate
#print axioms PASoundness.PAtoCompactMultiAlpha.multiAlpha_backward_certificate
