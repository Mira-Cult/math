import PASoundness.PAtoCompactTermTranslation
import PASoundness.CompactFreshen

/-! K alpha-renaming of one bound name throughout a named formula. Repeated
bindings in disjoint branches are allowed; nested shadowing of the selected
name is excluded. The target name is fresh for all named nodes. The named
bottom constructor remains literal compact code 1. This is a single-step
binder transport, not a complete dynamic template or PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAlphaMapOne
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.CompactProof

/-- No occurrence of a selected binder shadows another occurrence of the same
binder within its scope. -/
def NoShadow (x : Nat) : Formula → Prop
  | .truth | .bottom | .member _ _ | .equal _ _ => True
  | .imp a b => NoShadow x a ∧ NoShadow x b
  | .all z a | .ex z a => (z = x → x ∉ a.binders) ∧ NoShadow x a

instance noShadowDecidable (x : Nat) : (f : Formula) → Decidable (NoShadow x f)
  | .truth | .bottom | .member _ _ | .equal _ _ => isTrue trivial
  | .imp a b => by
      change Decidable (NoShadow x a ∧ NoShadow x b)
      letI := noShadowDecidable x a
      letI := noShadowDecidable x b
      infer_instance
  | .all z a | .ex z a => by
      change Decidable ((z = x → x ∉ a.binders) ∧ NoShadow x a)
      letI := noShadowDecidable x a
      infer_instance

theorem map_eq_replace (x y : Nat) (f : Formula) (hx : x ∉ f.binders) :
    mapNames (rename x y) f = replace x y f := by
  induction f with
  | truth | bottom | member | equal => rfl
  | imp a b ia ib =>
      simp only [Formula.binders,Finset.mem_union,not_or] at hx
      simp [mapNames,replace,ia hx.1,ib hx.2]
  | all z a ih | ex z a ih =>
      simp only [Formula.binders,Finset.mem_insert,not_or] at hx
      have hzx : z ≠ x := Ne.symm hx.1
      simp [mapNames,replace,rename,hzx,ih hx.2]

/-- If x is not free, one fresh renaming of every x binder and its occurrences
is justified by finite K alpha conversion. Every encoded bottom is unchanged. -/
def alpha_map_one (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hfree : x ∉ f.free) (hy : y ∉ f.names) (hs : NoShadow x f) :
    ProofEquiv f (mapNames (rename x y) f) := by
  cases f with
  | truth => exact .refl .truth
  | bottom => exact .refl .bottom
  | member a b =>
      simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton,not_or] at hfree
      simpa [mapNames,rename,Ne.symm hfree.1,Ne.symm hfree.2] using (ProofEquiv.refl (.member a b))
  | equal a b =>
      simp only [Formula.free,Finset.mem_insert,Finset.mem_singleton,not_or] at hfree
      simpa [mapNames,rename,Ne.symm hfree.1,Ne.symm hfree.2] using (ProofEquiv.refl (.equal a b))
  | imp a b =>
      simp only [Formula.free,Formula.names,Finset.mem_union,not_or] at hfree hy
      exact ProofEquiv.implication (alpha_map_one x y a hxy hfree.1 hy.1 hs.1) (alpha_map_one x y b hxy hfree.2 hy.2 hs.2)
  | all z a =>
      simp only [Formula.names,Finset.mem_insert,not_or] at hy
      by_cases hz : z = x
      · subst z
        have hb : x ∉ a.binders := hs.1 rfl
        have h := ProofEquiv.alphaAll x y a hxy hb hy.2
        simpa [mapNames,rename,map_eq_replace x y a hb] using h
      · have hf : x ∉ a.free := by
          intro hx
          exact hfree (by simp [Formula.free,Ne.symm hz,hx])
        have h := ProofEquiv.universal z (alpha_map_one x y a hxy hf hy.2 hs.2)
        simpa [mapNames,rename,hz] using h
  | ex z a =>
      simp only [Formula.names,Finset.mem_insert,not_or] at hy
      by_cases hz : z = x
      · subst z
        have hb : x ∉ a.binders := hs.1 rfl
        have h := ProofEquiv.alphaExists x y a hxy hb hy.2
        simpa [mapNames,rename,map_eq_replace x y a hb] using h
      · have hf : x ∉ a.free := by
          intro hx
          exact hfree (by simp [Formula.free,Ne.symm hz,hx])
        have h := ProofEquiv.existential z (alpha_map_one x y a hxy hf hy.2 hs.2)
        simpa [mapNames,rename,hz] using h

termination_by f

/-- Actual first alpha step for the proposed addition formula: its cut
binder 33 can be moved to any name above its finite syntax support. -/
def addition_cut_alpha (y : Nat) (hy : 35 < y) : ProofEquiv
    PAtoCompactOrdinalAddition.additionFormula
    (mapNames (rename 33 y) PAtoCompactOrdinalAddition.additionFormula) := by
  have hn : ∀ v ∈ PAtoCompactOrdinalAddition.additionFormula.names, v ≤ 35 := by
    intro v hv
    have hs : PAtoCompactOrdinalAddition.additionFormula.names ⊆ Finset.range 36 := by decide
    have hv' := hs hv
    simp only [Finset.mem_range] at hv'
    omega
  apply alpha_map_one 33 y PAtoCompactOrdinalAddition.additionFormula (by omega)
  · decide
  · intro h
    have := hn y h
    omega
  · decide

end PASoundness.PAtoCompactAlphaMapOne
#print axioms PASoundness.PAtoCompactAlphaMapOne.alpha_map_one

#print axioms PASoundness.PAtoCompactAlphaMapOne.addition_cut_alpha
