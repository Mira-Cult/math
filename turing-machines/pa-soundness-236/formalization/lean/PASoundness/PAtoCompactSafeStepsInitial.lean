import PASoundness.PAtoCompactMultiAlpha
import PASoundness.PAtoCompactMapNoShadow
import PASoundness.PAtoCompactFreeNames

/-! Initial sufficient conditions for a finite sequence of safe K alpha
steps. This is generic and does not instantiate any concrete template. -/
namespace PASoundness.PAtoCompactSafeStepsInitial

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactMapNoShadow PASoundness.PAtoCompactFreeNames

theorem rename_free_subset (f : Formula) (x y : Nat) (hx : x ∉ f.free) :
    (mapNames (rename x y) f).free ⊆ f.free := by
  intro z hz
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp (mapNames_free_subset (rename x y) f hz)
  have hvx : v ≠ x := fun h => hx (h ▸ hv)
  have hv' : rename x y v = v := by simp [rename, hvx]
  rw [hv'] at he
  exact he ▸ hv

theorem rename_names_subset (f : Formula) (x y : Nat) :
    (mapNames (rename x y) f).names ⊆ insert y f.names := by
  rw [mapNames_names]
  intro z hz
  obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hz
  by_cases hvx : v = x
  · simp [rename, hvx] at he
    simp [← he]
  · simp [rename, hvx] at he
    exact Finset.mem_insert_of_mem (he ▸ hv)

theorem rename_injective_on_binders (f : Formula) (x y : Nat) (hy : y ∉ f.names) :
    ∀ u ∈ f.binders, ∀ v ∈ f.binders, rename x y u = rename x y v → u = v := by
  intro u hu v hv he
  have hyb : y ∉ f.binders := fun h => hy (f.binders_subset_names h)
  by_cases hux : u = x <;> by_cases hvx : v = x
  · exact hux.trans hvx.symm
  · simp [rename, hux, hvx] at he
    exact False.elim (hyb (he ▸ hv))
  · simp [rename, hux, hvx] at he
    exact False.elim (hyb (he ▸ hu))
  · simpa [rename, hux, hvx] using he

/-- Every input rename is initially safe, and different steps use different
fresh targets. The given no-shadow condition covers all source names. -/
def InitialSafe (steps : List (Nat × Nat)) (f : Formula) : Prop :=
  (∀ p ∈ steps, p.1 ≠ p.2 ∧ p.1 ∉ f.free ∧ p.2 ∉ f.names) ∧
  (steps.map Prod.snd).Nodup ∧ ∀ x, NoShadow x f

theorem initial_safe_steps (steps : List (Nat × Nat)) (f : Formula)
    (h : InitialSafe steps f) : SafeSteps steps f := by
  induction steps generalizing f with
  | nil => trivial
  | cons p ps ih =>
      rcases p with ⟨x, y⟩
      have hhead := h.1 (x, y) (by simp)
      have hnod := List.nodup_cons.mp h.2.1
      refine ⟨hhead.1, hhead.2.1, hhead.2.2, h.2.2 x, ?_⟩
      apply ih
      refine ⟨?_, hnod.2, ?_⟩
      · intro q hq
        have hq0 := h.1 q (by simp [hq])
        refine ⟨hq0.1, ?_, ?_⟩
        · intro hqf
          exact hq0.2.1 (rename_free_subset f x y hhead.2.1 hqf)
        · intro hqn
          have hm := rename_names_subset f x y hqn
          rcases Finset.mem_insert.mp hm with he | he
          · have htarget : q.2 ∈ ps.map Prod.snd := List.mem_map.mpr ⟨q, hq, rfl⟩
            exact hnod.1 (he ▸ htarget)
          · exact hq0.2.2 he
      · exact allNoShadow_map f (rename x y) h.2.2
          (rename_injective_on_binders f x y hhead.2.2)

end PASoundness.PAtoCompactSafeStepsInitial

#print axioms PASoundness.PAtoCompactSafeStepsInitial.initial_safe_steps
