import PASoundness.PAtoCompactSuccessorCongruence
import PASoundness.PAtoCompactDynamicTransRelocation

/-! Capture-safe relocation of raw-successor congruence. Both source-domain
transitivity conditions remain explicit finite-K antecedents. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRawSuccCongruenceRelocate
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactSuccessorCongruence PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveDomain PASoundness.PAtoCompactSuccCongruenceWitnessVacuity
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactEquivStepsSyntax
open PASoundness.PAtoCompactEquivNoShadow

def source : Formula := .imp equivalentFormula successorGoal

def steps (d e : Nat) : List (Nat × Nat) :=
  [(14,d+2),(15,d+3),(37,d+4),(38,d+5),
   (2,e+4),(3,e+5),(4,e+6),(5,e+7),(6,e+8),
   (19,e+21),(20,e+22),(21,e+23),(22,e+24)]

def relabel (d e n : Nat) : Nat :=
  if n=14 then d+2 else if n=15 then d+3 else if n=37 then d+4 else
  if n=38 then d+5 else if n=2 then e+4 else if n=3 then e+5 else
  if n=4 then e+6 else if n=5 then e+7 else if n=6 then e+8 else
  if n=19 then e+21 else if n=20 then e+22 else if n=21 then e+23 else
  if n=22 then e+24 else n

def frame (d e x y s t : Nat) : Formula := .imp (equivAt e x y)
  (.imp (namedSuccessor x s (d+2)) (.imp (namedSuccessor y t (d+3))
    (.imp (namedTransitive x (d+4) (d+5)) (.imp (namedTransitive y (d+4) (d+5))
      (equivAt e s t)))))

theorem relabel_shape (d e : Nat) : mapNames (relabel d e) source = frame d e 0 1 7 8 := by rfl

theorem source_names : source.names =
    {0,1,2,3,4,5,6,7,8,14,15,19,20,21,22,37,38} := by decide

theorem source_binders : source.binders =
    {2,3,4,5,6,14,15,19,20,21,22,37,38} := by decide

theorem source_free : source.free = {0,1,7,8} := by decide

theorem source_no_shadow (x : Nat) : NoShadow x source := by
  by_cases h : x ∈ source.binders
  · have hh : ∀ x ∈ source.binders, NoShadow x source := by rw [source_binders]; decide
    exact hh x h
  · exact noShadow_of_not_binder source x h

theorem initial_safe (d e : Nat) (hd : 50 ≤ d) (hde : d+5 < e+4) :
    InitialSafe (steps d e) source := by
  refine ⟨?_, ?_, source_no_shadow⟩
  · intro p hp
    simp only [steps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [source_free, source_names, Finset.mem_insert, Finset.mem_singleton, not_or] <;> omega
  · simp only [steps, List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    omega

theorem step_hit (d e : Nat) (hd : 100 ≤ d) (he : d+100 ≤ e)
    (x y : Nat) (hm : (x,y) ∈ steps d e) : applySteps (steps d e) x = y := by
  apply applySteps_hit
  · exact hm
  · intro z hz
    simp only [steps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hz
    omega
  · intro p hp
    obtain ⟨u,v⟩ := p
    simp only [steps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hp
    simp only
    omega

theorem steps_shape (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    renameSteps (steps d e) source = frame d e 0 1 7 8 := by
  rw [renameSteps_eq_map, ← relabel_shape]
  apply PASoundness.PAtoCompactMapNamesCongr.mapNames_congr
  intro n hn
  rw [source_names] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [relabel, ↓reduceIte] <;>
    first | (apply step_hit d e hd hde; solve | simp [steps]) |
      (apply applySteps_avoid; intro p hp; simp [steps] at hp;
       rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

def relocated (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    KDerivation (frame d e 0 1 7 8).encode := by
  have hs := initial_safe_steps (steps d e) source (initial_safe d e (by omega) (by omega))
  have hh := multiAlpha (steps d e) source hs
  rw [steps_shape d e hd hde] at hh
  have h : KDerivation source.encode := by exact successor_congruence
  exact .mp h hh.forward

end PASoundness.PAtoCompactRawSuccCongruenceRelocate

#print axioms PASoundness.PAtoCompactRawSuccCongruenceRelocate.relocated
