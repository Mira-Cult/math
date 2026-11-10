import PASoundness.PAtoCompactCandidateSymmetryObjectClosed
import PASoundness.PAtoCompactCandidateDynamicReflexivity

/-! Capture-safe relocation of the fixed candidate-relative symmetry proof.
Only finite K proof data are used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDynamicSymmetryRelocate
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateSymmetryObject
open PASoundness.PAtoCompactCandidateSymmetryObjectClosed PASoundness.PAtoCompactCandidateRestrictedSymmetryClosed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrderIsoSwap PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactEquivNoShadow
open PASoundness.PAtoCompactEquivStepsSyntax

def source : Formula := replace 0 8 sourceBody

def sourceSteps (d e : Nat) : List (Nat × Nat) :=
  [(37,d+32),(32,d+33),(33,d+34),(34,d+35),(30,d+36),(35,d+37),
   (10,d+38),(36,d+39),(2,e+4),(3,e+5),(4,e+6),(5,e+7),(6,e+8),
   (19,e+21),(20,e+22),(21,e+23),(22,e+24)]

def sourceMap (d e n : Nat) : Nat :=
  if n=37 then d+32 else if n=32 then d+33 else if n=33 then d+34 else
  if n=34 then d+35 else if n=30 then d+36 else if n=35 then d+37 else
  if n=10 then d+38 else if n=36 then d+39 else if n=2 then e+4 else
  if n=3 then e+5 else if n=4 then e+6 else if n=5 then e+7 else
  if n=6 then e+8 else if n=19 then e+21 else if n=20 then e+22 else
  if n=21 then e+23 else if n=22 then e+24 else n

def frame (d e x y : Nat) : Formula :=
  .imp (domainAt d x) (.imp (equivAt e x y) (equivAt e y x))

theorem sourceMap_shape (d e : Nat) :
    mapNames (sourceMap d e) source = frame d e 8 1 := by rfl

theorem source_names : source.names =
    {1,8,37,32,33,34,30,35,10,36,2,3,4,5,6,19,20,21,22} := by decide

theorem source_binders : source.binders =
    {37,32,33,34,30,35,10,36,2,3,4,5,6,19,20,21,22} := by decide

theorem source_free : source.free = {1,8} := by decide

theorem source_all_noShadow (x : Nat) : NoShadow x source := by
  by_cases h : x ∈ source.binders
  · have hs : ∀ x ∈ source.binders, NoShadow x source := by rw [source_binders]; decide
    exact hs x h
  · exact noShadow_of_not_binder source x h

theorem source_initial_safe (d e : Nat) (hd : 50 ≤ d) (hde : d+39 < e+2) :
    InitialSafe (sourceSteps d e) source := by
  refine ⟨?_, ?_, source_all_noShadow⟩
  · intro p hp
    simp only [sourceSteps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [source_free, source_names, Finset.mem_insert, Finset.mem_singleton,
        not_or] <;> omega
  · simp only [sourceSteps, List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    omega

theorem source_step_hit (d e : Nat) (hd : 100 ≤ d) (he : d+100 ≤ e)
    (x y : Nat) (hm : (x,y) ∈ sourceSteps d e) : applySteps (sourceSteps d e) x = y := by
  apply applySteps_hit
  · exact hm
  · intro z hz
    simp only [sourceSteps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hz
    omega
  · intro p hp
    obtain ⟨u,v⟩ := p
    simp only [sourceSteps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hp
    simp only
    omega

theorem source_steps_shape (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    renameSteps (sourceSteps d e) source = frame d e 8 1 := by
  rw [renameSteps_eq_map, ← sourceMap_shape]
  apply PASoundness.PAtoCompactMapNamesCongr.mapNames_congr
  intro n hn
  rw [source_names] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sourceMap, ↓reduceIte] <;>
    first | (apply source_step_hit d e hd hde; solve | simp [sourceSteps]) |
      (apply applySteps_avoid; intro p hp; simp [sourceSteps] at hp;
       rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

/-- The fixed symmetry proof transported to two fresh disjoint blocks. -/
def relocated_symmetry (d e : Nat) (hd : 100 ≤ d) (he : d+100 ≤ e) :
    KDerivation (frame d e 8 1).encode := by
  have hs := initial_safe_steps (sourceSteps d e) source (source_initial_safe d e (by omega) (by omega))
  have hh := multiAlpha (sourceSteps d e) source hs
  rw [source_steps_shape d e hd he] at hh
  have h : KDerivation source.encode := by
    simpa [source, body_substitution, Formula.encode, named_candidate_code,
      equivalentEightOne, equivalentOneEight] using symmetry_at_eight
  exact .mp h hh.forward

#print axioms relocated_symmetry
end PASoundness.PAtoCompactDynamicSymmetryRelocate
