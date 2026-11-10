import PASoundness.PAtoCompactCandidateDynamicReflexivity
import PASoundness.PAtoCompactQuotientLeftTransAtWitness

/-! Capture-safe private-binder relocation of the fixed quotient transitivity
proof. The three operand labels remain 0, 1, and 8. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactDynamicTransRelocation

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactQuotientLeftTransAtWitness
open PASoundness.PAtoCompactCompositionSharedTransitivity
open PASoundness.PAtoCompactSafeStepsInitial PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactTemplateBlockShift
open PASoundness.PAtoCompactEquivNoShadow PASoundness.PAtoCompactEquivStepsSyntax

def transSteps (d e : Nat) : List (Nat × Nat) :=
  [(37,d+32),(32,d+33),(33,d+34),(34,d+35),(30,d+36),(35,d+37),
   (10,d+38),(36,d+39),(2,e+4),(3,e+5),(4,e+6),(5,e+7),(6,e+8),
   (19,e+21),(20,e+22),(21,e+23),(22,e+24)]

def transMap (d e n : Nat) : Nat :=
  if n=37 then d+32 else if n=32 then d+33 else if n=33 then d+34 else
  if n=34 then d+35 else if n=30 then d+36 else if n=35 then d+37 else
  if n=10 then d+38 else if n=36 then d+39 else if n=2 then e+4 else
  if n=3 then e+5 else if n=4 then e+6 else if n=5 then e+7 else
  if n=6 then e+8 else if n=19 then e+21 else if n=20 then e+22 else
  if n=21 then e+23 else if n=22 then e+24 else n

def transFrame (d e x y z : Nat) : Formula := .imp (domainAt d x)
  (.imp (equivAt e x y) (.imp (equivAt e y z) (equivAt e x z)))

theorem transMap_shape (d e : Nat) : mapNames (transMap d e) transBody =
    transFrame d e 0 1 8 := by rfl

theorem trans_names : transBody.names =
    {0,1,2,3,4,5,6,8,10,19,20,21,22,30,32,33,34,35,36,37} := by decide

theorem trans_binders : transBody.binders =
    {2,3,4,5,6,10,19,20,21,22,30,32,33,34,35,36,37} := by decide

theorem trans_free : transBody.free = {0,1,8} := by decide

theorem trans_no_shadow (x : Nat) : NoShadow x transBody := by
  by_cases h : x ∈ transBody.binders
  · have hh : ∀ x ∈ transBody.binders, NoShadow x transBody := by
      rw [trans_binders]
      decide
    exact hh x h
  · exact noShadow_of_not_binder transBody x h

theorem trans_initial_safe (d e : Nat) (hd : 50 ≤ d) (hde : d+39 < e+2) :
    InitialSafe (transSteps d e) transBody := by
  refine ⟨?_, ?_, trans_no_shadow⟩
  · intro p hp
    simp only [transSteps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [trans_free, trans_names, Finset.mem_insert, Finset.mem_singleton,
        not_or] <;> omega
  · simp only [transSteps, List.map_cons, List.map_nil, List.nodup_cons, List.nodup_nil,
      List.mem_cons, List.not_mem_nil, not_false_eq_true, not_or, and_true]
    omega

theorem trans_step_hit (d e : Nat) (hd : 100 ≤ d) (he : d+100 ≤ e)
    (x y : Nat) (hm : (x,y) ∈ transSteps d e) : applySteps (transSteps d e) x = y := by
  apply applySteps_hit
  · exact hm
  · intro z hz
    simp only [transSteps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hz
    omega
  · intro p hp
    obtain ⟨u,v⟩ := p
    simp only [transSteps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm hp
    simp only
    omega

theorem trans_steps_shape (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    renameSteps (transSteps d e) transBody = transFrame d e 0 1 8 := by
  rw [renameSteps_eq_map, ← transMap_shape]
  apply PASoundness.PAtoCompactMapNamesCongr.mapNames_congr
  intro n hn
  rw [trans_names] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [transMap, ↓reduceIte] <;>
    first | (apply trans_step_hit d e hd hde; solve | simp [transSteps]) |
      (apply applySteps_avoid; intro p hp; simp [transSteps] at hp;
       rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

/-- The original finite K transitivity proof, with all private binders moved
above the operands and split into independent candidate/equivalence blocks. -/
def relocated_transitivity (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    KDerivation (transFrame d e 0 1 8).encode := by
  have hs := initial_safe_steps (transSteps d e) transBody
    (trans_initial_safe d e (by omega) (by omega))
  have hh := multiAlpha (transSteps d e) transBody hs
  rw [trans_steps_shape d e hd hde] at hh
  have h : KDerivation transBody.encode := by
    rw [trans_body_code]
    exact shared_candidate_transitivity
  exact .mp h hh.forward

theorem relocated_transitivity_certificate (d e : Nat) (hd : 100 ≤ d) (hde : d+100 ≤ e) :
    theoremCode (certificate (relocated_transitivity d e hd hde)) =
      (transFrame d e 0 1 8).encode := certificate_correct _

end PASoundness.PAtoCompactDynamicTransRelocation

#print axioms PASoundness.PAtoCompactDynamicTransRelocation.relocated_transitivity
#print axioms PASoundness.PAtoCompactDynamicTransRelocation.relocated_transitivity_certificate
