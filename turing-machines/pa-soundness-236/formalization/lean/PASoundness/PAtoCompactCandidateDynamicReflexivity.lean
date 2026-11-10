import PASoundness.PAtoCompactGuardedVariableReflexivity
import PASoundness.PAtoCompactVariableTermTotality
import PASoundness.PAtoCompactEquivStepsSyntax

/-! Capture-safe relocation of the fixed candidate-reflexivity proof.
The two private blocks are deliberately disjoint and above every original
name. No semantic soundness theorem is used. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateDynamicReflexivity

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactCandidateExact
open PASoundness.PAtoCompactCandidateReflexivity PASoundness.PAtoCompactCandidateReflexiveObject
open PASoundness.PAtoCompactGuardedVariableReflexivity PASoundness.PAtoCompactDiagonalReflexiveMatrixTransport
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactSafeStepsInitial
open PASoundness.PAtoCompactMultiAlpha PASoundness.PAtoCompactVariableTermTotality
open PASoundness.PAtoCompactEquivNoShadow PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactTermGraphBinderRange PASoundness.PAtoCompactTemplateBlockShift

/-- The fixed proof uses the explicit distinguished bottom already. -/
theorem normalize_source : normalizeBottom sourceBody = sourceBody := by decide

/-- Reassign the candidate's eight and isomorphism's nine private labels. -/
def sourceSteps (d e : Nat) : List (Nat × Nat) :=
  [(41,d+32),(37,d+33),(38,d+34),(32,d+35),(0,d+36),(31,d+37),
   (34,d+38),(35,d+39),(2,e+4),(3,e+5),(4,e+6),(5,e+7),(6,e+8),
   (19,e+21),(20,e+22),(21,e+23),(22,e+24)]

def sourceMap (d e n : Nat) : Nat :=
  if n=41 then d+32 else if n=37 then d+33 else if n=38 then d+34 else
  if n=32 then d+35 else if n=0 then d+36 else if n=31 then d+37 else
  if n=34 then d+38 else if n=35 then d+39 else if n=2 then e+4 else
  if n=3 then e+5 else if n=4 then e+6 else if n=5 then e+7 else
  if n=6 then e+8 else if n=19 then e+21 else if n=20 then e+22 else
  if n=21 then e+23 else if n=22 then e+24 else n

/-- The desired dynamically allocated formulas are exactly the mapped source. -/
theorem sourceMap_shape (d e : Nat) :
    mapNames (sourceMap d e) sourceBody = .imp (domainAt d 30) (equivAt e 30 30) := by
  rfl

theorem source_names : sourceBody.names =
    {0,2,3,4,5,6,19,20,21,22,30,31,32,34,35,37,38,41} := by decide

theorem source_all_noShadow (x : Nat) : NoShadow x sourceBody := by
  by_cases h : x ∈ sourceBody.binders
  · exact source_no_shadow x h
  · exact noShadow_of_not_binder sourceBody x h

theorem source_initial_safe (d e : Nat) (hd : 50 ≤ d) (hde : d+39 < e+2) :
    InitialSafe (sourceSteps d e) sourceBody := by
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
    renameSteps (sourceSteps d e) sourceBody = .imp (domainAt d 30) (equivAt e 30 30) := by
  rw [renameSteps_eq_map, ← sourceMap_shape]
  apply PASoundness.PAtoCompactMapNamesCongr.mapNames_congr
  intro n hn
  rw [source_names] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [sourceMap, ↓reduceIte] <;>
    first | (apply source_step_hit d e hd hde; solve | simp [sourceSteps]) |
      (apply applySteps_avoid; intro p hp; simp [sourceSteps] at hp;
       rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)

def frame (d e x : Nat) : Formula := .imp (domainAt d x) (equivAt e x x)

theorem frame_not_binder (d e x w : Nat) (hd : w < d + 2) (he : w < e + 2) :
    w ∉ (frame d e x).binders := by
  intro h
  simp only [frame, Formula.binders, Finset.mem_union] at h
  rcases h with h | h
  · have := domainAt_private d x w h; omega
  · have := equivAt_private e x x w h; omega

/-- Substitution for a name below both private blocks changes the operand,
including both occurrences in the equality template. -/
theorem frame_replace (d e x y : Nat) (hd : x < d) (he : x < e) :
    replace x y (frame d e x) = frame d e y := by
  have hd' : x ∉ (domainAt d x).binders := by
    intro h
    have := domainAt_private d x x h
    omega
  have he' : x ∉ (equivAt e x x).binders := by
    intro h
    have := equivAt_private e x x x h
    omega
  have hdom : replace x y (domainAt d x) = domainAt d y := by
    rw [← map_eq_replace x y _ hd']
    have hs : ∀ i < 64, rename x y (d + i) = d + i := by
      intro i hi
      have h : d + i ≠ x := by omega
      simp [rename, h]
    simpa [rename] using domainAt_shift (rename x y) d d x hs
  have heq : replace x y (equivAt e x x) = equivAt e y y := by
    rw [← map_eq_replace x y _ he']
    have hs : ∀ i < 64, rename x y (e + i) = e + i := by
      intro i hi
      have h : e + i ≠ x := by omega
      simp [rename, h]
    simpa [rename] using equivAt_shift (rename x y) e e x x hs
  simp [frame, replace, hdom, heq]

/-- Given the literal endpoint identity, the safe sequence relocates the
existing finite reflexivity proof to the two private blocks. -/
def relocated_reflexive (d e : Nat) (hd : 50 ≤ d) (hde : d+39 < e+2)
    (hshape : renameSteps (sourceSteps d e) sourceBody = frame d e 30) :
    KDerivation (frame d e 30).encode := by
  have hs := initial_safe_steps (sourceSteps d e) sourceBody (source_initial_safe d e hd hde)
  have hh := multiAlpha (sourceSteps d e) sourceBody hs
  rw [hshape] at hh
  exact .mp candidate_reflexive hh.forward

/-- Generalize the fixed object and instantiate it with an arbitrary label
below both private blocks. The represented values may coincide. -/
def instantiate_frame (d e a : Nat) (hd : 30 < d) (he : 30 < e)
    (had : a < d+2) (hae : a < e+2)
    (h : KDerivation (frame d e 30).encode) : KDerivation (frame d e a).encode := by
  by_cases ha : a = 30
  · subst a
    exact h
  · have hg : KDerivation (allCode 30 (frame d e 30).encode) := .generalize 30 h
    have hi := universalInstance 30 a (frame d e 30) (Ne.symm ha)
      (frame_not_binder d e 30 30 (by omega) (by omega))
      (frame_not_binder d e 30 a had hae)
    rw [frame_replace d e 30 a hd he] at hi
    exact .mp hg hi

/-- Candidate-relative quotient reflexivity at any operand name below its
private block. This constructs finite K proof data without assuming either
soundness or a reflexivity proof. -/
def dynamic_reflexive (b a : Nat) (hab : a < b+2) :
    KDerivation (imp (domainAt b a).encode (equivAt b a a).encode) := by
  let d := max b a + 100
  let e := d + 100
  have hd : 100 ≤ d := by dsimp [d]; omega
  have hde : d + 100 ≤ e := by dsimp [e]; omega
  have hsafe : d + 39 < e + 2 := by omega
  have hshape : renameSteps (sourceSteps d e) sourceBody = frame d e 30 := by
    simpa [frame] using source_steps_shape d e hd hde
  have hfixed := relocated_reflexive d e (by omega) hsafe hshape
  have ha := instantiate_frame d e a (by omega) (by omega) (by dsimp [d]; omega)
    (by dsimp [e, d]; omega) hfixed
  exact reflexivity_rebase d e b a (by dsimp [d]; omega) (by omega)
    (by dsimp [e, d]; omega) hab (by simpa [frame, Formula.encode] using ha)

theorem dynamic_reflexive_certificate (b a : Nat) (hab : a < b+2) :
    theoremCode (certificate (dynamic_reflexive b a hab)) =
      imp (domainAt b a).encode (equivAt b a a).encode := certificate_correct _

/-- A variable graph has a value using the source value as witness. The
operand and witness are syntactic names; their assigned objects may coincide. -/
def variable_graph_total (b a o : Nat) (ha : a < b) (ho : o < b) (hoa : o ≠ a) :
    KDerivation (imp (domainAt b a).encode
      (existsCode o (termGraph (fun x : Nat => x) (.var a : Peano.language.Term Nat) o b).encode)) :=
  PAtoCompactVariableTermTotality.variable_graph_total b a o ha ho hoa
    (dynamic_reflexive b a (by omega))

theorem variable_graph_total_certificate (b a o : Nat)
    (ha : a < b) (ho : o < b) (hoa : o ≠ a) :
    theoremCode (certificate (variable_graph_total b a o ha ho hoa)) =
      imp (domainAt b a).encode
        (existsCode o (termGraph (fun x : Nat => x) (.var a : Peano.language.Term Nat) o b).encode) :=
  certificate_correct _

#print axioms dynamic_reflexive
#print axioms dynamic_reflexive_certificate
#print axioms variable_graph_total
#print axioms variable_graph_total_certificate

end PASoundness.PAtoCompactCandidateDynamicReflexivity
