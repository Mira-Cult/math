import PASoundness.PAtoCompactSuffixRebaseRenamedFrame
import PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
import PASoundness.PAtoCompactEquivStepsSyntax

/-! Compare the full capture-safe frame relocation with the three moves that
actually affect the alpha-prepared suffix endpoint formula. This is a named
syntax identity, not a semantic or K soundness argument. -/
namespace PASoundness.PAtoCompactSuffixEndpointMoves
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactSuffixRebaseRenamedFrame
open PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints
set_option maxRecDepth 262144
set_option maxHeartbeats 0

private def endpoints : List (Nat × Nat) := [(41,70),(40,34),(70,38)]
private def activeNames : Finset Nat :=
  {0,1,2,5,6,8,32,33,34,38,40,41,60,70,71,72,73,74,75,76}

/-- Formula replacement and full named mapping coincide at each stage when
all source labels avoid the original binder set. -/
private theorem fold_replace_eq_renameSteps (steps : List (Nat × Nat)) (f : Formula)
    (safe : ∀ p ∈ steps, p.1 ∉ f.binders) :
    steps.foldl (fun g p => replace p.1 p.2 g) f = renameSteps steps f := by
  induction steps generalizing f with
  | nil => rfl
  | cons p ps ih =>
      have hp : p.1 ∉ f.binders := safe p (by simp)
      have hs : ∀ q ∈ ps, q.1 ∉ (replace p.1 p.2 f).binders := by
        intro q hq
        simpa only [replace_binders] using safe q (by simp [hq])
      simp only [List.foldl, renameSteps]
      rw [map_eq_replace p.1 p.2 f hp]
      exact ih (replace p.1 p.2 f) hs

private theorem active_avoids_binders : Disjoint activeNames alpha6.binders := by decide

private theorem active_safe (x : Nat) (hx : x ∈ activeNames) : x ∉ alpha6.binders := by
  intro hb
  exact (Finset.disjoint_left.mp active_avoids_binders) hx hb

private theorem moves_safe : ∀ p ∈ moves, p.1 ∉ alpha6.binders := by
  intro p hp
  apply active_safe
  simp only [moves, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem endpoints_safe : ∀ p ∈ endpoints, p.1 ∉ alpha6.binders := by
  intro p hp
  apply active_safe
  simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

private theorem alpha6_name_support : alpha6.names ⊆
    ({3,4,19,20,21,22,40,41,102,105,106} : Finset Nat) := by decide

/-- Relocating the entire prepared frame affects its suffix-equivalence
component exactly as relocating just its two free endpoint labels. -/
theorem suffix_endpoint_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) alpha6 = alphaEndpoint := by
  have h1 := fold_replace_eq_renameSteps moves alpha6 moves_safe
  have h2 := fold_replace_eq_renameSteps endpoints alpha6 endpoints_safe
  have hmap : mapNames (applySteps moves) alpha6 = mapNames (applySteps endpoints) alpha6 := by
    apply mapNames_congr
    intro x hx
    have h := alpha6_name_support hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hend : endpoints.foldl (fun f p => replace p.1 p.2 f) alpha6 = alphaEndpoint := by rfl
  rw [h1, renameSteps_eq_map, hmap, ← renameSteps_eq_map, ← h2, hend]

end PASoundness.PAtoCompactSuffixEndpointMoves

#print axioms PASoundness.PAtoCompactSuffixEndpointMoves.suffix_endpoint_moves
