import PASoundness.PAtoCompactSuffixRebaseRenamedFrame
import PASoundness.PAtoCompactSuffixEndpointMoves
import PASoundness.PAtoCompactSuffixRebaseFilterAlpha
import PASoundness.PAtoCompactEquivStepsSyntax

/-! Syntax alignment for the capture-safe relocated suffix frame. This proves
only named-formula equality; finite K derivations, witness existence and
addition output transport are separate. -/
namespace PASoundness.PAtoCompactSuffixRebaseTargetFrame
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactAlphaMapOne PASoundness.PAtoCompactMultiAlpha
open PASoundness.PAtoCompactEquivStepsSyntax PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactSuffixRebaseMatrixAlpha
open PASoundness.PAtoCompactSuffixRebaseAlphaFrame PASoundness.PAtoCompactSuffixRebaseRenamedFrame
open PASoundness.PAtoCompactSuffixEquivalentAlphaEndpoints PASoundness.PAtoCompactSuffixEndpointMoves
open PASoundness.PAtoCompactSuffixRebaseFilterAlpha
set_option maxRecDepth 262144
set_option maxHeartbeats 0

private def matrixMoves : List (Nat × Nat) := [(0,32),(1,8),(6,60)]
private def activeNames : Finset Nat :=
  {0,1,2,5,6,8,32,33,34,38,40,41,60,70,71,72,73,74,75,76}

/-- If source names avoid binders, repeated replacement agrees with the
corresponding raw name-map sequence. -/
private theorem fold_replace_eq_renameSteps (steps : List (Nat × Nat)) (f : Formula)
    (safe : ∀ p ∈ steps, p.1 ∉ f.binders) :
    steps.foldl (fun g p => replace p.1 p.2 g) f = renameSteps steps f := by
  induction steps generalizing f with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨x,y⟩ := p
      have hp : x ∉ f.binders := safe (x,y) (by simp)
      have hs : ∀ q ∈ ps, q.1 ∉ (replace x y f).binders := by
        intro q hq
        simpa only [replace_binders] using safe q (by simp [hq])
      simp only [List.foldl, renameSteps]
      rw [map_eq_replace x y f hp]
      exact ih (replace x y f) hs

private theorem order_avoids : Disjoint activeNames orderAlpha.binders := by decide
private theorem bijection_avoids : Disjoint activeNames bijectionAlpha.binders := by decide

private theorem active_of_moves (p : Nat × Nat) (hp : p ∈ moves) : p.1 ∈ activeNames := by
  simp only [moves, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

private theorem active_of_matrix_moves (p : Nat × Nat) (hp : p ∈ matrixMoves) : p.1 ∈ activeNames := by
  simp only [matrixMoves, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl <;> decide

private theorem order_support : orderAlpha.names ⊆
    ({0,1,3,4,6,19,20,21,22,102,105} : Finset Nat) := by decide
private theorem bijection_support : bijectionAlpha.names ⊆
    ({0,1,3,4,6,19,20,21,22,102} : Finset Nat) := by decide

/-- The full staged name sequence agrees with the three relevant outer/graph
name substitutions on the bound-prepared order matrix. -/
theorem order_moves : moves.foldl (fun f p => replace p.1 p.2 f) orderAlpha = relabel orderAlpha := by
  have hm : ∀ p ∈ moves, p.1 ∉ orderAlpha.binders := by
    intro p hp h; exact (Finset.disjoint_left.mp order_avoids) (active_of_moves p hp) h
  have hs : ∀ p ∈ matrixMoves, p.1 ∉ orderAlpha.binders := by
    intro p hp h; exact (Finset.disjoint_left.mp order_avoids) (active_of_matrix_moves p hp) h
  have h1 := fold_replace_eq_renameSteps moves orderAlpha hm
  have h2 := fold_replace_eq_renameSteps matrixMoves orderAlpha hs
  have hmap : mapNames (applySteps moves) orderAlpha = mapNames (applySteps matrixMoves) orderAlpha := by
    apply mapNames_congr
    intro x hx
    have h := order_support hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hend : matrixMoves.foldl (fun f p => replace p.1 p.2 f) orderAlpha = relabel orderAlpha := by rfl
  rw [h1, renameSteps_eq_map, hmap, ← renameSteps_eq_map, ← h2, hend]

/-- The corresponding syntactic identity for the prepared bijection matrix. -/
theorem bijection_moves : moves.foldl (fun f p => replace p.1 p.2 f) bijectionAlpha = relabel bijectionAlpha := by
  have hm : ∀ p ∈ moves, p.1 ∉ bijectionAlpha.binders := by
    intro p hp h; exact (Finset.disjoint_left.mp bijection_avoids) (active_of_moves p hp) h
  have hs : ∀ p ∈ matrixMoves, p.1 ∉ bijectionAlpha.binders := by
    intro p hp h; exact (Finset.disjoint_left.mp bijection_avoids) (active_of_matrix_moves p hp) h
  have h1 := fold_replace_eq_renameSteps moves bijectionAlpha hm
  have h2 := fold_replace_eq_renameSteps matrixMoves bijectionAlpha hs
  have hmap : mapNames (applySteps moves) bijectionAlpha = mapNames (applySteps matrixMoves) bijectionAlpha := by
    apply mapNames_congr
    intro x hx
    have h := bijection_support hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have hend : matrixMoves.foldl (fun f p => replace p.1 p.2 f) bijectionAlpha = relabel bijectionAlpha := by rfl
  rw [h1, renameSteps_eq_map, hmap, ← renameSteps_eq_map, ← h2, hend]

private theorem fold_imp (steps : List (Nat × Nat)) (a b : Formula) :
    steps.foldl (fun f p => replace p.1 p.2 f) (.imp a b) =
      .imp (steps.foldl (fun f p => replace p.1 p.2 f) a)
        (steps.foldl (fun f p => replace p.1 p.2 f) b) := by
  induction steps generalizing a b with
  | nil => rfl
  | cons p ps ih =>
      simpa only [List.foldl, replace] using ih (replace p.1 p.2 a) (replace p.1 p.2 b)

private theorem source_filter_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) sourceFilterNamed = sourceFilter42 := by decide
private theorem target_filter_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) targetFilterNamed = targetFilter43 := by decide
private theorem source_member_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) (.member 0 2) = .member 32 33 := by decide
private theorem target_member_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) (.member 1 5) = .member 8 41 := by decide
private theorem cut_edge_moves :
    moves.foldl (fun f p => replace p.1 p.2 f) (graphFormula 6 2 5) = graphFormula 60 33 41 := by decide

/-- Named target frame with the prepared order and bijection matrices, the
actual two filters, matched cut edge and the same suffix endpoint formula. -/
def targetFrame : Formula := .imp (relabel orderAlpha) (.imp sourceFilter42 (.imp targetFilter43
  (.imp (.member 32 33) (.imp (.member 8 41) (.imp (graphFormula 60 33 41)
    (.imp (relabel bijectionAlpha) alphaEndpoint))))))

/-- All 14 capture-safe moves produce exactly `targetFrame`. In particular,
the old suffix name 41 was staged away before target cut 41 was installed. -/
theorem renamed_frame_shape : renamedFrame = targetFrame := by
  simp only [renamedFrame, alphaFrame, frame, fold_imp, order_moves, source_filter_moves,
    target_filter_moves, source_member_moves, target_member_moves, cut_edge_moves,
    bijection_moves, suffix_endpoint_moves, targetFrame]

end PASoundness.PAtoCompactSuffixRebaseTargetFrame

#print axioms PASoundness.PAtoCompactSuffixRebaseTargetFrame.order_moves
#print axioms PASoundness.PAtoCompactSuffixRebaseTargetFrame.bijection_moves
#print axioms PASoundness.PAtoCompactSuffixRebaseTargetFrame.targetFrame
#print axioms PASoundness.PAtoCompactSuffixRebaseTargetFrame.renamed_frame_shape
