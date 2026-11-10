import PASoundness.PAtoCompactSuffixRebaseAlphaFrame
import PASoundness.PAtoCompactScopedActiveReplace

/-! Capture-safe relocation of the alpha-prepared suffix-isomorphism frame.
All original free labels first move to disjoint temporary labels before the
final target names are installed. This is finite K proof data; the resulting
frame's alignment with separately named target formulas is a later obligation. -/
namespace PASoundness.PAtoCompactSuffixRebaseRenamedFrame
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactScopedActiveReplace PASoundness.PAtoCompactSuffixRebaseAlphaFrame
set_option maxRecDepth 262144
set_option maxHeartbeats 0

/-- One capture-safe active-name replacement per pair, applied left to right. -/
def moves : List (Nat × Nat) :=
  [(0,70),(1,71),(2,72),(5,73),(40,74),(41,75),(6,76),
   (70,32),(71,8),(72,33),(73,41),(74,34),(75,38),(76,60)]

/-- Exact relocated named formula, preserving the original relation and
guard order. The variables are syntactic names; assigned objects may alias. -/
def renamedFrame : Formula := moves.foldl (fun f p => replace p.1 p.2 f) alphaFrame

private def movedNames : Finset Nat := {0,1,2,5,6,8,32,33,34,38,40,41,60,70,71,72,73,74,75,76}

/-- Alpha preparation moves every conflicting bound occurrence away from the
active source, temporary and target names. -/
private theorem frame_avoids_moved : Disjoint movedNames alphaFrame.binders := by decide

private theorem moved_avoids (x : Nat) (hx : x ∈ movedNames) : x ∉ alphaFrame.binders := by
  intro hb
  exact (Finset.disjoint_left.mp frame_avoids_moved) hx hb

private theorem moves_safe : ∀ p ∈ moves,
    p.1 ∉ alphaFrame.binders ∧ p.2 ∉ alphaFrame.binders := by
  intro p hp
  have hp' : p.1 ∈ movedNames ∧ p.2 ∈ movedNames := by
    simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      constructor <;> decide
  exact ⟨moved_avoids _ hp'.1, moved_avoids _ hp'.2⟩

/-- Each explicit rename is justified by the finite K universal-instantiation
transformer, using invariance of binder labels under `replace`. -/
noncomputable def reassign (steps : List (Nat × Nat)) (f : Formula)
    (safe : ∀ p ∈ steps, p.1 ∉ f.binders ∧ p.2 ∉ f.binders)
    (d : KDerivation f.encode) :
    KDerivation (steps.foldl (fun g p => replace p.1 p.2 g) f).encode := by
  induction steps generalizing f with
  | nil => simpa using d
  | cons p ps ih =>
      have hp := safe p (by simp)
      have hs : ∀ q ∈ ps, q.1 ∉ (replace p.1 p.2 f).binders ∧
          q.2 ∉ (replace p.1 p.2 f).binders := by
        intro q hq
        simpa only [replace_binders] using safe q (by simp [hq])
      have hd := replace_derivation p.1 p.2 f hp.1 hp.2 d
      simpa only [List.foldl] using ih (replace p.1 p.2 f) hs hd

/-- K proof of the fully relocated alpha frame; no target-syntax alignment or
elimination of the original graph hypothesis is claimed. -/
noncomputable def renamed_frame_proof : KDerivation renamedFrame.encode := by
  simpa only [renamedFrame] using reassign moves alphaFrame moves_safe alpha_frame_proof

theorem renamed_frame_proof_certificate : theoremCode (certificate renamed_frame_proof) =
    renamedFrame.encode := certificate_correct _

end PASoundness.PAtoCompactSuffixRebaseRenamedFrame

#print axioms PASoundness.PAtoCompactSuffixRebaseRenamedFrame.moves
#print axioms PASoundness.PAtoCompactSuffixRebaseRenamedFrame.renamedFrame
#print axioms PASoundness.PAtoCompactSuffixRebaseRenamedFrame.reassign
#print axioms PASoundness.PAtoCompactSuffixRebaseRenamedFrame.renamed_frame_proof
#print axioms PASoundness.PAtoCompactSuffixRebaseRenamedFrame.renamed_frame_proof_certificate
