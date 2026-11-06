import Shared.Beeping.PostInputLoader
import Shared.Beeping.BinaryLoaderRefinement

/-! Positive-segment refinement from a finite post-Turing input to the actual
blank-start binary table, including the loader's finite silent startup. -/
namespace Shared.Beeping.PostInputRefinement
open Turing
open Shared.Beeping.ComparisonSingleTape Shared.Beeping.PostInputLoader
open Shared.Beeping.BinarySourceCompiler Shared.Beeping.PostTableBinding

variable {Λ : Type} [Inhabited Λ]

noncomputable def refinement {m : Nat} {tab : SourceTable m}
    {M : TM0.Machine Alphabet Λ} {flags}
    (binding : Binding M flags tab) (start : Fin m) (input : List Alphabet) :
    EventRefinement (externalSystem M flags ⟨binding.state start,Tape.mk₁ input⟩)
      (Shared.Beeping.BinaryLoader.machine (BinarySourceCompiler.machine tab start) (payload input)).system := by
  let p : PostSourceRefinement.PostConfig m := ⟨start,Tape.mk₁ input⟩
  have he : Shared.Beeping.BinaryLoader.loadedSystem (BinarySourceCompiler.machine tab start) (payload input) =
      BinarySourceLoaded.binaryFrom tab start (PostSourceRefinement.sourceInitial p) := by
    change EventSystem.mk (Shared.Beeping.BinaryLoader.loaded (BinarySourceCompiler.machine tab start) (payload input)) _ = _
    rw [compiler_loaded]
    rfl
  have hr : EventRefinement (externalSystem M flags ⟨binding.state start,Tape.mk₁ input⟩)
      (Shared.Beeping.BinaryLoader.loadedSystem (BinarySourceCompiler.machine tab start) (payload input)) := by
    rw [he]
    exact PostTableBinding.binaryRefinement binding start p
  exact hr.trans (Shared.Beeping.BinaryLoader.refinement _ _)
end Shared.Beeping.PostInputRefinement
