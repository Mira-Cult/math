import Shared.Codes.FiniteProgramProtectedScanLoop
import Shared.Codes.FiniteProgramRelink
import Shared.ComplexityBridge.TM2OutputProtectedScan

/-! Position at the protected output's right edge, then scan left until the
retained marked block. This is a total finite task for every finite protected
output; it does not compact or emit the output. -/
namespace Shared.ComplexityBridge.TM2OutputProtectedLoop
open Turing
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus run_shift)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel)
open Shared.Codes.FiniteProgramWriteWord (leftRows rewind rewind_word left_run)
open Shared.Codes.FiniteProgramProtectedScanLoop (block blocks terminal)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseWitness (tapeLeft)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def program (width : Nat) : Program :=
  link (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedScanLoop.program width) []

@[simp] theorem program_length (width : Nat) : (program width).length = 5*(width+4)+2 := by
  simp [program,link]
  omega

theorem program_valid (width : Nat) : valid (program width) = true := by
  apply Shared.Codes.FiniteProgramRelink.valid_relink
    (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedScan.program width)
  · exact Shared.ComplexityBridge.TM2OutputProtectedScan.positioned_valid width
  · exact Shared.Codes.FiniteProgramProtectedScanLoop.program_valid width
  · simp

/-- Move across the fixed blank terminator and onto the next data bit. -/
theorem position (width : Nat) (b : Bool) (L : List Bool) :
    run (program width) (0,tapeAt (List.replicate (width+3) false ++ b::L) []) (width+4) =
      some (.inr (width+4,tapeLeft (b::L) (List.replicate (width+3) false ++ [false]))) := by
  let blanks := List.replicate (width+3) false
  let traversed := b::blanks
  have hre := rewind_word traversed L false []
  have hpos : rewind (width+4) (tapeAt (blanks ++ b::L) []) =
      tapeLeft (b::L) (blanks ++ [false]) := by
    simpa [traversed,blanks,tapeAt,tapeLeft,List.reverse_cons,List.reverse_append,List.append_assoc] using hre
  have h := left_run []
    ((Shared.Codes.FiniteProgramProtectedScanLoop.program width).map (shiftPair (width+4))) (width+4)
    (tapeAt (blanks ++ b::L) [])
  have hp : run (program width) (0,tapeAt (blanks ++ b::L) []) (width+4) =
      some (.inr (width+4,rewind (width+4) (tapeAt (blanks ++ b::L) []))) := by
    simpa [program,link,Shared.ComplexityBridge.TM2OutputProtectedScan.positioning,
      Shared.Codes.FiniteProgramWriteWord.leftRows_length] using h
  rw [hpos] at hp
  exact hp

/-- The positioning pass also respects blank-equivalent list tapes. -/
theorem position_related (width : Nat) (b : Bool) (L : List Bool) (t : Tape)
    (ht : TapeRel t (tapeAt (List.replicate (width+3) false ++ b::L) [])) :
    ∃ t', run (program width) (0,t) (width+4) = some (.inr (width+4,t')) ∧
      TapeRel t' (tapeLeft (b::L) (List.replicate (width+3) false ++ [false])) := by
  have h := Shared.Codes.FiniteProgramTapeEquiv.run_related (program width) (0,t)
    (0,tapeAt (List.replicate (width+3) false ++ b::L) []) rfl ht (width+4)
  rw [position width b L] at h
  cases hr : run (program width) (0,t) (width+4) with
  | none => rw [hr] at h; exact False.elim h
  | some v => cases v with
    | inl r => rw [hr] at h; exact False.elim h
    | inr c =>
      rcases c with ⟨q,t'⟩
      rw [hr] at h
      change q = width+4 ∧ _ at h
      refine ⟨t',?_,h.2⟩
      rw [h.1]

/-- All supplied unmarked cells are processed and the marked cell is reached,
with a strictly positive cost per block and an explicit total step count. -/
theorem run_to_marked (width : Nat) (xs : List (Bool × List Bool))
    (hxs : ∀ x ∈ xs, x.2.length = width)
    (first : Bool) (payload L : List Bool) (hfirst : payload.length = width)
    (t : Tape) (ht : TapeRel t (tapeAt (List.replicate (width+3) false ++
      blocks xs ++ block first payload true ++ L) [])) :
    ∃ t', run (program width) (0,t) ((width+4)+(xs.length*(width+5)+(width+3))) =
        some (.inr ((width+4)+terminal width first true,t')) ∧
      TapeRel t' (tapeLeft L ((block first payload true).reverse ++ (blocks xs).reverse ++
        List.replicate (width+3) false ++ [false])) := by
  let sparse := blocks xs ++ block first payload true ++ L
  obtain ⟨b,rest,hsparse⟩ : ∃ b rest, sparse = b::rest := by
    cases xs with
    | nil => exact ⟨first,payload ++ [true,true] ++ L,by simp [sparse,blocks,block]⟩
    | cons x xs =>
      rcases x with ⟨b,word⟩
      exact ⟨b,word ++ [false,true] ++ blocks xs ++ block first payload true ++ L,
        by simp [sparse,blocks,block,List.append_assoc]⟩
  have ht' : TapeRel t (tapeAt (List.replicate (width+3) false ++ b::rest) []) := by
    simpa [sparse,hsparse] using ht
  obtain ⟨u,hu,hurel⟩ := position_related width b rest t ht'
  have hloopinput : TapeRel u (tapeLeft (blocks xs ++ block first payload true ++ L)
      (List.replicate (width+3) false ++ [false])) := by
    simpa [sparse,hsparse] using hurel
  obtain ⟨v,hv,hvrel⟩ := Shared.Codes.FiniteProgramProtectedScanLoop.run_to_marked
    width xs hxs first payload L (List.replicate (width+3) false ++ [false]) hfirst u hloopinput
  have hshift := run_shift (Shared.ComplexityBridge.TM2OutputProtectedScan.positioning width)
    (Shared.Codes.FiniteProgramProtectedScanLoop.program width) []
    (Shared.Codes.FiniteProgramProtectedScanLoop.program_valid width) (0,u)
    (by simp [Shared.Codes.FiniteProgramProtectedScanLoop.program_length])
    (xs.length*(width+5)+(width+3))
  rw [hv] at hshift
  refine ⟨v,?_,?_⟩
  · rw [run_continue _ _ _ _ _ hu]
    simpa [program,shiftConfig,shiftStatus] using hshift
  · simpa [List.append_assoc] using hvrel

end Shared.ComplexityBridge.TM2OutputProtectedLoop
