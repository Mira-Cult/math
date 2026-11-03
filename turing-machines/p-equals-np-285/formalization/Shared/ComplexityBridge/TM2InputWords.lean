import Shared.ComplexityBridge.TM2BinaryPostCosts
import Shared.Codes.FiniteProgramWriteWord
/-! Exact code words required at the TM2-to-binary input boundary. -/
namespace Shared.ComplexityBridge.TM2InputWords
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts

def inputCell (tm : FinTM2) (mark : Bool) (a : tm.Γ tm.k₀) : Alphabet tm := by
  letI := tm.kFin
  exact (mark, Function.update (fun _ => none) tm.k₀ (some a))

def bottomEmpty (tm : FinTM2) : Alphabet tm := (true, (default : Alphabet tm).2)

variable (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)

theorem inputBits_empty : inputBits tm enc [] = (enc (bottomEmpty tm)).toList := by
  simp [inputBits,Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput,
    TM2to1.trInit,bottomEmpty,List.map,List.headI,List.flatMap]

set_option backward.isDefEq.respectTransparency false in
theorem inputBits_reverse_cons (bits : List (tm.Γ tm.k₀)) (b : tm.Γ tm.k₀) (bs : List (tm.Γ tm.k₀))
    (h : bits.reverse = b::bs) :
    inputBits tm enc bits = (enc (inputCell tm true b)).toList ++
      bs.flatMap (fun a => (enc (inputCell tm false a)).toList) := by
  let := tm.kFin
  simp [inputBits,Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput,
    TM2to1.trInit,h,inputCell,List.headI,List.flatMap]
  rfl

/-- For any fixed codec and input symbol, the generated literal rows write
its code word in exactly `width` transitions. Codec selection is separate
from effective runtime reification of an arbitrary Lean function. -/
theorem emit_input_cell (pre suffix : Shared.Codes.FinitePrograms.Program)
    (mark : Bool) (a : tm.Γ tm.k₀) (t : Shared.Codes.FinitePrograms.Tape) :
    let word := (enc (inputCell tm mark a)).toList
    Shared.Codes.FinitePrograms.run
      (pre ++ Shared.Codes.FiniteProgramWriteWord.rows pre.length word ++ suffix)
      (pre.length,t) width =
      some (.inr (pre.length+width,Shared.Codes.FiniteProgramWriteWord.writeTape word t)) := by
  simpa [List.Vector.toList_length] using
    Shared.Codes.FiniteProgramWriteWord.write_run pre suffix (enc (inputCell tm mark a)).toList t

end Shared.ComplexityBridge.TM2InputWords
