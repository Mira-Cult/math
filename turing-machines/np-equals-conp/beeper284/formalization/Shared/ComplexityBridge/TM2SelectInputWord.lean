import Shared.ComplexityBridge.TM2InputWords
import Shared.Codes.FiniteProgramSelectWord

/-! Runtime selection of the translated TM2 code word from a binary input
symbol. The source bit and target region have separate physical cells. -/
namespace Shared.ComplexityBridge.TM2SelectInputWord
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.ComplexityBridge.TM2InputWords
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramSelectWord

variable (tm : FinTM2) {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
variable (inp : tm.Γ tm.k₀ ≃ Bool)

def word (mark bit : Bool) : List Bool := (enc (inputCell tm mark (inp.symm bit))).toList

theorem word_length (mark bit : Bool) : (word tm enc inp mark bit).length = width := by
  simp [word,List.Vector.toList_length]

/-- A single physical input bit selects its associated fixed-width translated
symbol. The dispatch and output use `1+width` actual table transitions. -/
theorem select_cell (pre suffix : Program) (mark : Bool) (t : Tape) :
    let zero := word tm enc inp mark false
    let one := word tm enc inp mark true
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,t) (1+width) =
      some (.inr (pre.length+1+2*width,
        Shared.Codes.FiniteProgramWriteWord.writeTape (word tm enc inp mark t.2.1)
          (moveTape false t.2.1 t))) := by
  have h := select_run pre suffix (word tm enc inp mark false) (word tm enc inp mark true) t
  cases ht : t.2.1 <;>
    simpa [ht,word_length,finish,two_mul,Nat.add_assoc] using h

/-- The generated selector has one dispatch row and two fixed-width paths. -/
theorem select_cell_rows (q : Nat) (mark : Bool) :
    (selectRows q (word tm enc inp mark false) (word tm enc inp mark true)).length = 1+2*width := by
  rw [selectRows_length,word_length,word_length]
  omega

/-- On blank workspace the selected word is written next to the retained
source bit, ready for a caller to reposition the head. -/
theorem select_cell_blank (pre suffix : Program) (mark bit : Bool) (left : List Bool) :
    let zero := word tm enc inp mark false
    let one := word tm enc inp mark true
    run (pre ++ selectRows pre.length zero one ++ suffix) (pre.length,(left,bit,[false])) (1+width) =
      some (.inr (pre.length+1+2*width,((word tm enc inp mark bit).reverse ++ bit::left,false,[]))) := by
  have h := select_run_blank pre suffix (word tm enc inp mark false) (word tm enc inp mark true) left bit
  cases bit <;> simpa [word_length,finish,two_mul,Nat.add_assoc] using h

end Shared.ComplexityBridge.TM2SelectInputWord
