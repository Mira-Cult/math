import Shared.Codes.FiniteProgramFirstBlocksController
import Shared.ComplexityBridge.TM2SelectInputWord

/-! The precise contents accumulated by the first-component scan. The
metadata interpreter is executable list code, not a proved finite-tape
implementation or a charged runtime in the beeping machine. -/
namespace Shared.ComplexityBridge.FirstBlocksContent
open Turing
open Shared.Codes.FiniteProgramFirstBlocksController (pred groupOutput loopOutput)
open Shared.Codes.FiniteProgramTaggedLoop (result output)
open Shared.ComplexityBridge.PairReverseFirst (expanded expanded_append expanded_cons)

def selected (zero one : List Bool) (b : Bool) : List Bool := if b then one else zero

def frames (zero one : List Bool) (bits : List Bool) : List Bool :=
  bits.flatMap (fun b => b::selected zero one b)

theorem frames_cons (zero one : List Bool) (b : Bool) (bits : List Bool) :
    frames zero one (b::bits) = (b::selected zero one b) ++ frames zero one bits := rfl

theorem frames_append (zero one bits₁ bits₂ : List Bool) :
    frames zero one (bits₁++bits₂) = frames zero one bits₁ ++ frames zero one bits₂ := by
  simp [frames,List.flatMap_append]

/-- Bits processed by a run ending at the last supplied predecessor. -/
def processed : Bool → List Bool → List Bool
  | _, [] => []
  | b, p::ps => b::processed p ps

theorem result_buffer (zero one remaining : List Bool) (b : Bool) (xs : List Bool) :
    (result zero one remaining b xs).2 = xs ++ frames zero one (processed b remaining) := by
  induction remaining generalizing b xs with
  | nil => simp [result,processed,frames]
  | cons p ps ih =>
    simp only [result,processed,frames_cons]
    rw [ih]
    simp [output,selected,List.append_assoc]

/-- Each first-component block contributes its six original bits in reverse
physical order, and every bit's metadata is followed by its chosen word. -/
theorem group_buffer (zero one : List Bool) (b : Bool) (xs : List Bool) :
    groupOutput zero one b xs = xs ++ frames zero one [false,true,b,true,true,true] := by
  simpa [groupOutput,pred,processed] using result_buffer zero one (pred b) false xs

def rawBlocks (todo : List Bool) : List Bool :=
  todo.flatMap (fun b => [false,true,b,true,true,true])

theorem loop_buffer (zero one todo xs : List Bool) :
    loopOutput zero one todo xs = xs ++ frames zero one (rawBlocks todo) := by
  induction todo generalizing xs with
  | nil => simp [loopOutput,rawBlocks,frames]
  | cons b todo ih =>
    simp only [loopOutput]
    rw [ih,group_buffer]
    change (xs ++ frames zero one [false,true,b,true,true,true]) ++ frames zero one (rawBlocks todo) =
      xs ++ frames zero one ([false,true,b,true,true,true] ++ rawBlocks todo)
    rw [frames_append]
    simp [List.append_assoc]

theorem rawBlocks_eq_reverse_expanded (todo : List Bool) :
    rawBlocks todo = (expanded todo.reverse).reverse := by
  induction todo with
  | nil => rfl
  | cons b todo ih =>
    simp only [rawBlocks,List.flatMap_cons,List.reverse_cons]
    change [false,true,b,true,true,true] ++ rawBlocks todo =
      (expanded (todo.reverse ++ [b])).reverse
    rw [expanded_append,expanded_cons]
    simp only [expanded,List.flatMap_nil,List.append_nil,List.reverse_append,
      List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    exact congrArg (fun x => false::true::b::true::true::true::x) ih

/-- The bounded interpreter consumes one metadata bit and exactly `width`
word bits per frame. A short or malformed input is interpreted by the same
total list operations; correctness below is only for complete frames. -/
def unframe (width : Nat) : Nat → List Bool → List Bool
  | 0, _ => []
  | _+1, [] => []
  | n+1, _::rest => rest.take width ++ unframe width n (rest.drop width)

theorem selected_length (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (b : Bool) :
    (selected zero one b).length = width := by cases b <;> simp [selected,hzero,hone]

/-- For complete frames with equal-width code words, metadata removal yields
exactly the concatenated selected code words. -/
theorem unframe_frames (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (bits : List Bool) :
    unframe width bits.length (frames zero one bits) =
      bits.flatMap (selected zero one) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    have hlen := selected_length zero one width hzero hone b
    simp [frames_cons,unframe,hlen,ih]

/-- The bounded interpreter recovers the code-word sequence for all source
bits actually scanned. This is a list-level theorem; running `unframe` on
finite tape and proving its cost remain separate obligations. -/
theorem unframe_loop_output (zero one : List Bool) (width : Nat)
    (hzero : zero.length = width) (hone : one.length = width) (todo : List Bool) :
    let raw := (expanded todo.reverse).reverse
    unframe width raw.length (loopOutput zero one todo []) = raw.flatMap (selected zero one) := by
  dsimp only
  rw [loop_buffer]
  simp only [List.nil_append,← rawBlocks_eq_reverse_expanded]
  exact unframe_frames zero one width hzero hone (rawBlocks todo)

/-- The selected unmarked words agree with the TM2 input-cell codec, in the
order actually scanned. This does not include the marked final input cell or
any cells outside the first-component blocks. -/
theorem unframe_tm2_words (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (todo : List Bool) :
    let raw := (expanded todo.reverse).reverse
    unframe width raw.length
        (loopOutput (TM2SelectInputWord.word tm enc inp false false)
          (TM2SelectInputWord.word tm enc inp false true) todo []) =
      raw.flatMap (fun b =>
        (enc (TM2InputWords.inputCell tm false (inp.symm b))).toList) := by
  have h := unframe_loop_output (TM2SelectInputWord.word tm enc inp false false)
    (TM2SelectInputWord.word tm enc inp false true) width
    (TM2SelectInputWord.word_length tm enc inp false false)
    (TM2SelectInputWord.word_length tm enc inp false true) todo
  have hs : selected (TM2SelectInputWord.word tm enc inp false false)
      (TM2SelectInputWord.word tm enc inp false true) =
      (fun b => (enc (TM2InputWords.inputCell tm false (inp.symm b))).toList) := by
    funext b
    cases b <;> rfl
  simpa only [hs] using h

/-- If the scan's bits form a contiguous portion of a nonempty reversed TM2
input, the recovered words occur at that exact position in its translated
initial tape. The caller must still establish the input layout hypothesis. -/
theorem tm2_input_segment (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (todo : List Bool)
    (bits : List (tm.Γ tm.k₀)) (head : tm.Γ tm.k₀)
    (before after : List (tm.Γ tm.k₀))
    (h : bits.reverse = head :: (before ++
      ((expanded todo.reverse).reverse.map inp.symm) ++ after)) :
    Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc bits =
      (enc (TM2InputWords.inputCell tm true head)).toList ++
      before.flatMap (fun a => (enc (TM2InputWords.inputCell tm false a)).toList) ++
      unframe width (expanded todo.reverse).reverse.length
        (loopOutput (TM2SelectInputWord.word tm enc inp false false)
          (TM2SelectInputWord.word tm enc inp false true) todo []) ++
      after.flatMap (fun a => (enc (TM2InputWords.inputCell tm false a)).toList) := by
  rw [TM2InputWords.inputBits_reverse_cons tm enc bits head _ h]
  rw [List.flatMap_append, List.flatMap_append, unframe_tm2_words]
  simp only [List.flatMap_map, List.append_assoc]

example : unframe 2 2 [true,true,false,false,false,true] = [true,false,false,true] := by decide
example : unframe 2 2 [true,false] = [false] := by decide
example : unframe 0 3 [true,false,true] = [] := by decide

end Shared.ComplexityBridge.FirstBlocksContent
