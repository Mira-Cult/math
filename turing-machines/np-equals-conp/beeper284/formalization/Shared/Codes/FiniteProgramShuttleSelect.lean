import Shared.Codes.FiniteProgramBitShuttle
import Shared.Codes.FiniteProgramSelectWord

/-! Compose the tagged-buffer shuttle's forward pass with the dynamic word
selector. The copy lands at the far boundary and is then used as the live
selector bit; the continuation is not executed in the proved segment. -/
namespace Shared.Codes.FiniteProgramShuttleSelect
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramBitShuttle (tagged tagged_cons boundary front middle third writer)
open Shared.Codes.FiniteProgramSelectWord (selectRows select_run_blank finish)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt consumed consumed_cons)

/-- Reuse the shuttle's first nine rows. The remaining three rows write the
carried bit to the far boundary and move back onto it. -/
def pre : Program :=
  (Shared.Codes.FiniteProgramBitShuttle.program []).take 9 ++
    [ ((false,true,11,0),(false,true,11,0)),
      ((true,true,11,0),(true,true,11,0)),
      ((false,false,12,0),(true,false,12,0)) ]

theorem pre_length : pre.length = 12 := by decide

def program (zero one : List Bool) (tail : Program) : Program :=
  pre ++ selectRows pre.length zero one ++ tail

theorem start_step (zero one : List Bool) (tail : Program) (b : Bool) (L R : List Bool) :
    run (program zero one tail) (0,tapeAt L (b::R)) 1 =
      some (.inr (boundary b,tapeAt (b::L) R)) := by
  cases b <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,boundary]

theorem boundary_step (zero one : List Bool) (tail : Program) (b : Bool) (L R : List Bool) :
    run (program zero one tail) (boundary b,tapeAt L (false::R)) 1 =
      some (.inr (front b,tapeAt (false::L) R)) := by
  cases b <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,boundary,front]

theorem front_step (zero one : List Bool) (tail : Program) (b : Bool) (L R : List Bool) :
    run (program zero one tail) (front b,tapeAt L (true::R)) 1 =
      some (.inr (middle b,tapeAt (true::L) R)) := by
  cases b <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,front,middle]

theorem middle_step (zero one : List Bool) (tail : Program) (b x : Bool) (L R : List Bool) :
    run (program zero one tail) (middle b,tapeAt L (x::R)) 1 =
      some (.inr (third b,tapeAt (x::L) R)) := by
  cases b <;> cases x <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,middle,third]

theorem third_step (zero one : List Bool) (tail : Program) (b : Bool) (L R : List Bool) :
    run (program zero one tail) (third b,tapeAt L (true::R)) 1 =
      some (.inr (front b,tapeAt (true::L) R)) := by
  cases b <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,third,front]

theorem forward (zero one : List Bool) (tail : Program) (b : Bool) (xs L R : List Bool) :
    run (program zero one tail) (front b,tapeAt L (tagged xs ++ R)) (3*xs.length) =
      some (.inr (front b,tapeAt (consumed L (tagged xs)) R)) := by
  induction xs generalizing L with
  | nil => rfl
  | cons x xs ih =>
    simp only [tagged_cons,List.cons_append,List.length_cons]
    rw [show 3*(xs.length+1) = 1+(1+(1+3*xs.length)) by omega]
    rw [run_continue _ _ _ 1 _ (front_step zero one tail b L _)]
    rw [run_continue _ _ _ 1 _ (middle_step zero one tail b x (true::L) _)]
    rw [run_continue _ _ _ 1 _ (third_step zero one tail b (x::true::L) _)]
    simpa only [consumed_cons] using ih (true::x::true::L)

theorem end_step (zero one : List Bool) (tail : Program) (b : Bool) (L R : List Bool) :
    run (program zero one tail) (front b,tapeAt L (false::R)) 1 =
      some (.inr (writer b,tapeAt (false::L) R)) := by
  cases b <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,front,writer]

theorem copy_step (zero one : List Bool) (tail : Program) (b old : Bool) (L R : List Bool) :
    run (program zero one tail) (writer b,tapeAt L (old::R)) 1 =
      some (.inr (11,tapeAt (b::L) R)) := by
  cases b <;> cases old <;> simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,tapeAt,moveTape,writer]

theorem back_step (zero one : List Bool) (tail : Program) (b : Bool) (L : List Bool) :
    run (program zero one tail) (11,((b::L),false,[])) 1 =
      some (.inr (12,(L,b,[false]))) := by
  simp [run,advance,step,program,pre,Shared.Codes.FiniteProgramBitShuttle.program,moveTape]

/-- Copy a varying source bit across a tagged buffer and write its selected
word in adjacent blank workspace. All movements and writes are charged. -/
theorem shuttle_select (zero one : List Bool) (tail : Program) (b old : Bool) (xs L : List Bool) :
    let word := if b then one else zero
    run (program zero one tail)
      (0,tapeAt L (b::false::tagged xs ++ [false,old,false]))
      (3*xs.length+6+word.length) =
      some (.inr (finish 12 zero one,
        (word.reverse ++ b::false::(tagged xs).reverse ++ false::b::L,false,[]))) := by
  dsimp only
  simp only [List.cons_append]
  rw [show 3*xs.length+6+(if b then one else zero).length =
    1+(1+(3*xs.length+(1+(1+(1+(1+(if b then one else zero).length)))))) by omega]
  rw [run_continue _ _ _ 1 _ (start_step zero one tail b L _)]
  rw [run_continue _ _ _ 1 _ (boundary_step zero one tail b (b::L) _)]
  rw [run_continue _ _ _ _ _ (forward zero one tail b xs (false::b::L) [false,old,false])]
  rw [run_continue _ _ _ 1 _ (end_step zero one tail b (consumed (false::b::L) (tagged xs)) [old,false])]
  rw [run_continue _ _ _ 1 _ (copy_step zero one tail b old (false::consumed (false::b::L) (tagged xs)) [false])]
  change run (program zero one tail)
    (11,(b::false::consumed (false::b::L) (tagged xs),false,[])) _ = _
  rw [run_continue _ _ _ 1 _ (back_step zero one tail b (false::consumed (false::b::L) (tagged xs)))]
  have h := select_run_blank pre tail zero one (false::consumed (false::b::L) (tagged xs)) b
  simp only [pre_length] at h
  change run (pre ++ selectRows 12 zero one ++ tail) _ _ = _ at h
  rw [show program zero one tail = pre ++ selectRows 12 zero one ++ tail by simp [program,pre_length]]
  rw [h]
  simp [consumed,List.append_assoc]

theorem validRow_mono (r : Row) (a b : Nat) (hab : a ≤ b)
    (hv : validRow a r = true) : validRow b r = true := by
  simp [validRow] at hv ⊢
  omega

/-- The assembled shuttle and selector are valid when at least one valid
continuation row follows them. -/
theorem valid_of_continuation (zero one : List Bool) (tail : Program) (hne : 0 < tail.length)
    (htail : ∀ r ∈ tail, validRow (finish 12 zero one+tail.length) r.1 = true ∧
      validRow (finish 12 zero one+tail.length) r.2 = true) :
    valid (program zero one tail) = true := by
  have hall : pre.all (fun r => validRow 13 r.1 && validRow 13 r.2) = true := by decide
  have hbound : 13 ≤ finish 12 zero one+tail.length := by simp [finish]; omega
  have hp : ∀ r ∈ pre, validRow (finish 12 zero one+tail.length) r.1 = true ∧
      validRow (finish 12 zero one+tail.length) r.2 = true := by
    intro r hr
    have h := (List.all_eq_true.mp hall) r hr
    have h' : validRow 13 r.1 = true ∧ validRow 13 r.2 = true := by
      simpa only [Bool.and_eq_true] using h
    exact ⟨validRow_mono r.1 13 _ hbound h'.1,validRow_mono r.2 13 _ hbound h'.2⟩
  apply Shared.Codes.FiniteProgramSelectWord.valid_assembly pre tail zero one hne
  · simpa [pre_length] using hp
  · simpa [pre_length] using htail

namespace Fixtures
example : run (program [true,false] [false,true,true] [])
    (0,tapeAt [] [false,false,true,true,true,false,true,false]) 11 =
      some (.inr (18,([false,true,false,false,true,true,true,false,false],false,[]))) := by decide
example : run (program [true,false] [false,true,true] [])
    (0,tapeAt [] [true,false,true,false,true,false,false,false]) 12 =
      some (.inr (18,([true,true,false,true,false,true,false,true,false,true],false,[]))) := by decide
example : run (program [] [] []) (0,tapeAt [] [true,false,false,false,false]) 6 =
    some (.inr (13,([true,false,false,true],false,[]))) := by decide
example : valid (program [true,false] [false,true,true]
    [((false,true,0,1),(true,true,0,1))]) = true := by decide
end Fixtures

end Shared.Codes.FiniteProgramShuttleSelect
