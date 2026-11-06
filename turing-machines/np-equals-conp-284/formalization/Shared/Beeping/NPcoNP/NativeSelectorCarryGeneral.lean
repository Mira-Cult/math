import Shared.Beeping.NPcoNP.NativeManyTerminalWindow

/-! Carry word at a value-three selector after any number of zero blocks. -/
namespace Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
open Shared.Beeping.NPcoNP.NativeHalfScan
open Shared.Beeping.NPcoNP.NativeHalfSweep
open Shared.Beeping.NPcoNP.NativeHalfBankFirst
open Shared.Beeping.NPcoNP.NativeHalfSelectorMarkerWindow
open Shared.Beeping.NPcoNP.NativeManyTerminalWindow
open Shared.Beeping.NPcoNP.Bootstrap284CanonicalTape
open Shared.Beeping.NPcoNP.UnaryBank
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

def zeroPairs : Nat → List Bool
  | 0 => []
  | k+1 => [false,true] ++ zeroPairs k

theorem zeroPairs_length (k : Nat) : (zeroPairs k).length=2*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeroPairs,ih]; omega

theorem zeroPairs_leading (k : Nat) :
    false :: encode (List.replicate k 0)=zeroPairs k ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ,encode,block,List.replicate_one,List.cons_append,zeroPairs]
    simpa [List.append_assoc] using congrArg (fun xs => false::true::xs) ih

/-- A supplied value-three selector contains a three-one carry preceded by a
zero, for every number of leading zero blocks. -/
theorem selector_carry_general (t : Int → Bool) (a : Int) (k y : Nat)
    (window : Holds t a (markerWindow (List.replicate k 0 ++ [3,y]))) :
    downHolds t (a+((2*k : Nat):Int)+3) (List.replicate 3 true ++ [false]) := by
  rw [terminal_many_window k 0 y] at window
  have hw : Holds t a (zeroPairs k ++ ([false] ++ block 3 ++ List.replicate (y+1) true)) := by
    have he : zeroPairs k ++ ([false] ++ block 3 ++ List.replicate (y+1) true) =
        false :: (encode (List.replicate k 0) ++ block 3 ++ List.replicate (y+1) true) := by
      calc
        _ = (zeroPairs k ++ [false]) ++ (block 3 ++ List.replicate (y+1) true) := by simp [List.append_assoc]
        _ = (false :: encode (List.replicate k 0)) ++ (block 3 ++ List.replicate (y+1) true) := by rw [zeroPairs_leading]
        _ = _ := by simp [List.append_assoc]
    rw [he]
    simpa [List.append_assoc] using window
  have ht := holds_append_tail t a (zeroPairs k) ([false] ++ block 3 ++ List.replicate (y+1) true) hw
  rw [zeroPairs_length] at ht
  have hbits : Holds t (a+((2*k : Nat):Int)) ([false,true,true,true] ++ [true,false] ++ List.replicate (y+1) true) := by
    simpa [block,List.replicate_succ,List.append_assoc] using ht
  simp only [List.cons_append,List.nil_append,Holds] at hbits
  simp only [List.replicate_succ,List.replicate_zero,List.cons_append,List.nil_append,downHolds]
  refine ⟨?_,?_,?_,?_,trivial⟩
  · have hp : a+((2*k : Nat):Int)+3=a+((2*k : Nat):Int)+1+1+1 := by omega
    rw [hp]; exact hbits.2.2.2.1
  · have hp : a+((2*k : Nat):Int)+3-1=a+((2*k : Nat):Int)+1+1 := by omega
    rw [hp]; exact hbits.2.2.1
  · have hp : a+((2*k : Nat):Int)+3-1-1=a+((2*k : Nat):Int)+1 := by omega
    rw [hp]; exact hbits.2.1
  · have hp : a+((2*k : Nat):Int)+3-1-1-1=a+((2*k : Nat):Int) := by omega
    rw [hp]; exact hbits.1

#print axioms selector_carry_general
end Shared.Beeping.NPcoNP.NativeSelectorCarryGeneral
