import Shared.Beeping.NPcoNP.Source284HardwireCorrect

/-! The existing finite hardwired-word table also works on arbitrary target
cells. It overwrites exactly the word and one following zero, preserving the
higher suffix. This is a paid table run, not global suffix erasure. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284HardwireOverwrite

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable
open Shared.Beeping.NPcoNP.Source284HardwireCorrect (run_add)
open Shared.Beeping.NPcoNP.Source284HardwireRewind (rewind)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack transfer pushed_eq_stack transfer_stack)

/-- A fixed writing row ignores the overwritten target bit. -/
theorem writing_step_any (bits : List Bool) (original : Nat → Bool → Row)
    (q left right : Nat) (hq : q < bits.length) :
    step (table bits original) ⟨left,right,some q⟩ =
      ⟨2*left+bit ((bits[q]?).getD false),right/2,some (q+1)⟩ := by
  simp [step,writing_row _ _ _ hq]

/-- Each of the remaining fixed bits is physically written, regardless of
old tape contents. -/
theorem write_suffix_any (original : Nat → Bool → Row) (pre rest : List Bool)
    (left right : Nat) :
    run (table (pre++rest) original) ⟨left,right,some pre.length⟩ rest.length =
      ⟨payloadFold left rest,right / 2^rest.length,some (pre++rest).length⟩ := by
  induction rest generalizing pre left right with
  | nil => simp [run,payloadFold]
  | cons b bs ih =>
    have hi : pre.length < (pre++b::bs).length := by simp
    have hv : (((pre++b::bs)[pre.length]?).getD false) = b := by
      rw [List.getElem?_append_right (by omega)]; simp
    have hfirst := writing_step_any (pre++b::bs) original pre.length left right hi
    rw [hv] at hfirst
    have hnext := ih (pre++[b]) (2*left+bit b) (right/2)
    simp only [List.length_append,List.length_singleton] at hnext
    rw [List.length_cons,run_front,hfirst]
    simpa [List.append_assoc,payloadFold,bit,Nat.div_div_eq_div_mul,pow_succ,
      Nat.mul_comm,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hnext

/-- Rewinding a word previously pushed above a preserved half puts that word
on the new side above any higher suffix. -/
theorem transfer_pushed (bits : List Bool) (left preserved : Nat) :
    transfer bits.length left (payloadFold preserved bits) = (stack bits left,preserved) := by
  rw [pushed_eq_stack]
  have h := transfer_stack bits.reverse left preserved
  simpa [pushed_eq_stack] using h

/-- Write and rewind over an arbitrary target half. The word and a zero
sentinel replace exactly `bits.length+1` old cells; the original opposite
half is restored. -/
theorem overwrite (bits : List Bool) (original : Nat → Bool → Row) (left right : Nat) :
    run (table bits original) ⟨left,right,some 0⟩ (offset bits) =
      ⟨left,stack bits (2*(right / 2^(bits.length+1))),some (offset bits)⟩ := by
  let t := table bits original
  let m := bits.length
  have hw : run t ⟨left,right,some 0⟩ m =
      ⟨payloadFold left bits,right/2^m,some m⟩ := by
    simpa [t,m] using write_suffix_any original [] bits left right
  have hfirst : run t ⟨left,right,some 0⟩ (m+1) =
      ⟨2*((right/2^m)/2),payloadFold left bits,some (m+1)⟩ := by
    rw [run,hw]
    simp [t,m,step,outward_turn_row,bit]
  have hr := rewind bits original (2*((right/2^m)/2)) (payloadFold left bits)
  rw [transfer_pushed] at hr
  have hback : run t ⟨left,right,some 0⟩ (m+1+m) =
      ⟨stack bits (2*((right/2^m)/2)),left,some (2*m+1)⟩ := by
    rw [run_add,hfirst]
    exact hr
  have hoff : offset bits = m+1+m+1 := by simp [offset,m]; omega
  rw [hoff,run,hback]
  simpa [offset,m,Nat.div_div_eq_div_mul,pow_succ,Nat.mul_comm,
    Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,two_mul] using
    return_turn_step bits original (stack bits (2*((right/2^m)/2))) left

/-- All later continuation transitions are preserved after the paid overwrite. -/
theorem overwrite_then (bits : List Bool) (original : Nat → Bool → Row)
    (left right fuel : Nat) :
    run (table bits original) ⟨left,right,some 0⟩ (offset bits+fuel) =
      shiftConfig (offset bits) (run original
        ⟨left,stack bits (2*(right / 2^(bits.length+1))),some 0⟩ fuel) := by
  rw [run_add,overwrite]
  change run (table bits original) (shiftConfig (offset bits)
    ⟨left,stack bits (2*(right / 2^(bits.length+1))),some 0⟩) fuel = _
  rw [relocated_run]

namespace Fixtures
example : run (table [true,false,true] (fun _ b => ⟨b,false,some 0⟩))
    ⟨19,255,some 0⟩ 8 = ⟨19,245,some 8⟩ := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284HardwireOverwrite
