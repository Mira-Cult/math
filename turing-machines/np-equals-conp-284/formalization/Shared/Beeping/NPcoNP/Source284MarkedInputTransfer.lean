import Shared.Beeping.NPcoNP.Source284CheckpointMarkedReveal
import Shared.Beeping.NPcoNP.Source284InputCounterGeometry

/-! Execute the independently generated workspace transfer immediately after
the marked guard reveals its witness and input. The resulting witness gap is
in the existing paired format and the original cutoff is unchanged. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedInputTransfer

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace (markCount blankTail)
open Shared.Beeping.NPcoNP.Source284InputCounterGeometry (extraPairs)

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284CheckpointMarkedReveal.description k r (178+states) (Source284InputCounterTransfer.table continuation)

def totalCost (k r : Nat) (input witness : List Bool) : Nat :=
  Source284CheckpointMarkedReveal.totalCost k r input witness+
    Source284InputCounterTransfer.cost input (markCount k r input.length-1)

/-- The actual marked initializer and guard are followed by the finite
counter transfer. Every successful witness reaches the supplied continuation
with its frame unchanged and the new longer gap in paired format. -/
theorem decoded_transferred (k r states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := Source284DynamicGuardSource.bound k input.length
      let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
      let gap := limit+1+extraPairs k r input.length
      let higher := blankTail k r input.length suffix/2
      Source284Relative.run (description k r states continuation)
        (Source284Relative.initial (encodeFrame input suffix) certificate)
        (totalCost k r input witness+fuel) =
      lift (1371+317*k+317*r+318+1+178) (Source284Relative.run (encode states continuation 1)
        ⟨2*(4*(4^gap*(2*wf))+1),encodeFrame input (4*(2*higher+1)),active 0⟩ fuel) := by
  have hc := Source284InputCounterTransfer.closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hreveal⟩ := Source284CheckpointMarkedReveal.decoded_reveal
    k r (178+states) (Source284InputCounterTransfer.table continuation) input witness certificate suffix (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  let limit := Source284DynamicGuardSource.bound k input.length
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let payload := 2*(4^(limit+1)*(2*wf))
  let saved := 4*(4^(limit+1)*(2*wf))+1
  let count := markCount k r input.length-1
  let higher := blankTail k r input.length suffix/2
  let t := Source284InputCounterTransfer.cost input count
  have ht : totalCost k r input witness+fuel = Source284CheckpointMarkedReveal.totalCost k r input witness+(t+fuel) := by
    simp [totalCost,t,count]; omega
  rw [ht]
  have hr := hreveal (t+fuel)
  have hcounter := Source284CheckpointMarkedBounds.higher_counter k r input.length suffix
  change Source284Relative.run (description k r states continuation) _ _ =
    lift (1371+317*k+317*r+318+1) (Source284Relative.run
      (encode (178+states) (Source284InputCounterTransfer.table continuation) 1)
      ⟨2*saved+1,flipped (input++[false]) (Source284CheckpointMarkedWorkspace.higher k r input.length suffix),active 0⟩
      (t+fuel)) at hr
  rw [hcounter] at hr
  have hs : saved = 2*payload+1 := by dsimp [saved,payload]; ring
  rw [hs] at hr
  let c : Config := ⟨2*(2*payload+1)+1,flipped (input++[false]) (Source284CountedShift.counter count higher),some 0⟩
  have hvalid : Valid (178+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have heval := run_toSource (178+states) (Source284InputCounterTransfer.table continuation) 1 c hc hvalid (t+fuel)
  change Source284Relative.run (encode (178+states) (Source284InputCounterTransfer.table continuation) 1)
    ⟨2*(2*payload+1)+1,flipped (input++[false]) (Source284CountedShift.counter count higher),active 0⟩ _ = _ at heval
  have htransfer := Source284InputCounterTransfer.transfer_then states continuation input payload count higher fuel hn hv
  change run (Source284InputCounterTransfer.table continuation) c (t+fuel) = _ at htransfer
  rw [heval,htransfer,← lift_toSource,Source284SourceRelocation.lift_add] at hr
  have hgeometry := Source284InputCounterGeometry.enlarged_saved_frame k r input.length limit wf
  change 2^(count+2)*payload+1 = 4*(4^(limit+1+extraPairs k r input.length)*(2*wf))+1 at hgeometry
  rw [hgeometry] at hr
  let d : Config := ⟨2*(4*(4^(limit+1+extraPairs k r input.length)*(2*wf))+1),
    encodeFrame input (4*(2*higher+1)),some 0⟩
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hfinal := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨2*(4*(4^(limit+1+extraPairs k r input.length)*(2*wf))+1),
      encodeFrame input (4*(2*higher+1)),active 0⟩ fuel = _ at hfinal
  rw [← hfinal] at hr
  exact hr

theorem rejected_raw_never_accepts (k r states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r states continuation) input certificate clock = false := by
  have hc := Source284InputCounterTransfer.closed states continuation hn hv
  unfold description
  exact Source284CheckpointMarkedReveal.rejected_raw_never_accepts k r (178+states)
    (Source284InputCounterTransfer.table continuation) input certificate (by omega) hc hbad

end Shared.Beeping.NPcoNP.Source284MarkedInputTransfer
