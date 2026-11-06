import Shared.Beeping.NPcoNP.Source284MarkedInputTransferCost
import Shared.Beeping.NPcoNP.Source284DynamicJoinedInput

/-! Join the input and guarded witness after the source-generated workspace
counter has been transferred to the witness gap. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284MarkedJoinedInput

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)
open Shared.Beeping.NPcoNP.Source284CheckpointMarkedWorkspace (markCount blankTail)
open Shared.Beeping.NPcoNP.Source284InputCounterGeometry (extraPairs)

def description (k r states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284MarkedInputTransfer.description k r (254+states) (Source284DynamicJoinedInput.table continuation)

def enlargedLimit (k r n : Nat) : Nat := Source284DynamicGuardSource.bound k n+extraPairs k r n

def totalCost (k r : Nat) (input witness : List Bool) : Nat :=
  Source284MarkedInputTransfer.totalCost k r input witness+
    Source284DynamicJoinedInput.cost (enlargedLimit k r input.length) input witness

/-- The actual guard uses its original cutoff. After transfer, the existing
seek and compactor use the larger gap and deliver the exact joined stream. -/
theorem decoded_joined (k r states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (certificate inputSuffix : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate=4*encodeFrame witness witnessSuffix ∧ ∀ fuel,
      let limit := enlargedLimit k r input.length
      let inputTail := blankTail k r input.length inputSuffix/2
      Source284Relative.run (description k r states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k r input witness+fuel) =
      lift (1371+317*k+317*r+318+1+178+254) (Source284Relative.run (encode states continuation 1)
        ⟨4*(2*inputTail+1),stack (Source284JoinedFrames.joinedBits input witness)
          (Source284DynamicJoinedInput.witnessTail limit witnessSuffix),active 0⟩ fuel) := by
  have hc := Source284DynamicJoinedInput.closed states continuation hn hv
  obtain ⟨witnessSuffix,hcert,hframe⟩ := Source284MarkedInputTransfer.decoded_transferred
    k r (254+states) (Source284DynamicJoinedInput.table continuation) input witness certificate inputSuffix
    (by omega) hc hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  have htime : totalCost k r input witness+fuel =
      Source284MarkedInputTransfer.totalCost k r input witness+
        (Source284DynamicJoinedInput.cost (enlargedLimit k r input.length) input witness+fuel) := by
    unfold totalCost
    omega
  rw [htime]
  let limit := enlargedLimit k r input.length
  let t := blankTail k r input.length inputSuffix/2
  let wf := encodeFrame witness (8*((witnessSuffix/4)/4)+1)
  let saved := 4*(4^(limit+1)*(2*wf))+1
  let inputFrame := encodeFrame input (4*(2*t+1))
  have hr := hframe (Source284DynamicJoinedInput.cost limit input witness+fuel)
  have hexp : Source284DynamicGuardSource.bound k input.length+1+extraPairs k r input.length = limit+1 := by
    dsimp [limit,enlargedLimit]; omega
  dsimp only at hr
  rw [hexp] at hr
  change Source284Relative.run (description k r states continuation) _ _ =
    lift (1371+317*k+317*r+318+1+178) (Source284Relative.run
      (encode (254+states) (Source284DynamicJoinedInput.table continuation) 1)
      ⟨2*saved,inputFrame,active 0⟩ (Source284DynamicJoinedInput.cost limit input witness+fuel)) at hr
  let c : Config := ⟨2*saved,inputFrame,some 0⟩
  have hvalid : Valid (254+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have heval := run_toSource (254+states) (Source284DynamicJoinedInput.table continuation) 1 c hc hvalid
    (Source284DynamicJoinedInput.cost limit input witness+fuel)
  change Source284Relative.run (encode (254+states) (Source284DynamicJoinedInput.table continuation) 1)
    ⟨2*saved,inputFrame,active 0⟩ _ = _ at heval
  have hj := Source284DynamicJoinedInput.join_then states continuation limit (4*(2*t+1)) witnessSuffix
    fuel input witness hn hv
  change run (Source284DynamicJoinedInput.table continuation) c _ = _ at hj
  rw [heval,hj,← lift_toSource,Source284SourceRelocation.lift_add] at hr
  let d : Config := ⟨4*(2*t+1),stack (Source284JoinedFrames.joinedBits input witness)
    (Source284DynamicJoinedInput.witnessTail limit witnessSuffix),some 0⟩
  have hd : Valid states d := by intro q hq; simp [d] at hq; subst q; exact hn
  have hfinal := run_toSource states continuation 1 d hv hd fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨4*(2*t+1),stack (Source284JoinedFrames.joinedBits input witness)
      (Source284DynamicJoinedInput.witnessTail limit witnessSuffix),active 0⟩ fuel = _ at hfinal
  rw [← hfinal] at hr
  exact hr

theorem rejected_raw_never_accepts (k r states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r states continuation) input certificate clock = false := by
  have hc := Source284DynamicJoinedInput.closed states continuation hn hv
  unfold description
  exact Source284MarkedInputTransfer.rejected_raw_never_accepts k r (254+states)
    (Source284DynamicJoinedInput.table continuation) input certificate (by omega) hc hbad

/-- The transferred counter provides a blank witness suffix at least as
long as the counter, independent of every high certificate bit. -/
theorem witness_tail_zero (k r n suffix depth : Nat)
    (hfit : depth ≤ markCount k r n-1) :
    2^depth ∣ Source284DynamicJoinedInput.witnessTail (enlargedLimit k r n) suffix := by
  have hgap := Source284InputCounterGeometry.counter_le_pairs k r n
  have he : depth ≤ 2*((enlargedLimit k r n+1)+1) := by
    unfold enlargedLimit
    omega
  unfold Source284DynamicJoinedInput.witnessTail
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 he) _

/-- The input-side tail retains a separate blank prefix after the counter is
consumed, so the transfer supplies space on both sides of the joined frame. -/
theorem input_tail_zero (k r n suffix depth : Nat)
    (hfit : depth ≤ Source284CheckpointWorkspace.workspace k r n) :
    2^depth ∣ blankTail k r n suffix/2 := by
  unfold blankTail
  let rest := Source284TokenCounterLoop.halves (Source284CheckpointWorkspace.workspace k r n)
    ((Source284ProductIteration.suffixAfter (r+2)
      (Source284CheckpointWorkspace.previous k n) (Source284CheckpointWorkspace.guard k n)
      (Source284ProductIteration.suffixAfter k (Source284CheckpointWorkspace.base n)
        (Source284CheckpointWorkspace.base n) (Source284SentinelPositiveTokens.retained n suffix)))/2)
  change 2^depth ∣ (2^(Source284CheckpointWorkspace.workspace k r n+1)*rest)/2
  have he : 2^(Source284CheckpointWorkspace.workspace k r n+1)*rest =
      2*(2^(Source284CheckpointWorkspace.workspace k r n)*rest) := by rw [pow_succ]; ring
  have hd : (2*(2^(Source284CheckpointWorkspace.workspace k r n)*rest))/2 =
      2^(Source284CheckpointWorkspace.workspace k r n)*rest := by omega
  rw [he,hd]
  exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hfit) _

end Shared.Beeping.NPcoNP.Source284MarkedJoinedInput
