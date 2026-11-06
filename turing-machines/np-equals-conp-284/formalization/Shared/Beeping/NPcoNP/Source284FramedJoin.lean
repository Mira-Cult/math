import Shared.Beeping.NPcoNP.Source284JoinedReframeCoverage
import Shared.Beeping.NPcoNP.Source284JoinedTripleAdapter
import Shared.Beeping.NPcoNP.Source284TripleFrameJoin
import Shared.Beeping.NPcoNP.Source284ShiftContinue

/-! Raw-input to the existing three-zero joined-prefix encoding, through a
paid finite scratch shift, two frame normalizers, dummy removal and join.
This source program is not the literal 284-state machine. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284FramedJoin

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284JoinedReframe (inputTail)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)

def finishing (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchShiftCycle.table (Source284ScratchNormalize.table
    (Source284JoinedTripleAdapter.table (Source284TripleFrameJoin.table continuation)))

theorem finishing_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (241+states) (finishing continuation) := by
  have h0 := Source284TripleFrameJoin.closed states continuation hn hv
  have h1 := Source284JoinedTripleAdapter.closed (20+states) (Source284TripleFrameJoin.table continuation) (by omega) h0
  have h2 := Source284WitnessReframe.closed (139+(20+states))
    (Source284JoinedTripleAdapter.table (Source284TripleFrameJoin.table continuation)) (by omega) h1
  have h3 := Source284ScratchShiftCycle.closed (68+(139+(20+states)))
    (Source284ScratchNormalize.table (Source284JoinedTripleAdapter.table (Source284TripleFrameJoin.table continuation)))
    (by omega) h2
  change Closed (14+(68+(139+(20+states)))) (finishing continuation) at h3
  convert h3 using 1 <;> omega

def finishingCost (x w : List Bool) :=
  (4*w.length+7)+(6*w.length+11)+Source284JoinedTripleAdapter.cost x+(2*x.length+10)

theorem finishing_then (states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix witnessSuffix k fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (finishing continuation)
      ⟨2*stream k input inputSuffix,
        2*flipped witness (witnessTail (firstZeros k input.length) input.length witnessSuffix),some 0⟩
      (finishingCost input witness+fuel) =
    shiftConfig 241 (run continuation
      ⟨4*(2*inputTail k input inputSuffix+1),
        stack (Source284JoinedFrames.joinedBits input witness)
          (witnessTail (firstZeros k input.length) input.length witnessSuffix/2),some 0⟩ fuel) := by
  have ht : finishingCost input witness+fuel = (4*witness.length+7)+((6*witness.length+11)+
      (Source284JoinedTripleAdapter.cost input+((2*input.length+10)+fuel))) := by simp [finishingCost]; omega
  rw [ht]
  unfold finishing
  rw [Source284ShiftContinue.cycle_then,Source284WitnessReframe.normalize_then]
  have he : 2*(2*(2*stream k input inputSuffix))=8*stream k input inputSuffix := by omega
  rw [he]
  change shiftConfig 14 (shiftConfig 68 (run (Source284JoinedTripleAdapter.table (Source284TripleFrameJoin.table continuation))
    ⟨8*flipped (input++[false]) (inputTail k input inputSuffix),
      encodeFrame witness (2*(witnessTail (firstZeros k input.length) input.length witnessSuffix/2)+1),some 0⟩ _)) = _
  rw [Source284JoinedTripleAdapter.reframe_then (20+states) (Source284TripleFrameJoin.table continuation)
      input (inputTail k input inputSuffix)
      (encodeFrame witness (2*(witnessTail (firstZeros k input.length) input.length witnessSuffix/2)+1))
      ((2*input.length+10)+fuel) (by omega) (Source284TripleFrameJoin.closed states continuation hn hv),
    Source284TripleFrameJoin.join_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CertificateJoin.table (finishing continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (446+states) (table continuation) := by
  have h := Source284CertificateJoin.closed (241+states) (finishing continuation)
    (by omega) (finishing_closed states continuation hn hv)
  change Closed (205+(241+states)) (table continuation) at h
  convert h using 1 <;> omega

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (446+states) (table continuation)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284CertificateJoin.totalCost k input witness+finishingCost input witness

/-- From raw input and a tagged witness frame the actual finite source table
reaches the exact existing joined-prefix layout and follows its continuation. -/
theorem source_joined_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (1286+220*k) (run continuation
      ⟨4*(2*inputTail k input inputSuffix+1),
        stack (Source284JoinedFrames.joinedBits input witness)
          (witnessTail (firstZeros k input.length) input.length witnessSuffix/2),some 0⟩ fuel)) := by
  have hp := Source284CertificateJoin.source_join_then k (241+states) (finishing continuation)
    input witness witnessSuffix inputSuffix (finishingCost input witness+fuel)
    (by omega) (finishing_closed states continuation hn hv)
  have hd : description k states continuation =
      Source284CertificateJoin.description k (241+states) (finishing continuation) := by
    unfold description table Source284CertificateJoin.description
    congr 1 <;> omega
  have ht : totalCost k input witness+fuel = Source284CertificateJoin.totalCost k input witness+
      (finishingCost input witness+fuel) := by simp [totalCost]; omega
  rw [hd,ht,hp,finishing_then states continuation input witness inputSuffix witnessSuffix k fuel hn hv,
    Source284SourceRelocation.shiftConfig_add]
  have he : 1045+220*k+241=1286+220*k := by omega
  rw [he]

theorem decoded_joined_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (1286+220*k) (run continuation
        ⟨4*(2*inputTail k input inputSuffix+1),
          stack (Source284JoinedFrames.joinedBits input witness)
            (witnessTail (firstZeros k input.length) input.length witnessSuffix/2),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_joined_then k states continuation input witness suffix inputSuffix fuel hn hv

theorem finishingCost_bound (limit certificate : Nat) (x w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    finishingCost x w ≤ 10*limit+12*x.length+64 := by
  have hlen := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  unfold finishingCost Source284JoinedTripleAdapter.cost
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

end Shared.Beeping.NPcoNP.Source284FramedJoin
