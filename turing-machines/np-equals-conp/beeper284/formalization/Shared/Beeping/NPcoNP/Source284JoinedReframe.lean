import Shared.Beeping.NPcoNP.Source284CertificateJoinCoverage
import Shared.Beeping.NPcoNP.Source284JoinedReframeAdapter

/-! Complete source execution to adjacent normalized frames. The input's
extra loader dummy is removed by the paid finite pop. The remaining layout
still requires a source-level join and canonical serializer. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284JoinedReframe

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284CertificateProbeLayout (firstZeros)
open Shared.Beeping.NPcoNP.Source284CertificatePackSource (stream)
open Shared.Beeping.NPcoNP.Source284CertificateJoin (witnessTail)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)

def inputTail (k : Nat) (x : List Bool) (suffix : Nat) :=
  2^(k*(x.length*x.length)+1)*Source284TwoSidedScaledQuadratic.finalTail k x.length suffix

def finishing (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchNormalize.table (Source284JoinedReframeAdapter.table continuation)

theorem finishing_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (206+states) (finishing continuation) := by
  have h0 := Source284JoinedReframeAdapter.closed states continuation hn hv
  have h1 := Source284WitnessReframe.closed (138+states) (Source284JoinedReframeAdapter.table continuation) (by omega) h0
  change Closed (68+(138+states)) (finishing continuation) at h1
  convert h1 using 1 <;> omega

def finishingCost (x w : List Bool) := (6*w.length+11)+Source284JoinedReframeAdapter.cost x

/-- Two finite normalizers and the dummy-pop pass reach adjacent input and
witness frames; each subsequent continuation step follows exactly. -/
theorem finishing_then (states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix witnessSuffix k fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (finishing continuation)
      ⟨2*stream k input inputSuffix,
        2*flipped witness (witnessTail (firstZeros k input.length) input.length witnessSuffix),some 0⟩
      (finishingCost input witness+fuel) =
    shiftConfig 206 (run continuation
      ⟨4*encodeFrame witness (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1),
        encodeFrame input (4*(2*inputTail k input inputSuffix+1)),some 0⟩ fuel) := by
  have ht : finishingCost input witness+fuel = (6*witness.length+11)+
      (Source284JoinedReframeAdapter.cost input+fuel) := by simp [finishingCost]; omega
  rw [ht]
  unfold finishing
  rw [Source284WitnessReframe.normalize_then]
  have he : 2*(2*stream k input inputSuffix)=4*stream k input inputSuffix := by omega
  rw [he]
  change shiftConfig 68 (run (Source284JoinedReframeAdapter.table continuation)
    ⟨4*flipped (input++[false]) (inputTail k input inputSuffix),
      encodeFrame witness (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1),some 0⟩ _) = _
  rw [Source284JoinedReframeAdapter.reframe_then states continuation input (inputTail k input inputSuffix)
    (encodeFrame witness (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1)) fuel hn hv,
    Source284SourceRelocation.shiftConfig_add]

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284CertificateJoin.table (finishing continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (411+states) (table continuation) := by
  have h := Source284CertificateJoin.closed (206+states) (finishing continuation)
    (by omega) (finishing_closed states continuation hn hv)
  change Closed (205+(206+states)) (table continuation) at h
  convert h using 1 <;> omega

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284TwoSidedScaledQuadratic.description k (411+states) (table continuation)

def totalCost (k : Nat) (input witness : List Bool) : Nat :=
  Source284CertificateJoin.totalCost k input witness+finishingCost input witness

theorem source_reframe_then (k states : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (witnessSuffix inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame input inputSuffix) (4*encodeFrame witness witnessSuffix))
      (totalCost k input witness+fuel) =
    toSource (shiftConfig (1251+220*k) (run continuation
      ⟨4*encodeFrame witness (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1),
        encodeFrame input (4*(2*inputTail k input inputSuffix+1)),some 0⟩ fuel)) := by
  have hp := Source284CertificateJoin.source_join_then k (206+states) (finishing continuation)
    input witness witnessSuffix inputSuffix (finishingCost input witness+fuel)
    (by omega) (finishing_closed states continuation hn hv)
  have hd : description k states continuation =
      Source284CertificateJoin.description k (206+states) (finishing continuation) := by
    unfold description table Source284CertificateJoin.description
    congr 1 <;> omega
  have ht : totalCost k input witness+fuel = Source284CertificateJoin.totalCost k input witness+
      (finishingCost input witness+fuel) := by simp [totalCost]; omega
  rw [hd,ht,hp,finishing_then states continuation input witness inputSuffix witnessSuffix k fuel hn hv,
    Source284SourceRelocation.shiftConfig_add]
  have he : 1045+220*k+206=1251+220*k := by omega
  rw [he]

theorem decoded_reframe_then (k states limit certificate : Nat) (continuation : Nat → Bool → Row)
    (input witness : List Bool) (inputSuffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some witness) :
    ∃ witnessSuffix,
      certificate=4*encodeFrame witness witnessSuffix ∧
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame input inputSuffix) certificate)
        (totalCost k input witness+fuel) =
      toSource (shiftConfig (1251+220*k) (run continuation
        ⟨4*encodeFrame witness (2*witnessTail (firstZeros k input.length) input.length witnessSuffix+1),
          encodeFrame input (4*(2*inputTail k input inputSuffix+1)),some 0⟩ fuel)) := by
  obtain ⟨suffix,hcert⟩ := Source284CertificateProbeSource.decoded_has_frame limit certificate witness hdec
  refine ⟨suffix,hcert,?_⟩
  rw [hcert]
  exact source_reframe_then k states continuation input witness suffix inputSuffix fuel hn hv

theorem finishingCost_bound (n limit certificate : Nat) (x w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) (hx : x.length=n) :
    finishingCost x w ≤ 6*limit+10*n+46 := by
  have hlen := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  unfold finishingCost Source284JoinedReframeAdapter.cost
  simp only [List.length_append,List.length_cons,List.length_nil]
  omega

end Shared.Beeping.NPcoNP.Source284JoinedReframe
