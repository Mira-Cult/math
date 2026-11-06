import Shared.Beeping.NPcoNP.Source284WitnessReframe
import Shared.Beeping.NPcoNP.Source284CertificatePrefix

/-! Join the adjacent input and witness frames into one finite raw window.
The input frame is reversed by the physical scan, followed by an explicit
three-zero boundary and the forward witness frame. This is a faithful
self-delimiting alternative layout, not Google's pair serialization. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284JoinedFrames

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame frameBits payloadFold)
open Shared.Beeping.NPcoNP.Source284WitnessScanArithmetic (pushPairs)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)

def turner (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 4⟩
  else if q < 4 then ⟨b,false,some q⟩
  else shiftRow 4 (continuation (q-4) b)

theorem turner_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (4+states) (turner continuation) := by
  intro q hq b q' hnext
  by_cases hs : q < 4
  · interval_cases q <;> cases b <;> simp [turner] at hnext <;> omega
  · have ht : (shiftRow 4 (continuation (q-4) b)).next = some q' := by
      simpa [turner,show q ≠ 0 by omega,hs] using hnext
    cases he : (continuation (q-4) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-4) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem turner_relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    turner continuation (4+q) b = shiftRow 4 (continuation q b) := by
  simp [turner,show ¬ 4+q < 4 by omega]

theorem turner_relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (turner continuation) (shiftConfig 4 c) = shiftConfig 4 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,turner_relocated_row,shiftRow]
      split <;> rfl

theorem turner_relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (turner continuation) (shiftConfig 4 c) fuel = shiftConfig 4 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,turner_relocated_step]

theorem turner_step (continuation : Nat → Bool → Row) (left right : Nat) :
    step (turner continuation) ⟨left,right,some 0⟩ = ⟨right,left,some 4⟩ := by
  apply Source284WindowRewind.generic_turn; intro b; simp [turner]

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨false,false,some 3⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else shiftRow 4 (Source284ModePrefixScan.table (turner continuation) (q-4) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (16+states) (table continuation) := by
  have hc := turner_closed states continuation hn hv
  have hs := Source284ModePrefixScan.closed (4+states) (turner continuation) (by omega) hc
  intro q hq b q' hnext
  by_cases h : q < 4
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have ht : (shiftRow 4 (Source284ModePrefixScan.table (turner continuation) (q-4) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,
        show q ≠ 2 by omega,show q ≠ 3 by omega] using hnext
    cases he : (Source284ModePrefixScan.table (turner continuation) (q-4) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have hh := hs (q-4) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (4+q) b = shiftRow 4 (Source284ModePrefixScan.table (turner continuation) q b) := by
  simp [table,show 4+q ≠ 1 by omega,show 4+q ≠ 2 by omega,show 4+q ≠ 3 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 4 c) =
      shiftConfig 4 (step (Source284ModePrefixScan.table (turner continuation)) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 4 c) fuel =
      shiftConfig 4 (run (Source284ModePrefixScan.table (turner continuation)) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- Cross the fixed `0,1,0` boundary; clear its one sentinel to make a
three-zero separator in the joined output. -/
theorem setup (continuation : Nat → Bool → Row) (inputFrame witnessFrame : Nat) :
    run (table continuation) ⟨2*(4*inputFrame+1),witnessFrame,some 0⟩ 4 =
      ⟨8*witnessFrame,inputFrame,some 4⟩ := by
  have h0 : step (table continuation) ⟨2*(4*inputFrame+1),witnessFrame,some 0⟩ =
      ⟨witnessFrame,2*(4*inputFrame+1),some 1⟩ := by
    apply Source284WindowRewind.generic_turn; intro b; simp [table]
  have h1 : step (table continuation) ⟨witnessFrame,2*(4*inputFrame+1),some 1⟩ =
      ⟨2*witnessFrame,4*inputFrame+1,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h2 : step (table continuation) ⟨2*witnessFrame,4*inputFrame+1,some 2⟩ =
      ⟨4*witnessFrame,2*inputFrame,some 3⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have h3 : step (table continuation) ⟨4*witnessFrame,2*inputFrame,some 3⟩ =
      ⟨8*witnessFrame,inputFrame,some 4⟩ := by
    simp [step,table,bit,Nat.testBit_zero] <;> omega
  simp only [run,h0,h1,h2,h3]

/-- The scan and paid turn join both frames on the forward side. -/
theorem join_then (continuation : Nat → Bool → Row) (x : List Bool)
    (inputSuffix witnessFrame fuel : Nat) :
    run (table continuation) ⟨2*(4*encodeFrame x inputSuffix+1),witnessFrame,some 0⟩
      ((2*x.length+6)+fuel) =
    shiftConfig 16 (run continuation
      ⟨inputSuffix,2*pushPairs (8*witnessFrame) x,some 0⟩ fuel) := by
  have ht : 2*x.length+6 = 4+((2*x.length+1)+1) := by omega
  rw [ht,Nat.add_assoc,run_add,setup]
  change run (table continuation) (shiftConfig 4
    ⟨8*witnessFrame,encodeFrame x inputSuffix,some 0⟩) _ = _
  rw [relocated_run]
  rw [show 2*x.length+1+1+fuel = (2*x.length+1)+(1+fuel) by omega]
  change shiftConfig 4 (run (Source284ModePrefixScan.table (turner continuation))
    ⟨8*witnessFrame,encodeFrame x inputSuffix,some 0⟩ ((2*x.length+1)+(1+fuel))) = _
  rw [run_add,Source284ModePrefixScan.scan_frame _ 0 (by omega)]
  change shiftConfig 4 (run (Source284ModePrefixScan.table (turner continuation))
    (shiftConfig 8 ⟨2*pushPairs (8*witnessFrame) x,inputSuffix,some 0⟩) _) = _
  rw [Source284ModePrefixScan.relocated_run]
  change shiftConfig 4 (shiftConfig 8 (run (turner continuation)
    ⟨2*pushPairs (8*witnessFrame) x,inputSuffix,some 0⟩ (1+fuel))) = _
  rw [run_add]
  simp only [run,turner_step]
  change shiftConfig 4 (shiftConfig 8 (run (turner continuation)
    (shiftConfig 4 ⟨inputSuffix,2*pushPairs (8*witnessFrame) x,some 0⟩) fuel)) = _
  rw [turner_relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

def joinedBits (x w : List Bool) : List Bool :=
  (frameBits x []).reverse ++ [false,false,false] ++ frameBits w [true]

theorem stack_frame_sentinel (w : List Bool) (tail : Nat) :
    stack (frameBits w [true]) tail = encodeFrame w (2*tail+1) := by
  induction w with
  | nil => simp [frameBits,stack,encodeFrame]
  | cons b bs ih =>
    cases b <;> simp [frameBits,stack,encodeFrame,ih] <;> omega

/-- Exact low-first joined stream, followed by the untouched arbitrary high
witness suffix. Three zeros separate reversed input and forward witness. -/
theorem joined_stack (x w : List Bool) (tail : Nat) :
    2*pushPairs (8*encodeFrame w (2*tail+1)) x = stack (joinedBits x w) tail := by
  rw [← Source284WitnessScanArithmetic.payloadFold_frame,
    Source284LoaderAlgebra.pushed_eq_stack]
  unfold joinedBits
  rw [Source284CertificatePrefix.stack_append,Source284CertificatePrefix.stack_append,
    stack_frame_sentinel]
  simp [stack]
  congr 1 <;> omega

theorem joined_length (x w : List Bool) : (joinedBits x w).length = 2*x.length+2*w.length+6 := by
  unfold joinedBits
  rw [List.length_append,List.length_append,List.length_reverse,
    Source284WitnessScanArithmetic.frame_length,Source284WitnessWindow.frame_length]
  simp
  omega

/-- A pair's second bit is its one marker. Three zeros terminate the reversed
input segment and separate it from the forward witness frame. -/
def reverseBlocks : List Bool → List Bool
  | [] => []
  | b::bs => b::true::reverseBlocks bs

theorem reverseBlocks_append (xs ys : List Bool) :
    reverseBlocks (xs++ys) = reverseBlocks xs ++ reverseBlocks ys := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [reverseBlocks,ih]

theorem reversed_frame (x : List Bool) :
    (frameBits x []).reverse = false :: reverseBlocks x.reverse := by
  induction x with
  | nil => rfl
  | cons b bs ih =>
    simp [frameBits,List.reverse_cons,ih,reverseBlocks_append,reverseBlocks]

def readReverse : List Bool → Option (List Bool × List Bool)
  | b::true::bs => (readReverse bs).map (fun p => (b::p.1,p.2))
  | false::false::false::bs => some ([],bs)
  | _ => none

theorem readReverse_blocks (xs rest : List Bool) :
    readReverse (reverseBlocks xs ++ [false,false,false] ++ rest) = some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons b bs ih =>
    have ih' : readReverse (reverseBlocks bs ++ (false::false::false::rest)) = some (bs,rest) := by
      simpa [List.append_assoc] using ih
    cases b <;> simp [reverseBlocks,readReverse,ih']

def decodeJoined (bits : List Bool) : Option (List Bool × List Bool) :=
  match bits with
  | false::rest => (readReverse rest).map (fun p => (p.1.reverse,Source284RawParse.payload p.2))
  | _ => none

theorem frameBits_append (w suffix extra : List Bool) :
    frameBits w suffix ++ extra = frameBits w (suffix++extra) := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits,ih]

theorem payload_frame_suffix (w suffix : List Bool) :
    Source284RawParse.payload (frameBits w suffix) = w := by
  induction w with
  | nil => rfl
  | cons b bs ih => simp [frameBits,Source284RawParse.payload,ih]

/-- The finite joined prefix uniquely identifies both original lists even
when an arbitrary high bit suffix follows the witness sentinel. -/
theorem decodeJoined_complete (x w extra : List Bool) :
    decodeJoined (joinedBits x w ++ extra) = some (x,w) := by
  unfold joinedBits decodeJoined
  rw [reversed_frame]
  simp only [List.cons_append]
  have h := readReverse_blocks x.reverse (frameBits w [true] ++ extra)
  simp only [List.append_assoc] at h ⊢
  rw [h]
  simp only [Option.map_some,List.reverse_reverse,Prod.fst,Prod.snd]
  rw [frameBits_append,payload_frame_suffix]

/-- The valid tagged certificate path reaches the single joined raw window.
All boundary edits, input scanning, and subsequent continuation steps are
included. The supplied continuation must still implement its own verifier. -/
theorem decoded_join_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(160+(68+(16+states))))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table (table continuation))))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
              ((2*(Source284RawParse.payload input.bits).length+6)+fuel))))) =
      Source284SourceRelocation.lift 782 (Source284Relative.run (encode states continuation 1)
        ⟨2*(inputSuffix/4)+1,
          stack (joinedBits (Source284RawParse.payload input.bits) w)
            (2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284WitnessReframe.decoded_reframe_then
    (16+states) (table continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let inputSuffix := 2*(is/4)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let t := 2*x.length+6
  have hr' := hr (t+fuel)
  change Source284Relative.run _ _ _ = Source284SourceRelocation.lift 766
    (Source284Relative.run (encode (16+states) (table continuation) 1)
      ⟨2*(4*encodeFrame x inputSuffix+1),encodeFrame w (2*tail+1),active 0⟩ (t+fuel)) at hr'
  let c : Config := ⟨2*(4*encodeFrame x inputSuffix+1),encodeFrame w (2*tail+1),some 0⟩
  have hc : Valid (16+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (16+states) (table continuation) 1 c
    (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (16+states) (table continuation) 1)
    ⟨2*(4*encodeFrame x inputSuffix+1),encodeFrame w (2*tail+1),active 0⟩ (t+fuel) = _ at hv0
  have hp := join_then continuation x inputSuffix (encodeFrame w (2*tail+1)) fuel
  rw [joined_stack] at hp
  change run (table continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨inputSuffix,stack (joinedBits x w) tail,some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨inputSuffix,stack (joinedBits x w) tail,active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

theorem decoded_join_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
          (2*(Source284RawParse.payload input.bits).length+6)))) ≤
      24*limit*limit+154*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        30*Source284Parser.length input+246 := by
  have h0 := Source284WitnessReframe.decoded_reframe_bound limit certificate input w hdec
  have hx : (Source284RawParse.payload input.bits).length = Source284Parser.length input := by
    have h := Source284RawParse.parse_length input.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  rw [hx]
  omega

namespace Fixtures
example : decodeJoined (joinedBits [] [] ++ [true,false,true]) = some ([],[]) :=
  decodeJoined_complete [] [] [true,false,true]
example : decodeJoined (joinedBits [false,true] [true,false] ++ [true,true]) =
    some ([false,true],[true,false]) := decodeJoined_complete _ _ _
end Fixtures
end Shared.Beeping.NPcoNP.Source284JoinedFrames
