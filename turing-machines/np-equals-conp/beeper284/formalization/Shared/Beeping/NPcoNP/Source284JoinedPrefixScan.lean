import Shared.Beeping.NPcoNP.Source284JoinedFrames

/-! A finite source-table scan isolates the exact joined prefix from arbitrary
high suffix data. It clears the final known one sentinel and turns at that
boundary, leaving the prefix reversed on one half and the suffix on the other.
It does not yet produce the fixed-width serialized TM2 initial tape. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284JoinedPrefixScan

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame frameBits payloadFold)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284JoinedFrames (joinedBits reverseBlocks)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,false,some (if b then 1 else 3)⟩
  else if q = 3 then ⟨b,false,some 4⟩
  else if q = 4 then ⟨b,false,some (if b then 5 else 6)⟩
  else if q = 5 then ⟨b,false,some 4⟩
  else if q = 6 then ⟨false,true,some 7⟩
  else shiftRow 7 (continuation (q-7) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q < 7
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have ht : (shiftRow 7 (continuation (q-7) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 5 by omega,show q ≠ 6 by omega] using hnext
    cases he : (continuation (q-7) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-7) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (7+q) b = shiftRow 7 (continuation q b) := by
  simp [table,show 7+q ≠ 1 by omega,show 7+q ≠ 2 by omega,show 7+q ≠ 3 by omega,
    show 7+q ≠ 4 by omega,show 7+q ≠ 5 by omega,show 7+q ≠ 6 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 7 c) = shiftConfig 7 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 7 c) fuel = shiftConfig 7 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem data_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,stack [b,true] tail,some 1⟩ 2 =
      ⟨4*left+2*bit b+1,tail,some 1⟩ := by
  cases b <;> simp [run,step,table,stack,bit,Nat.testBit_zero,Nat.add_mod] <;>
    (repeat' constructor) <;> (try split_ifs) <;> omega

theorem data_blocks (continuation : Nat → Bool → Row) (xs : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,stack (reverseBlocks xs) tail,some 1⟩ (2*xs.length) =
      ⟨payloadFold left (reverseBlocks xs),tail,some 1⟩ := by
  induction xs generalizing left with
  | nil => rfl
  | cons b bs ih =>
    have ht : 2*(b::bs).length = 2+2*bs.length := by simp; omega
    rw [ht,run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,stack [b,true] (stack (reverseBlocks bs) tail),some 1⟩ 2) _ = _
    rw [data_pair,ih]
    cases b <;> simp [reverseBlocks,payloadFold,bit] <;> congr 1 <;> omega

theorem separator (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,stack [false,false,false] tail,some 1⟩ 3 =
      ⟨8*left,tail,some 4⟩ := by
  simp [run,step,table,stack,bit,Nat.testBit_zero] <;> omega

theorem witness_pair (continuation : Nat → Bool → Row) (left tail : Nat) (b : Bool) :
    run (table continuation) ⟨left,stack [true,b] tail,some 4⟩ 2 =
      ⟨4*left+2+bit b,tail,some 4⟩ := by
  cases b <;> simp [run,step,table,stack,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;>
    congr 1 <;> try split_ifs <;> omega

theorem witness_frame (continuation : Nat → Bool → Row) (w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,stack (frameBits w []) tail,some 4⟩ (2*w.length+1) =
      ⟨payloadFold left (frameBits w []),tail,some 6⟩ := by
  induction w generalizing left with
  | nil =>
    simp [frameBits,stack,payloadFold,run,step,table,bit,Nat.testBit_zero]
  | cons b bs ih =>
    have ht : 2*(b::bs).length+1 = 2+(2*bs.length+1) := by simp; omega
    rw [ht,run_add]
    change run (table continuation)
      (run (table continuation) ⟨left,stack [true,b] (stack (frameBits bs []) tail),some 4⟩ 2) _ = _
    rw [witness_pair,ih]
    cases b <;> simp [frameBits,payloadFold,bit] <;> congr 1 <;> omega

def joinedBody (x w : List Bool) : List Bool :=
  (frameBits x []).reverse ++ [false,false,false] ++ frameBits w []

theorem joined_eq_body (x w : List Bool) : joinedBits x w = joinedBody x w ++ [true] := by
  unfold joinedBits joinedBody
  have hf : frameBits w [true] = frameBits w [] ++ [true] := by
    simpa using (Source284JoinedFrames.frameBits_append w [] [true]).symm
  simp [hf,List.append_assoc]

/-- The exact joined prefix is consumed in one transition per bit. The final
one is cleared and the direction reverses; neither high suffix is scanned. -/
theorem scan (continuation : Nat → Bool → Row) (x w : List Bool) (left tail : Nat) :
    run (table continuation) ⟨left,stack (joinedBits x w) tail,some 0⟩ (joinedBits x w).length =
      ⟨2*tail,payloadFold left (joinedBody x w),some 7⟩ := by
  have he : stack (joinedBits x w) tail =
      stack (false::(reverseBlocks x.reverse ++ [false,false,false] ++ frameBits w [])) (2*tail+1) := by
    rw [joined_eq_body]
    unfold joinedBody
    rw [Source284CertificatePrefix.stack_append]
    simp [joinedBody,Source284JoinedFrames.reversed_frame,stack]
  have hlen : (joinedBits x w).length = 1+(2*x.length+(3+((2*w.length+1)+1))) := by
    rw [Source284JoinedFrames.joined_length]; omega
  rw [he,hlen,show 1+(2*x.length+(3+((2*w.length+1)+1))) =
    (2*x.length+(3+((2*w.length+1)+1)))+1 by omega,
    Source284HardwireTable.run_front]
  have h0 : step (table continuation)
      ⟨left,stack (false::(reverseBlocks x.reverse ++ [false,false,false] ++ frameBits w [])) (2*tail+1),some 0⟩ =
      ⟨2*left,stack (reverseBlocks x.reverse ++ [false,false,false] ++ frameBits w []) (2*tail+1),some 1⟩ := by
    simp [step,table,stack,bit,Nat.testBit_zero]
  rw [h0]
  simp only [List.append_assoc,Source284CertificatePrefix.stack_append]
  rw [run_add]
  have hd := data_blocks continuation x.reverse (2*left)
    (stack [false,false,false] (stack (frameBits w []) (2*tail+1)))
  simp only [List.length_reverse] at hd
  rw [hd,run_add,separator,run_add,witness_frame]
  have hlast : step (table continuation)
      ⟨payloadFold (8*payloadFold (2*left) (reverseBlocks x.reverse)) (frameBits w []),2*tail+1,some 6⟩ =
      ⟨2*tail,payloadFold (8*payloadFold (2*left) (reverseBlocks x.reverse)) (frameBits w []),some 7⟩ := by
    simp [step,table,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  simp only [run]
  rw [hlast]
  congr 1
  unfold joinedBody
  rw [Source284JoinedFrames.reversed_frame]
  simp [payloadFold,Shared.Beeping.NPcoNP.Source284CertificateDispatch.payloadFold_append,List.append_assoc]
  congr 1 <;> omega

/-- Every later continuation step follows the isolated-prefix scan. -/
theorem scan_then (continuation : Nat → Bool → Row) (x w : List Bool) (left tail fuel : Nat) :
    run (table continuation) ⟨left,stack (joinedBits x w) tail,some 0⟩
      ((joinedBits x w).length+fuel) =
    shiftConfig 7 (run continuation ⟨2*tail,payloadFold left (joinedBody x w),some 0⟩ fuel) := by
  rw [run_add,scan]
  change run (table continuation) (shiftConfig 7 ⟨2*tail,payloadFold left (joinedBody x w),some 0⟩) fuel = _
  rw [relocated_run]

/-- The actual decoded source reaches the isolated-prefix boundary before the
continuation starts. The original high suffixes are arbitrary. -/
theorem decoded_scan_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(160+(68+(16+(7+states)))))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table
              (Source284JoinedFrames.table (table continuation)))))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
              ((2*(Source284RawParse.payload input.bits).length+6)+
                ((joinedBits (Source284RawParse.payload input.bits) w).length+fuel)))))) =
      Source284SourceRelocation.lift 789 (Source284Relative.run (encode states continuation 1)
        ⟨2*(2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)),
          payloadFold (2*(inputSuffix/4)+1)
            (joinedBody (Source284RawParse.payload input.bits) w),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284JoinedFrames.decoded_join_then
    (7+states) (table continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let left := 2*(is/4)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let t := (joinedBits x w).length
  have hr' := hr (t+fuel)
  let c : Config := ⟨left,stack (joinedBits x w) tail,some 0⟩
  have hc : Valid (7+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (7+states) (table continuation) 1 c
    (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (7+states) (table continuation) 1)
    ⟨left,stack (joinedBits x w) tail,active 0⟩ (t+fuel) = _ at hv0
  have hp := scan_then continuation x w left tail fuel
  change run (table continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨2*tail,payloadFold left (joinedBody x w),some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨2*tail,payloadFold left (joinedBody x w),active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

theorem decoded_scan_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
          ((2*(Source284RawParse.payload input.bits).length+6)+
            (joinedBits (Source284RawParse.payload input.bits) w).length)))) ≤
      24*limit*limit+156*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        32*Source284Parser.length input+252 := by
  have h0 := Source284JoinedFrames.decoded_join_bound limit certificate input w hdec
  have hw := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have hx : (Source284RawParse.payload input.bits).length = Source284Parser.length input := by
    have h := Source284RawParse.parse_length input.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  rw [Source284JoinedFrames.joined_length,hx]
  omega

namespace Fixtures
example (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,stack (joinedBits [] []) tail,some 0⟩ 6 =
      ⟨2*tail,payloadFold left (joinedBody [] []),some 7⟩ := by
  simpa [Source284JoinedFrames.joined_length] using scan continuation [] [] left tail
example (continuation : Nat → Bool → Row) (left tail : Nat) :
    run (table continuation) ⟨left,stack (joinedBits [false,true] [true,false]) tail,some 0⟩ 14 =
      ⟨2*tail,payloadFold left (joinedBody [false,true] [true,false]),some 7⟩ := by
  simpa [Source284JoinedFrames.joined_length] using scan continuation [false,true] [true,false] left tail
end Fixtures

end Shared.Beeping.NPcoNP.Source284JoinedPrefixScan
