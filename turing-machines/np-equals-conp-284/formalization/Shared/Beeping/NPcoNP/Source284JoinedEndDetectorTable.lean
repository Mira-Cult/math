import Shared.Beeping.NPcoNP.Source284JoinedEndDetector

/-! A finite relative source table implements the joined-body end detector.
It advances one real transition per inspected bit, retains both tape tails,
and hands off only after the final delimiter. This stand-alone scan moves the
head; an interleaved product with the tagged serializer remains separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable

open Shared.Beeping.NPcoNP.Source284JoinedEndDetector
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (stack)
open Shared.Beeping.NPcoNP.Source284Parser (payloadFold)

def index : State → Nat
  | .lead => 0 | .witnessData => 1 | .witnessZeroMarker => 2
  | .witnessOneMarker => 3 | .gap => 4 | .inputMarker => 5
  | .inputData => 6 | .bad => 7 | .done => 8

/-- Eight detector states; state eight is the relocated continuation. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some (if b then 7 else 1)⟩
  else if q = 1 then ⟨b,false,some (if b then 3 else 2)⟩
  else if q = 2 then ⟨b,false,some (if b then 1 else 4)⟩
  else if q = 3 then ⟨b,false,some (if b then 1 else 7)⟩
  else if q = 4 then ⟨b,false,some (if b then 7 else 5)⟩
  else if q = 5 then ⟨b,false,some (if b then 6 else 8)⟩
  else if q = 6 then ⟨b,false,some 5⟩
  else if q = 7 then ⟨b,false,some 7⟩
  else shiftRow 8 (continuation (q-8) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (8+states) (table continuation) := by
  intro q hq b q' hnext
  by_cases hs : q < 8
  · interval_cases q <;> cases b <;> simp [table] at hnext <;> omega
  · have ht : (shiftRow 8 (continuation (q-8) b)).next = some q' := by
      simpa [table,show q ≠ 0 by omega,show q ≠ 1 by omega,show q ≠ 2 by omega,
        show q ≠ 3 by omega,show q ≠ 4 by omega,show q ≠ 5 by omega,
        show q ≠ 6 by omega,show q ≠ 7 by omega] using hnext
    cases he : (continuation (q-8) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hv (q-8) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

/-- Each active detector state reads and transfers exactly one bit. -/
theorem detector_step (continuation : Nat → Bool → Row) (q : State)
    (hq : q ≠ .done) (b : Bool) (left tail : Nat) :
    Source284TableRun.step (table continuation) ⟨left,2*tail+bit b,some (index q)⟩ =
      ⟨2*left+bit b,tail,some (index (Source284JoinedEndDetector.step q b))⟩ := by
  cases q <;> cases b <;> simp_all [index,table,Source284TableRun.step,
    Source284JoinedEndDetector.step,bit,Nat.testBit_zero,Nat.add_mod] <;> omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (8+q) b = shiftRow 8 (continuation q b) := by
  simp [table,show 8+q ≠ 1 by omega,show 8+q ≠ 2 by omega,show 8+q ≠ 3 by omega,
    show 8+q ≠ 4 by omega,show 8+q ≠ 5 by omega,show 8+q ≠ 6 by omega,show 8+q ≠ 7 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    Source284TableRun.step (table continuation) (shiftConfig 8 c) =
      shiftConfig 8 (Source284TableRun.step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,Source284TableRun.step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 8 c) fuel = shiftConfig 8 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- If the executable detector returns a suffix, the actual finite table
performs exactly that many steps and leaves precisely that suffix under the
head. The traversed bits are transferred to the opposite tape half. -/
theorem scan_run (continuation : Nat → Bool → Row) (q : State) (bits suffix : List Bool)
    (n left tail : Nat) (h : scan q bits = some (n,suffix)) :
    run (table continuation) ⟨left,stack bits tail,some (index q)⟩ n =
      ⟨payloadFold left (bits.take n),stack suffix tail,some 8⟩ := by
  induction bits generalizing q n suffix left with
  | nil =>
    cases q <;> simp [scan] at h
    case done => rcases h with ⟨rfl,rfl⟩; rfl
  | cons b bs ih =>
    cases q with
    | done =>
      simp [scan] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | bad => simp [scan] at h
    | lead | witnessData | witnessZeroMarker | witnessOneMarker | gap | inputMarker | inputData =>
      simp only [scan] at h
      obtain ⟨⟨j,rest⟩,hs,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl⟩
      rw [run_front]
      rw [show stack (b::bs) tail = 2*stack bs tail+bit b by cases b <;> simp [stack,bit]]
      rw [detector_step _ _ (by decide)]
      have hh := ih _ _ _ (2*left+bit b) hs
      simpa [List.take_succ_cons,payloadFold,bit] using hh

/-- On actual joined bodies, the detector always reaches its continuation
in exactly the body's length, before inspecting any high suffix. -/
theorem detect_body (continuation : Nat → Bool → Row) (x w extra : List Bool) (left tail : Nat) :
    run (table continuation)
      ⟨left,stack ((Source284JoinedPrefixScan.joinedBody x w).reverse++extra) tail,some 0⟩
      (Source284JoinedPrefixScan.joinedBody x w).length =
      ⟨payloadFold left (Source284JoinedPrefixScan.joinedBody x w).reverse,
        stack extra tail,some 8⟩ := by
  have h := scan_run continuation .lead _ extra _ left tail (scan_body x w extra)
  have ht : ((Source284JoinedPrefixScan.joinedBody x w).reverse++extra).take
      (Source284JoinedPrefixScan.joinedBody x w).length =
        (Source284JoinedPrefixScan.joinedBody x w).reverse := by simp
  simpa only [index,ht] using h

/-- The detector's explicit pass is followed by every continuation step. -/
theorem detect_body_then (continuation : Nat → Bool → Row) (x w extra : List Bool)
    (left tail fuel : Nat) :
    run (table continuation)
      ⟨left,stack ((Source284JoinedPrefixScan.joinedBody x w).reverse++extra) tail,some 0⟩
      ((Source284JoinedPrefixScan.joinedBody x w).length+fuel) =
    shiftConfig 8 (run continuation
      ⟨payloadFold left (Source284JoinedPrefixScan.joinedBody x w).reverse,
        stack extra tail,some 0⟩ fuel) := by
  rw [Source284HardwireCorrect.run_add,detect_body]
  change run (table continuation) (shiftConfig 8
    ⟨payloadFold left (Source284JoinedPrefixScan.joinedBody x w).reverse,stack extra tail,some 0⟩) fuel = _
  rw [relocated_run]

theorem shift_add (a b : Nat) (c : Config) :
    shiftConfig a (shiftConfig b c) = shiftConfig (a+b) c := by
  cases c with
  | mk left right state => cases state <;> simp [shiftConfig,Nat.add_assoc]

/-- The original joined-prefix scan and this detector are one finite table;
the second pass reads exactly the exposed reversed body. -/
theorem joined_scan_then_detect (continuation : Nat → Bool → Row) (x w : List Bool)
    (left tail fuel : Nat) :
    run (Source284JoinedPrefixScan.table (table continuation))
      ⟨left,stack (Source284JoinedFrames.joinedBits x w) tail,some 0⟩
      ((Source284JoinedFrames.joinedBits x w).length+
        ((Source284JoinedPrefixScan.joinedBody x w).length+fuel)) =
    shiftConfig (7+8) (run continuation
      ⟨payloadFold (2*tail) (Source284JoinedPrefixScan.joinedBody x w).reverse,left,some 0⟩ fuel) := by
  rw [Source284JoinedPrefixScan.scan_then,Source284LoaderAlgebra.pushed_eq_stack]
  have hd := detect_body_then continuation x w [] (2*tail) left fuel
  simp only [List.append_nil,stack] at hd
  rw [hd,shift_add]

/-- The decoded source reaches the same end-detection boundary and follows
every later continuation step. This is a paid stand-alone scan, not yet the
serializer/detector product. -/
theorem decoded_detect_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*Source284Parser.encodeFrame w witnessSuffix ∧
      input = Source284Parser.encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(160+(68+(16+(7+(8+states))))))))))
          (Source284BothFrames.table (Source284WitnessSeek.table
            (Source284WitnessCompact.table (Source284ScratchNormalize.table
              (Source284JoinedFrames.table (Source284JoinedPrefixScan.table (table continuation))))))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
              ((2*(Source284RawParse.payload input.bits).length+6)+
                ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
                  ((Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).length+fuel))))))) =
      Source284SourceRelocation.lift 797 (Source284Relative.run (encode states continuation 1)
        ⟨payloadFold (2*(2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)))
            (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).reverse,
          2*(inputSuffix/4)+1,active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284JoinedPrefixScan.decoded_scan_then
    (8+states) (table continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let left := 2*(is/4)+1
  let tail := 2^(2*((limit+1)+1))*((8*((ws/4)/4)+1)/4)
  let t := (Source284JoinedPrefixScan.joinedBody x w).length
  have hr' := hr (t+fuel)
  let c : Config := ⟨2*tail,payloadFold left (Source284JoinedPrefixScan.joinedBody x w),some 0⟩
  have hc : Valid (8+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hv0 := run_toSource (8+states) (table continuation) 1 c
    (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (8+states) (table continuation) 1)
    ⟨2*tail,payloadFold left (Source284JoinedPrefixScan.joinedBody x w),active 0⟩ (t+fuel) = _ at hv0
  have hp := detect_body_then continuation x w [] (2*tail) left fuel
  simp only [List.append_nil,stack] at hp
  rw [← Source284LoaderAlgebra.pushed_eq_stack (Source284JoinedPrefixScan.joinedBody x w) left] at hp
  change run (table continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨payloadFold (2*tail) (Source284JoinedPrefixScan.joinedBody x w).reverse,left,some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨payloadFold (2*tail) (Source284JoinedPrefixScan.joinedBody x w).reverse,left,active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The entire decoded path through this detector has a quadratic bound in
the witness limit and the parsed input length. -/
theorem decoded_detect_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        (Source284WitnessCompact.extraCost (limit+1) w.length+((6*w.length+11)+
          ((2*(Source284RawParse.payload input.bits).length+6)+
            ((Source284JoinedFrames.joinedBits (Source284RawParse.payload input.bits) w).length+
              (Source284JoinedPrefixScan.joinedBody (Source284RawParse.payload input.bits) w).length))))) ≤
      24*limit*limit+158*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        34*Source284Parser.length input+257 := by
  have h0 := Source284JoinedPrefixScan.decoded_scan_bound limit certificate input w hdec
  have hw := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have hx : (Source284RawParse.payload input.bits).length = Source284Parser.length input := by
    have h := Source284RawParse.parse_length input.bits
    rw [Shared.Codes.BinaryAdditionCanonical.value_bits] at h
    exact h.symm
  have hb := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body (Source284RawParse.payload input.bits) w)
  simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at hb
  omega

namespace Fixtures
def loop (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩
example : run (table loop)
    ⟨9,stack ((Source284JoinedPrefixScan.joinedBody [] []).reverse++[true,false]) 7,some 0⟩ 5 =
    ⟨payloadFold 9 (Source284JoinedPrefixScan.joinedBody [] []).reverse,stack [true,false] 7,some 8⟩ :=
  detect_body loop [] [] [true,false] 9 7
end Fixtures

end Shared.Beeping.NPcoNP.Source284JoinedEndDetectorTable
