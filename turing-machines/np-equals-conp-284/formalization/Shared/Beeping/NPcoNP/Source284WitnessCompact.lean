import Shared.Beeping.NPcoNP.Source284WitnessScratch
import Shared.Beeping.NPcoNP.Source284ScratchCompactLoop

/-! The actual decoded-witness source path packs and flips the entire witness,
then autonomously removes the separating zero gap. The input and the witness
stream become adjacent at the existing sentinel. The verifier pair encoding
and the physical 284-state refinement are still separate obligations. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284WitnessCompact

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped push)

def engine (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284ScratchFlip.table (Source284ScratchFlipReturn.table
    (Source284ScratchCompactLoop.table continuation))

theorem engine_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (23+states) (engine continuation) := by
  have h0 := Source284ScratchCompactLoop.closed states continuation hn hv
  have h1 := Source284ScratchFlipReturn.closed (14+states) (Source284ScratchCompactLoop.table continuation) (by omega) h0
  have h2 := Source284ScratchFlip.closed (6+(14+states))
    (Source284ScratchFlipReturn.table (Source284ScratchCompactLoop.table continuation)) (by omega) h1
  change Closed (3+(6+(14+states))) (engine continuation) at h2
  convert h2 using 1 <;> omega

def extraCost (gap n : Nat) : Nat :=
  (2+Source284ScratchPack.totalCost n)+((2*n+3)+((2*n+5)+(2*(gap+1))*(8*n+11)))

/-- Starting at the witness seek boundary, a single finite table packs,
flips, and compacts all the way to the actual one sentinel. No gap size is
provided to the table as a runtime oracle. -/
theorem compact_after_seek (states : Nat) (continuation : Nat → Bool → Row)
    (gap inputFrame suffix : Nat) (w : List Bool) (fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (Source284WitnessScratch.entry (engine continuation))
      ⟨4^(gap+1)*(4*inputFrame+1),encodeFrame w suffix,some (if w = [] then 1 else 0)⟩
      (extraCost gap w.length+fuel) =
    shiftConfig 160 (run continuation
      ⟨4*inputFrame+1,2*flipped w (2^(2*(gap+1))*(suffix/4)),some 0⟩ fuel) := by
  let left := 4^(gap+1)*(4*inputFrame+1)
  let a := 2+Source284ScratchPack.totalCost w.length
  let b := 2*w.length+3
  let c := 2*w.length+5
  let d := (2*(gap+1))*(8*w.length+11)
  have hp := Source284WitnessScratch.pack_then (23+states) (engine continuation) w left suffix
    (b+(c+(d+fuel))) (by omega) (engine_closed states continuation hn hv)
  have ht : extraCost gap w.length+fuel = a+(b+(c+(d+fuel))) := by
    dsimp [extraCost,a,b,c,d]; omega
  rw [ht]
  change run (Source284WitnessScratch.entry (engine continuation))
    ⟨left,encodeFrame w suffix,some (if w = [] then 1 else 0)⟩ _ = _
  rw [hp,run_add]
  dsimp only [engine,Source284Parser.encodeFrame,b]
  rw [Source284ScratchFlip.scan_initial]
  change shiftConfig 137 (run (Source284ScratchFlip.table
    (Source284ScratchFlipReturn.table (Source284ScratchCompactLoop.table continuation)))
    (shiftConfig 3 ⟨4*push (2*left) w,suffix/4,some 0⟩) _) = _
  rw [Source284ScratchFlip.relocated_run,run_add,Source284ScratchFlipReturn.return_frame]
  change shiftConfig 137 (shiftConfig 3 (run (Source284ScratchFlipReturn.table
    (Source284ScratchCompactLoop.table continuation))
    (shiftConfig 6 ⟨left,2*flipped w (suffix/4),some 0⟩) _)) = _
  rw [Source284ScratchFlipReturn.relocated_run]
  have hp4 : 4^(gap+1) = 2^(2*(gap+1)) := by rw [Nat.pow_mul]
  have hk : 2*gap+1+1 = 2*(gap+1) := by omega
  have hl : left = 2^(2*gap+1+1)*(2*(2*inputFrame)+1) := by
    dsimp [left]; rw [hk,← hp4]; congr 1 <;> ring
  have hd : d = (2*gap+1+1)*(8*w.length+11) := by dsimp [d]; ring
  rw [hl,hd,Source284ScratchCompactLoop.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  congr 3 <;> simp [hk]
  all_goals omega

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284WitnessScratch.entry (engine continuation)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (160+states) (table continuation) := by
  have h := Source284WitnessScratch.closed (23+states) (engine continuation) (by omega)
    (engine_closed states continuation hn hv)
  change Closed (137+(23+states)) (table continuation) at h
  convert h using 1 <;> omega

/-- The original valid tagged certificate is decoded and its entire witness
is packed next to the parsed input sentinel. Every source step, including the
sentinel-controlled gap removal, is charged; subsequent execution agrees at
every clock. This is not yet the canonical pair serialization. -/
theorem decoded_compact_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate input : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ witnessSuffix inputSuffix,
      certificate = 4*encodeFrame w witnessSuffix ∧
      input = encodeFrame (Source284RawParse.payload input.bits) inputSuffix ∧
      ∀ fuel, Source284Relative.run
        (Source284OffsetTagged.description (19+(80+(7+(210+(10+(160+states))))))
          (Source284BothFrames.table (Source284WitnessSeek.table (table continuation))))
        (Source284Relative.initial certificate
          (Source284UnaryPairScanner.pairTape (List.replicate limit false) input))
        (Source284BothFrames.time limit w input+
          ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
            (extraCost (limit+1) w.length+fuel))) =
      Source284SourceRelocation.lift 698 (Source284Relative.run (encode states continuation 1)
        ⟨4*encodeFrame (Source284RawParse.payload input.bits) (2*(inputSuffix/4)+1)+1,
          2*flipped w (2^(2*((limit+1)+1))*((8*((witnessSuffix/4)/4)+1)/4)),active 0⟩ fuel) := by
  obtain ⟨ws,is,hcert,hinput,hr⟩ := Source284WitnessSeek.decoded_seek_then
    (160+states) (table continuation) limit certificate input w (by omega)
      (closed states continuation hn hv) hdec
  refine ⟨ws,is,hcert,hinput,?_⟩
  intro fuel
  let x := Source284RawParse.payload input.bits
  let inputFrame := encodeFrame x (2*(is/4)+1)
  let suffix := 8*((ws/4)/4)+1
  let t := extraCost (limit+1) w.length
  have hr' := hr (t+fuel)
  change Source284Relative.run _ _ _ = Source284SourceRelocation.lift 538
    (Source284Relative.run (encode (160+states) (table continuation) 1)
      ⟨4^((limit+1)+1)*(4*inputFrame+1),encodeFrame w suffix,
        active (if w = [] then 1 else 0)⟩ (t+fuel)) at hr'
  let c : Config := ⟨4^((limit+1)+1)*(4*inputFrame+1),encodeFrame w suffix,
    some (if w = [] then 1 else 0)⟩
  have hc : Valid (160+states) c := by
    intro q hq; simp [c] at hq; subst q; split <;> omega
  have hv0 := run_toSource (160+states) (table continuation) 1 c (closed states continuation hn hv) hc (t+fuel)
  change Source284Relative.run (encode (160+states) (table continuation) 1)
    ⟨4^((limit+1)+1)*(4*inputFrame+1),encodeFrame w suffix,
      active (if w = [] then 1 else 0)⟩ (t+fuel) = _ at hv0
  have hp := compact_after_seek states continuation (limit+1) inputFrame suffix w fuel hn hv
  change run (table continuation) c (t+fuel) = _ at hp
  rw [hv0,hp] at hr'
  let c' : Config := ⟨4*inputFrame+1,2*flipped w (2^(2*((limit+1)+1))*(suffix/4)),some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hv1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨4*inputFrame+1,2*flipped w (2^(2*((limit+1)+1))*(suffix/4)),active 0⟩ fuel = _ at hv1
  rw [← Source284SourceRelocation.lift_toSource,Source284SourceRelocation.lift_add,← hv1] at hr'
  exact hr'

/-- The complete valid-certificate preparation and gap compaction are bounded
by a fixed quadratic in the original cutoff and parsed input length. -/
theorem decoded_compact_bound (limit certificate input : Nat) (w : List Bool)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    Source284BothFrames.time limit w input+
      ((3+2*((limit+1)+1)+(if w = [] then 4 else 2))+
        extraCost (limit+1) w.length) ≤
      24*limit*limit+148*limit+
        2*Source284Parser.length input*Source284Parser.length input+
        28*Source284Parser.length input+229 := by
  have h0 := Source284BothFramesContinue.decoded_time_bound limit certificate input w hdec
  have h1 := Source284WitnessSeek.seek_time_bound limit w
  have h2 := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  have h3 : w.length*w.length ≤ limit*limit := Nat.mul_self_le_mul_self h2
  have h4 : (2*((limit+1)+1))*(8*w.length+11) ≤
      (2*((limit+1)+1))*(8*limit+11) := Nat.mul_le_mul_left _ (by omega)
  unfold extraCost
  rw [Source284ScratchPack.totalCost_formula]
  nlinarith

end Shared.Beeping.NPcoNP.Source284WitnessCompact
