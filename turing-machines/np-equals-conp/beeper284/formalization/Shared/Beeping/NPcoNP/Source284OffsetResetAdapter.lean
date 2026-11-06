import Shared.Beeping.NPcoNP.Source284OffsetDecodedHandoff
import Shared.Beeping.NPcoNP.Source284MatchReset

/-! A finite, paid adapter clears the comparator's token and witness marks
before continuing. It retains the high suffix and the extra tag pair. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284OffsetResetAdapter

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlipReturn (run_add)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PayloadMarkOne (zeros)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource shiftConfig_add)

/-- One turn restores comparator orientation before the existing 18-state
reset, then the supplied finite continuation follows. -/
def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else shiftRow 1 (Source284MatchReset.table continuation (q-1) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (19+states) (table continuation) := by
  have hr := Source284MatchReset.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · have ht : (shiftRow 1 (Source284MatchReset.table continuation (q-1) b)).next = some q' := by
      simpa [table,h0] using hnext
    cases he : (Source284MatchReset.table continuation (q-1) b).next with
    | none => simp [shiftRow,he] at ht
    | some r =>
      have h := hr (q-1) (by omega) b r he
      simp [shiftRow,he] at ht
      subst q'; omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (1+q) b = shiftRow 1 (Source284MatchReset.table continuation q b) := by
  simp [table]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 1 c) =
      shiftConfig 1 (step (Source284MatchReset.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 1 c) fuel =
      shiftConfig 1 (run (Source284MatchReset.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

/-- A single paid turn and the existing finite reset restore all token and
payload markers, without deleting the high suffix. -/
theorem reset (continuation : Nat → Bool → Row) (tokens w : List Bool)
    (certificate tail : Nat) :
    run (table continuation)
      ⟨2*zeros w (flipped [false] tail),pairTape tokens certificate,some 0⟩
      (1+((4*tokens.length+6)+(4*w.length+12))) =
    ⟨pairTape (List.replicate tokens.length false) certificate,
      2*flipped (w++[false]) tail,some 19⟩ := by
  rw [run_add]
  have ht : step (table continuation)
      ⟨2*zeros w (flipped [false] tail),pairTape tokens certificate,some 0⟩ =
      ⟨pairTape tokens certificate,2*zeros w (flipped [false] tail),some 1⟩ := by
    apply Source284WindowRewind.generic_turn
    intro b; simp [table]
  change run (table continuation) (step (table continuation)
    ⟨2*zeros w (flipped [false] tail),pairTape tokens certificate,some 0⟩) _ = _
  rw [ht]
  change run (table continuation) (shiftConfig 1
    ⟨pairTape tokens certificate,2*zeros w (flipped [false] tail),some 0⟩) _ = _
  rw [relocated_run]
  have hr := Source284MatchReset.reset continuation tokens w [] certificate tail
  simp only [List.length_nil,Nat.add_zero,List.nil_append,List.append_nil] at hr
  rw [hr]
  rfl

/-- All bound-token cases have exactly one tag pair plus the original
unary bound, regardless of whether the witness reaches the bound. -/
theorem boundTokens_length (limit : Nat) (w : List Bool) (hw : w.length ≤ limit) :
    (Source284OffsetExactHandoff.boundTokens limit w).length = limit+1 := by
  unfold Source284OffsetExactHandoff.boundTokens
  split <;> simp_all <;> omega

/-- After reset, every later transition is that of the supplied continuation,
with the 19-state relocation explicitly charged. -/
theorem reset_then (continuation : Nat → Bool → Row) (tokens w : List Bool)
    (certificate tail fuel : Nat) :
    run (table continuation)
      ⟨2*zeros w (flipped [false] tail),pairTape tokens certificate,some 0⟩
      ((1+((4*tokens.length+6)+(4*w.length+12)))+fuel) =
    shiftConfig 19 (run continuation
      ⟨pairTape (List.replicate tokens.length false) certificate,
        2*flipped (w++[false]) tail,some 0⟩ fuel) := by
  rw [run_add,reset]
  let c : Config := ⟨pairTape (List.replicate tokens.length false) certificate,
    2*flipped (w++[false]) tail,some 0⟩
  change run (table continuation) (shiftConfig 1 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6 c)))) fuel = _
  rw [relocated_run]
  unfold Source284MatchReset.table
  rw [Source284UnaryClear.relocated_run,Source284PayloadReset.relocated_run,
    Source284ScratchFlipReturn.relocated_run]
  rw [shiftConfig_add,shiftConfig_add,shiftConfig_add]

/-- For every valid tagged certificate, the concrete finite adapter clears
both kinds of marks and then executes the supplied finite continuation. The
remaining suffix and the extra unary tag pair are explicit. -/
theorem decoded_reset_then (states : Nat) (continuation : Nat → Bool → Row)
    (limit certificate otherHalf : Nat) (w : List Bool)
    (hn : 0 < states) (hv : Closed states continuation)
    (hdec : Source284TaggedWitnessCodec.decode limit certificate = some w) :
    ∃ suffix, certificate = 4*encodeFrame w suffix ∧
      ∀ fuel, Source284Relative.run (Source284OffsetTagged.description (19+states) (table continuation))
        (Source284Relative.initial certificate (pairTape (List.replicate limit false) otherHalf))
        (4+(Source284PayloadSentinelPipeline.totalCost w.length+
          (Source284OffsetMatch.compareCost w.length+(1+
            ((1+((4*(limit+1)+6)+(4*w.length+12)))+fuel))))) =
      lift 231 (Source284Relative.run (encode states continuation 1)
        ⟨pairTape (List.replicate (limit+1) false) otherHalf,
          2*flipped (w++[false]) ((suffix/4)/4),active 0⟩ fuel) := by
  have hw := Source284TaggedWitnessCodec.decode_length limit certificate w hdec
  obtain ⟨suffix,hcert,hr⟩ := Source284OffsetDecodedHandoff.decoded_verifier_exact
    (19+states) (table continuation) limit certificate otherHalf w (by omega) (closed states continuation hn hv) hdec
  refine ⟨suffix,hcert,?_⟩
  intro fuel
  let tokens := Source284OffsetExactHandoff.boundTokens limit w
  let tail := (suffix/4)/4
  let rtime := 1+((4*(limit+1)+6)+(4*w.length+12))
  have hlen : tokens.length = limit+1 := boundTokens_length limit w hw
  have hrun := hr (rtime+fuel)
  change Source284Relative.run _ _ _ = lift 212
    (Source284Relative.run (encode (19+states) (table continuation) 1)
      ⟨2*zeros w (flipped [false] tail),pairTape tokens otherHalf,active 0⟩ (rtime+fuel)) at hrun
  let c : Config := ⟨2*zeros w (flipped [false] tail),pairTape tokens otherHalf,some 0⟩
  have hc : Valid (19+states) c := by intro q hq; simp [c] at hq; subst q; omega
  have hc0 := run_toSource (19+states) (table continuation) 1 c (closed states continuation hn hv) hc (rtime+fuel)
  change Source284Relative.run (encode (19+states) (table continuation) 1)
    ⟨2*zeros w (flipped [false] tail),pairTape tokens otherHalf,active 0⟩ (rtime+fuel) = _ at hc0
  rw [hc0] at hrun
  have ht : rtime = 1+((4*tokens.length+6)+(4*w.length+12)) := by simp [rtime,hlen]
  rw [ht,reset_then] at hrun
  let c' : Config := ⟨pairTape (List.replicate (limit+1) false) otherHalf,
    2*flipped (w++[false]) tail,some 0⟩
  have hc' : Valid states c' := by intro q hq; simp [c'] at hq; subst q; exact hn
  have hc1 := run_toSource states continuation 1 c' hv hc' fuel
  change Source284Relative.run (encode states continuation 1)
    ⟨pairTape (List.replicate (limit+1) false) otherHalf,
      2*flipped (w++[false]) tail,active 0⟩ fuel = _ at hc1
  simp only [hlen] at hrun
  rw [← lift_toSource,Source284SourceRelocation.lift_add,← hc1] at hrun
  exact hrun

namespace Fixtures

example : Source284OffsetExactHandoff.boundTokens 0 [] = [true] := by decide +kernel
example : Source284OffsetExactHandoff.boundTokens 4 [false] =
    [true,true,true,false,false] := by decide +kernel

/-- Empty witness and zero original bound still require the paid tag-pair
reset; the continuation is reached in 23 transitions. -/
example : run (table Source284PreparedCutoff.Fixtures.acceptImmediately)
    ⟨4,pairTape [true] 0,some 0⟩ 23 = ⟨pairTape [false] 0,4,some 19⟩ := by
  simpa [zeros,flipped,bit] using reset Source284PreparedCutoff.Fixtures.acceptImmediately [true] [] 0 0

end Fixtures

end Shared.Beeping.NPcoNP.Source284OffsetResetAdapter
