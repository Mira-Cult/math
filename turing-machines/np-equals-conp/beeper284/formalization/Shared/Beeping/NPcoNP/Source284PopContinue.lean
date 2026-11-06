import Shared.Beeping.NPcoNP.Source284PayloadPop
import Shared.Beeping.NPcoNP.Source284WitnessScratch

/-! Exact continuation form of the checked last-payload pop. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PopContinue

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def table (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  Source284InputSentinel.table (Source284ModePrefixScan.table (Source284PayloadPop.table continuation))

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (68+states) (table continuation) := by
  have h0 := Source284PayloadPop.closed states continuation hn hv
  have h1 := Source284ModePrefixScan.closed (20+(32+states)) (Source284PayloadPop.table continuation) (by omega) h0
  have h2 := Source284InputSentinel.closed (8+(20+(32+states)))
    (Source284ModePrefixScan.table (Source284PayloadPop.table continuation)) (by omega) h1
  change Closed (8+(8+(20+(32+states)))) (table continuation) at h2
  convert h2 using 1 <;> omega

theorem pop (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (b : Bool) (certificate suffix : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩
      (4*(xs++[b]).length+12) =
    ⟨certificate,encodeFrame xs (4*suffix+bit b),some 68⟩ := by
  apply Source284WitnessScratch.toSource_injective
  have hc : Valid (68+states) ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩ := by
    intro q hq; simp at hq; subst q; omega
  have hr := run_toSource (68+states) (table continuation) 1
    ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩ (closed states continuation hn hv) hc
    (4*(xs++[b]).length+12)
  have hp := Source284PayloadPop.source_pop states continuation xs b certificate suffix hn hv
  unfold Source284InputSentinel.description at hp
  have hs : 8+(8+(20+(32+states)))=68+states := by omega
  rw [hs] at hp
  change Source284Relative.run (encode (68+states) (table continuation) 1)
    (toSource ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩) _ = _ at hp
  rw [hr] at hp
  exact hp

theorem after (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 68 c) fuel = shiftConfig 68 (run continuation c fuel) := by
  have he : shiftConfig 68 c = shiftConfig 8 (shiftConfig 8 (shiftConfig 20 (shiftConfig 32 c))) := by
    repeat rw [Source284SourceRelocation.shiftConfig_add]
  rw [he]
  unfold table
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284PayloadPop.relocated_run,Source284ModePrefixReturn.relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

theorem pop_then (states : Nat) (continuation : Nat → Bool → Row)
    (xs : List Bool) (b : Bool) (certificate suffix fuel : Nat)
    (hn : 0 < states) (hv : Closed states continuation) :
    run (table continuation) ⟨certificate,encodeFrame (xs++[b]) suffix,some 0⟩
      ((4*(xs++[b]).length+12)+fuel) =
    shiftConfig 68 (run continuation
      ⟨certificate,encodeFrame xs (4*suffix+bit b),some 0⟩ fuel) := by
  rw [Source284ScratchScanner.run_add,pop states continuation xs b certificate suffix hn hv]
  change run (table continuation)
    (shiftConfig 68 ⟨certificate,encodeFrame xs (4*suffix+bit b),some 0⟩) fuel = _
  exact after continuation _ fuel

end Shared.Beeping.NPcoNP.Source284PopContinue
