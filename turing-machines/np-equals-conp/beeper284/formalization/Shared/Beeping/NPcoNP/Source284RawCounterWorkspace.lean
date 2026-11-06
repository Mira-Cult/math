import Shared.Beeping.NPcoNP.Source284TokenCounterContinue

/-! The raw framed input is packed and seeded before the same encoded source
program consumes a separately prepared unary token tape. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284RawCounterWorkspace

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284CountedShift (counter)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)

/-- The full description includes the packer, seed, token loop and continuation. -/
def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284ScratchCounterSeed.description (32+states)
    (Source284TokenCounterLoop.table continuation)

def cost (m k width : Nat) : Nat :=
  Source284ScratchCounterSeed.totalCost width +
    Source284TokenCounterLoop.consumeTime m k 0 width

/-- Packing, seeding and autonomous consumption are one finite source run.
The opposite tape half is explicitly required to contain the prepared tokens. -/
theorem source_workspace (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (m k certificate suffix : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix)
        (pairTape (List.replicate k true ++ List.replicate m false) certificate))
      (cost m k w.length) =
      ⟨pairTape (List.replicate (k+m) true) certificate,
        2*flipped w (counter m (Source284TokenCounterLoop.halves m ((suffix/4)/2))),
        active 182⟩ := by
  have hc := Source284TokenCounterLoop.closed states continuation hn hv
  have hs := Source284ScratchCounterSeed.source_pack_seed_then (32+states)
    (Source284TokenCounterLoop.table continuation) w
    (pairTape (List.replicate k true ++ List.replicate m false) certificate) suffix
    (Source284TokenCounterLoop.consumeTime m k 0 w.length) (by omega) hc
  have hl := Source284TokenCounterLoop.source_consume states continuation m k w 0 certificate
    ((suffix/4)/2) hn hv
  change Source284Relative.run (encode (32+states) (Source284TokenCounterLoop.table continuation) 1)
    ⟨pairTape (List.replicate k true ++ List.replicate m false) certificate,
      2*flipped w (counter 0 ((suffix/4)/2)),active 0⟩ _ = _ at hl
  rw [hl] at hs
  simpa [description,cost,Source284SourceRelocation.lift,active] using hs

theorem cost_formula (m k width : Nat) :
    cost m k width = 2*width*width+22*width+30+
      (3*m*m + m*(4*k+4*width+25)+4*k+8) := by
  rw [cost,Source284ScratchCounterSeed.totalCost_formula,Source284TokenCounterLoop.consumeTime_formula]
  ring

/-- Every raw numeric input is covered; the token tape is still a separately
prepared argument and is not manufactured by this theorem. -/
theorem source_total_workspace (states : Nat) (continuation : Nat → Bool → Row)
    (input m k certificate : Nat) (hn : 2 ≤ states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description states continuation)
        (Source284Relative.initial input
          (pairTape (List.replicate k true ++ List.replicate m false) certificate))
        (cost m k (Source284Parser.length input)) =
      ⟨pairTape (List.replicate (k+m) true) certificate,
        2*flipped w (counter m (Source284TokenCounterLoop.halves m ((suffix/4)/2))),
        active 182⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,hw,hlen.symm,?_⟩
  rw [hlen,← hw]
  exact source_workspace states continuation w m k certificate suffix hn hv

/-- Any continuation state, including the exhaustion entry, is simulated in
the same source table with both tape halves and acceptance preserved. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row)
    (mode left right clock : Nat) (hn : 2 ≤ states) (hm : mode < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨left,right,active (181+mode)⟩ clock =
      toSource (Shared.Beeping.NPcoNP.Source284HardwireTable.shiftConfig 181
        (run continuation ⟨left,right,some mode⟩ clock)) := by
  let c : Config := ⟨left,right,some mode⟩
  let sh := Shared.Beeping.NPcoNP.Source284HardwireTable.shiftConfig
  have hc : Valid (133+(16+(32+states)))
      (sh 8 (sh 8 (sh 16 (sh 32 (sh 69 (sh 16 (sh 32 c))))))) := by
    intro q hq
    simp [sh,Shared.Beeping.NPcoNP.Source284HardwireTable.shiftConfig,c] at hq
    subst q
    omega
  have hloop := Source284TokenCounterLoop.closed states continuation hn hv
  have hseed := Source284ScratchCounterSeed.closed (32+states)
    (Source284TokenCounterLoop.table continuation) (by omega) hloop
  have hr := run_toSource (133+(16+(32+states)))
    (Source284ScratchPack.table (Source284ScratchCounterSeed.table
      (Source284TokenCounterLoop.table continuation))) 1
    (sh 8 (sh 8 (sh 16 (sh 32 (sh 69 (sh 16 (sh 32 c)))))))
    (Source284ScratchPack.closed (16+(32+states))
      (Source284ScratchCounterSeed.table (Source284TokenCounterLoop.table continuation))
      (by omega) hseed) hc clock
  have hsource : toSource (sh 8 (sh 8 (sh 16 (sh 32 (sh 69 (sh 16 (sh 32 c))))))) =
      ⟨left,right,active (181+mode)⟩ := by
    simp [sh,Shared.Beeping.NPcoNP.Source284HardwireTable.shiftConfig,c,toSource,nextState,active]
    omega
  rw [hsource] at hr
  change Source284Relative.run (description states continuation)
    ⟨left,right,active (181+mode)⟩ clock = _ at hr
  rw [hr]
  change toSource (run (Source284InputSentinel.table
    (Source284ModePrefixScan.table (Source284ScratchTerminator.table
      (Source284PayloadLoop.table (Source284ScratchCounterSeed.table
        (Source284TokenCounterLoop.table continuation))))))
    (sh 8 (sh 8 (sh 16 (sh 32 (sh 69 (sh 16 (sh 32 c))))))) clock) = _
  rw [Source284InputSentinel.relocated_run,Source284ModePrefixScan.relocated_run,
    Source284ScratchTerminator.relocated_run,Source284ModePrefixReturn.relocated_run,
    Source284PayloadLoop.relocated_run,Source284ScratchCounterSeed.continuation_run,
    Source284TokenCounterContinue.relocated_run]
  repeat rw [Source284SourceRelocation.shiftConfig_add]

/-- The raw input setup and token loop complete before the actual continuation
executes; all extra continuation steps remain in the same encoded program. -/
theorem source_workspace_then (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (m k certificate suffix fuel : Nat)
    (hn : 2 ≤ states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix)
        (pairTape (List.replicate k true ++ List.replicate m false) certificate))
      (cost m k w.length+fuel) =
      toSource (Shared.Beeping.NPcoNP.Source284HardwireTable.shiftConfig 181
        (run continuation ⟨pairTape (List.replicate (k+m) true) certificate,
          2*flipped w (counter m (Source284TokenCounterLoop.halves m ((suffix/4)/2))),some 1⟩ fuel)) := by
  rw [Source284Relative.run_add_clock,source_workspace states continuation w m k certificate suffix hn hv]
  change Source284Relative.run (description states continuation) ⟨_,_,active (181+1)⟩ fuel = _
  exact source_after states continuation 1 _ _ fuel hn (by omega) hv

end Shared.Beeping.NPcoNP.Source284RawCounterWorkspace
