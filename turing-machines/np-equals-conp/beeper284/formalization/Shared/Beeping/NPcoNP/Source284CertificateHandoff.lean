import Shared.Beeping.NPcoNP.Source284PreparedFramePipeline
import Shared.Beeping.NPcoNP.Source284WindowRewind

/-! A finite boundary adapter and unary-pair scan expose the retained
certificate. The input frame and all its high suffix bits remain on the
opposite tape half; no certificate validation or witness packing is claimed. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284CertificateHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchScanner (push)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

def table (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,true,some 1⟩
  else if q = 1 then ⟨b,false,some 2⟩
  else if q = 2 then ⟨b,true,some 3⟩
  else shiftRow 3 (Source284UnaryPairScanner.table continuation (q-3) b)

theorem closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (7+states) (table continuation) := by
  have hs := Source284UnaryPairScanner.closed states continuation hn hv
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; simp [table] at hnext; omega
  · by_cases h1 : q = 1
    · subst q; simp [table] at hnext; omega
    · by_cases h2 : q = 2
      · subst q; simp [table] at hnext; omega
      · have ht : (shiftRow 3 (Source284UnaryPairScanner.table continuation (q-3) b)).next = some q' := by
          simpa [table,h0,h1,h2] using hnext
        have hq0 : q-3 < 4+states := by omega
        cases he : (Source284UnaryPairScanner.table continuation (q-3) b).next with
        | none => simp [shiftRow,he] at ht
        | some r =>
          have h := hs (q-3) hq0 b r he
          simp [shiftRow,he] at ht
          subst q'
          omega

theorem relocated_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table continuation (3+q) b = shiftRow 3 (Source284UnaryPairScanner.table continuation q b) := by
  simp [table, show 3+q ≠ 1 by omega, show 3+q ≠ 2 by omega]

theorem relocated_step (continuation : Nat → Bool → Row) (c : Config) :
    step (table continuation) (shiftConfig 3 c) =
      shiftConfig 3 (step (Source284UnaryPairScanner.table continuation) c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,relocated_row,shiftRow]
      split <;> rfl

theorem relocated_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 3 c) fuel =
      shiftConfig 3 (run (Source284UnaryPairScanner.table continuation) c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,relocated_step]

theorem setup (continuation : Nat → Bool → Row) (left right : Nat) :
    run (table continuation) ⟨2*left,right,some 0⟩ 3 =
      shiftConfig 3 ⟨left,2*right,some 0⟩ := by
  have h0 : step (table continuation) ⟨2*left,right,some 0⟩ = ⟨right,2*left,some 1⟩ := by
    apply Source284WindowRewind.generic_turn
    intro b; simp [table]
  have h1 : step (table continuation) ⟨right,2*left,some 1⟩ = ⟨2*right,left,some 2⟩ := by
    simp [step,table,bit,Nat.testBit_zero]
  have h2 : step (table continuation) ⟨2*right,left,some 2⟩ = ⟨left,2*right,some 3⟩ := by
    apply Source284WindowRewind.generic_turn
    intro b; simp [table]
  simp only [run,h0,h1,h2,shiftConfig,Option.map_some]

theorem scan (continuation : Nat → Bool → Row) (xs : List Bool) (certificate right : Nat) :
    run (table continuation) ⟨2*pairTape xs certificate,right,some 0⟩ (2*xs.length+6) =
      ⟨4*push (2*right) xs+1,certificate,some 7⟩ := by
  have ht : 2*xs.length+6 = 3+(2*xs.length+3) := by omega
  rw [ht,Source284PayloadPop.run_add,setup,relocated_run,Source284UnaryPairScanner.scan]
  rfl

theorem scan_zeros (continuation : Nat → Bool → Row) (n certificate right : Nat) :
    run (table continuation) ⟨2*pairTape (List.replicate n false) certificate,right,some 0⟩ (2*n+6) =
      ⟨4^(n+1)*(2*right)+1,certificate,some 7⟩ := by
  have h := scan continuation (List.replicate n false) certificate right
  simp only [List.length_replicate,Source284UnaryPairScanner.push_zeros] at h
  rw [h]
  simp [pow_succ]
  ring

theorem continuation_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table continuation) (shiftConfig 3 (shiftConfig 1 (shiftConfig 3 c))) fuel =
      shiftConfig 3 (shiftConfig 1 (shiftConfig 3 (run continuation c fuel))) := by
  rw [relocated_run,Source284UnaryPairScanner.relocated_run,Source284ScratchScanner.relocated_run]

def description (states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PreparedFramePipeline.description (7+states) (table continuation)

def totalCost (n : Nat) : Nat := Source284PreparedFramePipeline.totalCost n+(2*n+6)

theorem source_scan (states : Nat) (continuation : Nat → Bool → Row)
    (n certificate right : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation)
      ⟨2*pairTape (List.replicate n false) certificate,right,active 383⟩ (2*n+6) =
      ⟨4^(n+1)*(2*right)+1,certificate,active 390⟩ := by
  have hc := closed states continuation hn hv
  have hr := Source284PreparedFramePipeline.source_after (7+states) (table continuation)
    0 (2*pairTape (List.replicate n false) certificate) right (2*n+6) (by omega) (by omega) hc
  change Source284Relative.run (description states continuation)
    ⟨2*pairTape (List.replicate n false) certificate,right,active (383+0)⟩ _ = _ at hr
  rw [scan_zeros] at hr
  simpa [shiftConfig,toSource,nextState,active,← Nat.add_assoc] using hr

theorem source_pipeline (states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    let right := encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1)
    Source284Relative.run (description states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨4^(w.length+1)*(2*right)+1,certificate,active 390⟩ := by
  have hc := closed states continuation hn hv
  have hp := Source284PreparedFramePipeline.source_pipeline (7+states) (table continuation)
    w certificate suffix (by omega) hc
  dsimp only
  unfold totalCost
  rw [Source284Relative.run_add_clock]
  change Source284Relative.run (description states continuation)
    (Source284Relative.run (Source284PreparedFramePipeline.description (7+states)
      (table continuation)) _ _) _ = _
  rw [hp,source_scan states continuation w.length certificate _ hn hv]

theorem totalCost_le (n : Nat) : totalCost n ≤ 4*n*n*n+42*n*n+130*n+123 := by
  have h := Source284PreparedFramePipeline.totalCost_le n
  unfold totalCost
  have he : (4*n*n*n+42*n*n+128*n+117)+(2*n+6) =
      4*n*n*n+42*n*n+130*n+123 := by ring
  omega

/-- For every numeric input, the source program reaches its unchanged
certificate with the entire prepared frame retained, in bounded time. -/
theorem source_total_progress (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (w : List Bool) (suffix t : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        130*(Source284Parser.length input)+123 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
    ⟨4^(w.length+1)*(2*encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1))+1,
      certificate,active 390⟩ := by
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  refine ⟨w,suffix,totalCost (Source284Parser.length input),hw,hlen.symm,?_,?_⟩
  · have h := totalCost_le (Source284Parser.length input)
    nlinarith
  · rw [hlen,← hw]
    exact source_pipeline states continuation w certificate suffix hn hv

/-- Relocation of the supplied continuation through all preparation stages. -/
def preparedShift (c : Config) : Config :=
  shiftConfig 8 (shiftConfig 8 (shiftConfig 16 (shiftConfig 32 (shiftConfig 69
    (shiftConfig 3 (shiftConfig 6 (shiftConfig 7 (shiftConfig 6 (shiftConfig 14 (shiftConfig 14
      (shiftConfig 97 (shiftConfig 2 (shiftConfig 3 (shiftConfig 7 (shiftConfig 5 (shiftConfig 6
        (shiftConfig 6 (shiftConfig 6 (shiftConfig 36 (shiftConfig 32 c))))))))))))))))))))

/-- The continuation after the certificate handoff is executed by the same
finite numeric source table, not by a separate free interpreter. -/
theorem source_after (states : Nat) (continuation : Nat → Bool → Row) (mode : Nat)
    (left right fuel : Nat) (hn : 0 < states) (hm : mode < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) ⟨left,right,active (390+mode)⟩ fuel =
      toSource (preparedShift (shiftConfig 3 (shiftConfig 1 (shiftConfig 3
        (run continuation ⟨left,right,some mode⟩ fuel))))) := by
  have hc := closed states continuation hn hv
  have hr := Source284PreparedFramePipeline.source_after (7+states) (table continuation)
    (7+mode) left right fuel (by omega) (by omega) hc
  have he : 383+(7+mode) = 390+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description states continuation) _ _ = _ at hr
  have hi : shiftConfig 3 (shiftConfig 1 (shiftConfig 3 ⟨left,right,some mode⟩)) =
      ⟨left,right,some (7+mode)⟩ := by simp [shiftConfig] <;> omega
  rw [← hi] at hr
  change Source284Relative.run (description states continuation) _ _ =
    toSource (preparedShift (run (table continuation)
      (shiftConfig 3 (shiftConfig 1 (shiftConfig 3 ⟨left,right,some mode⟩))) fuel)) at hr
  rw [continuation_run] at hr
  exact hr

/-- The retained frame still has exactly the verifier's input window after
reaching the certificate. The larger tape number also preserves its high suffix. -/
theorem source_canonical_window (states : Nat) (continuation : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ (right t : Nat),
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        130*(Source284Parser.length input)+123 ∧
      Source284Relative.run (description states continuation) (Source284Relative.initial input certificate) t =
        ⟨4^(Source284Parser.length input+1)*(2*right)+1,certificate,active 390⟩ ∧
      Source284CanonicalPairWindow.window (Source284PackedGuardWindow.inputBits input.bits).length right =
        Source284PackedGuardWindow.inputBits input.bits := by
  have hc := closed states continuation hn hv
  obtain ⟨right,t,ht,hr,hw⟩ := Source284PreparedFramePipeline.source_canonical_window_bits
    (7+states) (table continuation) input certificate (by omega) hc
  refine ⟨right,t+(2*Source284Parser.length input+6),?_,?_,hw⟩
  · omega
  · rw [Source284Relative.run_add_clock]
    change Source284Relative.run (description states continuation)
      (Source284Relative.run (Source284PreparedFramePipeline.description (7+states)
        (table continuation)) _ _) _ = _
    rw [hr,source_scan states continuation _ certificate right hn hv]

namespace Fixtures
example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 0 7) 123 =
      ⟨17,7,active 390⟩ := by
  simpa [encodeFrame,totalCost,Source284PreparedFramePipeline.totalCost,
    Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    Source284ScratchFlip.flipped,bit] using source_pipeline states continuation [] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 3 7) 271 =
      ⟨353,7,active 390⟩ := by
  simpa [encodeFrame,totalCost,Source284PreparedFramePipeline.totalCost,
    Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    Source284ScratchFlip.flipped,bit] using source_pipeline states continuation [true] 7 0 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 295 7) 483 =
      ⟨4993,7,active 390⟩ := by
  simpa [encodeFrame,totalCost,Source284PreparedFramePipeline.totalCost,
    Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    Source284ScratchFlip.flipped,bit] using source_pipeline states continuation [true,false] 7 9 hn hv

example (states : Nat) (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description states continuation) (Source284Relative.initial 32775 7) 483 =
      ⟨37761,7,active 390⟩ := by
  simpa [encodeFrame,totalCost,Source284PreparedFramePipeline.totalCost,
    Source284EqualityPipeline.totalCost,Source284EqualityPipeline.finalTail,
    Source284RetryInitPipeline.totalCost,Source284PayloadSentinelPipeline.totalCost_formula,
    Source284RetryLoopComplete.totalCost,Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,
    Source284ScratchFlip.flipped,bit] using source_pipeline states continuation [true,false] 7 1024 hn hv
end Fixtures

end Shared.Beeping.NPcoNP.Source284CertificateHandoff
