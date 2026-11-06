import Shared.Beeping.NPcoNP.Source284SentinelPositiveTokens
import Shared.Beeping.NPcoNP.Source284RestoredPolynomialRunway

/-! A paid polynomial runway whose original certificate is protected by a
detectable delimiter. All product, cleanup, and return-shift stages are
executed in one fixed finite source table. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284DelimitedPolynomialRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialRunwayCleanup (zeros cleanupCost)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284RestoredPolynomialRunway (shiftCost)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)

def postTable (k : Nat) (continuation : Nat → Bool → Row) : Nat → Bool → Row :=
  table k (Source284TwoSidedWorkspace.table
    (Source284PolynomialMarkedCleanup.table k (Source284CountedShift.table continuation)))

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284SentinelPositiveTokens.description (124+317*k+states) (postTable k continuation)

def postCost (k : Nat) (w : List Bool) : Nat :=
  cost k (w.length+2) (w.length+2) (w++[false]).length+
    Source284TwoSidedWorkspace.workCost (block k w.length) (w++[false]).length+
    cleanupCost k w+shiftCost k w

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284SentinelPositiveTokens.totalCost w+postCost k w

def retained (k n suffix : Nat) : Nat :=
  halves (block k n) ((suffixAfter k (n+2) (n+2) (Source284SentinelPositiveTokens.retained n suffix))/2)

theorem post_closed (k states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) :
    Closed (124+317*k+states) (postTable k continuation) := by
  have hs := Source284CountedShift.closed states continuation hn hv
  have hc := Source284PolynomialMarkedCleanup.closed k (21+states)
    (Source284CountedShift.table continuation) (by omega) hs
  have hw := Source284TwoSidedWorkspace.closed (30+30*k+(21+states))
    (Source284PolynomialMarkedCleanup.table k (Source284CountedShift.table continuation)) (by omega) hc
  have hp := Source284ProductIteration.closed k (73+(30+30*k+(21+states)))
    (Source284TwoSidedWorkspace.table
      (Source284PolynomialMarkedCleanup.table k (Source284CountedShift.table continuation))) (by omega) hw
  simpa [postTable,show 287*k+(73+(30+30*k+(21+states)))=124+317*k+states by omega] using hp

/-- The original certificate is preceded by a physically written one
delimiter after a polynomially large left gap. The frame is followed by a
separate right gap. Every initialization and cleanup transition is paid. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost k w+fuel) =
    toSource (shiftConfig (699+317*k) (run continuation
      ⟨2^(count k w.length+1)*(2*certificate+1),
        2*flipped (w++[false]) (2^(block k w.length)*retained k w.length suffix),some 0⟩ fuel)) := by
  have hc := post_closed k states continuation hn hv
  have h := Source284SentinelPositiveTokens.source_then (124+317*k+states)
    (postTable k continuation) w certificate suffix (postCost k w+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284SentinelPositiveTokens.totalCost w+
      (postCost k w+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284SentinelPositiveTokens.description (124+317*k+states)
    (postTable k continuation)) _ _ = _
  rw [h]
  unfold postTable postCost
  have ha : cost k (w.length+2) (w.length+2) (w++[false]).length+
      Source284TwoSidedWorkspace.workCost (block k w.length) (w++[false]).length+
        cleanupCost k w+shiftCost k w+fuel =
      cost k (w.length+2) (w.length+2) (w++[false]).length+
        (Source284TwoSidedWorkspace.workCost (block k w.length) (w++[false]).length+
          (cleanupCost k w+(shiftCost k w+fuel))) := by omega
  rw [ha,Source284ProductIteration.iterate_then]
  dsimp only [block]
  rw [Source284TwoSidedWorkspace.workspace_then]
  simp only [cleanupCost,Source284PolynomialRunwayCleanup.cleanupCost,Source284PolynomialMarkedCleanup.table]
  rw [Source284PolynomialRunwayCleanup.top_form]
  change toSource (shiftConfig 575 (shiftConfig (287*k) (shiftConfig 73
    (run (Source284EraseMarkedBlock.table (Source284EraseMarkedHistory.table k
      (Source284CountedShift.table continuation)))
      ⟨2^(zeros k w.length+1)*
        (2*historyAfter k (w.length+2) (w.length+2) (2*certificate+1)+1),_,some 0⟩ _)))) = _
  rw [show Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
      Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+
        (shiftCost k w+fuel) =
      Source284EraseZeroBlock.cost (zeros k w.length) (w++[false]).length+
        (Source284EraseTokenHistory.cost k (w.length+2) (w.length+2) (w++[false]).length+
          (shiftCost k w+fuel)) by omega]
  rw [Source284EraseMarkedBlock.erase_then,Source284EraseMarkedHistory.erase_then,
    Source284EraseMarkedHistory.marks_add]
  have hpow : 2^(block k w.length+1)*retained k w.length suffix =
      2*(2^(block k w.length)*retained k w.length suffix) := by rw [pow_succ]; ring
  change _ = toSource (shiftConfig (699+317*k) (run continuation _ fuel))
  dsimp only [retained,block] at hpow
  rw [hpow,Source284RestoredPolynomialRunway.marks_counter]
  simp only [shiftCost,count]
  rw [Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 575+287*k+73+30+30*k+14+1+6=699+317*k := by omega
  rw [hs]
  rfl

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284RestoredPolynomialRunway.costPolynomial k+(4*(Polynomial.X+1)+7)

theorem totalCost_polynomial (k : Nat) (w : List Bool) :
    totalCost k w ≤ (costPolynomial k).eval w.length := by
  have h := Source284RestoredPolynomialRunway.totalCost_polynomial k w
  have he : totalCost k w = Source284RestoredPolynomialRunway.totalCost k w+
      (4*(w++[false]).length+7) := by
    simp [totalCost,postCost,Source284SentinelPositiveTokens.totalCost,
      Source284InitialCertificateSentinel.totalCost,Source284RestoredPolynomialRunway.totalCost,
      Source284PolynomialRunwayCleanup.totalCost,Source284PositivePolynomialTwoSided.totalCost,
      Source284DoublePositiveTokens.totalCost,Source284DoubleLengthTokens.totalCost,
      Source284LengthGrowSource.totalCost]; omega
  rw [he]
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one,List.length_append,List.length_singleton] at *
  omega

/-- One fixed table, chosen from the polynomial demand, works for every
parsed input, arbitrary certificate and ignored high input suffix. -/
theorem source_polynomial_runway (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ (w : List Bool) (certificate suffix : Nat), ∃ scratch,
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost k w) =
        ⟨2^(count k w.length+1)*(2*certificate+1),
          2*flipped (w++[false]) (2^(p.eval w.length)*scratch),active (699+317*k)⟩ ∧
      p.eval w.length ≤ count k w.length+1 ∧
      totalCost k w ≤ (costPolynomial k).eval w.length := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates p
  refine ⟨k,?_⟩
  intro w certificate suffix
  have hb := hk w.length
  have hc : block k w.length ≤ count k w.length+1 := by
    simp only [count,Source284PolynomialRunwayCleanup.zeros]; omega
  have hp : p.eval w.length ≤ block k w.length := hb
  have hprefix : 2^(block k w.length)*retained k w.length suffix =
      2^(p.eval w.length)*(2^(block k w.length-p.eval w.length)*retained k w.length suffix) := by
    have he : block k w.length = p.eval w.length+(block k w.length-p.eval w.length) := by omega
    conv_lhs => rw [he,pow_add]
    ring
  refine ⟨2^(block k w.length-p.eval w.length)*retained k w.length suffix,?_,by omega,
    totalCost_polynomial k w⟩
  have h := source_then k states continuation w certificate suffix 0 hn hv
  simpa [hprefix,run,shiftConfig,toSource,nextState] using h

theorem source_all_inputs (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ input certificate : Nat, ∃ (w : List Bool) (suffix scratch : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation) (Source284Relative.initial input certificate)
        (totalCost k w) =
        ⟨2^(count k w.length+1)*(2*certificate+1),
          2*flipped (w++[false]) (2^(p.eval (Source284Parser.length input))*scratch),
          active (699+317*k)⟩ ∧
      p.eval (Source284Parser.length input) ≤ count k w.length+1 ∧
      totalCost k w ≤ (costPolynomial k).eval (Source284Parser.length input) := by
  obtain ⟨k,hk⟩ := source_polynomial_runway p states continuation hn hv
  refine ⟨k,?_⟩
  intro input certificate
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  obtain ⟨scratch,hr,hleft,hcost⟩ := hk w certificate suffix
  refine ⟨w,suffix,scratch,hw,hlen.symm,?_,?_,?_⟩
  · simpa [hw,hlen] using hr
  · simpa [hlen] using hleft
  · simpa [hlen] using hcost

end Shared.Beeping.NPcoNP.Source284DelimitedPolynomialRunway
