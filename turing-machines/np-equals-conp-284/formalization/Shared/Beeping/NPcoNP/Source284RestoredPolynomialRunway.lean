import Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup
import Shared.Beeping.NPcoNP.Source284CountedShift

/-! Restore the arbitrary certificate and a polynomially large workspace on
both sides using paid finite source tables. This remains a source-level
layout, not a refinement of the literal 284-state machine. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284RestoredPolynomialRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284ScratchMarkedLoop (marks)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284PolynomialMarkedCleanup.description k (21+states) (Source284CountedShift.table continuation)

def shiftCost (k : Nat) (w : List Bool) : Nat :=
  (count k w.length+1)*(4*(w++[false]).length+7)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284PolynomialRunwayCleanup.totalCost k w+shiftCost k w

theorem marks_counter (n higher : Nat) :
    marks n (2*higher) = Source284CountedShift.counter n higher := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Source284EraseMarkedBlock.marks_succ,Source284CountedShift.counter,ih]

/-- Preparation, complete token cleanup, and the counted return shift all
execute in the actual finite source table. The continuation sees the original
certificate behind a left zero gap and the preserved frame followed by a
right zero gap. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate)
      (totalCost k w+fuel) =
    toSource (shiftConfig (685+317*k) (run continuation
      ⟨2^(count k w.length+1)*certificate,
        2*flipped (w++[false])
          (2^(block k w.length)*Source284PositivePolynomialTwoSided.retained k w.length suffix),some 0⟩ fuel)) := by
  have hc := Source284CountedShift.closed states continuation hn hv
  have h := Source284PolynomialMarkedCleanup.source_then k (21+states)
    (Source284CountedShift.table continuation) w certificate suffix (shiftCost k w+fuel) (by omega) hc
  have ht : totalCost k w+fuel = Source284PolynomialRunwayCleanup.totalCost k w+
      (shiftCost k w+fuel) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284PolynomialMarkedCleanup.description k (21+states)
    (Source284CountedShift.table continuation)) _ _ = _
  rw [h]
  have hpow : 2^(block k w.length+1)*Source284PositivePolynomialTwoSided.retained k w.length suffix =
      2*(2^(block k w.length)*Source284PositivePolynomialTwoSided.retained k w.length suffix) := by
    rw [pow_succ]; ring
  rw [hpow,marks_counter]
  simp only [shiftCost]
  rw [Source284CountedShift.countdown_after]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have hs : 664+317*k+14+1+6=685+317*k := by omega
  rw [hs]

noncomputable def countPolynomial (k : Nat) : Polynomial Nat :=
  Source284EraseMarkedHistory.cellsPolynomial k (Polynomial.X+2) (Polynomial.X+2)+
    (Source284PolynomialRunwayCleanup.zerosPolynomial k+2)

theorem countPolynomial_eval (k n : Nat) : (countPolynomial k).eval n = count k n := by
  simp [countPolynomial,count,Source284PolynomialRunwayCleanup.zerosPolynomial,
    Source284PolynomialRunwayCleanup.zeros,Source284PositivePolynomialRunway.blockPolynomial_eval,
    Source284ProductIterationPolynomial.outer_eval,Source284EraseMarkedHistory.cellsPolynomial_eval,
    Polynomial.eval_add,Polynomial.eval_mul]

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284PolynomialRunwayCleanup.costPolynomial k+
    (countPolynomial k+1)*(4*(Polynomial.X+1)+7)

theorem totalCost_polynomial (k : Nat) (w : List Bool) :
    totalCost k w ≤ (costPolynomial k).eval w.length := by
  have h := Source284PolynomialRunwayCleanup.totalCost_polynomial k w
  simp only [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,countPolynomial_eval]
  simp [totalCost,shiftCost] at *
  omega

/-- For any fixed polynomial demand, one fixed finite source program prepares
both gaps and restores the arbitrary certificate. The chosen stage count is
independent of the tested input and certificate. -/
theorem source_polynomial_runway (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ (w : List Bool) (certificate suffix : Nat), ∃ scratch,
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (Source284Parser.encodeFrame w suffix) certificate) (totalCost k w) =
        ⟨2^(count k w.length+1)*certificate,
          2*flipped (w++[false]) (2^(p.eval w.length)*scratch),active (685+317*k)⟩ ∧
      p.eval w.length ≤ count k w.length+1 ∧
      totalCost k w ≤ (costPolynomial k).eval w.length := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates p
  refine ⟨k,?_⟩
  intro w certificate suffix
  have hb := hk w.length
  have hc : block k w.length ≤ count k w.length+1 := by
    simp only [count,Source284PolynomialRunwayCleanup.zeros]; omega
  have hp : p.eval w.length ≤ block k w.length := hb
  have hprefix : 2^(block k w.length)*Source284PositivePolynomialTwoSided.retained k w.length suffix =
      2^(p.eval w.length)*(2^(block k w.length-p.eval w.length)*
        Source284PositivePolynomialTwoSided.retained k w.length suffix) := by
    have he : block k w.length = p.eval w.length+(block k w.length-p.eval w.length) := by omega
    conv_lhs => rw [he,pow_add]
    ring
  refine ⟨2^(block k w.length-p.eval w.length)*
    Source284PositivePolynomialTwoSided.retained k w.length suffix,?_,by omega,totalCost_polynomial k w⟩
  have h := source_then k states continuation w certificate suffix 0 hn hv
  simpa [hprefix,run,shiftConfig,toSource,nextState] using h

/-- The restored-runway theorem covers every numeric source input, including
the empty decoded frame and arbitrary ignored high suffixes. -/
theorem source_all_inputs (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ input certificate : Nat, ∃ (w : List Bool) (suffix scratch : Nat),
      Source284Parser.encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation) (Source284Relative.initial input certificate)
        (totalCost k w) =
        ⟨2^(count k w.length+1)*certificate,
          2*flipped (w++[false]) (2^(p.eval (Source284Parser.length input))*scratch),
          active (685+317*k)⟩ ∧
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

end Shared.Beeping.NPcoNP.Source284RestoredPolynomialRunway
