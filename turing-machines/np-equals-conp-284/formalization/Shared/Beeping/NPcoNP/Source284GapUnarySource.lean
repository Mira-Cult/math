import Shared.Beeping.NPcoNP.Source284GapUnaryPrepare
import Shared.Beeping.NPcoNP.Source284DelimitedPolynomialRunway

/-! Raw-input initialization, paid certificate seek, and conversion of the
protected gap into a polynomial unary bound. A later continuation must enforce
the witness cutoff and implement the verifier; this module does not claim a
complexity equality or a physical-table refinement. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284GapUnarySource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig run_front)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block)
open Shared.Beeping.NPcoNP.Source284PolynomialMarkedCleanup (count)
open Shared.Beeping.NPcoNP.Source284SingleTaggedDispatch (boundary)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- The seek stops on the certificate itself, before consuming either tag
bit. Its two states turn onto the protected half and scan to the delimiter. -/
def seek (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q=0 then ⟨true,true,some 1⟩
  else if q=1 then ⟨b,false,some (if b then 2 else 1)⟩
  else shiftRow 2 (continuation (q-2) b)

theorem seek_closed (states : Nat) (continuation : Nat → Bool → Row)
    (hn : 0 < states) (hv : Closed states continuation) : Closed (2+states) (seek continuation) := by
  intro q hq b q' hnext
  by_cases h0 : q=0
  · subst q; simp [seek] at hnext; omega
  · by_cases h1 : q=1
    · subst q; cases b <;> simp [seek,h0] at hnext <;> omega
    · have he : (shiftRow 2 (continuation (q-2) b)).next = some q' := by
        simpa [seek,h0,h1] using hnext
      cases ht : (continuation (q-2) b).next with
      | none => simp [shiftRow,ht] at he
      | some r =>
        have hr := hv (q-2) (by omega) b r ht
        simp [shiftRow,ht] at he
        subst q'
        omega

theorem seek_row (continuation : Nat → Bool → Row) (q : Nat) (b : Bool) :
    seek continuation (2+q) b = shiftRow 2 (continuation q b) := by
  simp [seek,show 2+q ≠ 1 by omega]

theorem seek_step (continuation : Nat → Bool → Row) (c : Config) :
    step (seek continuation) (shiftConfig 2 c) = shiftConfig 2 (step continuation c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,seek_row,shiftRow]
      split <;> rfl

theorem seek_run (continuation : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (seek continuation) (shiftConfig 2 c) fuel = shiftConfig 2 (run continuation c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,seek_step]

theorem seek_zeros (continuation : Nat → Bool → Row) (n left right : Nat) :
    run (seek continuation) ⟨left,2^n*right,some 1⟩ n = ⟨2^n*left,right,some 1⟩ := by
  induction n generalizing left with
  | zero => simp [run]
  | succ n ih =>
    rw [pow_succ]
    have he : (2^n*2)*right=2*(2^n*right) := by ring
    rw [he,run_front]
    have hs : step (seek continuation) ⟨left,2*(2^n*right),some 1⟩ =
        ⟨2*left,2^n*right,some 1⟩ := by simp [step,seek,bit,Nat.testBit_zero]
    rw [hs,ih]
    congr 1 <;> ring

theorem seek_then (continuation : Nat → Bool → Row) (gap certificate stream fuel : Nat) :
    run (seek continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩ (gap+2+fuel) =
      shiftConfig 2 (run continuation ⟨boundary gap stream,certificate,some 0⟩ fuel) := by
  have h0 : step (seek continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩ =
      ⟨2*stream+1,2^gap*(2*certificate+1),some 1⟩ := by
    simp [step,seek,bit,Nat.testBit_zero]
  have h1 (left right : Nat) : step (seek continuation) ⟨left,2*right+1,some 1⟩ =
      ⟨2*left+1,right,some 2⟩ := by
    simp [step,seek,bit,Nat.testBit_zero,Nat.add_mod,Nat.mul_mod] <;> omega
  have ht : gap+2+fuel = 1+(gap+(1+fuel)) := by omega
  rw [ht,Source284ScratchScanner.run_add]
  change run (seek continuation)
    (step (seek continuation) ⟨2^gap*(2*certificate+1),2*stream,some 0⟩) _ = _
  rw [h0,Source284ScratchScanner.run_add,seek_zeros,Source284ScratchScanner.run_add]
  change run (seek continuation) (step (seek continuation) ⟨_,_,some 1⟩) fuel = _
  rw [h1]
  change run (seek continuation) (shiftConfig 2 ⟨boundary gap stream,certificate,some 0⟩) fuel = _
  exact seek_run continuation _ fuel

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DelimitedPolynomialRunway.description k (2+(6+states))
    (seek (Source284GapUnaryPrepare.table continuation))

def gap (k n : Nat) : Nat := count k n+1

theorem history_cells_even (k a b : Nat) :
    Source284EraseTokenHistory.cells k a b % 2 = 0 := by
  induction k generalizing a b with
  | zero => simp [Source284EraseTokenHistory.cells]
  | succ k ih =>
    simp [Source284EraseTokenHistory.cells,ih,Nat.add_mod,Nat.mul_mod]

/-- The produced gap is always odd: every erased token contributes two
cells, and the initializer adds one delimiter cell. -/
theorem gap_odd (k n : Nat) : gap k n % 2 = 1 := by
  have h := history_cells_even k (n+2) (n+2)
  simp only [gap,count,Source284PolynomialRunwayCleanup.zeros]
  omega

def stream (k : Nat) (w : List Bool) (suffix : Nat) : Nat :=
  flipped (w++[false]) (2^(block k w.length)*
    Source284DelimitedPolynomialRunway.retained k w.length suffix)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284DelimitedPolynomialRunway.totalCost k w+3*gap k w.length+6

/-- From the original framed input and arbitrary certificate, the fixed
finite program prepares an actual unary bound, preserving the full
certificate and the high input-side stream. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states)
    (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (707+317*k) (run continuation
      ⟨pairTape (List.replicate (gap k w.length/2) false)
          (Source284GapUnaryPrepare.retained (gap k w.length) (stream k w suffix)),
        certificate,some 0⟩ fuel)) := by
  have hp := Source284GapUnaryPrepare.closed states continuation hn hv
  have hs := seek_closed (6+states) (Source284GapUnaryPrepare.table continuation) (by omega) hp
  have h := Source284DelimitedPolynomialRunway.source_then k (2+(6+states))
    (seek (Source284GapUnaryPrepare.table continuation)) w certificate suffix
    (gap k w.length+2+(2*gap k w.length+4+fuel)) (by omega) hs
  have ht : totalCost k w+fuel = Source284DelimitedPolynomialRunway.totalCost k w+
      (gap k w.length+2+(2*gap k w.length+4+fuel)) := by simp [totalCost]; omega
  rw [ht]
  change Source284Relative.run (Source284DelimitedPolynomialRunway.description k (2+(6+states))
    (seek (Source284GapUnaryPrepare.table continuation))) _ _ = _
  rw [h]
  change toSource (shiftConfig (699+317*k) (run (seek (Source284GapUnaryPrepare.table continuation))
    ⟨2^(gap k w.length)*(2*certificate+1),2*stream k w suffix,some 0⟩ _)) = _
  rw [seek_then,Source284GapUnaryPrepare.prepare_then]
  repeat rw [Source284SourceRelocation.shiftConfig_add]
  have he : 699+317*k+2+6=707+317*k := by omega
  rw [he]

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284DelimitedPolynomialRunway.costPolynomial k+
    3*(Source284RestoredPolynomialRunway.countPolynomial k+1)+6

theorem cost_polynomial (k : Nat) (w : List Bool) : totalCost k w ≤ (costPolynomial k).eval w.length := by
  have h := Source284DelimitedPolynomialRunway.totalCost_polynomial k w
  simp only [totalCost,gap,costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_one,Polynomial.eval_ofNat,Source284RestoredPolynomialRunway.countPolynomial_eval]
  omega

/-- One fixed stage count creates a unary bound at least as large as the
requested polynomial on every input, including empty inputs. -/
theorem bound_dominates (p : Polynomial Nat) : ∃ k : Nat, ∀ n : Nat, p.eval n ≤ gap k n/2 := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates (2*p+4)
  refine ⟨k,?_⟩
  intro n
  have h := hk n
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at h
  have hc : block k n ≤ count k n+3 := by
    simp only [count,Source284PolynomialRunwayCleanup.zeros]; omega
  simp only [gap]
  omega

end Shared.Beeping.NPcoNP.Source284GapUnarySource
