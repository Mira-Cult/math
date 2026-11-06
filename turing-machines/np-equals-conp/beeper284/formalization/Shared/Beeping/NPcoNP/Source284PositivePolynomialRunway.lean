import Shared.Beeping.NPcoNP.Source284DoublePositiveTokens
import Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial
import Shared.Beeping.NPcoNP.Source284PreparedTokenRunway

/-! A paid, fixed finite source program creates a one-sided runway for any
fixed polynomial input-length demand, including empty and unit-length inputs.
The second side, verifier composition and physical table remain separate. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial (innerPolynomial)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DoublePositiveTokens.description (287*k+(71+states))
    (table k (Source284PreparedTokenRunway.table continuation))

def block (k n : Nat) : Nat := innerAfter k (n+2) (n+2)

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284DoublePositiveTokens.totalCost w+
    cost k (w.length+2) (w.length+2) (w++[false]).length+
    Source284PreparedTokenRunway.cost (block k w.length) (w++[false]).length

def retained (k n suffix : Nat) : Nat :=
  halves (block k n) ((suffixAfter k (n+2) (n+2) (Source284DoublePositiveTokens.retained n suffix))/2)

/-- All bootstrap, product, token-counting, zero-writing and handoff steps
execute in one fixed source description. The certificate is retained beyond
the new zero prefix; ignored high scratch bits are accounted for. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (632+287*k) (run continuation
      ⟨2^(block k w.length+1)*
        pairTape (List.replicate (block k w.length) true)
          (pairTape (List.replicate (outerAfter k (w.length+2) (w.length+2)) false)
            (historyAfter k (w.length+2) (w.length+2) certificate)),
        2*flipped (w++[false]) (retained k w.length suffix),some 0⟩ fuel)) := by
  let m := block k w.length
  have ht := Source284PreparedTokenRunway.closed states continuation hn hv
  have hc := closed k (71+states) (Source284PreparedTokenRunway.table continuation) (by omega) ht
  have hp := Source284DoublePositiveTokens.source_then (287*k+(71+states))
    (table k (Source284PreparedTokenRunway.table continuation)) w certificate suffix
    (cost k (w.length+2) (w.length+2) (w++[false]).length+
      (Source284PreparedTokenRunway.cost m (w++[false]).length+fuel)) (by omega) hc
  have ht' : totalCost k w+fuel = Source284DoublePositiveTokens.totalCost w+
      (cost k (w.length+2) (w.length+2) (w++[false]).length+
        (Source284PreparedTokenRunway.cost m (w++[false]).length+fuel)) := by
    simp [totalCost,m]; omega
  rw [ht']
  change Source284Relative.run (Source284DoublePositiveTokens.description (287*k+(71+states))
    (table k (Source284PreparedTokenRunway.table continuation))) _ _ = _
  rw [hp,iterate_then]
  dsimp only [m,block]
  rw [Source284PreparedTokenRunway.runway_then]
  simp only [Source284SourceRelocation.shiftConfig_add]
  have he : 561+(287*k+71)=632+287*k := by omega
  rw [he]
  rfl

noncomputable def blockPolynomial (k : Nat) : Polynomial Nat :=
  innerPolynomial k (Polynomial.X+2) (Polynomial.X+2)

theorem blockPolynomial_eval (k n : Nat) : (blockPolynomial k).eval n = block k n := by
  have h := Source284ProductIterationPolynomial.inner_eval k n (Polynomial.X+2) (Polynomial.X+2)
  have hp : (Polynomial.X+2 : Polynomial Nat).eval n = n+2 := by simp
  rw [hp] at h
  exact h

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284DoublePositiveTokens.costPolynomial+
    Source284ProductIteration.costPolynomial k (Polynomial.X+2) (Polynomial.X+2) (Polynomial.X+1)+
    Source284PreparedTokenRunway.costPolynomial (blockPolynomial k) (Polynomial.X+1)

/-- With the exponent/stage count fixed in the table, its complete source
runway-generation clock is polynomial in the parsed input length. -/
theorem totalCost_polynomial (k : Nat) (w : List Bool) : totalCost k w ≤ (costPolynomial k).eval w.length := by
  have hinit := Source284DoublePositiveTokens.totalCost_polynomial w
  have hstage := Source284ProductIteration.cost_polynomial k w.length (w.length+2) (w.length+2)
    (w++[false]).length (Polynomial.X+2) (Polynomial.X+2) (Polynomial.X+1)
    (by simp) (by simp) (by simp)
  have hb : block k w.length ≤ (blockPolynomial k).eval w.length := by rw [blockPolynomial_eval]
  have hrun := Source284PreparedTokenRunway.cost_polynomial w.length (block k w.length)
    (w++[false]).length (blockPolynomial k) (Polynomial.X+1) hb (by simp)
  unfold totalCost
  simp only [costPolynomial,Polynomial.eval_add]
  omega

/-- One stage count dominates the requested polynomial for every input
length, because both initialized token blocks have length `n+2`. -/
theorem block_dominates (p : Polynomial Nat) : ∃ k : Nat, ∀ n : Nat, p.eval n ≤ block k n := by
  obtain ⟨e,he⟩ := Shared.ComplexityBridge.ClockBounds.polynomial_fixed_exponent p
  refine ⟨e,?_⟩
  intro n
  have hm : (n+2)^e ≤ (n+2)^(e+1) := Nat.pow_le_pow_right (by omega) (by omega)
  exact le_trans (he n) (le_trans hm (Source284ProductGrowth.square_seed_lower e (n+2) (by omega)))

/-- One source description, selected from the requested polynomial once,
creates a sufficiently long one-sided zero runway on every raw frame. -/
theorem source_polynomial_runway (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ (w : List Bool) (certificate suffix : Nat), ∃ left right,
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w) =
          ⟨left,right,active (632+287*k)⟩ ∧ 2^(p.eval w.length) ∣ left := by
  obtain ⟨k,hk⟩ := block_dominates p
  refine ⟨k,?_⟩
  intro w certificate suffix
  let m := block k w.length
  let tail := pairTape (List.replicate m true)
    (pairTape (List.replicate (outerAfter k (w.length+2) (w.length+2)) false)
      (historyAfter k (w.length+2) (w.length+2) certificate))
  refine ⟨2^(m+1)*tail,2*flipped (w++[false]) (retained k w.length suffix),?_,?_⟩
  · have h := source_then k states continuation w certificate suffix 0 hn hv
    simpa [m,tail,run,shiftConfig,toSource,nextState] using h
  · have hsize : p.eval w.length ≤ m+1 := by dsimp [m]; have h := hk w.length; omega
    exact dvd_mul_of_dvd_left (Nat.pow_dvd_pow 2 hsize) tail

/-- The same fixed table works on every numeric input and every certificate;
the parser supplies the frame and its arbitrary suffix, and the complete
preparation has a polynomial source-transition bound. -/
theorem source_all_inputs (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ input certificate : Nat, ∃ (w : List Bool) (suffix left right : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation) (Source284Relative.initial input certificate)
        (totalCost k w) = ⟨left,right,active (632+287*k)⟩ ∧
      2^(p.eval (Source284Parser.length input)) ∣ left ∧
      totalCost k w ≤ (costPolynomial k).eval (Source284Parser.length input) := by
  obtain ⟨k,hk⟩ := source_polynomial_runway p states continuation hn hv
  refine ⟨k,?_⟩
  intro input certificate
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  obtain ⟨left,right,hr,hd⟩ := hk w certificate suffix
  refine ⟨w,suffix,left,right,hw,hlen.symm,?_,?_,?_⟩
  · simpa [hw] using hr
  · simpa [hlen] using hd
  · simpa [hlen] using totalCost_polynomial k w

end Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway
