import Shared.Beeping.NPcoNP.Source284DoublePositiveTokens
import Shared.Beeping.NPcoNP.Source284ProductIterationPolynomial
import Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway
import Shared.Beeping.NPcoNP.Source284TwoSidedWorkspace

/-! A fixed finite source program builds a polynomially large token block
from a raw frame, then pays for zero workspace on both tape sides. The
guarded verifier and physical 284-state table are not bound in this module. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
namespace Shared.Beeping.NPcoNP.Source284PositivePolynomialTwoSided

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284ScratchFlip (flipped)
open Shared.Beeping.NPcoNP.Source284TokenCounterLoop (halves)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284ProductIteration
open Shared.Beeping.NPcoNP.Source284PositivePolynomialRunway (block blockPolynomial blockPolynomial_eval)

def description (k states : Nat) (continuation : Nat → Bool → Row) : Nat :=
  Source284DoublePositiveTokens.description (287*k+(73+states))
    (table k (Source284TwoSidedWorkspace.table continuation))

def totalCost (k : Nat) (w : List Bool) : Nat :=
  Source284DoublePositiveTokens.totalCost w+
    cost k (w.length+2) (w.length+2) (w++[false]).length+
    Source284TwoSidedWorkspace.workCost (block k w.length) (w++[false]).length

def retained (k n suffix : Nat) : Nat :=
  halves (block k n) ((suffixAfter k (n+2) (n+2) (Source284DoublePositiveTokens.retained n suffix))/2)

/-- The exact paid source run retains all older token blocks and the entire
certificate beyond the left zeros. The right zero prefix precedes the
tracked higher scratch suffix. -/
theorem source_then (k states : Nat) (continuation : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < states) (hv : Closed states continuation) :
    Source284Relative.run (description k states continuation)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w+fuel) =
    toSource (shiftConfig (634+287*k) (run continuation
      ⟨4^(block k w.length+1)*
        pairTape (List.replicate (outerAfter k (w.length+2) (w.length+2)) false)
          (historyAfter k (w.length+2) (w.length+2) certificate),
        2*flipped (w++[false]) (2^(block k w.length+1)*retained k w.length suffix),some 0⟩ fuel)) := by
  let m := block k w.length
  have ht := Source284TwoSidedWorkspace.closed states continuation hn hv
  have hc := closed k (73+states) (Source284TwoSidedWorkspace.table continuation) (by omega) ht
  have hp := Source284DoublePositiveTokens.source_then (287*k+(73+states))
    (table k (Source284TwoSidedWorkspace.table continuation)) w certificate suffix
    (cost k (w.length+2) (w.length+2) (w++[false]).length+
      (Source284TwoSidedWorkspace.workCost m (w++[false]).length+fuel)) (by omega) hc
  have ht' : totalCost k w+fuel = Source284DoublePositiveTokens.totalCost w+
      (cost k (w.length+2) (w.length+2) (w++[false]).length+
        (Source284TwoSidedWorkspace.workCost m (w++[false]).length+fuel)) := by
    simp [totalCost,m]; omega
  rw [ht']
  change Source284Relative.run (Source284DoublePositiveTokens.description (287*k+(73+states))
    (table k (Source284TwoSidedWorkspace.table continuation))) _ _ = _
  rw [hp,iterate_then]
  dsimp only [m,block]
  rw [Source284TwoSidedWorkspace.workspace_then]
  simp only [Source284SourceRelocation.shiftConfig_add]
  have he : 561+(287*k+73)=634+287*k := by omega
  rw [he]
  rfl

noncomputable def workspacePolynomial (block width : Polynomial Nat) : Polynomial Nat :=
  3*block*block+block*(4*width+31)+8*width+44

noncomputable def costPolynomial (k : Nat) : Polynomial Nat :=
  Source284DoublePositiveTokens.costPolynomial+
    Source284ProductIteration.costPolynomial k (Polynomial.X+2) (Polynomial.X+2) (Polynomial.X+1)+
    workspacePolynomial (blockPolynomial k) (Polynomial.X+1)

/-- For fixed `k`, the complete two-sided preparation is polynomial in the
parsed input length, including token erasure and scratch clearing. -/
theorem totalCost_polynomial (k : Nat) (w : List Bool) : totalCost k w ≤ (costPolynomial k).eval w.length := by
  have hinit := Source284DoublePositiveTokens.totalCost_polynomial w
  have hstage := Source284ProductIteration.cost_polynomial k w.length (w.length+2) (w.length+2)
    (w++[false]).length (Polynomial.X+2) (Polynomial.X+2) (Polynomial.X+1)
    (by simp) (by simp) (by simp)
  have hwork := Source284TwoSidedWorkspace.workCost_formula (block k w.length) (w++[false]).length
  have he : (workspacePolynomial (blockPolynomial k) (Polynomial.X+1)).eval w.length =
      Source284TwoSidedWorkspace.workCost (block k w.length) (w++[false]).length := by
    simp [workspacePolynomial,Polynomial.eval_add,Polynomial.eval_mul,blockPolynomial_eval,
      Source284TwoSidedWorkspace.workCost_formula]
  unfold totalCost
  simp only [costPolynomial,Polynomial.eval_add,he]
  omega

/-- The stage count is chosen from the desired polynomial once. For every
raw frame, the left half and the right scratch suffix each have at least the
requested number of zeros; the complete paid source run is polynomially
bounded in parsed input length. -/
theorem source_polynomial_workspace (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ (w : List Bool) (certificate suffix : Nat), ∃ left scratch,
      Source284Relative.run (description k states continuation)
        (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost k w) =
          ⟨left,2*flipped (w++[false]) (2^(p.eval w.length)*scratch),active (634+287*k)⟩ ∧
      2^(p.eval w.length) ∣ left ∧ totalCost k w ≤ (costPolynomial k).eval w.length := by
  obtain ⟨k,hk⟩ := Source284PositivePolynomialRunway.block_dominates p
  refine ⟨k,?_⟩
  intro w certificate suffix
  let m := block k w.length
  let tail := pairTape (List.replicate (outerAfter k (w.length+2) (w.length+2)) false)
    (historyAfter k (w.length+2) (w.length+2) certificate)
  let rem := retained k w.length suffix
  have hsize : p.eval w.length ≤ m+1 := by dsimp [m]; have h := hk w.length; omega
  have hpow : 2^(p.eval w.length) ∣ 2^(m+1) := Nat.pow_dvd_pow 2 hsize
  have hfour : 4^(m+1) = 2^(m+1)*2^(m+1) := by rw [← mul_pow]; norm_num
  have hprefix : 2^(m+1)*rem = 2^(p.eval w.length)*(2^(m+1-p.eval w.length)*rem) := by
    have he : m+1 = p.eval w.length+(m+1-p.eval w.length) := by omega
    conv_lhs => rw [he,pow_add]
    ring
  refine ⟨4^(m+1)*tail,2^(m+1-p.eval w.length)*rem,?_,?_,totalCost_polynomial k w⟩
  · have h := source_then k states continuation w certificate suffix 0 hn hv
    simpa [m,tail,rem,hprefix,run,shiftConfig,toSource,nextState] using h
  · rw [hfour]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpow _) tail

/-- Every numeric input has a parsed frame. The fixed program supplies the
requested zero prefixes for that frame and for every initial certificate. -/
theorem source_all_inputs (p : Polynomial Nat) (states : Nat)
    (continuation : Nat → Bool → Row) (hn : 0 < states) (hv : Closed states continuation) :
    ∃ k : Nat, ∀ input certificate : Nat, ∃ (w : List Bool) (suffix left scratch : Nat),
      encodeFrame w suffix = input ∧ w.length = Source284Parser.length input ∧
      Source284Relative.run (description k states continuation) (Source284Relative.initial input certificate)
        (totalCost k w) =
          ⟨left,2*flipped (w++[false])
            (2^(p.eval (Source284Parser.length input))*scratch),active (634+287*k)⟩ ∧
      2^(p.eval (Source284Parser.length input)) ∣ left ∧
      totalCost k w ≤ (costPolynomial k).eval (Source284Parser.length input) := by
  obtain ⟨k,hk⟩ := source_polynomial_workspace p states continuation hn hv
  refine ⟨k,?_⟩
  intro input certificate
  obtain ⟨w,suffix,hw⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hw]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  obtain ⟨left,scratch,hr,hd,hcost⟩ := hk w certificate suffix
  refine ⟨w,suffix,left,scratch,hw,hlen.symm,?_,?_,?_⟩
  · simpa [hw,hlen] using hr
  · simpa [hlen] using hd
  · simpa [hlen] using hcost

end Shared.Beeping.NPcoNP.Source284PositivePolynomialTwoSided
