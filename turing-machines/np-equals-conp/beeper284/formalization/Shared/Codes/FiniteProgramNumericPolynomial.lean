import Shared.Codes.FiniteProgramNumericTotal
import Shared.Codes.FiniteProgramPairPolynomial
set_option maxHeartbeats 3000000

/-! Normalize the complete totalized numeric evaluator to one polynomial
clock in canonical encoded-pair length. The option-valued adapter remains
separate. -/
namespace Shared.Codes.FiniteProgramNumericPolynomial
open Shared.Codes.FinitePrograms
open Shared.Codes.TM2Program (programValid)
open Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2PairTotalPoly
open Shared.ComplexityBridge.TM2BinaryPostCosts

private theorem bounded_mono (p : Program) (input : List Bool) (small large : Nat) (b : Bool)
    (hle : small ≤ large) (h : bounded p input small = some b) : bounded p input large = some b := by
  obtain ⟨t,ht,hr⟩ := (bounded_iff_result p input small b).1 h
  exact (bounded_iff_result p input large b).2 ⟨t,le_trans ht hle,hr⟩

/-- For each validated numeric source, one literal finite program and one
polynomial compute its totalized Boolean result on every canonical pair. -/
theorem compile_totalized_polynomial (d : InputData) (k : Nat) (p : Shared.Codes.TM2Program.Program)
    (output z one : Nat) (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
        (clock.eval (BitstringEncoding.bitEncode (x,w)).length) =
          some (boundedNumeric d k p output z one (x,w)) := by
  let tm := Shared.Codes.FiniteProgramNumericTotal.machine d k p output z one
  let alph := Shared.Codes.FiniteProgramNumericTotal.alphabet d.stackCount d.symbols
  let poly := Shared.ComplexityBridge.TM2PairTotalPoly.timePolynomial d.stackCount k p
  obtain ⟨width,enc,dec,eval,hblank,hinv,hvalid,hlinked,hcomp⟩ :=
    Shared.Codes.FiniteProgramNumericTotal.compile_totalized d k p output z one hdata hmain hp hout
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true true
  let zz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false false
  let oo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false true
  let code := Shared.Codes.FiniteProgramPairContinuation.program mz mo zz oo width eval
  let clock := Shared.Codes.FiniteProgramPairPolynomial.polynomial mz zz oo width + Polynomial.C 2 +
    (2*timePolynomial tm alph enc dec poly+1)
  refine ⟨code,clock,hlinked,?_⟩
  intro x w
  have hm : mz.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc (Equiv.refl Bool) true false
  have hz : zz.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc (Equiv.refl Bool) false false
  have ho : oo.length = width := Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc (Equiv.refl Bool) false true
  have hb := Shared.Codes.FiniteProgramPairPolynomial.runtime_polynomial mz mo zz oo x w width hm hz ho
  have he : Shared.Codes.FiniteProgramPairUnified.runtime mz mo zz oo x w width + 2 +
        ((2*timePolynomial tm alph enc dec poly+1).eval (BitstringEncoding.bitEncode (x,w)).length) ≤
      clock.eval (BitstringEncoding.bitEncode (x,w)).length := by
    simp only [clock,Polynomial.eval_add,Polynomial.eval_C]
    omega
  have hc := hcomp x w
  change bounded code (BitstringEncoding.bitEncode (x,w))
    (Shared.Codes.FiniteProgramPairUnified.runtime mz mo zz oo x w width + 2 +
      ((2*timePolynomial tm alph enc dec poly+1).eval (BitstringEncoding.bitEncode (x,w)).length)) = _ at hc
  exact bounded_mono code _ _ _ _ he hc


/-- A validated checked candidate is compiled with its `none` outcome
    explicitly totalized to false. -/
theorem compile_checked_totalized (candidate : Shared.Codes.TM2Candidate.Candidate)
    (p : Shared.Codes.TM2Program.Program)
    (hdecode : Shared.Codes.TM2Program.decodeProgram candidate.1.1 = some p)
    (hdata : validInputData (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2) = true)
    (hmain : (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).main < p.length)
    (hp : programValid p (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).stackCount
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).states
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).symbols = true)
    (hout : candidate.2.2.2 < (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).stackCount) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
        (clock.eval (BitstringEncoding.bitEncode (x,w)).length) =
          some ((Shared.Codes.TM2PairCandidate.evaluate candidate x w).getD false) := by
  let d := Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2
  obtain ⟨program,clock,hvalid,h⟩ := compile_totalized_polynomial d candidate.1.2.1 p
    candidate.2.2.2 candidate.2.1 candidate.2.2.1 hdata hmain hp hout
  refine ⟨program,clock,hvalid,?_⟩
  intro x w
  rw [Shared.ComplexityBridge.TM2PairTotalPoly.evaluate_total_eq candidate p hdecode hdata hp x w]
  exact h x w

/-- Option-valued correctness follows for a candidate only when every test
    has separately been proved to return a Boolean. -/
theorem compile_checked_if_total (candidate : Shared.Codes.TM2Candidate.Candidate)
    (p : Shared.Codes.TM2Program.Program)
    (hdecode : Shared.Codes.TM2Program.decodeProgram candidate.1.1 = some p)
    (hdata : validInputData (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2) = true)
    (hmain : (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).main < p.length)
    (hp : programValid p (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).stackCount
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).states
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).symbols = true)
    (hout : candidate.2.2.2 < (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw candidate.1.2.2).stackCount)
    (htotal : ∀ x w, ∃ b, Shared.Codes.TM2PairCandidate.evaluate candidate x w = some b) :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x w, bounded program (BitstringEncoding.bitEncode (x,w))
        (clock.eval (BitstringEncoding.bitEncode (x,w)).length) =
          Shared.Codes.TM2PairCandidate.evaluate candidate x w := by
  obtain ⟨program,clock,hvalid,h⟩ := compile_checked_totalized candidate p hdecode hdata hmain hp hout
  refine ⟨program,clock,hvalid,?_⟩
  intro x w
  obtain ⟨b,hb⟩ := htotal x w
  rw [hb]
  simpa [hb] using h x w

end Shared.Codes.FiniteProgramNumericPolynomial
