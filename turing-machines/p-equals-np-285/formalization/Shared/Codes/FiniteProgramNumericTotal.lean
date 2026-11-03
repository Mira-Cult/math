import Shared.Codes.FiniteProgramPairBoolean
import Shared.ComplexityBridge.TM2PairTotalPoly
set_option maxHeartbeats 3000000
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-! Compile the proved totalized numeric pair checker to the linked finite
program. Timeout and malformed outputs are deliberately mapped to false, as
in `boundedNumeric`; this is not the option-preserving compiler contract. -/
namespace Shared.Codes.FiniteProgramNumericTotal
open Shared.Codes.FinitePrograms
open Shared.Codes.TM2Program (programValid)
open Shared.Codes.TM2StatementValidation
open Shared.ComplexityBridge.TM2BooleanInput
open Shared.ComplexityBridge.TM2PairTotalPoly
open Shared.ComplexityBridge.TM2BinaryPostCosts

/-- The totalizer's two Boolean auxiliary stacks and its finite numeric
    stacks all have finite alphabets. -/
@[instance_reducible] def alphabet (ks symbols : Nat) (j : Shared.ComplexityBridge.TM2PairTotalizer.Key ks) :
    Fintype (Shared.ComplexityBridge.TM2PairTotalizer.Alphabet ks symbols j) := by
  cases j <;> infer_instance

abbrev machine (d : InputData) (k : Nat) (p : Shared.Codes.TM2Program.Program) (output z one : Nat) :=
  Shared.ComplexityBridge.TM2PairTotalizer.machine d.stackCount d.states d.symbols k p
    d.inputStack output d.main d.initialState d.falseSymbol d.trueSymbol z one

/-- A fixed linked table computes the totalized numeric checker on all pairs.
The clock is the explicit initializer time, handoff, and TM2 simulator fuel;
no claim is made here that this is the option-valued checker. -/
theorem compile_totalized (d : InputData) (k : Nat) (p : Shared.Codes.TM2Program.Program)
    (output z one : Nat) (hdata : validInputData d = true) (hmain : d.main < p.length)
    (hp : programValid p d.stackCount d.states d.symbols = true) (hout : output < d.stackCount) :
    let tm := machine d k p output z one
    let alph := alphabet d.stackCount d.symbols
    let poly := Shared.ComplexityBridge.TM2PairTotalPoly.timePolynomial d.stackCount k p
    ∃ (width : Nat) (enc : Alphabet tm → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet tm) (eval : Program),
      enc default = List.Vector.replicate width false ∧ (∀ a, dec (enc a) = a) ∧
      valid eval = true ∧
      (let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true false
       let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true true
       let zz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false false
       let oo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false true
       valid (Shared.Codes.FiniteProgramPairContinuation.program mz mo zz oo width eval) = true) ∧
      ∀ x w,
        let bits := BitstringEncoding.bitEncode (x,w)
        let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true false
        let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) true true
        let zz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false false
        let oo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc (Equiv.refl Bool) false true
        bounded (Shared.Codes.FiniteProgramPairContinuation.program mz mo zz oo width eval) bits
          (Shared.Codes.FiniteProgramPairUnified.runtime mz mo zz oo x w width + 2 +
            ((2*timePolynomial tm alph enc dec poly+1).eval bits.length)) =
          some (boundedNumeric d k p output z one (x,w)) := by
  let tm := machine d k p output z one
  let alph := alphabet d.stackCount d.symbols
  let poly := Shared.ComplexityBridge.TM2PairTotalPoly.timePolynomial d.stackCount k p
  letI : DecidableEq (tm.Γ tm.k₁) := by
    change DecidableEq Bool
    infer_instance
  let R : List Bool → List Bool → Bool := fun x w => boundedNumeric d k p output z one (x,w)
  have hs : ∀ x w, ∃ n ≤ poly.eval ((BitstringEncoding.bitEncode (x,w)).map (Equiv.refl Bool).symm).length,
      Shared.ComplexityBridge.TM2Symbols.runSteps tm.step n
        (Turing.initList tm ((BitstringEncoding.bitEncode (x,w)).map (Equiv.refl Bool).symm)) =
          some (Turing.haltList tm [if R x w then true else false]) := by
    intro x w
    simp only [Equiv.refl_symm, Equiv.coe_refl, List.map_id]
    have h := boundedNumeric_run d k p output z one hdata hmain hp hout x w
    cases hb : R x w <;> simpa [tm,machine,poly,R,List.map_id,hb] using h
  have h := Shared.Codes.FiniteProgramPairBoolean.total_pair_evaluator tm alph false true Bool.false_ne_true
    (Equiv.refl Bool) poly R hs
  simpa [tm,alph,poly,R] using h

end Shared.Codes.FiniteProgramNumericTotal
