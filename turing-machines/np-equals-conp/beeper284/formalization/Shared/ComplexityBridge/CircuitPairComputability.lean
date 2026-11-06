import Shared.ComplexityBridge.CircuitGateComputability
import Shared.ComplexityBridge.CircuitPairWitness

/-! Effective construction of the witness-shape clauses and assembly of the
fixed-witness formula. Time bounds and circuit generation remain separate. -/
namespace Shared.ComplexityBridge.CircuitPairComputability

open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitPairWitness
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitGateComputability
open Shared.ComplexityBridge.UnaryBounded
open Shared.Codes.VerifierPrograms
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitProgramMove

def shapeSuffix (endIndex : Nat) : Nat → Formula
  | 0 => []
  | n+1 => [(endIndex-3*(n+1),true)] :: [(endIndex-3*(n+1)+2,false)] :: shapeSuffix endIndex n

theorem shapeSuffix_correct (n base : Nat) : shapeSuffix (base+3*n) n = shapeClauses base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [shapeSuffix,shapeClauses]
    have he : base+3*(n+1)-3*(n+1) = base := by omega
    have hn : base+3*(n+1) = (base+3)+3*n := by omega
    rw [he,hn,ih]

theorem shapeSuffix_primrec : Primrec₂ shapeSuffix := by
  let A := Nat × Nat
  let S := Nat × Formula
  have hstep : Primrec₂ (fun (a : A) (s : S) =>
      [(a.1-3*(s.1+1),true)] :: [(a.1-3*(s.1+1)+2,false)] :: s.2) := by
    have hi : Primrec (fun z : A × S => z.1.1-3*(z.2.1+1)) :=
      Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
    have hi2 : Primrec (fun z : A × S => z.1.1-3*(z.2.1+1)+2) :=
      Primrec.nat_add.comp hi (Primrec.const 2)
    have htrue : Primrec (fun z : A × S => [(z.1.1-3*(z.2.1+1),true)]) :=
      Primrec.list_cons.comp (Primrec.pair hi (Primrec.const true)) (Primrec.const [])
    have hfalse : Primrec (fun z : A × S => [(z.1.1-3*(z.2.1+1)+2,false)]) :=
      Primrec.list_cons.comp (Primrec.pair hi2 (Primrec.const false)) (Primrec.const [])
    exact (Primrec.list_cons.comp htrue (Primrec.list_cons.comp hfalse (Primrec.snd.comp Primrec.snd))).to₂
  have h := Primrec.nat_rec' (Primrec.snd : Primrec (fun a : A => a.2)) (Primrec.const ([] : Formula)) hstep
  apply h.to₂.of_eq
  intro endIndex n
  induction n with
  | zero => rfl
  | succ n ih => simp [shapeSuffix,ih]

theorem shapeClauses_primrec : Primrec₂ shapeClauses := by
  have h := shapeSuffix_primrec.comp
    (Primrec.nat_add.comp (Primrec.fst : Primrec (fun z : Nat × Nat => z.1))
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd)) Primrec.snd
  apply h.to₂.of_eq
  intro base n
  exact shapeSuffix_correct n base

abbrev AssemblyArg := List Bool × Nat × Nat × List Gate

theorem constrainedFormula_primrec : Primrec (fun z : AssemblyArg =>
    constrainedFormula z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hfixed : Primrec (fun z : AssemblyArg => z.1) := Primrec.fst
  have hn : Primrec (fun z : AssemblyArg => z.2.1) := Primrec.fst.comp Primrec.snd
  have hout : Primrec (fun z : AssemblyArg => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hgates : Primrec (fun z : AssemblyArg => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hshape := shapeClauses_primrec.comp (Primrec.list_length.comp hfixed) hn
  have hfree := Primrec.nat_mul.comp (Primrec.const 3) hn
  have hcompile := compileFixed_primrec.comp (Primrec.pair hfixed (Primrec.pair hfree (Primrec.pair hout hgates)))
  exact Primrec.list_append.comp hshape hcompile

theorem pairPrefix_primrec : Primrec pairPrefix :=
  delimit_primrec.comp bitListEncoding_primrec

theorem initialState_zero (p : Program) : initialState p = 0 := by
  unfold initialState invalidState
  split <;> omega

def directCircuitInput (p : Program) (input : List Bool) (fuel : Nat) : List Bool :=
  (List.range (circuitWidth p input fuel)).map fun i =>
    if i < (totalProgram p).length then decide (i = initialState p)
    else if i < inputStart p input fuel then false
    else wire input (i-inputStart p input fuel)

theorem directCircuitInput_correct (p : Program) (input : List Bool) (fuel : Nat) :
    directCircuitInput p input fuel = circuitInput p input fuel := by
  apply List.ext_getElem
  · simp [directCircuitInput,circuitInput_length]
  · intro i hi hj
    have hh := input_bit p input fuel i (by simpa [circuitInput_length] using hj)
    simpa [directCircuitInput,wire,List.getElem?_eq_getElem hj] using hh.symm

theorem circuitWidth_primrec : Primrec (fun z : Program × List Bool × Nat => circuitWidth z.1 z.2.1 z.2.2) := by
  let A := Program × List Bool × Nat
  have hp : Primrec (fun z : A => z.1.length+3) :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 3)
  have hw : Primrec (fun z : A => z.2.1.length+z.2.2) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have h := Primrec.nat_add.comp hp (Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 2) hw))
  apply h.of_eq
  intro z
  simp [circuitWidth,inputWidth,totalProgram_length,window]

theorem inputStart_primrec : Primrec (fun z : Program × List Bool × Nat => inputStart z.1 z.2.1 z.2.2) := by
  let A := Program × List Bool × Nat
  have hp : Primrec (fun z : A => z.1.length+3) :=
    Primrec.nat_add.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 3)
  have hw : Primrec (fun z : A => z.2.1.length+z.2.2) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.nat_add.comp hp hw).of_eq
  intro z
  simp [inputStart,totalProgram_length,window]

theorem directCircuitInput_primrec : Primrec (fun z : Program × List Bool × Nat =>
    directCircuitInput z.1 z.2.1 z.2.2) := by
  let A := Program × List Bool × Nat
  let B := A × Nat
  have hstates : Primrec (fun z : B => z.1.1.length+3) :=
    Primrec.nat_add.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 3)
  have hi : Primrec (fun z : B => z.2) := Primrec.snd
  have hstart : Primrec (fun z : B => inputStart z.1.1 z.1.2.1 z.1.2.2) := inputStart_primrec.comp Primrec.fst
  have hinput : Primrec (fun z : B => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hbit : Primrec (fun z : B => (z.1.2.1[z.2-inputStart z.1.1 z.1.2.1 z.1.2.2]?).getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp hinput (Primrec.nat_sub.comp hi hstart)) (Primrec.const false)
  have hhead := (Primrec.eq.comp hi (Primrec.const 0)).decide
  have htest := Primrec.ite (Primrec.nat_lt.comp hi hstates) hhead
    (Primrec.ite (Primrec.nat_lt.comp hi hstart) (Primrec.const false) hbit)
  have hmap := Primrec.list_map (Primrec.list_range.comp circuitWidth_primrec) htest.to₂
  apply hmap.of_eq
  intro z
  simp [directCircuitInput,totalProgram_length,initialState_zero,wire]

theorem circuitInput_primrec : Primrec (fun z : Program × List Bool × Nat =>
    circuitInput z.1 z.2.1 z.2.2) := by
  apply directCircuitInput_primrec.of_eq
  intro z
  exact directCircuitInput_correct z.1 z.2.1 z.2.2

theorem replicateFalse_primrec : Primrec (fun n : Nat => List.replicate n false) := by
  have hstep : Primrec₂ (fun (_ : Nat) (bits : List Bool) => false::bits) :=
    (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂
  have h := Primrec.nat_rec₁ ([] : List Bool) hstep
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih,List.replicate_succ]

theorem dummyInput_primrec : Primrec₂ dummyInput :=
  (Primrec.list_append.comp (Primrec.fst : Primrec (fun z : List Bool × Nat => z.1))
    (replicateFalse_primrec.comp Primrec.snd)).to₂

theorem template_primrec : Primrec (fun z : Decoded => template z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => z.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact circuitInput_primrec.comp (Primrec.pair hp (Primrec.pair (dummyInput_primrec.comp hx hn) ht))

/-- The remaining hypotheses concern the actual initial wires, output wire,
and gates of the bounded computation circuit. -/
theorem pairFormula_primrec_of_circuit
    (htemplate : Primrec (fun z : Decoded => template z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hout : Primrec (fun z : Decoded => witnessOutput z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hgates : Primrec (fun z : Decoded => witnessGates z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Primrec (fun z : Decoded => pairFormula z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : Primrec (fun z : Decoded => z.1) := Primrec.fst
  have hx : Primrec (fun z : Decoded => pairPrefix z.2.1) :=
    pairPrefix_primrec.comp (Primrec.fst.comp Primrec.snd)
  have hn : Primrec (fun z : Decoded => z.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun z : Decoded => z.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hinput : Primrec (fun z : Decoded => (z.1,pairPrefix z.2.1,3*z.2.2.1,z.2.2.2)) :=
    Primrec.pair hp (Primrec.pair hx (Primrec.pair (Primrec.nat_mul.comp (Primrec.const 3) hn) ht))
  exact constrainedFormula_primrec.comp (Primrec.pair (htemplate.comp hinput)
    (Primrec.pair hn (Primrec.pair (hout.comp hinput) (hgates.comp hinput))))

theorem reduction_primrec_of_circuit
    (htemplate : Primrec (fun z : Decoded => template z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hout : Primrec (fun z : Decoded => witnessOutput z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hgates : Primrec (fun z : Decoded => witnessGates z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Primrec reduction :=
  Shared.ComplexityBridge.CNFEncodingComputability.reduction_primrec_of_pair
    (pairFormula_primrec_of_circuit htemplate hout hgates)

/-- The initial wires are now discharged; only the output-index and gate-list
generators remain as recursion-theoretic obligations. -/
theorem reduction_primrec_of_outputs
    (hout : Primrec (fun z : Decoded => witnessOutput z.1 z.2.1 z.2.2.1 z.2.2.2))
    (hgates : Primrec (fun z : Decoded => witnessGates z.1 z.2.1 z.2.2.1 z.2.2.2)) :
    Primrec reduction := reduction_primrec_of_circuit template_primrec hout hgates

namespace Fixtures
example : shapeSuffix 9 2 = shapeClauses 3 2 := by decide
example : directCircuitInput [] [] 0 = circuitInput [] [] 0 := by decide
end Fixtures

end Shared.ComplexityBridge.CircuitPairComputability
