import Shared.ComplexityBridge.CircuitWitness

/-! Closed forms for the actual accepting output wire. This is a semantic
arithmetic result; polynomial-time code for the arithmetic remains separate. -/
namespace Shared.ComplexityBridge.CircuitOutputClosed
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.ComplexityBridge.CircuitTable

/-- The row selector's final wire is determined by its row count, even when
the table is empty. -/
theorem rowOutput_closed (rows : List (Bool × Bool)) (acc : Nat) :
    rowOutput (acc+1) acc rows = acc+4*rows.length := by
  induction rows generalizing acc with
  | nil => simp [rowOutput]
  | cons row rows ih =>
    simp only [rowOutput,List.length_cons]
    have he : acc+1+4 = (acc+4)+1 := by omega
    have ha : acc+1+3 = acc+4 := by omega
    rw [he,ha,ih]
    omega

theorem lookupOutput_closed (n : Nat) (rows : List (Bool × Bool)) :
    lookupOutput n rows = n+2+4*rows.length := by
  change rowOutput (n+3) (n+2) rows = _
  have he : n+3 = (n+2)+1 := by omega
  rw [he,rowOutput_closed]

theorem tableResult_closed (p : Program) (read : Nat) (project : Row → Bool) (base : Nat) :
    tableResult p read project base = base+1+4*p.length := by
  unfold tableResult
  rw [lookupOutput_closed]
  simp only [projectRows,List.length_map]
  have hnot : ¬ p.length+2+4*p.length < p.length+1 := by omega
  simp [remap,hnot]
  omega

theorem nextStateOutput_closed (p : Program) (k base j : Nat) :
    nextStateOutput p k base j = base + (programMoveGates p k base).length +
      j*(2+4*p.length) + 1+4*p.length := by
  simp only [nextStateOutput,stateResult,tableResult_closed,Nat.zero_add]

/-- A component whose update output is a newly appended gate has an explicit
reference after any positive number of copies, independent of the intermediate
reference lists. -/
theorem finalRefs_fresh (width : Nat) (gates : List Gate) (outputs inputs : List Nat)
    (base j delta n : Nat) (h : outputs[j]? = some (width+delta)) :
    ((finalRefs width gates outputs base inputs (n+1))[j]?).getD 0 =
      base+n*gates.length+delta := by
  induction n generalizing base inputs with
  | zero =>
    simp only [finalRefs,nextRefs,List.getElem?_map,h,Option.map_some,Option.getD_some,Nat.zero_mul,Nat.add_zero]
    simp [remap]
  | succ n ih =>
    change ((finalRefs width gates outputs (base+gates.length)
      (nextRefs width base inputs outputs) (n+1))[j]?).getD 0 = _
    rw [ih]
    simp [Nat.succ_mul,Nat.add_assoc,Nat.add_comm]

/-- The accepting state output is a fresh wire at a fixed offset in the
single-step circuit, regardless of the original program rows. -/
theorem accepting_output_fresh (p : Program) (input : List Bool) (fuel : Nat) :
    let pp := totalProgram p
    let width := circuitWidth p input fuel
    let k := window input fuel
    let j := trueState p
    (updateOutputs p input fuel)[j]? = some
      (width + ((programMoveGates pp k width).length + j*(2+4*pp.length) + 1+4*pp.length)) := by
  dsimp only
  let pp := totalProgram p
  let width := circuitWidth p input fuel
  let k := window input fuel
  let j := trueState p
  have hj : j < pp.length := by simp [j,pp,trueState,totalProgram_length]
  have hout := continuingOutputs_state pp k width j hj
  have hh : (continuingOutputs pp k width)[j]? = some (nextStateOutput pp k width j) := by
    have he : j < (continuingOutputs pp k width).length := by
      rw [continuingOutputs_length]
      simp only [inputWidth]
      omega
    have heq := List.getElem?_eq_getElem he
    rw [heq] at hout
    rw [heq]
    simpa only [Option.getD_some] using congrArg some hout
  change (continuingOutputs pp k width)[j]? = some
    (width + ((programMoveGates pp k width).length+j*(2+4*pp.length)+1+4*pp.length))
  rw [hh,nextStateOutput_closed]
  simp [Nat.add_assoc]

/-- For positive fuel, the unrelocated accepting wire has a closed form;
no computation of `finalRefs` is needed. -/
theorem acceptIndex_succ (p : Program) (input : List Bool) (n : Nat) :
    let fuel := n+1
    let pp := totalProgram p
    let width := circuitWidth p input fuel
    let k := window input fuel
    let j := trueState p
    acceptIndex p input fuel = width+n*(updateGates p input fuel).length+
      ((programMoveGates pp k width).length+j*(2+4*pp.length)+1+4*pp.length) := by
  dsimp only
  unfold acceptIndex
  have h := accepting_output_fresh p input (n+1)
  have hf := finalRefs_fresh (circuitWidth p input (n+1)) (updateGates p input (n+1))
    (updateOutputs p input (n+1)) (List.range (circuitWidth p input (n+1)))
    (circuitWidth p input (n+1)) (trueState p)
    ((programMoveGates (totalProgram p) (window input (n+1)) (circuitWidth p input (n+1))).length+
      trueState p*(2+4*(totalProgram p).length)+1+4*(totalProgram p).length) n h
  exact hf

theorem acceptIndex_zero (p : Program) (input : List Bool) :
    acceptIndex p input 0 = trueState p := by
  unfold acceptIndex
  simp only [finalRefs]
  have h : trueState p < circuitWidth p input 0 := by
    have hp : trueState p < (totalProgram p).length := by simp [trueState,totalProgram_length]
    simp only [circuitWidth,inputWidth]
    omega
  simp [h]

/-- With zero fuel the accepting wire remains the initial state wire. -/
theorem witnessOutput_zero (p : Program) (publicBits : List Bool) (count : Nat) :
    witnessOutput p publicBits count 0 = trueState p := by
  let input := dummyInput publicBits count
  let width := circuitWidth p input 0
  have hstate : trueState p < (totalProgram p).length := by simp [trueState,totalProgram_length]
  have hw : trueState p < width := by
    dsimp [width,circuitWidth,inputWidth]
    omega
  have hstart : trueState p < witnessStart p publicBits count 0 := by
    dsimp [witnessStart,inputStart,window,input]
    omega
  unfold witnessOutput
  change remap width (width+count) (refs p publicBits count 0) (acceptIndex p input 0) = _
  rw [acceptIndex_zero]
  simp only [remap,if_pos hw,refs]
  change ((patchRefs width (witnessStart p publicBits count 0) count)[trueState p]?).getD 0 = _
  rw [patchRefs_get _ _ _ _ hw]
  simp [show ¬ witnessStart p publicBits count 0 ≤ trueState p by omega]

/-- For positive fuel the relocated output is a fresh gate wire, so the
witness relocation adds exactly the number of free wires. -/
theorem witnessOutput_succ (p : Program) (publicBits : List Bool) (count n : Nat) :
    let fuel := n+1
    let input := dummyInput publicBits count
    let pp := totalProgram p
    let width := circuitWidth p input fuel
    let k := window input fuel
    let j := trueState p
    witnessOutput p publicBits count fuel = width+count+n*(updateGates p input fuel).length+
      ((programMoveGates pp k width).length+j*(2+4*pp.length)+1+4*pp.length) := by
  dsimp only
  let input := dummyInput publicBits count
  let width := circuitWidth p input (n+1)
  let delta := (programMoveGates (totalProgram p) (window input (n+1)) width).length+
    trueState p*(2+4*(totalProgram p).length)+1+4*(totalProgram p).length
  have ha : acceptIndex p input (n+1) = width+n*(updateGates p input (n+1)).length+delta :=
    acceptIndex_succ p input n
  have hw : width ≤ acceptIndex p input (n+1) := by rw [ha]; omega
  unfold witnessOutput
  change remap width (width+count) (refs p publicBits count (n+1)) (acceptIndex p input (n+1)) = _
  simp only [remap,if_neg (show ¬ acceptIndex p input (n+1) < width by omega)]
  rw [ha]
  dsimp only [input,width,delta]
  omega

/-- Fully arithmetic positive-fuel wire index. It uses only the fixed
program length and the actual public, witness and fuel lengths. No gate list
or iterated reference list is evaluated on the right-hand side. -/
theorem witnessOutput_succ_arithmetic (p : Program) (publicBits : List Bool) (count n : Nat) :
    let m := p.length+3
    let k := publicBits.length+count+(n+1)
    let move := 2*(2+4*m)+(1+4*(2*k+1))
    let oneStep := move+m*(2+4*m)
    witnessOutput p publicBits count (n+1) =
      (m+(2*k+1))+count+n*oneStep+(move+(p.length+2)*(2+4*m)+1+4*m) := by
  have h := witnessOutput_succ p publicBits count n
  simpa only [CircuitBounded.updateGates,CircuitBounded.circuitWidth,CircuitBounded.window,
    CircuitWitness.dummyInput,CircuitProgramMove.continuingGates_length,
    CircuitProgramMove.programMoveGates_length,CircuitProgramMove.inputWidth,
    totalProgram_length,trueState,List.length_append,List.length_replicate] using h

namespace Fixtures
example : lookupOutput 2 [(false,true),(true,false)] = 12 := rfl
example : acceptIndex [] [] 0 = 2 := rfl
end Fixtures
end Shared.ComplexityBridge.CircuitOutputClosed
