import Shared.ComplexityBridge.CircuitBounded

/-! Free-witness wiring for bounded finite-program acceptance. Witnesses are
raw bit lists of a fixed length and are appended to a fixed raw input publicBits.
This does not by itself establish the canonical NP pair-encoding bridge or a
polynomial bit-cost implementation of the generator. -/
namespace Shared.ComplexityBridge.CircuitWitness
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.ComplexityBridge.CircuitTapeMove

def initialState (p : Program) : Nat := if 0 < p.length then 0 else invalidState p

def inputStart (p : Program) (input : List Bool) (fuel : Nat) : Nat :=
  (totalProgram p).length+window input fuel

theorem input_bit (p : Program) (input : List Bool) (fuel i : Nat)
    (hi : i < circuitWidth p input fuel) :
    wire (circuitInput p input fuel) i =
      if i < (totalProgram p).length then decide (i = initialState p)
      else if i < inputStart p input fuel then false
      else wire input (i-inputStart p input fuel) := by
  let pp := totalProgram p
  let k := window input fuel
  let c := initialConfig p input
  have hc : c.1 = initialState p := by simp [c,initialConfig,embed,initial,initialState] <;> rfl
  change i < pp.length+(2*k+1) at hi
  by_cases hs : i < pp.length
  · have h := machineWires_state pp k c i hs
    simpa [c,pp,k,circuitInput,hc,hs] using h
  · by_cases hl : i < pp.length+k
    · let j := i-pp.length
      have hj : j < 2*k+1 := by dsimp [j]; omega
      have hjleft : j < k := by dsimp [j]; omega
      have he : pp.length+j = i := by dsimp [j]; omega
      have h := machineWires_tape pp k c j hj
      rw [he] at h
      simpa [c,pp,k,circuitInput,initialConfig,embed,initial,tapeView,hjleft,hs,hl,inputStart] using h
    · by_cases heq : i = pp.length+k
      · have hjw : k < 2*k+1 := by omega
        have h := machineWires_tape pp k c k hjw
        rw [←heq] at h
        have hidx : i-(pp.length+k) = 0 := by omega
        simpa [c,pp,k,circuitInput,initialConfig,embed,initial,tapeView,hs,hl,inputStart,hidx,wire,head_get] using h
      · let j := i-(pp.length+k)-1
        have hj : j < k := by dsimp [j]; omega
        have hjw : k+(j+1) < 2*k+1 := by omega
        have he : pp.length+(k+(j+1)) = i := by dsimp [j]; omega
        have h := machineWires_tape pp k c (k+(j+1)) hjw
        rw [he] at h
        have hidx : i-(pp.length+k) = j+1 := by dsimp [j]; omega
        have hlt : ¬k+(j+1) < k := by omega
        have hne : k+(j+1) ≠ k := by omega
        have hsub : k+(j+1)-k-1 = j := by omega
        have ht := tail_getD input j
        have hw : wire input (j+1) = (input.tail[j]?).getD false := by simpa [wire] using ht.symm
        simpa [c,pp,k,circuitInput,initialConfig,embed,initial,tapeView,hs,hl,inputStart,hidx,hlt,hne,hsub,hw] using h

theorem width_congr (p : Program) (a b : List Bool) (fuel : Nat) (h : a.length = b.length) :
    circuitWidth p a fuel = circuitWidth p b fuel := by simp [circuitWidth,window,h]

theorem start_congr (p : Program) (a b : List Bool) (fuel : Nat) (h : a.length = b.length) :
    inputStart p a fuel = inputStart p b fuel := by simp [inputStart,window,h]

theorem gates_congr (p : Program) (a b : List Bool) (fuel : Nat) (h : a.length = b.length) :
    circuitGates p a fuel = circuitGates p b fuel := by
  simp [circuitGates,updateGates,updateOutputs,circuitWidth,window,h]

theorem acceptIndex_congr (p : Program) (a b : List Bool) (fuel : Nat) (h : a.length = b.length) :
    acceptIndex p a fuel = acceptIndex p b fuel := by
  simp [acceptIndex,updateGates,updateOutputs,circuitWidth,window,h]

theorem wire_append_after (xs ys : List Bool) (j : Nat) :
    wire (xs++ys) (xs.length+j) = wire ys j := by
  simp [wire,List.getElem?_append_right]

theorem wire_outside (xs : List Bool) (j : Nat) (h : xs.length ≤ j) : wire xs j = false := by
  have hh : xs[j]? = none := List.getElem?_eq_none (by omega)
  simp [wire,hh]

/-- Inputs of equal length induce identical circuit bits wherever their raw
input bits agree. -/
theorem input_bit_congr (p : Program) (a b : List Bool) (fuel i : Nat)
    (hlen : a.length = b.length) (hi : i < circuitWidth p a fuel)
    (hraw : wire a (i-inputStart p a fuel) = wire b (i-inputStart p a fuel)) :
    wire (circuitInput p a fuel) i = wire (circuitInput p b fuel) i := by
  have hi' : i < circuitWidth p b fuel := by rw [←width_congr p a b fuel hlen]; exact hi
  rw [input_bit p a fuel i hi,input_bit p b fuel i hi',←start_congr p a b fuel hlen]
  split_ifs <;> simp_all

def dummyInput (publicBits : List Bool) (count : Nat) : List Bool := publicBits ++ List.replicate count false

def witnessStart (p : Program) (publicBits : List Bool) (count fuel : Nat) : Nat :=
  inputStart p (dummyInput publicBits count) fuel+publicBits.length

theorem witnessEnd_bound (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    witnessStart p publicBits count fuel+count ≤ circuitWidth p (dummyInput publicBits count) fuel := by
  simp [witnessStart,inputStart,circuitWidth,inputWidth,window,dummyInput]
  omega

/-- Each original circuit input is wired either to its pinned template bit or
to the corresponding freely chosen witness wire. -/
def patchRefs (width start count : Nat) : List Nat :=
  (List.range width).map fun i => if start ≤ i ∧ i < start+count then width+(i-start) else i

theorem patchRefs_get (width start count i : Nat) (hi : i < width) :
    ((patchRefs width start count)[i]?).getD 0 =
      if start ≤ i ∧ i < start+count then width+(i-start) else i := by
  simp [patchRefs,hi]

theorem patchRefs_bound (width start count : Nat) :
    ∀ i < width, ((patchRefs width start count)[i]?).getD 0 < width+count := by
  intro i hi
  rw [patchRefs_get width start count i hi]
  split_ifs <;> omega

/-- A template and an equally long witness input agree on every machine wire
outside the designated witness interval. -/
theorem input_agree_outside (p : Program) (publicBits witness : List Bool) (fuel i : Nat)
    (hi : i < circuitWidth p (dummyInput publicBits witness.length) fuel)
    (hout : ¬(witnessStart p publicBits witness.length fuel ≤ i ∧
      i < witnessStart p publicBits witness.length fuel+witness.length)) :
    wire (circuitInput p (dummyInput publicBits witness.length) fuel) i =
      wire (circuitInput p (publicBits++witness) fuel) i := by
  let a := dummyInput publicBits witness.length
  let b := publicBits++witness
  have hl : a.length = b.length := by simp [a,b,dummyInput]
  have hwidth := width_congr p a b fuel hl
  have hstart := start_congr p a b fuel hl
  by_cases hpre : i < inputStart p a fuel
  · have hi' : i < circuitWidth p b fuel := by rw [←hwidth]; exact hi
    rw [input_bit p a fuel i hi,input_bit p b fuel i hi',←hstart]
    split_ifs <;> simp_all
  · have hraw : wire a (i-inputStart p a fuel) = wire b (i-inputStart p a fuel) := by
      by_cases hb : i-inputStart p a fuel < publicBits.length
      · change wire (publicBits++List.replicate witness.length false) (i-inputStart p a fuel) =
            wire (publicBits++witness) (i-inputStart p a fuel)
        rw [wire_append publicBits _ _ hb,wire_append publicBits _ _ hb]
      · have hafter : publicBits.length+witness.length ≤ i-inputStart p a fuel := by
          dsimp [witnessStart] at hout
          change ¬(inputStart p a fuel+publicBits.length ≤ i ∧
            i < inputStart p a fuel+publicBits.length+witness.length) at hout
          omega
        have hal : a.length = publicBits.length+witness.length := by simp [a,dummyInput]
        have hbl : b.length = publicBits.length+witness.length := by simp [b]
        have ha : a.length ≤ i-inputStart p a fuel := by omega
        have hb' : b.length ≤ i-inputStart p a fuel := by omega
        rw [wire_outside a _ ha,wire_outside b _ hb']
    exact input_bit_congr p a b fuel i hl hi hraw

/-- A witness bit appears at its designated machine input position. -/
theorem input_witness_bit (p : Program) (publicBits witness : List Bool) (fuel j : Nat)
    (hj : j < witness.length) :
    wire (circuitInput p (publicBits++witness) fuel)
      (witnessStart p publicBits witness.length fuel+j) = wire witness j := by
  let a := dummyInput publicBits witness.length
  let b := publicBits++witness
  have hl : a.length = b.length := by simp [a,b,dummyInput]
  have hstart := start_congr p a b fuel hl
  have hwidth := width_congr p a b fuel hl
  have hend := witnessEnd_bound p publicBits witness.length fuel
  change witnessStart p publicBits witness.length fuel+witness.length ≤ circuitWidth p a fuel at hend
  have hi : witnessStart p publicBits witness.length fuel+j < circuitWidth p b fuel := by
    rw [←hwidth]
    omega
  rw [input_bit p b fuel _ hi]
  have hn : ¬witnessStart p publicBits witness.length fuel+j < (totalProgram p).length := by
    simp only [witnessStart,inputStart,window]
    omega
  have hh : ¬witnessStart p publicBits witness.length fuel+j < inputStart p b fuel := by
    rw [←hstart]
    dsimp [witnessStart]
    change ¬ inputStart p a fuel+publicBits.length+j < inputStart p a fuel
    omega
  have hidx : witnessStart p publicBits witness.length fuel+j-inputStart p b fuel = publicBits.length+j := by
    rw [←hstart]
    dsimp [witnessStart]
    change inputStart p a fuel+publicBits.length+j-inputStart p a fuel = publicBits.length+j
    omega
  simp only [if_neg hn,if_neg hh,hidx]
  exact wire_append_after publicBits witness j

/-- Relocating from the template plus free bits reconstructs exactly the
machine's initialized wires for the public input and the witness. -/
theorem patched_readState (p : Program) (publicBits witness : List Bool) (fuel : Nat) :
    readState
      (circuitInput p (dummyInput publicBits witness.length) fuel ++ witness)
      (circuitWidth p (dummyInput publicBits witness.length) fuel)
      (patchRefs (circuitWidth p (dummyInput publicBits witness.length) fuel)
        (witnessStart p publicBits witness.length fuel) witness.length) =
    circuitInput p (publicBits++witness) fuel := by
  let a := dummyInput publicBits witness.length
  let b := publicBits++witness
  let width := circuitWidth p a fuel
  let start := witnessStart p publicBits witness.length fuel
  let template := circuitInput p a fuel
  let refs := patchRefs width start witness.length
  have hl : a.length = b.length := by simp [a,b,dummyInput]
  have hw : circuitWidth p b fuel = width := (width_congr p a b fuel hl).symm
  have ht : template.length = width := circuitInput_length p a fuel
  have htarget : (circuitInput p b fuel).length = width := by rw [circuitInput_length,hw]
  apply List.ext_getElem
  · simpa only [readState_length] using htarget.symm
  · intro i hi₁ hi₂
    have hi : i < width := by simpa [readState_length] using hi₁
    rw [←wire_get _ i hi₁,readState_wire _ width refs i hi]
    rw [←wire_get _ i hi₂]
    rw [show ((refs[i]?).getD 0) =
      (if start ≤ i ∧ i < start+witness.length then width+(i-start) else i) from
      patchRefs_get width start witness.length i hi]
    by_cases hv : start ≤ i ∧ i < start+witness.length
    · simp only [if_pos hv]
      have hj : i-start < witness.length := by omega
      have he : start+(i-start) = i := by omega
      have hwire : wire (template++witness) (width+(i-start)) = wire witness (i-start) := by
        simpa [ht] using wire_append_after template witness (i-start)
      rw [hwire]
      have hh := input_witness_bit p publicBits witness fuel (i-start) hj
      change wire (circuitInput p b fuel) (start+(i-start)) = wire witness (i-start) at hh
      rw [he] at hh
      exact hh.symm
    · simp only [if_neg hv]
      rw [wire_append template witness i (by rw [ht]; exact hi)]
      exact input_agree_outside p publicBits witness fuel i hi hv

def template (p : Program) (publicBits : List Bool) (count fuel : Nat) : List Bool :=
  circuitInput p (dummyInput publicBits count) fuel

def innerWidth (p : Program) (publicBits : List Bool) (count fuel : Nat) : Nat :=
  circuitWidth p (dummyInput publicBits count) fuel

def refs (p : Program) (publicBits : List Bool) (count fuel : Nat) : List Nat :=
  patchRefs (innerWidth p publicBits count fuel) (witnessStart p publicBits count fuel) count

def witnessGates (p : Program) (publicBits : List Bool) (count fuel : Nat) : List Gate :=
  relocate (innerWidth p publicBits count fuel) (innerWidth p publicBits count fuel+count)
    (refs p publicBits count fuel) (circuitGates p (dummyInput publicBits count) fuel)

def witnessOutput (p : Program) (publicBits : List Bool) (count fuel : Nat) : Nat :=
  remap (innerWidth p publicBits count fuel) (innerWidth p publicBits count fuel+count)
    (refs p publicBits count fuel) (acceptIndex p (dummyInput publicBits count) fuel)

theorem template_length (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    (template p publicBits count fuel).length = innerWidth p publicBits count fuel := circuitInput_length _ _ _

theorem witnessGates_valid (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    validGates ((template p publicBits count fuel).length+count) (witnessGates p publicBits count fuel) := by
  rw [template_length]
  apply relocate_valid
  · exact patchRefs_bound _ _ _
  · exact circuitGates_valid _ _ _

theorem witnessOutput_bound (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    witnessOutput p publicBits count fuel <
      (template p publicBits count fuel).length+count+(witnessGates p publicBits count fuel).length := by
  let width := innerWidth p publicBits count fuel
  let base := width+count
  let pins := refs p publicBits count fuel
  let gates := circuitGates p (dummyInput publicBits count) fuel
  let out := acceptIndex p (dummyInput publicBits count) fuel
  have hr : ∀ i < width, (pins[i]?).getD 0 < base := patchRefs_bound _ _ _
  have ho : out < width+gates.length := acceptIndex_bound p (dummyInput publicBits count) fuel
  have h := remap_bound width base pins hr gates.length out ho
  simpa [witnessOutput,witnessGates,template_length,relocate_length,width,base,pins,gates,out,Nat.add_assoc] using h

/-- For every actual witness, the relocated circuit agrees with the bounded
program on the public input followed by that witness. -/
theorem witnessCircuit_correct (p : Program) (publicBits witness : List Bool) (fuel : Nat) :
    wire (simulate (template p publicBits witness.length fuel ++ witness)
        (witnessGates p publicBits witness.length fuel))
      (witnessOutput p publicBits witness.length fuel) = true ↔
    bounded p (publicBits++witness) fuel = some true := by
  let a := dummyInput publicBits witness.length
  let b := publicBits++witness
  let width := circuitWidth p a fuel
  let pins := refs p publicBits witness.length fuel
  let bits := template p publicBits witness.length fuel ++ witness
  have hl : a.length = b.length := by simp [a,b,dummyInput]
  have ht : (template p publicBits witness.length fuel).length = width := template_length _ _ _ _
  have hw : bits.length = width+witness.length := by simp [bits,ht]
  have hp : ∀ i < width, (pins[i]?).getD 0 < bits.length := by
    rw [hw]
    exact patchRefs_bound _ _ _
  have he := relocate_simulate bits width pins (circuitGates p a fuel) hp
    (circuitGates_valid p a fuel) (acceptIndex p a fuel) (acceptIndex_bound p a fuel)
  change wire (simulate bits (relocate width bits.length pins (circuitGates p a fuel)))
      (remap width bits.length pins (acceptIndex p a fuel)) =
    wire (simulate (readState bits width pins) (circuitGates p a fuel)) (acceptIndex p a fuel) at he
  rw [show readState bits width pins = circuitInput p b fuel from patched_readState p publicBits witness fuel] at he
  rw [hw] at he
  change wire (simulate (template p publicBits witness.length fuel ++ witness)
      (witnessGates p publicBits witness.length fuel)) (witnessOutput p publicBits witness.length fuel) =
    wire (simulate (circuitInput p b fuel) (circuitGates p a fuel)) (acceptIndex p a fuel) at he
  rw [gates_congr p a b fuel hl,acceptIndex_congr p a b fuel hl] at he
  rw [he]
  exact (bounded_true_iff_circuit p b fuel).symm

/-- Fixed template wires and a fixed total length decompose uniquely into
the template and a witness suffix of the requested length. -/
theorem fixed_decompose (fixed wires : List Bool) (count : Nat)
    (hlen : wires.length = fixed.length+count) (hf : Fixed (wire wires) 0 fixed) :
    ∃ witness : List Bool, witness.length = count ∧ wires = fixed++witness := by
  let first := wires.take fixed.length
  let rest := wires.drop fixed.length
  have hfirstlen : first.length = fixed.length := by simp [first,hlen]
  have hfirstfixed : Fixed (wire first) 0 fixed := by
    apply (Fixed_congr (wire wires) (wire first) 0 fixed ?_).1 hf
    intro i _ hi
    have hi' : i < fixed.length := by simpa using hi
    have he : wire first i = wire wires i := by
      simp only [first,wire,List.getElem?_take_of_lt hi']
    exact he.symm
  have he : first = fixed := fixed_list_eq fixed first hfirstlen hfirstfixed
  have hrest : rest.length = count := by simp [rest,hlen]
  refine ⟨rest,hrest,?_⟩
  have hsplit : first++rest = wires := List.take_append_drop fixed.length wires
  rw [he] at hsplit
  exact hsplit.symm

/-- The encoded formula pins the template and leaves exactly `count` raw
witness bits unconstrained. -/
def witnessFormula (p : Program) (publicBits : List Bool) (count fuel : Nat) : Formula :=
  compileFixed (template p publicBits count fuel) count (witnessOutput p publicBits count fuel)
    (witnessGates p publicBits count fuel)

/-- Sound and complete reduction of a fixed-length existential witness search
to the repository's actual canonical SAT language. -/
theorem sat_witnessFormula_iff (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    sat (BitstringEncoding.bitEncode (witnessFormula p publicBits count fuel)) = true ↔
      ∃ witness : List Bool, witness.length = count ∧ bounded p (publicBits++witness) fuel = some true := by
  rw [show sat (BitstringEncoding.bitEncode (witnessFormula p publicBits count fuel)) = true ↔
      ∃ wires : List Bool, wires.length = (template p publicBits count fuel).length+count ∧
        Fixed (wire wires) 0 (template p publicBits count fuel) ∧
        wire (simulate wires (witnessGates p publicBits count fuel)) (witnessOutput p publicBits count fuel) = true from
      fixed_sat_compiled_iff _ _ _ _ (witnessGates_valid p publicBits count fuel)
        (witnessOutput_bound p publicBits count fuel)]
  constructor
  · rintro ⟨wires,hlen,hfixed,hout⟩
    obtain ⟨witness,hw,he⟩ := fixed_decompose _ wires count hlen hfixed
    refine ⟨witness,hw,?_⟩
    subst wires
    have hc := witnessCircuit_correct p publicBits witness fuel
    rw [hw] at hc
    exact hc.1 hout
  · rintro ⟨witness,hw,haccept⟩
    refine ⟨template p publicBits count fuel++witness,?_,?_,?_⟩
    · simp [hw]
    · apply (Fixed_congr (wire (template p publicBits count fuel))
        (wire (template p publicBits count fuel++witness)) 0 (template p publicBits count fuel) ?_).1
        (fixed_self _)
      intro i _ hi
      symm
      exact wire_append _ _ i (by simpa using hi)
    · have hc := witnessCircuit_correct p publicBits witness fuel
      rw [hw] at hc
      exact hc.2 haccept

theorem witnessGates_length (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    (witnessGates p publicBits count fuel).length =
      fuel*((2*(2+4*(p.length+3))+(1+4*(2*window (dummyInput publicBits count) fuel+1))) +
        (p.length+3)*(2+4*(p.length+3))) := by
  rw [witnessGates,relocate_length,circuitGates_length]

/-- An explicit bound on the actual serialized CNF in the template size,
free-bit count and generated gate count. The gate count has the separate
closed form in `witnessGates_length`. -/
theorem witnessFormula_encoded_length (p : Program) (publicBits : List Bool) (count fuel : Nat) :
    (BitstringEncoding.bitEncode (witnessFormula p publicBits count fuel)).length ≤
      ((template p publicBits count fuel).length+3*(witnessGates p publicBits count fuel).length+1) *
      (24*((template p publicBits count fuel).length+count+(witnessGates p publicBits count fuel).length)+31) :=
  compileFixed_encoded_length _ _ _ _ (witnessGates_valid p publicBits count fuel)
    (witnessOutput_bound p publicBits count fuel)

namespace Fixtures
def readsFirst : Program := [((false,false,0,1),(false,false,0,2))]

example : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [] 1 1)) = true := by
  apply (sat_witnessFormula_iff readsFirst [] 1 1).2
  exact ⟨[true],by decide,by decide⟩

example : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [false] 1 1)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [false] 1 1)) with
  | false => rfl
  | true =>
    obtain ⟨w,_,h⟩ := (sat_witnessFormula_iff readsFirst [false] 1 1).1 hs
    simp [readsFirst,bounded,run,advance,step,initial] at h

example : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [] 1 0)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [] 1 0)) with
  | false => rfl
  | true =>
    obtain ⟨w,_,h⟩ := (sat_witnessFormula_iff readsFirst [] 1 0).1 hs
    simp [bounded,run] at h

example : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [] 0 1)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (witnessFormula readsFirst [] 0 1)) with
  | false => rfl
  | true =>
    obtain ⟨w,hw,h⟩ := (sat_witnessFormula_iff readsFirst [] 0 1).1 hs
    have hw' : w = [] := List.length_eq_zero_iff.mp hw
    subst w
    simp [readsFirst,bounded,run,advance,step,initial] at h
end Fixtures

end Shared.ComplexityBridge.CircuitWitness
