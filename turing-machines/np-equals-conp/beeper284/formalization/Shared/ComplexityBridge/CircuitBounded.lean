import Shared.Codes.FiniteProgramTotalize

/-! A concrete circuit for bounded Boolean acceptance of the shared finite
program model, including timeout, invalid and both terminal outcomes. The
construction is parameterized by the actual program, input and natural-number
fuel; no polynomial bit-cost generator or SAT-hardness theorem is claimed. -/
namespace Shared.ComplexityBridge.CircuitBounded
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitProgramMove

/-- Every side of the initial tape plus one cell per transition fits. -/
def window (input : List Bool) (fuel : Nat) : Nat := input.length+fuel

def initialConfig (p : Program) (input : List Bool) : Config := embed p (initial input)

def circuitWidth (p : Program) (input : List Bool) (fuel : Nat) : Nat :=
  inputWidth (totalProgram p) (window input fuel)

def circuitInput (p : Program) (input : List Bool) (fuel : Nat) : List Bool :=
  machineWires (totalProgram p) (window input fuel) (initialConfig p input)

def updateGates (p : Program) (input : List Bool) (fuel : Nat) : List Gate :=
  continuingGates (totalProgram p) (window input fuel) (circuitWidth p input fuel)

def updateOutputs (p : Program) (input : List Bool) (fuel : Nat) : List Nat :=
  continuingOutputs (totalProgram p) (window input fuel) (circuitWidth p input fuel)

def circuitGates (p : Program) (input : List Bool) (fuel : Nat) : List Gate :=
  unroll (circuitWidth p input fuel) (updateGates p input fuel) (updateOutputs p input fuel)
    (circuitWidth p input fuel) (List.range (circuitWidth p input fuel)) fuel

def acceptIndex (p : Program) (input : List Bool) (fuel : Nat) : Nat :=
  ((finalRefs (circuitWidth p input fuel) (updateGates p input fuel) (updateOutputs p input fuel)
    (circuitWidth p input fuel) (List.range (circuitWidth p input fuel)) fuel)[trueState p]?).getD 0

theorem circuitInput_length (p : Program) (input : List Bool) (fuel : Nat) :
    (circuitInput p input fuel).length = circuitWidth p input fuel := by
  simp [circuitInput,circuitWidth,machineWires_length]

theorem initial_slack_left (p : Program) (input : List Bool) (fuel : Nat) :
    (initialConfig p input).2.1.length+fuel ≤ window input fuel := by
  simp [initialConfig,embed,initial,window]

theorem initial_slack_right (p : Program) (input : List Bool) (fuel : Nat) :
    (initialConfig p input).2.2.2.length+fuel ≤ window input fuel := by
  simp [initialConfig,embed,initial,window,List.length_tail]

theorem acceptState_bound (p : Program) (input : List Bool) (fuel : Nat) :
    trueState p < (totalProgram p).length := by simp [trueState,totalProgram_length]

/-- An output gate of the concrete unrolled circuit is true exactly when the
original fuel-bounded evaluator returns true. -/
theorem bounded_true_iff_circuit (p : Program) (input : List Bool) (fuel : Nat) :
    bounded p input fuel = some true ↔
      wire (simulate (circuitInput p input fuel) (circuitGates p input fuel))
        (acceptIndex p input fuel) = true := by
  obtain ⟨d,hd,he⟩ := bounded_true_iff_totalized p input fuel
  have hc := unroll_of_live_run (totalProgram p) (window input fuel) fuel (initialConfig p input) d hd
    (initial_slack_left p input fuel) (initial_slack_right p input fuel)
  change readState (simulate (circuitInput p input fuel) (circuitGates p input fuel))
    (circuitWidth p input fuel)
    (finalRefs (circuitWidth p input fuel) (updateGates p input fuel) (updateOutputs p input fuel)
      (circuitWidth p input fuel) (List.range (circuitWidth p input fuel)) fuel) =
    machineWires (totalProgram p) (window input fuel) d at hc
  have hindex : trueState p < circuitWidth p input fuel := by
    have h := acceptState_bound p input fuel
    simp only [circuitWidth,inputWidth]
    omega
  have hb := readState_wire (simulate (circuitInput p input fuel) (circuitGates p input fuel))
    (circuitWidth p input fuel)
    (finalRefs (circuitWidth p input fuel) (updateGates p input fuel) (updateOutputs p input fuel)
      (circuitWidth p input fuel) (List.range (circuitWidth p input fuel)) fuel) (trueState p) hindex
  rw [hc,machineWires_state (totalProgram p) (window input fuel) d (trueState p) (acceptState_bound p input fuel)] at hb
  change decide (trueState p = d.1) = wire (simulate (circuitInput p input fuel) (circuitGates p input fuel))
    (acceptIndex p input fuel) at hb
  rw [←hb,decide_eq_true_eq]
  simpa [eq_comm] using he

theorem circuitGates_valid (p : Program) (input : List Bool) (fuel : Nat) :
    validGates (circuitWidth p input fuel) (circuitGates p input fuel) := by
  unfold circuitGates updateGates updateOutputs circuitWidth
  apply unroll_valid
  · exact continuingGates_valid _ _ _ le_rfl
  · exact continuingOutputs_length _ _ _
  · exact continuingOutputs_bound _ _ _ le_rfl
  · intro i hi
    simp [hi]

theorem acceptIndex_bound (p : Program) (input : List Bool) (fuel : Nat) :
    acceptIndex p input fuel < circuitWidth p input fuel+(circuitGates p input fuel).length := by
  let width := circuitWidth p input fuel
  let gates := updateGates p input fuel
  let outs := updateOutputs p input fuel
  have ho : outs.length = width := continuingOutputs_length _ _ _
  have hb : ∀ o ∈ outs, o < width+gates.length := continuingOutputs_bound _ _ _ le_rfl
  have hi : trueState p < width := by
    have h := acceptState_bound p input fuel
    dsimp [width,circuitWidth,inputWidth]
    omega
  have href : ∀ i < width, ((List.range width)[i]?).getD 0 < width := by
    intro i hi
    simp [hi]
  have h := finalRefs_bound width gates outs ho hb width (List.range width) href fuel (trueState p) hi
  simpa [acceptIndex,circuitGates,unroll_length,width,gates,outs] using h

theorem circuitGates_length (p : Program) (input : List Bool) (fuel : Nat) :
    (circuitGates p input fuel).length =
      fuel*((2*(2+4*(p.length+3))+(1+4*(2*window input fuel+1))) +
        (p.length+3)*(2+4*(p.length+3))) := by
  unfold circuitGates updateGates updateOutputs circuitWidth
  rw [continuingTrace_unroll_length,totalProgram_length]

/-- `Fixed` pins every bit of its list at the specified offset. -/
theorem fixed_get (a : Valuation) (offset : Nat) (bits : List Bool) (h : Fixed a offset bits)
    (i : Nat) (hi : i < bits.length) : a (offset+i) = (bits[i]?).getD false := by
  induction bits generalizing offset i with
  | nil => simp at hi
  | cons b bs ih =>
    simp only [Fixed] at h
    cases i with
    | zero => simpa using h.1
    | succ i =>
      have htail : i < bs.length := by simp at hi; omega
      have hh := ih (offset+1) h.2 i htail
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem fixed_build (a : Valuation) (offset : Nat) (bits : List Bool)
    (h : ∀ i < bits.length, a (offset+i) = (bits[i]?).getD false) : Fixed a offset bits := by
  induction bits generalizing offset with
  | nil => trivial
  | cons b bs ih =>
    simp only [Fixed]
    constructor
    · simpa using h 0 (by simp)
    · apply ih
      intro i hi
      have hh := h (i+1) (by simp; omega)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem fixed_self (bits : List Bool) : Fixed (wire bits) 0 bits := by
  apply fixed_build
  intro i hi
  simp [wire]

theorem fixed_list_eq (fixed wires : List Bool) (hlen : wires.length = fixed.length)
    (h : Fixed (wire wires) 0 fixed) : wires = fixed := by
  apply List.ext_getElem
  · exact hlen
  · intro i hi₁ hi₂
    have hh := fixed_get (wire wires) 0 fixed h i hi₂
    simp only [Nat.zero_add] at hh
    rw [wire_get wires i hi₁] at hh
    simpa [hi₂] using hh

/-- The actual canonical CNF encoding, with every initial circuit wire pinned. -/
def formula (p : Program) (input : List Bool) (fuel : Nat) : Formula :=
  compileFixed (circuitInput p input fuel) 0 (acceptIndex p input fuel) (circuitGates p input fuel)

/-- Both directions of the finite-program bounded-acceptance reduction to
this repository's all-bitstrings SAT language. -/
theorem sat_formula_iff_bounded_true (p : Program) (input : List Bool) (fuel : Nat) :
    sat (BitstringEncoding.bitEncode (formula p input fuel)) = true ↔ bounded p input fuel = some true := by
  let bits := circuitInput p input fuel
  let gates := circuitGates p input fuel
  let out := acceptIndex p input fuel
  have hv : validGates (bits.length+0) gates := by
    simpa [bits,gates,circuitInput_length] using circuitGates_valid p input fuel
  have ho : out < bits.length+0+gates.length := by
    simpa [out,bits,gates,circuitInput_length] using acceptIndex_bound p input fuel
  change sat (BitstringEncoding.bitEncode (compileFixed bits 0 out gates)) = true ↔ _
  rw [fixed_sat_compiled_iff bits 0 out gates hv ho]
  constructor
  · rintro ⟨wires,hlen,hfixed,hout⟩
    have he : wires = bits := fixed_list_eq bits wires (by simpa using hlen) hfixed
    subst wires
    exact (bounded_true_iff_circuit p input fuel).2 hout
  · intro hb
    refine ⟨bits,by simp,fixed_self bits,?_⟩
    exact (bounded_true_iff_circuit p input fuel).1 hb

/-- Bound on the actual canonical CNF serialization, expressed in the program
state count, input length and numerical fuel. It is an output-size bound,
not a runtime bound for its generator. -/
theorem formula_encoded_length (p : Program) (input : List Bool) (fuel : Nat) :
    (BitstringEncoding.bitEncode (formula p input fuel)).length ≤
      (circuitWidth p input fuel +
        3*(fuel*((2*(2+4*(p.length+3))+(1+4*(2*window input fuel+1))) +
          (p.length+3)*(2+4*(p.length+3))))+1) *
      (24*(circuitWidth p input fuel +
        fuel*((2*(2+4*(p.length+3))+(1+4*(2*window input fuel+1))) +
          (p.length+3)*(2+4*(p.length+3))))+31) := by
  have hv : validGates ((circuitInput p input fuel).length+0) (circuitGates p input fuel) := by
    simpa [circuitInput_length] using circuitGates_valid p input fuel
  have ho : acceptIndex p input fuel < (circuitInput p input fuel).length+0+(circuitGates p input fuel).length := by
    simpa [circuitInput_length] using acceptIndex_bound p input fuel
  have h := compileFixed_encoded_length (circuitInput p input fuel) 0 (acceptIndex p input fuel)
    (circuitGates p input fuel) hv ho
  rw [circuitInput_length,circuitGates_length] at h
  simpa only [formula,Nat.add_zero] using h

namespace Fixtures
def yesProgram : Program := [((false,false,0,2),(false,false,0,2))]
def noProgram : Program := [((false,false,0,1),(false,false,0,1))]
def badProgram : Program := [((false,false,0,9),(false,false,0,9))]

example : sat (BitstringEncoding.bitEncode (formula yesProgram [] 1)) = true :=
  (sat_formula_iff_bounded_true yesProgram [] 1).2 (by decide)

example : sat (BitstringEncoding.bitEncode (formula yesProgram [] 0)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (formula yesProgram [] 0)) with
  | false => rfl
  | true =>
    have h := (sat_formula_iff_bounded_true yesProgram [] 0).1 hs
    cases h

example : sat (BitstringEncoding.bitEncode (formula noProgram [] 1)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (formula noProgram [] 1)) with
  | false => rfl
  | true =>
    have h := (sat_formula_iff_bounded_true noProgram [] 1).1 hs
    cases h

example : sat (BitstringEncoding.bitEncode (formula badProgram [] 1)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (formula badProgram [] 1)) with
  | false => rfl
  | true =>
    have h := (sat_formula_iff_bounded_true badProgram [] 1).1 hs
    cases h
end Fixtures

end Shared.ComplexityBridge.CircuitBounded
