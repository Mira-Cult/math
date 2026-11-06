import Shared.ComplexityBridge.CircuitWitness
import Shared.ComplexityBridge.CircuitPairComputability

/-! Explicit construction of the initial circuit-wire template. -/
namespace Shared.ComplexityBridge.CircuitTemplateExplicit
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTotalize
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitProgramMove

/-- A totalized program always begins in state zero, including an empty
program (whose invalid-state index is zero). -/
def stateBits (p : Program) : List Bool := true :: List.replicate (p.length+2) false

def explicit (p : Program) (input : List Bool) (fuel : Nat) : List Bool :=
  (stateBits p ++ List.replicate (input.length+fuel) false) ++
    (input ++ List.replicate (fuel+1) false)

theorem initialState_zero (p : Program) : initialState p = 0 :=
  Shared.ComplexityBridge.CircuitPairComputability.initialState_zero p

theorem wire_replicate_false (n i : Nat) : wire (List.replicate n false) i = false := by
  simp only [wire,List.getElem?_replicate]
  split <;> rfl

theorem wire_state (p : Program) (i : Nat) : wire (stateBits p) i = decide (i=0) := by
  cases i with
  | zero => rfl
  | succ i =>
    simp only [wire,stateBits,List.getElem?_cons_succ,List.getElem?_replicate,Nat.succ_ne_zero,decide_false]
    split <;> rfl

theorem wire_pad (xs : List Bool) (n i : Nat) :
    wire (xs ++ List.replicate n false) i = wire xs i := by
  by_cases h : i < xs.length
  · exact wire_append xs _ i h
  · have hw : wire xs i = false := wire_outside xs i (by omega)
    -- The two appended tails are both blank beyond the input.
    have he : xs.length+(i-xs.length)=i := by omega
    conv_lhs => rw [←he,wire_append_after,wire_replicate_false]
    exact hw.symm

theorem explicit_length (p : Program) (input : List Bool) (fuel : Nat) :
    (explicit p input fuel).length = circuitWidth p input fuel := by
  simp [explicit,stateBits,circuitWidth,inputWidth,window,totalProgram_length]
  omega

/-- The finite list construction agrees bit-for-bit with the actual circuit
initialization, including empty input and zero fuel. -/
theorem explicit_correct (p : Program) (input : List Bool) (fuel : Nat) :
    explicit p input fuel = circuitInput p input fuel := by
  apply List.ext_getElem
  · rw [explicit_length,circuitInput_length]
  · intro i hi₁ hi₂
    rw [← wire_get _ i hi₁,← wire_get _ i hi₂]
    rw [input_bit p input fuel i (by simpa [explicit_length] using hi₁)]
    simp only [initialState_zero,totalProgram_length,inputStart,window]
    let s := stateBits p
    let k := input.length+fuel
    have hs : s.length = p.length+3 := by simp [s,stateBits]
    change wire ((s ++ List.replicate k false) ++ (input ++ List.replicate (fuel+1) false)) i = _
    by_cases hstate : i < s.length
    · have hp : i < (s ++ List.replicate k false).length := by simp; omega
      rw [wire_append _ _ i hp,wire_append _ _ i hstate,wire_state]
      simp [hs] at hstate
      simp [hstate]
    · by_cases hblank : i < s.length+k
      · have hp : i < (s ++ List.replicate k false).length := by simp; omega
        rw [wire_append _ _ i hp]
        have he : s.length+(i-s.length)=i := by omega
        conv_lhs => rw [←he,wire_append_after,wire_replicate_false]
        have hh : ¬ i < p.length+3 := by omega
        have hk : i < p.length+3+(input.length+fuel) := by omega
        simp [hh,hk]
      · have hlen : (s ++ List.replicate k false).length = s.length+k := by simp
        have he : (s ++ List.replicate k false).length + (i-(s.length+k)) = i := by omega
        conv_lhs => rw [←he,wire_append_after,wire_pad]
        have hh : ¬ i < p.length+3 := by omega
        have hk : ¬ i < p.length+3+(input.length+fuel) := by omega
        simp [hh,hk,hs,k]

end Shared.ComplexityBridge.CircuitTemplateExplicit
