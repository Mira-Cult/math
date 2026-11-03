import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2BinaryHalf
import Shared.ComplexityBridge.CNFChoiceOutput
import Shared.ComplexityBridge.TM2UnaryPolynomialIO

/-! Enumerate exactly `0, …, input.length - 1` with finite polynomial-time
machines. The input bits are tokens; their values are immaterial. -/
namespace Shared.ComplexityBridge.TM2UnaryRange
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

def literalIndex (l : Literal) : Nat := l.1.div2

theorem literalIndex_isPolyTime : ComplexityTheory.IsPolyTime literalIndex := by
  have hf : ComplexityTheory.IsPolyTime (Shared.ComplexityBridge.TM2PairFirst.first (α := Nat) (β := Bool)) :=
    Shared.ComplexityBridge.TM2PairFirst.first_isPolyTime
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (Shared.ComplexityBridge.TM2PairFirst.first (α := Nat) (β := Bool)) Nat.div2 hf
    Shared.ComplexityBridge.TM2BinaryHalf.div2_isPolyTime
  change ComplexityTheory.IsPolyTime (fun l : Literal => l.1.div2)
  simpa [Shared.ComplexityBridge.TM2PairFirst.first] using h

def rangeFromTokens (tokens : List Bool) : List Nat := List.range tokens.length

theorem choice_indices (tokens : List Bool) :
    (Shared.ComplexityBridge.CNFChoiceOutput.choiceClause tokens).map literalIndex = rangeFromTokens tokens := by
  simp [Shared.ComplexityBridge.CNFChoiceOutput.choiceClause,choices,selector,literalIndex,rangeFromTokens,
    List.map_map,Function.comp_def,Nat.div2_bit1]

/-- The range constructor builds the existing selector list and maps a
finite binary projection/division machine over it. All encodings and list
traversal costs are included in the canonical bound. -/
theorem rangeFromTokens_isPolyTime : ComplexityTheory.IsPolyTime rangeFromTokens := by
  have hc := Shared.ComplexityBridge.CNFChoiceOutput.choiceClause_isPolyTime
  have hm := Shared.ComplexityBridge.TM2ContextMapGeneric.listMap_isPolyTime literalIndex literalIndex_isPolyTime
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp Shared.ComplexityBridge.CNFChoiceOutput.choiceClause
    (fun c : Clause => c.map literalIndex) hc hm
  have he : (fun x => (Shared.ComplexityBridge.CNFChoiceOutput.choiceClause x).map literalIndex) = rangeFromTokens := by
    funext x; exact choice_indices x
  rw [he] at h
  exact h

/-- For every fixed polynomial, enumerate all witness lengths through its
value, without ever storing a binary time bound as an implicit unary clock. -/
theorem polynomialRange_isPolyTime (bound : Polynomial Nat) : ComplexityTheory.IsPolyTime
    (fun x : List Bool => List.range (bound.eval x.length+1)) := by
  have hc := Shared.ComplexityBridge.TM2UnaryPolynomialIO.witnessCount_isPolyTime bound
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp
    (fun x : List Bool => List.replicate (bound.eval x.length+1) true) rangeFromTokens hc rangeFromTokens_isPolyTime
  simpa [rangeFromTokens] using h

namespace Fixtures
example : rangeFromTokens [] = [] := rfl
example : rangeFromTokens [false,true,true] = [0,1,2] := rfl
example : (Shared.ComplexityBridge.CNFChoiceOutput.choiceClause [true,true,true]).map literalIndex = [0,1,2] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2UnaryRange
