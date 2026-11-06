import Shared.ComplexityBridge.TM2FoldIO
import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.ComplexityBridge.TM2ListUnaryLength

set_option backward.isDefEq.respectTransparency false

/-! Polynomial-time implementation of the actual CNF disjunction front end. -/
namespace Shared.ComplexityBridge.TM2DisjoinPoly
open Shared.ComplexityBridge.CNF Shared.ComplexityBridge.CNFDisjunction

theorem guardAll_zero_isPolyTime : ComplexityTheory.IsPolyTime
    (fun fs : List Formula => guardAll 0 fs) := by
  let pair : List Formula → Nat × List Formula := fun fs => (0,fs)
  have hz : ComplexityTheory.IsPolyTime (fun _ : List Formula => (0 : Nat)) :=
    Shared.ComplexityBridge.TM2EmptyConstant.zero_isPolyTime
  have hi : ComplexityTheory.IsPolyTime (id : List Formula → List Formula) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp : ComplexityTheory.IsPolyTime pair := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime _ _ hz hi
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp pair
    (fun p : Nat × List Formula => guardAll p.1 p.2) hp Shared.ComplexityBridge.TM2FoldIO.guardAll_isPolyTime
  simpa [pair] using h

/-- The complete disjunction constructor, including the choice clause and
all guarded formulas, has a finite canonical polynomial-time implementation. -/
theorem disjoin_isPolyTime : ComplexityTheory.IsPolyTime disjoin := by
  let choice : List Formula → Clause := fun fs => choices 0 fs.length
  let guarded : List Formula → Formula := fun fs => guardAll 0 fs
  let both : List Formula → Clause × Formula := fun fs => (choice fs,guarded fs)
  have hc : ComplexityTheory.IsPolyTime choice := Shared.ComplexityBridge.TM2ListUnaryLength.disjoin_choices_isPolyTime
  have hg : ComplexityTheory.IsPolyTime guarded := guardAll_zero_isPolyTime
  have hb : ComplexityTheory.IsPolyTime both := Shared.ComplexityBridge.TM2GuardAllStep.pair_isPolyTime choice guarded hc hg
  have h := Shared.ComplexityBridge.TM2Compose.isPolyTime_comp both
    (Shared.ComplexityBridge.TM2ListAppend.cons (α := Clause)) hb Shared.ComplexityBridge.TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun fs : List Formula => disjoin fs)
  simpa [both,choice,guarded,disjoin,Shared.ComplexityBridge.TM2ListAppend.cons] using h

namespace Fixtures
example : disjoin [] = [[]] := rfl
example : disjoin [[],[]] = [[(1,true),(3,true)]] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2DisjoinPoly
