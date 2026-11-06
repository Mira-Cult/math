import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.ComplexityBridge.TM2UnaryRange
import Shared.ComplexityBridge.CNFLiteralConstructor
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.CircuitPairWitness

/-! Polynomial-time construction of the witness-shape clause component from
unary tokens. This does not construct the remaining circuit formula. -/
namespace Shared.ComplexityBridge.TM2ShapeClauses
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF

/-- One witness bit contributes two unit clauses with consecutive shape
constraints; `i` is the bit index. -/
def piece (p : Nat × Nat) : Formula :=
  [[(p.1+3*p.2,true)],[(p.1+3*p.2+2,false)]]

theorem triple_isPolyTime : ComplexityTheory.IsPolyTime (fun n : Nat => 3*n) := by
  let twice : Nat → Nat := fun n => 2*n
  let prep : Nat → Nat × Nat := fun n => (twice n,n)
  have ht : ComplexityTheory.IsPolyTime twice := CNFBinaryIndex.double_isPolyTime
  have hi : ComplexityTheory.IsPolyTime (id : Nat → Nat) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp : ComplexityTheory.IsPolyTime prep := TM2GuardAllStep.pair_isPolyTime twice id ht hi
  have h := TM2Compose.isPolyTime_comp prep CNFBinaryPairAdd.addPair hp CNFBinaryPairAdd.addPair_isPolyTime
  have he : (fun n => CNFBinaryPairAdd.addPair (prep n)) = (fun n => 3*n) := by
    funext n; simp [CNFBinaryPairAdd.addPair,prep,twice]; omega
  rw [he] at h
  exact h

theorem plusTwo_isPolyTime : ComplexityTheory.IsPolyTime (fun n : Nat => n+2) := by
  have h := TM2Compose.isPolyTime_comp Nat.succ Nat.succ
    CNFBinaryIncrement.successor_isPolyTime CNFBinaryIncrement.successor_isPolyTime
  simpa [Nat.succ_eq_add_one,Nat.add_assoc] using h

def unit (sign : Bool) (n : Nat) : Clause := [CNFLiteralConstructor.literal sign n]

theorem unit_isPolyTime (sign : Bool) : ComplexityTheory.IsPolyTime (unit sign) := by
  let lit : Nat → Literal := CNFLiteralConstructor.literal sign
  let empty : Nat → Clause := fun _ => []
  let prep : Nat → Literal × Clause := fun n => (lit n,empty n)
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hp : ComplexityTheory.IsPolyTime prep := TM2GuardAllStep.pair_isPolyTime lit empty
    (CNFLiteralConstructor.literal_isPolyTime sign) he
  have h := TM2Compose.isPolyTime_comp prep (TM2ListAppend.cons (α := Literal)) hp TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun n : Nat => [CNFLiteralConstructor.literal sign n])
  simpa [prep,lit,empty,TM2ListAppend.cons] using h

theorem piece_isPolyTime : ComplexityTheory.IsPolyTime piece := by
  let base : Nat × Nat → Nat := fun p => p.1
  let idx : Nat × Nat → Nat := fun p => p.2
  let triple : Nat × Nat → Nat := fun p => 3*p.2
  let args : Nat × Nat → Nat × Nat := fun p => (base p,triple p)
  let index : Nat × Nat → Nat := fun p => p.1+3*p.2
  let index2 : Nat × Nat → Nat := fun p => index p+2
  let yes : Nat × Nat → Clause := fun p => unit true (index p)
  let no : Nat × Nat → Clause := fun p => unit false (index2 p)
  let empty : Nat × Nat → Formula := fun _ => []
  let tail : Nat × Nat → Formula := fun p => [no p]
  let tailargs : Nat × Nat → Clause × Formula := fun p => (no p,empty p)
  let args2 : Nat × Nat → Clause × Formula := fun p => (yes p,tail p)
  have hb : ComplexityTheory.IsPolyTime base := TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx := TM2GuardAllStep.second_isPolyTime
  have ht : ComplexityTheory.IsPolyTime triple := TM2Compose.isPolyTime_comp idx (fun n => 3*n) hi triple_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime base triple hb ht
  have hx : ComplexityTheory.IsPolyTime index := TM2Compose.isPolyTime_comp args CNFBinaryPairAdd.addPair ha CNFBinaryPairAdd.addPair_isPolyTime
  have hx2 : ComplexityTheory.IsPolyTime index2 := TM2Compose.isPolyTime_comp index (fun n => n+2) hx plusTwo_isPolyTime
  have hy : ComplexityTheory.IsPolyTime yes := TM2Compose.isPolyTime_comp index (unit true) hx (unit_isPolyTime true)
  have hn : ComplexityTheory.IsPolyTime no := TM2Compose.isPolyTime_comp index2 (unit false) hx2 (unit_isPolyTime false)
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hta : ComplexityTheory.IsPolyTime tailargs := TM2GuardAllStep.pair_isPolyTime no empty hn he
  have htail : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp tailargs (TM2ListAppend.cons (α := Clause)) hta TM2ListAppend.cons_isPolyTime
  have ha2 : ComplexityTheory.IsPolyTime args2 := TM2GuardAllStep.pair_isPolyTime yes tail hy htail
  have h := TM2Compose.isPolyTime_comp args2 (TM2ListAppend.cons (α := Clause)) ha2 TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Nat × Nat => [[(p.1+3*p.2,true)],[(p.1+3*p.2+2,false)]])
  simpa [args2,tail,yes,no,index,index2,unit,CNFLiteralConstructor.literal,TM2ListAppend.cons] using h

def fromTokens (p : Nat × List Bool) : Formula :=
  ((List.range p.2.length).map (fun i => piece (p.1,i))).flatten

theorem fromTokens_isPolyTime : ComplexityTheory.IsPolyTime fromTokens := by
  let base : Nat × List Bool → Nat := fun p => p.1
  let tokens : Nat × List Bool → List Bool := fun p => p.2
  let indices : Nat × List Bool → List Nat := fun p => TM2UnaryRange.rangeFromTokens (tokens p)
  let args : Nat × List Bool → Nat × List Nat := fun p => (base p,indices p)
  have hb : ComplexityTheory.IsPolyTime base := TM2PairFirst.first_isPolyTime
  have ht : ComplexityTheory.IsPolyTime tokens := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp tokens TM2UnaryRange.rangeFromTokens ht TM2UnaryRange.rangeFromTokens_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime base indices hb hi
  have hm := TM2ContextMapGeneric.contextMap_isPolyTime piece piece_isPolyTime
  have h := TM2Compose.isPolyTime_comp args (TM2ContextMapGeneric.contextMap piece) ha hm
  have hf := TM2Compose.isPolyTime_comp (fun p => TM2ContextMapGeneric.contextMap piece (args p))
    (List.flatten : List Formula → Formula) h TM2FlattenList.flatten_isPolyTime
  change ComplexityTheory.IsPolyTime (fun p : Nat × List Bool => ((List.range p.2.length).map (fun i => piece (p.1,i))).flatten)
  simpa [args,indices,base,tokens,TM2UnaryRange.rangeFromTokens,TM2ContextMapGeneric.contextMap] using hf

theorem range_correct (n base : Nat) :
    ((List.range n).map (fun i => piece (base,i))).flatten =
      CircuitPairWitness.shapeClauses base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map]
    simp only [List.map_cons,List.map_map,Function.comp_def,List.flatten_cons]
    have he : (fun i : Nat => piece (base,i+1)) = (fun i => piece (base+3,i)) := by
      funext i
      have hh : base+3*(i+1) = base+3+3*i := by omega
      simp only [piece,hh]
    change piece (base,0) ++ ((List.range n).map (fun i => piece (base,i+1))).flatten = _
    rw [he,ih]
    simp [piece,CircuitPairWitness.shapeClauses]

/-- The token constructor produces exactly the shape clauses used by the
existing SAT reduction. -/
theorem fromTokens_correct (base : Nat) (tokens : List Bool) :
    fromTokens (base,tokens) = CircuitPairWitness.shapeClauses base tokens.length :=
  range_correct tokens.length base
/-- The actual witness-shape clause function, with its count supplied in
unary, is canonical polynomial time. -/
theorem shapeClauses_unary_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × List Bool => CircuitPairWitness.shapeClauses p.1 p.2.length) := by
  have h := fromTokens_isPolyTime
  have he : fromTokens = (fun p : Nat × List Bool => CircuitPairWitness.shapeClauses p.1 p.2.length) := by
    funext p
    exact fromTokens_correct p.1 p.2
  rw [he] at h
  exact h

namespace Fixtures
example : fromTokens (7,[]) = [] := rfl
example : fromTokens (7,[false,true]) = [[(7,true)],[(9,false)],[(10,true)],[(12,false)]] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2ShapeClauses
