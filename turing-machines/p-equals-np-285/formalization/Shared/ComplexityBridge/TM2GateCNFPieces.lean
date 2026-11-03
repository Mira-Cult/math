import Shared.ComplexityBridge.TM2ShapeClauses

/-! Fixed-variant Tseitin gate clauses constructed by finite polynomial-time
machines. Dynamic dispatch and traversal of a gate list are separate. -/
namespace Shared.ComplexityBridge.TM2GateCNFPieces
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF

/-- Fixed-size list construction uses the canonical list and pair encodings. -/
theorem singleton_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f : α → β) (hf : ComplexityTheory.IsPolyTime f) :
    ComplexityTheory.IsPolyTime (fun x => [f x]) := by
  let empty : α → List β := fun _ => []
  have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
  have hp := TM2GuardAllStep.pair_isPolyTime f empty hf he
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,empty x)) (TM2ListAppend.cons (α := β)) hp TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun x => TM2ListAppend.cons (f x,empty x)) at h
  exact h

theorem pairList_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f g : α → β) (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g) :
    ComplexityTheory.IsPolyTime (fun x => [f x,g x]) := by
  let tail : α → List β := fun x => [g x]
  have ht : ComplexityTheory.IsPolyTime tail := singleton_isPolyTime g hg
  have hp := TM2GuardAllStep.pair_isPolyTime f tail hf ht
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,tail x)) (TM2ListAppend.cons (α := β)) hp TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun x => TM2ListAppend.cons (f x,tail x)) at h
  exact h

theorem tripleList_isPolyTime {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (f g h : α → β) (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g)
    (hh : ComplexityTheory.IsPolyTime h) : ComplexityTheory.IsPolyTime (fun x => [f x,g x,h x]) := by
  let tail : α → List β := fun x => [g x,h x]
  have ht : ComplexityTheory.IsPolyTime tail := pairList_isPolyTime g h hg hh
  have hp := TM2GuardAllStep.pair_isPolyTime f tail hf ht
  have hc := TM2Compose.isPolyTime_comp (fun x => (f x,tail x)) (TM2ListAppend.cons (α := β)) hp TM2ListAppend.cons_isPolyTime
  change ComplexityTheory.IsPolyTime (fun x => TM2ListAppend.cons (f x,tail x)) at hc
  exact hc

theorem literal_isPolyTime {α : Type} [BitstringEncoding α]
    (f : α → Nat) (hf : ComplexityTheory.IsPolyTime f) (sign : Bool) :
    ComplexityTheory.IsPolyTime (fun x => (f x,sign)) :=
  TM2Compose.isPolyTime_comp f (CNFLiteralConstructor.literal sign) hf
    (CNFLiteralConstructor.literal_isPolyTime sign)

/-- A constant gate has a runtime Boolean output value; no finite program is
selected according to an input-dependent Lean proposition. -/
theorem constant_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Bool => gateCNF p.1 (.constant p.2)) := by
  let identity : Nat × Bool → Literal := id
  have hi : ComplexityTheory.IsPolyTime identity := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have h := singleton_isPolyTime (fun p : Nat × Bool => [identity p]) (singleton_isPolyTime identity hi)
  change ComplexityTheory.IsPolyTime (fun p : Nat × Bool => [[(p.1,p.2)]])
  exact h

theorem neg_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × Nat => gateCNF p.1 (.neg p.2)) := by
  let o : Nat × Nat → Nat := fun p => p.1
  let x : Nat × Nat → Nat := fun p => p.2
  have ho : ComplexityTheory.IsPolyTime o := TM2PairFirst.first_isPolyTime
  have hx : ComplexityTheory.IsPolyTime x := TM2GuardAllStep.second_isPolyTime
  let a : Nat × Nat → Clause := fun p => [(o p,false),(x p,false)]
  let b : Nat × Nat → Clause := fun p => [(o p,true),(x p,true)]
  have ha : ComplexityTheory.IsPolyTime a := pairList_isPolyTime _ _ (literal_isPolyTime o ho false) (literal_isPolyTime x hx false)
  have hb : ComplexityTheory.IsPolyTime b := pairList_isPolyTime _ _ (literal_isPolyTime o ho true) (literal_isPolyTime x hx true)
  have h := pairList_isPolyTime a b ha hb
  change ComplexityTheory.IsPolyTime (fun p : Nat × Nat => [[(p.1,false),(p.2,false)],[(p.1,true),(p.2,true)]])
  exact h

/-- One uniform family for conjunction (`sign = true`) and disjunction
(`sign = false`). The sign is fixed once when selecting the finite machine. -/
def binary (sign : Bool) (p : Nat × (Nat × Nat)) : Formula :=
  [[(p.1,!sign),(p.2.1,sign)],[(p.1,!sign),(p.2.2,sign)],
    [(p.1,sign),(p.2.1,!sign),(p.2.2,!sign)]]

theorem binary_isPolyTime (sign : Bool) : ComplexityTheory.IsPolyTime (binary sign) := by
  let o : Nat × (Nat × Nat) → Nat := fun p => p.1
  let pair : Nat × (Nat × Nat) → Nat × Nat := fun p => p.2
  let x : Nat × (Nat × Nat) → Nat := fun p => p.2.1
  let y : Nat × (Nat × Nat) → Nat := fun p => p.2.2
  have ho : ComplexityTheory.IsPolyTime o := TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pair := TM2GuardAllStep.second_isPolyTime
  have hx : ComplexityTheory.IsPolyTime x := TM2Compose.isPolyTime_comp pair (fun p : Nat × Nat => p.1) hp TM2PairFirst.first_isPolyTime
  have hy : ComplexityTheory.IsPolyTime y := TM2Compose.isPolyTime_comp pair (fun p : Nat × Nat => p.2) hp TM2GuardAllStep.second_isPolyTime
  let a : Nat × (Nat × Nat) → Clause := fun p => [(o p,!sign),(x p,sign)]
  let b : Nat × (Nat × Nat) → Clause := fun p => [(o p,!sign),(y p,sign)]
  let c : Nat × (Nat × Nat) → Clause := fun p => [(o p,sign),(x p,!sign),(y p,!sign)]
  have ha : ComplexityTheory.IsPolyTime a := pairList_isPolyTime _ _ (literal_isPolyTime o ho (!sign)) (literal_isPolyTime x hx sign)
  have hb : ComplexityTheory.IsPolyTime b := pairList_isPolyTime _ _ (literal_isPolyTime o ho (!sign)) (literal_isPolyTime y hy sign)
  have hc : ComplexityTheory.IsPolyTime c := tripleList_isPolyTime _ _ _ (literal_isPolyTime o ho sign) (literal_isPolyTime x hx (!sign)) (literal_isPolyTime y hy (!sign))
  have h := tripleList_isPolyTime a b c ha hb hc
  change ComplexityTheory.IsPolyTime (fun p : Nat × (Nat × Nat) =>
    [[(p.1,!sign),(p.2.1,sign)],[(p.1,!sign),(p.2.2,sign)],[(p.1,sign),(p.2.1,!sign),(p.2.2,!sign)]])
  exact h

theorem conj_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × (Nat × Nat) => gateCNF p.1 (.conj p.2.1 p.2.2)) := by
  change ComplexityTheory.IsPolyTime (binary true)
  exact binary_isPolyTime true

theorem disj_isPolyTime : ComplexityTheory.IsPolyTime
    (fun p : Nat × (Nat × Nat) => gateCNF p.1 (.disj p.2.1 p.2.2)) := by
  change ComplexityTheory.IsPolyTime (binary false)
  exact binary_isPolyTime false

namespace Fixtures
example : gateCNF 3 (.neg 1) = [[(3,false),(1,false)],[(3,true),(1,true)]] := rfl
example : gateCNF 4 (.conj 1 2) = binary true (4,1,2) := rfl
example : gateCNF 4 (.disj 1 2) = binary false (4,1,2) := rfl
end Fixtures
end Shared.ComplexityBridge.TM2GateCNFPieces
