import Shared.ComplexityBridge.TM2GateCNFPieces
import Shared.ComplexityBridge.CircuitTemplateExplicit
import Shared.ComplexityBridge.TM2UnaryPolynomialIO
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2ListAppend

/-! Construct the actual circuit template from public bits, unary witness
count, and unary fuel, using finite polynomial-time list machines. -/
namespace Shared.ComplexityBridge.TM2CircuitTemplate
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms

abbrev Input := (List Bool × List Bool) × List Bool

def zeros (xs : List Bool) : List Bool := xs.map (fun _ => false)

theorem zeros_eq (xs : List Bool) : zeros xs = List.replicate xs.length false := by
  simp [zeros]

theorem zeros_isPolyTime : ComplexityTheory.IsPolyTime zeros := by
  exact TM2ContextMapGeneric.listMap_isPolyTime (fun _ : Bool => false) (TM2Constant.isPolyTime false)

theorem append_isPolyTime {α : Type} [BitstringEncoding α] (F G : α → List Bool)
    (hF : ComplexityTheory.IsPolyTime F) (hG : ComplexityTheory.IsPolyTime G) :
    ComplexityTheory.IsPolyTime (fun x => F x ++ G x) := by
  have h := TM2GuardAllStep.pair_isPolyTime F G hF hG
  exact TM2Compose.isPolyTime_comp (fun x => (F x,G x)) (TM2ListAppend.append (α := Bool)) h TM2ListAppend.append_isPolyTime

/-- Fixed program state bits are built from the input using a constant unary
polynomial, a bit conversion and one finite cons operation. -/
theorem stateBits_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime
    (fun _ : List Bool => CircuitTemplateExplicit.stateBits p) := by
  let tokens : List Bool → List Bool := TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C (p.length+2))
  let tail : List Bool → List Bool := fun x => zeros (tokens x)
  let flag : List Bool → Bool := fun _ => true
  let args : List Bool → Bool × List Bool := fun x => (flag x,tail x)
  have ht : ComplexityTheory.IsPolyTime tokens := TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime _
  have htail : ComplexityTheory.IsPolyTime tail := TM2Compose.isPolyTime_comp tokens zeros ht zeros_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Constant.isPolyTime true
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime flag tail hf htail
  have h := TM2Compose.isPolyTime_comp args (TM2ListAppend.cons (α := Bool)) ha TM2ListAppend.cons_isPolyTime
  have he : (fun x => TM2ListAppend.cons (args x)) = (fun _ : List Bool => CircuitTemplateExplicit.stateBits p) := by
    funext x
    simp [args,flag,tail,tokens,TM2ListAppend.cons,CircuitTemplateExplicit.stateBits,
      zeros_eq,TM2UnaryPolynomialIO.unaryPolynomial]
  rw [he] at h
  exact h

def build (p : Program) (z : Input) : List Bool :=
  let pubBits := z.1.1
  let w := z.1.2
  let fuel := z.2
  let triple := w ++ w ++ w
  let rest := triple ++ fuel
  (CircuitTemplateExplicit.stateBits p ++ zeros (pubBits ++ rest)) ++
    (pubBits ++ zeros (rest ++ [true]))

theorem build_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (build p) := by
  let left : Input → List Bool × List Bool := fun z => z.1
  let pubBits : Input → List Bool := fun z => z.1.1
  let w : Input → List Bool := fun z => z.1.2
  let fuel : Input → List Bool := fun z => z.2
  let triple : Input → List Bool := fun z => w z ++ w z ++ w z
  let rest : Input → List Bool := fun z => triple z ++ fuel z
  let leftTokens : Input → List Bool := fun z => pubBits z ++ rest z
  let one : Input → List Bool := fun _ => [true]
  let rightTokens : Input → List Bool := fun z => rest z ++ one z
  let state : Input → List Bool := fun z => CircuitTemplateExplicit.stateBits p
  let leftZeros : Input → List Bool := fun z => zeros (leftTokens z)
  let rightZeros : Input → List Bool := fun z => zeros (rightTokens z)
  let leftPart : Input → List Bool := fun z => state z ++ leftZeros z
  let rightPart : Input → List Bool := fun z => pubBits z ++ rightZeros z
  have hl : ComplexityTheory.IsPolyTime left := TM2PairFirst.first_isPolyTime
  have hp : ComplexityTheory.IsPolyTime pubBits := TM2Compose.isPolyTime_comp left
    (fun q : List Bool × List Bool => q.1) hl TM2PairFirst.first_isPolyTime
  have hw : ComplexityTheory.IsPolyTime w := TM2Compose.isPolyTime_comp left
    (fun q : List Bool × List Bool => q.2) hl TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fuel := TM2GuardAllStep.second_isPolyTime
  have htriple : ComplexityTheory.IsPolyTime triple := append_isPolyTime _ _ (append_isPolyTime w w hw hw) hw
  have hrest : ComplexityTheory.IsPolyTime rest := append_isPolyTime triple fuel htriple hf
  have hlt : ComplexityTheory.IsPolyTime leftTokens := append_isPolyTime pubBits rest hp hrest
  have hone : ComplexityTheory.IsPolyTime one := by
    let v : Input → Bool := fun _ => true
    have hv : ComplexityTheory.IsPolyTime v := TM2Constant.isPolyTime true
    exact TM2GateCNFPieces.singleton_isPolyTime v hv
  have hrt : ComplexityTheory.IsPolyTime rightTokens := append_isPolyTime rest one hrest hone
  have hstate : ComplexityTheory.IsPolyTime state := TM2Compose.isPolyTime_comp pubBits
    (fun _ : List Bool => CircuitTemplateExplicit.stateBits p) hp (stateBits_isPolyTime p)
  have hlz : ComplexityTheory.IsPolyTime leftZeros := TM2Compose.isPolyTime_comp leftTokens zeros hlt zeros_isPolyTime
  have hrz : ComplexityTheory.IsPolyTime rightZeros := TM2Compose.isPolyTime_comp rightTokens zeros hrt zeros_isPolyTime
  have hlp : ComplexityTheory.IsPolyTime leftPart := append_isPolyTime state leftZeros hstate hlz
  have hrp : ComplexityTheory.IsPolyTime rightPart := append_isPolyTime pubBits rightZeros hp hrz
  have h := append_isPolyTime leftPart rightPart hlp hrp
  have he : (fun z => leftPart z ++ rightPart z) = build p := by
    funext z
    simp [leftPart,rightPart,state,leftZeros,rightZeros,leftTokens,rightTokens,
      rest,triple,pubBits,w,fuel,one,build,List.append_assoc]
  rw [←he]
  exact h

/-- The construction agrees with the actual witness template for every input,
including zero witness length and zero fuel. -/
theorem build_correct (p : Program) (pubBits w fuel : List Bool) :
    build p ((pubBits,w),fuel) = CircuitWitness.template p pubBits (3*w.length) fuel.length := by
  rw [CircuitWitness.template,←CircuitTemplateExplicit.explicit_correct]
  simp only [build,CircuitTemplateExplicit.explicit,CircuitWitness.dummyInput,zeros_eq,
    List.length_append,List.length_replicate,List.length_cons,List.length_nil]
  simp only [←List.replicate_add,List.append_assoc]
  have h1 : pubBits.length + 3*w.length+fuel.length =
      pubBits.length+(w.length+w.length+w.length+fuel.length) := by omega
  have h2 : 3*w.length+(fuel.length+1) = (w.length+w.length+w.length+fuel.length)+1 := by omega
  rw [h1,h2]

namespace Fixtures
example : build [] (([],[]),[]) = [true,false,false,false] := rfl
example : build [] (([true],[false]),[]) =
  [true,false,false,false,false,false,false,true,false,false,false,false] := rfl
end Fixtures
end Shared.ComplexityBridge.TM2CircuitTemplate
