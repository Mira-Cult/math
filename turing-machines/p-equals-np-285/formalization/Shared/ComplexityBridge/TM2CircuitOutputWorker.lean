import Shared.ComplexityBridge.CircuitOutputClosed
import Shared.ComplexityBridge.TM2UnaryProductLength
import Shared.ComplexityBridge.TM2UnaryPredecessor
import Shared.ComplexityBridge.TM2CircuitTemplate

/-! Polynomial-time computation of the actual relocated accepting output
wire from public input, unary witness count, and unary fuel. The arithmetic
is represented by explicitly generated unary lists before binary counting. -/
namespace Shared.ComplexityBridge.TM2CircuitOutputWorker
open Shared.ComplexityBridge
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitOutputClosed

abbrev Input := (List Bool × List Bool) × List Bool

def copies : Nat → List Bool → List Bool
  | 0, _ => []
  | n+1, xs => xs ++ copies n xs

theorem copies_length (n : Nat) (xs : List Bool) : (copies n xs).length = n*xs.length := by
  induction n with
  | zero => simp [copies]
  | succ n ih => simp [copies,ih,Nat.succ_mul,Nat.add_comm]

theorem copies_isPolyTime (n : Nat) : ComplexityTheory.IsPolyTime (copies n) := by
  induction n with
  | zero => exact TM2EmptyConstant.isPolyTime [] rfl
  | succ n ih =>
    have hi : ComplexityTheory.IsPolyTime (id : List Bool → List Bool) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
    exact TM2CircuitTemplate.append_isPolyTime id (copies n) hi ih

def constantTokens (n : Nat) (_xs : List Bool) : List Bool := List.replicate n true

theorem constantTokens_length (n : Nat) (xs : List Bool) : (constantTokens n xs).length = n := by
  simp [constantTokens]

theorem constantTokens_isPolyTime (n : Nat) : ComplexityTheory.IsPolyTime (constantTokens n) := by
  have h := TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (Polynomial.C n)
  have he : TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C n) = constantTokens n := by
    funext xs
    simp [TM2UnaryPolynomialIO.unaryPolynomial,constantTokens]
  rw [he] at h
  exact h

def nonempty (xs : List Bool) : Bool := TM2BoundedWitnessGuard.numericNe (xs.length,0)

theorem nonempty_isPolyTime : ComplexityTheory.IsPolyTime nonempty := by
  let zero : List Bool → Nat := fun _ => 0
  let args : List Bool → Nat × Nat := fun xs => (xs.length,zero xs)
  have hz : ComplexityTheory.IsPolyTime zero := TM2EmptyConstant.zero_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime List.length zero TM2BinaryListLength.length_isPolyTime hz
  exact TM2Compose.isPolyTime_comp args TM2BoundedWitnessGuard.numericNe ha TM2BoundedWitnessGuard.numericNe_isPolyTime

def countTokens (z : Input) : List Bool := copies 3 z.1.2

def windowTokens (z : Input) : List Bool := z.1.1 ++ countTokens z ++ z.2

def stateCount (p : Program) : Nat := p.length+2
def stateTotal (p : Program) : Nat := p.length+3
def moveConstant (p : Program) : Nat := 2*(2+4*stateTotal p)+5
def stepConstant (p : Program) : Nat := moveConstant p+stateTotal p*(2+4*stateTotal p)
def extraConstant (p : Program) : Nat := moveConstant p+stateCount p*(2+4*stateTotal p)+3+4*stateTotal p

def stepTokens (p : Program) (z : Input) : List Bool :=
  constantTokens (stepConstant p) z.1.1 ++ copies 8 (windowTokens z)

def extraTokens (p : Program) (z : Input) : List Bool :=
  constantTokens (extraConstant p) z.1.1 ++ copies 10 (windowTokens z) ++ countTokens z ++
    TM2UnaryProductLength.productBits (TM2UnaryPredecessor.predecessor z.2,stepTokens p z)

def outputTokens (p : Program) (z : Input) : List Bool :=
  constantTokens (stateCount p) z.1.1 ++ TM2ListMask.mask (nonempty z.2,extraTokens p z)

def worker (p : Program) (z : Input) : Nat := (outputTokens p z).length

/-- Every list construction is bounded by the supplied unary input sizes;
all operations use finite canonical polynomial-time machines. -/
theorem worker_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (worker p) := by
  let pair : Input → List Bool × List Bool := fun z => z.1
  let pubBits : Input → List Bool := fun z => z.1.1
  let witness : Input → List Bool := fun z => z.1.2
  let fuel : Input → List Bool := fun z => z.2
  let count : Input → List Bool := countTokens
  let win : Input → List Bool := windowTokens
  let steps : Input → List Bool := stepTokens p
  let pred : Input → List Bool := fun z => TM2UnaryPredecessor.predecessor (fuel z)
  let product : Input → List Bool := fun z => TM2UnaryProductLength.productBits (pred z,steps z)
  let extra : Input → List Bool := extraTokens p
  let flag : Input → Bool := fun z => nonempty (fuel z)
  let masked : Input → List Bool := fun z => TM2ListMask.mask (flag z,extra z)
  let base : Input → List Bool := fun z => constantTokens (stateCount p) (pubBits z)
  have hp : ComplexityTheory.IsPolyTime pair := TM2PairFirst.first_isPolyTime
  have hpub : ComplexityTheory.IsPolyTime pubBits := TM2Compose.isPolyTime_comp pair (fun q : List Bool × List Bool => q.1) hp TM2PairFirst.first_isPolyTime
  have hw : ComplexityTheory.IsPolyTime witness := TM2Compose.isPolyTime_comp pair (fun q : List Bool × List Bool => q.2) hp TM2GuardAllStep.second_isPolyTime
  have hf : ComplexityTheory.IsPolyTime fuel := TM2GuardAllStep.second_isPolyTime
  have hc : ComplexityTheory.IsPolyTime count := TM2Compose.isPolyTime_comp witness (copies 3) hw (copies_isPolyTime 3)
  have hwin : ComplexityTheory.IsPolyTime win := TM2CircuitTemplate.append_isPolyTime _ fuel
    (TM2CircuitTemplate.append_isPolyTime pubBits count hpub hc) hf
  have hconst (n : Nat) : ComplexityTheory.IsPolyTime (fun z : Input => constantTokens n (pubBits z)) :=
    TM2Compose.isPolyTime_comp pubBits (constantTokens n) hpub (constantTokens_isPolyTime n)
  have hcopy (n : Nat) : ComplexityTheory.IsPolyTime (fun z : Input => copies n (win z)) :=
    TM2Compose.isPolyTime_comp win (copies n) hwin (copies_isPolyTime n)
  have hsteps : ComplexityTheory.IsPolyTime steps := TM2CircuitTemplate.append_isPolyTime _ _ (hconst _) (hcopy 8)
  have hpred : ComplexityTheory.IsPolyTime pred := TM2Compose.isPolyTime_comp fuel TM2UnaryPredecessor.predecessor hf TM2UnaryPredecessor.predecessor_isPolyTime
  have hproduct : ComplexityTheory.IsPolyTime product := TM2Compose.isPolyTime_comp
    (fun z => (pred z,steps z)) TM2UnaryProductLength.productBits
    (TM2GuardAllStep.pair_isPolyTime pred steps hpred hsteps) TM2UnaryProductLength.productBits_isPolyTime
  have hextra : ComplexityTheory.IsPolyTime extra := TM2CircuitTemplate.append_isPolyTime _ product
    (TM2CircuitTemplate.append_isPolyTime _ count
      (TM2CircuitTemplate.append_isPolyTime _ _ (hconst _) (hcopy 10)) hc) hproduct
  have hflag : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp fuel nonempty hf nonempty_isPolyTime
  have hmasked : ComplexityTheory.IsPolyTime masked := TM2Compose.isPolyTime_comp
    (fun z => (flag z,extra z)) (TM2ListMask.mask (α := Bool))
    (TM2GuardAllStep.pair_isPolyTime flag extra hflag hextra) TM2ListMask.mask_isPolyTime
  have hbase : ComplexityTheory.IsPolyTime base := hconst _
  have hout : ComplexityTheory.IsPolyTime (outputTokens p) := TM2CircuitTemplate.append_isPolyTime base masked hbase hmasked
  exact TM2Compose.isPolyTime_comp (outputTokens p) List.length hout TM2BinaryListLength.length_isPolyTime

theorem worker_correct (p : Program) (pubBits witness fuel : List Bool) :
    worker p ((pubBits,witness),fuel) = witnessOutput p pubBits (3*witness.length) fuel.length := by
  cases fuel with
  | nil =>
    simp [worker,outputTokens,nonempty,TM2BoundedWitnessGuard.numericNe,TM2ListMask.mask,
      constantTokens_length,stateCount,witnessOutput_zero,Shared.Codes.FiniteProgramTotalize.trueState]
  | cons b fuel =>
    have h := witnessOutput_succ_arithmetic p pubBits (3*witness.length) fuel.length
    have hflag : nonempty (b::fuel) = true := by
      simp [nonempty,TM2BoundedWitnessGuard.numericNe]
    change (constantTokens (stateCount p) pubBits ++
      TM2ListMask.mask (nonempty (b::fuel),extraTokens p ((pubBits,witness),b::fuel))).length = _
    rw [hflag]
    simp only [TM2ListMask.mask, ↓reduceIte]
    simp only [List.length_append,constantTokens_length,extraTokens,stepTokens,
      windowTokens,countTokens,copies_length,TM2UnaryProductLength.productBits_length,
      TM2UnaryPredecessor.predecessor_correct,List.length_replicate,List.length_cons,Nat.add_sub_cancel]
    dsimp [stateCount,stateTotal,moveConstant,stepConstant,extraConstant] at *
    rw [h]
    ring

namespace Fixtures
example : worker [] (([],[]),[]) = 2 := rfl
example : worker [] (([],[]),[true]) = witnessOutput [] [] 0 1 := by decide
end Fixtures
end Shared.ComplexityBridge.TM2CircuitOutputWorker
