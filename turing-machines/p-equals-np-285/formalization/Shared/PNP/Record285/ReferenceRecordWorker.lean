import Shared.PNP.Record285.ReferenceRowBudget
import Shared.ComplexityBridge.TM2BoundedSubtract
import Shared.ComplexityBridge.TM2InputBitLookup
import Shared.ComplexityBridge.TM2ListLookup
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.TM2If
import Shared.ComplexityBridge.TM2BinaryHalf
import Shared.ComplexityBridge.TM2Serialize

/-! Charged construction of the indexed 285 reference-table row selector. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section
namespace Shared.PNP.Record285.ReferenceRecordWorker
open Shared.PNP.Record285.ReferenceRowBudget
open Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.PNP.Record285.ReferenceSerialization
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.RelativeTape
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge

abbrev Input := List Bool × Nat

/-- Standard charged combinators for binary naturals and fixed constants. -/
theorem constNat {α : Type} [BitstringEncoding α] (n : Nat) :
    ComplexityTheory.IsPolyTime (fun _ : α => n) := by
  have h := TM2Compose.isPolyTime_comp (fun _ : α => (0 : Nat)) (fun x => x+n)
    TM2EmptyConstant.zero_isPolyTime (TM2FixedRows.addFixed_isPolyTime n)
  simpa using h

theorem add {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) (hg : ComplexityTheory.IsPolyTime g) :
    ComplexityTheory.IsPolyTime (fun x => f x+g x) := by
  exact TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime

theorem double {α : Type} [BitstringEncoding α] (f : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) : ComplexityTheory.IsPolyTime (fun x => 2*f x) :=
  TM2Compose.isPolyTime_comp f (fun n : Nat => 2*n) hf CNFBinaryIndex.double_isPolyTime

theorem fixedMul {α : Type} [BitstringEncoding α] (c : Nat) (f : α → Nat)
    (hf : ComplexityTheory.IsPolyTime f) : ComplexityTheory.IsPolyTime (fun x => c*f x) := by
  induction c with
  | zero => simpa using (constNat (α := α) 0)
  | succ c ih => simpa [Nat.succ_mul] using add (fun x => c*f x) f ih hf

theorem boolNat_isPolyTime : ComplexityTheory.IsPolyTime bitVal := by
  have h := TM2If.if_isPolyTime (fun b : Bool => b) (fun _ => (1 : Nat)) (fun _ => 0)
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ (constNat 1) (constNat 0)
  exact h

theorem constantPair_isPolyTime {α : Type} [BitstringEncoding α] (n : Nat) (b : Bool) :
    ComplexityTheory.IsPolyTime (fun _ : α => (n,b)) :=
  TM2GuardAllStep.pair_isPolyTime (fun _ : α => n) (fun _ : α => b) (constNat n) (TM2Constant.isPolyTime b)

theorem constantRows_isPolyTime {α : Type} [BitstringEncoding α] (rows : List (Nat × Bool)) :
    ComplexityTheory.IsPolyTime (fun _ : α => rows) := by
  induction rows with
  | nil => exact TM2EmptyConstant.isPolyTime [] rfl
  | cons x xs ih =>
    have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : α => x) (fun _ : α => xs)
      (constantPair_isPolyTime x.1 x.2) ih
    exact TM2Compose.isPolyTime_comp (fun _ : α => (x,xs))
      (TM2ListAppend.cons (α := Nat × Bool)) hp TM2ListAppend.cons_isPolyTime

/-- A natural's binary representation is serialized and queried by the
already verified total list lookup; missing high bits are false. -/
def bitAt (p : Nat × Nat) : Bool := TM2InputBitLookup.lookup (BitstringEncoding.bitEncode p.1,p.2)

theorem bitAt_isPolyTime : ComplexityTheory.IsPolyTime bitAt := by
  have hf : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.1) := TM2PairFirst.first_isPolyTime
  have hs : ComplexityTheory.IsPolyTime (fun p : Nat × Nat => p.2) := TM2GuardAllStep.second_isPolyTime
  have hb := TM2Compose.isPolyTime_comp (fun p : Nat × Nat => p.1)
    (BitstringEncoding.bitEncode : Nat → List Bool) hf TM2Serialize.isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime (fun p : Nat × Nat => BitstringEncoding.bitEncode p.1)
    (fun p : Nat × Nat => p.2) hb hs
  exact TM2Compose.isPolyTime_comp (fun p : Nat × Nat => (BitstringEncoding.bitEncode p.1,p.2))
    TM2InputBitLookup.lookup hp TM2InputBitLookup.lookup_isPolyTime

theorem bitAt_correct (n i : Nat) : bitAt (n,i) = n.testBit i := by
  rw [bitAt,TM2InputBitLookup.lookup_correct]
  change (Computability.encodeNat n)[i]?.getD false = _
  rw [CNFEncodingComputability.encodeNat_bits,Nat.testBit_eq_inth]
  rfl

/-- Two rows per verifier state. The table is a fixed finite constant once
`p` is fixed; its entries preserve both the packed row and the live/HALT tag. -/
def tableData (p : Program) : List (Nat × Bool) :=
  List.ofFn fun j : Fin (2*states p) =>
    let q : Fin (states p) := ⟨j.val/2,by have h := j.isLt; omega⟩
    let read := decide (j.val%2=1)
    let a := relativeTable p q read false
    (pack (lower a),a.next.isSome)

/-- All control and arithmetic inputs are finite, total functions of the
public input and binary selector. -/
def index (z : Input) : Nat := z.2

def quarter (z : Input) : Nat := z.2.div2.div2

def readBit (z : Input) : Bool := bitAt (z.2,1)

def choiceBit (z : Input) : Bool := bitAt (z.2,0)

def stateTokens (p : Program) (w : Polynomial Nat) (z : Input) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (statePolynomial p w) z.1

def rowCountTokens (p : Program) (w : Polynomial Nat) (z : Input) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (rowCountPolynomial p w) z.1

def writeTokens (w : Polynomial Nat) (z : Input) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.X+w) z.1

def offsetTokens (w : Polynomial Nat) (z : Input) : List Bool :=
  TM2UnaryPolynomialIO.unaryPolynomial (Polynomial.C 2*(Polynomial.X+w)+Polynomial.C 2) z.1

def inside (p : Program) (w : Polynomial Nat) (z : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (rowCountTokens p w z,index z)

def loader (w : Polynomial Nat) (z : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (offsetTokens w z,quarter z)

def writing (w : Polynomial Nat) (z : Input) : Bool :=
  TM2BoundedWitnessGuard.guard (writeTokens w z,quarter z)

def publicGuard (z : Input) : Bool := TM2BoundedWitnessGuard.guard (z.1,quarter z)

def publicBit (z : Input) : Bool := TM2InputBitLookup.lookup (z.1,quarter z)

def writeBit (w : Polynomial Nat) (z : Input) : Bool :=
  if writing w z then if publicGuard z then publicBit z else choiceBit z else readBit z

def equalNat (p : Nat × Nat) : Bool := !TM2BoundedWitnessGuard.numericNe p

def turnBit (w : Polynomial Nat) (z : Input) : Bool :=
  let k := (writeTokens w z).length
  equalNat (quarter z,k) || equalNat (quarter z,2*k+1)

def localIndex (p : Program) (w : Polynomial Nat) (z : Input) : Nat :=
  TM2BoundedSubtract.subtract (stateTokens p w z,(quarter z,(offsetTokens w z).length))

def fixedIndex (p : Program) (w : Polynomial Nat) (z : Input) : Nat :=
  2*localIndex p w z+bitVal (readBit z)

def fixedRow (p : Program) (w : Polynomial Nat) (z : Input) : Nat × Bool :=
  TM2ListLookup.lookup (tableData p,(fixedIndex p w z,(0,false)))

def loaderRecord (w : Polynomial Nat) (z : Input) : Nat :=
  bitVal (writeBit w z)+2*bitVal (turnBit w z)+16*(quarter z+1)+4

def fixedRecord (p : Program) (w : Polynomial Nat) (z : Input) : Nat :=
  (fixedRow p w z).1 + if (fixedRow p w z).2 then 16*(offsetTokens w z).length else 0

def worker (p : Program) (w : Polynomial Nat) (z : Input) : Nat :=
  if inside p w z then if loader w z then loaderRecord w z else fixedRecord p w z else 0

theorem index_isPolyTime : ComplexityTheory.IsPolyTime index := TM2GuardAllStep.second_isPolyTime

theorem quarter_isPolyTime : ComplexityTheory.IsPolyTime quarter := by
  have h := TM2Compose.isPolyTime_comp index Nat.div2 index_isPolyTime TM2BinaryHalf.div2_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun z => (index z).div2) Nat.div2 h TM2BinaryHalf.div2_isPolyTime

theorem fixedBit_isPolyTime (i : Nat) : ComplexityTheory.IsPolyTime (fun z : Input => bitAt (index z,i)) := by
  have hp := TM2GuardAllStep.pair_isPolyTime index (fun _ : Input => i) index_isPolyTime (constNat i)
  exact TM2Compose.isPolyTime_comp (fun z => (index z,i)) bitAt hp bitAt_isPolyTime

theorem readBit_isPolyTime : ComplexityTheory.IsPolyTime readBit := fixedBit_isPolyTime 1

theorem choiceBit_isPolyTime : ComplexityTheory.IsPolyTime choiceBit := fixedBit_isPolyTime 0

theorem tokens_isPolyTime (p : Polynomial Nat) : ComplexityTheory.IsPolyTime
    (fun z : Input => TM2UnaryPolynomialIO.unaryPolynomial p z.1) :=
  TM2Compose.isPolyTime_comp (fun z : Input => z.1) (TM2UnaryPolynomialIO.unaryPolynomial p)
    TM2PairFirst.first_isPolyTime (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime p)

theorem stateTokens_isPolyTime (p : Program) (w : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (stateTokens p w) := tokens_isPolyTime _

theorem rowCountTokens_isPolyTime (p : Program) (w : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (rowCountTokens p w) := tokens_isPolyTime _

theorem writeTokens_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (writeTokens w) :=
  tokens_isPolyTime _

theorem offsetTokens_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (offsetTokens w) :=
  tokens_isPolyTime _

theorem guard_isPolyTime (tokens : Input → List Bool) (value : Input → Nat)
    (ht : ComplexityTheory.IsPolyTime tokens) (hv : ComplexityTheory.IsPolyTime value) :
    ComplexityTheory.IsPolyTime (fun z => TM2BoundedWitnessGuard.guard (tokens z,value z)) :=
  TM2Compose.isPolyTime_comp (fun z => (tokens z,value z)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime tokens value ht hv) TM2BoundedWitnessGuard.guard_isPolyTime

theorem inside_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (inside p w) :=
  guard_isPolyTime _ _ (rowCountTokens_isPolyTime p w) index_isPolyTime

theorem loader_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (loader w) :=
  guard_isPolyTime _ _ (offsetTokens_isPolyTime w) quarter_isPolyTime

theorem writing_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (writing w) :=
  guard_isPolyTime _ _ (writeTokens_isPolyTime w) quarter_isPolyTime

theorem publicGuard_isPolyTime : ComplexityTheory.IsPolyTime publicGuard :=
  guard_isPolyTime _ _ TM2PairFirst.first_isPolyTime quarter_isPolyTime

theorem publicBit_isPolyTime : ComplexityTheory.IsPolyTime publicBit := by
  have hp := TM2GuardAllStep.pair_isPolyTime (fun z : Input => z.1) quarter
    TM2PairFirst.first_isPolyTime quarter_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun z : Input => (z.1,quarter z)) TM2InputBitLookup.lookup
    hp TM2InputBitLookup.lookup_isPolyTime

theorem writeBit_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (writeBit w) := by
  have h := TM2If.if_isPolyTime publicGuard publicBit choiceBit publicGuard_isPolyTime
    publicBit_isPolyTime choiceBit_isPolyTime
  exact TM2If.if_isPolyTime (writing w) (fun z => if publicGuard z then publicBit z else choiceBit z)
    readBit (writing_isPolyTime w) h readBit_isPolyTime

theorem length_of_tokens (tokens : Input → List Bool) (h : ComplexityTheory.IsPolyTime tokens) :
    ComplexityTheory.IsPolyTime (fun z => (tokens z).length) :=
  TM2Compose.isPolyTime_comp tokens List.length h TM2BinaryListLength.length_isPolyTime

theorem equalNat_isPolyTime : ComplexityTheory.IsPolyTime equalNat := by
  exact TM2Compose.isPolyTime_comp TM2BoundedWitnessGuard.numericNe (fun b => !b)
    TM2BoundedWitnessGuard.numericNe_isPolyTime TM2GateDispatch.not_isPolyTime

theorem turnBit_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (turnBit w) := by
  let k : Input → Nat := fun z => (writeTokens w z).length
  let twice : Input → Nat := fun z => 2*k z+1
  let first : Input → Bool := fun z => equalNat (quarter z,k z)
  let second : Input → Bool := fun z => equalNat (quarter z,twice z)
  have hk : ComplexityTheory.IsPolyTime k := length_of_tokens _ (writeTokens_isPolyTime w)
  have ht : ComplexityTheory.IsPolyTime twice := add (fun z => 2*k z) (fun _ => 1)
    (double k hk) (constNat 1)
  have hf : ComplexityTheory.IsPolyTime first := TM2Compose.isPolyTime_comp (fun z => (quarter z,k z)) equalNat
    (TM2GuardAllStep.pair_isPolyTime quarter k quarter_isPolyTime hk) equalNat_isPolyTime
  have hs : ComplexityTheory.IsPolyTime second := TM2Compose.isPolyTime_comp (fun z => (quarter z,twice z)) equalNat
    (TM2GuardAllStep.pair_isPolyTime quarter twice quarter_isPolyTime ht) equalNat_isPolyTime
  have hor := TM2If.if_isPolyTime first (fun _ : Input => true) second hf (TM2Constant.isPolyTime true) hs
  have he : (fun z => if first z then true else second z) = turnBit w := by
    funext z
    cases h : first z <;> simp [turnBit,first,second,twice,k,h]
  rw [he] at hor
  exact hor

theorem localIndex_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (localIndex p w) := by
  let off : Input → Nat := fun z => (offsetTokens w z).length
  have ho : ComplexityTheory.IsPolyTime off := length_of_tokens _ (offsetTokens_isPolyTime w)
  have hp := TM2GuardAllStep.pair_isPolyTime (stateTokens p w) (fun z => (quarter z,off z))
    (stateTokens_isPolyTime p w) (TM2GuardAllStep.pair_isPolyTime quarter off quarter_isPolyTime ho)
  exact TM2Compose.isPolyTime_comp (fun z => (stateTokens p w z,(quarter z,off z)))
    TM2BoundedSubtract.subtract hp TM2BoundedSubtract.subtract_isPolyTime

theorem fixedIndex_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (fixedIndex p w) := by
  have hb := TM2Compose.isPolyTime_comp readBit bitVal readBit_isPolyTime boolNat_isPolyTime
  exact add (fun z => 2*localIndex p w z) (fun z => bitVal (readBit z))
    (double _ (localIndex_isPolyTime p w)) hb

theorem fixedRow_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (fixedRow p w) := by
  have htable : ComplexityTheory.IsPolyTime (fun _ : Input => tableData p) := constantRows_isPolyTime _
  have hdefault : ComplexityTheory.IsPolyTime (fun _ : Input => ((0 : Nat),false)) := constantPair_isPolyTime _ _
  have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : Input => tableData p)
    (fun z => (fixedIndex p w z,((0 : Nat),false))) htable
    (TM2GuardAllStep.pair_isPolyTime (fixedIndex p w) (fun _ : Input => ((0 : Nat),false))
      (fixedIndex_isPolyTime p w) hdefault)
  exact TM2Compose.isPolyTime_comp (fun z => (tableData p,(fixedIndex p w z,((0 : Nat),false))))
    (TM2ListLookup.lookup (β := Nat × Bool)) hp TM2ListLookup.lookup_isPolyTime

theorem loaderRecord_isPolyTime (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (loaderRecord w) := by
  have hw := TM2Compose.isPolyTime_comp (writeBit w) bitVal (writeBit_isPolyTime w) boolNat_isPolyTime
  have ht := TM2Compose.isPolyTime_comp (turnBit w) bitVal (turnBit_isPolyTime w) boolNat_isPolyTime
  have hq := add quarter (fun _ : Input => 1) quarter_isPolyTime (constNat 1)
  have ha := add (fun z => bitVal (writeBit w z)) (fun z => 2*bitVal (turnBit w z)) hw
    (double _ ht)
  have hb := add (fun z => bitVal (writeBit w z)+2*bitVal (turnBit w z))
    (fun z => 16*(quarter z+1)) ha (fixedMul 16 _ hq)
  exact add _ _ hb (constNat 4)

theorem fixedRecord_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (fixedRecord p w) := by
  let row := fixedRow p w
  let base : Input → Nat := fun z => (row z).1
  let flag : Input → Bool := fun z => (row z).2
  let offset : Input → Nat := fun z => (offsetTokens w z).length
  have hr := fixedRow_isPolyTime p w
  have hb : ComplexityTheory.IsPolyTime base := TM2Compose.isPolyTime_comp row (fun p : Nat × Bool => p.1)
    hr TM2PairFirst.first_isPolyTime
  have hf : ComplexityTheory.IsPolyTime flag := TM2Compose.isPolyTime_comp row (fun p : Nat × Bool => p.2)
    hr TM2GuardAllStep.second_isPolyTime
  have ho : ComplexityTheory.IsPolyTime offset := length_of_tokens _ (offsetTokens_isPolyTime w)
  have hshift := TM2If.if_isPolyTime flag (fun z => 16*offset z) (fun _ => 0)
    hf (fixedMul 16 offset ho) (constNat 0)
  exact add base (fun z => if flag z then 16*offset z else 0) hb hshift

theorem worker_isPolyTime (p : Program) (w : Polynomial Nat) : ComplexityTheory.IsPolyTime (worker p w) := by
  have h := TM2If.if_isPolyTime (loader w) (loaderRecord w) (fixedRecord p w)
    (loader_isPolyTime w) (loaderRecord_isPolyTime w) (fixedRecord_isPolyTime p w)
  exact TM2If.if_isPolyTime (inside p w)
    (fun z => if loader w z then loaderRecord w z else fixedRecord p w z) (fun _ => 0)
    (inside_isPolyTime p w) h (constNat 0)

@[simp] theorem quarter_correct (z : Input) : quarter z = z.2/4 := by
  simp [quarter,Nat.div2_val,Nat.div_div_eq_div_mul]

@[simp] theorem choiceBit_correct (z : Input) : choiceBit z = decide (z.2%2=1) := by
  simp [choiceBit,bitAt_correct,Nat.testBit_zero]

@[simp] theorem readBit_correct (z : Input) : readBit z = decide ((z.2%4)/2=1) := by
  rw [readBit,bitAt_correct,Nat.testBit_succ,Nat.testBit_zero]
  have h : (z.2/2)%2 = (z.2%4)/2 := by omega
  rw [h]

@[simp] theorem stateTokens_length (p : Program) (w : Polynomial Nat) (z : Input) :
    (stateTokens p w z).length = Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length)+states p := by
  simp [stateTokens,TM2UnaryPolynomialIO.unaryPolynomial,statePolynomial_eval]

@[simp] theorem rowCountTokens_length (p : Program) (w : Polynomial Nat) (z : Input) :
    (rowCountTokens p w z).length = 4*(Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length)+states p) := by
  simp [rowCountTokens,TM2UnaryPolynomialIO.unaryPolynomial,rowCountPolynomial_eval]

@[simp] theorem writeTokens_length (w : Polynomial Nat) (z : Input) :
    (writeTokens w z).length = z.1.length+w.eval z.1.length := by
  simp [writeTokens,TM2UnaryPolynomialIO.unaryPolynomial,Polynomial.eval_add,Polynomial.eval_X]

@[simp] theorem offsetTokens_length (w : Polynomial Nat) (z : Input) :
    (offsetTokens w z).length = Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length) := by
  simp [offsetTokens,TM2UnaryPolynomialIO.unaryPolynomial,Shared.PNP.Record285.ChoiceLoader.offset,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]

@[simp] theorem inside_correct (p : Program) (w : Polynomial Nat) (z : Input) :
    inside p w z = decide (z.2 < 4*(Shared.PNP.Record285.ChoiceLoader.offset
      (z.1.length+w.eval z.1.length)+states p)) := by
  simp [inside,TM2TapePairs.guard_eq_decide,index]

@[simp] theorem loader_correct (w : Polynomial Nat) (z : Input) :
    loader w z = decide (z.2/4 < Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length)) := by
  simp [loader,TM2TapePairs.guard_eq_decide]

@[simp] theorem writing_correct (w : Polynomial Nat) (z : Input) :
    writing w z = decide (z.2/4 < z.1.length+w.eval z.1.length) := by
  simp [writing,TM2TapePairs.guard_eq_decide]

@[simp] theorem publicGuard_correct (z : Input) : publicGuard z = decide (z.2/4 < z.1.length) := by
  simp [publicGuard,TM2TapePairs.guard_eq_decide]

@[simp] theorem publicBit_correct (z : Input) : publicBit z = (z.1[z.2/4]?).getD false := by
  simp [publicBit,TM2InputBitLookup.lookup_correct]

@[simp] theorem equalNat_correct (p : Nat × Nat) : equalNat p = decide (p.1=p.2) := by
  by_cases h : p.1=p.2 <;> simp [equalNat,TM2BoundedWitnessGuard.numericNe,h]

@[simp] theorem turnBit_correct (w : Polynomial Nat) (z : Input) :
    turnBit w z = decide (z.2/4 = z.1.length+w.eval z.1.length ∨
      z.2/4 = 2*(z.1.length+w.eval z.1.length)+1) := by
  by_cases h1 : z.2/4 = z.1.length+w.eval z.1.length <;>
    by_cases h2 : z.2/4 = 2*(z.1.length+w.eval z.1.length)+1 <;>
      simp [turnBit,h1,h2]

theorem localIndex_correct (p : Program) (w : Polynomial Nat) (z : Input)
    (hi : z.2 < 4*(Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length)+states p)) :
    localIndex p w z = z.2/4-Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length) := by
  unfold localIndex
  rw [TM2BoundedSubtract.subtract_exact]
  · simp
  · simp only [stateTokens_length,quarter_correct]
    omega
  · simp only [stateTokens_length,offsetTokens_length]
    omega

theorem tableData_get (p : Program) (q : Fin (states p)) (read : Bool) :
    (tableData p)[2*q.val+bitVal read]? =
      some (pack (lower (relativeTable p q read false)),(relativeTable p q read false).next.isSome) := by
  have hq := q.isLt
  have hi : 2*q.val+bitVal read < 2*states p := by cases read <;> simp [bitVal] <;> omega
  have hd : (2*q.val+bitVal read)/2 = q.val := by cases read <;> simp [bitVal] <;> omega
  have hr : decide ((2*q.val+bitVal read)%2=1) = read := by cases read <;> simp [bitVal] <;> omega
  simp only [tableData,List.getElem?_ofFn,hi, ↓reduceDIte]
  have he : (⟨(2*q.val+bitVal read)/2,by omega⟩ : Fin (states p)) = q := Fin.ext hd
  rw [he,hr]

theorem fixedRow_correct (p : Program) (w : Polynomial Nat) (z : Input)
    (hi : z.2 < 4*(Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length)+states p))
    (hq : Shared.PNP.Record285.ChoiceLoader.offset (z.1.length+w.eval z.1.length) ≤ z.2/4) :
    let q : Fin (states p) := ⟨z.2/4-Shared.PNP.Record285.ChoiceLoader.offset
      (z.1.length+w.eval z.1.length),by omega⟩
    let a := relativeTable p q (decide ((z.2%4)/2=1)) false
    fixedRow p w z = (pack (lower a),a.next.isSome) := by
  dsimp only
  simp only [fixedRow,TM2ListLookup.lookup,fixedIndex,localIndex_correct p w z hi,readBit_correct]
  exact congrArg (fun x => x.getD (0,false))
    (tableData_get p ⟨z.2/4-Shared.PNP.Record285.ChoiceLoader.offset
      (z.1.length+w.eval z.1.length),by omega⟩ (decide ((z.2%4)/2=1)))

/-- The paid worker is extensionally the exact selector, for every input and
binary index, including out-of-range values and terminal rows. -/
theorem worker_correct (p : Program) (w : Polynomial Nat) : worker p w = verifierRecordAt p w := by
  funext z
  rcases z with ⟨input,i⟩
  by_cases hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+w.eval input.length)+states p)
  · by_cases hq : i/4 < Shared.PNP.Record285.ChoiceLoader.offset (input.length+w.eval input.length)
    · rw [verifierRecordAt_loader p w input i hi hq]
      simp [worker,hi,hq,loaderRecord,writeBit]
    · have hq' : Shared.PNP.Record285.ChoiceLoader.offset (input.length+w.eval input.length) ≤ i/4 := by omega
      rw [verifierRecordAt_verifier p w input i hi hq']
      have hf := fixedRow_correct p w (input,i) hi hq'
      dsimp only at hf
      have hc : relativeTable p
          ⟨i/4-Shared.PNP.Record285.ChoiceLoader.offset (input.length+w.eval input.length),by omega⟩
          (decide ((i%4)/2=1)) false =
        relativeTable p
          ⟨i/4-Shared.PNP.Record285.ChoiceLoader.offset (input.length+w.eval input.length),by omega⟩
          (decide ((i%4)/2=1)) (decide (i%2=1)) := rfl
      simp only [worker,inside_correct,hi,decide_true, ↓reduceIte,loader_correct,hq,decide_false,
        Bool.false_eq_true,fixedRecord,hf,offsetTokens_length]
      rw [hc]
  · have ho := verifierRecordAt_outside p w input i (by omega)
    simp [worker,hi,ho]

/-- No table-builder premise remains: every row operation and its output are
computed by the charged canonical polynomial-time machine. -/
theorem verifierRecordAt_isPolyTime (p : Program) (w : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (verifierRecordAt p w) := by
  rw [← worker_correct p w]
  exact worker_isPolyTime p w

/-- The actual hardwired verifier reference frame is uniformly polynomial in
the public input, for each fixed verifier and each fixed witness/time
polynomial. This theorem does not assert verifier totality or NP-hardness. -/
theorem verifierFrame_isPolyTime (p : Program) (w budget : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (fun input => verifierReferenceFrame p input
      (w.eval input.length) (budget.eval input.length)) :=
  verifierFrame_isPolyTime_of_recordAt p w budget (verifierRecordAt_isPolyTime p w)

/-- A fixed total bounded verifier yields a genuine canonical polynomial-time
many-one map to the actual reference language. The witness convention remains
the raw tape `input ++ witness`, so applications requiring length-sensitive
witnesses must supply a correctly framed verifier. -/
theorem reduction_of_total_verifier (p : Program) (w budget : Polynomial Nat)
    (language : List Bool → Prop)
    (htotal : ∀ input witness : List Bool, witness.length ≤ w.eval input.length →
      ∃ result, bounded p (input++witness) (budget.eval input.length) = some result)
    (hcorrect : ∀ input : List Bool, language input ↔
      ∃ witness : List Bool, witness.length ≤ w.eval input.length ∧
        bounded p (input++witness) (budget.eval input.length) = some true) :
    ∃ reduction : List Bool → List Bool, ComplexityTheory.IsPolyTime reduction ∧
      ∀ input, language input ↔
        Shared.PNP.Record285.CanonicalInput.referenceLanguage (reduction input) = true := by
  refine ⟨fun input => verifierReferenceFrame p input (w.eval input.length) (budget.eval input.length),
    verifierFrame_isPolyTime p w budget,?_⟩
  intro input
  rw [hcorrect input]
  exact (reference_padded_total_verifier p input (w.eval input.length) (budget.eval input.length)
    (htotal input)).symm

end Shared.PNP.Record285.ReferenceRecordWorker
