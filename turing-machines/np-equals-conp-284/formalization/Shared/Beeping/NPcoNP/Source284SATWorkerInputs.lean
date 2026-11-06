import Shared.Beeping.NPcoNP.Source284SATProducerIteration
import Shared.ComplexityBridge.TM2TapePairs
import Shared.ComplexityBridge.TM2BinaryListLength
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.TM2BoundedSubtract
import Shared.Beeping.NPcoNP.Source284RowNormalizationTM2
import Shared.ComplexityBridge.TM2InputBitLookup

/-! Paid input bounds and offsets for the single SAT row worker. These
lemmas do not yet establish the worker's complete polynomial running time. -/
namespace Shared.Beeping.NPcoNP.Source284SATWorkerInputs

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284SATProducerIteration
open Shared.Beeping.NPcoNP.Source284EncodedRows

abbrev Request := Input × Nat

private theorem add_poly {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x+g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

def inBudget (p : Request) : Bool := decide (p.2 < (budget p.1).length)

theorem inBudget_isPolyTime : IsPolyTime inBudget := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let tokens : Request → List Bool := fun p => budget (data p)
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime tokens index ht hi
  have h := TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,index p))
    TM2BoundedWitnessGuard.guard hp TM2BoundedWitnessGuard.guard_isPolyTime
  change IsPolyTime (fun p : Request => decide (p.2 < (budget p.1).length))
  simpa [data,index,tokens,TM2TapePairs.guard_eq_decide] using h

def allocation (p : Input) : Nat :=
  Source284CertificateDispatch.allocated p.1 p.2.1.length

theorem allocation_isPolyTime : IsPolyTime allocation := by
  let expected : Input → List Bool := fun p => p.1
  let rest : Input → List Bool × EncRows := fun p => p.2
  let ticks : Input → List Bool := fun p => (rest p).1
  let l : Input → Nat := fun p => (expected p).length
  let c : Input → Nat := fun p => (ticks p).length
  have he : IsPolyTime expected := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp rest
    (fun p : List Bool × EncRows => p.1) hr TM2PairFirst.first_isPolyTime
  have hl : IsPolyTime l := TM2Compose.isPolyTime_comp expected List.length
    he TM2BinaryListLength.length_isPolyTime
  have hc : IsPolyTime c := TM2Compose.isPolyTime_comp ticks List.length
    ht TM2BinaryListLength.length_isPolyTime
  have h2l : IsPolyTime (fun p => l p+l p) := add_poly l l hl hl
  have h2c : IsPolyTime (fun p => c p+c p) := add_poly c c hc hc
  have h3c : IsPolyTime (fun p => (c p+c p)+c p) := add_poly _ c h2c hc
  have h6c : IsPolyTime (fun p => ((c p+c p)+c p)+((c p+c p)+c p)) := add_poly _ _ h3c h3c
  have hsum := add_poly (fun p => l p+l p)
    (fun p => ((c p+c p)+c p)+((c p+c p)+c p)) h2l h6c
  have h := TM2Compose.isPolyTime_comp
    (fun p => (l p+l p)+(((c p+c p)+c p)+((c p+c p)+c p))) (fun n : Nat => n+8)
    hsum (TM2FixedRows.addFixed_isPolyTime 8)
  change IsPolyTime (fun p : Input => Source284CertificateDispatch.allocated p.1 p.2.1.length)
  convert h using 1
  funext p
  simp [l,c,expected,ticks,rest,Source284CertificateDispatch.allocated,
    Source284CertificateDispatch.sink,Source284CertificateDispatch.handoff,
    Source284CertificateDispatch.rewindStart,Source284CertificateDispatch.width]
  omega

/-- A safe relocated verifier index. Both operands are clamped to the charged
unary budget, so arbitrary large binary requests remain total and bounded. -/
def verifierIndex (p : Request) : Nat :=
  TM2BoundedSubtract.subtract (budget p.1,(p.2,allocation p.1+1))

theorem verifierIndex_isPolyTime : IsPolyTime verifierIndex := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let tokens : Request → List Bool := fun p => budget (data p)
  let base : Request → Nat := fun p => allocation (data p)+1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have ha : IsPolyTime (fun p : Request => allocation (data p)) :=
    TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have hb : IsPolyTime base := TM2Compose.isPolyTime_comp (fun p : Request => allocation (data p))
    (fun n : Nat => n+1) ha (TM2FixedRows.addFixed_isPolyTime 1)
  have hargs := TM2GuardAllStep.pair_isPolyTime tokens (fun p => (index p,base p)) ht
    (TM2GuardAllStep.pair_isPolyTime index base hi hb)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,(index p,base p)))
    TM2BoundedSubtract.subtract hargs TM2BoundedSubtract.subtract_isPolyTime

theorem verifierIndex_correct (p : Request) (h : p.2 ≤ (budget p.1).length) :
    verifierIndex p = p.2 - (allocation p.1+1) := by
  have hb : allocation p.1+1 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width]
    omega
  simp [verifierIndex,TM2BoundedSubtract.subtract_correct,Nat.min_eq_left h,Nat.min_eq_left hb]

/-- Encoded verifier row after both state relocations. This branch is total
on all inputs; its correctness below uses the proved finite index bound. -/
def verifierBranch (p : Request) : EncRow × EncRow :=
  let r := Source284RowNormalizationTM2.lookupPair (p.1.2.2,verifierIndex p)
  let offset := allocation p.1+1
  (Source284RowNormalizationTM2.normalizedShift (offset,r.1),
   Source284RowNormalizationTM2.normalizedShift (offset,r.2))

theorem verifierBranch_isPolyTime : IsPolyTime verifierBranch := by
  let data : Request → Input := fun p => p.1
  let rest : Request → List Bool × EncRows := fun p => (data p).2
  let rows : Request → EncRows := fun p => (rest p).2
  let index : Request → Nat := verifierIndex
  let pair : Request → EncRow × EncRow := fun p => Source284RowNormalizationTM2.lookupPair (rows p,index p)
  let base : Request → Nat := fun p => allocation (data p)+1
  let first : Request → EncRow := fun p => (pair p).1
  let second : Request → EncRow := fun p => (pair p).2
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2Compose.isPolyTime_comp data (fun p : Input => p.2)
    hd TM2GuardAllStep.second_isPolyTime
  have hrs : IsPolyTime rows := TM2Compose.isPolyTime_comp rest (fun p : List Bool × EncRows => p.2)
    hr TM2GuardAllStep.second_isPolyTime
  have hp : IsPolyTime pair := TM2Compose.isPolyTime_comp (fun p => (rows p,index p))
    Source284RowNormalizationTM2.lookupPair
    (TM2GuardAllStep.pair_isPolyTime rows index hrs verifierIndex_isPolyTime)
    Source284RowNormalizationTM2.lookupPair_isPolyTime
  have hb0 : IsPolyTime (fun p : Request => allocation (data p)) :=
    TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have hb : IsPolyTime base := TM2Compose.isPolyTime_comp (fun p : Request => allocation (data p))
    (fun n : Nat => n+1) hb0 (TM2FixedRows.addFixed_isPolyTime 1)
  have hf : IsPolyTime first := TM2Compose.isPolyTime_comp pair (fun p : EncRow × EncRow => p.1)
    hp TM2PairFirst.first_isPolyTime
  have hs : IsPolyTime second := TM2Compose.isPolyTime_comp pair (fun p : EncRow × EncRow => p.2)
    hp TM2GuardAllStep.second_isPolyTime
  have hfirst := TM2Compose.isPolyTime_comp (fun p => (base p,first p))
    Source284RowNormalizationTM2.normalizedShift
    (TM2GuardAllStep.pair_isPolyTime base first hb hf) Source284RowNormalizationTM2.normalizedShift_isPolyTime
  have hsecond := TM2Compose.isPolyTime_comp (fun p => (base p,second p))
    Source284RowNormalizationTM2.normalizedShift
    (TM2GuardAllStep.pair_isPolyTime base second hb hs) Source284RowNormalizationTM2.normalizedShift_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ hfirst hsecond

private theorem shift_twice (a b : Nat) (r : Source284TableEncode.Row) :
    Source284HardwireTable.shiftRow a (Source284HardwireTable.shiftRow b r) =
      Source284HardwireTable.shiftRow (b+a) r := by
  cases r with
  | mk w t n => cases n <;> simp [Source284HardwireTable.shiftRow] <;> omega

theorem verifierBranch_correct (p : Request)
    (hstart : allocation p.1+1 ≤ p.2) (hbound : p.2 ≤ (budget p.1).length) :
    verifierBranch p = rowWorker p := by
  have hq0 : p.2 ≠ 0 := by omega
  have hrel : Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length ≤ p.2-1 := by
    change allocation p.1 ≤ p.2-1
    omega
  have hne : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink] at *
    omega
  have hi := verifierIndex_correct p hbound
  have hsub : p.2-(allocation p.1+1) = p.2-1-allocation p.1 := by omega
  simp only [allocation] at hsub
  simp only [rowWorker,Source284FacingAdapter.table,hq0,↓reduceIte,
    Source284VerifierHandoff.table,hne,hrel, allocation]
  simp only [verifierBranch,hi,allocation]
  rw [hsub]
  rw [Source284RowNormalizationTM2.normalizedShift_correct,
    Source284RowNormalizationTM2.normalizedShift_correct]
  have ha := Source284RowNormalizationTM2.lookupPair_correct p.1.2.2
    (p.2-1-Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length) false
  have hb := Source284RowNormalizationTM2.lookupPair_correct p.1.2.2
    (p.2-1-Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length) true
  simp only [Bool.false_eq_true,↓reduceIte] at ha
  simp only [↓reduceIte] at hb
  rw [ha,hb,decode_encode_row,decode_encode_row,← shift_twice,← shift_twice]

/-- The handoff executes verifier state zero. Reusing the already paid
verifier branch at its first relocated index avoids a separate lookup. -/
def handoffBranch (p : Request) : EncRow × EncRow :=
  verifierBranch (p.1,allocation p.1+1)

theorem handoffBranch_isPolyTime : IsPolyTime handoffBranch := by
  let data : Request → Input := fun p => p.1
  let offset : Request → Nat := fun p => allocation (data p)+1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have ha : IsPolyTime (fun p : Request => allocation (data p)) :=
    TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have ho : IsPolyTime offset := TM2Compose.isPolyTime_comp (fun p : Request => allocation (data p))
    (fun n : Nat => n+1) ha (TM2FixedRows.addFixed_isPolyTime 1)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (data p,offset p)) verifierBranch
    (TM2GuardAllStep.pair_isPolyTime data offset hd ho) verifierBranch_isPolyTime

theorem handoffBranch_correct (p : Request)
    (hhand : p.2 = Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length+1) :
    handoffBranch p = rowWorker p := by
  have hbound : allocation p.1+1 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width]
    omega
  have hb := verifierBranch_correct (p.1,allocation p.1+1) (by simp) hbound
  have he : rowWorker (p.1,allocation p.1+1) = rowWorker p := by
    have h0 : p.2 ≠ 0 := by omega
    have hh : p.2-1 = Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by omega
    have ha : allocation p.1+1 ≠ 0 := by omega
    have har : allocation p.1+1-1 = allocation p.1 := by omega
    have hne : allocation p.1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
      simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink]
      omega
    simp only [rowWorker,Source284FacingAdapter.table,ha,h0,↓reduceIte,har,hh,
      Source284VerifierHandoff.table,hne,allocation]
    simp
  exact hb.trans he

/-- The two read-symbol rows of the initial preserving turn. -/
def initialBranch (_ : Request) : EncRow × EncRow :=
  ((false,true,true,1),(true,true,true,1))

theorem initialBranch_isPolyTime : IsPolyTime initialBranch :=
  Source284ConstantEncodedRowsTM2.constPair_isPolyTime _

theorem initialBranch_correct (p : Request) (hq : p.2 = 0) :
    initialBranch p = rowWorker p := by
  simp [initialBranch,rowWorker,Source284FacingAdapter.table,hq,encodeRow]

/-- The permanent reject row sits immediately below the relocated verifier. -/
def sinkBranch (p : Request) : EncRow × EncRow :=
  ((false,false,true,allocation p.1),(true,false,true,allocation p.1))

theorem sinkBranch_isPolyTime : IsPolyTime sinkBranch := by
  let data : Request → Input := fun p => p.1
  let target : Request → Nat := fun p => allocation (data p)
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime target := TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have hf : IsPolyTime (fun _ : Request => false) := TM2Constant.isPolyTime false
  have htrue : IsPolyTime (fun _ : Request => true) := TM2Constant.isPolyTime true
  have h0 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ target hf hf htrue ht
  have h1 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ target htrue hf htrue ht
  exact TM2GuardAllStep.pair_isPolyTime _ _ h0 h1

theorem sinkBranch_correct (p : Request) (hq : p.2 = allocation p.1) :
    sinkBranch p = rowWorker p := by
  have hn : allocation p.1 ≠ 0 := by
    simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink]
  have hs : allocation p.1-1 = Source284CertificateDispatch.sink p.1.1 p.1.2.1.length := by
    simp [allocation,Source284CertificateDispatch.allocated]
  have hh : Source284CertificateDispatch.sink p.1.1 p.1.2.1.length ≠
      Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.sink]
  have hlt : ¬ Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length ≤
      Source284CertificateDispatch.sink p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.allocated]
  simp [rowWorker,Source284FacingAdapter.table,hq,hn,hs,Source284VerifierHandoff.table,hh,hlt,
    Source284CertificateDispatch.sink_row,Source284HardwireTable.shiftRow,encodeRow,sinkBranch,
    allocation,Source284CertificateDispatch.allocated,Nat.add_comm]

def prefixIndex (p : Request) : Nat :=
  TM2BoundedSubtract.subtract (budget p.1,(p.2,1))

theorem prefixIndex_isPolyTime : IsPolyTime prefixIndex := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let tokens : Request → List Bool := fun p => budget (data p)
  let one : Request → Nat := fun _ => 1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have hz : IsPolyTime (fun _ : Request => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have ho : IsPolyTime one := by
    have h := TM2Compose.isPolyTime_comp (fun _ : Request => (0 : Nat))
      (fun n : Nat => n+1) hz (TM2FixedRows.addFixed_isPolyTime 1)
    simpa [one] using h
  have ha := TM2GuardAllStep.pair_isPolyTime tokens (fun p => (index p,one p)) ht
    (TM2GuardAllStep.pair_isPolyTime index one hi ho)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,(index p,one p)))
    TM2BoundedSubtract.subtract ha TM2BoundedSubtract.subtract_isPolyTime

theorem prefixIndex_correct (p : Request) (hbound : p.2 ≤ (budget p.1).length) :
    prefixIndex p = p.2-1 := by
  have hb : 1 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    omega
  simp [prefixIndex,TM2BoundedSubtract.subtract_correct,Nat.min_eq_left hbound,Nat.min_eq_left hb]

def prefixBit (p : Request) : Bool := TM2InputBitLookup.lookup (p.1.1,prefixIndex p)

theorem prefixBit_isPolyTime : IsPolyTime prefixBit := by
  let data : Request → Input := fun p => p.1
  let expected : Request → List Bool := fun p => (data p).1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have he : IsPolyTime expected := TM2Compose.isPolyTime_comp data
    (fun p : Input => p.1) hd TM2PairFirst.first_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Request => (expected p,prefixIndex p))
    TM2InputBitLookup.lookup (TM2GuardAllStep.pair_isPolyTime expected prefixIndex he prefixIndex_isPolyTime)
    TM2InputBitLookup.lookup_isPolyTime

def prefixBranch (p : Request) : EncRow × EncRow :=
  ((false,false,true,if prefixBit p then allocation p.1 else p.2+1),
   (true,false,true,if prefixBit p then p.2+1 else allocation p.1))

theorem prefixBranch_isPolyTime : IsPolyTime prefixBranch := by
  let data : Request → Input := fun p => p.1
  let index : Request → Nat := fun p => p.2
  let next : Request → Nat := fun p => index p+1
  let reject : Request → Nat := fun p => allocation (data p)
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hn : IsPolyTime next := TM2Compose.isPolyTime_comp index (fun n : Nat => n+1)
    hi (TM2FixedRows.addFixed_isPolyTime 1)
  have hr : IsPolyTime reject := TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have h0 := TM2If.if_isPolyTime prefixBit reject next prefixBit_isPolyTime hr hn
  have h1 := TM2If.if_isPolyTime prefixBit next reject prefixBit_isPolyTime hn hr
  have hf : IsPolyTime (fun _ : Request => false) := TM2Constant.isPolyTime false
  have ht : IsPolyTime (fun _ : Request => true) := TM2Constant.isPolyTime true
  have ha := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ _ hf hf ht h0
  have hb := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ _ ht hf ht h1
  exact TM2GuardAllStep.pair_isPolyTime _ _ ha hb

theorem prefixBranch_correct (p : Request) (hpos : 0 < p.2)
    (hq : p.2-1 < p.1.1.length) (hbound : p.2 ≤ (budget p.1).length) :
    prefixBranch p = rowWorker p := by
  have hq0 : p.2 ≠ 0 := by omega
  have hb : p.2-1 < Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width] at *
    omega
  have hn : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width] at *
    omega
  have ht (b : Bool) := Source284VerifierHandoff.validator_row p.1.1 p.1.2.1.length
    (Source284ListTables.table (decodeRows p.1.2.2)) (p.2-1) b hb hn
  simp only [rowWorker,Source284FacingAdapter.table,hq0,↓reduceIte,ht]
  rw [Source284CertificateDispatch.prefix_row _ _ _ _ hq,
    Source284CertificateDispatch.prefix_row _ _ _ _ hq]
  simp only [prefixBranch,prefixBit,prefixIndex_correct p hbound,TM2InputBitLookup.lookup_correct,
    Source284HardwireTable.shiftRow,encodeRow]
  cases hb' : (p.1.1[p.2-1]?).getD false <;>
    simp [hb',allocation,Source284CertificateDispatch.allocated] <;> omega

/-- A preserving transition to the next encoded state, optionally turning. -/
def continuingBranch (turn : Bool) (p : Request) : EncRow × EncRow :=
  ((false,turn,true,p.2+1),(true,turn,true,p.2+1))

theorem continuingBranch_isPolyTime (turn : Bool) : IsPolyTime (continuingBranch turn) := by
  let index : Request → Nat := fun p => p.2
  let target : Request → Nat := fun p => index p+1
  have hi : IsPolyTime index := TM2GuardAllStep.second_isPolyTime
  have hn : IsPolyTime target := TM2Compose.isPolyTime_comp index (fun n : Nat => n+1)
    hi (TM2FixedRows.addFixed_isPolyTime 1)
  have hf : IsPolyTime (fun _ : Request => false) := TM2Constant.isPolyTime false
  have ht : IsPolyTime (fun _ : Request => true) := TM2Constant.isPolyTime true
  have hd : IsPolyTime (fun _ : Request => turn) := TM2Constant.isPolyTime turn
  have h0 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ target hf hd ht hn
  have h1 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ target ht hd ht hn
  exact TM2GuardAllStep.pair_isPolyTime _ _ h0 h1

theorem rewindBranch_correct (p : Request)
    (hlo : Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length ≤ p.2-1)
    (hhi : p.2-1 < Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length +
      Source284CertificateDispatch.width p.1.1 p.1.2.1.length) :
    continuingBranch false p = rowWorker p := by
  have hq0 : p.2 ≠ 0 := by
    simp [Source284CertificateDispatch.rewindStart] at hlo
    omega
  have hb : p.2-1 < Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff] at *
    omega
  have hn : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.handoff] at *
    omega
  have ht (b : Bool) := Source284VerifierHandoff.validator_row p.1.1 p.1.2.1.length
    (Source284ListTables.table (decodeRows p.1.2.2)) (p.2-1) b hb hn
  let i := p.2-1-Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length
  have hi : i < Source284CertificateDispatch.width p.1.1 p.1.2.1.length := by dsimp [i]; omega
  have he : Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length+i = p.2-1 := by
    dsimp [i]; omega
  have hr (b : Bool) := Source284CertificateDispatch.rewind_row p.1.1 p.1.2.1.length i hi b
  rw [he] at hr
  simp only [rowWorker,Source284FacingAdapter.table,hq0,↓reduceIte,ht,hr,
    Source284HardwireTable.shiftRow,encodeRow,continuingBranch]
  simp only [Option.map_some,Option.isSome_some,Option.getD_some]
  simp only [Prod.mk.injEq, true_and]
  omega

theorem finalTurnBranch_correct (p : Request)
    (hq : p.2-1 = Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length +
      Source284CertificateDispatch.width p.1.1 p.1.2.1.length) :
    continuingBranch true p = rowWorker p := by
  have hq0 : p.2 ≠ 0 := by
    have hr : 0 < Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length := by
      simp [Source284CertificateDispatch.rewindStart]
    omega
  have hb : p.2-1 < Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff] at *
    omega
  have hn : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [Source284CertificateDispatch.handoff] at *
    omega
  have ht (b : Bool) := Source284VerifierHandoff.validator_row p.1.1 p.1.2.1.length
    (Source284ListTables.table (decodeRows p.1.2.2)) (p.2-1) b hb hn
  have hr (b : Bool) := Source284CertificateDispatch.final_turn_row p.1.1 p.1.2.1.length b
  rw [← hq] at hr
  simp only [rowWorker,Source284FacingAdapter.table,hq0,↓reduceIte,ht,hr,
    Source284HardwireTable.shiftRow,encodeRow,continuingBranch,
    Source284CertificateDispatch.handoff]
  simp only [Option.map_some,Option.isSome_some,Option.getD_some]
  simp only [Prod.mk.injEq, true_and]
  omega

def rewindTarget (p : Request) : Nat :=
  Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length+1

theorem rewindTarget_isPolyTime : IsPolyTime rewindTarget := by
  let data : Request → Input := fun p => p.1
  let expected : Request → List Bool := fun p => (data p).1
  let rest : Request → List Bool × EncRows := fun p => (data p).2
  let ticks : Request → List Bool := fun p => (rest p).1
  let l : Request → Nat := fun p => (expected p).length
  let c : Request → Nat := fun p => (ticks p).length
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have he : IsPolyTime expected := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2Compose.isPolyTime_comp data (fun p : Input => p.2)
    hd TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp rest (fun p : List Bool × EncRows => p.1)
    hr TM2PairFirst.first_isPolyTime
  have hl : IsPolyTime l := TM2Compose.isPolyTime_comp expected List.length he TM2BinaryListLength.length_isPolyTime
  have hc : IsPolyTime c := TM2Compose.isPolyTime_comp ticks List.length ht TM2BinaryListLength.length_isPolyTime
  have h2c := add_poly c c hc hc
  have h4c := add_poly (fun p => c p+c p) (fun p => c p+c p) h2c h2c
  have h5c := add_poly (fun p => (c p+c p)+(c p+c p)) c h4c hc
  have hsum := add_poly l (fun p => ((c p+c p)+(c p+c p))+c p) hl h5c
  have h := TM2Compose.isPolyTime_comp (fun p => l p+(((c p+c p)+(c p+c p))+c p))
    (fun n : Nat => n+6) hsum (TM2FixedRows.addFixed_isPolyTime 6)
  change IsPolyTime (fun p : Request => Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length+1)
  convert h using 1
  funext p
  simp [l,c,expected,ticks,rest,data,Source284CertificateDispatch.rewindStart]
  omega

def boundaryAcceptBranch (p : Request) : EncRow × EncRow :=
  ((false,true,true,rewindTarget p),(true,true,true,rewindTarget p))

theorem boundaryAcceptBranch_isPolyTime : IsPolyTime boundaryAcceptBranch := by
  have hf : IsPolyTime (fun _ : Request => false) := TM2Constant.isPolyTime false
  have ht : IsPolyTime (fun _ : Request => true) := TM2Constant.isPolyTime true
  have h0 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ rewindTarget hf ht ht rewindTarget_isPolyTime
  have h1 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ rewindTarget ht ht ht rewindTarget_isPolyTime
  exact TM2GuardAllStep.pair_isPolyTime _ _ h0 h1

theorem boundaryAcceptBranch_correct (p : Request) (mode : Nat)
    (hm : mode = 0 ∨ mode = 3)
    (hq : p.2-1 = Source284CertificateValidator.boundary p.1.1 p.1.2.1.length mode)
    (hpos : 0 < p.2) : boundaryAcceptBranch p = rowWorker p := by
  have hb : p.2-1 < Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length := by
    rcases hm with rfl | rfl <;>
      simp [Source284CertificateValidator.boundary,Source284CertificateGrammarClock.state,
        Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
        Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
        Source284CertificateDispatch.width] at * <;> omega
  have hn : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    rcases hm with rfl | rfl <;>
      simp [Source284CertificateValidator.boundary,Source284CertificateGrammarClock.state,
        Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
        Source284CertificateDispatch.width] at * <;> omega
  have ht (b : Bool) := Source284VerifierHandoff.validator_row p.1.1 p.1.2.1.length
    (Source284ListTables.table (decodeRows p.1.2.2)) (p.2-1) b hb hn
  have hr (b : Bool) := Source284CertificateDispatch.boundary_accept p.1.1 p.1.2.1.length mode hm b
  rw [← hq] at hr
  have hq0 : p.2 ≠ 0 := by omega
  simp [rowWorker,Source284FacingAdapter.table,hq0,ht,hr,Source284HardwireTable.shiftRow,
    encodeRow,boundaryAcceptBranch,rewindTarget,Nat.add_comm]

theorem boundaryRejectBranch_correct (p : Request) (mode : Nat)
    (hm : mode < 5) (h0 : mode ≠ 0) (h3 : mode ≠ 3)
    (hq : p.2-1 = Source284CertificateValidator.boundary p.1.1 p.1.2.1.length mode)
    (hpos : 0 < p.2) : sinkBranch p = rowWorker p := by
  have hb : p.2-1 < Source284CertificateDispatch.allocated p.1.1 p.1.2.1.length := by
    simp [Source284CertificateValidator.boundary,Source284CertificateGrammarClock.state,
      Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width] at *
    omega
  have hn : p.2-1 ≠ Source284CertificateDispatch.handoff p.1.1 p.1.2.1.length := by
    simp [Source284CertificateValidator.boundary,Source284CertificateGrammarClock.state,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width] at *
    omega
  have ht (b : Bool) := Source284VerifierHandoff.validator_row p.1.1 p.1.2.1.length
    (Source284ListTables.table (decodeRows p.1.2.2)) (p.2-1) b hb hn
  have hr (b : Bool) := Source284CertificateDispatch.boundary_reject p.1.1 p.1.2.1.length mode hm h0 h3 b
  rw [← hq] at hr
  have hq0 : p.2 ≠ 0 := by omega
  simp [rowWorker,Source284FacingAdapter.table,hq0,ht,hr,Source284HardwireTable.shiftRow,
    encodeRow,sinkBranch,allocation,Source284CertificateDispatch.allocated,Nat.add_comm]

end Shared.Beeping.NPcoNP.Source284SATWorkerInputs
