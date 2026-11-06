import Shared.Beeping.NPcoNP.Source284SATGrammarWorker
import Shared.ComplexityBridge.TM2BoundedUnary

/-! Polynomial selectors for the bounded SAT table-row worker. Thresholds are
materialized under an explicit unary budget; no unbounded-integer unit cost
is used. The branch assembly is proved separately. -/
namespace Shared.Beeping.NPcoNP.Source284SATWorkerSelect

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284SATProducerIteration
open Shared.Beeping.NPcoNP.Source284SATWorkerInputs

abbrev ThresholdRequest := Request × Nat

/-- Compare the clipped row index with a clipped threshold. -/
def below (p : ThresholdRequest) : Bool :=
  TM2BoundedWitnessGuard.guard
    (TM2BoundedUnary.expand (budget p.1.1,p.2),prefixIndex p.1)

theorem below_isPolyTime : IsPolyTime below := by
  let request : ThresholdRequest → Request := fun p => p.1
  let threshold : ThresholdRequest → Nat := fun p => p.2
  let data : ThresholdRequest → Input := fun p => (request p).1
  let tokens : ThresholdRequest → List Bool := fun p => budget (data p)
  let limit : ThresholdRequest → List Bool := fun p => TM2BoundedUnary.expand (tokens p,threshold p)
  let index : ThresholdRequest → Nat := fun p => prefixIndex (request p)
  have hr : IsPolyTime request := TM2PairFirst.first_isPolyTime
  have hh : IsPolyTime threshold := TM2GuardAllStep.second_isPolyTime
  have hd : IsPolyTime data := TM2Compose.isPolyTime_comp request (fun p : Request => p.1)
    hr TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have hl : IsPolyTime limit := TM2Compose.isPolyTime_comp (fun p => (tokens p,threshold p))
    TM2BoundedUnary.expand (TM2GuardAllStep.pair_isPolyTime tokens threshold ht hh)
    TM2BoundedUnary.expand_isPolyTime
  have hi : IsPolyTime index := TM2Compose.isPolyTime_comp request prefixIndex hr prefixIndex_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p => (limit p,index p)) TM2BoundedWitnessGuard.guard
    (TM2GuardAllStep.pair_isPolyTime limit index hl hi) TM2BoundedWitnessGuard.guard_isPolyTime

theorem below_correct (p : Request) (threshold : Nat)
    (hbound : p.2 ≤ (budget p.1).length) (hthreshold : threshold ≤ (budget p.1).length) :
    below (p,threshold) = decide (p.2-1 < threshold) := by
  simp [below,TM2TapePairs.guard_eq_decide,TM2BoundedUnary.expand_correct,
    Nat.min_eq_left hthreshold,prefixIndex_correct p hbound]

def grammarEnd (p : Request) : Nat :=
  TM2BoundedSubtract.subtract (budget p.1,(rewindTarget p,6))

theorem grammarEnd_isPolyTime : IsPolyTime grammarEnd := by
  let data : Request → Input := fun p => p.1
  let tokens : Request → List Bool := fun p => budget (data p)
  let six : Request → Nat := fun _ => 6
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have hz : IsPolyTime (fun _ : Request => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have hs : IsPolyTime six := by
    have h := TM2Compose.isPolyTime_comp (fun _ : Request => (0 : Nat))
      (fun n : Nat => n+6) hz (TM2FixedRows.addFixed_isPolyTime 6)
    simpa [six] using h
  have ha := TM2GuardAllStep.pair_isPolyTime tokens (fun p => (rewindTarget p,six p)) ht
    (TM2GuardAllStep.pair_isPolyTime rewindTarget six rewindTarget_isPolyTime hs)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,(rewindTarget p,six p)))
    TM2BoundedSubtract.subtract ha TM2BoundedSubtract.subtract_isPolyTime

theorem grammarEnd_correct (p : Request) :
    grammarEnd p = p.1.1.length+5*p.1.2.1.length := by
  have htarget : rewindTarget p ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp [rewindTarget,Source284CertificateDispatch.rewindStart]
    omega
  have hsix : 6 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    omega
  rw [grammarEnd,TM2BoundedSubtract.subtract_exact _ _ _ htarget hsix]
  simp [rewindTarget,Source284CertificateDispatch.rewindStart]

def rewindEnd (p : Request) : Nat :=
  TM2BoundedSubtract.subtract (budget p.1,(allocation p.1,3))

theorem rewindEnd_isPolyTime : IsPolyTime rewindEnd := by
  let data : Request → Input := fun p => p.1
  let tokens : Request → List Bool := fun p => budget (data p)
  let alloc : Request → Nat := fun p => allocation (data p)
  let three : Request → Nat := fun _ => 3
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have ha : IsPolyTime alloc := TM2Compose.isPolyTime_comp data allocation hd allocation_isPolyTime
  have hz : IsPolyTime (fun _ : Request => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have h3 : IsPolyTime three := by
    have h := TM2Compose.isPolyTime_comp (fun _ : Request => (0 : Nat))
      (fun n : Nat => n+3) hz (TM2FixedRows.addFixed_isPolyTime 3)
    simpa [three] using h
  have hargs := TM2GuardAllStep.pair_isPolyTime tokens (fun p => (alloc p,three p)) ht
    (TM2GuardAllStep.pair_isPolyTime alloc three ha h3)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,(alloc p,three p)))
    TM2BoundedSubtract.subtract hargs TM2BoundedSubtract.subtract_isPolyTime

theorem rewindEnd_correct (p : Request) :
    rewindEnd p = Source284CertificateDispatch.rewindStart p.1.1 p.1.2.1.length +
      Source284CertificateDispatch.width p.1.1 p.1.2.1.length := by
  have halloc : allocation p.1 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
      Source284CertificateDispatch.handoff,Source284CertificateDispatch.rewindStart,
      Source284CertificateDispatch.width]
    omega
  have hthree : 3 ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    omega
  rw [rewindEnd,TM2BoundedSubtract.subtract_exact _ _ _ halloc hthree]
  simp [allocation,Source284CertificateDispatch.allocated,Source284CertificateDispatch.sink,
    Source284CertificateDispatch.handoff]

/-- A threshold supplied by a polynomial-time function can be tested in
polynomial time on every encoded request. -/
def test (threshold : Request → Nat) (p : Request) : Bool := below (p,threshold p)

theorem test_isPolyTime (threshold : Request → Nat) (h : IsPolyTime threshold) :
    IsPolyTime (test threshold) := by
  have hid : IsPolyTime (id : Request → Request) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  exact TM2Compose.isPolyTime_comp (fun p : Request => (p,threshold p)) below
    (TM2GuardAllStep.pair_isPolyTime id threshold hid h) below_isPolyTime

def prefixEnd (p : Request) : Nat := p.1.1.length

theorem prefixEnd_isPolyTime : IsPolyTime prefixEnd := by
  let data : Request → Input := fun p => p.1
  let bits : Request → List Bool := fun p => (data p).1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hb : IsPolyTime bits := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  exact TM2Compose.isPolyTime_comp bits List.length hb TM2BinaryListLength.length_isPolyTime

def shifted (f : Request → Nat) (n : Nat) (p : Request) : Nat := f p+n

theorem shifted_isPolyTime (f : Request → Nat) (n : Nat) (hf : IsPolyTime f) :
    IsPolyTime (shifted f n) :=
  TM2Compose.isPolyTime_comp f (fun x : Nat => x+n) hf (TM2FixedRows.addFixed_isPolyTime n)

def isZero (p : Request) : Bool := !TM2BoundedWitnessGuard.numericNe (p.2,0)

theorem isZero_isPolyTime : IsPolyTime isZero := by
  have hi : IsPolyTime (fun p : Request => p.2) := TM2GuardAllStep.second_isPolyTime
  have hz : IsPolyTime (fun _ : Request => (0 : Nat)) := TM2EmptyConstant.zero_isPolyTime
  have hn := TM2Compose.isPolyTime_comp (fun p : Request => (p.2,0))
    TM2BoundedWitnessGuard.numericNe (TM2GuardAllStep.pair_isPolyTime _ _ hi hz)
    TM2BoundedWitnessGuard.numericNe_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Request => TM2BoundedWitnessGuard.numericNe (p.2,0))
    Bool.not hn TM2GateDispatch.not_isPolyTime

theorem isZero_correct (p : Request) : isZero p = true ↔ p.2 = 0 := by
  simp [isZero,TM2BoundedWitnessGuard.numericNe]

/-- Every arm is total and charged on arbitrary requests, even though only
one arm is selected for a valid row. -/
def select (p : Request) : Source284EncodedRows.EncRow × Source284EncodedRows.EncRow :=
  if inBudget p then
    if isZero p then initialBranch p
    else if test prefixEnd p then prefixBranch p
    else if test grammarEnd p then Source284SATGrammarWorker.branch p
    else if test (shifted grammarEnd 1) p then boundaryAcceptBranch p
    else if test (shifted grammarEnd 3) p then sinkBranch p
    else if test (shifted grammarEnd 4) p then boundaryAcceptBranch p
    else if test (shifted grammarEnd 5) p then sinkBranch p
    else if test rewindEnd p then continuingBranch false p
    else if test (shifted rewindEnd 1) p then continuingBranch true p
    else if test (shifted rewindEnd 2) p then handoffBranch p
    else if test (shifted rewindEnd 3) p then sinkBranch p
    else verifierBranch p
  else ((false,false,false,0),(false,false,false,0))

theorem select_isPolyTime : IsPolyTime select := by
  have hdefault : IsPolyTime (fun _ : Request =>
      (((false,false,false,0),(false,false,false,0)) : Source284EncodedRows.EncRow × Source284EncodedRows.EncRow)) :=
    Source284ConstantEncodedRowsTM2.constPair_isPolyTime _
  have hR3 := test_isPolyTime (shifted rewindEnd 3) (shifted_isPolyTime _ _ rewindEnd_isPolyTime)
  have hR2 := test_isPolyTime (shifted rewindEnd 2) (shifted_isPolyTime _ _ rewindEnd_isPolyTime)
  have hR1 := test_isPolyTime (shifted rewindEnd 1) (shifted_isPolyTime _ _ rewindEnd_isPolyTime)
  have hR := test_isPolyTime rewindEnd rewindEnd_isPolyTime
  have hG5 := test_isPolyTime (shifted grammarEnd 5) (shifted_isPolyTime _ _ grammarEnd_isPolyTime)
  have hG4 := test_isPolyTime (shifted grammarEnd 4) (shifted_isPolyTime _ _ grammarEnd_isPolyTime)
  have hG3 := test_isPolyTime (shifted grammarEnd 3) (shifted_isPolyTime _ _ grammarEnd_isPolyTime)
  have hG1 := test_isPolyTime (shifted grammarEnd 1) (shifted_isPolyTime _ _ grammarEnd_isPolyTime)
  have hG := test_isPolyTime grammarEnd grammarEnd_isPolyTime
  have hP := test_isPolyTime prefixEnd prefixEnd_isPolyTime
  have a := TM2If.if_isPolyTime _ _ _ hR3 sinkBranch_isPolyTime verifierBranch_isPolyTime
  have b := TM2If.if_isPolyTime _ _ _ hR2 handoffBranch_isPolyTime a
  have c := TM2If.if_isPolyTime _ _ _ hR1 (continuingBranch_isPolyTime true) b
  have d := TM2If.if_isPolyTime _ _ _ hR (continuingBranch_isPolyTime false) c
  have e := TM2If.if_isPolyTime _ _ _ hG5 sinkBranch_isPolyTime d
  have f := TM2If.if_isPolyTime _ _ _ hG4 boundaryAcceptBranch_isPolyTime e
  have g := TM2If.if_isPolyTime _ _ _ hG3 sinkBranch_isPolyTime f
  have h := TM2If.if_isPolyTime _ _ _ hG1 boundaryAcceptBranch_isPolyTime g
  have i := TM2If.if_isPolyTime _ _ _ hG Source284SATGrammarWorker.branch_isPolyTime h
  have j := TM2If.if_isPolyTime _ _ _ hP prefixBranch_isPolyTime i
  have k := TM2If.if_isPolyTime _ _ _ isZero_isPolyTime initialBranch_isPolyTime j
  exact TM2If.if_isPolyTime _ _ _ inBudget_isPolyTime k hdefault

theorem boundedRowWorker_isPolyTime_of_eq (h : select = boundedRowWorker) :
    IsPolyTime boundedRowWorker := by
  rw [← h]
  exact select_isPolyTime

end Shared.Beeping.NPcoNP.Source284SATWorkerSelect
