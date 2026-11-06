import Shared.Beeping.NPcoNP.Source284SATWorkerInputs
import Shared.Beeping.NPcoNP.Source284FiveSearchTM2
import Shared.Beeping.NPcoNP.Source284GrammarNextTM2

/-! Polynomial construction of a timed grammar row. The input index is
bounded by an explicitly charged unary list; all out-of-range calculations
remain total. This is one branch of the overall row worker. -/
namespace Shared.Beeping.NPcoNP.Source284SATGrammarWorker

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284SATProducerIteration
open Shared.Beeping.NPcoNP.Source284SATWorkerInputs
open Shared.Beeping.NPcoNP.Source284EncodedRows

private theorem add_poly {α : Type} [BitstringEncoding α] (f g : α → Nat)
    (hf : IsPolyTime f) (hg : IsPolyTime g) : IsPolyTime (fun x => f x+g x) := by
  have h := TM2Compose.isPolyTime_comp (fun x => (f x,g x)) CNFBinaryPairAdd.addPair
    (TM2GuardAllStep.pair_isPolyTime f g hf hg) CNFBinaryPairAdd.addPair_isPolyTime
  simpa [CNFBinaryPairAdd.addPair] using h

def grammarIndex (p : Request) : Nat :=
  TM2BoundedSubtract.subtract (budget p.1,(prefixIndex p,p.1.1.length))

theorem grammarIndex_isPolyTime : IsPolyTime grammarIndex := by
  let data : Request → Input := fun p => p.1
  let expected : Request → List Bool := fun p => (data p).1
  let tokens : Request → List Bool := fun p => budget (data p)
  let length : Request → Nat := fun p => (expected p).length
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have he : IsPolyTime expected := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  have ht : IsPolyTime tokens := TM2Compose.isPolyTime_comp data budget hd budget_isPolyTime
  have hl : IsPolyTime length := TM2Compose.isPolyTime_comp expected List.length
    he TM2BinaryListLength.length_isPolyTime
  have ha := TM2GuardAllStep.pair_isPolyTime tokens (fun p => (prefixIndex p,length p)) ht
    (TM2GuardAllStep.pair_isPolyTime prefixIndex length prefixIndex_isPolyTime hl)
  exact TM2Compose.isPolyTime_comp (fun p : Request => (tokens p,(prefixIndex p,length p)))
    TM2BoundedSubtract.subtract ha TM2BoundedSubtract.subtract_isPolyTime

theorem grammarIndex_correct (p : Request) (hbound : p.2 ≤ (budget p.1).length) :
    grammarIndex p = p.2-1-p.1.1.length := by
  have hl : p.1.1.length ≤ (budget p.1).length := by
    rw [budget_length,Source284SATProducerSize.rows_length]
    omega
  have hi : prefixIndex p ≤ (budget p.1).length := by
    rw [prefixIndex_correct p hbound]
    omega
  have hq : p.2-1 ≤ (budget p.1).length := by omega
  simp [grammarIndex,TM2BoundedSubtract.subtract_correct,Nat.min_eq_left hi,Nat.min_eq_left hl,
    Nat.min_eq_left hq,
    prefixIndex_correct p hbound]

def coordinate (p : Request) : Nat × Nat :=
  Source284FiveSearchTM2.select (p.1.2.1,grammarIndex p)

theorem coordinate_isPolyTime : IsPolyTime coordinate := by
  let data : Request → Input := fun p => p.1
  let rest : Request → List Bool × EncRows := fun p => (data p).2
  let ticks : Request → List Bool := fun p => (rest p).1
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have hr : IsPolyTime rest := TM2Compose.isPolyTime_comp data (fun p : Input => p.2)
    hd TM2GuardAllStep.second_isPolyTime
  have ht : IsPolyTime ticks := TM2Compose.isPolyTime_comp rest (fun p : List Bool × EncRows => p.1)
    hr TM2PairFirst.first_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : Request => (ticks p,grammarIndex p))
    Source284FiveSearchTM2.select
    (TM2GuardAllStep.pair_isPolyTime ticks grammarIndex ht grammarIndex_isPolyTime)
    Source284FiveSearchTM2.select_isPolyTime

def target (read : Bool) (p : Request) : Nat :=
  p.1.1.length + Source284FiveSearchTM2.code
    ((coordinate p).1+1,Source284GrammarNextTM2.next ((coordinate p).2,read)) + 1

theorem target_isPolyTime (read : Bool) : IsPolyTime (target read) := by
  let data : Request → Input := fun p => p.1
  let expected : Request → List Bool := fun p => (data p).1
  let length : Request → Nat := fun p => (expected p).length
  let elapsed : Request → Nat := fun p => (coordinate p).1
  let mode : Request → Nat := fun p => (coordinate p).2
  let nextElapsed : Request → Nat := fun p => elapsed p+1
  let bit : Request → Bool := fun _ => read
  let nextMode : Request → Nat := fun p => Source284GrammarNextTM2.next (mode p,bit p)
  let code : Request → Nat := fun p => Source284FiveSearchTM2.code (nextElapsed p,nextMode p)
  have hd : IsPolyTime data := TM2PairFirst.first_isPolyTime
  have he : IsPolyTime expected := TM2Compose.isPolyTime_comp data (fun p : Input => p.1)
    hd TM2PairFirst.first_isPolyTime
  have hl : IsPolyTime length := TM2Compose.isPolyTime_comp expected List.length he TM2BinaryListLength.length_isPolyTime
  have hi : IsPolyTime elapsed := TM2Compose.isPolyTime_comp coordinate (fun p : Nat × Nat => p.1)
    coordinate_isPolyTime TM2PairFirst.first_isPolyTime
  have hm : IsPolyTime mode := TM2Compose.isPolyTime_comp coordinate (fun p : Nat × Nat => p.2)
    coordinate_isPolyTime TM2GuardAllStep.second_isPolyTime
  have hn : IsPolyTime nextElapsed := TM2Compose.isPolyTime_comp elapsed (fun n : Nat => n+1)
    hi (TM2FixedRows.addFixed_isPolyTime 1)
  have hb : IsPolyTime bit := TM2Constant.isPolyTime read
  have hmode : IsPolyTime nextMode := TM2Compose.isPolyTime_comp (fun p => (mode p,bit p))
    Source284GrammarNextTM2.next (TM2GuardAllStep.pair_isPolyTime mode bit hm hb)
    Source284GrammarNextTM2.next_isPolyTime
  have hcode : IsPolyTime code := TM2Compose.isPolyTime_comp (fun p => (nextElapsed p,nextMode p))
    Source284FiveSearchTM2.code (TM2GuardAllStep.pair_isPolyTime nextElapsed nextMode hn hmode)
    Source284FiveSearchTM2.code_isPolyTime
  have hsum := add_poly length code hl hcode
  have h := TM2Compose.isPolyTime_comp (fun p => length p+code p) (fun n : Nat => n+1)
    hsum (TM2FixedRows.addFixed_isPolyTime 1)
  exact h

def branch (p : Request) : EncRow × EncRow :=
  ((false,false,true,target false p),(true,false,true,target true p))

theorem branch_isPolyTime : IsPolyTime branch := by
  have hf : IsPolyTime (fun _ : Request => false) := TM2Constant.isPolyTime false
  have ht : IsPolyTime (fun _ : Request => true) := TM2Constant.isPolyTime true
  have h0 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ (target false) hf hf ht (target_isPolyTime false)
  have h1 := Source284HardwireEncodedWorkersTM2.row_isPolyTime _ _ _ (target true) ht hf ht (target_isPolyTime true)
  exact TM2GuardAllStep.pair_isPolyTime _ _ h0 h1

/-- In the live grammar range, bounded search recovers the exact elapsed
step and mode used by the source table. -/
theorem branch_correct (p : Request) (hpos : 0 < p.2)
    (hlo : p.1.1.length ≤ p.2-1)
    (hhi : p.2-1 < p.1.1.length+5*p.1.2.1.length)
    (hbound : p.2 ≤ (budget p.1).length) : branch p = rowWorker p := by
  let d := p.2-1-p.1.1.length
  let i := d/5
  let mode := d%5
  have hd : d < 5*p.1.2.1.length := by dsimp [d]; omega
  have hi : i < p.1.2.1.length := by dsimp [i]; omega
  have hm : mode < 5 := by dsimp [mode]; omega
  have he : p.1.1.length + Source284CertificateGrammarClock.state i mode = p.2-1 := by
    dsimp [i,mode,d,Source284CertificateGrammarClock.state]
    omega
  have hc : coordinate p = (i,mode) := by
    dsimp [coordinate]
    rw [grammarIndex_correct p hbound]
    exact Source284FiveSearchTM2.select_correct p.1.2.1 d hd
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
  have hr (b : Bool) := Source284CertificateDispatch.grammar_row p.1.1 p.1.2.1.length i mode hi hm b
  rw [he] at hr
  have hq0 : p.2 ≠ 0 := by omega
  simp only [rowWorker,Source284FacingAdapter.table,hq0,↓reduceIte,ht,hr,
    Source284HardwireTable.shiftRow,encodeRow,branch,target,hc,
    Source284GrammarNextTM2.next_correct,Source284FiveSearchTM2.code,
    Source284CertificateGrammarClock.state,Option.map_some,Option.isSome_some,Option.getD_some]
  simp only [Prod.mk.injEq,true_and]
  omega

end Shared.Beeping.NPcoNP.Source284SATGrammarWorker
