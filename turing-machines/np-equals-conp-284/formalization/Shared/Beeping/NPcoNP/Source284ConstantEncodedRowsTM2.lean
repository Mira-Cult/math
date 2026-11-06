import Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2
import Shared.ComplexityBridge.TM2FixedRows
import Shared.ComplexityBridge.TM2EmptyConstant
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2ListAppend

/-! A fixed finite relative table can be emitted by a canonical polynomial-time
machine. Each binary numeric constant and every tuple/list constructor is
charged. This does not reify function-valued machine descriptions. -/
namespace Shared.Beeping.NPcoNP.Source284ConstantEncodedRowsTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284HardwireEncodedWorkersTM2

private theorem constNat {α : Type} [BitstringEncoding α] (n : Nat) :
    IsPolyTime (fun _ : α => n) := by
  have h := TM2Compose.isPolyTime_comp (fun _ : α => (0 : Nat)) (fun x : Nat => x+n)
    TM2EmptyConstant.zero_isPolyTime (TM2FixedRows.addFixed_isPolyTime n)
  simpa using h

theorem constRow_isPolyTime {α : Type} [BitstringEncoding α] (r : EncRow) :
    IsPolyTime (fun _ : α => r) := by
  rcases r with ⟨w,t,c,n⟩
  have h := row_isPolyTime (fun _ : α => w) (fun _ => t) (fun _ => c) (fun _ => n)
    (TM2Constant.isPolyTime w) (TM2Constant.isPolyTime t) (TM2Constant.isPolyTime c) (constNat n)
  exact h

theorem constPair_isPolyTime {α : Type} [BitstringEncoding α] (r : EncRow × EncRow) :
    IsPolyTime (fun _ : α => r) := by
  rcases r with ⟨a,b⟩
  exact TM2GuardAllStep.pair_isPolyTime (fun _ : α => a) (fun _ => b)
    (constRow_isPolyTime a) (constRow_isPolyTime b)

/-- An arbitrary fixed finite encoded table has a polynomial-time emitter;
the fixed table may contain invalid or very large destinations. -/
theorem constRows_isPolyTime {α : Type} [BitstringEncoding α] (rows : EncRows) :
    IsPolyTime (fun _ : α => rows) := by
  induction rows with
  | nil => exact TM2EmptyConstant.isPolyTime [] rfl
  | cons row rows ih =>
    have h := TM2Compose.isPolyTime_comp (fun x : α => (row,rows))
      (TM2ListAppend.cons (α := EncRow × EncRow))
      (TM2GuardAllStep.pair_isPolyTime (fun _ : α => row) (fun _ => rows)
        (constPair_isPolyTime row) ih) TM2ListAppend.cons_isPolyTime
    change IsPolyTime (fun _ : α => row::rows)
    simpa [TM2ListAppend.cons] using h

end Shared.Beeping.NPcoNP.Source284ConstantEncodedRowsTM2
