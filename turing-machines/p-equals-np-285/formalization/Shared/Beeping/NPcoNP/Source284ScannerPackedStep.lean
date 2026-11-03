import Shared.Beeping.NPcoNP.Source284ScannerFoldStep

/-! Reassociate the scanner fold state to match the actual generic TM2 fold
loader: `(status,index)` is the first field and the accumulator is the
second. This proves a polynomial-time step and finite-fold correspondence;
it does not itself prove a polynomial-time complete fold. -/
namespace Shared.Beeping.NPcoNP.Source284ScannerPackedStep

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284RecordBitCost

abbrev Packed := (Bool × List Bool) × List Bool
abbrev Input := Packed × Bool

def unpack (s : Packed) : Source284ScannerFoldStep.State := (s.1.1,(s.1.2,s.2))
def pack (s : Source284ScannerFoldStep.State) : Packed := ((s.1,s.2.1),s.2.2)

@[simp] theorem unpack_pack (s : Source284ScannerFoldStep.State) : unpack (pack s) = s := by
  rcases s with ⟨d,i,a⟩
  rfl

@[simp] theorem pack_unpack (s : Packed) : pack (unpack s) = s := by
  rcases s with ⟨⟨d,i⟩,a⟩
  rfl

def step (p : Input) : Packed := pack (Source284ScannerFoldStep.step (unpack p.1,p.2))

theorem unpack_isPolyTime : ComplexityTheory.IsPolyTime unpack := by
  let first : Packed → Bool × List Bool := fun p => p.1
  let last : Packed → List Bool := fun p => p.2
  let flag : Packed → Bool := fun p => p.1.1
  let idx : Packed → List Bool := fun p => p.1.2
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hl : ComplexityTheory.IsPolyTime last := TM2GuardAllStep.second_isPolyTime
  have hd : ComplexityTheory.IsPolyTime flag :=
    TM2Compose.isPolyTime_comp first (fun p : Bool × List Bool => p.1) hf TM2PairFirst.first_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx :=
    TM2Compose.isPolyTime_comp first (fun p : Bool × List Bool => p.2) hf TM2GuardAllStep.second_isPolyTime
  have hfields := TM2GuardAllStep.pair_isPolyTime idx last hi hl
  have h := TM2GuardAllStep.pair_isPolyTime flag (fun p => (idx p,last p)) hd hfields
  change ComplexityTheory.IsPolyTime unpack
  exact h

theorem pack_isPolyTime : ComplexityTheory.IsPolyTime pack := by
  let first : Source284ScannerFoldStep.State → Bool := fun p => p.1
  let rest : Source284ScannerFoldStep.State → List Bool × List Bool := fun p => p.2
  let idx : Source284ScannerFoldStep.State → List Bool := fun p => p.2.1
  let last : Source284ScannerFoldStep.State → List Bool := fun p => p.2.2
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hr : ComplexityTheory.IsPolyTime rest := TM2GuardAllStep.second_isPolyTime
  have hi : ComplexityTheory.IsPolyTime idx :=
    TM2Compose.isPolyTime_comp rest (fun p : List Bool × List Bool => p.1) hr TM2PairFirst.first_isPolyTime
  have hl : ComplexityTheory.IsPolyTime last :=
    TM2Compose.isPolyTime_comp rest (fun p : List Bool × List Bool => p.2) hr TM2GuardAllStep.second_isPolyTime
  have hfields := TM2GuardAllStep.pair_isPolyTime first idx hf hi
  have h := TM2GuardAllStep.pair_isPolyTime (fun p => (first p,idx p)) last hfields hl
  change ComplexityTheory.IsPolyTime pack
  exact h

theorem step_isPolyTime : ComplexityTheory.IsPolyTime step := by
  let first : Input → Packed := fun p => p.1
  let bit : Input → Bool := fun p => p.2
  let source : Input → Source284ScannerFoldStep.State := fun p => unpack (first p)
  let args : Input → Source284ScannerFoldStep.Input := fun p => (source p,bit p)
  have hf : ComplexityTheory.IsPolyTime first := TM2PairFirst.first_isPolyTime
  have hb : ComplexityTheory.IsPolyTime bit := TM2GuardAllStep.second_isPolyTime
  have hs : ComplexityTheory.IsPolyTime source := TM2Compose.isPolyTime_comp first unpack hf unpack_isPolyTime
  have ha : ComplexityTheory.IsPolyTime args := TM2GuardAllStep.pair_isPolyTime source bit hs hb
  have hm := TM2Compose.isPolyTime_comp args Source284ScannerFoldStep.step ha
    Source284ScannerFoldStep.step_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun p => Source284ScannerFoldStep.step (args p)) pack hm pack_isPolyTime
  change ComplexityTheory.IsPolyTime step
  exact h

theorem fold_transport (s : Packed) (code : List Bool) :
    TM2PolynomialFold.fold step s code =
      pack (TM2PolynomialFold.fold Source284ScannerFoldStep.step (unpack s) code) := by
  induction code generalizing s with
  | nil => simp [TM2PolynomialFold.fold]
  | cons b bs ih =>
    change TM2PolynomialFold.fold step (step (s,b)) bs =
      pack (TM2PolynomialFold.fold Source284ScannerFoldStep.step
        (Source284ScannerFoldStep.step (unpack s,b)) bs)
    rw [ih]
    simp [step]

theorem fold_correct (code idx : List Bool) :
    (TM2PolynomialFold.fold step ((false,idx),[]) code).2.reverse = scan code idx := by
  rw [fold_transport]
  simpa [pack, unpack] using Source284ScannerFoldStep.fold_correct code idx

end Shared.Beeping.NPcoNP.Source284ScannerPackedStep
