import Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
import Shared.Beeping.NPcoNP.Source284SATVerifier

/-! A fixed finite relative table for the independently defined all-bitstrings
SAT verifier. This is an equal-clock semantic theorem, not a construction of
the framed source input, a witness loader, or a literal 284-state simulation. -/
namespace Shared.Beeping.NPcoNP.Source284SATRelativeRun

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284ListTables
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRows
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
open Shared.Beeping.NPcoNP.Source284SATVerifier
open Shared.ComplexityBridge.BoundedHardness
open Shared.Codes.BitNumeralCompare (value)

/-- There is one valid finite program whose explicit relative table accepts
the canonical pair of a public input and an originally bounded list witness
exactly when the all-bitstrings SAT language accepts that input. All witnesses
under the bound use the same polynomial clock. The canonical pair occupies the
blank-extended positive tape half, and the negative tape half is zero. -/
theorem sat_fixed_relative_verifier :
    ∃ (program : Program) (clock : Polynomial Nat), valid program = true ∧
      ∀ x : List Bool,
        Shared.ComplexityBridge.CNF.sat x = true ↔
          ∃ w : List Bool, w.length ≤ x.length ∧
            (Source284TableRun.run (table (rows program))
              ⟨0, value (BitstringEncoding.bitEncode (x,w)), some 0⟩
              (commonFuel Polynomial.X clock x)).state.isNone = true := by
  obtain ⟨program,clock,hvalid,hprogram⟩ :=
    valid_pair_verifier Shared.ComplexityBridge.CNFWitness.verify
      Shared.ComplexityBridge.TM2PreparedVerify.verify_isPolyTime
  refine ⟨program,clock,hvalid,?_⟩
  intro x
  rw [Shared.ComplexityBridge.CNFWitness.sat_iff_bounded_verifier]
  apply exists_congr
  intro w
  apply and_congr_right
  intro hw
  have hfuel := commonFuel_correct Shared.ComplexityBridge.CNFWitness.verify
    program Polynomial.X clock hprogram x w (by simpa using hw)
  rw [bounded_acceptance program _ _ hvalid, hfuel]
  simp

end Shared.Beeping.NPcoNP.Source284SATRelativeRun
