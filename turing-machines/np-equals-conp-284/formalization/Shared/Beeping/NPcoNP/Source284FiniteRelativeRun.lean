import Shared.Beeping.NPcoNP.Source284FiniteRelativeRows

/-! Compose the finite-program row adapter with the existing equal-clock
source execution theorems. The finite input list is blank-extended on the
positive tape half and the negative half is zero. This result does not load a
witness, charge table generation, or connect to the literal 284-state table. -/
namespace Shared.Beeping.NPcoNP.Source284FiniteRelativeRun

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284ListTables
open Shared.Beeping.NPcoNP.Source284FiniteRelativeRows
open Shared.Codes.BitNumeralCompare (value)

/-- The finite relative row list is an exact alternate presentation of the
compiled program, including the sentinel tail used by that compilation. -/
theorem encode_eq_compile (p : Program) :
    Source284TableEncode.encode (rows p).length (table (rows p)) 1 =
      Source284CompileRecords.compile p := by
  simp only [Source284TableEncode.encode, Source284CompileRecords.compile, records_eq]

/-- With valid continuations, a run of the finite relative table accepts at
exactly the same clock as the original finite program. The certificate/negative
tape half is zero. The list's length is not itself recoverable from its numeric
value; the finite program reads the corresponding blank-extended tape. -/
theorem bounded_acceptance (p : Program) (input : List Bool) (clock : Nat)
    (hv : valid p = true) :
    (Source284TableRun.run (table (rows p)) ⟨0, value input, some 0⟩ clock).state.isNone = true ↔
      bounded p input clock = some true := by
  have hn : 0 < (rows p).length := by simp [rows_length]
  have h := Source284TableRun.bounded_acceptance (rows p).length (table (rows p)) 1 hn
    (closed p hv) (value input) 0 clock
  rw [encode_eq_compile] at h
  rw [← h]
  exact Source284FiniteProgramRun.bounded_acceptance_shared p input clock hv

end Shared.Beeping.NPcoNP.Source284FiniteRelativeRun
