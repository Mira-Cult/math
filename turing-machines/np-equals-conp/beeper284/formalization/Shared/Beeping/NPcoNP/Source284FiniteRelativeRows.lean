import Shared.Beeping.NPcoNP.Source284ListTables
import Shared.Beeping.NPcoNP.Source284FiniteProgramRun

/-! The fixed finite-program compiler already allocates two orientation states
per absolute state, together with two orientations of its reject sink. This
file presents those same rows as an executable finite list in the shared
relative-table format. It does not prove a uniform running-time bound for
building this list or construct a witness loader. -/
namespace Shared.Beeping.NPcoNP.Source284FiniteRelativeRows

open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284ListTables


/-- The relative index for a physical state and tape orientation. -/
def index (q : Nat) (rev : Bool) : Nat := 2*q + Source284CompileRecords.bit rev

/-- Translation of an actual finite-program row. False or invalid terminal
outcomes enter the reserved reject sink, while true enters acceptance. -/
def translate (p : Program) (rev : Bool) (r : Row) : Source284TableEncode.Row :=
  let leftward := !r.2.1
  ⟨r.1, xor rev leftward,
    if r.2.2.2 = 0 then some (index r.2.2.1 leftward)
    else if r.2.2.2 = 2 then none else some (index p.length false)⟩

/-- At out-of-range finite-program states the compiler uses its reject sink.
Only the two allocated sink orientations are used in the finite row list. -/
def row (p : Program) (s : Nat) (read : Bool) : Source284TableEncode.Row :=
  let q := s / 2
  let rev := decide (s % 2 = 1)
  match p[q]? with
  | some pair => translate p rev (if read then pair.2 else pair.1)
  | none => ⟨read, rev, some (index p.length false)⟩

def rows (p : Program) : Rows :=
  List.ofFn (fun s : Fin (2*(p.length+1)) => (row p s.val false, row p s.val true))

@[simp] theorem rows_length (p : Program) : (rows p).length = 2*(p.length+1) := by
  simp only [rows, List.length_ofFn]

@[simp] theorem active_index (q : Nat) (rev : Bool) :
    Source284TableEncode.active (index q rev) = Source284CompileRecords.codeState q rev := by
  cases rev <;> simp [Source284TableEncode.active, index, Source284CompileRecords.codeState, Source284CompileRecords.bit] <;> omega

@[simp] theorem translate_code (p : Program) (rev : Bool) (r : Row) :
    Source284TableEncode.rowCode (translate p rev r) = Source284CompileRecords.encodedRow p.length rev r := by
  by_cases h0 : r.2.2.2 = 0
  · simp [translate, Source284TableEncode.rowCode, Source284TableEncode.nextState,
      Source284CompileRecords.encodedRow, Source284CompileRecords.pack, h0,
      Source284TableEncode.bit, Source284CompileRecords.bit]
  · by_cases h2 : r.2.2.2 = 2
    · simp [translate, Source284TableEncode.rowCode, Source284TableEncode.nextState,
        Source284CompileRecords.encodedRow, Source284CompileRecords.pack, h0, h2,
        Source284TableEncode.bit, Source284CompileRecords.bit]
    · simp [translate, Source284TableEncode.rowCode, Source284TableEncode.nextState,
        Source284CompileRecords.encodedRow, Source284CompileRecords.pack, h0, h2,
        Source284TableEncode.bit, Source284CompileRecords.bit, Source284CompileRecords.rejectState]

@[simp] theorem sink_code (p : Program) (rev read : Bool) :
    Source284TableEncode.rowCode ⟨read, rev, some (index p.length false)⟩ =
      Source284CompileRecords.pack read rev (Source284CompileRecords.rejectState p.length) := by
  simp [Source284TableEncode.rowCode, Source284TableEncode.nextState, Source284CompileRecords.pack, Source284CompileRecords.rejectState, Source284TableEncode.bit, Source284CompileRecords.bit]

/-- The list lookup agrees with the explicitly generated row in range. -/
theorem table_row (p : Program) (s : Nat) (hs : s < 2*(p.length+1)) (read : Bool) :
    table (rows p) s read = row p s read := by
  have hs' : s < (rows p).length := by simpa using hs
  rw [table_in_range _ _ hs']
  cases read <;> simp only [rows, List.getElem_ofFn, Bool.false_eq_true, ↓reduceIte]

/-- The two source encoders enumerate precisely the same records. -/
theorem records_eq (p : Program) :
    Source284TableEncode.records (rows p).length (table (rows p)) = Source284CompileRecords.records p := by
  apply List.ext_getElem
  · simp only [Source284TableEncode.records, Source284CompileRecords.records, List.length_ofFn, rows_length]
    omega
  · intro i h₁ h₂
    have hi : i < 4*(p.length+1) := by
      simp only [Source284CompileRecords.records, List.length_ofFn] at h₂
      exact h₂
    have hs : i / 2 < 2*(p.length+1) := by omega
    simp only [Source284TableEncode.records, Source284CompileRecords.records, List.getElem_ofFn]
    rw [table_row p (i / 2) hs]
    have hq : (i / 2) / 2 = i / 4 := by omega
    simp only [row, hq, Source284CompileRecords.recordAt]
    by_cases hh : i / 4 < p.length
    · simp [List.getElem?_eq_getElem hh, hh, translate_code]
    · have hge : p.length ≤ i / 4 := by omega
      simp [List.getElem?_eq_none hge, hh, sink_code]

/-- Valid program continuations remain in the allocated finite relative
state range; terminal outcomes go to acceptance or the reserved sink. -/
theorem closed (p : Program) (hv : valid p = true) :
    Shared.Beeping.NPcoNP.Source284TableRun.Closed (rows p).length (table (rows p)) := by
  intro s hs read next hn
  have hs' : s < 2*(p.length+1) := by simpa using hs
  rw [table_row p s hs'] at hn
  have hc := Source284FiniteProgramRun.closed_of_valid p hv
  by_cases hq : s / 2 < p.length
  · simp only [row, List.getElem?_eq_getElem hq, Option.get_some] at hn
    by_cases htag : (if read then p[s/2].2 else p[s/2].1).2.2.2 = 0
    · simp only [translate, htag, ↓reduceIte, Option.some.injEq] at hn
      subst next
      have hd := hc (s/2) hq read htag
      simp only [rows_length, index]
      have hb := Source284CompileRecords.bit_lt (!(if read then p[s / 2].2 else p[s / 2].1).2.1)
      omega
    · by_cases htwo : (if read then p[s/2].2 else p[s/2].1).2.2.2 = 2
      · simp [translate, htag, htwo] at hn
      · simp [translate, htag, htwo] at hn
        subst next
        simp [rows_length, index, Source284CompileRecords.bit]
  · have hge : p.length ≤ s / 2 := by omega
    simp [row, List.getElem?_eq_none hge, index, Source284CompileRecords.bit] at hn
    subst next
    simp [rows_length]

end Shared.Beeping.NPcoNP.Source284FiniteRelativeRows
