import Shared.Beeping.NPcoNP.GraphRegister284
import Shared.Beeping.NPcoNP.Parent290Coalesced

/-! Exact, partial decoding of the 12-register graph syntax into the extended
register IR. Native HALF is interpreted separately from ordinary DECNZ: its
yes target is the odd-input branch. The executable checker below can compare
any supplied finite graph with a register program; it does not assert that the
pinned producer graph has been obtained or that a Python compiler is correct. -/

namespace Shared.Beeping.NPcoNP.GraphExtended284
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.GraphRegister284
open Shared.Beeping.NPcoNP.MaskInvariant
open PASoundness.RegisterMachine

deriving instance DecidableEq for Action
deriving instance DecidableEq for Shared.Beeping.NPcoNP.MaskInvariant.Instruction

/-- Parse only the exact native-HALF spelling and canonical register suffix. -/
def halfRegister (op : String) : Option (Fin 12) := do
  let cs ← match op.toList with
    | '3' :: '.' :: '$' :: 'n' :: 'a' :: 't' :: 'i' :: 'v' :: 'e' :: '-' :: 'h' :: 'a' :: 'l' :: 'f' :: ':' :: '$' :: 'c' :: 'o' :: 'a' :: 'l' :: 'e' :: 's' :: 'c' :: 'e' :: 'd' :: '.' :: cs => some cs
    | _ => none
  let (reg, rest) ← readRegister cs
  if rest == ['.', 'd', 'e', 'c', 'n', 'z'] then some reg else none

/-- The first target of native HALF is the odd branch; the second is the even
branch, as in `MaskInvariant.Action.execute`. Other supported operations are
identical to the ordinary decoder. -/
def decode (row : Row) : Option (Shared.Beeping.NPcoNP.MaskInvariant.Instruction 12 185) :=
  match GraphRegister284.decodeRow row with
  | some inst => some ⟨.base inst.operation, inst.yes, inst.no⟩
  | none => do
    let [y,n] := row.targets | none
    let yes ← targetFin y
    let no ← targetFin n
    let reg ← halfRegister row.op
    pure ⟨.half reg, yes, no⟩

/-- Executable local graph/program comparison, including failure and an absent
row. This does not accept a mismatch or ignore malformed input. -/
def rowMatches (g : Graph) (p : Shared.Beeping.NPcoNP.MaskInvariant.Program 12 185)
    (i : Fin 185) : Bool :=
  match g.rows[i.val]? with
  | none => false
  | some row =>
    match decode row with
    | none => false
    | some inst => decide (inst = p.code[i])

/-- Check the entry and every decoded row of a graph against a program. -/
def graphMatches (g : Graph) (p : Shared.Beeping.NPcoNP.MaskInvariant.Program 12 185) : Bool :=
  (g.rows.size == 185) && (g.entry == p.start.val) &&
    (List.finRange 185).all (rowMatches g p)

theorem rowMatches_sound (g : Graph) (p : Shared.Beeping.NPcoNP.MaskInvariant.Program 12 185)
    (i : Fin 185) (h : rowMatches g p i = true) :
    ∃ row, g.rows[i.val]? = some row ∧ decode row = some p.code[i] := by
  unfold rowMatches at h
  cases hr : g.rows[i.val]? with
  | none => simp [hr] at h
  | some row =>
    cases hd : decode row with
    | none => simp [hr, hd] at h
    | some inst =>
      have he : inst = p.code[i] := by simpa [hr, hd] using h
      exact ⟨row, rfl, by simpa [he] using hd⟩

theorem graphMatches_sound (g : Graph) (p : Shared.Beeping.NPcoNP.MaskInvariant.Program 12 185)
    (h : graphMatches g p = true) :
    g.rows.size = 185 ∧ g.entry = p.start.val ∧
      ∀ i : Fin 185, ∃ row, g.rows[i.val]? = some row ∧ decode row = some p.code[i] := by
  simp only [graphMatches, Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨h.1.1, h.1.2, ?_⟩
  intro i
  apply rowMatches_sound
  exact List.all_eq_true.mp h.2 i (List.mem_finRange i)

/-- Specialization to the currently generated coalesced program: success of
this executable check suffices for every row and the entry to agree. No graph
is asserted to pass it. -/
theorem target_sound (g : Graph)
    (h : graphMatches g Shared.Beeping.NPcoNP.Parent290Coalesced.target = true) :
    g.rows.size = 185 ∧ g.entry = Shared.Beeping.NPcoNP.Parent290Coalesced.target.start.val ∧
      ∀ i : Fin 185, ∃ row, g.rows[i.val]? = some row ∧
        decode row = some Shared.Beeping.NPcoNP.Parent290Coalesced.target.code[i] :=
  graphMatches_sound g _ h

example : decode ⟨"3.$native-half:$coalesced.2.decnz", [71,77]⟩ =
    some ⟨.half 2, 71, 77⟩ := by decide
example : decode ⟨"3.$coalesced.8.decnz", [72,73]⟩ =
    some ⟨.base (.decNZ 8), 72, 73⟩ := by decide
example : decode ⟨"3.$native-half:$coalesced.12.decnz", [71,77]⟩ = none := by decide
example : decode ⟨"3.$native-half:$coalesced.2.decnz", [71,185]⟩ = none := by decide
example : decode ⟨"3.$native-half:$coalesced.2.decnz", [71]⟩ = none := by decide
example : decode ⟨"3.$native-half:$coalesced.2.inc", [71,77]⟩ = none := by decide
example (b : Bank 12) (h : b 2 = 5) :
    ((Action.half 2).execute b).success = true ∧ ((Action.half 2).execute b).bank 2 = 2 := by
  simp [Action.execute, write, h]
example (b : Bank 12) (h : b 2 = 4) :
    ((Action.half 2).execute b).success = false ∧ ((Action.half 2).execute b).bank 2 = 2 := by
  simp [Action.execute, write, h]

end Shared.Beeping.NPcoNP.GraphExtended284
