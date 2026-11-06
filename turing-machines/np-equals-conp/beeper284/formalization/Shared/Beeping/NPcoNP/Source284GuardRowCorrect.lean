import Shared.Beeping.NPcoNP.Source284GuardRow

/-! Semantic correctness of one encoded countdown row, for every explicit
input row list and every source-state index. No table-enumeration or
polynomial-time theorem is asserted here. -/
namespace Shared.Beeping.NPcoNP.Source284GuardRowCorrect

open Shared.ComplexityBridge
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284BoundedPairTM2
open Shared.Beeping.NPcoNP.Source284SearchSelectTM2
open Shared.Beeping.NPcoNP.Source284CountdownSearch
open Shared.Beeping.NPcoNP.Source284TableCountdown
open Shared.Beeping.NPcoNP.Source284GuardRow

theorem selection_correct (cutoff : List Bool) (rows : EncRows) (s : Nat) (read : Bool) :
    selection ((cutoff,rows),(s,read)) =
      match search rows.length cutoff.length s with
      | none => (false,(0,0))
      | some p => (true,p) := by
  change select ((nTokens rows,cutoff),s) = _
  rw [← nTokens_length rows]
  exact select_correct (nTokens rows) cutoff s

theorem selectedRow_correct (cutoff : List Bool) (rows : EncRows) (s e q : Nat)
    (read : Bool) (hsel : selection ((cutoff,rows),(s,read)) = (true,(e,q)))
    (hq : q < rows.length) :
    decodeRow (selectedRow ((cutoff,rows),(s,read))) =
      Source284ListTables.table (decodeRows rows) q read := by
  rw [Source284EncodedRows.lookup rows q hq read]
  cases read <;> simp [selectedRow,selectedPair,TM2ListLookup.lookup,hsel,
    List.getElem?_eq_getElem hq]

theorem nextLive_correct (cutoff : List Bool) (rows : EncRows) (s e q : Nat)
    (read : Bool) (hsel : selection ((cutoff,rows),(s,read)) = (true,(e,q))) :
    nextLive ((cutoff,rows),(s,read)) =
      decide (e+1 < cutoff.length ∧ (selectedRow ((cutoff,rows),(s,read))).2.2.2 < rows.length) := by
  apply Bool.eq_iff_iff.mpr
  simp [nextLive,hsel,TM2BoundedWitnessGuard.guard_correct]

theorem destination_correct (cutoff : List Bool) (rows : EncRows) (s e q : Nat)
    (read : Bool) (hsel : selection ((cutoff,rows),(s,read)) = (true,(e,q))) :
    destination ((cutoff,rows),(s,read)) =
      if e+1 < cutoff.length ∧ (selectedRow ((cutoff,rows),(s,read))).2.2.2 < rows.length then
        Nat.pair (e+1) (selectedRow ((cutoff,rows),(s,read))).2.2.2
      else Source284TableCountdown.sink rows.length cutoff.length := by
  by_cases h : e+1 < cutoff.length ∧ (selectedRow ((cutoff,rows),(s,read))).2.2.2 < rows.length
  · have hp := pairBounded_correct (budget cutoff rows) (e+1)
        (selectedRow ((cutoff,rows),(s,read))).2.2.2 (by simp; omega) (by simp; omega)
    simp [destination,nextLive_correct cutoff rows s e q read hsel,hsel,h,hp]
  · simp [destination,nextLive_correct cutoff rows s e q read hsel,hsel,h,sinkCode_correct]

theorem guardedRow_correct (cutoff : List Bool) (rows : EncRows) (s : Nat) (read : Bool) :
    decodeRow (guardedRow ((cutoff,rows),(s,read))) =
      Source284TableCountdown.table rows.length cutoff.length
        (Source284ListTables.table (decodeRows rows)) s read := by
  have hsel := selection_correct cutoff rows s read
  cases hs : search rows.length cutoff.length s with
  | none =>
    have hn : ¬ ((Nat.unpair s).1 < cutoff.length ∧ (Nat.unpair s).2 < rows.length) := by
      intro h
      rw [search_eq] at hs
      simp [h] at hs
    have hsel' : selection ((cutoff,rows),(s,read)) = (false,(0,0)) := by simpa [hs] using hsel
    simp only [guardedRow,hsel',Bool.false_eq_true,↓reduceIte,Source284GuardRow.sinkRow,
      decodeRow,sinkCode_correct]
    by_cases hst : s = Source284TableCountdown.sink rows.length cutoff.length <;>
      simp [Source284TableCountdown.table,Source284TableCountdown.sinkRow,hst,hn]
  | some c =>
    rcases c with ⟨e,q⟩
    obtain ⟨he,hq,hpair⟩ := (search_some_iff rows.length cutoff.length s e q).1 hs
    have hsel' : selection ((cutoff,rows),(s,read)) = (true,(e,q)) := by simpa [hs] using hsel
    have hne : s ≠ Source284TableCountdown.sink rows.length cutoff.length := by
      rw [← hpair]
      exact ne_of_lt (live_lt_sink rows.length cutoff.length e q he hq)
    have hrow := selectedRow_correct cutoff rows s e q read hsel' hq
    have hd := destination_correct cutoff rows s e q read hsel'
    rw [← hpair] at *
    simp only [Source284TableCountdown.table, hne, ↓reduceIte, Nat.unpair_pair, he, hq,
      and_self, true_and, ↓reduceIte]
    rw [← hrow]
    cases hc : (selectedRow ((cutoff,rows),(Nat.pair e q,read))).2.2.1 <;>
      simp [guardedRow,hsel',decodeRow,hc,hd] <;> split_ifs <;> rfl

end Shared.Beeping.NPcoNP.Source284GuardRowCorrect
