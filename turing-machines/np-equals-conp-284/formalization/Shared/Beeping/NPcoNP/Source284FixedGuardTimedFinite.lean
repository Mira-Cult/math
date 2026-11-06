import Shared.Beeping.NPcoNP.Source284FixedGuardTimed
import Shared.Beeping.NPcoNP.Source284MaterializeRows
import Shared.Beeping.NPcoNP.Source284EmptyBranchValidity

/-! Materialized finite code for the fixed witness guard plus timed verifier.
The input is a finite encoded row list, not a reified Lean function. This
proves output validity and a unary-description length bound; it does not
prove bit-time complexity, dynamic bounds, or a physical-machine compiler. -/
namespace Shared.Beeping.NPcoNP.Source284FixedGuardTimedFinite

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284FixedGuardTimed

def rows (m fuel : Nat) (original : EncRows) : EncRows :=
  Source284MaterializeRows.rows (statesTotal m original.length fuel)
    (table m original.length fuel (Source284ListTables.table (decodeRows original)))

theorem rows_length (m fuel : Nat) (original : EncRows) :
    (rows m fuel original).length = statesTotal m original.length fuel := by
  simp [rows,Source284MaterializeRows.rows_length]

theorem rows_closed (m fuel : Nat) (original : EncRows) :
    Closed (rows m fuel original).length (Source284ListTables.table (decodeRows (rows m fuel original))) := by
  apply Source284MaterializeRows.table_closed
  exact Source284FixedGuardTimed.closed m original.length fuel _

/-- Even malformed finite input tables produce a closed output table; the
countdown rejects out-of-range successor states. -/
theorem rows_valid (m fuel : Nat) (original : EncRows) :
    Source284ListTables.valid (decodeRows (rows m fuel original)) = true := by
  apply Source284EmptyBranchValidity.valid_of_closed
  simpa using rows_closed m fuel original

/-- The fully materialized row list and the linked mathematical table have
identical unary source descriptions for every unused high tail. -/
theorem rows_encode (m fuel tail : Nat) (original : EncRows) :
    encode (rows m fuel original).length (Source284ListTables.table (decodeRows (rows m fuel original))) tail =
      description m original.length fuel tail (Source284ListTables.table (decodeRows original)) := by
  exact Source284MaterializeRows.encode_agrees _ _ tail

def source (m fuel : Nat) (original : EncRows) : Nat :=
  Source284ListTables.source (decodeRows (rows m fuel original))

theorem source_eq (m fuel : Nat) (original : EncRows) :
    source m fuel original =
      description m original.length fuel 0 (Source284ListTables.table (decodeRows original)) := by
  unfold source Source284ListTables.source
  simpa using rows_encode m fuel 0 original

/-- The finite output's actual unary description has quadratic bit length
in its logical-state allocation. No table-generation running time is claimed. -/
theorem source_size (m fuel : Nat) (original : EncRows) :
    Nat.size (source m fuel original) ≤
      1+2*(statesTotal m original.length fuel)*(8*(statesTotal m original.length fuel)+8) := by
  have h := Source284ListTables.source_size (decodeRows (rows m fuel original))
    (rows_valid m fuel original)
  simpa [source,rows_length] using h

/-- Explicit logical allocation bound in the original table size, fixed
witness limit, and fixed verifier cutoff. -/
theorem states_bound (m n fuel : Nat) :
    statesTotal m n fuel ≤ 16*m+34+(max n (fuel+1)+1)^2+1 := by
  have h := Source284TableCountdown.allocated_le n (fuel+1)
  simp only [statesTotal, timedStates, Source284FixedGuardRewind.state_count]
  omega

/-- The materialized source reaches acceptance or one of its two designated
reject sinks by the fixed time, for every input and certificate. -/
theorem source_finished (m fuel c i : Nat) (original : EncRows)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true) :
    let s := (Source284Relative.run (source m fuel original)
      (Source284Relative.initial i c) (time m fuel)).state
    s = 0 ∨ s = active (guardSink m) ∨ s = active (timedSink m original.length fuel) := by
  dsimp only
  rw [source_eq]
  apply Source284FixedGuardTimed.source_finished m original.length fuel c i 0 _ hn
  simpa using Source284ListTables.valid_closed (decodeRows original) hv

/-- The serialized program's comparison result is stable for all later clocks
for every finite, nonempty valid original verifier table. -/
theorem source_stable (m fuel i c extra : Nat) (original : EncRows)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true) :
    Source284Relative.accepts (source m fuel original) i c (time m fuel+extra) =
      Source284Relative.accepts (source m fuel original) i c (time m fuel) := by
  rw [source_eq]
  apply Source284FixedGuardTimed.source_stable m original.length fuel c i 0 extra _ hn
  simpa using Source284ListTables.valid_closed (decodeRows original) hv

/-- Materialized-code form of the coupled-clock bounded-witness theorem.
Correctness of the supplied verifier on decoded aliases remains explicit. -/
theorem source_coupled_stable_search (m fuel i extra : Nat) (original : EncRows)
    (predicate : List Bool → Bool) (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run (Source284ListTables.table (decodeRows original)) ⟨c,i,some 0⟩ (fuel+1)).state.isNone =
        predicate w) :
    Source284Relative.acceptBound (source m fuel original) i (time m fuel+extra)
        (2^(time m fuel+extra)) = true ↔ ∃ w, w.length ≤ m ∧ predicate w = true := by
  rw [source_eq]
  apply Source284FixedGuardTimed.source_coupled_stable_search m original.length fuel i 0 extra
    _ predicate hn _ hmatch
  simpa using Source284ListTables.valid_closed (decodeRows original) hv

end Shared.Beeping.NPcoNP.Source284FixedGuardTimedFinite
