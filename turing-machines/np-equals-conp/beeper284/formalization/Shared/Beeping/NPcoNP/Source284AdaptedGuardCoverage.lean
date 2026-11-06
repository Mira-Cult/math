import Shared.Beeping.NPcoNP.Source284EmptyBranchSink
import Shared.Beeping.NPcoNP.Source284PrefixGuardCoverage

/-! Composition of the concrete empty-prefix source adapter with an assumed
finite guarded verifier. This does not construct the verifier or its timeout
counter, and it is not a physical-machine theorem. -/
namespace Shared.Beeping.NPcoNP.Source284AdaptedGuardCoverage

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EmptyBranchAdapter
open Shared.Beeping.NPcoNP.Source284EmptyBranchSink
open Shared.Beeping.NPcoNP.Source284RawParse

/-- A closed finite logical verifier with an explicit self-looping reject
sink, a polynomial cutoff and correct bounded-witness behavior gives one
coupled candidate. The adapter pays two logical states and two iterations on
positive-prefix inputs and supplies the one-step zero-prefix case itself. -/
theorem candidate_of_guarded_table
    (p fuel : Polynomial Nat) (R : (List Bool × List Bool) → Bool)
    (original : Nat → Bool → Row) (n sink tail : Nat)
    (hn : 0 < n) (hs : sink < n) (hclosed : Closed n original)
    (hzero : (original sink false).next = some sink)
    (hone : (original sink true).next = some sink)
    (hwitness : ∀ i : Nat, (!reference i) = true ↔
      ∃ w : List Bool, w.length ≤ p.eval (2*Source284Parser.length i+1) ∧
        R (payload i.bits,w) = true)
    (hwindow : ∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤
        fuel.eval (Source284Parser.length i)+2)
    (hrealize : ∀ i, 0 < Source284Parser.length i → ∀ c,
      (run original ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state.isNone =
        Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c)
    (hfinished : ∀ i, 0 < Source284Parser.length i → ∀ c,
      (run original ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = none ∨
      (run original ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = some sink) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  let description := encode (n+2) (table original) tail
  let sinkState := active (2+sink)
  have heval (i : Nat) : (fuel+2).eval (Source284Parser.length i) =
      fuel.eval (Source284Parser.length i)+2 := by simp
  have hodd (i : Nat) (hi : 0 < Source284Parser.length i) : i % 2 = 1 := by
    have hne : i % 2 ≠ 0 := by
      intro h
      have hlen := (Source284EmptyPrefix.empty_iff_even i).2 h
      omega
    have hm := Nat.mod_lt i (by decide : 0 < 2)
    omega
  apply Source284PrefixGuardCoverage.candidate_of_prefix_guard p (fuel+2) R description sinkState hwitness
  · intro i hi
    rw [heval]
    exact hwindow i hi
  · intro i hi c
    rw [heval]
    change Source284Relative.accepts (encode (n+2) (table original) tail) i c
      (fuel.eval (Source284Parser.length i)+2) = _
    rw [encoded_odd_acceptance original n tail i c _ hn hclosed (hodd i hi),
      bounded_acceptance n original 0 hn hclosed]
    exact hrealize i hi c
  · simp [sinkState,active]
  · exact encoded_sink_invariant original n tail sink hs hzero hone
  · intro i hi c
    rw [heval]
    exact encoded_odd_finished original n tail sink i c _ hn hclosed (hodd i hi) (hfinished i hi c)
  · change Source284Relative.record (encode (n+2) (table original) tail) 0 < 4
    rw [encoded_first_record]
    decide

/-- Finite-code specialization: the verifier is supplied as actual encoded
row tuples, and its closure follows from the executable Boolean validity
check. The listed semantic obligations still require proofs for that code. -/
theorem candidate_of_guarded_encoded_rows
    (p fuel : Polynomial Nat) (R : (List Bool × List Bool) → Bool)
    (rows : Source284EncodedRows.EncRows) (sink tail : Nat)
    (hn : 0 < rows.length) (hs : sink < rows.length)
    (hv : Source284ListTables.valid (Source284EncodedRows.decodeRows rows) = true)
    (hzero : (Source284ListTables.table (Source284EncodedRows.decodeRows rows) sink false).next = some sink)
    (hone : (Source284ListTables.table (Source284EncodedRows.decodeRows rows) sink true).next = some sink)
    (hwitness : ∀ i : Nat, (!reference i) = true ↔
      ∃ w : List Bool, w.length ≤ p.eval (2*Source284Parser.length i+1) ∧
        R (payload i.bits,w) = true)
    (hwindow : ∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤
        fuel.eval (Source284Parser.length i)+2)
    (hrealize : ∀ i, 0 < Source284Parser.length i → ∀ c,
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state.isNone =
        Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c)
    (hfinished : ∀ i, 0 < Source284Parser.length i → ∀ c,
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = none ∨
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = some sink) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  apply candidate_of_guarded_table p fuel R
    (Source284ListTables.table (Source284EncodedRows.decodeRows rows)) rows.length sink tail hn hs
  · simpa using Source284ListTables.valid_closed (Source284EncodedRows.decodeRows rows) hv
  · exact hzero
  · exact hone
  · exact hwitness
  · exact hwindow
  · exact hrealize
  · exact hfinished

end Shared.Beeping.NPcoNP.Source284AdaptedGuardCoverage
