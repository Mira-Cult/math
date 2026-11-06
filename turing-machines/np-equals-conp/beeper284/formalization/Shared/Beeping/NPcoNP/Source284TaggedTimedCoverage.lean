import Shared.Beeping.NPcoNP.Source284TaggedGuardCoverage
import Shared.Beeping.NPcoNP.Source284FixedGuardTimedFinite
import Shared.Beeping.NPcoNP.Source284EmptyBranchFinite

/-! A fixed-bound source candidate made from actual finite verifier rows.
This is a restricted conditional result: neither a general input-dependent
bound nor an alias-correct canonical verifier is constructed here. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedTimedCoverage

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284EncodedRows
open Shared.Beeping.NPcoNP.Source284RawParse
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison

/-- The literal finite-data candidate consists of the timed fixed-window
verifier with the paid two-state empty-prefix adapter. -/
def rows (m fuel : Nat) (original : EncRows) : EncRows :=
  Source284EmptyBranchFinite.adapt (Source284FixedGuardTimedFinite.rows m fuel original)

def description (m fuel : Nat) (original : EncRows) : Nat :=
  Source284ListTables.source (decodeRows (rows m fuel original))

def base (m fuel : Nat) (original : EncRows) : EncRows :=
  Source284FixedGuardTimedFinite.rows m fuel original

def baseTable (m fuel : Nat) (original : EncRows) : Nat → Bool → Row :=
  Source284ListTables.table (decodeRows (base m fuel original))

theorem base_nonempty (m fuel : Nat) (original : EncRows) : 0 < (base m fuel original).length := by
  simp only [base,Source284FixedGuardTimedFinite.rows_length,
    Source284FixedGuardTimed.statesTotal,Source284FixedGuardRewind.state_count]
  omega

theorem base_closed (m fuel : Nat) (original : EncRows) :
    Closed (base m fuel original).length (baseTable m fuel original) := by
  exact Source284FixedGuardTimedFinite.rows_closed m fuel original

theorem description_eq (m fuel : Nat) (original : EncRows) :
    description m fuel original = encode ((base m fuel original).length+2)
      (Source284EmptyBranchAdapter.table (baseTable m fuel original)) 0 := by
  simp only [description,Source284ListTables.source,rows,baseTable,base,decodeRows_length]
  exact Source284EmptyBranchFinite.adapt_encode
    (Source284FixedGuardTimedFinite.rows m fuel original) 0

/-- The actual adapter is finite, has two extra logical states, and passes
the executable row-validity check even when the supplied original rows are
malformed: the inner countdown redirects invalid destinations to its sink. -/
theorem rows_length (m fuel : Nat) (original : EncRows) :
    (rows m fuel original).length =
      Source284FixedGuardTimed.statesTotal m original.length fuel+2 := by
  simp [rows,Source284EmptyBranchFinite.adapt_length,Source284FixedGuardTimedFinite.rows_length]

/-- The hardwired row list changes when the witness limit changes. Thus
these tables do not by themselves provide one input-independent candidate
for an unbounded input-dependent limit. -/
theorem rows_length_strict (m₁ m₂ fuel : Nat) (original : EncRows) (h : m₁ < m₂) :
    (rows m₁ fuel original).length < (rows m₂ fuel original).length := by
  simp only [rows_length,Source284FixedGuardTimed.statesTotal,
    Source284FixedGuardRewind.state_count]
  omega

theorem rows_ne_of_limit_ne (m₁ m₂ fuel : Nat) (original : EncRows) (h : m₁ ≠ m₂) :
    rows m₁ fuel original ≠ rows m₂ fuel original := by
  intro he
  have hl := congrArg List.length he
  rcases Nat.lt_or_gt_of_ne h with hlt | hgt
  · have hh := rows_length_strict m₁ m₂ fuel original hlt
    omega
  · have hh := rows_length_strict m₂ m₁ fuel original hgt
    omega

theorem rows_valid (m fuel : Nat) (original : EncRows) :
    Source284ListTables.valid (decodeRows (rows m fuel original)) = true := by
  apply Source284EmptyBranchValidity.adapt_valid (base m fuel original)
    (base_nonempty m fuel original)
  exact Source284FixedGuardTimedFinite.rows_valid m fuel original

/-- A description-length bound for the literal finite code. It is not a
bit-time bound for generating the code or a physical state-count claim. -/
theorem description_size (m fuel : Nat) (original : EncRows) :
    Nat.size (description m fuel original) ≤
      1+2*(Source284FixedGuardTimed.statesTotal m original.length fuel+2)*
        (8*(Source284FixedGuardTimed.statesTotal m original.length fuel+2)+8) := by
  have h := Source284ListTables.source_size (decodeRows (rows m fuel original))
    (rows_valid m fuel original)
  simpa [description,rows_length] using h

theorem first_record (m fuel : Nat) (original : EncRows) :
    Source284Relative.record (description m fuel original) 0 = 0 := by
  rw [description_eq,Source284EmptyBranchAdapter.encoded_first_record]

theorem positive_odd (i : Nat) (hi : 0 < Source284Parser.length i) : i % 2 = 1 := by
  have hne : i % 2 ≠ 0 := by
    intro h
    have hz := (Source284EmptyPrefix.empty_iff_even i).2 h
    omega
  have hm := Nat.mod_lt i (by decide : 0 < 2)
  omega

/-- Positive input pays two turns and then follows the actual materialized
fixed-limit timed verifier on its original input and certificate. -/
theorem positive_attempt (m fuel i c k : Nat) (original : EncRows)
    (hi : 0 < Source284Parser.length i) :
    Source284Relative.accepts (description m fuel original) i c (k+2) =
      Source284Relative.accepts (Source284FixedGuardTimedFinite.source m fuel original) i c k := by
  rw [description_eq]
  rw [Source284EmptyBranchAdapter.encoded_odd_acceptance _ _ 0 i c k
    (base_nonempty m fuel original) (base_closed m fuel original) (positive_odd i hi)]
  simp [Source284FixedGuardTimedFinite.source,Source284ListTables.source,base,baseTable]

/-- Exact bounded-attempt behavior of the timed table for a supplied
alias-correct verifier. No termination premise for the verifier is needed. -/
theorem timed_check (m fuel i c : Nat) (original : EncRows) (predicate : List Bool → Bool)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ c w, Source284TaggedWitnessCodec.decode m c = some w →
      (run (Source284ListTables.table (decodeRows original)) ⟨c,i,some 0⟩ (fuel+1)).state.isNone =
        predicate w) :
    Source284Relative.accepts (Source284FixedGuardTimedFinite.source m fuel original) i c
      (Source284FixedGuardTimed.time m fuel) = Source284TaggedWitnessCodec.check m predicate c := by
  rw [Source284FixedGuardTimedFinite.source_eq]
  cases hd : Source284TaggedWitnessCodec.decode m c with
  | none =>
    rw [Source284FixedGuardTimed.source_bad m original.length fuel c i 0 _ _ hd]
    simp [Source284TaggedWitnessCodec.check,hd]
  | some w =>
    have hg : Source284TaggedWitnessCodec.decode m c ≠ none := by rw [hd]; simp
    have hc : Closed original.length (Source284ListTables.table (decodeRows original)) := by
      simpa using Source284ListTables.valid_closed (decodeRows original) hv
    have hh := Source284FixedGuardTimed.source_good_stable m original.length fuel c i 0 0 _ hn hc hg
    simp only [Nat.add_zero] at hh
    rw [hh,hmatch c w hd]
    simp [Source284TaggedWitnessCodec.check,hd]

/-- The concrete adapter inherits stability from the timed verifier for all
positive-prefix inputs; the one-step zero-prefix case is handled separately. -/
theorem positive_stable (m fuel : Nat) (original : EncRows)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true) :
    PositiveStableAfter (description m fuel original)
      (fun _ => Source284FixedGuardTimed.time m fuel+2) := by
  intro i hi c t ht
  change Source284FixedGuardTimed.time m fuel+2 ≤ t at ht
  let delta := t-(Source284FixedGuardTimed.time m fuel+2)
  have he : Source284FixedGuardTimed.time m fuel+delta+2 = t := by
    dsimp [delta]
    omega
  calc
    Source284Relative.accepts (description m fuel original) i c t =
        Source284Relative.accepts (description m fuel original) i c
          ((Source284FixedGuardTimed.time m fuel+delta)+2) := by rw [he]
    _ = Source284Relative.accepts (Source284FixedGuardTimedFinite.source m fuel original) i c
          (Source284FixedGuardTimed.time m fuel+delta) := positive_attempt m fuel i c _ original hi
    _ = Source284Relative.accepts (Source284FixedGuardTimedFinite.source m fuel original) i c
          (Source284FixedGuardTimed.time m fuel) :=
        Source284FixedGuardTimedFinite.source_stable m fuel i c delta original hn hv
    _ = Source284Relative.accepts (description m fuel original) i c
          (Source284FixedGuardTimed.time m fuel+2) := (positive_attempt m fuel i c _ original hi).symm

/-- The constructed finite rows instantiate the uniform tagged-source
contract for a constant witness bound and a verifier correct within one
fixed fuel value. This does not construct the verifier or cover a genuinely
input-dependent witness bound or running time. -/
theorem realization_of_fixed_timed_verifier (m fuel : Nat) (original : EncRows)
    (R : (List Bool × List Bool) → Bool)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true)
    (hmatch : ∀ i, 0 < Source284Parser.length i → ∀ c w,
      Source284TaggedWitnessCodec.decode m c = some w →
      (run (Source284ListTables.table (decodeRows original)) ⟨c,i,some 0⟩ (fuel+1)).state.isNone =
        R (payload i.bits,w)) :
    Source284TaggedGuardCoverage.UniformTaggedRealization (Polynomial.C m) R := by
  refine ⟨rows m fuel original, Polynomial.C (Source284FixedGuardTimed.time m fuel+2),
    ?_, rows_valid m fuel original, ?_, ?_, ?_, ?_⟩
  · have h := base_nonempty m fuel original
    simp only [rows,Source284EmptyBranchFinite.adapt_length]
    omega
  · change Source284Relative.record (description m fuel original) 0 < 4
    rw [first_record]
    decide
  · intro i hi
    have hd := Source284FixedGuardRewind.duration_exact m
    simp [Source284WitnessWindow.width,Source284FixedGuardTimed.time]
    omega
  · intro i hi c
    have hh := positive_attempt m fuel i c (Source284FixedGuardTimed.time m fuel) original hi
    have ht := timed_check m fuel i c original (fun w => R (payload i.bits,w)) hn hv (hmatch i hi)
    change Source284Relative.accepts (description m fuel original) i c
      ((Polynomial.C (Source284FixedGuardTimed.time m fuel+2) : Polynomial Nat).eval
        (Source284Parser.length i)) = _
    simpa using hh.trans ht
  · change PositiveStableAfter (description m fuel original) _
    simpa using positive_stable m fuel original hn hv

/-- The fixed-window construction discharges all source-table, timeout,
padding, and empty-input obligations for a constant-witness-bound special
case. The remaining hypotheses say that one finite verifier computes the
relation uniformly, including on all tagged aliases, and that this fixed
bound characterizes the reference complement. They are not established for
arbitrary canonical NP relations by this theorem. -/
theorem candidate_of_fixed_timed_verifier (m fuel : Nat) (original : EncRows)
    (R : (List Bool × List Bool) → Bool)
    (hn : 0 < original.length)
    (hv : Source284ListTables.valid (decodeRows original) = true)
    (hwitness : ∀ i : Nat, (!reference i) = true ↔
      ∃ w : List Bool, w.length ≤ m ∧ R (payload i.bits,w) = true)
    (hmatch : ∀ i, 0 < Source284Parser.length i → ∀ c w,
      Source284TaggedWitnessCodec.decode m c = some w →
      (run (Source284ListTables.table (decodeRows original)) ⟨c,i,some 0⟩ (fuel+1)).state.isNone =
        R (payload i.bits,w)) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  let p : Polynomial Nat := Polynomial.C m
  let cutoff : Polynomial Nat := Polynomial.C (Source284FixedGuardTimed.time m fuel+2)
  apply Source284TaggedGuardCoverage.candidate_of_tagged_stable p cutoff R (description m fuel original)
  · intro i
    simpa [p] using hwitness i
  · intro i hi
    have hd := Source284FixedGuardRewind.duration_exact m
    simp [p,cutoff,Source284WitnessWindow.width,Source284FixedGuardTimed.time]
    omega
  · intro i hi c
    have hh := positive_attempt m fuel i c (Source284FixedGuardTimed.time m fuel) original hi
    have ht := timed_check m fuel i c original (fun w => R (payload i.bits,w)) hn hv (hmatch i hi)
    simpa [p,cutoff] using hh.trans ht
  · simpa [cutoff] using positive_stable m fuel original hn hv
  · rw [first_record]
    decide

end Shared.Beeping.NPcoNP.Source284TaggedTimedCoverage
