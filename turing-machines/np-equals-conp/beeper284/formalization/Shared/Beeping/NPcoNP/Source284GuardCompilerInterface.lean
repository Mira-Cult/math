import Shared.Beeping.NPcoNP.Source284AdaptedGuardCoverage
import Shared.Beeping.NPcoNP.Source284SelectorClosed

/-! An explicit remaining compiler obligation for the source controller.
No implementation of this obligation, physical machine, or unconditional
class equality endpoint is claimed. -/
namespace Shared.Beeping.NPcoNP.Source284GuardCompilerInterface

open ComplexityTheory
open Shared.Beeping.NPcoNP.Source284CanonicalConditional
open Shared.Beeping.NPcoNP.Source284Comparison
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284RawParse

/-- A finite encoded verifier table realizes a given normalized relation and
its original witness cutoff on every positive-prefix input. Its execution
reaches acceptance or an explicit absorbing reject state by the polynomial
cutoff; the separately proved adapter supplies the zero-prefix branch. This
is an obligation on a concrete row list, not an assumed class equality. -/
def GuardedRowsRealize (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool) : Prop :=
  ∃ (rows : Source284EncodedRows.EncRows) (sink : Nat) (fuel : Polynomial Nat),
    0 < rows.length ∧ sink < rows.length ∧
    Source284ListTables.valid (Source284EncodedRows.decodeRows rows) = true ∧
    (Source284ListTables.table (Source284EncodedRows.decodeRows rows) sink false).next = some sink ∧
    (Source284ListTables.table (Source284EncodedRows.decodeRows rows) sink true).next = some sink ∧
    (∀ i, 0 < Source284Parser.length i →
      Source284WitnessWindow.width (p.eval (2*Source284Parser.length i+1)) ≤
        fuel.eval (Source284Parser.length i)+2) ∧
    (∀ i, 0 < Source284Parser.length i → ∀ c,
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state.isNone =
        Source284WitnessWindow.check (p.eval (2*Source284Parser.length i+1))
          (fun w => R (payload i.bits,w)) c) ∧
    (∀ i, 0 < Source284Parser.length i → ∀ c,
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = none ∨
      (run (Source284ListTables.table (Source284EncodedRows.decodeRows rows))
        ⟨c,i,some 0⟩ (fuel.eval (Source284Parser.length i))).state = some sink)

/-- Exact outstanding source-table compilation hypothesis. It asserts only
existence of finite rows with the stated operational and cost properties;
it does not assert an effective reifier for arbitrary Lean functions. -/
def GuardCompiler : Prop :=
  ∀ (p : Polynomial Nat) (R : (List Bool × List Bool) → Bool),
    IsPolyTime R → GuardedRowsRealize p R

/-- Once the stated guard compiler is proved, the actual source candidate
family covers the complement of the complete reference. -/
theorem coverage_of_guardCompiler (compiler : GuardCompiler)
    (hNP : referenceLanguageᶜ ∈ NP) :
    ∃ j, candidateLanguage j = referenceLanguageᶜ := by
  obtain ⟨p,R,hR,hwitness⟩ := Source284PrefixVerifier.witness_of_complement_mem_NP hNP
  obtain ⟨rows,sink,fuel,hn,hs,hvalid,hzero,hone,hwindow,hrealize,hfinished⟩ := compiler p R hR
  exact Source284AdaptedGuardCoverage.candidate_of_guarded_encoded_rows
    p fuel R rows sink 0 hn hs hvalid hzero hone hwitness hwindow hrealize hfinished

/-- Conditional class endpoint for the atomic source controller. The guard
compiler and progress-sensitive refinement to a concrete beeper are still
open; the theorem is not a statement about the literal 284-state table. -/
theorem entry_controller_iff_classes (compiler : GuardCompiler) :
    (Shared.Beeping.CandidateEntryController.system compare 0).EventuallySilent ↔ NP = coNP :=
  Source284SelectorClosed.entry_controller_iff_classes (coverage_of_guardCompiler compiler)

end Shared.Beeping.NPcoNP.Source284GuardCompilerInterface
