import Shared.Beeping.NPcoNP.Source284VerifierReject

/-! Source-encoded execution of the linked validator and verifier. The
certificate is already under the head. Initial orientation, uniform
polynomial table generation and the physical beeper remain separate. -/
namespace Shared.Beeping.NPcoNP.Source284VerifierLinkedSource

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284CanonicalPairWindow (window)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix)
open Shared.Beeping.NPcoNP.Source284CertificateDispatch (allocated)
open Shared.Beeping.NPcoNP.Source284SATGrammarCharacterization (validWindow)
open Shared.Beeping.NPcoNP.Source284VerifierHandoff (table)

/-- The encoded source table accepts exactly when its finite window is valid
and the original closed verifier accepts within the supplied positive fuel. -/
theorem source_combined_acceptance (x : List Bool) (width certificate fuel codeTail n : Nat)
    (verifier : Nat → Bool → Row) (hn : 0 < n) (hclosed : Closed n verifier)
    (hwidth : (pairPrefix x).length ≤ width) :
    let suffix := (window width certificate).drop (pairPrefix x).length
    ((Shared.Beeping.NPcoNP.Source284Relative.run
      (encode (allocated (pairPrefix x) suffix.length+n)
        (table (pairPrefix x) suffix.length verifier) codeTail)
      (toSource ⟨0,certificate,some 0⟩) ((2*width+2)+(fuel+1))).state == 0) =
      (validWindow x width certificate &&
        (run verifier ⟨0,certificate,some 0⟩ (fuel+1)).state.isNone) := by
  let suffix := (window width certificate).drop (pairPrefix x).length
  have hc := Source284VerifierHandoff.closed (pairPrefix x) suffix.length n verifier hn hclosed
  have hv : Valid (allocated (pairPrefix x) suffix.length+n) ⟨0,certificate,some 0⟩ := by
    intro q hq
    simp only [Option.some.injEq] at hq
    subst q
    omega
  change ((Shared.Beeping.NPcoNP.Source284Relative.run
    (encode (allocated (pairPrefix x) suffix.length+n)
      (table (pairPrefix x) suffix.length verifier) codeTail)
    (toSource ⟨0,certificate,some 0⟩) ((2*width+2)+(fuel+1))).state == 0) = _
  rw [run_toSource _ _ codeTail _ hc hv]
  change (nextState (run (table (pairPrefix x) suffix.length verifier)
    ⟨0,certificate,some 0⟩ ((2*width+2)+(fuel+1))).state == 0) = _
  rw [nextState_zero]
  exact Source284VerifierReject.combined_acceptance x width certificate fuel verifier hwidth

end Shared.Beeping.NPcoNP.Source284VerifierLinkedSource
