import Shared.Beeping.NPcoNP.Source284CheckpointGuardSource
import Shared.ComplexityBridge.TM2Compose

/-! The checkpointed initializer really reaches the established tagged
witness comparator, rejects invalid outer certificates at every clock, and
can choose independently large input-side scratch for that cutoff. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 6000000
set_option autoImplicit false
namespace Shared.Beeping.NPcoNP.Source284CheckpointGuardVerifier

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftConfig)
open Shared.Beeping.NPcoNP.Source284UnaryPairScanner (pairTape)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)
open Shared.Beeping.NPcoNP.Source284SourceRelocation (lift lift_toSource)
open Shared.Beeping.NPcoNP.Source284CheckpointGuardSource (stream otherHalf)

def description (k r n : Nat) (verifier : Nat → Bool → Row) : Nat :=
  Source284CheckpointGuardSource.description k r (Source284DynamicGuardSource.states n)
    (Source284OffsetTagged.table n verifier)

theorem otherHalf_shape (k r : Nat) (w : List Bool) (suffix : Nat) :
    otherHalf k r w suffix = 2*stream k r w suffix+1 := by
  have h := Source284GapUnarySource.gap_odd k w.length
  simp [otherHalf,Source284GapUnaryPrepare.retained,
    show Source284GapUnarySource.gap k w.length%2 ≠ 0 by omega]

/-- The continuation is exactly the existing tagged comparator on the
original certificate and preserved high input-side data. -/
theorem source_after (k r n : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix fuel : Nat) (hn : 0 < n) (hv : Closed n verifier) :
    Source284Relative.run (description k r n verifier)
      (Source284Relative.initial (encodeFrame w suffix) certificate)
      (Source284CheckpointGuardSource.totalCost k r w+fuel) =
    lift (1341+317*k+317*r) (Source284Relative.run (Source284OffsetTagged.description n verifier)
      (Source284Relative.initial certificate
        (pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
          (otherHalf k r w suffix))) fuel) := by
  have hc : Closed (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier) :=
    Source284OffsetTagged.table_closed n verifier hn hv
  let c : Config := ⟨pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
    (otherHalf k r w suffix),certificate,some 0⟩
  have hvalid : Valid (Source284DynamicGuardSource.states n) c := by
    intro q hq
    simp [c] at hq
    subst q
    simp [Source284DynamicGuardSource.states,Source284OffsetTagged.goodStates,
      Source284OffsetTagged.rawStates,Source284PositiveTaggedCutoff.rawStates]
  have hr := run_toSource (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier)
    1 c hc hvalid fuel
  change Source284Relative.run (Source284OffsetTagged.description n verifier)
    (Source284Relative.initial certificate
      (pairTape (List.replicate (Source284DynamicGuardSource.bound k w.length) false)
        (otherHalf k r w suffix))) fuel = _ at hr
  calc
    _ = toSource (shiftConfig (1341+317*k+317*r) (run (Source284OffsetTagged.table n verifier) c fuel)) := by
      simpa [description,c] using Source284CheckpointGuardSource.source_then k r
        (Source284DynamicGuardSource.states n) (Source284OffsetTagged.table n verifier)
        w certificate suffix fuel (by simp [Source284DynamicGuardSource.states]) hc
    _ = lift (1341+317*k+317*r) (toSource (run (Source284OffsetTagged.table n verifier) c fuel)) :=
      (lift_toSource _ _).symm
    _ = _ := by rw [hr]

theorem rejected_certificate_never_accepts (k r n : Nat) (verifier : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k w.length) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r n verifier)
      (encodeFrame w suffix) certificate clock = false := by
  apply Source284PositiveTaggedCutoff.never_of_after _ _ _ (Source284CheckpointGuardSource.totalCost k r w)
  intro extra
  have h := Source284OffsetTagged.decoded_none_never_accepts n verifier
    (Source284DynamicGuardSource.bound k w.length) certificate (otherHalf k r w suffix) hn hv hbad extra
  unfold Source284Relative.accepts at h ⊢
  rw [source_after k r n verifier w certificate suffix extra hn hv]
  simp only [beq_eq_false_iff_ne] at h ⊢
  simp [Source284SourceRelocation.lift,h]

/-- The rejection guarantee also covers every raw input encoding, including
the empty parsed frame and arbitrary high input suffixes. -/
theorem rejected_raw_certificate_never_accepts (k r n : Nat) (verifier : Nat → Bool → Row)
    (input certificate : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hbad : Source284TaggedWitnessCodec.decode
      (Source284DynamicGuardSource.bound k (Source284Parser.length input)) certificate = none) :
    ∀ clock, Source284Relative.accepts (description k r n verifier) input certificate clock = false := by
  obtain ⟨w,suffix,hframe⟩ := Source284Parser.encodeFrame_surjective input
  have hlen : Source284Parser.length input = w.length := by
    rw [← hframe]
    simp [Source284Parser.length,Source284Parser.parse_encodeFrame]
  have hbad' : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k w.length)
      certificate = none := by simpa [hlen] using hbad
  have h := rejected_certificate_never_accepts k r n verifier w certificate suffix hn hv hbad'
  simpa [hframe] using h

/-- Valid decoded certificates reach the existing verifier continuation,
with the same retained unary tokens and input stream. -/
theorem decoded_verifier_exact (k r n : Nat) (verifier : Nat → Bool → Row)
    (input witness : List Bool) (certificate suffix : Nat) (hn : 0 < n) (hv : Closed n verifier)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    ∃ witnessSuffix, certificate = 4*encodeFrame witness witnessSuffix ∧
      ∀ fuel, Source284Relative.run (description k r n verifier)
        (Source284Relative.initial (encodeFrame input suffix) certificate)
        (Source284CheckpointGuardSource.totalCost k r input+
          (4+(Source284PayloadSentinelPipeline.totalCost witness.length+
            (Source284OffsetMatch.compareCost witness.length+(1+fuel))))) =
      lift (1341+317*k+317*r+212) (Source284Relative.run (encode n verifier 1)
        ⟨2*Source284PayloadMarkOne.zeros witness
            (Source284ScratchFlip.flipped [false] ((witnessSuffix/4)/4)),
          pairTape (Source284OffsetExactHandoff.boundTokens (Source284DynamicGuardSource.bound k input.length) witness)
            (otherHalf k r input suffix),active 0⟩ fuel) := by
  obtain ⟨witnessSuffix,hcert,hafter⟩ := Source284OffsetDecodedHandoff.decoded_verifier_exact
    n verifier (Source284DynamicGuardSource.bound k input.length) certificate (otherHalf k r input suffix)
    witness hn hv hdec
  refine ⟨witnessSuffix,hcert,?_⟩
  intro fuel
  rw [source_after k r n verifier input certificate suffix _ hn hv,hafter fuel,
    Source284SourceRelocation.lift_add]

def verifierEntryCost (k r : Nat) (input witness : List Bool) : Nat :=
  Source284CheckpointGuardSource.totalCost k r input+
    (4+(Source284PayloadSentinelPipeline.totalCost witness.length+
      (Source284OffsetMatch.compareCost witness.length+1)))

noncomputable def verifierEntryPolynomial (k r : Nat) : Polynomial Nat :=
  let b := Source284RestoredPolynomialRunway.countPolynomial k+1
  Source284CheckpointGuardSource.costPolynomial k r+6*b*b+50*b+61

theorem verifier_entry_polynomial (k r : Nat) (input witness : List Bool) (certificate : Nat)
    (hdec : Source284TaggedWitnessCodec.decode (Source284DynamicGuardSource.bound k input.length)
      certificate = some witness) :
    verifierEntryCost k r input witness ≤ (verifierEntryPolynomial k r).eval input.length := by
  have hw := Source284TaggedWitnessCodec.decode_length
    (Source284DynamicGuardSource.bound k input.length) certificate witness hdec
  have hb : witness.length ≤ Source284GapUnarySource.gap k input.length :=
    le_trans hw (Nat.div_le_self _ _)
  have hsquare := Nat.mul_self_le_mul_self hb
  have hinit := Source284CheckpointGuardSource.cost_polynomial k r input
  unfold verifierEntryCost verifierEntryPolynomial
  rw [Source284PayloadSentinelPipeline.totalCost_formula]
  simp only [Source284OffsetMatch.compareCost,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_one,Source284RestoredPolynomialRunway.countPolynomial_eval]
  simp only [Source284GapUnarySource.gap] at hb hsquare
  nlinarith

/-- Removing the counted shift's one cell leaves the rest of the independently
constructed blank input-side prefix. -/
theorem retained_half_zero (k r n suffix depth : Nat)
    (h : depth ≤ Source284CheckpointWorkspace.workspace k r n) :
    2^depth ∣ Source284CheckpointWorkspace.retained k r n suffix/2 := by
  obtain ⟨tail,ht⟩ := Source284CheckpointGrowth.retained_zero k r n suffix (depth+1) (by omega)
  refine ⟨tail,?_⟩
  rw [ht,pow_succ]
  have he : 2^depth*2*tail=2*(2^depth*tail) := by ring
  rw [he]
  simp

/-- For a fixed original stage count, one further fixed stage count can
cover any polynomial in the *actual* generated comparator bound. -/
theorem workspace_dominates_bound (k : Nat) (p : Polynomial Nat) :
    ∃ r : Nat, ∀ n, p.eval (Source284DynamicGuardSource.bound k n) ≤
      Source284CheckpointWorkspace.workspace k r n := by
  let q := p.comp (Source284RestoredPolynomialRunway.countPolynomial k+1)
  obtain ⟨r,hr⟩ := Source284CheckpointGrowth.workspace_dominates_guard q
  refine ⟨r,?_⟩
  intro n
  have hseed := Source284ProductGrowth.inner_lower k 1
    (Source284CheckpointWorkspace.base n) (Source284CheckpointWorkspace.base n)
    (by omega) (by simp [Source284CheckpointWorkspace.base]) (by simp [Source284CheckpointWorkspace.base])
  simp only [one_pow,Nat.mul_one] at hseed
  change n+2 ≤ Source284CheckpointWorkspace.guard k n at hseed
  have hn : n ≤ Source284CheckpointWorkspace.guard k n := by
    omega
  have hb : Source284DynamicGuardSource.bound k n ≤
      (Source284RestoredPolynomialRunway.countPolynomial k+1).eval
        (Source284CheckpointWorkspace.guard k n) := by
    have hmono := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono
      (Source284RestoredPolynomialRunway.countPolynomial k+1) hn
    simp only [Polynomial.eval_add,Polynomial.eval_one,
      Source284RestoredPolynomialRunway.countPolynomial_eval] at hmono ⊢
    unfold Source284DynamicGuardSource.bound Source284GapUnarySource.gap
    have hd := Nat.div_le_self (Source284PolynomialMarkedCleanup.count k n+1) 2
    omega
  have hp := Shared.ComplexityBridge.TM2Compose.polynomial_eval_mono p hb
  have hg := hr k n
  simp only [q,Polynomial.eval_comp] at hg
  exact le_trans hp hg

/-- Both fixed stage counts are selected before any input is tested. The
same bound covers the original witness demand and supplies blank input-side
scratch for any polynomial demand in that actual bound. -/
theorem uniform_bound_and_scratch (witnessDemand scratchDemand : Polynomial Nat) :
    ∃ k r : Nat, ∀ n suffix : Nat,
      witnessDemand.eval n ≤ Source284DynamicGuardSource.bound k n ∧
      2^(scratchDemand.eval (Source284DynamicGuardSource.bound k n)) ∣
        Source284CheckpointWorkspace.retained k r n suffix/2 := by
  obtain ⟨k,hk⟩ := Source284DynamicGuardSource.bound_dominates witnessDemand
  obtain ⟨r,hr⟩ := workspace_dominates_bound k scratchDemand
  exact ⟨k,r,fun n suffix => ⟨hk n,retained_half_zero k r n suffix _ (hr n)⟩⟩

namespace Fixtures
open Source284PreparedCutoff.Fixtures (acceptImmediately accept_closed)

/-- A malformed tag cannot reach an immediately accepting verifier, even
for the empty input and with extra workspace stages. -/
example : ∀ clock, Source284Relative.accepts (description 0 2 1 acceptImmediately)
    (encodeFrame [] 0) 3 clock = false := by
  apply rejected_certificate_never_accepts 0 2 1 acceptImmediately [] 3 0 (by decide) accept_closed
  simp [Source284TaggedWitnessCodec.decode]
end Fixtures

end Shared.Beeping.NPcoNP.Source284CheckpointGuardVerifier
