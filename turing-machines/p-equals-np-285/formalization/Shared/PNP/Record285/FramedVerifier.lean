import Shared.PNP.Record285.MaskedChoiceLoader
import Shared.PNP.Record285.HardwireFiniteVerifier
import Shared.ComplexityBridge.FiniteVerifierCompiler
import Shared.ComplexityBridge.TM2PreparedVerify
import Shared.ComplexityBridge.BoundedHardness
import Shared.ComplexityBridge.GeneratorGateListClosed
import Shared.ComplexityBridge.GeneratorFamilyBridge

/-! The actual reference search with canonical fixed-length witness frames.
This proves the semantic SAT reduction; polynomial construction of this new
masked table is a separate obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.FramedVerifier
open Shared.PNP.Record285.MaskedChoiceLoader
open Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.CanonicalInput
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CNFWitness

/-- Actual source input for the masked loader and a fixed finite verifier. -/
def frame (p : Program) (publicBits : List Bool) (count budget : Nat) : List Bool :=
  let mask := framedMask publicBits count
  let k := mask.length
  let g := table k (states p) (states_positive p) mask (relativeTable p)
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  let remaining := tableWidth total g+budget
  canonical (bits (remaining+Shared.PNP.Record285.ChoiceLoader.offset k) (finiteProgram total g))

/-- The source runs an actual finite verifier on each correctly framed witness,
using the exact remaining source clock. -/
theorem reference_exact (p : Program) (publicBits : List Bool) (count budget : Nat) :
    let mask := framedMask publicBits count
    let k := mask.length
    let g := table k (states p) (states_positive p) mask (relativeTable p)
    let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
    let remaining := tableWidth total g+budget
    referenceLanguage (frame p publicBits count budget) = true ↔
      ∃ witness : List Bool, witness.length = count ∧
        bounded p (publicBits++BitstringEncoding.bitEncode witness) remaining = some true := by
  dsimp only
  have h := reference_framed_search publicBits count (states p) (states_positive p) (relativeTable p) budget
  dsimp only at h
  change referenceLanguage (canonical (bits _ _)) = true ↔ _ at h
  unfold frame
  rw [h]
  constructor
  · rintro ⟨w,hw,tail,ha⟩
    exact ⟨w,hw,(verifier_halt_iff_bounded_true p (publicBits++BitstringEncoding.bitEncode w) _ tail).1 ha⟩
  · rintro ⟨w,hw,ha⟩
    exact ⟨w,hw,0,(verifier_halt_iff_bounded_true p (publicBits++BitstringEncoding.bitEncode w) _ 0).2 ha⟩

/-- Padding by a uniform totality budget permits replacing the longer source
clock by the verifier's original clock. -/
theorem reference_total (p : Program) (publicBits : List Bool) (count budget : Nat)
    (htotal : ∀ witness : List Bool, witness.length = count →
      ∃ result, bounded p (publicBits++BitstringEncoding.bitEncode witness) budget = some result) :
    referenceLanguage (frame p publicBits count budget) = true ↔
      ∃ witness : List Bool, witness.length = count ∧
        bounded p (publicBits++BitstringEncoding.bitEncode witness) budget = some true := by
  have h := reference_exact p publicBits count budget
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨w,hw,ha⟩
    exact ⟨w,hw,(bounded_true_iff_of_total p _ budget _ (by omega) (htotal w hw)).1 ha⟩
  · rintro ⟨w,hw,ha⟩
    exact ⟨w,hw,(bounded_true_iff_of_total p _ budget _ (by omega) (htotal w hw)).2 ha⟩

/-- Padding a witness with zero cells does not change any represented
assignment, even with duplicate variables or an exhausted witness. -/
theorem assignment_zeros (vars : List Nat) (m : Nat) (i : Nat) :
    assignment vars (List.replicate m false) i = false := by
  induction vars generalizing m with
  | nil => rfl
  | cons v vs ih =>
    cases m with
    | zero => rfl
    | succ m =>
      by_cases he : i = v <;> simp [assignment,List.replicate_succ,he,ih]

theorem assignment_pad (vars : List Nat) (witness : List Bool) (m : Nat) :
    assignment vars (witness++List.replicate m false) = assignment vars witness := by
  funext i
  induction vars generalizing witness with
  | nil => rfl
  | cons v vs ih =>
    cases witness with
    | nil => simpa [assignment] using assignment_zeros (v::vs) m i
    | cons b bs =>
      by_cases he : i = v <;> simp [assignment,he,ih]

theorem verify_pad (input witness : List Bool) (m : Nat) :
    verify (input,witness++List.replicate m false) = verify (input,witness) := by
  cases hp : Shared.ComplexityBridge.CNF.parse input <;> simp [verify,hp,assignment_pad]

/-- Occurrence witnesses may be padded to exactly the raw input length;
malformed input is still rejected. -/
theorem sat_iff_exact_verifier (input : List Bool) :
    sat input = true ↔ ∃ witness : List Bool, witness.length = input.length ∧ verify (input,witness) = true := by
  rw [sat_iff_bounded_verifier]
  constructor
  · rintro ⟨w,hw,ha⟩
    refine ⟨w++List.replicate (input.length-w.length) false,?_,?_⟩
    · simp; omega
    · simpa [verify_pad] using ha
  · rintro ⟨w,hw,ha⟩
    exact ⟨w,by omega,ha⟩

/-- A compiled total canonical SAT verifier supplies one fixed source frame
whose reference value is exactly SAT, for all raw and malformed inputs. -/
theorem sat_frame_of_compiler (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (input : List Bool) :
    sat input = true ↔ referenceLanguage
      (frame p (CircuitPairWitness.pairPrefix input) input.length
        (BoundedHardness.commonFuel Polynomial.X time input)) = true := by
  let budget := BoundedHardness.commonFuel Polynomial.X time input
  have hcorrect := BoundedHardness.commonFuel_correct verify p Polynomial.X time hprogram input
  have htotal : ∀ witness : List Bool, witness.length = input.length →
      ∃ result, bounded p (CircuitPairWitness.pairPrefix input++BitstringEncoding.bitEncode witness) budget = some result := by
    intro witness hw
    refine ⟨verify (input,witness),?_⟩
    rw [←CircuitPairWitness.pair_encode]
    exact hcorrect witness (by simpa [Polynomial.eval_X] using Nat.le_of_eq hw)
  rw [reference_total p _ _ _ htotal]
  rw [sat_iff_exact_verifier]
  constructor
  · rintro ⟨w,hw,hv⟩
    refine ⟨w,hw,?_⟩
    rw [←CircuitPairWitness.pair_encode]
    simpa [hv] using hcorrect w (by simpa [Polynomial.eval_X] using Nat.le_of_eq hw)
  · rintro ⟨w,hw,hv⟩
    refine ⟨w,hw,?_⟩
    rw [←CircuitPairWitness.pair_encode] at hv
    have hc := hcorrect w (by simpa [Polynomial.eval_X] using Nat.le_of_eq hw)
    rw [hc] at hv
    simpa using hv

/-- One fixed finite program works uniformly for every input; the existence
uses the existing proved canonical compiler, not a P = NP hypothesis. -/
theorem sat_frame_exists :
    ∃ (p : Program) (time : Polynomial Nat), ∀ input,
      sat input = true ↔ referenceLanguage
        (frame p (CircuitPairWitness.pairPrefix input) input.length
          (BoundedHardness.commonFuel Polynomial.X time input)) = true := by
  obtain ⟨p,time,hp⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    verify TM2PreparedVerify.verify_isPolyTime
  exact ⟨p,time,sat_frame_of_compiler p time hp⟩

/-- The exact all-bitstrings SAT-to-reference frame for a fixed verifier. -/
noncomputable def satFrame (p : Program) (time : Polynomial Nat) (input : List Bool) : List Bool :=
  frame p (CircuitPairWitness.pairPrefix input) input.length
    (BoundedHardness.commonFuel Polynomial.X time input)

theorem satFrame_correct (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (input : List Bool) : sat input = referenceLanguage (satFrame p time input) := by
  have h := sat_frame_of_compiler p time hprogram input
  cases hs : sat input <;> cases hr : referenceLanguage (satFrame p time input) <;>
    simp_all [satFrame]

/-- The remaining computational premise for this exact reduction is the
polynomial construction of its masked table and frame. -/
theorem sat_reduces_of_frame_poly (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (hframe : ComplexityTheory.IsPolyTime (satFrame p time)) :
    CanonicalClasses.PolyRed sat referenceLanguage :=
  ⟨satFrame p time,hframe,satFrame_correct p time hprogram⟩

/-- The existing canonical SAT-hardness proof composes with the exact masked
frame, conditional only on the latter's paid polynomial construction. -/
theorem reference_hard_of_frame_poly (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (hframe : ComplexityTheory.IsPolyTime (satFrame p time)) :
    ∀ L : ComplexityTheory.DecisionProblem, L ∈ ComplexityTheory.NP →
      CanonicalClasses.PolyRed L referenceLanguage := by
  intro L hL
  obtain ⟨f,hf,hcorrect⟩ := GeneratorGateListClosed.satHard L hL
  refine ⟨fun x => satFrame p time (f x),TM2Compose.isPolyTime_comp f (satFrame p time) hf hframe,?_⟩
  intro x
  rw [hcorrect,satFrame_correct p time hprogram]

/-- Frame length is controlled by the finite state count and the explicit
clock padding. This is an output-size bound, not a running-time proof. -/
theorem frame_length_bound (p : Program) (publicBits : List Bool) (count budget : Nat) :
    let k := publicBits.length+3*count
    let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
    (frame p publicBits count budget).length ≤
      2*((4*total)*(16*total+8)+budget+Shared.PNP.Record285.ChoiceLoader.offset k)+1 := by
  dsimp only
  let mask := framedMask publicBits count
  let k := mask.length
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  let g := table k (states p) (states_positive p) mask (relativeTable p)
  have hwidth := tableWidth_bound total g
  have hk : k = publicBits.length+3*count := by simp [k,mask]
  change (canonical (bits (tableWidth total g+budget+Shared.PNP.Record285.ChoiceLoader.offset k)
    (finiteProgram total g))).length ≤ _
  rw [canonical_length,bits_length]
  rw [←hk]
  change 2*(tableWidth total g+budget+Shared.PNP.Record285.ChoiceLoader.offset k)+1 ≤
    2*((4*total)*(16*total+8)+budget+Shared.PNP.Record285.ChoiceLoader.offset k)+1
  omega

/-- Any larger fixed witness size works for the SAT occurrence verifier,
which treats extra zero assignment bits as false. -/
theorem sat_iff_exact_verifier_of_le (input : List Bool) (count : Nat) (hcount : input.length ≤ count) :
    sat input = true ↔ ∃ witness : List Bool, witness.length = count ∧ verify (input,witness) = true := by
  rw [sat_iff_bounded_verifier]
  constructor
  · rintro ⟨w,hw,ha⟩
    refine ⟨w++List.replicate (count-w.length) false,?_,?_⟩
    · simp; omega
    · simpa [verify_pad] using ha
  · rintro ⟨w,hw,ha⟩
    cases hp : Shared.ComplexityBridge.CNF.parse input with
    | none => simp [verify,hp] at ha
    | some formula =>
      have hs : sat input = true := by
        simp only [sat,hp]
        apply (satFormula_correct formula).2
        exact ⟨assignment (variableOccurrences formula) w,by simpa [verify,hp] using ha⟩
      exact (sat_iff_bounded_verifier input).1 hs

theorem pairPrefix_length (input : List Bool) :
    (CircuitPairWitness.pairPrefix input).length = 6*input.length+1 := by
  simp [CircuitPairWitness.pairPrefix,BitstringEncoding.length_delimit,bitstring_list_encoded_length]
  omega

theorem aligned_pair_length (input witness : List Bool)
    (hw : witness.length = (CircuitPairWitness.pairPrefix input).length) :
    (BitstringEncoding.bitEncode (input,witness)).length =
      4*(CircuitPairWitness.pairPrefix input).length := by
  rw [bitstring_pair_encoded_length,hw,pairPrefix_length]
  omega

noncomputable def alignedBudget (time : Polynomial Nat) : Polynomial Nat :=
  time.comp (Polynomial.C 4*Polynomial.X)

theorem alignedBudget_eval (time : Polynomial Nat) (n : Nat) :
    (alignedBudget time).eval n = time.eval (4*n) := by
  simp [alignedBudget,Polynomial.eval_comp,Polynomial.eval_mul]

/-- The count and clock depend only polynomially on the actual hardwired
public-prefix length. This form can reuse a single generic masked-frame
builder and then compose with the existing paid pair-prefix encoder. -/
noncomputable def alignedFrame (p : Program) (time : Polynomial Nat) (publicBits : List Bool) : List Bool :=
  frame p publicBits publicBits.length ((alignedBudget time).eval publicBits.length)

theorem aligned_sat_correct (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (input : List Bool) :
    sat input = true ↔ referenceLanguage (alignedFrame p time (CircuitPairWitness.pairPrefix input)) = true := by
  let pub := CircuitPairWitness.pairPrefix input
  let budget := time.eval (4*pub.length)
  have hle : input.length ≤ pub.length := by simp [pub,pairPrefix_length]; omega
  have hcomp : ∀ w : List Bool, w.length = pub.length →
      bounded p (pub++BitstringEncoding.bitEncode w) budget = some (verify (input,w)) := by
    intro w hw
    rw [←CircuitPairWitness.pair_encode]
    have hc := hprogram input w
    rw [aligned_pair_length input w hw] at hc
    exact hc
  have htotal : ∀ w : List Bool, w.length = pub.length →
      ∃ result, bounded p (pub++BitstringEncoding.bitEncode w) budget = some result := by
    intro w hw
    exact ⟨verify (input,w),hcomp w hw⟩
  unfold alignedFrame
  rw [alignedBudget_eval]
  change sat input = true ↔ referenceLanguage (frame p pub pub.length budget) = true
  rw [reference_total p pub pub.length budget htotal,sat_iff_exact_verifier_of_le input pub.length hle]
  constructor
  · rintro ⟨w,hw,hv⟩
    exact ⟨w,hw,by rw [hcomp w hw,hv]⟩
  · rintro ⟨w,hw,ha⟩
    rw [hcomp w hw] at ha
    exact ⟨w,hw,Option.some.inj ha⟩

/-- The existing prefix encoder is already polynomial. Only the uniform
masked-frame construction remains to turn the semantic SAT bridge into a
canonical polynomial-time reduction. -/
theorem aligned_sat_reduces_of_frame_poly (p : Program) (time : Polynomial Nat)
    (hprogram : ∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
      (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w)))
    (hframe : ComplexityTheory.IsPolyTime (alignedFrame p time)) :
    CanonicalClasses.PolyRed sat referenceLanguage := by
  refine ⟨fun input => alignedFrame p time (CircuitPairWitness.pairPrefix input),
    TM2Compose.isPolyTime_comp CircuitPairWitness.pairPrefix (alignedFrame p time)
      GeneratorFamilyBridge.pairPrefix_isPolyTime hframe,?_⟩
  intro input
  have h := aligned_sat_correct p time hprogram input
  cases hs : sat input <;> cases hr : referenceLanguage (alignedFrame p time (CircuitPairWitness.pairPrefix input)) <;>
    simp_all

/-- The compiled verifier and its clock are fixed uniformly, including for
malformed SAT inputs and zero-length witnesses. -/
theorem aligned_sat_compiler_exists :
    ∃ (p : Program) (time : Polynomial Nat),
      (∀ x w, bounded p (BitstringEncoding.bitEncode (x,w))
        (time.eval (BitstringEncoding.bitEncode (x,w)).length) = some (verify (x,w))) ∧
      ∀ input, sat input = true ↔
        referenceLanguage (alignedFrame p time (CircuitPairWitness.pairPrefix input)) = true := by
  obtain ⟨p,time,hp⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    verify TM2PreparedVerify.verify_isPolyTime
  exact ⟨p,time,hp,aligned_sat_correct p time hp⟩

/-- This isolates the sole remaining premise for canonical NP-hardness along
this route: the actual aligned masked-frame builder is polynomial-time. -/
theorem reference_hard_of_alignedFrame_poly
    (hframe : ∀ (p : Program) (time : Polynomial Nat), ComplexityTheory.IsPolyTime (alignedFrame p time)) :
    ∀ L : ComplexityTheory.DecisionProblem, L ∈ ComplexityTheory.NP →
      CanonicalClasses.PolyRed L referenceLanguage := by
  obtain ⟨p,time,hprogram,_⟩ := aligned_sat_compiler_exists
  obtain ⟨g,hg,hgcorrect⟩ := aligned_sat_reduces_of_frame_poly p time hprogram (hframe p time)
  intro L hL
  obtain ⟨f,hf,hfcorrect⟩ := GeneratorGateListClosed.satHard L hL
  refine ⟨fun x => g (f x),TM2Compose.isPolyTime_comp f g hf hg,?_⟩
  intro x
  rw [hfcorrect,hgcorrect]

end Shared.PNP.Record285.FramedVerifier
