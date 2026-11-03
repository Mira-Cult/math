import Shared.PNP.Record285.FramedVerifier
import Shared.PNP.Record285.ReferenceRecordWorker
import Shared.PNP.Record285.SourceLiteralEndpoint

/-! Charged construction of the aligned canonical-witness reference frame. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace Shared.PNP.Record285.MaskedFramePoly
open Shared.Codes.FinitePrograms
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.PNP.Record285.ReferenceSerialization
open Shared.PNP.Record285.ReferenceRowBudget
open Shared.PNP.Record285.ReferenceRecordWorker
open Shared.PNP.Record285.MaskedChoiceLoader
open Shared.PNP.Record285.FramedVerifier
open Shared.ComplexityBridge

/-- Three actual tape cells are allocated per canonical witness bit. -/
def witnessPolynomial : Polynomial Nat := Polynomial.C 3*Polynomial.X

@[simp] theorem witnessPolynomial_eval (n : Nat) : witnessPolynomial.eval n = 3*n := by
  simp [witnessPolynomial,Polynomial.eval_mul]

@[simp] theorem aligned_mask_length (xs : List Bool) :
    (framedMask xs xs.length).length = xs.length+witnessPolynomial.eval xs.length := by
  simp

def flagBlocks (xs : List Bool) : List Bool := (xs.map (fun _ => [true,false,true])).flatten

def valueBlocks (xs : List Bool) : List Bool := (xs.map (fun _ => [true,false,false])).flatten

def flags (xs : List Bool) : List Bool := List.replicate xs.length true ++ flagBlocks xs

def values (xs : List Bool) : List Bool := xs ++ valueBlocks xs

/-- Both streams are concrete Boolean encodings of the exact mask; an absent
entry has false flag and hence leaves the original choice bit unchanged. -/
theorem witness_flags (n : Nat) :
    (witnessMask n).map Option.isSome = (List.replicate n [true,false,true]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [witnessMask,List.replicate_succ] at *

theorem witness_values (n : Nat) :
    (witnessMask n).map (fun o => o.getD false) = (List.replicate n [true,false,false]).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => simp [witnessMask,List.replicate_succ] at *

theorem flags_eq (xs : List Bool) : flags xs = (framedMask xs xs.length).map Option.isSome := by
  simp [flags,framedMask,flagBlocks,witness_flags,Function.comp_def]

theorem values_eq (xs : List Bool) : values xs = (framedMask xs xs.length).map (fun o => o.getD false) := by
  simp [values,framedMask,valueBlocks,witness_values,Function.comp_def]

/-- Fixed output lists are built using actual pair and list constructors. -/
theorem constBoolList {α : Type} [BitstringEncoding α] (xs : List Bool) :
    ComplexityTheory.IsPolyTime (fun _ : α => xs) := by
  induction xs with
  | nil => exact TM2EmptyConstant.isPolyTime [] rfl
  | cons b bs ih =>
    have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : α => b) (fun _ : α => bs)
      (TM2Constant.isPolyTime b) ih
    exact TM2Compose.isPolyTime_comp (fun _ : α => (b,bs)) (TM2ListAppend.cons (α := Bool))
      hp TM2ListAppend.cons_isPolyTime

theorem blocks_isPolyTime (block : List Bool) :
    ComplexityTheory.IsPolyTime (fun xs : List Bool => (xs.map (fun _ => block)).flatten) := by
  have hm := TM2ContextMapGeneric.listMap_isPolyTime (fun _ : Bool => block) (constBoolList block)
  exact TM2Compose.isPolyTime_comp (fun xs : List Bool => xs.map (fun _ => block))
    (List.flatten (α := Bool)) hm TM2FlattenList.flatten_isPolyTime

theorem flags_isPolyTime : ComplexityTheory.IsPolyTime flags := by
  have hu := TM2ListUnaryLength.unaryLength_isPolyTime (α := Bool)
  have hb : ComplexityTheory.IsPolyTime flagBlocks := blocks_isPolyTime _
  have hp := TM2GuardAllStep.pair_isPolyTime TM2ListUnaryLength.unaryLength flagBlocks hu hb
  exact TM2Compose.isPolyTime_comp (fun xs => (TM2ListUnaryLength.unaryLength xs,flagBlocks xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime

theorem values_isPolyTime : ComplexityTheory.IsPolyTime values := by
  have hi : ComplexityTheory.IsPolyTime (fun xs : List Bool => xs) := ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hb : ComplexityTheory.IsPolyTime valueBlocks := blocks_isPolyTime _
  have hp := TM2GuardAllStep.pair_isPolyTime (fun xs : List Bool => xs) valueBlocks hi hb
  exact TM2Compose.isPolyTime_comp (fun xs => (xs,valueBlocks xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime

def maskFlag (z : Input) : Bool := TM2InputBitLookup.lookup (flags z.1,quarter z)
def maskValue (z : Input) : Bool := TM2InputBitLookup.lookup (values z.1,quarter z)

def maskChoice (z : Input) : Bool := if maskFlag z then maskValue z else choiceBit z

theorem lookup_isPolyTime (f : List Bool → List Bool) (hf : ComplexityTheory.IsPolyTime f) :
    ComplexityTheory.IsPolyTime (fun z : Input => TM2InputBitLookup.lookup (f z.1,quarter z)) := by
  have ha := TM2Compose.isPolyTime_comp (fun z : Input => z.1) f TM2PairFirst.first_isPolyTime hf
  have hp := TM2GuardAllStep.pair_isPolyTime (fun z : Input => f z.1) quarter ha quarter_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun z : Input => (f z.1,quarter z)) TM2InputBitLookup.lookup
    hp TM2InputBitLookup.lookup_isPolyTime

theorem maskFlag_isPolyTime : ComplexityTheory.IsPolyTime maskFlag := lookup_isPolyTime flags flags_isPolyTime

theorem maskValue_isPolyTime : ComplexityTheory.IsPolyTime maskValue := lookup_isPolyTime values values_isPolyTime

theorem maskChoice_isPolyTime : ComplexityTheory.IsPolyTime maskChoice :=
  TM2If.if_isPolyTime maskFlag maskValue choiceBit maskFlag_isPolyTime maskValue_isPolyTime choiceBit_isPolyTime

/-- The charged two-stream lookup is exactly the semantic optional mask. -/
theorem maskChoice_correct (z : Input) : maskChoice z =
    (((framedMask z.1 z.1.length)[z.2/4]?).getD none).getD (decide (z.2%2=1)) := by
  simp only [maskChoice,maskFlag,maskValue,TM2InputBitLookup.lookup_correct,flags_eq,values_eq,
    quarter_correct,choiceBit_correct,List.getElem?_map]
  cases h : (framedMask z.1 z.1.length)[z.2/4]? with
  | none => simp
  | some a => cases a <;> simp

def maskedWrite (z : Input) : Bool :=
  if writing witnessPolynomial z then maskChoice z else readBit z

def maskedLoaderRecord (z : Input) : Nat :=
  bitVal (maskedWrite z)+2*bitVal (turnBit witnessPolynomial z)+16*(quarter z+1)+4

def maskedWorker (p : Program) (z : Input) : Nat :=
  if inside p witnessPolynomial z then
    if loader witnessPolynomial z then maskedLoaderRecord z else fixedRecord p witnessPolynomial z
  else 0

theorem maskedWrite_isPolyTime : ComplexityTheory.IsPolyTime maskedWrite :=
  TM2If.if_isPolyTime (writing witnessPolynomial) maskChoice readBit
    (writing_isPolyTime witnessPolynomial) maskChoice_isPolyTime readBit_isPolyTime

theorem maskedLoaderRecord_isPolyTime : ComplexityTheory.IsPolyTime maskedLoaderRecord := by
  have hw := TM2Compose.isPolyTime_comp maskedWrite bitVal maskedWrite_isPolyTime boolNat_isPolyTime
  have ht := TM2Compose.isPolyTime_comp (turnBit witnessPolynomial) bitVal
    (turnBit_isPolyTime witnessPolynomial) boolNat_isPolyTime
  have hq := add quarter (fun _ : Input => 1) quarter_isPolyTime (constNat 1)
  have ha := add (fun z => bitVal (maskedWrite z)) (fun z => 2*bitVal (turnBit witnessPolynomial z)) hw
    (double _ ht)
  have hb := add (fun z => bitVal (maskedWrite z)+2*bitVal (turnBit witnessPolynomial z))
    (fun z => 16*(quarter z+1)) ha (fixedMul 16 _ hq)
  exact add _ _ hb (constNat 4)

theorem maskedWorker_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (maskedWorker p) := by
  have h := TM2If.if_isPolyTime (loader witnessPolynomial) maskedLoaderRecord (fixedRecord p witnessPolynomial)
    (loader_isPolyTime witnessPolynomial) maskedLoaderRecord_isPolyTime (fixedRecord_isPolyTime p witnessPolynomial)
  exact TM2If.if_isPolyTime (inside p witnessPolynomial)
    (fun z => if loader witnessPolynomial z then maskedLoaderRecord z else fixedRecord p witnessPolynomial z)
    (fun _ => 0) (inside_isPolyTime p witnessPolynomial) h (constNat 0)

/-- Total selector for the actual masked verifier table, with zero for every
out-of-range ordinal. -/
def maskedRecordAt (p : Program) (request : Input) : Nat :=
  let input := request.1
  let i := request.2
  let k := input.length+witnessPolynomial.eval input.length
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  let mask := framedMask input input.length
  if h : i < 4*total then
    pack (lower (MaskedChoiceLoader.table k (states p) (states_positive p) mask (relativeTable p)
      ⟨i/4,by omega⟩ (decide ((i%4)/2=1)) (decide (i%2=1))))
  else 0

theorem maskedRecordAt_loader (p : Program) (input : List Bool) (i : Nat)
    (hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length)+states p))
    (hq : i/4 < Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length)) :
    maskedRecordAt p (input,i) =
      bitVal (if i/4 < input.length+witnessPolynomial.eval input.length then
        (((framedMask input input.length)[i/4]?).getD none).getD (decide (i%2=1))
        else decide ((i%4)/2=1)) +
      2*bitVal (decide (i/4 = input.length+witnessPolynomial.eval input.length ∨
        i/4 = 2*(input.length+witnessPolynomial.eval input.length)+1)) +
      16*(i/4+1)+4 := by
  simp only [maskedRecordAt,hi, ↓reduceDIte,MaskedChoiceLoader.table,
    Shared.PNP.Record285.ChoiceLoader.table,hq,lower,Option.elim_some,pack,stateCode]
  split_ifs <;> omega

/-- Beyond the loader, both tables expose the identical relocated verifier. -/
theorem maskedRecordAt_verifier (p : Program) (input : List Bool) (i : Nat)
    (hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length)+states p))
    (hq : Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length) ≤ i/4) :
    maskedRecordAt p (input,i) = verifierRecordAt p witnessPolynomial (input,i) := by
  have hk : input.length+witnessPolynomial.eval input.length ≤ i/4 := by
    unfold Shared.PNP.Record285.ChoiceLoader.offset at hq
    omega
  have hp : input.length ≤ i/4 := by omega
  simp only [maskedRecordAt,verifierRecordAt,hi, ↓reduceDIte]
  rw [MaskedChoiceLoader.table_after _ _ _ _ _ _ _ _ hk,
    HardwireChoiceLoader.table_after _ _ _ _ _ _ _ _ _ hp]

theorem maskedWorker_correct (p : Program) : maskedWorker p = maskedRecordAt p := by
  funext z
  rcases z with ⟨input,i⟩
  by_cases hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length)+states p)
  · by_cases hq : i/4 < Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length)
    · rw [maskedRecordAt_loader p input i hi hq]
      have hi' := hi
      have hq' := hq
      simp only [witnessPolynomial_eval] at hi' hq'
      simp [maskedWorker,hi',hq',maskedLoaderRecord,maskedWrite,maskChoice_correct]
    · have hq' : Shared.PNP.Record285.ChoiceLoader.offset (input.length+witnessPolynomial.eval input.length) ≤ i/4 := by omega
      rw [maskedRecordAt_verifier p input i hi hq']
      have hr := congrFun (worker_correct p witnessPolynomial) (input,i)
      have hi' := hi
      have hq'' := hq
      simp only [witnessPolynomial_eval] at hi' hq''
      simp [worker,hi',hq''] at hr
      simpa [maskedWorker,hi',hq''] using hr
  · have hi' := hi
    simp only [witnessPolynomial_eval] at hi'
    simp [maskedWorker,maskedRecordAt,hi']

theorem maskedRecordAt_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (maskedRecordAt p) := by
  rw [←maskedWorker_correct p]
  exact maskedWorker_isPolyTime p

/-- The actual masked table's four rows per state, in source selector order. -/
def maskedRows (p : Program) (input : List Bool) : List Nat :=
  let k := input.length+witnessPolynomial.eval input.length
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  tableRecords total (MaskedChoiceLoader.table k (states p) (states_positive p)
    (framedMask input input.length) (relativeTable p))

theorem maskedRows_eq_indexed (p : Program) (input : List Bool) :
    maskedRows p input = (List.range ((rowCountPolynomial p witnessPolynomial).eval input.length)).map
      (fun i => maskedRecordAt p (input,i)) := by
  rw [rowCountPolynomial_eval]
  apply List.ext_getElem
  · simp only [maskedRows,tableRecords,finiteRows,List.length_map,List.length_ofFn,List.length_range]
  · intro i hleft hright
    have hi : i < 4*(Shared.PNP.Record285.ChoiceLoader.offset
        (input.length+witnessPolynomial.eval input.length)+states p) := by
      simpa only [maskedRows,tableRecords,finiteRows,List.length_map,List.length_ofFn] using hleft
    simp only [maskedRows,tableRecords,finiteRows,List.getElem_map,List.getElem_ofFn,
      List.getElem_range,maskedRecordAt,hi, ↓reduceDIte]

theorem maskedRows_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (maskedRows p) := by
  let indices : List Bool → List Nat := fun input =>
    TM2UnaryRange.rangeFromTokens (TM2UnaryPolynomialIO.unaryPolynomial (rowCountPolynomial p witnessPolynomial) input)
  have hi : ComplexityTheory.IsPolyTime indices := TM2Compose.isPolyTime_comp
    (TM2UnaryPolynomialIO.unaryPolynomial (rowCountPolynomial p witnessPolynomial)) TM2UnaryRange.rangeFromTokens
    (TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime _) TM2UnaryRange.rangeFromTokens_isPolyTime
  have hp := TM2GuardAllStep.pair_isPolyTime (fun input : List Bool => input) indices
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩ hi
  have hc := TM2Compose.isPolyTime_comp (fun input => (input,indices input))
    (TM2ContextMapGeneric.contextMap (maskedRecordAt p)) hp
    (TM2ContextMapGeneric.contextMap_isPolyTime (maskedRecordAt p) (maskedRecordAt_isPolyTime p))
  have he : (fun input => TM2ContextMapGeneric.contextMap (maskedRecordAt p) (input,indices input)) =
      maskedRows p := by
    funext input
    simpa [TM2ContextMapGeneric.contextMap,indices,TM2UnaryRange.rangeFromTokens,
      TM2UnaryPolynomialIO.unaryPolynomial] using (maskedRows_eq_indexed p input).symm
  rw [he] at hc
  exact hc

def maskedRowTokens (p : Program) (input : List Bool) : List (List Bool) :=
  rowTokens (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witnessPolynomial) input,maskedRows p input)

theorem maskedRowTokens_lengths (p : Program) (input : List Bool) :
    (maskedRowTokens p input).map List.length = maskedRows p input := by
  apply rowTokens_lengths
  intro n hn
  simp only [TM2UnaryPolynomialIO.unaryPolynomial,List.length_replicate,rowPolynomial_eval]
  exact tableRecords_bounded _ _ n hn

theorem maskedRowTokens_isPolyTime (p : Program) : ComplexityTheory.IsPolyTime (maskedRowTokens p) := by
  have hf := TM2UnaryPolynomialIO.unaryPolynomial_isPolyTime (rowPolynomial p witnessPolynomial)
  have hp := TM2GuardAllStep.pair_isPolyTime
    (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witnessPolynomial)) (maskedRows p) hf (maskedRows_isPolyTime p)
  exact TM2Compose.isPolyTime_comp
    (fun input => (TM2UnaryPolynomialIO.unaryPolynomial (rowPolynomial p witnessPolynomial) input,maskedRows p input))
    rowTokens hp rowTokens_isPolyTime

/-- The already proved generic serializer produces the literal masked frame,
including the entire header, every row and all clock padding. -/
theorem alignedFrame_as_tokens (p : Program) (time : Polynomial Nat) (input : List Bool) :
    tokenFrame (maskedRowTokens p input,verifierPadding witnessPolynomial (alignedBudget time) input) =
      alignedFrame p time input := by
  rw [tokenFrame_eq,maskedRowTokens_lengths,verifierPadding_length]
  let k := input.length+witnessPolynomial.eval input.length
  let total := Shared.PNP.Record285.ChoiceLoader.offset k+states p
  let g := MaskedChoiceLoader.table k (states p) (states_positive p)
    (framedMask input input.length) (relativeTable p)
  let padding := (alignedBudget time).eval input.length+Shared.PNP.Record285.ChoiceLoader.offset k
  have h := finite_frame total g padding
  change List.replicate (tableWidth total g+padding) true ++
      false :: (recordBits (tableRecords total g) ++ List.replicate padding false) = _
  rw [←h]
  unfold alignedFrame frame
  dsimp only
  rw [aligned_mask_length input]
  simp only [padding,Nat.add_assoc]
  rfl

/-- The entire actual aligned masked frame has a canonical polynomial-time
constructor, including table enumeration, row encoding, padding and header. -/
theorem alignedFrame_isPolyTime (p : Program) (time : Polynomial Nat) :
    ComplexityTheory.IsPolyTime (alignedFrame p time) := by
  let padding := verifierPadding witnessPolynomial (alignedBudget time)
  have hp := TM2GuardAllStep.pair_isPolyTime (maskedRowTokens p) padding
    (maskedRowTokens_isPolyTime p) (verifierPadding_isPolyTime witnessPolynomial (alignedBudget time))
  have hc := TM2Compose.isPolyTime_comp (fun input => (maskedRowTokens p input,padding input))
    tokenFrame hp tokenFrame_isPolyTime
  have he : (fun input => tokenFrame (maskedRowTokens p input,padding input)) = alignedFrame p time := by
    funext input
    exact alignedFrame_as_tokens p time input
  rw [he] at hc
  exact hc

/-- An explicit fixed canonical SAT reduction into the source reference. -/
theorem sat_reduces_reference :
    CanonicalClasses.PolyRed Shared.ComplexityBridge.CNF.sat referenceLanguage := by
  obtain ⟨p,time,hprogram,_⟩ := aligned_sat_compiler_exists
  exact aligned_sat_reduces_of_frame_poly p time hprogram (alignedFrame_isPolyTime p time)

/-- SAT reduces to the actual source reference by a fully paid polynomial-time
map, and canonical NP hardness follows from the existing SAT completeness. -/
theorem reference_np_hard :
    ∀ L : ComplexityTheory.DecisionProblem, L ∈ ComplexityTheory.NP →
      CanonicalClasses.PolyRed L referenceLanguage :=
  reference_hard_of_alignedFrame_poly alignedFrame_isPolyTime

/-- Since the actual reference is NP-hard, a canonical polynomial-time
decider for it entails P = NP. This direction does not assume that the
reference has already been shown to belong to NP. -/
theorem reference_in_P_implies_P_eq_NP (h : referenceLanguage ∈ ComplexityTheory.P) :
    ComplexityTheory.P = ComplexityTheory.NP := by
  have hs : Shared.ComplexityBridge.CNF.sat ∈ ComplexityTheory.P :=
    TM2Compose.p_pullback_closed Shared.ComplexityBridge.CNF.sat referenceLanguage h
      (reference_np_hard Shared.ComplexityBridge.CNF.sat GeneratorGateListClosed.satComplete.member)
  exact (CanonicalClasses.p_eq_np_iff_complete_in_p GeneratorGateListClosed.satComplete
    TM2IgnoreWitness.P_subset_NP TM2Compose.p_pullback_closed).2 hs

/-- The literal-event implication now needs only the separate quantitative
source-candidate simulation premise. The premise is not supplied by the
NP-hardness or by finite trace evidence. -/
theorem literal_silent_implies_P_eq_NP_of_candidate_poly
    (hpoly : ∀ program exponent, 0 < exponent →
      ComplexityTheory.IsPolyTime (candidateLanguage program exponent))
    (hsilent : Shared.PNP.Record285.machine.system.EventuallySilent) :
    ComplexityTheory.P = ComplexityTheory.NP := by
  obtain ⟨program,exponent,hpos,hgood⟩ :=
    Shared.PNP.Record285.SourceControllerSimulation.literal_eventuallySilent_iff_goodCandidate.1 hsilent
  have he : candidateLanguage program exponent = referenceLanguage := by
    funext input
    exact (goodCandidate_iff_all_bitstrings program exponent).1 hgood input
  apply reference_in_P_implies_P_eq_NP
  rw [←he]
  exact hpoly program exponent hpos

end Shared.PNP.Record285.MaskedFramePoly
