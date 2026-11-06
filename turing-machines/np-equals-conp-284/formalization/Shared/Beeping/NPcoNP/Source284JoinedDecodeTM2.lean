import Shared.Beeping.NPcoNP.Source284JoinedFrames
import Shared.Beeping.NPcoNP.Source284RawParseTM2
import Shared.Beeping.NPcoNP.Source284BitListAccessTM2
import Shared.Beeping.NPcoNP.Source284FramedRelationVerifier

/-! A total canonical polynomial-time decoder for the joined raw layout.
Two fixed finite-control folds extract input and witness independently; on
malformed input their total behavior is simply the behavior of these folds.
The valid-layout theorem handles arbitrary high suffix bits. This module does
not yet connect the decoder's compiled source machine to a prepared window. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284JoinedDecodeTM2

open ComplexityTheory Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2PolynomialFold
open Shared.Beeping.NPcoNP.Source284JoinedFrames

abbrev Packed := (Bool × Bool) × List Bool
abbrev Input := Packed × Bool

def state (p : Input) : Packed := p.1
def flags (p : Input) : Bool × Bool := p.1.1
def f1 (p : Input) : Bool := p.1.1.1
def f2 (p : Input) : Bool := p.1.1.2
def acc (p : Input) : List Bool := p.1.2
def bit (p : Input) : Bool := p.2

def originalStep (p : Input) : Packed :=
  if f1 p then
    if bit p then ((false,false), f2 p :: acc p) else ((false,true),acc p)
  else if f2 p then state p else ((true,bit p),acc p)

def witnessStep (p : Input) : Packed :=
  if f1 p then
    if f2 p then ((true,true),bit p :: acc p) else ((true,true),acc p)
  else if f2 p then
    if bit p then ((false,false),acc p) else ((true,false),acc p)
  else ((false,true),acc p)

theorem state_isPolyTime : IsPolyTime state := TM2PairFirst.first_isPolyTime
theorem bit_isPolyTime : IsPolyTime bit := TM2GuardAllStep.second_isPolyTime
theorem flags_isPolyTime : IsPolyTime flags :=
  TM2Compose.isPolyTime_comp state (fun s : Packed => s.1) state_isPolyTime TM2PairFirst.first_isPolyTime
theorem f1_isPolyTime : IsPolyTime f1 :=
  TM2Compose.isPolyTime_comp flags (fun p : Bool × Bool => p.1) flags_isPolyTime TM2PairFirst.first_isPolyTime
theorem f2_isPolyTime : IsPolyTime f2 :=
  TM2Compose.isPolyTime_comp flags (fun p : Bool × Bool => p.2) flags_isPolyTime TM2GuardAllStep.second_isPolyTime
theorem acc_isPolyTime : IsPolyTime acc :=
  TM2Compose.isPolyTime_comp state (fun s : Packed => s.2) state_isPolyTime TM2GuardAllStep.second_isPolyTime

theorem const_bool_isPolyTime (b : Bool) : IsPolyTime (fun _ : Input => b) := TM2Constant.isPolyTime b

theorem const_flags_isPolyTime (a b : Bool) : IsPolyTime (fun _ : Input => (a,b)) :=
  TM2GuardAllStep.pair_isPolyTime (fun _ : Input => a) (fun _ : Input => b)
    (const_bool_isPolyTime a) (const_bool_isPolyTime b)

theorem push_isPolyTime (f : Input → Bool) (hf : IsPolyTime f) : IsPolyTime (fun p => f p :: acc p) := by
  have hpair := TM2GuardAllStep.pair_isPolyTime f acc hf acc_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun p : Input => (f p,acc p))
    (TM2ListAppend.cons (α := Bool)) hpair TM2ListAppend.cons_isPolyTime
  simpa [TM2ListAppend.cons] using h

theorem pair_const_acc_isPolyTime (a b : Bool) : IsPolyTime (fun p : Input => ((a,b),acc p)) :=
  TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (a,b)) acc (const_flags_isPolyTime a b) acc_isPolyTime

theorem originalStep_isPolyTime : IsPolyTime originalStep := by
  have hp : IsPolyTime (fun p : Input => ((false,false),f2 p::acc p)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (false,false))
      (fun p => f2 p::acc p) (const_flags_isPolyTime false false) (push_isPolyTime f2 f2_isPolyTime)
  have hs := pair_const_acc_isPolyTime false true
  have hmarker := TM2If.if_isPolyTime bit (fun p : Input => ((false,false),f2 p::acc p))
    (fun p => ((false,true),acc p)) bit_isPolyTime hp hs
  have hflags : IsPolyTime (fun p : Input => (true,bit p)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => true) bit (const_bool_isPolyTime true) bit_isPolyTime
  have hread : IsPolyTime (fun p : Input => ((true,bit p),acc p)) :=
    TM2GuardAllStep.pair_isPolyTime (fun p : Input => (true,bit p)) acc hflags acc_isPolyTime
  have hwork := TM2If.if_isPolyTime f2 state (fun p : Input => ((true,bit p),acc p))
    f2_isPolyTime state_isPolyTime hread
  exact TM2If.if_isPolyTime f1
    (fun p : Input => if bit p then ((false,false),f2 p::acc p) else ((false,true),acc p))
    (fun p : Input => if f2 p then state p else ((true,bit p),acc p))
    f1_isPolyTime hmarker hwork

theorem witnessStep_isPolyTime : IsPolyTime witnessStep := by
  have hp : IsPolyTime (fun p : Input => ((true,true),bit p::acc p)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : Input => (true,true))
      (fun p => bit p::acc p) (const_flags_isPolyTime true true) (push_isPolyTime bit bit_isPolyTime)
  have htt := pair_const_acc_isPolyTime true true
  have hcollect := TM2If.if_isPolyTime f2 (fun p : Input => ((true,true),bit p::acc p))
    (fun p : Input => ((true,true),acc p)) f2_isPolyTime hp htt
  have hff := pair_const_acc_isPolyTime false false
  have htf := pair_const_acc_isPolyTime true false
  have hmark := TM2If.if_isPolyTime bit (fun p : Input => ((false,false),acc p))
    (fun p : Input => ((true,false),acc p)) bit_isPolyTime hff htf
  have hft := pair_const_acc_isPolyTime false true
  have hskip := TM2If.if_isPolyTime f2
    (fun p : Input => if bit p then ((false,false),acc p) else ((true,false),acc p))
    (fun p : Input => ((false,true),acc p)) f2_isPolyTime hmark hft
  exact TM2If.if_isPolyTime f1
    (fun p : Input => if f2 p then ((true,true),bit p::acc p) else ((true,true),acc p))
    (fun p : Input => if f2 p then (if bit p then ((false,false),acc p) else ((true,false),acc p)) else ((false,true),acc p))
    f1_isPolyTime hcollect hskip

theorem original_length (s : Packed) (b : Bool) : (originalStep (s,b)).2.length ≤ s.2.length+1 := by
  rcases s with ⟨⟨a,c⟩,xs⟩
  cases a <;> cases c <;> cases b <;> simp [originalStep,state,f1,f2,acc,bit]

theorem witness_length (s : Packed) (b : Bool) : (witnessStep (s,b)).2.length ≤ s.2.length+1 := by
  rcases s with ⟨⟨a,c⟩,xs⟩
  cases a <;> cases c <;> cases b <;> simp [witnessStep,state,f1,f2,acc,bit]

theorem original_fold_isPolyTime : IsPolyTime (TM2FoldGenericIO.result originalStep) := by
  apply TM2FoldGenericBounds.isPolyTime_of_prefix_bound originalStep originalStep_isPolyTime
  refine ⟨Polynomial.X,?_⟩
  intro flags xs pref tail hxs
  simpa only [Polynomial.eval_X] using
    Source284ParseBounds.fold_prefix_encoded_bound originalStep original_length flags xs pref tail hxs

theorem witness_fold_isPolyTime : IsPolyTime (TM2FoldGenericIO.result witnessStep) := by
  apply TM2FoldGenericBounds.isPolyTime_of_prefix_bound witnessStep witnessStep_isPolyTime
  refine ⟨Polynomial.X,?_⟩
  intro flags xs pref tail hxs
  simpa only [Polynomial.eval_X] using
    Source284ParseBounds.fold_prefix_encoded_bound witnessStep witness_length flags xs pref tail hxs

def foldInput (xs : List Bool) : (Bool × Bool) × List Bool := ((false,false),xs.tail)

theorem foldInput_isPolyTime : IsPolyTime foldInput := by
  have hfalse : IsPolyTime (fun _ : List Bool => false) := TM2Constant.isPolyTime false
  have hf : IsPolyTime (fun _ : List Bool => (false,false)) :=
    TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => false) (fun _ : List Bool => false) hfalse hfalse
  exact TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => (false,false)) List.tail
    hf Source284BitListAccessTM2.tail_isPolyTime

def extractInput (xs : List Bool) : List Bool := (TM2FoldGenericIO.result originalStep (foldInput xs)).2

def extractWitnessRaw (xs : List Bool) : List Bool := (TM2FoldGenericIO.result witnessStep (foldInput xs)).2

def extractWitness (xs : List Bool) : List Bool := Source284RawParse.payload (extractWitnessRaw xs |>.reverse)

def decode (xs : List Bool) : List Bool × List Bool := (extractInput xs,extractWitness xs)

theorem extractInput_isPolyTime : IsPolyTime extractInput := by
  have h := TM2Compose.isPolyTime_comp foldInput (TM2FoldGenericIO.result originalStep)
    foldInput_isPolyTime original_fold_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun xs => TM2FoldGenericIO.result originalStep (foldInput xs))
    (fun p : Packed => p.2) h TM2GuardAllStep.second_isPolyTime

theorem extractWitness_isPolyTime : IsPolyTime extractWitness := by
  have h := TM2Compose.isPolyTime_comp foldInput (TM2FoldGenericIO.result witnessStep)
    foldInput_isPolyTime witness_fold_isPolyTime
  have hraw := TM2Compose.isPolyTime_comp (fun xs => TM2FoldGenericIO.result witnessStep (foldInput xs))
    (fun p : Packed => p.2) h TM2GuardAllStep.second_isPolyTime
  have hr := TM2Compose.isPolyTime_comp extractWitnessRaw (List.reverse : List Bool → List Bool)
    hraw TM2ListReverse.reverse_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun xs => (extractWitnessRaw xs).reverse) Source284RawParse.payload
    hr Source284RawParseTM2.payload_isPolyTime

theorem decode_isPolyTime : IsPolyTime decode :=
  TM2GuardAllStep.pair_isPolyTime extractInput extractWitness extractInput_isPolyTime extractWitness_isPolyTime

@[simp] theorem fold_cons (step : Input → Packed) (s : Packed) (b : Bool) (xs : List Bool) :
    fold step s (b::xs) = fold step (step (s,b)) xs := rfl

theorem original_done (xs accBits : List Bool) :
    fold originalStep ((false,true),accBits) xs = ((false,true),accBits) := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simpa [originalStep,state,f1,f2,acc,bit] using ih

theorem original_blocks (xs rest : List Bool) : ∀ accBits : List Bool,
    fold originalStep ((false,false),accBits)
      (reverseBlocks xs ++ [false,false,false] ++ rest) = ((false,true),xs.reverse++accBits) := by
  induction xs with
  | nil =>
    intro accBits
    simpa [reverseBlocks,originalStep,state,f1,f2,acc,bit] using original_done (false::rest) accBits
  | cons b bs ih =>
    intro accBits
    have ih' (a : List Bool) :
        fold originalStep ((false,false),a) (reverseBlocks bs ++ (false::false::false::rest)) =
          ((false,true),bs.reverse++a) := by simpa [List.append_assoc] using ih a
    cases b <;>
      simp [reverseBlocks,originalStep,state,f1,f2,acc,bit,ih',List.reverse_cons,List.append_assoc]

theorem witness_collect (xs : List Bool) : ∀ accBits : List Bool,
    fold witnessStep ((true,true),accBits) xs = ((true,true),xs.reverse++accBits) := by
  induction xs with
  | nil => intro accBits; rfl
  | cons b bs ih =>
    intro accBits
    simpa [witnessStep,f1,f2,acc,bit,List.reverse_cons,List.append_assoc] using ih (b::accBits)

theorem witness_blocks (xs rest : List Bool) : ∀ accBits : List Bool,
    fold witnessStep ((false,false),accBits)
      (reverseBlocks xs ++ [false,false,false] ++ rest) = ((true,true),rest.reverse++accBits) := by
  induction xs with
  | nil =>
    intro accBits
    simpa [reverseBlocks,witnessStep,f1,f2,acc,bit] using witness_collect rest accBits
  | cons b bs ih =>
    intro accBits
    have ih' : fold witnessStep ((false,false),accBits)
        (reverseBlocks bs ++ (false::false::false::rest)) = ((true,true),rest.reverse++accBits) := by
      simpa [List.append_assoc] using ih accBits
    cases b <;> simp [reverseBlocks,witnessStep,f1,f2,acc,bit,ih']

theorem joined_tail (x w extra : List Bool) :
    (joinedBits x w ++ extra).tail =
      reverseBlocks x.reverse ++ [false,false,false] ++ (Source284Parser.frameBits w [true] ++ extra) := by
  simp [joinedBits,reversed_frame,List.append_assoc]

/-- Both folds compute the original input and witness on every correctly
joined finite prefix, for every arbitrary high bit suffix. -/
theorem decode_correct (x w extra : List Bool) : decode (joinedBits x w ++ extra) = (x,w) := by
  have hx := original_blocks x.reverse (Source284Parser.frameBits w [true] ++ extra) []
  have hw := witness_blocks x.reverse (Source284Parser.frameBits w [true] ++ extra) []
  simp only [List.reverse_reverse,List.append_nil] at hx hw
  unfold decode extractInput extractWitness extractWitnessRaw foldInput TM2FoldGenericIO.result
  rw [joined_tail,hx,hw]
  simp only [List.reverse_reverse]
  rw [frameBits_append,payload_frame_suffix]

/-- Any canonical polynomial-time relation can consume the joined layout via
this actual polynomial-time decoder. The theorem does not assert a physical
machine or hide the caller's finite input-window construction. -/
theorem relation_isPolyTime (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    IsPolyTime (fun bits => R (decode bits)) :=
  TM2Compose.isPolyTime_comp decode R decode_isPolyTime hR

theorem relation_correct (R : List Bool × List Bool → Bool) (x w extra : List Bool) :
    R (decode (joinedBits x w ++ extra)) = R (x,w) := by rw [decode_correct]

namespace Fixtures
example : decode [] = ([],[]) := by decide +kernel
example : decode (joinedBits [] [] ++ [true,false]) = ([],[]) := decode_correct _ _ _
example : decode (joinedBits [false,true] [true,false] ++ [true,true]) =
    ([false,true],[true,false]) := decode_correct _ _ _
end Fixtures
/-- Embed the joined list as the first component of the existing canonical
pair compiler. This is an executable polynomial-time reduction on all inputs. -/
def pairedRelation (R : List Bool × List Bool → Bool) (p : List Bool × List Bool) : Bool :=
  R (decode p.1)

theorem pairedRelation_isPolyTime (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    IsPolyTime (pairedRelation R) := by
  have hfirst : IsPolyTime (fun p : List Bool × List Bool => p.1) := TM2PairFirst.first_isPolyTime
  have hdecode : IsPolyTime (fun p : List Bool × List Bool => decode p.1) :=
    TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => p.1) decode hfirst decode_isPolyTime
  exact TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => decode p.1) R hdecode hR

theorem canonical_joined_length (x w : List Bool) :
    (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))).length =
      12*x.length+12*w.length+37 := by
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length,joined_length]
  simp
  omega

/-- The existing finite-program compiler produces an actual fixed source
verifier for a canonically encoded joined list. The window hypothesis is
explicit: constructing it from the raw joined tape is not proved here. -/
theorem source_verifier (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) :
    ∃ (program : Shared.Codes.FinitePrograms.Program) (clock : Polynomial Nat),
      Shared.Codes.FinitePrograms.valid program = true ∧
      ∀ (x w : List Bool) (limit : Nat), w.length ≤ limit →
      ∀ (c : Source284Relative.Config) (extra : Nat),
        let packed := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
        let t := clock.eval (12*x.length+12*limit+37)
        Source284Relative.Window t c (Source284Relative.initial (Shared.Codes.BitNumeralCompare.value packed) 0) →
        ((Source284Relative.run (Source284CompileRecords.compile program) c (t+extra)).state == 0) = R (x,w) := by
  obtain ⟨raw,clock,hcorrect⟩ := FiniteVerifierCompiler.canonical_finite_verifier_compiler
    (pairedRelation R) (pairedRelation_isPolyTime R hR)
  let program := Shared.Codes.FiniteProgramRepair.repair raw
  refine ⟨program,clock,Shared.Codes.FiniteProgramRepair.repair_valid raw,?_⟩
  intro x w limit hw c extra
  dsimp only
  intro hwindow
  let packed := BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool))
  let t := clock.eval (12*x.length+12*limit+37)
  have hlen : packed.length ≤ 12*x.length+12*limit+37 := by
    dsimp only [packed]
    rw [canonical_joined_length]
    omega
  have hclock : clock.eval packed.length ≤ t := TM2Compose.polynomial_eval_mono clock hlen
  have hd : decode (joinedBits x w) = (x,w) := by simpa using decode_correct x w []
  have hsmall := hcorrect (joinedBits x w) []
  simp only [pairedRelation,hd] at hsmall
  have hbounded : Shared.Codes.FinitePrograms.bounded program packed t = some (R (x,w)) := by
    dsimp only [program]
    rw [Shared.Codes.FiniteProgramRepair.bounded_repair]
    exact BoundedHardness.bounded_mono raw packed (clock.eval packed.length) t (R (x,w)) hclock hsmall
  exact Source284PackedGuardIsolation.compiled_window_stable program packed t (R (x,w))
    (Shared.Codes.FiniteProgramRepair.repair_valid raw) hbounded c hwindow extra

end Shared.Beeping.NPcoNP.Source284JoinedDecodeTM2
