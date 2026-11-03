import Shared.PNP.Record285.HardwireFiniteVerifier
import Shared.ComplexityBridge.TM2ContextMapGeneric
import Shared.ComplexityBridge.TM2FlattenList
import Shared.ComplexityBridge.TM2ListUnaryLength
import Shared.ComplexityBridge.TM2Constant
import Shared.ComplexityBridge.TM2EmptyConstant

/-! Exact list serialization for the 285-state reference frame.  This
removes the exponentially large intermediate natural number from the frame
construction.  The row-producing worker remains a separate obligation. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ReferenceSerialization
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.HardwireFiniteVerifier
open Shared.Codes.FinitePrograms

/-- The actual least-significant-bit-first encoding of unary records. -/
def recordBits : List Nat → List Bool
  | [] => []
  | a :: rest => List.replicate a true ++ false :: recordBits rest

@[simp] theorem recordBits_length (records : List Nat) :
    (recordBits records).length = width records := by
  induction records with
  | nil => rfl
  | cons a rest ih => simp [recordBits,width,ih]; omega

theorem value_record (a : Nat) (tail : List Bool) :
    value (List.replicate a true ++ false :: tail) = prepend a (value tail) := by
  induction a with
  | zero => simp [value,prepend]
  | succ a ih => simp [List.replicate_succ,value,prepend,ih]; omega

@[simp] theorem recordBits_value (records : List Nat) : value (recordBits records) = encode records := by
  induction records with
  | nil => rfl
  | cons a rest ih => simp [recordBits,encode,value_record,ih]

/-- Extraction preserves all supplied bits and appends exactly the requested
number of zeros, including when the supplied bits already end in zero. -/
theorem bits_value_pad (xs : List Bool) (padding : Nat) :
    bits (xs.length+padding) (value xs) = xs ++ List.replicate padding false := by
  induction xs with
  | nil =>
    induction padding with
    | zero => rfl
    | succ n ih =>
      simp only [List.length_nil,Nat.zero_add,value,List.nil_append] at ih
      simp [bits,value,ih,List.replicate_succ]
  | cons b xs ih =>
    have hm : value (b::xs) % 2 = if b then 1 else 0 := by cases b <;> simp [value]
    have hd : value (b::xs) / 2 = value xs := by cases b <;> simp [value] <;> omega
    have hn : (b::xs).length+padding = (xs.length+padding)+1 := by simp; omega
    rw [hn,bits,hm,hd]
    cases b <;> simp [ih]

/-- A finite table's frame is built directly from its unary row stream,
including its length header and its explicit zero padding. -/
theorem finite_frame (n : Nat)
    (f : Fin n → Bool → Bool → FiniteAction n)
    (padding : Nat) :
    canonical (bits (tableWidth n f+padding) (finiteProgram n f)) =
      List.replicate (tableWidth n f+padding) true ++
        false :: (recordBits (tableRecords n f) ++ List.replicate padding false) := by
  have hp := bits_value_pad (recordBits (tableRecords n f)) padding
  rw [recordBits_length,recordBits_value] at hp
  change bits (tableWidth n f+padding) (finiteProgram n f) = _ at hp
  simpa [canonical,tableWidth] using congrArg canonical hp

/-- Exact bit-list construction for the actual hardwired verifier frame. -/
theorem verifier_frame (p : Program) (publicBits : List Bool) (count budget : Nat) :
    let k := publicBits.length+count
    let n := states p
    let g := Shared.PNP.Record285.HardwireChoiceLoader.table k n (states_positive p)
      publicBits.length (value publicBits) (relativeTable p)
    let total := Shared.PNP.Record285.ChoiceLoader.offset k+n
    let padding := budget+Shared.PNP.Record285.ChoiceLoader.offset k
    verifierReferenceFrame p publicBits count budget =
      List.replicate (tableWidth total g+padding) true ++
        false :: (recordBits (tableRecords total g) ++ List.replicate padding false) := by
  dsimp only
  have h := finite_frame
    (Shared.PNP.Record285.ChoiceLoader.offset (publicBits.length+count)+states p)
    (Shared.PNP.Record285.HardwireChoiceLoader.table (publicBits.length+count) (states p)
      (states_positive p) publicBits.length (value publicBits) (relativeTable p))
    (budget+Shared.PNP.Record285.ChoiceLoader.offset (publicBits.length+count))
  simpa [verifierReferenceFrame,Nat.add_assoc] using h

open Shared.ComplexityBridge

/-- Row lengths are supplied as token lists, so the running time is charged
against their actual unary representation rather than a binary natural. -/
def tokenRecord (tokens : List Bool) : List Bool :=
  TM2ListUnaryLength.unaryLength tokens ++ [false]

def tokenStream (rows : List (List Bool)) : List Bool :=
  (rows.map tokenRecord).flatten

def tokenFrame (input : List (List Bool) × List Bool) : List Bool :=
  canonical (tokenStream input.1 ++ input.2.map (fun _ => false))

@[simp] theorem tokenStream_eq (rows : List (List Bool)) :
    tokenStream rows = recordBits (rows.map List.length) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change (rows.map tokenRecord).flatten = _ at ih
    simp [tokenStream, tokenRecord, TM2ListUnaryLength.unaryLength,
      recordBits, List.append_assoc, ih]

/-- Both token contents are ignored: only their lengths describe the unary
rows and the number of explicit padding zeros. -/
theorem tokenFrame_eq (rows : List (List Bool)) (padding : List Bool) :
    tokenFrame (rows,padding) =
      List.replicate (width (rows.map List.length)+padding.length) true ++
        false :: (recordBits (rows.map List.length) ++ List.replicate padding.length false) := by
  simp [tokenFrame,canonical,tokenStream_eq]

/-- Producing each unary record, flattening the records, writing the padding,
and producing the actual length header all run in canonical polynomial time. -/
theorem tokenRecord_isPolyTime : ComplexityTheory.IsPolyTime tokenRecord := by
  let singles : List Bool → List Bool := fun _ => [false]
  have hs : ComplexityTheory.IsPolyTime singles := by
    let empty : List Bool → List Bool := fun _ => []
    have he : ComplexityTheory.IsPolyTime empty := TM2EmptyConstant.isPolyTime [] rfl
    have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => false) empty
      (TM2Constant.isPolyTime false) he
    have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (false,empty xs))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    exact h
  have hp := TM2GuardAllStep.pair_isPolyTime TM2ListUnaryLength.unaryLength singles
    (TM2ListUnaryLength.unaryLength_isPolyTime (α := Bool)) hs
  have h := TM2Compose.isPolyTime_comp
    (fun xs : List Bool => (TM2ListUnaryLength.unaryLength xs,singles xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  change ComplexityTheory.IsPolyTime (fun xs : List Bool =>
    TM2ListUnaryLength.unaryLength xs ++ [false])
  exact h

theorem tokenStream_isPolyTime : ComplexityTheory.IsPolyTime tokenStream := by
  have hm := TM2ContextMapGeneric.listMap_isPolyTime tokenRecord tokenRecord_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun rows : List (List Bool) => rows.map tokenRecord)
    (List.flatten (α := Bool)) hm TM2FlattenList.flatten_isPolyTime
  exact h

theorem canonical_isPolyTime : ComplexityTheory.IsPolyTime canonical := by
  let tail : List Bool → List Bool := fun xs => false :: xs
  have ht : ComplexityTheory.IsPolyTime tail := by
    have hp := TM2GuardAllStep.pair_isPolyTime (fun _ : List Bool => false) (fun xs : List Bool => xs)
      (TM2Constant.isPolyTime false) ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
    have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (false,xs))
      (TM2ListAppend.cons (α := Bool)) hp TM2ListAppend.cons_isPolyTime
    exact h
  have hp := TM2GuardAllStep.pair_isPolyTime TM2ListUnaryLength.unaryLength tail
    (TM2ListUnaryLength.unaryLength_isPolyTime (α := Bool)) ht
  have h := TM2Compose.isPolyTime_comp
    (fun xs : List Bool => (TM2ListUnaryLength.unaryLength xs,tail xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  exact h

theorem tokenFrame_isPolyTime : ComplexityTheory.IsPolyTime tokenFrame := by
  let rows : (List (List Bool) × List Bool) → List Bool := fun x => tokenStream x.1
  let padding : (List (List Bool) × List Bool) → List Bool := fun x => x.2.map (fun _ => false)
  have hr : ComplexityTheory.IsPolyTime rows := TM2Compose.isPolyTime_comp
    (fun x : List (List Bool) × List Bool => x.1) tokenStream TM2PairFirst.first_isPolyTime tokenStream_isPolyTime
  have hz := TM2ContextMapGeneric.listMap_isPolyTime (fun _ : Bool => false) (TM2Constant.isPolyTime false)
  have hd : ComplexityTheory.IsPolyTime padding := TM2Compose.isPolyTime_comp
    (fun x : List (List Bool) × List Bool => x.2) (fun xs : List Bool => xs.map (fun _ => false))
    TM2GuardAllStep.second_isPolyTime hz
  have hp := TM2GuardAllStep.pair_isPolyTime rows padding hr hd
  have hb := TM2Compose.isPolyTime_comp (fun x => (rows x,padding x))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun x => TM2ListAppend.append (rows x,padding x))
    canonical hb canonical_isPolyTime
  exact h

/-- The remaining worker must output one unary token list for every actual
row and a unary padding list. This equality checks every row, including its
choice-dependent variants. -/
theorem tokenFrame_verifier (p : Program) (publicBits : List Bool) (count budget : Nat)
    (rows : List (List Bool)) (padding : List Bool)
    (hrows : rows.map List.length = tableRecords
      (Shared.PNP.Record285.ChoiceLoader.offset (publicBits.length+count)+states p)
      (Shared.PNP.Record285.HardwireChoiceLoader.table (publicBits.length+count) (states p)
        (states_positive p) publicBits.length (value publicBits) (relativeTable p)))
    (hpadding : padding.length = budget+Shared.PNP.Record285.ChoiceLoader.offset (publicBits.length+count)) :
    tokenFrame (rows,padding) = verifierReferenceFrame p publicBits count budget := by
  rw [tokenFrame_eq,hrows,hpadding]
  exact (verifier_frame p publicBits count budget).symm

/-- Conditional composition theorem for the precise missing front end.
The two workers must themselves be polynomial-time and must construct every
row token and the required padding, uniformly for all public inputs. -/
theorem verifier_frame_isPolyTime_of_workers (p : Program)
    (count budget : List Bool → Nat)
    (rows : List Bool → List (List Bool)) (padding : List Bool → List Bool)
    (hrowsTime : ComplexityTheory.IsPolyTime rows)
    (hpaddingTime : ComplexityTheory.IsPolyTime padding)
    (hrows : ∀ input, (rows input).map List.length = tableRecords
      (Shared.PNP.Record285.ChoiceLoader.offset (input.length+count input)+states p)
      (Shared.PNP.Record285.HardwireChoiceLoader.table (input.length+count input) (states p)
        (states_positive p) input.length (value input) (relativeTable p)))
    (hpadding : ∀ input, (padding input).length =
      budget input+Shared.PNP.Record285.ChoiceLoader.offset (input.length+count input)) :
    ComplexityTheory.IsPolyTime (fun input => verifierReferenceFrame p input (count input) (budget input)) := by
  have hp := TM2GuardAllStep.pair_isPolyTime rows padding hrowsTime hpaddingTime
  have hc := TM2Compose.isPolyTime_comp (fun input => (rows input,padding input)) tokenFrame hp tokenFrame_isPolyTime
  have he : (fun input => tokenFrame (rows input,padding input)) =
      (fun input => verifierReferenceFrame p input (count input) (budget input)) := by
    funext input
    exact tokenFrame_verifier p input (count input) (budget input) (rows input) (padding input)
      (hrows input) (hpadding input)
  rw [← he]
  exact hc

/-- The serialized frame retains the full bounded-verifier language theorem;
the explicit totality premise excludes accepting a timeout. -/
theorem tokenFrame_reference_total (p : Program) (input : List Bool) (count budget : Nat)
    (rows : List (List Bool)) (padding : List Bool)
    (hrows : rows.map List.length = tableRecords
      (Shared.PNP.Record285.ChoiceLoader.offset (input.length+count)+states p)
      (Shared.PNP.Record285.HardwireChoiceLoader.table (input.length+count) (states p)
        (states_positive p) input.length (value input) (relativeTable p)))
    (hpadding : padding.length = budget+Shared.PNP.Record285.ChoiceLoader.offset (input.length+count))
    (htotal : ∀ witness : List Bool, witness.length ≤ count →
      ∃ result, bounded p (input++witness) budget = some result) :
    Shared.PNP.Record285.CanonicalInput.referenceLanguage (tokenFrame (rows,padding)) = true ↔
      ∃ witness : List Bool, witness.length ≤ count ∧ bounded p (input++witness) budget = some true := by
  rw [tokenFrame_verifier p input count budget rows padding hrows hpadding]
  exact reference_padded_total_verifier p input count budget htotal

end Shared.PNP.Record285.ReferenceSerialization
