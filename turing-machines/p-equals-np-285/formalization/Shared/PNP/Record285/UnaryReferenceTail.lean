import Shared.PNP.Record285.UnaryProgram
import Shared.PNP.Record285.CanonicalInput

/-! Exact finite-table embedding into the reference's sentinel-terminated
program numbers. The arbitrary high tail is not assumed to be zero. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.CanonicalInput

def encodeTail : List Nat → Nat → Nat
  | [], tail => tail
  | a :: rest, tail => prepend a (encodeTail rest tail)

def width : List Nat → Nat
  | [] => 0
  | a :: rest => a+1+width rest

@[simp] theorem encodeTail_zero (records : List Nat) : encodeTail records 0 = encode records := by
  induction records with
  | nil => rfl
  | cons a records ih => simp [encodeTail,encode,ih]

theorem skip_encodeTail (n : Nat) (records : List Nat) (tail : Nat) (h : n ≤ records.length) :
    skipUnary n (encodeTail records tail) = encodeTail (records.drop n) tail := by
  induction n generalizing records with
  | zero => rfl
  | succ n ih =>
    cases records with
    | nil => simp at h
    | cons a rest =>
      have hr : n ≤ rest.length := by simpa using h
      simpa [skipUnary,encodeTail] using ih rest hr

/-- Earlier records decode identically for every arbitrary suffix. -/
theorem record_tail (records : List Nat) (tail ordinal : Nat) (h : ordinal < records.length) :
    (popUnary (skipUnary ordinal (encodeTail records tail))).1 = records[ordinal] := by
  rw [skip_encodeTail _ _ _ (by omega)]
  induction ordinal generalizing records with
  | zero =>
    cases records with
    | nil => simp at h
    | cons a rest => simp [encodeTail]
  | succ ordinal ih =>
    cases records with
    | nil => simp at h
    | cons a rest => simpa using ih rest (by simpa using h)

/-- The suffix is deliberately not treated as virtual zero beyond the listed
records: this concrete extra row differs when the suffix is nonzero. -/
theorem high_tail_changes_unlisted_record :
    (popUnary (skipUnary 1 (encodeTail [0] 1))).1 = 1 ∧
    (popUnary (skipUnary 1 (encode [0]))).1 = 0 := by
  simp [encodeTail,encode,prepend,skipUnary,popUnary]

def encodeActionsTail (rows : List Action) (tail : Nat) : Nat := encodeTail (rows.map pack) tail

theorem finite_table_tail (n : Nat) (f : Fin n → Bool → Bool → Action)
    (tail : Nat) (q : Fin n) (read choice : Bool) :
    rowAction (encodeActionsTail (finiteRows n f) tail) (stateCode q) read choice = f q read choice := by
  have hrow := finiteRows_at n f q read choice
  let i := stateCode q - 1 + 2*bitVal read + bitVal choice
  have hi : i < (finiteRows n f).length := by
    have hh := List.getElem?_eq_some_iff.mp hrow
    exact hh.1
  have hrecord := record_tail ((finiteRows n f).map pack) tail i (by simpa using hi)
  unfold rowAction encodeActionsTail
  change unpack ((popUnary (skipUnary i (encodeTail ((finiteRows n f).map pack) tail))).1) = _
  rw [hrecord]
  have hh : (finiteRows n f)[i] = f q read choice := by
    have ht := List.getElem?_eq_some_iff.mp hrow
    exact ht.2
  simp [List.getElem_map,hh]

def finiteProgramTail (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n) (tail : Nat) : Nat :=
  encodeActionsTail (finiteRows n fun q read choice => lower (f q read choice)) tail

theorem finiteStep_tail (f : Fin n → Bool → Bool → FiniteAction n)
    (tail : Nat) (c : FiniteConfig n) :
    (finiteStep f c).map embed = relativeStep (finiteProgramTail n f tail) (embed c) := by
  unfold finiteStep relativeStep embed finiteProgramTail
  simp only [finite_table_tail]
  generalize h : f c.state (c.physical.tape c.physical.head) (c.choices.testBit 0) = a
  cases a with
  | mk write turn next =>
    cases next with
    | none => rfl
    | some target => simp [lower,stateCode]

theorem finiteRun_tail (f : Fin n → Bool → Bool → FiniteAction n)
    (tail clock : Nat) (c : FiniteConfig n) :
    (finiteRun f clock c).map embed = relativeRun (finiteProgramTail n f tail) clock (embed c) := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    have hs := finiteStep_tail f tail c
    cases hf : finiteStep f c with
    | none =>
      simp only [hf, Option.map_none] at hs
      simp [finiteRun,hf,relativeRun,← hs]
    | some next =>
      simp only [hf, Option.map_some] at hs
      simpa [finiteRun,hf,relativeRun,← hs] using ih next

/-- A prepended record occupies exactly `count+1` bits, with all higher
bits carried in the tail. -/
theorem prepend_add_tail (count x y : Nat) :
    prepend count (x+y) = prepend count x + 2^(count+1)*y := by
  induction count with
  | zero => simp [prepend,Nat.mul_add]
  | succ count ih =>
    have hp : 2^(count+1+1)*y = 2*(2^(count+1)*y) := by
      rw [Nat.pow_succ]
      simp [Nat.mul_comm,Nat.mul_left_comm]
    simp only [prepend,ih]
    rw [hp]
    omega

theorem encodeTail_arithmetic (records : List Nat) (tail : Nat) :
    encodeTail records tail = encode records + 2^(width records)*tail := by
  induction records with
  | nil => simp [encodeTail,encode,width]
  | cons a rest ih =>
    simp only [encodeTail,encode,width,ih,prepend_add_tail,Nat.pow_add,Nat.mul_assoc]

/-- Every encoded finite record list fits strictly inside its declared bit
width, even when records themselves have zero length. -/
theorem prepend_bound (count tail bits : Nat) (h : tail < 2^bits) :
    prepend count tail < 2^(count+1+bits) := by
  induction count with
  | zero =>
    simp only [prepend]
    have he : 2^(0+1+bits) = 2*2^bits := by
      have hh : 0+1+bits = bits+1 := by omega
      rw [hh,Nat.pow_succ,Nat.mul_comm]
    rw [he]
    omega
  | succ count ih =>
    have he : 2^(count+1+1+bits) = 2*2^(count+1+bits) := by
      have hh : count+1+1+bits = (count+1+bits)+1 := by omega
      rw [hh,Nat.pow_succ,Nat.mul_comm]
    rw [he]
    simp only [prepend]
    omega

theorem encode_lt_width (records : List Nat) : encode records < 2^(width records) := by
  induction records with
  | nil => simp [encode,width]
  | cons a rest ih => exact prepend_bound a (encode rest) (width rest) ih

/-- A high sentinel after any number of zero padding bits has the exact
natural value required by the selected reference enumeration. -/
theorem sentinel_number (records : List Nat) (padding : Nat) :
    encodeTail records (2^padding) = 2^(width records+padding)+encode records := by
  rw [encodeTail_arithmetic,Nat.pow_add]
  omega

/-- Record list and width used by the exact finite nondeterministic table. -/
def tableRecords (states : Nat) (f : Fin states → Bool → Bool → FiniteAction states) : List Nat :=
  (finiteRows states fun q read choice => lower (f q read choice)).map pack

def tableWidth (states : Nat) (f : Fin states → Bool → Bool → FiniteAction states) : Nat :=
  width (tableRecords states f)

theorem finiteProgram_sentinel (states : Nat) (f : Fin states → Bool → Bool → FiniteAction states)
    (padding : Nat) :
    finiteProgramTail states f (2^padding) =
      2^(tableWidth states f+padding)+finiteProgram states f := by
  exact sentinel_number (tableRecords states f) padding

theorem finiteProgram_lt_sentinel (states : Nat) (f : Fin states → Bool → Bool → FiniteAction states)
    (padding : Nat) : finiteProgram states f < 2^(tableWidth states f+padding) := by
  have h := encode_lt_width (tableRecords states f)
  have hp : 2^(tableWidth states f) ≤ 2^(tableWidth states f+padding) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
  exact Nat.lt_of_lt_of_le h hp

/-- The actual source reference, with its fixed high sentinel and arbitrary
zero padding, exactly searches the finite nondeterministic table from a blank
tape. The witness bound and clock are both the actual source values. -/
theorem reference_embeds_finite (states : Nat) (hn : 0 < states)
    (f : Fin states → Bool → Bool → FiniteAction states) (padding : Nat) :
    let clock := tableWidth states f+padding
    Source.reference clock (2^clock) (finiteProgram states f) = true ↔
      ∃ branch, branch < 2^clock ∧ finiteRun f clock (finiteInitial hn 0 branch) = none := by
  dsimp only
  rw [reference_halts_iff]
  have hp := finiteProgram_sentinel states f padding
  rw [←hp]
  constructor <;> rintro ⟨branch,hbound,hresult⟩ <;> refine ⟨branch,hbound,?_⟩
  · have h := finiteRun_tail f (2^padding) (tableWidth states f+padding) (finiteInitial hn 0 branch)
    rw [embed_finiteInitial] at h
    rw [←h] at hresult
    cases hr : finiteRun f (tableWidth states f+padding) (finiteInitial hn 0 branch) <;> simp_all
  · have h := finiteRun_tail f (2^padding) (tableWidth states f+padding) (finiteInitial hn 0 branch)
    rw [embed_finiteInitial,hresult] at h
    simpa using h.symm

/-- The same exact theorem is exposed through the all-bitstring reference
language on a valid canonical frame, for every padding length. -/
theorem referenceLanguage_embeds_finite (states : Nat) (hn : 0 < states)
    (f : Fin states → Bool → Bool → FiniteAction states) (padding : Nat) :
    let clock := tableWidth states f+padding
    referenceLanguage (canonical (bits clock (finiteProgram states f))) = true ↔
      ∃ branch, branch < 2^clock ∧ finiteRun f clock (finiteInitial hn 0 branch) = none := by
  dsimp only
  have hc := finiteProgram_lt_sentinel states f padding
  simpa [referenceLanguage,parse_canonical,bits_length,value_bits_of_lt _ _ hc] using
    reference_embeds_finite states hn f padding

/-- Any requested finite clock can be included by padding after the table;
this does not assert polynomial-time construction of the resulting frame. -/
theorem referenceLanguage_uniform_padding (states : Nat) (hn : 0 < states)
    (f : Fin states → Bool → Bool → FiniteAction states) (minimumClock : Nat) :
    ∃ clock, minimumClock ≤ clock ∧ finiteProgram states f < 2^clock ∧
      (referenceLanguage (canonical (bits clock (finiteProgram states f))) = true ↔
        ∃ branch, branch < 2^clock ∧ finiteRun f clock (finiteInitial hn 0 branch) = none) := by
  refine ⟨tableWidth states f+minimumClock,by omega,finiteProgram_lt_sentinel states f minimumClock,?_⟩
  exact referenceLanguage_embeds_finite states hn f minimumClock

/-- Unary table size is bounded by the number and maximum value of records. -/
theorem width_le_length_mul (records : List Nat) (bound : Nat)
    (h : ∀ a ∈ records, a ≤ bound) : width records ≤ records.length*(bound+1) := by
  induction records with
  | nil => simp [width]
  | cons a rest ih =>
    have ha : a ≤ bound := h a (by simp)
    have hr : ∀ b ∈ rest, b ≤ bound := by
      intro b hb; exact h b (by simp [hb])
    have hh := ih hr
    simp only [width,List.length_cons,Nat.succ_mul]
    omega

/-- A finite target has a uniformly bounded unary row value. -/
theorem lower_pack_bound (n : Nat) (a : FiniteAction n) : pack (lower a) ≤ 16*n+7 := by
  cases a with
  | mk write turn next =>
    cases write <;> cases turn <;> cases next with
    | none => simp [pack,lower,bitVal]
    | some q =>
      have hq := q.isLt
      simp [pack,lower,stateCode,bitVal]
      omega

/-- The concrete number of record bits is quadratic in the finite state
count. This is an output-size bound; it does not claim a paid table builder. -/
theorem tableWidth_bound (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n) :
    tableWidth n f ≤ (4*n)*(16*n+8) := by
  have hbound : ∀ a ∈ (tableRecords n f), a ≤ 16*n+7 := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp ha
    unfold finiteRows at hb
    obtain ⟨i,hi⟩ := List.mem_ofFn.mp hb
    subst b
    exact lower_pack_bound n _
  have hh := width_le_length_mul (tableRecords n f) (16*n+7) hbound
  simpa [tableWidth,tableRecords,finiteRows] using hh

/-- The exact finite-table reference frame has quadratic state-count size,
plus the caller's requested clock padding. -/
theorem finite_reference_frame_bound (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n)
    (minimumClock : Nat) :
    (canonical (bits (tableWidth n f+minimumClock) (finiteProgram n f))).length ≤
      2*((4*n)*(16*n+8)+minimumClock)+1 := by
  have hw := tableWidth_bound n f
  simp only [canonical_length,bits_length]
  omega

end Shared.PNP.Record285.UnaryReferenceTail
