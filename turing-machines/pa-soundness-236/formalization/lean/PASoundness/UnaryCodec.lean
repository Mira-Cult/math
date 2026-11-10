import PASoundness.Observer

/-!
The addressed unary-record wire format used by PA926. All parsers below are
structural finite functions. They recognize framing and ledger consistency;
they neither validate proof certificates nor evaluate a theory's formulas.
-/
namespace PASoundness.UnaryCodec

open PASoundness.Observer

abbrev Record := Address × Bool

def ValidAddress (a : Address) : Prop := 0 < a.rank ∧ a.coordinates.length = a.rank

instance (a : Address) : Decidable (ValidAddress a) :=
  inferInstanceAs (Decidable (0 < a.rank ∧ a.coordinates.length = a.rank))

def bitNat (b : Bool) : Nat := if b then 1 else 0

def unary : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: unary n

def encodeFields : List Nat → List Bool
  | [] => []
  | n :: ns => unary n ++ encodeFields ns

def frameFields (a : Address) (b : Bool) : List Nat :=
  a.rank :: a.certificate :: (a.coordinates ++ [bitNat b])

def encodeFrame (a : Address) (b : Bool) : List Bool := encodeFields (frameFields a b)

/-- A finite total parser for completed numeric fields. Exact field count and
Boolean value are checked, not inferred from a permissive default. -/
def decodeFields : List Nat → Option Record
  | n :: p :: tail =>
    if n = 0 then none else
      match tail.reverse with
      | [] => none
      | b :: revxs =>
        if revxs.length = n ∧ b ≤ 1 then
          some (⟨n, p, revxs.reverse⟩, b = 1)
        else none
  | _ => none

theorem decodeFields_frame (a : Address) (b : Bool) (ha : ValidAddress a) :
    decodeFields (frameFields a b) = some (a, b) := by
  rcases a with ⟨n, p, xs⟩
  rcases ha with ⟨hn, hlen⟩
  change 0 < n at hn
  change xs.length = n at hlen
  have hn0 : n ≠ 0 := by omega
  cases b <;> simp [frameFields, decodeFields, bitNat, hn0, hlen]

theorem decodeFields_valid {fields : List Nat} {r : Record}
    (h : decodeFields fields = some r) : ValidAddress r.1 := by
  cases fields with
  | nil => simp [decodeFields] at h
  | cons n rest =>
    cases rest with
    | nil => simp [decodeFields] at h
    | cons p tail =>
      simp only [decodeFields] at h
      split at h
      · cases h
      · rename_i hn
        cases htail : tail.reverse with
        | nil => simp [htail] at h
        | cons b revxs =>
          simp only [htail] at h
          split at h
          · rename_i hb
            have heq := Option.some.inj h
            subst r
            constructor
            · change 0 < n
              omega
            · simpa using hb.1
          · cases h

theorem frameFields_length (a : Address) (b : Bool) (ha : ValidAddress a) :
    (frameFields a b).length = a.rank + 3 := by
  simp [frameFields, ha.2]

inductive Cursor where
  | rank
  | body (remaining : Nat) (fields : List Nat)
  deriving DecidableEq, Repr

structure NumberDecoder where
  cursor : Cursor := .rank
  records : List Record := []
  failed : Bool := false
  deriving DecidableEq, Repr

def Compatible (records : List Record) (r : Record) : Prop :=
  ∀ old ∈ records, old.1 = r.1 → old.2 = r.2

instance (records : List Record) (r : Record) : Decidable (Compatible records r) :=
  inferInstanceAs (Decidable (∀ old ∈ records, old.1 = r.1 → old.2 = r.2))

def active (cursor : Cursor) (records : List Record) : NumberDecoder :=
  ⟨cursor, records, false⟩

def finish (records : List Record) (fields : List Nat) : NumberDecoder :=
  match decodeFields fields with
  | none => ⟨.rank, records, true⟩
  | some r => if Compatible records r then ⟨.rank, records ++ [r], false⟩
    else ⟨.rank, records, true⟩

/-- The first field fixes the exact number of subsequent fields. Unreachable
zero-count states are rejected as well, making the function total on every
input state. A fatal error is permanent. -/
def onNumber (d : NumberDecoder) (v : Nat) : NumberDecoder :=
  if d.failed then d else
    match d.cursor with
    | .rank => if v = 0 then ⟨.rank, d.records, true⟩
      else active (.body (v + 2) [v]) d.records
    | .body 0 _ => ⟨.rank, d.records, true⟩
    | .body 1 fields => finish d.records (fields ++ [v])
    | .body (r + 2) fields => active (.body (r + 1) (fields ++ [v])) d.records

def feedFields (d : NumberDecoder) (fields : List Nat) : NumberDecoder :=
  fields.foldl onNumber d

@[simp] theorem feedFields_nil (d : NumberDecoder) : feedFields d [] = d := rfl
@[simp] theorem feedFields_cons (d : NumberDecoder) (v : Nat) (vs : List Nat) :
    feedFields d (v :: vs) = feedFields (onNumber d v) vs := rfl

theorem feedFields_body (fields rest : List Nat) (records : List Record)
    (hne : rest ≠ []) :
    feedFields (active (.body rest.length fields) records) rest =
      finish records (fields ++ rest) := by
  induction rest generalizing fields with
  | nil => exact False.elim (hne rfl)
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons w ws =>
      rw [feedFields_cons]
      change feedFields (active (.body (w :: ws).length (fields ++ [v])) records)
        (w :: ws) = _
      rw [ih (fields ++ [v]) (by simp)]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem feedFields_frame (a : Address) (b : Bool) (records : List Record)
    (ha : ValidAddress a) :
    feedFields (active .rank records) (frameFields a b) =
      finish records (frameFields a b) := by
  have hn : a.rank ≠ 0 := by have := ha.1; omega
  have hlen : (a.certificate :: (a.coordinates ++ [bitNat b])).length = a.rank + 2 := by
    simp [ha.2]
  rw [frameFields, feedFields_cons]
  change feedFields (if a.rank = 0 then _ else _) _ = _
  rw [if_neg hn]
  rw [← hlen]
  exact feedFields_body [a.rank] _ records (by simp)

theorem finish_frame (a : Address) (b : Bool) (records : List Record)
    (ha : ValidAddress a) :
    finish records (frameFields a b) =
      if Compatible records (a, b) then active .rank (records ++ [(a, b)])
      else ⟨.rank, records, true⟩ := by
  simp only [finish, decodeFields_frame a b ha, active]

def RecordsValid (records : List Record) : Prop :=
  ∀ r ∈ records, ValidAddress r.1

theorem finish_records_valid (records : List Record) (fields : List Nat)
    (hv : RecordsValid records) : RecordsValid (finish records fields).records := by
  cases hd : decodeFields fields with
  | none => simpa [finish, hd] using hv
  | some r =>
    by_cases hc : Compatible records r
    · simp only [finish, hd, if_pos hc]
      intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | rfl
      · exact hv q hq
      · exact decodeFields_valid hd
    · simpa [finish, hd, hc] using hv

theorem onNumber_records_valid (d : NumberDecoder) (v : Nat)
    (hv : RecordsValid d.records) : RecordsValid (onNumber d v).records := by
  cases hb : d.failed with
  | true => simpa [onNumber, hb] using hv
  | false =>
    cases hc : d.cursor with
    | rank =>
      by_cases hz : v = 0 <;> simpa [onNumber, hb, hc, hz, active] using hv
    | body remaining fields =>
      cases remaining with
      | zero => simpa [onNumber, hb, hc] using hv
      | succ r =>
        cases r with
        | zero => simpa [onNumber, hb, hc] using
            finish_records_valid d.records (fields ++ [v]) hv
        | succ r => simpa [onNumber, hb, hc, active] using hv

structure Decoder where
  numbers : NumberDecoder := {}
  ones : Nat := 0
  deriving DecidableEq, Repr

/-- Consume one physical BIT0/BIT1 event. Silences have a separate entry point.
The running unary count and finite frame buffer are the whole parser state. -/
def feedBit (d : Decoder) (b : Bool) : Decoder :=
  if d.numbers.failed then d else
    if b then ⟨d.numbers, d.ones + 1⟩
    else ⟨onNumber d.numbers d.ones, 0⟩

def feedBits (d : Decoder) (bits : List Bool) : Decoder := bits.foldl feedBit d

theorem feedBits_append (d : Decoder) (left right : List Bool) :
    feedBits d (left ++ right) = feedBits (feedBits d left) right := by
  exact List.foldl_append

theorem feedBits_failed (d : Decoder) (bits : List Bool) (hbad : d.numbers.failed = true) :
    feedBits d bits = d := by
  induction bits with
  | nil => rfl
  | cons b bs ih =>
    change feedBits (feedBit d b) bs = d
    simp only [feedBit, hbad, if_true]
    exact ih

theorem feedBits_unary_active (numbers : NumberDecoder) (k v : Nat)
    (hgood : numbers.failed = false) :
    feedBits ⟨numbers, k⟩ (unary v) = ⟨onNumber numbers (k + v), 0⟩ := by
  induction v generalizing k with
  | zero => simp [unary, feedBits, feedBit, hgood]
  | succ v ih =>
    change feedBits (feedBit ⟨numbers, k⟩ true) (unary v) = _
    simp only [feedBit, hgood, Bool.false_eq_true, if_false, if_true]
    rw [ih]
    congr 2
    omega

theorem feedBits_unary (numbers : NumberDecoder) (v : Nat) :
    feedBits ⟨numbers, 0⟩ (unary v) = ⟨onNumber numbers v, 0⟩ := by
  cases hbad : numbers.failed with
  | false => simpa using feedBits_unary_active numbers 0 v hbad
  | true =>
    rw [feedBits_failed _ _ hbad]
    simp [onNumber, hbad]

theorem feedBits_encodedFields (numbers : NumberDecoder) (fields : List Nat) :
    feedBits ⟨numbers, 0⟩ (encodeFields fields) = ⟨feedFields numbers fields, 0⟩ := by
  induction fields generalizing numbers with
  | nil => rfl
  | cons v vs ih =>
    rw [encodeFields, feedBits_append, feedBits_unary, ih, feedFields_cons]

/-- Exact valid-frame roundtrip, including the finite consistency check against
every earlier receipt. The proof is independent of the certificate's validity
in the producer's theory. -/
theorem decode_encodeFrame (a : Address) (b : Bool) (records : List Record)
    (ha : ValidAddress a) :
    feedBits ⟨active .rank records, 0⟩ (encodeFrame a b) =
      ⟨if Compatible records (a, b) then active .rank (records ++ [(a, b)])
        else ⟨.rank, records, true⟩, 0⟩ := by
  rw [encodeFrame, feedBits_encodedFields, feedFields_frame a b records ha,
    finish_frame a b records ha]

theorem feedBit_records_valid (d : Decoder) (b : Bool)
    (hv : RecordsValid d.numbers.records) :
    RecordsValid (feedBit d b).numbers.records := by
  unfold feedBit
  split
  · exact hv
  · split
    · exact hv
    · exact onNumber_records_valid _ _ hv

theorem feedBits_records_valid (d : Decoder) (bits : List Bool)
    (hv : RecordsValid d.numbers.records) :
    RecordsValid (feedBits d bits).numbers.records := by
  induction bits generalizing d with
  | nil => exact hv
  | cons b bs ih => exact ih (feedBit d b) (feedBit_records_valid d b hv)

/-- A transparent finite-stream contract. Compatibility is checked against
earlier receipts, so equal duplicate records remain permitted. -/
def CoherentAfter : List Record → List Record → Prop
  | _, [] => True
  | before, r :: rest => ValidAddress r.1 ∧ Compatible before r ∧
      CoherentAfter (before ++ [r]) rest

def encodeRecords : List Record → List Bool
  | [] => []
  | r :: rs => encodeFrame r.1 r.2 ++ encodeRecords rs

theorem decode_encodeRecords (before records : List Record)
    (h : CoherentAfter before records) :
    feedBits ⟨active .rank before, 0⟩ (encodeRecords records) =
      ⟨active .rank (before ++ records), 0⟩ := by
  induction records generalizing before with
  | nil => simp [encodeRecords, feedBits]
  | cons r rs ih =>
    rcases h with ⟨hvalid, hcompatible, hrest⟩
    rw [encodeRecords, feedBits_append, decode_encodeFrame r.1 r.2 before hvalid]
    simp only [Prod.mk.eta, if_pos hcompatible]
    rw [ih (before ++ [r]) hrest]
    simp [List.append_assoc]

def feedEvent (d : Decoder) : Option Bool → Decoder
  | none => d
  | some b => feedBit d b

def feedEvents (d : Decoder) (events : List (Option Bool)) : Decoder :=
  events.foldl feedEvent d

/-- Exact finite timing invariance. The equality requires equality of the
ordered bit word; inserted/dropped/reordered bits are not covered. -/
theorem feedEvents_erase_silence (d : Decoder) (events : List (Option Bool)) :
    feedEvents d events = feedBits d (events.filterMap id) := by
  induction events generalizing d with
  | nil => rfl
  | cons event rest ih =>
    cases event with
    | none => simpa [feedEvents, feedEvent, feedBits] using ih d
    | some b => simpa [feedEvents, feedEvent, feedBits] using ih (feedBit d b)

theorem timing_invariance (d : Decoder) (left right : List (Option Bool))
    (h : left.filterMap id = right.filterMap id) :
    feedEvents d left = feedEvents d right := by
  rw [feedEvents_erase_silence, feedEvents_erase_silence, h]

theorem feedEvents_failed (d : Decoder) (events : List (Option Bool))
    (hbad : d.numbers.failed = true) : feedEvents d events = d := by
  rw [feedEvents_erase_silence]
  exact feedBits_failed d _ hbad

def decoderRun (trace : Nat → Option Bool) : Nat → Decoder
  | 0 => {}
  | t + 1 => feedEvent (decoderRun trace t) (trace t)

/-- A decoded event is recognized at precisely the physical transition that
appends one completed receipt. Equal duplicates are distinct events. -/
def decodedEvents (trace : Nat → Option Bool) : EventStructure where
  profile := .legacy
  out := fun b t a =>
    (decoderRun trace (t + 1)).numbers.records =
      (decoderRun trace t).numbers.records ++ [(a, b)]
  error := fun t => (decoderRun trace t).numbers.failed = true

instance (trace : Nat → Option Bool) (b : Bool) (t : Nat) (a : Address) :
    Decidable ((decodedEvents trace).out b t a) :=
  inferInstanceAs (Decidable ((decoderRun trace (t + 1)).numbers.records =
    (decoderRun trace t).numbers.records ++ [(a, b)]))

instance (trace : Nat → Option Bool) (t : Nat) :
    Decidable ((decodedEvents trace).error t) :=
  inferInstanceAs (Decidable ((decoderRun trace t).numbers.failed = true))

theorem decoderRun_records_valid (trace : Nat → Option Bool) (t : Nat) :
    RecordsValid (decoderRun trace t).numbers.records := by
  induction t with
  | zero => intro r hr; cases hr
  | succ t ih =>
    change RecordsValid (feedEvent (decoderRun trace t) (trace t)).numbers.records
    cases he : trace t with
    | none => simpa [he, feedEvent] using ih
    | some b => simpa [he, feedEvent] using feedBit_records_valid _ b ih

/-- The explicit observer address guard follows from online decoder correctness
on every physical trace, with no hypothesis about the producer or PA. -/
theorem decodedEvents_wellAddressed (trace : Nat → Option Bool) :
    WellAddressed (decodedEvents trace) := by
  intro b t a hout
  have hmem : (a, b) ∈ (decoderRun trace (t + 1)).numbers.records := by
    rw [hout]
    simp
  have ha := decoderRun_records_valid trace (t + 1) (a, b) hmem
  exact ⟨ha.2, fun _ => ha.1⟩

def RecordStep (before after : List Record) : Prop :=
  after = before ∨ ∃ r, after = before ++ [r]

theorem RecordStep.mem_mono {before after : List Record} (h : RecordStep before after)
    (r : Record) (hr : r ∈ before) : r ∈ after := by
  rcases h with h | ⟨q, h⟩
  · simpa [h] using hr
  · rw [h]
    exact List.mem_append_left _ hr

theorem finish_recordStep (records : List Record) (fields : List Nat) :
    RecordStep records (finish records fields).records := by
  cases hd : decodeFields fields with
  | none => exact Or.inl (by simp [finish, hd])
  | some r =>
    by_cases hc : Compatible records r
    · exact Or.inr ⟨r, by simp [finish, hd, hc]⟩
    · exact Or.inl (by simp [finish, hd, hc])

theorem onNumber_recordStep (d : NumberDecoder) (v : Nat) :
    RecordStep d.records (onNumber d v).records := by
  cases hb : d.failed with
  | true => exact Or.inl (by simp [onNumber, hb])
  | false =>
    cases hc : d.cursor with
    | rank =>
      by_cases hz : v = 0 <;> exact Or.inl (by simp [onNumber, hb, hc, hz, active])
    | body remaining fields =>
      cases remaining with
      | zero => exact Or.inl (by simp [onNumber, hb, hc])
      | succ r =>
        cases r with
        | zero => simpa [onNumber, hb, hc] using finish_recordStep d.records (fields ++ [v])
        | succ r => exact Or.inl (by simp [onNumber, hb, hc, active])

theorem feedBit_recordStep (d : Decoder) (b : Bool) :
    RecordStep d.numbers.records (feedBit d b).numbers.records := by
  unfold feedBit
  split
  · exact Or.inl rfl
  · split
    · exact Or.inl rfl
    · exact onNumber_recordStep _ _

theorem feedEvent_recordStep (d : Decoder) (event : Option Bool) :
    RecordStep d.numbers.records (feedEvent d event).numbers.records := by
  cases event with
  | none => exact Or.inl rfl
  | some b => exact feedBit_recordStep d b

theorem feedBits_records_mono (d : Decoder) (bits : List Bool) (r : Record)
    (hr : r ∈ d.numbers.records) : r ∈ (feedBits d bits).numbers.records := by
  induction bits generalizing d with
  | nil => exact hr
  | cons b bs ih => exact ih (feedBit d b) ((feedBit_recordStep d b).mem_mono r hr)

theorem decoderRun_records_mono (trace : Nat → Option Bool) {t u : Nat} (h : t ≤ u)
    (r : Record) (hr : r ∈ (decoderRun trace t).numbers.records) :
    r ∈ (decoderRun trace u).numbers.records := by
  induction h with
  | refl => exact hr
  | @step u _ ih => exact (feedEvent_recordStep (decoderRun trace u) (trace u)).mem_mono r ih

/-- Every recorded receipt originated at one actual completed-frame event;
it is not synthesized by the semantic observer from absent output. -/
theorem decoderRun_record_origin (trace : Nat → Option Bool) (n : Nat) (a : Address) (b : Bool)
    (h : (a, b) ∈ (decoderRun trace n).numbers.records) :
    ∃ t, t < n ∧ (decodedEvents trace).out b t a := by
  induction n with
  | zero => cases h
  | succ n ih =>
    have hs := feedEvent_recordStep (decoderRun trace n) (trace n)
    change RecordStep (decoderRun trace n).numbers.records
      (decoderRun trace (n + 1)).numbers.records at hs
    rcases hs with hs | ⟨r, hs⟩
    · rw [hs] at h
      obtain ⟨t, ht, hout⟩ := ih h
      exact ⟨t, by omega, hout⟩
    · rw [hs] at h
      simp only [List.mem_append, List.mem_singleton] at h
      rcases h with h | h
      · obtain ⟨t, ht, hout⟩ := ih h
        exact ⟨t, by omega, hout⟩
      · refine ⟨n, by omega, ?_⟩
        change (decoderRun trace (n + 1)).numbers.records =
          (decoderRun trace n).numbers.records ++ [(a, b)]
        rw [h]
        exact hs

theorem decodedEvents_emitted_iff_record (trace : Nat → Option Bool) (b : Bool) (a : Address) :
    Emitted (decodedEvents trace) b a ↔
      ∃ n, (a, b) ∈ (decoderRun trace n).numbers.records := by
  constructor
  · rintro ⟨t, hout⟩
    refine ⟨t + 1, ?_⟩
    rw [hout]
    simp
  · rintro ⟨n, hr⟩
    obtain ⟨t, _, hout⟩ := decoderRun_record_origin trace n a b hr
    exact ⟨t, hout⟩

def RecordsConsistent (records : List Record) : Prop :=
  ∀ x ∈ records, ∀ y ∈ records, x.1 = y.1 → x.2 = y.2

theorem recordsConsistent_append {records : List Record} {r : Record}
    (hc : RecordsConsistent records) (hr : Compatible records r) :
    RecordsConsistent (records ++ [r]) := by
  intro x hx y hy hxy
  simp only [List.mem_append, List.mem_singleton] at hx hy
  rcases hx with hx | rfl
  · rcases hy with hy | rfl
    · exact hc x hx y hy hxy
    · exact hr x hx hxy
  · rcases hy with hy | rfl
    · exact (hr y hy hxy.symm).symm
    · rfl

theorem finish_records_consistent (records : List Record) (fields : List Nat)
    (hv : RecordsConsistent records) : RecordsConsistent (finish records fields).records := by
  cases hd : decodeFields fields with
  | none => simpa [finish, hd] using hv
  | some r =>
    by_cases hc : Compatible records r
    · simpa [finish, hd, hc] using recordsConsistent_append hv hc
    · simpa [finish, hd, hc] using hv

theorem onNumber_records_consistent (d : NumberDecoder) (v : Nat)
    (hv : RecordsConsistent d.records) : RecordsConsistent (onNumber d v).records := by
  cases hb : d.failed with
  | true => simpa [onNumber, hb] using hv
  | false =>
    cases hc : d.cursor with
    | rank =>
      by_cases hz : v = 0 <;> simpa [onNumber, hb, hc, hz, active] using hv
    | body remaining fields =>
      cases remaining with
      | zero => simpa [onNumber, hb, hc] using hv
      | succ r =>
        cases r with
        | zero => simpa [onNumber, hb, hc] using
            finish_records_consistent d.records (fields ++ [v]) hv
        | succ r => simpa [onNumber, hb, hc, active] using hv

theorem feedBit_records_consistent (d : Decoder) (b : Bool)
    (hv : RecordsConsistent d.numbers.records) :
    RecordsConsistent (feedBit d b).numbers.records := by
  unfold feedBit
  split
  · exact hv
  · split
    · exact hv
    · exact onNumber_records_consistent _ _ hv

theorem decoderRun_records_consistent (trace : Nat → Option Bool) (t : Nat) :
    RecordsConsistent (decoderRun trace t).numbers.records := by
  induction t with
  | zero => intro r hr; cases hr
  | succ t ih =>
    change RecordsConsistent (feedEvent (decoderRun trace t) (trace t)).numbers.records
    cases he : trace t with
    | none => simpa [he, feedEvent] using ih
    | some b => simpa [he, feedEvent] using feedBit_records_consistent _ b ih

theorem decodedEvents_conflictFree (trace : Nat → Option Bool) (a : Address) :
    ¬ (Emitted (decodedEvents trace) false a ∧ Emitted (decodedEvents trace) true a) := by
  rintro ⟨hf, ht⟩
  obtain ⟨m, hm⟩ := (decodedEvents_emitted_iff_record trace false a).mp hf
  obtain ⟨n, hn⟩ := (decodedEvents_emitted_iff_record trace true a).mp ht
  have hmf := decoderRun_records_mono trace (Nat.le_max_left m n) _ hm
  have hnt := decoderRun_records_mono trace (Nat.le_max_right m n) _ hn
  have hbad := decoderRun_records_consistent trace (max m n) _ hmf _ hnt rfl
  cases hbad

namespace Fixtures

def address : Address := ⟨1, 0, [0]⟩
theorem address_valid : ValidAddress address := by decide

theorem zero_frame :
    feedBits {} (encodeFrame address false) =
      ⟨active .rank [(address, false)], 0⟩ := by decide

theorem duplicate_zero_frame :
    feedBits {} (encodeFrame address false ++ encodeFrame address false) =
      ⟨active .rank [(address, false), (address, false)], 0⟩ := by decide

theorem conflicting_frames :
    (feedBits {} (encodeFrame address false ++ encodeFrame address true)).numbers.failed = true :=
  by decide

theorem rank_zero_rejected : (feedBits {} [false]).numbers.failed = true := by decide

theorem nonboolean_value_rejected :
    (feedBits {} (encodeFields [1, 0, 0, 2])).numbers.failed = true := by decide

theorem wrong_field_count_rejected : decodeFields [2, 0, 0, 0] = none := by decide

theorem empty_output_has_no_receipts : (feedBits {} []).numbers.records = [] := rfl

theorem missing_final_delimiter_is_incomplete :
    (feedBits {} ((encodeFrame address false).dropLast)).numbers.records = [] := by decide

theorem all_proper_prefixes_are_incomplete :
    ∀ k : Fin (encodeFrame address false).length,
      (feedBits {} ((encodeFrame address false).take k.val)).numbers.records = [] := by decide

end Fixtures

end PASoundness.UnaryCodec
