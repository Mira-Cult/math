import PASoundness.M236Observer

/-!
A finite parser invariant for the historical legal-frame progress condition.
No producer or PA soundness assumption is used.
-/
namespace PASoundness.M236FrameSegmentation

open PASoundness PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer

/-- Successful finite field decoding recovers exactly the supplied fields.
Proof contributed by Codex subagent `/root/frame_binding/inverse`. -/
theorem decodeFields_inverse {fields : List Nat} {r : Record}
    (h : decodeFields fields = some r) : fields = frameFields r.1 r.2 := by
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
            have htail' : tail = revxs.reverse ++ [b] := by
              have := congrArg List.reverse htail
              simpa using this
            have hbit : bitNat (decide (b = 1)) = b := by
              have hb' : b ≤ 1 := hb.2
              have hcases : b = 0 ∨ b = 1 := by omega
              rcases hcases with rfl | rfl <;> rfl
            simp [frameFields, htail', hbit]
          · cases h

/-- The fields accumulated since the last frame boundary. -/
def pendingFields (d : Decoder) : List Nat :=
  match d.numbers.cursor with
  | .rank => []
  | .body _ fields => fields

/-- The complete-ledger encoding followed by the partial frame and partial
unary run. Its equality with the exact consumed word is proved below. -/
def parseForm (d : Decoder) : List Bool :=
  encodeRecords d.numbers.records ++ encodeFields (pendingFields d) ++ List.replicate d.ones true

theorem unary_eq_replicate (n : Nat) : unary n = List.replicate n true ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih => simp [unary, List.replicate_succ, ih]

theorem encodeFields_append (xs ys : List Nat) :
    encodeFields (xs ++ ys) = encodeFields xs ++ encodeFields ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeFields, ih, List.append_assoc]

theorem encodeRecords_append (xs ys : List Record) :
    encodeRecords (xs ++ ys) = encodeRecords xs ++ encodeRecords ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encodeRecords, ih, List.append_assoc]

theorem parseForm_true (d : Decoder) (hgood : d.numbers.failed = false) :
    parseForm d ++ [true] = parseForm (feedBit d true) := by
  simp [parseForm, pendingFields, feedBit, hgood, List.replicate_succ', List.append_assoc]

/-- The terminating zero of a numeric field appends one unary field to the
stored fields, except when it completes a successfully decoded frame. -/
theorem parseForm_false (d : Decoder) (hgood : d.numbers.failed = false)
    (hnext : (feedBit d false).numbers.failed = false) :
    parseForm d ++ [false] = parseForm (feedBit d false) := by
  cases hc : d.numbers.cursor with
  | rank =>
    by_cases hz : d.ones = 0
    · simp [feedBit, hgood, onNumber, hc, hz] at hnext
    · simp [parseForm, pendingFields, feedBit, hgood, onNumber, hc, hz,
        active, encodeFields, unary_eq_replicate, List.append_assoc]
  | body remaining fields =>
    cases remaining with
    | zero => simp [feedBit, hgood, onNumber, hc] at hnext
    | succ n =>
      cases n with
      | zero =>
        cases hd : decodeFields (fields ++ [d.ones]) with
        | none => simp [feedBit, hgood, onNumber, hc, finish, hd] at hnext
        | some r =>
          by_cases hcomp : Compatible d.numbers.records r
          · have hi := decodeFields_inverse hd
            simp [parseForm, pendingFields, feedBit, hgood, onNumber, hc, finish,
              hd, hcomp, encodeRecords_append, encodeRecords, encodeFrame,
              ← hi, encodeFields_append, encodeFields, unary_eq_replicate,
              List.append_assoc]
          · simp [feedBit, hgood, onNumber, hc, finish, hd, hcomp] at hnext
      | succ n =>
        simp [parseForm, pendingFields, feedBit, hgood, onNumber, hc, active,
          encodeFields_append, encodeFields, unary_eq_replicate, List.append_assoc]

theorem parseForm_step (d : Decoder) (b : Bool) (hgood : d.numbers.failed = false)
    (hnext : (feedBit d b).numbers.failed = false) :
    parseForm d ++ [b] = parseForm (feedBit d b) := by
  cases b with
  | false => exact parseForm_false d hgood hnext
  | true => exact parseForm_true d hgood

/-- Every successful finite parse retains the exact consumed word as its
completed frames, incomplete numeric fields, and unfinished unary run. -/
theorem parseForm_feedBits (d : Decoder) (bits : List Bool)
    (hgood : d.numbers.failed = false)
    (hfinal : (feedBits d bits).numbers.failed = false) :
    parseForm d ++ bits = parseForm (feedBits d bits) := by
  induction bits generalizing d with
  | nil => simp [feedBits]
  | cons b bits ih =>
    have hstep : (feedBit d b).numbers.failed = false := by
      cases hf : (feedBit d b).numbers.failed with
      | false => rfl
      | true =>
        have hs := feedBits_failed (feedBit d b) bits hf
        change (feedBits (feedBit d b) bits).numbers.failed = false at hfinal
        rw [hs, hf] at hfinal
        cases hfinal
    have hnext := ih (feedBit d b) hstep hfinal
    rw [← parseForm_step d b hgood hstep] at hnext
    simpa [feedBits, List.append_assoc] using hnext

/-- If a finite prefix is good and ends at a clean boundary, its entire bit
word is precisely the encoding of the completed records it contains. -/
theorem good_boundary_segmentation (bits : List Bool)
    (hgood : (feedBits {} bits).numbers.failed = false)
    (hrank : (feedBits {} bits).numbers.cursor = .rank)
    (hones : (feedBits {} bits).ones = 0) :
    bits = encodeRecords (feedBits {} bits).numbers.records ∧
      RecordsValid (feedBits {} bits).numbers.records := by
  have h := parseForm_feedBits ({} : Decoder) bits rfl hgood
  constructor
  · simpa [parseForm, pendingFields, hrank, hones, encodeRecords, encodeFields] using h
  · apply feedBits_records_valid
    intro r hr
    cases hr

/-- At every position in a finite sequence of valid encoded frames there is a
specific frame whose half-open bit interval contains that position. -/
theorem encodedRecords_position (records : List Record) (k : Nat)
    (hv : RecordsValid records) (hk : k < (encodeRecords records).length) :
    ∃ before r after, records = before ++ r :: after ∧ ValidAddress r.1 ∧
      (encodeRecords before).length ≤ k ∧
      k < (encodeRecords before).length + (encodeFrame r.1 r.2).length := by
  induction records generalizing k with
  | nil => simp [encodeRecords] at hk
  | cons r rs ih =>
    have hr : ValidAddress r.1 := hv r (by simp)
    by_cases hfirst : k < (encodeFrame r.1 r.2).length
    · refine ⟨[], r, rs, rfl, hr, ?_, ?_⟩
      · simp [encodeRecords]
      · simpa [encodeRecords] using hfirst
    · have hvrs : RecordsValid rs := by
        intro q hq
        exact hv q (by simp [hq])
      have htail : k - (encodeFrame r.1 r.2).length < (encodeRecords rs).length := by
        simp only [encodeRecords, List.length_append] at hk
        omega
      obtain ⟨before, q, after, hrec, hq, hlo, hhi⟩ :=
        ih (k - (encodeFrame r.1 r.2).length) hvrs htail
      refine ⟨r :: before, q, after, ?_, hq, ?_, ?_⟩
      · simp [hrec]
      · simp only [encodeRecords, List.length_append]
        omega
      · simp only [encodeRecords, List.length_append]
        omega

/-- Replaying a list of legal frame encodings from a clean active decoder
ends at a clean boundary, even if a conflicting record makes it fail: the
failed decoder remains at that boundary. -/
theorem encodedRecords_boundary (before records : List Record)
    (hv : RecordsValid records) :
    (feedBits ⟨active .rank before, 0⟩ (encodeRecords records)).numbers.cursor = .rank ∧
      (feedBits ⟨active .rank before, 0⟩ (encodeRecords records)).ones = 0 := by
  induction records generalizing before with
  | nil => simp [encodeRecords, feedBits, active]
  | cons r rs ih =>
    have hr : ValidAddress r.1 := hv r (by simp)
    have hvr : RecordsValid rs := by
      intro q hq
      exact hv q (by simp [hq])
    rw [encodeRecords, feedBits_append, decode_encodeFrame r.1 r.2 before hr]
    by_cases hc : Compatible before (r.1, r.2)
    · simp only [hc, if_true, Prod.mk.eta]
      exact ih (before ++ [r]) hvr
    · simp only [hc, if_false]
      rw [feedBits_failed _ _ rfl]
      exact ⟨rfl, rfl⟩

/-- Every already-output bit eventually lies inside a specific legal frame in
an exact complete-frame segmentation of a later output prefix. Positions are
zero-based in the concatenated nonsilent output word; the half-open bounds
identify the containing frame. -/
def EveryBitInLegalFrame {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ t k, k < (M.prefixWord t).length →
    ∃ u before r after, t ≤ u ∧
      M.prefixWord u = encodeRecords (before ++ r :: after) ∧
      RecordsValid (before ++ r :: after) ∧
      (encodeRecords before).length ≤ k ∧
      k < (encodeRecords before).length + (encodeFrame r.1 r.2).length

/-- On a parser-error-free output, the explicit `FrameProgress` guard is
equivalent to the manuscript's per-output-bit completion condition, stated
with an exact segmentation and a containing legal frame. This holds for word
systems as well as physical singleton-bit systems. -/
theorem frameProgress_iff_everyBitInLegalFrame {C : Type} (M : WordEventSystem C Bool)
    (hgood : ∀ t, (feedBits {} (M.prefixWord t)).numbers.failed = false) :
    FrameProgress M ↔ EveryBitInLegalFrame M := by
  constructor
  · intro hp t k hk
    obtain ⟨u, htu, hr, ho⟩ := hp t
    obtain ⟨hsegment, hvalid⟩ := good_boundary_segmentation (M.prefixWord u) (hgood u) hr ho
    obtain ⟨tail, htail⟩ := M.prefix_extends htu
    have hk' : k < (encodeRecords (feedBits {} (M.prefixWord u)).numbers.records).length := by
      rw [← hsegment, htail, List.length_append]
      omega
    obtain ⟨before, r, after, hrecords, _, hlo, hhi⟩ :=
      encodedRecords_position _ k hvalid hk'
    refine ⟨u, before, r, after, htu, ?_, ?_, hlo, hhi⟩
    · simpa [hrecords] using hsegment
    · simpa [hrecords] using hvalid
  · intro hp t
    by_cases he : M.prefixWord t = []
    · refine ⟨t, Nat.le_refl _, ?_, ?_⟩ <;> rw [he] <;> rfl
    · have hlen : 0 < (M.prefixWord t).length := by
        cases hw : M.prefixWord t with
        | nil => exact False.elim (he hw)
        | cons b bs => simp
      obtain ⟨u, before, r, after, htu, hword, hv, _, _⟩ := hp t 0 hlen
      have hb := encodedRecords_boundary [] (before ++ r :: after) hv
      refine ⟨u, htu, ?_, ?_⟩
      · rw [hword]
        exact hb.1
      · rw [hword]
        exact hb.2

/-- A physical bit stream attains each intermediate output length at a
transition boundary; silent transitions may repeat the same length. -/
theorem physical_reaches_length_between {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) {t u n : Nat} (htu : t ≤ u)
    (hlo : (M.prefixWord t).length ≤ n) (hhi : n ≤ (M.prefixWord u).length) :
    ∃ v, t ≤ v ∧ v ≤ u ∧ (M.prefixWord v).length = n := by
  induction u generalizing n with
  | zero =>
    have : t = 0 := by omega
    subst t
    refine ⟨0, by omega, by omega, ?_⟩
    omega
  | succ u ih =>
    by_cases htu' : t ≤ u
    · by_cases hbefore : n ≤ (M.prefixWord u).length
      · obtain ⟨v, htv, hvu, hv⟩ := ih htu' hlo hbefore
        exact ⟨v, htv, by omega, hv⟩
      · have hstep := hphys u
        have hlen : (M.prefixWord (u+1)).length =
            (M.prefixWord u).length + ((M.step (M.run u)).2).length := by
          rw [WordEventSystem.prefix_succ, List.length_append]
        refine ⟨u+1, by omega, by omega, ?_⟩
        omega
    · have ht : t = u+1 := by omega
      subst t
      refine ⟨u+1, by omega, by omega, ?_⟩
      omega

/-- A prefix of the output word that ends at an achievable physical output
length is itself the complete output prefix at the corresponding time. -/
theorem physical_reaches_output_prefix {C : Type} (M : WordEventSystem C Bool)
    (hphys : M.PhysicalBits) {t u : Nat} {w suffix : List Bool} (htu : t ≤ u)
    (hlo : (M.prefixWord t).length ≤ w.length)
    (hword : M.prefixWord u = w ++ suffix) :
    ∃ v, t ≤ v ∧ v ≤ u ∧ M.prefixWord v = w := by
  have hhi : w.length ≤ (M.prefixWord u).length := by rw [hword, List.length_append]; omega
  obtain ⟨v, htv, hvu, hvlen⟩ := physical_reaches_length_between M hphys htu hlo hhi
  obtain ⟨tail, htail⟩ := M.prefix_extends hvu
  have hv : (M.prefixWord u).take w.length = M.prefixWord v := by
    rw [htail, ← hvlen]
    simp
  have hw : (M.prefixWord u).take w.length = w := by
    rw [hword]
    simp
  exact ⟨v, htv, hvu, hv.symm.trans hw⟩

/-- Historical bit-completion formulation: each emitted bit belongs to a
complete legal frame in some later output prefix. Output following that frame
is allowed to be an arbitrary (possibly incomplete) suffix. Earlier frames and
the containing frame must be legal. -/
def EveryBitInCompletedFrame {C : Type} (M : WordEventSystem C Bool) : Prop :=
  ∀ t k, k < (M.prefixWord t).length →
    ∃ u before r suffix, t ≤ u ∧
      M.prefixWord u = encodeRecords before ++ encodeFrame r.1 r.2 ++ suffix ∧
      RecordsValid (before ++ [r]) ∧
      (encodeRecords before).length ≤ k ∧
      k < (encodeRecords before).length + (encodeFrame r.1 r.2).length

/-- For physical single-bit output, the actual frame-progress guard is
equivalent to the independent condition that every emitted bit eventually
belongs to a completed legal frame, even when later output has started another
frame. The no-error hypothesis is used in the forward direction. -/
theorem physical_frameProgress_iff_everyBitInCompletedFrame {C : Type}
    (M : WordEventSystem C Bool) (hphys : M.PhysicalBits)
    (hgood : ∀ t, (feedBits {} (M.prefixWord t)).numbers.failed = false) :
    FrameProgress M ↔ EveryBitInCompletedFrame M := by
  constructor
  · intro hp t k hk
    obtain ⟨u, before, r, after, htu, hword, hvalid, hlo, hhi⟩ :=
      (frameProgress_iff_everyBitInLegalFrame M hgood).mp hp t k hk
    refine ⟨u, before, r, encodeRecords after, htu, ?_, ?_, hlo, hhi⟩
    · simpa [encodeRecords_append, encodeRecords, List.append_assoc] using hword
    · intro q hq
      apply hvalid q
      simp only [List.mem_append, List.mem_singleton] at hq ⊢
      rcases hq with hq | rfl
      · exact Or.inl hq
      · exact Or.inr (by simp)
  · intro hp t
    by_cases hempty : M.prefixWord t = []
    · refine ⟨t, Nat.le_refl _, ?_, ?_⟩ <;> rw [hempty] <;> rfl
    · have hpos : 0 < (M.prefixWord t).length := by
        cases hw : M.prefixWord t with
        | nil => exact False.elim (hempty hw)
        | cons b bs => simp
      obtain ⟨u, before, r, suffix, htu, hword, hvalid, hlo, hhi⟩ :=
        hp t ((M.prefixWord t).length - 1) (by omega)
      have hlen : (M.prefixWord t).length ≤
          (encodeRecords before ++ encodeFrame r.1 r.2).length := by
        simp only [List.length_append]
        omega
      obtain ⟨v, htv, _, hv⟩ := physical_reaches_output_prefix M hphys htu hlen hword
      have hb := encodedRecords_boundary [] (before ++ [r]) hvalid
      refine ⟨v, htv, ?_, ?_⟩
      · rw [hv]
        simpa [encodeRecords_append, encodeRecords, active] using hb.1
      · rw [hv]
        simpa [encodeRecords_append, encodeRecords, active] using hb.2

end PASoundness.M236FrameSegmentation
