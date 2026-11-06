import Shared.Beeping.NPcoNP.Source284Parser
import Shared.Codes.BitNumeralCompare

/-! Exact input coverage and ignored-suffix behavior of the pinned 284 source
normalizer. The candidate phase still receives the original whole natural;
these lemmas concern only the parser result and do not erase its suffix. -/
namespace Shared.Beeping.NPcoNP.Source284Parser

/-- Write marker/payload pairs low first, followed by the zero marker and
all remaining higher input bits represented by `suffix`. -/
def encodeFrame : List Bool → Nat → Nat
  | [], suffix => 2 * suffix
  | b :: bs, suffix => 1 + 2 * (if b then 1 else 0) + 4 * encodeFrame bs suffix

/-- On the terminating zero marker, the source's final halving returns
exactly the otherwise ignored suffix. -/
theorem final_scan_suffix (suffix : Nat) : encodeFrame [] suffix / 2 = suffix := by
  simp [encodeFrame]

/-- Append the payloads to the high end of the sentinel as the source does. -/
def payloadFold (e : Nat) : List Bool → Nat
  | [] => e
  | b :: bs => payloadFold (2 * e + (if b then 1 else 0)) bs

theorem bitValue_append (xs ys : List Bool) :
    Shared.Codes.BitNumeralCompare.value (xs ++ ys) =
      Shared.Codes.BitNumeralCompare.value xs +
        2 ^ xs.length * Shared.Codes.BitNumeralCompare.value ys := by
  induction xs with
  | nil => simp [Shared.Codes.BitNumeralCompare.value]
  | cons b bs ih =>
    simp only [List.cons_append, Shared.Codes.BitNumeralCompare.value, ih,
      List.length_cons, pow_succ]
    ring

/-- Payloads are appended most-significant first to the initial sentinel;
`value` itself uses the shared low-endian bitstring convention. -/
theorem payloadFold_value (bits : List Bool) (e : Nat) :
    payloadFold e bits = 2 ^ bits.length * e +
      Shared.Codes.BitNumeralCompare.value bits.reverse := by
  induction bits generalizing e with
  | nil => simp [payloadFold, Shared.Codes.BitNumeralCompare.value]
  | cons b bs ih =>
    simp only [payloadFold, ih, List.length_cons, List.reverse_cons,
      bitValue_append, Shared.Codes.BitNumeralCompare.value, pow_succ]
    cases b <;> simp <;> ring

theorem run_encodeFrame (bits : List Bool) (suffix n e : Nat) :
    run (encodeFrame bits suffix) n e = (n + bits.length, payloadFold e bits) := by
  induction bits generalizing n e with
  | nil =>
    rw [run_even _ _ _ (by simp [encodeFrame])]
    simp [payloadFold]
  | cons b bs ih =>
    have ho : encodeFrame (b :: bs) suffix % 2 = 1 := by
      cases b <;> simp [encodeFrame] <;> omega
    rw [run_odd _ _ _ ho]
    have hd : encodeFrame (b :: bs) suffix / 4 = encodeFrame bs suffix := by
      cases b <;> simp [encodeFrame] <;> omega
    have hp : (encodeFrame (b :: bs) suffix / 2) % 2 = (if b then 1 else 0) := by
      cases b <;> simp [encodeFrame] <;> omega
    rw [hd, hp, ih]
    simp [payloadFold, Nat.add_comm, Nat.add_left_comm]

/-- The finite prefix determines both results for every suffix, including
arbitrarily long suffixes after the first zero marker. -/
theorem parse_encodeFrame (bits : List Bool) (suffix : Nat) :
    parse (encodeFrame bits suffix) = (bits.length, payloadFold 1 bits) := by
  simpa [parse] using run_encodeFrame bits suffix 0 1

theorem parse_suffix_independent (bits : List Bool) (s₁ s₂ : Nat) :
    parse (encodeFrame bits s₁) = parse (encodeFrame bits s₂) := by
  rw [parse_encodeFrame, parse_encodeFrame]

/-- The finite-marker encoding is exhaustive, including inputs with a
virtual zero payload or a virtual zero final marker. -/
theorem encodeFrame_surjective (i : Nat) : ∃ bits suffix, encodeFrame bits suffix = i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
    by_cases h : i % 2 = 0
    · exact ⟨[], i / 2, by simp [encodeFrame]; omega⟩
    · have hi : i / 4 < i := by omega
      obtain ⟨bs, s, he⟩ := ih (i / 4) hi
      by_cases hb : (i / 2) % 2 = 0
      · refine ⟨false :: bs, s, ?_⟩
        simp only [encodeFrame, Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero, he]
        omega
      · refine ⟨true :: bs, s, ?_⟩
        simp only [encodeFrame, ↓reduceIte, he]
        omega

/-- The finite marked prefix, with no bits above the final zero marker. -/
def prefixValue : List Bool → Nat
  | [] => 0
  | b :: bs => 1 + 2 * (if b then 1 else 0) + 4 * prefixValue bs

/-- The suffix begins above the marker in position `2 * bits.length`. -/
theorem encodeFrame_decompose (bits : List Bool) (suffix : Nat) :
    encodeFrame bits suffix = prefixValue bits + 2 * 4 ^ bits.length * suffix := by
  induction bits with
  | nil => simp [encodeFrame, prefixValue]
  | cons b bs ih =>
    simp only [encodeFrame, prefixValue, ih, List.length_cons, pow_succ]
    ring

/-- The same framing in the existing shared low-endian bitstring encoding. -/
def frameBits : List Bool → List Bool → List Bool
  | [], suffix => false :: suffix
  | b :: bs, suffix => true :: b :: frameBits bs suffix

theorem encodeFrame_eq_value (bits suffix : List Bool) :
    encodeFrame bits (Shared.Codes.BitNumeralCompare.value suffix) =
      Shared.Codes.BitNumeralCompare.value (frameBits bits suffix) := by
  induction bits with
  | nil => simp [encodeFrame, frameBits, Shared.Codes.BitNumeralCompare.value]
  | cons b bs ih =>
    simp only [encodeFrame, frameBits, Shared.Codes.BitNumeralCompare.value, ih]
    cases b <;> simp <;> omega

theorem parse_value_frameBits (bits suffix : List Bool) :
    parse (Shared.Codes.BitNumeralCompare.value (frameBits bits suffix)) =
      (bits.length, payloadFold 1 bits) := by
  rw [← encodeFrame_eq_value]
  exact parse_encodeFrame bits _

/-- The source description is the high sentinel followed by the payload in
the source's reversed order relative to shared low-endian bit values. -/
theorem frame_length_description (bits : List Bool) (suffix : Nat) :
    length (encodeFrame bits suffix) = bits.length ∧
      description (encodeFrame bits suffix) =
        2 ^ bits.length + Shared.Codes.BitNumeralCompare.value bits.reverse := by
  unfold length description
  rw [parse_encodeFrame]
  simp [payloadFold_value]

/-- Every natural input has a complete framing using the shared binary
encoding; this is independent of any candidate-code enumeration. -/
theorem frameBits_covers (i : Nat) : ∃ bits suffix : List Bool,
    Shared.Codes.BitNumeralCompare.value (frameBits bits suffix) = i := by
  obtain ⟨bits, s, hs⟩ := encodeFrame_surjective i
  refine ⟨bits, Computability.encodeNat s, ?_⟩
  rw [← encodeFrame_eq_value, Shared.Codes.BitNumeralCompare.value_encodeNat, hs]

/-- `1` has an odd marker and a virtual zero payload. -/
example : parse 1 = (1, 2) := by
  simpa [encodeFrame, payloadFold] using parse_encodeFrame [false] 0

/-- Any higher bits above a zero marker are ignored by the normalizer. -/
example : parse (encodeFrame [] 12345) = (0, 1) := by
  simpa [payloadFold] using parse_encodeFrame [] 12345

end Shared.Beeping.NPcoNP.Source284Parser
