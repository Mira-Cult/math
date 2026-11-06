import Shared.Beeping.NPcoNP.Source284PairPrefixLoader
import Shared.Beeping.NPcoNP.Source284HardnessFrame
import Shared.Beeping.NPcoNP.Source284Witness

/-! Executable syntax for a fixed-window certificate containing a canonical
pair. The public input is checked as a literal canonical prefix; the suffix
is a bounded list witness followed only by zero padding. This is a list-level
specification: it does not implement a transition table or prove a cost bound. -/
namespace Shared.Beeping.NPcoNP.Source284CanonicalPairWindow

open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284PairPrefixLoader (pairPrefix pair_bits)

def zeros (bs : List Bool) : Bool := bs.all (fun b => !b)

/-- Decode at most `limit` witness blocks `[true,b,false]`; the first zero
marker begins padding, which must be entirely zero within the window. -/
def decodeWitness : Nat → List Bool → Option (List Bool)
  | 0, bs => if zeros bs then some [] else none
  | _ + 1, [] => some []
  | _ + 1, false :: bs => if zeros bs then some [] else none
  | n + 1, true :: b :: false :: bs => (decodeWitness n bs).map (b :: ·)
  | _ + 1, _ => none

@[simp] theorem encode_nil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl

@[simp] theorem encode_cons (b : Bool) (bs : List Bool) :
    BitstringEncoding.bitEncode (b :: bs) = true :: b :: false :: BitstringEncoding.bitEncode bs := rfl

@[simp] theorem zeros_nil : zeros [] = true := rfl
@[simp] theorem zeros_false (bs : List Bool) : zeros (false :: bs) = zeros bs := rfl
@[simp] theorem zeros_true (bs : List Bool) : zeros (true :: bs) = false := rfl

theorem decodeWitness_sound (limit : Nat) (bs w : List Bool)
    (h : decodeWitness limit bs = some w) :
    w.length ≤ limit ∧ ∃ padding, bs = BitstringEncoding.bitEncode w ++ padding ∧
      zeros padding = true := by
  induction limit generalizing bs w with
  | zero =>
      by_cases hz : zeros bs = true
      · simp [decodeWitness, hz] at h
        subst w
        exact ⟨by simp, bs, by simp, hz⟩
      · simp [decodeWitness, hz] at h
  | succ limit ih =>
      cases bs with
      | nil =>
          simp [decodeWitness] at h
          subst w
          exact ⟨by simp, [], by simp, rfl⟩
      | cons a rest =>
          cases a with
          | false =>
              by_cases hz : zeros rest = true
              · simp [decodeWitness, hz] at h
                subst w
                exact ⟨by simp, false :: rest, by simp, by simpa using hz⟩
              · simp [decodeWitness, hz] at h
          | true =>
              cases rest with
              | nil => simp [decodeWitness] at h
              | cons b rest =>
                  cases rest with
                  | nil => simp [decodeWitness] at h
                  | cons term tail =>
                      cases term with
                      | true => simp [decodeWitness] at h
                      | false =>
                          cases hd : decodeWitness limit tail with
                          | none => simp [decodeWitness, hd] at h
                          | some decoded =>
                              simp [decodeWitness, hd] at h
                              subst w
                              obtain ⟨hlen, padding, htail, hzero⟩ := ih tail decoded hd
                              refine ⟨by simp; omega, padding, ?_, hzero⟩
                              simp [htail]

theorem decodeWitness_complete (limit : Nat) (w padding : List Bool)
    (hw : w.length ≤ limit) (hz : zeros padding = true) :
    decodeWitness limit (BitstringEncoding.bitEncode w ++ padding) = some w := by
  induction w generalizing limit with
  | nil =>
      cases limit with
      | zero => simp [decodeWitness, hz]
      | succ limit =>
          cases padding with
          | nil => rfl
          | cons b bs =>
              cases b with
              | false => simpa [decodeWitness] using hz
              | true => simp at hz
  | cons b w ih =>
      cases limit with
      | zero => simp at hw
      | succ limit =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at hw
          simpa [decodeWitness] using congrArg (Option.map (b :: ·)) (ih limit hw)

/-- Compare the complete canonical public-input prefix, then validate the
witness blocks and zero padding. -/
def decode (x window : List Bool) : Option (List Bool) :=
  if window.take (pairPrefix x).length = pairPrefix x then
    decodeWitness x.length (window.drop (pairPrefix x).length)
  else none

theorem decode_sound (x window w : List Bool) (h : decode x window = some w) :
    w.length ≤ x.length ∧ ∃ padding,
      window = BitstringEncoding.bitEncode (x,w) ++ padding ∧ zeros padding = true := by
  unfold decode at h
  split_ifs at h with hp
  obtain ⟨hw, padding, ht, hz⟩ := decodeWitness_sound _ _ _ h
  refine ⟨hw, padding, ?_, hz⟩
  calc
    window = window.take (pairPrefix x).length ++ window.drop (pairPrefix x).length :=
      (List.take_append_drop _ _).symm
    _ = pairPrefix x ++ (BitstringEncoding.bitEncode w ++ padding) := by rw [hp, ht]
    _ = BitstringEncoding.bitEncode (x,w) ++ padding := by rw [pair_bits, List.append_assoc]

theorem decode_complete (x w padding : List Bool) (hw : w.length ≤ x.length)
    (hz : zeros padding = true) :
    decode x (BitstringEncoding.bitEncode (x,w) ++ padding) = some w := by
  rw [pair_bits]
  simp [decode, decodeWitness_complete _ _ _ hw hz]

/-- A fixed number of little-endian certificate bits, with virtual high
zeroes explicitly padded. Bits at and above `width` are ignored. -/
def window (width certificate : Nat) : List Bool :=
  let low := certificate % 2^width
  low.bits ++ List.replicate (width - low.bits.length) false

theorem window_length (width certificate : Nat) :
    (window width certificate).length = width := by
  have h : (certificate % 2^width).bits.length ≤ width := by
    rw [Nat.size_eq_bits_len]
    exact Nat.size_le.mpr (Nat.mod_lt _ (Nat.two_pow_pos _))
  simp [window]
  omega

theorem window_value (width certificate : Nat) :
    value (window width certificate) = certificate % 2^width := by
  simp [window, Shared.Beeping.NPcoNP.Source284HardnessFrame.value_padding,
    Shared.Codes.BinaryAdditionCanonical.value_bits]

theorem same_length_value_injective (xs ys : List Bool)
    (hl : xs.length = ys.length) (hv : value xs = value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons b xs ih =>
      cases ys with
      | nil => simp at hl
      | cons c ys =>
          have ht : xs.length = ys.length := by simpa using hl
          cases b <;> cases c <;> simp [value] at hv
          · have he : value xs = value ys := by omega
            simp [ih ys ht he]
          · omega
          · omega
          · have he : value xs = value ys := by omega
            simp [ih ys ht he]

theorem window_value_bits (width : Nat) (bs : List Bool) (h : bs.length ≤ width) :
    window width (value bs) = bs ++ List.replicate (width - bs.length) false := by
  apply same_length_value_injective
  · rw [window_length]
    simp only [List.length_append, List.length_replicate]
    omega
  · rw [window_value, Shared.Beeping.NPcoNP.Source284HardnessFrame.value_padding]
    apply Nat.mod_eq_of_lt
    exact lt_of_lt_of_le
      (Shared.Beeping.NPcoNP.Source284Witness.value_lt_pow_length bs)
      (Nat.pow_le_pow_right (by decide) h)

@[simp] theorem zeros_replicate (n : Nat) : zeros (List.replicate n false) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

theorem zeros_value (padding : List Bool) (h : zeros padding = true) : value padding = 0 := by
  induction padding with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false =>
          have h' : zeros bs = true := by simpa using h
          simp [value, ih h']
      | true => simp at h

theorem window_decode_sound (width certificate : Nat) (x w : List Bool)
    (h : decode x (window width certificate) = some w) :
    w.length ≤ x.length ∧ certificate % 2^width =
      value (BitstringEncoding.bitEncode (x,w)) := by
  obtain ⟨hw, padding, he, hz⟩ := decode_sound x _ w h
  have hv := congrArg value he
  rw [window_value] at hv
  have hp := zeros_value padding hz
  refine ⟨hw, ?_⟩
  rw [pair_bits] at hv ⊢
  rw [Shared.Beeping.NPcoNP.Source284Parser.bitValue_append] at hv
  simpa [hp] using hv

theorem window_decode_complete (width : Nat) (x w : List Bool)
    (hw : w.length ≤ x.length)
    (hwidth : (BitstringEncoding.bitEncode (x,w)).length ≤ width) :
    decode x (window width (value (BitstringEncoding.bitEncode (x,w)))) = some w := by
  rw [window_value_bits width _ hwidth]
  exact decode_complete x w _ hw (zeros_replicate _)

theorem window_mod (width certificate : Nat) :
    window width (certificate % 2^width) = window width certificate := by
  simp [window]

theorem window_decode_complete_bound (width : Nat) (x w : List Bool)
    (hw : w.length ≤ x.length) (hwidth : 9*x.length+1 ≤ width) :
    decode x (window width (value (BitstringEncoding.bitEncode (x,w)))) = some w := by
  apply window_decode_complete width x w hw
  rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
  omega

/-- The finite-window recognizer accepts exactly the low-window numeral of
the original bounded canonical pair; bits above the window are aliases. -/
theorem window_decode_iff (width certificate : Nat) (x w : List Bool)
    (hwidth : 9*x.length+1 ≤ width) :
    decode x (window width certificate) = some w ↔
      w.length ≤ x.length ∧ certificate % 2^width =
        value (BitstringEncoding.bitEncode (x,w)) := by
  constructor
  · exact window_decode_sound width certificate x w
  · rintro ⟨hw, hv⟩
    rw [← window_mod width certificate, hv]
    exact window_decode_complete_bound width x w hw hwidth

/-- `predicate` is supplied data; computability and cost of an arbitrary
predicate are not asserted. -/
def check (width : Nat) (x : List Bool) (predicate : List Bool → Bool)
    (certificate : Nat) : Bool :=
  match decode x (window width certificate) with
  | none => false
  | some w => predicate w

theorem check_mod (width : Nat) (x : List Bool) (predicate : List Bool → Bool)
    (certificate : Nat) :
    check width x predicate (certificate % 2^width) = check width x predicate certificate := by
  simp [check, window_mod]

/-- A sufficiently large finite certificate search captures exactly the
original bounded-list existential, while retaining all high-bit aliases. -/
theorem bounded_search_iff (width clock : Nat) (x : List Bool)
    (predicate : List Bool → Bool) (hwidth : 9*x.length+1 ≤ width)
    (hclock : width ≤ clock) :
    (∃ c, c < 2^clock ∧ check width x predicate c = true) ↔
      ∃ w, w.length ≤ x.length ∧ predicate w = true := by
  constructor
  · rintro ⟨c, _, hc⟩
    cases hd : decode x (window width c) with
    | none => simp [check, hd] at hc
    | some w =>
        exact ⟨w, (window_decode_sound width c x w hd).1, by simpa [check, hd] using hc⟩
  · rintro ⟨w, hw, hp⟩
    refine ⟨value (BitstringEncoding.bitEncode (x,w)), ?_, ?_⟩
    · have hlen : (BitstringEncoding.bitEncode (x,w)).length ≤ clock := by
        rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]
        omega
      exact lt_of_lt_of_le
        (Shared.Beeping.NPcoNP.Source284Witness.value_lt_pow_length _)
        (Nat.pow_le_pow_right (by decide) hlen)
    · simp [check, window_decode_complete_bound width x w hw hwidth, hp]

example : decode [] [false] = some [] := by decide
example : decode [] [false, true, false, false] = none := by decide
example : decode [] [] = none := by decide
example : decode [false] [true, true, true, false, true, false, false] = some [] := by decide

end Shared.Beeping.NPcoNP.Source284CanonicalPairWindow
