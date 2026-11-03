import Shared.PNP.Record285.RelativeEndpoint

/-! Exact all-bitstring interface for the selected bounded-reference source.
This proves encoding and language identities, not polynomial running time. -/
namespace Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.Source

/-- Bits are least-significant first. -/
def value : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * value bs

def bits : Nat → Nat → List Bool
  | 0, _ => []
  | n+1, w => decide (w%2=1) :: bits n (w/2)

@[simp] theorem bits_length (n w : Nat) : (bits n w).length = n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih => simp [bits, ih]

theorem value_lt_pow (xs : List Bool) : value xs < 2^xs.length := by
  induction xs with
  | nil => decide
  | cons b bs ih =>
    cases b <;> simp only [value, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
      if_false, if_true] <;> omega


/-- Decoding the numerical value recovers every payload bit, and supplies
zero beyond the end. -/
theorem value_bit (xs : List Bool) (i : Nat) :
    (value xs).testBit i = xs[i]?.getD false := by
  induction xs generalizing i with
  | nil => simp [value]
  | cons b bs ih =>
    cases i with
    | zero => cases b <;> simp [value, Nat.testBit_zero]
    | succ i =>
      rw [Nat.testBit_succ]
      have hdiv : value (b :: bs) / 2 = value bs := by cases b <;> simp [value] <;> omega
      rw [hdiv, ih]
      rfl

/-- Every numeric suffix below the n-bit bound has a canonical n-bit word. -/
theorem value_bits_of_lt (n w : Nat) (h : w < 2^n) : value (bits n w) = w := by
  induction n generalizing w with
  | zero =>
    simp only [Nat.pow_zero] at h
    have hw : w = 0 := by omega
    subst w
    rfl
  | succ n ih =>
    have hpow : 0 < 2^n := Nat.pow_pos (by decide : 0 < 2)
    have hquot : w/2 < 2^n := by rw [Nat.pow_succ] at h; omega
    simp only [bits, value, ih (w/2) hquot]
    by_cases hm : w%2=1
    · simp only [hm, decide_true, if_true]
      omega
    · have hz : w%2=0 := by omega
      simp only [hm, decide_false, Bool.false_eq_true, if_false]
      omega

def canonical (payload : List Bool) : List Bool :=
  List.replicate payload.length true ++ false :: payload


@[simp] theorem canonical_length (payload : List Bool) :
    (canonical payload).length = 2*payload.length+1 := by
  simp [canonical]
  omega

theorem canonical_bit (payload : List Bool) (i : Nat) :
    (canonical payload)[i]?.getD false =
      if i < payload.length then true else if i = payload.length then false
      else payload[i-(payload.length+1)]?.getD false := by
  by_cases hi : i < payload.length
  · simp [canonical, List.getElem?_append, hi]
  · by_cases he : i = payload.length
    · subst i
      simp [canonical]
    · have hidx : i - payload.length = (i-(payload.length+1))+1 := by omega
      simp [canonical, List.getElem?_append, hi, he, hidx]

/-- The numeric initial tape and the full canonical bitstring agree at every
nonnegative position, including the blank tail. -/
theorem frame_tape_canonical (payload : List Bool) (i : Nat) :
    (Shared.PNP.Record285.RelativeTape.initialRelative
      (frame (2^payload.length) (value payload)) 0).physical.tape (i : Int) =
        (canonical payload)[i]?.getD false := by
  rw [Shared.PNP.Record285.RelativeTape.candidate_input_tape, canonical_bit, value_bit]

/-- Parse a run of ones and its required zero delimiter. -/
def parsePrefix : List Bool → Option (Nat × List Bool)
  | [] => none
  | false :: rest => some (0,rest)
  | true :: rest => do
      let (n,tail) ← parsePrefix rest
      some (n+1,tail)

def parse (input : List Bool) : Option (List Bool) := do
  let (n,payload) ← parsePrefix input
  if payload.length = n then some payload else none


@[simp] theorem parse_empty : parse [] = none := rfl
@[simp] theorem parse_zero_frame : parse [false] = some [] := rfl

@[simp] theorem prefix_ones (n : Nat) (tail : List Bool) :
    parsePrefix (List.replicate n true ++ false :: tail) = some (n,tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, parsePrefix, ih]

@[simp] theorem parse_canonical (payload : List Bool) : parse (canonical payload) = some payload := by
  simp [parse, canonical]

/-- A successful prefix parse accounts for every input bit. -/
theorem prefix_sound {input : List Bool} {n : Nat} {tail : List Bool}
    (h : parsePrefix input = some (n,tail)) : input = List.replicate n true ++ false :: tail := by
  induction input generalizing n with
  | nil => simp [parsePrefix] at h
  | cons b bs ih =>
    cases b with
    | false =>
      simp only [parsePrefix, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl⟩
      rfl
    | true =>
      cases hp : parsePrefix bs with
      | none => simp [parsePrefix,hp] at h
      | some v =>
        rcases v with ⟨m,rest⟩
        simp only [parsePrefix,hp,bind,Option.bind,Option.some.injEq,Prod.mk.injEq] at h
        rcases h with ⟨hn,ht⟩
        subst n
        subst rest
        rw [ih hp]
        simp only [List.replicate_succ, List.cons_append]

/-- Malformed words are exactly those with no `1^n 0` prefix followed by n
bits. Empty input is malformed; `[false]` is the unique zero-length frame. -/
theorem parse_sound {input payload : List Bool} (h : parse input = some payload) :
    input = canonical payload := by
  unfold parse at h
  cases hp : parsePrefix input with
  | none => simp [hp] at h
  | some v =>
    rcases v with ⟨n,tail⟩
    by_cases hl : tail.length = n
    · simp [hp,hl] at h
      subst payload
      have hs := prefix_sound hp
      simpa [canonical, hl] using hs
    · simp [hp,hl] at h

theorem parse_iff {input payload : List Bool} :
    parse input = some payload ↔ input = canonical payload := by
  constructor
  · exact parse_sound
  · rintro rfl
    exact parse_canonical payload

def referenceLanguage (input : List Bool) : Bool :=
  match parse input with
  | none => false
  | some payload => reference payload.length (2^payload.length) (value payload)

def candidateLanguage (program exponent : Nat) (input : List Bool) : Bool :=
  match parse input with
  | none => false
  | some payload => candidate program exponent payload.length (2^payload.length) (value payload)

/-- Both derived languages reject every malformed bitstring. -/
theorem malformed_rejected (program exponent : Nat) (input : List Bool) (h : parse input = none) :
    referenceLanguage input = false ∧ candidateLanguage program exponent input = false := by
  simp [referenceLanguage, candidateLanguage, h]

/-- Agreement on the source's `(n,w)` enumeration is agreement on every raw
bitstring under the explicit malformed-input convention. -/
theorem goodCandidate_iff_all_bitstrings (program exponent : Nat) :
    GoodCandidate program exponent ↔
      ∀ input, candidateLanguage program exponent input = referenceLanguage input := by
  constructor
  · intro h input
    cases hp : parse input with
    | none => simp [candidateLanguage, referenceLanguage, hp]
    | some payload =>
      have hb := value_lt_pow payload
      have he := h payload.length (value payload) hb
      cases hc : candidate program exponent payload.length (2^payload.length) (value payload) <;>
        cases hr : reference payload.length (2^payload.length) (value payload) <;>
        simp [candidateLanguage, referenceLanguage, hp, mismatch, hc, hr] at he ⊢
  · intro h n w hw
    let payload := bits n w
    have hlen : payload.length = n := bits_length n w
    have hv : value payload = w := value_bits_of_lt n w hw
    have ha := h (canonical payload)
    simp only [candidateLanguage, referenceLanguage, parse_canonical, hlen, hv] at ha
    unfold mismatch
    rw [ha]
    simp

end Shared.PNP.Record285.CanonicalInput
