import PASoundness.Cantor

/-!
The fixed PA238-ABI contradiction suffix from the observer lane.  This module
decodes only a list of natural command *numbers* and compares its final sixteen
numbers.  It never interprets a command, checks a derivation, or evaluates a
formula. Its exact connection to compact derivations is proved in CompactMarker;
the genuine-PA interpretation remains separate.

The constants reproduce `inconsistency_suffix_words()` from the inspected
PR59 source `pa_marker.py` (SHA256
07654c5f3529a076820249cc845cf2754c92e965075346fa2f18bc3573c03037)
and `weakening-schema.json` (SHA256
b796124fc6b7a3cb1ab4e766032c4386d363ea4b48973d2810b4348c5ca2be7c).
These bytes were absent from PR59's initial checkpoint and were subsequently
published unchanged at f98f4b7c81f0171a15aed75437d4ec5eeca9779e.
-/

namespace PASoundness.Marker

open PASoundness.Cantor

def encode : List Nat → Nat
  | [] => 0
  | c :: cs => pair c (encode cs) + 1

/-- A structurally total parser: each call spends one unit of explicit fuel. -/
def decodeAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, code + 1 =>
    (unpair code).1 :: decodeAux fuel (unpair code).2

def decode (code : Nat) : List Nat := decodeAux code code

def bottomSuffix : List Nat :=
  [28, 28,
   27522917047026758076159745906442732023373882368,
   27523211463306142016561936129939648680044857008,
   4412934486990549678856113725590982722864182779107834387146130308450560593982878949560954501611399316,
   2,
   170464592763764838179784624396316909523992692473817637299365242831796001738217495680472719422468834012217196496654050197805704211114019178952779704646213909975429703281193918024803492852479686150252442085527687143376104946728629986064938672219541612859767148239517975066205296328232101514073043414274969054315051403987179205652116270113244809932282346742790002366275927343702103256777448332088,
   2, 2, 2,
   27523506118941623619931883796737043646882006180,
   689536502954158575572734132752319117661921492501272506552379086580674996554799169924205687968468,
   2, 2, 2, 2]

theorem bottomSuffix_length : bottomSuffix.length = 16 := rfl

/-- Exact suffix equality; no prefix computation is performed. -/
def hasBottomSuffix (words : List Nat) : Bool :=
  decide (16 ≤ words.length ∧ words.drop (words.length - 16) = bottomSuffix)

def bottomTail (code : Nat) : Bool := hasBottomSuffix (decode code)

theorem hasBottomSuffix_iff (words : List Nat) :
    hasBottomSuffix words = true ↔
      16 ≤ words.length ∧ words.drop (words.length - 16) = bottomSuffix := by
  simp only [hasBottomSuffix, decide_eq_true_eq]

theorem decodeAux_encode (words : List Nat) (fuel : Nat) (h : words.length ≤ fuel) :
    decodeAux fuel (encode words) = words := by
  induction words generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons c cs ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at h; omega
    | succ fuel =>
      simp only [encode, decodeAux, unpair_pair]
      rw [ih fuel (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using h)]

theorem length_le_encode (words : List Nat) : words.length ≤ encode words := by
  induction words with
  | nil => rfl
  | cons c cs ih =>
    have hs : encode cs ≤ pair c (encode cs) := by
      simpa only [unpair_pair] using unpair_snd_le (pair c (encode cs))
    simp only [List.length_cons, encode]
    omega

theorem decode_encode (words : List Nat) : decode (encode words) = words :=
  decodeAux_encode words (encode words) (length_le_encode words)

theorem encode_surjective (code : Nat) : ∃ words, encode words = code := by
  induction code using Nat.strong_induction_on with
  | h code ih =>
    cases code with
    | zero => exact ⟨[], rfl⟩
    | succ code =>
      obtain ⟨words, hw⟩ := ih (unpair code).2
        (Nat.lt_succ_of_le (unpair_snd_le code))
      refine ⟨(unpair code).1 :: words, ?_⟩
      simp only [encode, hw, pair_unpair]

/-- No malformed numeric list can evade the finite structural decoder. -/
theorem encode_decode (code : Nat) : encode (decode code) = code := by
  obtain ⟨words, hw⟩ := encode_surjective code
  rw [← hw, decode_encode]

theorem bottomTail_zero : bottomTail 0 = false := by
  decide

theorem encoded_suffix_recognized (words : List Nat) :
    bottomTail (encode (words ++ bottomSuffix)) = true := by
  rw [bottomTail, decode_encode, hasBottomSuffix_iff]
  simp only [List.length_append, bottomSuffix_length, Nat.add_sub_cancel_right]
  exact ⟨by omega, by simp⟩

end PASoundness.Marker
