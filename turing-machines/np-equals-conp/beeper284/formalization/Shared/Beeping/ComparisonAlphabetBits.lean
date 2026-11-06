import Shared.Beeping.ComparisonSingleTape

/-! Executable fixed-width binary encoding of the actual TM2-to-TM0 tape
alphabet. One marker bit and four three-bit option-symbol fields yield 13
bits per cell. This supplies no machine that reads or writes the blocks. -/
namespace Shared.Beeping.ComparisonAlphabetBits
open Turing Turing.PartrecToTM2
open Shared.Beeping.ComparisonSingleTape

/-- Field code 000 is the blank option; 001 through 100 are the four stack
symbols. The remaining three-bit words are invalid. -/
def putField : Option Symbol → List Bool
  | none => [false,false,false]
  | some .consₗ => [false,false,true]
  | some .cons => [false,true,false]
  | some .bit0 => [false,true,true]
  | some .bit1 => [true,false,false]

def getField : List Bool → Option (Option Symbol × List Bool)
  | false::false::false::rest => some (none,rest)
  | false::false::true::rest => some (some .consₗ,rest)
  | false::true::false::rest => some (some .cons,rest)
  | false::true::true::rest => some (some .bit0,rest)
  | true::false::false::rest => some (some .bit1,rest)
  | _ => none

theorem field_length (s : Option Symbol) : (putField s).length = 3 := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

theorem get_put (s : Option Symbol) (rest : List Bool) :
    getField (putField s ++ rest) = some (s,rest) := by
  cases s with
  | none => rfl
  | some s => cases s <;> rfl

theorem get_put_nil (s : Option Symbol) : getField (putField s) = some (s,[]) := by
  simpa using get_put s []

theorem getField_size (bits : List Bool) (s : Option Symbol) (rest : List Bool)
    (h : getField bits = some (s,rest)) : bits.length = 3 + rest.length := by
  cases bits with
  | nil => simp [getField] at h
  | cons a bits =>
    cases bits with
    | nil => simp [getField] at h
    | cons b bits =>
      cases bits with
      | nil => simp [getField] at h
      | cons c bits =>
        cases a <;> cases b <;> cases c <;> simp [getField] at h <;>
          rcases h with ⟨rfl,rfl⟩ <;> simp <;> omega

def encode (a : Alphabet) : List Bool :=
  a.1 :: (putField (a.2 K'.main) ++ putField (a.2 K'.rev) ++
    putField (a.2 K'.aux) ++ putField (a.2 K'.stack))

def decode : List Bool → Option Alphabet
  | [] => none
  | marker::rest => do
    let (main,r1) ← getField rest
    let (rev,r2) ← getField r1
    let (aux,r3) ← getField r2
    let (stack,r4) ← getField r3
    if r4 = [] then some (marker, fun k => match k with
      | .main => main | .rev => rev | .aux => aux | .stack => stack) else none

theorem encode_length (a : Alphabet) : (encode a).length = 13 := by
  simp [encode,field_length]

theorem decode_encode (a : Alphabet) : decode (encode a) = some a := by
  rcases a with ⟨marker,cols⟩
  simp [encode,decode,List.append_assoc,get_put,get_put_nil]
  congr 1
  congr 1
  funext k
  cases k <;> rfl

/-- Successful decoding requires exactly one complete block. -/
theorem decode_size (bits : List Bool) (a : Alphabet) (h : decode bits = some a) :
    bits.length = 13 := by
  cases bits with
  | nil => simp [decode] at h
  | cons marker rest =>
    cases h1 : getField rest with
    | none => simp [decode,h1] at h
    | some p1 =>
      rcases p1 with ⟨s1,r1⟩
      cases h2 : getField r1 with
      | none => simp [decode,h1,h2] at h
      | some p2 =>
        rcases p2 with ⟨s2,r2⟩
        cases h3 : getField r2 with
        | none => simp [decode,h1,h2,h3] at h
        | some p3 =>
          rcases p3 with ⟨s3,r3⟩
          cases h4 : getField r3 with
          | none => simp [decode,h1,h2,h3,h4] at h
          | some p4 =>
            rcases p4 with ⟨s4,r4⟩
            have hnil : r4 = [] := by
              by_contra hn
              simp [decode,h1,h2,h3,h4,hn] at h
            have hs1 := getField_size rest s1 r1 h1
            have hs2 := getField_size r1 s2 r2 h2
            have hs3 := getField_size r2 s3 r3 h3
            have hs4 := getField_size r3 s4 r4 h4
            simp only [List.length_cons, hnil, List.length_nil] at *
            omega

theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := congrArg decode h
  simpa [decode_encode] using hh

/-- The all-blank unbounded source tape becomes an all-false bit tape. -/
theorem encode_blank : encode (default : Alphabet) = List.replicate 13 false := by rfl

/-- Encode each integer-indexed source cell as an aligned 13-bit block. -/
def binaryTape (tape : Int → Alphabet) (i : Int) : Bool :=
  ((encode (tape (i / 13)))[(i % 13).toNat]?).getD false

/-- Every block, including those at negative positions, decodes to its source
cell when read at its aligned integer address. -/
theorem block_bit (tape : Int → Alphabet) (position : Int) (offset : Nat) (h : offset < 13) :
    binaryTape tape (13 * position + (offset : Int)) =
      ((encode (tape position))[offset]?).getD false := by
  have hd : (13 * position + (offset : Int)) / 13 = position := by omega
  have hm : (13 * position + (offset : Int)) % 13 = (offset : Int) := by omega
  simp [binaryTape,hd,hm]

/-- Read exactly the 13 bits of an aligned source-cell block. -/
def readBlock (tape : Int → Bool) (position : Int) : List Bool :=
  (List.range 13).map (fun (offset : Nat) => tape (13 * position + (offset : Int)))

theorem readBlock_binaryTape (tape : Int → Alphabet) (position : Int) :
    readBlock (binaryTape tape) position = encode (tape position) := by
  apply List.ext_getElem
  · simp [readBlock,encode_length]
  · intro i hi hj
    have hlt : i < 13 := by simpa [readBlock] using hi
    simp only [readBlock,List.getElem_map,List.getElem_range]
    rw [block_bit tape position i hlt, List.getElem?_eq_getElem hj]
    rfl

theorem decode_readBlock (tape : Int → Alphabet) (position : Int) :
    decode (readBlock (binaryTape tape) position) = some (tape position) := by
  rw [readBlock_binaryTape,decode_encode]

/-- Updating one source symbol changes no other encoded cell block. -/
theorem update_other_block (tape : Int → Alphabet) (position other : Int)
    (a : Alphabet) (h : other ≠ position) :
    readBlock (binaryTape (Function.update tape position a)) other = encode (tape other) := by
  rw [readBlock_binaryTape,Function.update_of_ne h]

theorem update_own_block (tape : Int → Alphabet) (position : Int) (a : Alphabet) :
    readBlock (binaryTape (Function.update tape position a)) position = encode a := by
  rw [readBlock_binaryTape,Function.update_self]

theorem blankTape (i : Int) : binaryTape (fun _ => (default : Alphabet)) i = false := by
  unfold binaryTape
  rw [encode_blank]
  simp only [List.getElem?_replicate]
  split <;> rfl

/-- Each block of an actual post-Turing tape represents the symbol at that
integer offset from its head. -/
theorem decode_postTape (tape : Tape Alphabet) (position : Int) :
    decode (readBlock (binaryTape tape.nth) position) = some (tape.nth position) :=
  decode_readBlock tape.nth position

/-- Moving the source head right changes the relative binary origin by 13. -/
theorem move_right_binary (tape : Tape Alphabet) (i : Int) :
    binaryTape (tape.move Dir.right).nth i = binaryTape tape.nth (i + 13) := by
  have hd : (i + 13) / 13 = i / 13 + 1 := by omega
  have hm : (i + 13) % 13 = i % 13 := by omega
  simp [binaryTape,hd,hm,Tape.move_right_nth]

/-- Moving the source head left changes the relative binary origin by 13. -/
theorem move_left_binary (tape : Tape Alphabet) (i : Int) :
    binaryTape (tape.move Dir.left).nth i = binaryTape tape.nth (i - 13) := by
  have hd : (i - 13) / 13 = i / 13 - 1 := by omega
  have hm : (i - 13) % 13 = i % 13 := by omega
  simp [binaryTape,hd,hm,Tape.move_left_nth]

namespace Fixtures
example : decode [] = none := by decide
example : decode (true :: List.replicate 12 true) = none := by decide
example : decode (List.replicate 14 false) = none := by decide
example : decode (encode (default : Alphabet)) = some default := decode_encode _
end Fixtures

end Shared.Beeping.ComparisonAlphabetBits
