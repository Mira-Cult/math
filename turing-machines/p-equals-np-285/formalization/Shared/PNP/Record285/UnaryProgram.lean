import Shared.PNP.Record285.RelativeTape

/-! Finite source-program record encoding. This represents arbitrary finite
flat action lists with zero-padded tails; it does not itself establish a
polynomial-time canonical-model simulation or state-numbering coverage. -/
namespace Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape

/-- Prefix `count` one bits and one zero bit to a low-endian numeric stream. -/
def prepend : Nat → Nat → Nat
  | 0, tail => 2 * tail
  | count+1, tail => 2 * prepend count tail + 1

@[simp] theorem pop_prepend (count tail : Nat) : popUnary (prepend count tail) = (count,tail) := by
  induction count with
  | zero => simp [prepend]
  | succ count ih => simp [prepend, ih]

/-- A finite sequence of records, followed by virtual zero records. -/
def encode : List Nat → Nat
  | [] => 0
  | head :: tail => prepend head (encode tail)

@[simp] theorem skip_encode (n : Nat) (records : List Nat) :
    skipUnary n (encode records) = encode (records.drop n) := by
  induction n generalizing records with
  | zero => rfl
  | succ n ih =>
    cases records with
    | nil =>
      have h := ih []
      simpa [skipUnary, encode, popUnary] using h
    | cons head tail => simp [skipUnary, encode, ih]

/-- The result includes the residual stream as well as the decoded record,
including every out-of-range index. -/
theorem pop_skip_encode (n : Nat) (records : List Nat) :
    popUnary (skipUnary n (encode records)) =
      ((records[n]?).getD 0, encode (records.drop (n+1))) := by
  rw [skip_encode]
  induction n generalizing records with
  | zero => cases records <;> simp [encode, popUnary]
  | succ n ih => cases records <;> simp [encode, popUnary, ih]

/-- Explicit packed representation of write, relative turn and target state. -/
def pack (a : Action) : Nat := bitVal a.write + 2 * bitVal a.turn + 4 * a.next

def unpack (n : Nat) : Action :=
  ⟨decide (n % 2 = 1), decide ((n / 2) % 2 = 1), n / 4⟩

@[simp] theorem unpack_pack (a : Action) : unpack (pack a) = a := by
  cases a with
  | mk write turn next =>
    cases write <;> cases turn <;> simp [pack, unpack, bitVal] <;> omega

def defaultAction : Action := ⟨false,false,0⟩

@[simp] theorem pack_default : pack defaultAction = 0 := rfl
@[simp] theorem unpack_zero : unpack 0 = defaultAction := rfl

def encodeActions (rows : List Action) : Nat := encode (rows.map pack)

/-- The evaluator's exact action at every ordinal, including padded zeros. -/
theorem action_at (rows : List Action) (ordinal : Nat) :
    unpack (popUnary (skipUnary ordinal (encodeActions rows))).1 =
      (rows[ordinal]?).getD defaultAction := by
  have h := pop_skip_encode ordinal (rows.map pack)
  have hp := congrArg Prod.fst h
  simp only [encodeActions, hp, List.getElem?_map]
  cases rows[ordinal]? <;> simp

/-- Every source action selector is exactly the corresponding encoded flat row.
Selectors can overlap unless the caller chooses compatible state offsets. -/
theorem rowAction_encoded (rows : List Action) (state : Nat) (read choice : Bool) :
    rowAction (encodeActions rows) state read choice =
      (rows[state - 1 + 2*bitVal read + bitVal choice]?).getD defaultAction := by
  exact action_at rows (state - 1 + 2*bitVal read + bitVal choice)

/-- State offsets are spaced by four so the four read/choice selectors for
one finite state cannot collide with selectors for another. -/
def stateCode (q : Fin n) : Nat := 4 * q.val + 1

def finiteRows (n : Nat) (f : Fin n → Bool → Bool → Action) : List Action :=
  List.ofFn fun (i : Fin (4*n)) =>
    f ⟨i.val / 4, by have h := i.isLt; omega⟩
      (decide ((i.val % 4) / 2 = 1)) (decide (i.val % 2 = 1))

theorem finiteRows_at (n : Nat) (f : Fin n → Bool → Bool → Action)
    (q : Fin n) (read choice : Bool) :
    (finiteRows n f)[stateCode q - 1 + 2*bitVal read + bitVal choice]? =
      some (f q read choice) := by
  have hq := q.isLt
  let i := stateCode q - 1 + 2*bitVal read + bitVal choice
  have hi : i < 4*n := by
    dsimp [i, stateCode]
    cases read <;> cases choice <;> simp [bitVal] <;> omega
  have hs : i / 4 = q.val := by
    dsimp [i, stateCode]
    cases read <;> cases choice <;> simp [bitVal] <;> omega
  have hr : decide ((i % 4) / 2 = 1) = read := by
    dsimp [i, stateCode]
    cases read <;> cases choice <;> simp [bitVal] <;> omega
  have hc : decide (i % 2 = 1) = choice := by
    dsimp [i, stateCode]
    cases read <;> cases choice <;> simp [bitVal] <;> omega
  change (List.ofFn (fun (j : Fin (4*n)) =>
    f ⟨j.val / 4, by have h := j.isLt; omega⟩
      (decide ((j.val % 4) / 2 = 1)) (decide (j.val % 2 = 1))))[i]? = _
  rw [List.getElem?_ofFn, dif_pos hi]
  have he : (⟨i / 4, by omega⟩ : Fin n) = q := Fin.ext hs
  rw [he, hr, hc]

/-- Every finite table of actions is simultaneously represented at spaced
source selectors, uniformly in the finite table and both input bits. -/
theorem finite_table_encoded (n : Nat) (f : Fin n → Bool → Bool → Action)
    (q : Fin n) (read choice : Bool) :
    rowAction (encodeActions (finiteRows n f)) (stateCode q) read choice =
      f q read choice := by
  rw [rowAction_encoded, finiteRows_at]
  rfl

/-- A bounded relative machine has finite control and an optional HALT target. -/
structure FiniteAction (n : Nat) where
  write : Bool
  turn : Bool
  next : Option (Fin n)

/-- Translate live finite targets to their spaced source-state codes. -/
def lower (a : FiniteAction n) : Action :=
  ⟨a.write, a.turn, a.next.elim 0 stateCode⟩

def finiteProgram (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n) : Nat :=
  encodeActions (finiteRows n fun q read choice => lower (f q read choice))

@[simp] theorem finiteProgram_row (n : Nat) (f : Fin n → Bool → Bool → FiniteAction n)
    (q : Fin n) (read choice : Bool) :
    rowAction (finiteProgram n f) (stateCode q) read choice = lower (f q read choice) :=
  finite_table_encoded n _ q read choice

structure FiniteConfig (n : Nat) where
  state : Fin n
  physical : TapeConfig
  choices : Nat

def embed (c : FiniteConfig n) : RelativeConfig :=
  ⟨stateCode c.state, c.physical, c.choices⟩

def finiteStep (f : Fin n → Bool → Bool → FiniteAction n)
    (c : FiniteConfig n) : Option (FiniteConfig n) :=
  let a := f c.state (c.physical.tape c.physical.head) (c.choices.testBit 0)
  a.next.map fun q => ⟨q, physicalStep c.physical a.write a.turn, c.choices / 2⟩

/-- Encoding preserves one full live configuration, or reports HALT at the
same step. The full tape and head are included in `physical`. -/
theorem finiteStep_encoded (f : Fin n → Bool → Bool → FiniteAction n)
    (c : FiniteConfig n) :
    (finiteStep f c).map embed = relativeStep (finiteProgram n f) (embed c) := by
  unfold finiteStep relativeStep embed
  simp only [finiteProgram_row]
  generalize h : f c.state (c.physical.tape c.physical.head) (c.choices.testBit 0) = a
  cases a with
  | mk write turn next =>
    cases next with
    | none => rfl
    | some target => simp [lower, stateCode]

def finiteRun (f : Fin n → Bool → Bool → FiniteAction n) :
    Nat → FiniteConfig n → Option (FiniteConfig n)
  | 0, c => some c
  | clock+1, c =>
    match finiteStep f c with
    | none => none
    | some next => finiteRun f clock next

/-- Any finite source-style transition table has an encoded natural program
with identical bounded halting behavior and live full configurations. -/
theorem finiteRun_encoded (f : Fin n → Bool → Bool → FiniteAction n)
    (clock : Nat) (c : FiniteConfig n) :
    (finiteRun f clock c).map embed = relativeRun (finiteProgram n f) clock (embed c) := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    have hs := finiteStep_encoded f c
    cases hf : finiteStep f c with
    | none =>
      simp only [hf, Option.map_none] at hs
      simp [finiteRun, hf, relativeRun, ← hs]
    | some next =>
      simp only [hf, Option.map_some] at hs
      simpa [finiteRun, hf, relativeRun, ← hs] using ih next

def finiteInitial (hn : 0 < n) (input choices : Nat) : FiniteConfig n :=
  ⟨⟨0,hn⟩, ⟨inputTape input, 0, false⟩, choices⟩

@[simp] theorem embed_finiteInitial (hn : 0 < n) (input choices : Nat) :
    embed (finiteInitial hn input choices) = initialRelative input choices := rfl

/-- In particular, the encoded program is reached by the actual candidate
family and has the same result under its original clock and input frame. -/
theorem finite_candidate_iff (hn : 0 < n) (f : Fin n → Bool → Bool → FiniteAction n)
    (exponent size radix remaining : Nat) :
    Source.candidate (finiteProgram n f) exponent size radix remaining = true ↔
      finiteRun f ((size+2)^exponent)
        (finiteInitial hn (Source.frame radix remaining) 0) = none := by
  rw [candidate_halts_iff]
  have h := finiteRun_encoded f ((size+2)^exponent)
    (finiteInitial hn (Source.frame radix remaining) 0)
  rw [embed_finiteInitial] at h
  rw [← h]
  cases finiteRun f ((size+2)^exponent)
    (finiteInitial hn (Source.frame radix remaining) 0) <;> simp

end Shared.PNP.Record285.UnaryProgram
