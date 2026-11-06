import Shared.Codes.FiniteTables

/-! Numeric statement syntax and a fuel-bounded prefix decoder. This is not
an execution semantics or a TM2 model simulation. `TM2Primcodable` proves
computability of complete decoding; the fuel-bounded prefix parser is separate.
Tables remain subject to later range and shape validation. -/
namespace Shared.Codes.TM2Statements

/-- Finite numeric syntax for one TM2 statement block. The tables contain
numeric results; Boolean tables use the conventional 0/1 representation. -/
inductive Code where
  | halt
  | goto (table : List Nat)
  | push (stack : Nat) (table : List Nat) (next : Code)
  | peek (stack : Nat) (table : List (List Nat)) (next : Code)
  | pop (stack : Nat) (table : List (List Nat)) (next : Code)
  | load (table : List Nat) (next : Code)
  | branch (table : List Nat) (yes no : Code)
  deriving DecidableEq, Repr

/-- Prefix serialization: tables are encoded through the shared numeric codec. -/
def tokens : Code → List Nat
  | .halt => [0]
  | .goto t => [1, Encodable.encode t]
  | .push k t q => 2 :: k :: Encodable.encode t :: tokens q
  | .peek k t q => 3 :: k :: Encodable.encode t :: tokens q
  | .pop k t q => 4 :: k :: Encodable.encode t :: tokens q
  | .load t q => 5 :: Encodable.encode t :: tokens q
  | .branch t a b => 6 :: Encodable.encode t :: (tokens a ++ tokens b)

def depth : Code → Nat
  | .halt | .goto _ => 1
  | .push _ _ q | .peek _ _ q | .pop _ _ q | .load _ q => depth q + 1
  | .branch _ a b => max (depth a) (depth b) + 1

/-- A fuel-bounded parser. Invalid tags, truncated input, invalid table codes,
or exhausted fuel fail. The unconsumed suffix is returned for branch parsing. -/
def parse : Nat → List Nat → Option (Code × List Nat)
  | 0, _ => none
  | _ + 1, 0 :: xs => some (.halt, xs)
  | _ + 1, 1 :: t :: xs => (FiniteTables.decode₁ t).map fun table => (.goto table, xs)
  | f + 1, 2 :: k :: t :: xs => do
      let table ← FiniteTables.decode₁ t
      let (q, rest) ← parse f xs
      return (.push k table q, rest)
  | f + 1, 3 :: k :: t :: xs => do
      let table ← FiniteTables.decode₂ t
      let (q, rest) ← parse f xs
      return (.peek k table q, rest)
  | f + 1, 4 :: k :: t :: xs => do
      let table ← FiniteTables.decode₂ t
      let (q, rest) ← parse f xs
      return (.pop k table q, rest)
  | f + 1, 5 :: t :: xs => do
      let table ← FiniteTables.decode₁ t
      let (q, rest) ← parse f xs
      return (.load table q, rest)
  | f + 1, 6 :: t :: xs => do
      let table ← FiniteTables.decode₁ t
      let (a, rest) ← parse f xs
      let (b, rest') ← parse f rest
      return (.branch table a b, rest')
  | _, _ => none

/-- Appending unrelated tokens does not change parsing of the first statement. -/
theorem parse_tokens (q : Code) (fuel : Nat) (suffix : List Nat) (h : depth q ≤ fuel) :
    parse fuel (tokens q ++ suffix) = some (q, suffix) := by
  induction q generalizing fuel suffix with
  | halt =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f => simp [parse, tokens]
  | goto t =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f => simp [parse, tokens, FiniteTables.decode₁]
  | push k t q ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f =>
      have hh : depth q ≤ f := by simp [depth] at h; omega
      simp [parse, tokens, FiniteTables.decode₁, ih f suffix hh]
  | peek k t q ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f =>
      have hh : depth q ≤ f := by simp [depth] at h; omega
      simp [parse, tokens, FiniteTables.decode₂, ih f suffix hh]
  | pop k t q ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f =>
      have hh : depth q ≤ f := by simp [depth] at h; omega
      simp [parse, tokens, FiniteTables.decode₂, ih f suffix hh]
  | load t q ih =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f =>
      have hh : depth q ≤ f := by simp [depth] at h; omega
      simp [parse, tokens, FiniteTables.decode₁, ih f suffix hh]
  | branch t a b iha ihb =>
    cases fuel with
    | zero => simp [depth] at h
    | succ f =>
      have ha : depth a ≤ f := by simp [depth] at h; omega
      have hb : depth b ≤ f := by simp [depth] at h; omega
      simp [parse, tokens, FiniteTables.decode₁, List.append_assoc,
        iha f (tokens b ++ suffix) ha, ihb f suffix hb]

theorem depth_le_tokens_length (q : Code) : depth q ≤ (tokens q).length := by
  induction q with
  | halt => simp [depth, tokens]
  | goto t => simp [depth, tokens]
  | push k t q ih => simp [depth, tokens] at *; omega
  | peek k t q ih => simp [depth, tokens] at *; omega
  | pop k t q ih => simp [depth, tokens] at *; omega
  | load t q ih => simp [depth, tokens] at *; omega
  | branch t a b iha ihb => simp [depth, tokens] at *; omega

/-- Reject a trailing suffix so only one complete statement is accepted. -/
def decodeTokens (xs : List Nat) : Option Code :=
  match parse xs.length xs with
  | some (q, []) => some q
  | _ => none

theorem decodeTokens_tokens (q : Code) : decodeTokens (tokens q) = some q := by
  unfold decodeTokens
  have h := parse_tokens q (tokens q).length [] (depth_le_tokens_length q)
  simp only [List.append_nil] at h
  rw [h]

instance : Encodable Code := Encodable.ofLeftInjection tokens decodeTokens decodeTokens_tokens

/-- Total enumeration; malformed numeric inputs return `none`. -/
def decode (e : Nat) : Option Code := Encodable.decode e

theorem decode_coverage (q : Code) : decode (Encodable.encode q) = some q := Encodable.encodek q

example : parse 0 [0] = none := rfl
example : decodeTokens [] = none := rfl
example : decodeTokens [7] = none := rfl
example : decodeTokens [0, 0] = none := rfl
example : parse 1 [2] = none := rfl

end Shared.Codes.TM2Statements
