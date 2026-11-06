import Shared.Beeping.NPcoNP.Table284Ascii

/-! A compositional certificate for the row portion of the restricted event
table parser.  It permits separate proofs for finite contiguous chunks while
retaining both read rows, the ordered source index, destination bounds and
the complete suffix. No particular source text or table is asserted here. -/

namespace Shared.Beeping.NPcoNP.Table284Ascii.RowCert
open Shared.Beeping.TableBits

/-- Both rows of a state parse to exactly the supplied raw pair. -/
structure PairCorrect (n i : Nat) (a b : List Char) (p : RawPair) : Prop where
  first : row a = some (i, false, p.1)
  second : row b = some (i, true, p.2)
  state_lt : i < n
  first_target_lt : p.1.2.2.1 < n
  second_target_lt : p.2.2.2.1 < n

/-- A contiguous, ordered sequence of complete row pairs. -/
inductive Chunk (n : Nat) : Nat → List (List Char) → List RawPair → Nat → Prop
  | nil (i : Nat) : Chunk n i [] [] i
  | cons {i j : Nat} {a b : List Char} {p : RawPair}
      {lines : List (List Char)} {pairs : List RawPair} :
      PairCorrect n i a b p → Chunk n (i+1) lines pairs j →
      Chunk n i (a :: b :: lines) (p :: pairs) j

theorem rows_cons (n i : Nat) (a b : List Char) (p : RawPair)
    (rest : List (List Char)) (tail : List RawPair)
    (hc : PairCorrect n i a b p) (ht : rows n (i+1) rest = some tail) :
    rows n i (a :: b :: rest) = some (p :: tail) := by
  rcases hc with ⟨ha, hb, hi, hwa, hwb⟩
  cases p with
  | mk wa wb =>
    simp [rows, ha, hb, hi, hwa, hwb, ht]

/-- A proved chunk followed by a successful tail gives exactly the same full
result as the original parser. Thus no line can be silently dropped or
reordered when certificates are concatenated. -/
theorem rows_append (n i j : Nat) (lines : List (List Char))
    (pairs : List RawPair) (hc : Chunk n i lines pairs j)
    (rest : List (List Char)) (tail : List RawPair)
    (ht : rows n j rest = some tail) :
    rows n i (lines ++ rest) = some (pairs ++ tail) := by
  induction hc with
  | nil => simpa using ht
  | cons hp hchunk ih =>
    simp only [List.cons_append]
    exact rows_cons _ _ _ _ _ _ _ hp (ih ht)

/-- Separately proved adjacent chunks compose without reevaluating their
individual parser checks. -/
theorem Chunk.append {n i j k : Nat} {lines₁ lines₂ : List (List Char)}
    {pairs₁ pairs₂ : List RawPair}
    (h₁ : Chunk n i lines₁ pairs₁ j) (h₂ : Chunk n j lines₂ pairs₂ k) :
    Chunk n i (lines₁ ++ lines₂) (pairs₁ ++ pairs₂) k := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hp hchunk ih =>
    simp only [List.cons_append]
    exact .cons hp (ih h₂)

/-- A complete chunk with a single final newline parses to its exact rows. -/
theorem rows_complete (n i : Nat) (lines : List (List Char))
    (pairs : List RawPair) (hc : Chunk n i lines pairs n) :
    rows n i (lines ++ [[]]) = some pairs := by
  have ht : rows n n [[]] = some [] := by simp [rows]
  simpa using rows_append n i n lines pairs hc [[]] [] ht

end Shared.Beeping.NPcoNP.Table284Ascii.RowCert
