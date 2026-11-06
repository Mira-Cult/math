import Shared.Beeping.NPcoNP.Grammar284OperationLeaf
import Shared.Beeping.NPcoNP.Grammar284Types

/-! Parameterized exact-layout pair/node-list parser: no file-byte assertion. -/
namespace Shared.Beeping.NPcoNP.Grammar284NodePairs
open Shared.Beeping.NPcoNP.Grammar284
open Shared.Beeping.NPcoNP.Grammar284OperationLeaf (strip strip_append)

abbrev Parser := List Char → Option (Leaf × List Char)
abbrev Renderer := Leaf → List Char

def openPair : List Char := "    [\n".toList
def sepPair : List Char := ",\n".toList
def closePair : List Char := "\n    ]".toList

def renderPair (render : Renderer) (p : Leaf × Leaf) : List Char :=
  openPair ++ render p.1 ++ sepPair ++ render p.2 ++ closePair

def parsePair (parse : Parser) (input : List Char) : Option ((Leaf × Leaf) × List Char) := do
  let s ← strip openPair input
  let (a,s) ← parse s
  let s ← strip sepPair s
  let (b,s) ← parse s
  let s ← strip closePair s
  some ((a,b),s)

theorem parsePair_render (parse : Parser) (render : Renderer) (good : Leaf → Prop)
    (hp : ∀ a tail, good a → parse (render a ++ tail) = some (a,tail))
    (p : Leaf × Leaf) (ha : good p.1) (hb : good p.2) (tail : List Char) :
    parsePair parse (renderPair render p ++ tail) = some (p,tail) := by
  cases p with
  | mk a b =>
    simp only at ha hb
    simp [parsePair, renderPair, List.append_assoc, strip_append, hp a _ ha, hp b _ hb]

/-- Commas are separators only: no trailing comma appears after the last pair. -/
def renderNodes (render : Renderer) : List (Leaf × Leaf) → List Char
  | [] => []
  | [p] => renderPair render p
  | p :: q :: rest => renderPair render p ++ sepPair ++ renderNodes render (q :: rest)

def parseNodes (parse : Parser) : Nat → List Char → Option (List (Leaf × Leaf) × List Char)
  | 0, s => some ([],s)
  | n+1, s => do
      let (p,s) ← parsePair parse s
      if n = 0 then some ([p],s) else do
        let s ← strip sepPair s
        let (ps,s) ← parseNodes parse n s
        some (p::ps,s)

theorem parseNodes_render (parse : Parser) (render : Renderer) (good : Leaf → Prop)
    (hp : ∀ a tail, good a → parse (render a ++ tail) = some (a,tail))
    (ps : List (Leaf × Leaf)) (hps : ∀ p ∈ ps, good p.1 ∧ good p.2) (tail : List Char) :
    parseNodes parse ps.length (renderNodes render ps ++ tail) = some (ps,tail) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have hp1 := hps p (by simp)
    have hrest : ∀ q ∈ ps, good q.1 ∧ good q.2 := by
      intro q hq
      exact hps q (by simp [hq])
    cases ps with
    | nil =>
      simp only [List.length_cons, List.length_nil, parseNodes, Nat.zero_eq, ↓reduceIte,
        renderNodes]
      rw [parsePair_render parse render good hp p hp1.1 hp1.2 tail]
      rfl
    | cons q rest =>
      have hlen : 0 < (q :: rest).length := by simp
      simp only [List.length_cons, parseNodes, renderNodes, List.append_assoc]
      rw [parsePair_render parse render good hp p hp1.1 hp1.2]
      simp only [bind, Option.bind, strip_append]
      have hi := ih hrest
      simp only [List.length_cons, parseNodes, bind, Option.bind] at hi
      simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte]
      rw [hi]

end Shared.Beeping.NPcoNP.Grammar284NodePairs
