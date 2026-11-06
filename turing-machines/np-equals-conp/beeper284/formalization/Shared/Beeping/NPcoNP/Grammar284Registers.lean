import Shared.Beeping.NPcoNP.Grammar284OperationLeaf
import Shared.Beeping.NPcoNP.Grammar284SourceRender

/-! A fixed-count parser for the selected register-array layout. It does not bind source bytes or assert a complete JSON parser. -/
namespace Shared.Beeping.NPcoNP.Grammar284Registers
open Shared.Beeping.NPcoNP
open Shared.Beeping.NPcoNP.Grammar284Quoted
open Shared.Beeping.NPcoNP.Grammar284OperationLeaf (strip strip_append)

/-- Exact indented register-item renderer; a comma follows each nonfinal item. -/
def render : List (List Char) → List Char
  | [] => []
  | name :: rest => "    ".toList ++ Grammar284Quoted.render name ++
      (if rest.isEmpty then "\n".toList else ",\n".toList) ++ render rest

/-- Consume exactly `n` register items, with arbitrary trailing input. -/
def parse : Nat → List Char → Option (List (List Char) × List Char)
  | 0, input => some ([], input)
  | n+1, input => do
    let rest ← strip "    ".toList input
    let (name, rest) ← Grammar284Quoted.parse rest
    let rest ← strip (if n = 0 then "\n".toList else ",\n".toList) rest
    let (names, tail) ← parse n rest
    some (name :: names, tail)

set_option maxHeartbeats 1000000 in
theorem parse_render (names : List (List Char)) (tail : List Char)
    (hs : ∀ name ∈ names, safe name = true) :
    parse names.length (render names ++ tail) = some (names, tail) := by
  induction names with
  | nil => rfl
  | cons name rest ih =>
    have hn : safe name = true := hs name (by simp)
    have hr : ∀ x ∈ rest, safe x = true := by
      intro x hx
      exact hs x (by simp [hx])
    have he : (if rest.isEmpty then "\n".toList else ",\n".toList) =
        (if rest.length = 0 then "\n".toList else ",\n".toList) := by
      cases rest <;> rfl
    simp only [List.length_cons, parse, render, List.append_assoc, he]
    rw [strip_append]
    simp only [bind, Option.bind]
    rw [Grammar284Quoted.parse_render name _ hn]
    simp only [bind, Option.bind]
    rw [strip_append]
    simp only [bind, Option.bind]
    rw [ih hr]

example : parse 2 (render ["a".toList, "bc".toList] ++ "suffix".toList) =
    some (["a".toList, "bc".toList], "suffix".toList) := by decide

open Shared.Beeping.NPcoNP.Grammar284

theorem source_register (s : String) :
    SourceRender.register s = "    ".toList ++ Grammar284Quoted.render s.toList := by
  rfl

theorem render_eq_source (ss : List String) (hne : ss ≠ []) :
    render (ss.map String.toList) = SourceRender.join (ss.map SourceRender.register) ++ "\n".toList := by
  induction ss with
  | nil => contradiction
  | cons s rest ih =>
    cases rest with
    | nil => simp [render, SourceRender.join, source_register, List.append_assoc]
    | cons t ts =>
      have ht := ih (by simp)
      change ("    ".toList ++ Grammar284Quoted.render s.toList ++ ",\n".toList ++
        render ((t :: ts).map String.toList)) = _
      rw [ht]
      simp [SourceRender.join, source_register, List.append_assoc]

end Shared.Beeping.NPcoNP.Grammar284Registers
