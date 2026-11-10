import PASoundness.M236OccurrenceGraphData
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.OccurrenceGraph
open PASoundness.M236
open PASoundness.M236.Control

def paths : Array (List Bool) := Grammar.completePaths.toArray

def resolveWith (rule : List Bool → Option (List Bool)) (word : List Bool) : Option (List Bool) :=
  (rule word).bind (Control.resolveZeros Grammar.nodes 158 157)

def isDec (name : String) : Bool :=
  name == "3.scratch.copy.decnz" || name == "3.k.stage.decnz" || name == "3.k.rest.decnz" ||
  name == "3.k.count.decnz" || name == "3.k.top.decnz" || name == "3.k.env.decnz" ||
  name == "3.k.a.decnz" || name == "3.k.b.decnz" || name == "3.k.c.decnz"

def rowMatches (i : Nat) : Bool :=
  match sourceRows[i]?, paths[i]? with
  | some (op, dest, extra), some word =>
    let target := paths[dest]?
    target.isSome && (match Continue.pathName 157 word with
    | some "_continue.1" => op == "jump" && extra == none && resolveWith (Continue.restartPrefix 1) word == target
    | some "_continue.2" => op == "jump" && extra == none && resolveWith (Continue.restartPrefix 2) word == target
    | some "_continue.3" => op == "jump" && extra == none && resolveWith (Continue.restartPrefix 3) word == target
    | some "_break.1" => op == "jump" && extra == none && resolveWith (Break.successorPrefix 1) word == target
    | some "_break.3" => op == "jump" && extra == none && resolveWith (Break.successorPrefix 3) word == target
    | some "emit.0" => op == "emit.0" && extra == none && resolveWith (Break.successorPrefix 0) word == target
    | some "emit.1" => op == "emit.1" && extra == none && resolveWith (Break.successorPrefix 0) word == target
    | some name => op == name && dest == (i+1)%760 &&
      if isDec name then
        match Control.decodeZero word, extra with
        | some (_, tail), some z => paths[z]?.isSome && (Control.resolveZeros Grammar.nodes 158 157 tail == paths[z]?)
        | _, _ => false
      else extra == none
    | none => false)
  | _, _ => false

/-- Literal operation names classify all nine register decrement entries. -/
theorem decrement_names_checked : ∀ r : Fin 9,
    isDec ("3." ++ Selector.registerNames[r] ++ ".decnz") = true ∧
    isDec ("3." ++ Selector.registerNames[r] ++ ".inc") = false := by decide

theorem graph_size : sourceRows.size = 760 := by decide

theorem check_000 : (List.range 100).all (fun j => rowMatches (0 + j)) = true := by decide
theorem check_100 : (List.range 100).all (fun j => rowMatches (100 + j)) = true := by decide
theorem check_200 : (List.range 100).all (fun j => rowMatches (200 + j)) = true := by decide
theorem check_300 : (List.range 100).all (fun j => rowMatches (300 + j)) = true := by decide
theorem check_400 : (List.range 100).all (fun j => rowMatches (400 + j)) = true := by decide
theorem check_500 : (List.range 100).all (fun j => rowMatches (500 + j)) = true := by decide
theorem check_600 : (List.range 100).all (fun j => rowMatches (600 + j)) = true := by decide
theorem check_700 : (List.range 60).all (fun j => rowMatches (700 + j)) = true := by decide

/-- Every source-graph witness row agrees with the literal grammar's
occurrence, both decrement branches, resolved jumps and output destination. -/
theorem every_occurrence_checked (i : Nat) (hi : i < 760) : rowMatches i = true := by
  by_cases h0 : i < 100
  · have h := (List.all_eq_true.mp check_000) (i - 0) (List.mem_range.mpr (by omega))
    have heq : 0 + (i - 0) = i := by omega
    simpa only [heq] using h
  by_cases h100 : i < 200
  · have h := (List.all_eq_true.mp check_100) (i - 100) (List.mem_range.mpr (by omega))
    have heq : 100 + (i - 100) = i := by omega
    simpa only [heq] using h
  by_cases h200 : i < 300
  · have h := (List.all_eq_true.mp check_200) (i - 200) (List.mem_range.mpr (by omega))
    have heq : 200 + (i - 200) = i := by omega
    simpa only [heq] using h
  by_cases h300 : i < 400
  · have h := (List.all_eq_true.mp check_300) (i - 300) (List.mem_range.mpr (by omega))
    have heq : 300 + (i - 300) = i := by omega
    simpa only [heq] using h
  by_cases h400 : i < 500
  · have h := (List.all_eq_true.mp check_400) (i - 400) (List.mem_range.mpr (by omega))
    have heq : 400 + (i - 400) = i := by omega
    simpa only [heq] using h
  by_cases h500 : i < 600
  · have h := (List.all_eq_true.mp check_500) (i - 500) (List.mem_range.mpr (by omega))
    have heq : 500 + (i - 500) = i := by omega
    simpa only [heq] using h
  by_cases h600 : i < 700
  · have h := (List.all_eq_true.mp check_600) (i - 600) (List.mem_range.mpr (by omega))
    have heq : 600 + (i - 600) = i := by omega
    simpa only [heq] using h
  have h := (List.all_eq_true.mp check_700) (i - 700) (List.mem_range.mpr (by omega))
  have heq : 700 + (i - 700) = i := by omega
  simpa only [heq] using h
end PASoundness.M236.OccurrenceGraph
