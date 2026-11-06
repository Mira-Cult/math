import Mathlib.Tactic

/-! Syntax of the finite control-grammar DAG. These are data types only;
identification with producer bytes is a separate checked obligation. -/
namespace Shared.Beeping.NPcoNP.Grammar284

inductive Leaf where
  | node (n : Nat)
  | op (s : String)
  deriving DecidableEq, Repr, Inhabited

structure Grammar where
  nodes : Array (Leaf × Leaf)
  registers : Array String
  root : Nat
  deriving DecidableEq, Repr, Inhabited

end Shared.Beeping.NPcoNP.Grammar284
