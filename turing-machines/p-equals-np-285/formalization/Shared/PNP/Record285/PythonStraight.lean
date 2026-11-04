import Shared.PNP.Record285.PythonSyntaxData

/-! Executable partial semantics for straight-line natural-number Python
operations. Subtraction underflow and division by zero return `none` instead
of silently changing Python integer semantics; initialized variables are
supplied by a total store. This is not a semantics for all of Python. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace Shared.PNP.Record285.PythonStraight
open Shared.PNP.Record285.PythonSyntax

abbrev Store := String → Nat

def put (s : Store) (name : String) (value : Nat) : Store :=
  fun key => if key = name then value else s key

/-- Checked operations: partial cases are made explicit. -/
def op (o : Op) (a b : Nat) : Option Nat :=
  match o with
  | .add => some (a+b)
  | .sub => if b ≤ a then some (a-b) else none
  | .mul => some (a*b)
  | .div => if b=0 then none else some (a/b)
  | .mod => if b=0 then none else some (a%b)
  | .pow => some (a^b)
  | .eq => some (if a=b then 1 else 0)

def eval (s : Store) : Expr → Option Nat
  | .name name => some (s name)
  | .num value => some value
  | .truth => some 1
  | .binary o a b => do
      let x ← eval s a
      let y ← eval s b
      op o x y

/-- Evaluate all tuple RHS expressions before performing any assignment. -/
def values (s : Store) : List Expr → Option (List Nat)
  | [] => some []
  | e::es => do
      let x ← eval s e
      let xs ← values s es
      pure (x::xs)

def assignAll : Store → List String → List Nat → Option Store
  | s, [], [] => some s
  | s, n::ns, v::vs => assignAll (put s n v) ns vs
  | _, _, _ => none

def augOp : String → Option Op
  | "+" => some .add | "-" => some .sub | "*" => some .mul | "//" => some .div
  | _ => none

def simple (line : Line) (s : Store) : Option Store :=
  match line with
  | .assign _ name e => do
      let v ← eval s e
      pure (put s name v)
  | .assignMany _ names es => do
      let vs ← values s es
      assignAll s names vs
  | .aug _ name operator e => do
      let o ← augOp operator
      let v ← eval s e
      let result ← op o (s name) v
      pure (put s name result)
  | _ => none

def sequence : List Line → Store → Option Store
  | [], s => some s
  | line::lines, s => do
      let next ← simple line s
      sequence lines next

/-- A single Python `if` without `else`, whose body is one simple line. -/
def ifOne (condition body : Line) (s : Store) : Option Store :=
  match condition with
  | .if_ _ e => do
      let v ← eval s e
      if v=0 then pure s else simple body s
  | _ => none

/-- The entire typed block from `steps = ...` through the first candidate
head read; its line data is part of the kernel-bound source listing. -/
def candidateSetup (s : Store) : Option Store := do
  let a ← sequence (lines16.drop 2 ++ lines17.take 3) s
  let b ← ifOne (lines17[3]?.getD .blank) (lines17[4]?.getD .blank) a
  sequence (lines18.take 1) b

/-- A pair assignment evaluates both expressions in the original store. -/
theorem tuple_swap (s : Store) (x y : String) :
    simple (.assignMany 0 [x,y] [.name y,.name x]) s =
      some (put (put s x (s y)) y (s x)) := by rfl

end Shared.PNP.Record285.PythonStraight
