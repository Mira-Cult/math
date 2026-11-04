import Shared.PNP.Record285.Source

/-! A small concrete-syntax tree for the Python subset used by the frozen
producer. The data and its exact-text certificate are supplied separately.
This file gives syntax and rendering only, not Python execution semantics. -/
set_option maxRecDepth 8192
namespace Shared.PNP.Record285.PythonSyntax

inductive Op where
  | add | sub | mul | div | mod | pow | eq
  deriving DecidableEq, Repr

def Op.text : Op → String
  | .add => " + " | .sub => " - " | .mul => " * " | .div => " // "
  | .mod => " % " | .pow => " ** " | .eq => " == "

def Op.priority : Op → Nat
  | .eq => 1 | .add | .sub => 2 | .mul | .div | .mod => 3 | .pow => 4

inductive Expr where
  | name : String → Expr
  | num : Nat → Expr
  | truth : Expr
  | binary : Op → Expr → Expr → Expr
  deriving DecidableEq, Repr

def Expr.priority : Expr → Nat
  | .binary op _ _ => op.priority
  | _ => 5

/-- Parentheses preserve the typed expression tree according to Python's
precedence and associativity for the operators used by the frozen source. -/
def Expr.render : Expr → String
  | .name s => s
  | .num n => toString n
  | .truth => "True"
  | .binary op a b =>
      let pa := if op = .pow then op.priority+1 else op.priority
      let pb := if op = .pow then op.priority else op.priority+1
      let left := if a.priority < pa then "(" ++ a.render ++ ")" else a.render
      let right := if b.priority < pb then "(" ++ b.render ++ ")" else b.render
      left ++ op.text ++ right

def indent (n : Nat) : String := String.ofList (List.replicate n ' ')

inductive Line where
  | function : String → List String → Line
  | blank : Line
  | while_ : Nat → Expr → Line
  | if_ : Nat → Expr → Line
  | else_ : Nat → Line
  | assign : Nat → String → Expr → Line
  | assignMany : Nat → List String → List Expr → Line
  | aug : Nat → String → String → Expr → Line
  | call : Nat → String → Line
  | return_ : Nat → Expr → Line
  | break_ : Nat → Line
  deriving DecidableEq, Repr

def Line.render : Line → String
  | .function name args => "def " ++ name ++ "(" ++ String.intercalate ", " args ++ "):\n"
  | .blank => "\n"
  | .while_ i e => indent i ++ "while " ++ e.render ++ ":\n"
  | .if_ i e => indent i ++ "if " ++ e.render ++ ":\n"
  | .else_ i => indent i ++ "else:\n"
  | .assign i name e => indent i ++ name ++ " = " ++ e.render ++ "\n"
  | .assignMany i names values => indent i ++ String.intercalate ", " names ++ " = (" ++
      String.intercalate ", " (values.map Expr.render) ++ ")\n"
  | .aug i name op e => indent i ++ name ++ " " ++ op ++ "= " ++ e.render ++ "\n"
  | .call i name => indent i ++ name ++ "()\n"
  | .return_ i e => indent i ++ "return " ++ e.render ++ "\n"
  | .break_ i => indent i ++ "break\n"

def renderLines (lines : List Line) : String := String.join (lines.map Line.render)

end Shared.PNP.Record285.PythonSyntax
