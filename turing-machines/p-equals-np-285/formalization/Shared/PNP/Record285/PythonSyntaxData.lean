import Shared.PNP.Record285.PythonSyntax

/-! Untrusted syntax proposal generated from the frozen Python source. -/
namespace Shared.PNP.Record285.PythonSyntax

def sourceHeader : String := "\"\"\"Alternative complete P=NP source: a clocked universal NP reference language.\n\nEvery candidate is deterministic (choice zero).  Reference membership uses\nbounded nondeterministic choices.  Compare equality, not complementation.\n\"\"\"\n\n"

def lines0 : List Line := [
  .function "accept" ["e", "initial", "clock", "branches"],
  .while_ 4 (.name "branches"),
  .aug 8 "branches" "-" (.num 1),
  .assignMany 8 ["left", "right", "state", "steps", "choices"] [(.num 0), (.name "initial"), (.num 1), (.name "clock"), (.name "branches")],
  .assignMany 8 ["read", "right"] [(.binary .mod (.name "right") (.num 2)), (.binary .div (.name "right") (.num 2))]
]

def lines1 : List Line := [
  .while_ 8 (.name "steps"),
  .aug 12 "steps" "-" (.num 1),
  .assignMany 12 ["choice", "choices"] [(.binary .mod (.name "choices") (.num 2)), (.binary .div (.name "choices") (.num 2))],
  .assignMany 12 ["digit", "place"] [(.name "e"), (.binary .add (.binary .add (.name "state") (.binary .mul (.num 2) (.name "read"))) (.name "choice"))],
  .while_ 12 (.name "place")
]

def lines2 : List Line := [
  .aug 16 "place" "-" (.num 1),
  .assign 16 "state" (.num 0),
  .while_ 16 (.binary .mod (.name "digit") (.num 2)),
  .aug 20 "state" "+" (.num 1),
  .aug 20 "digit" "//" (.num 2)
]

def lines3 : List Line := [
  .aug 16 "digit" "//" (.num 2),
  .assignMany 12 ["write", "state"] [(.binary .mod (.name "state") (.num 2)), (.binary .div (.name "state") (.num 2))],
  .assignMany 12 ["direction", "state"] [(.binary .mod (.name "state") (.num 2)), (.binary .div (.name "state") (.num 2))],
  .if_ 12 (.name "direction"),
  .assignMany 16 ["left", "right"] [(.name "right"), (.name "left")]
]

def lines4 : List Line := [
  .assign 12 "left" (.binary .add (.binary .mul (.num 2) (.name "left")) (.name "write")),
  .assignMany 12 ["read", "right"] [(.binary .mod (.name "right") (.num 2)), (.binary .div (.name "right") (.num 2))],
  .if_ 12 (.binary .eq (.name "state") (.num 0)),
  .return_ 16 (.num 1),
  .return_ 4 (.num 0)
]

def lines5 : List Line := [
  .blank,
  .function "main" [],
  .assignMany 4 ["program", "exponent"] [(.num 0), (.num 1)],
  .while_ 4 (.truth),
  .call 8 "beep"
]

def lines6 : List Line := [
  .assignMany 8 ["n", "radix", "remaining"] [(.num 0), (.num 1), (.num 0)],
  .while_ 8 (.truth),
  .assign 12 "expected" (.num 0),
  .assign 12 "branches" (.name "radix"),
  .while_ 12 (.name "branches")
]

def lines7 : List Line := [
  .aug 16 "branches" "-" (.num 1),
  .assign 16 "left" (.num 0),
  .assign 16 "right" (.num 0),
  .assign 16 "state" (.num 0),
  .assign 16 "steps" (.name "n")
]

def lines8 : List Line := [
  .assign 16 "choices" (.name "branches"),
  .while_ 16 (.name "steps"),
  .aug 20 "steps" "-" (.num 1),
  .if_ 20 (.binary .mod (.name "choices") (.num 2)),
  .aug 24 "state" "+" (.num 1)
]

def lines9 : List Line := [
  .aug 20 "choices" "//" (.num 2),
  .assign 20 "digit" (.binary .add (.name "radix") (.name "remaining")),
  .while_ 20 (.name "state"),
  .aug 24 "state" "-" (.num 1),
  .while_ 24 (.binary .mod (.name "digit") (.num 2))
]

def lines10 : List Line := [
  .aug 28 "digit" "//" (.num 2),
  .aug 24 "digit" "//" (.num 2),
  .assignMany 20 ["write", "direction", "state"] [(.num 0), (.num 0), (.num 0)],
  .while_ 20 (.binary .mod (.name "digit") (.num 2)),
  .aug 24 "digit" "//" (.num 2)
]

def lines11 : List Line := [
  .if_ 24 (.name "write"),
  .assign 28 "write" (.num 0),
  .if_ 28 (.name "direction"),
  .assign 32 "direction" (.num 0),
  .aug 32 "state" "+" (.num 1)
]

def lines12 : List Line := [
  .else_ 28,
  .assign 32 "direction" (.num 1),
  .else_ 24,
  .assign 28 "write" (.num 1),
  .aug 20 "digit" "//" (.num 2)
]

def lines13 : List Line := [
  .if_ 20 (.name "direction"),
  .assign 24 "direction" (.num 0),
  .assignMany 24 ["left", "right"] [(.name "right"), (.name "left")],
  .aug 20 "left" "*" (.num 2),
  .if_ 20 (.name "write")
]

def lines14 : List Line := [
  .assign 24 "write" (.num 0),
  .aug 24 "left" "+" (.num 1),
  .if_ 20 (.name "state"),
  .aug 24 "state" "-" (.num 1),
  .if_ 24 (.binary .mod (.name "right") (.num 2))
]

def lines15 : List Line := [
  .aug 28 "state" "+" (.num 2),
  .aug 24 "right" "//" (.num 2),
  .else_ 20,
  .aug 24 "right" "//" (.num 2),
  .assign 24 "expected" (.num 1)
]

def lines16 : List Line := [
  .assign 24 "branches" (.num 0),
  .break_ 24,
  .assign 12 "steps" (.binary .pow (.binary .add (.name "n") (.num 2)) (.name "exponent")),
  .assign 12 "left" (.num 0),
  .assign 12 "state" (.num 0)
]

def lines17 : List Line := [
  .assign 12 "right" (.binary .mul (.name "remaining") (.name "radix")),
  .assign 12 "right" (.binary .add (.binary .mul (.num 2) (.name "right")) (.name "radix")),
  .aug 12 "right" "-" (.num 1),
  .if_ 12 (.binary .mod (.name "right") (.num 2)),
  .aug 16 "state" "+" (.num 2)
]

def lines18 : List Line := [
  .aug 12 "right" "//" (.num 2),
  .while_ 12 (.name "steps"),
  .aug 16 "steps" "-" (.num 1),
  .assign 16 "digit" (.name "program"),
  .while_ 16 (.name "state")
]

def lines19 : List Line := [
  .aug 20 "state" "-" (.num 1),
  .while_ 20 (.binary .mod (.name "digit") (.num 2)),
  .aug 24 "digit" "//" (.num 2),
  .aug 20 "digit" "//" (.num 2),
  .assignMany 16 ["write", "direction", "state"] [(.num 0), (.num 0), (.num 0)]
]

def lines20 : List Line := [
  .while_ 16 (.binary .mod (.name "digit") (.num 2)),
  .aug 20 "digit" "//" (.num 2),
  .if_ 20 (.name "write"),
  .assign 24 "write" (.num 0),
  .if_ 24 (.name "direction")
]

def lines21 : List Line := [
  .assign 28 "direction" (.num 0),
  .aug 28 "state" "+" (.num 1),
  .else_ 24,
  .assign 28 "direction" (.num 1),
  .else_ 20
]

def lines22 : List Line := [
  .assign 24 "write" (.num 1),
  .aug 16 "digit" "//" (.num 2),
  .if_ 16 (.name "direction"),
  .assign 20 "direction" (.num 0),
  .assignMany 20 ["left", "right"] [(.name "right"), (.name "left")]
]

def lines23 : List Line := [
  .aug 16 "left" "*" (.num 2),
  .if_ 16 (.name "write"),
  .assign 20 "write" (.num 0),
  .aug 20 "left" "+" (.num 1),
  .if_ 16 (.name "state")
]

def lines24 : List Line := [
  .aug 20 "state" "-" (.num 1),
  .if_ 20 (.binary .mod (.name "right") (.num 2)),
  .aug 24 "state" "+" (.num 2),
  .aug 20 "right" "//" (.num 2),
  .else_ 16
]

def lines25 : List Line := [
  .aug 20 "right" "//" (.num 2),
  .if_ 20 (.name "expected"),
  .assign 24 "expected" (.num 0),
  .else_ 20,
  .assign 24 "expected" (.num 1)
]

def lines26 : List Line := [
  .break_ 20,
  .if_ 12 (.name "expected"),
  .break_ 16,
  .if_ 12 (.name "remaining"),
  .aug 16 "remaining" "-" (.num 1)
]

def lines27 : List Line := [
  .else_ 12,
  .aug 16 "radix" "*" (.num 2),
  .aug 16 "n" "+" (.num 1),
  .assign 16 "remaining" (.name "radix"),
  .aug 16 "remaining" "-" (.num 1)
]

def lines28 : List Line := [
  .if_ 8 (.name "program"),
  .aug 12 "program" "-" (.num 1),
  .aug 12 "exponent" "+" (.num 1),
  .else_ 8,
  .assign 12 "program" (.name "exponent")
]

def lines29 : List Line := [
  .assign 12 "exponent" (.num 1)
]

def linesFrom30 : List Line := []
def linesFrom29 : List Line := lines29 ++ linesFrom30
def linesFrom28 : List Line := lines28 ++ linesFrom29
def linesFrom27 : List Line := lines27 ++ linesFrom28
def linesFrom26 : List Line := lines26 ++ linesFrom27
def linesFrom25 : List Line := lines25 ++ linesFrom26
def linesFrom24 : List Line := lines24 ++ linesFrom25
def linesFrom23 : List Line := lines23 ++ linesFrom24
def linesFrom22 : List Line := lines22 ++ linesFrom23
def linesFrom21 : List Line := lines21 ++ linesFrom22
def linesFrom20 : List Line := lines20 ++ linesFrom21
def linesFrom19 : List Line := lines19 ++ linesFrom20
def linesFrom18 : List Line := lines18 ++ linesFrom19
def linesFrom17 : List Line := lines17 ++ linesFrom18
def linesFrom16 : List Line := lines16 ++ linesFrom17
def linesFrom15 : List Line := lines15 ++ linesFrom16
def linesFrom14 : List Line := lines14 ++ linesFrom15
def linesFrom13 : List Line := lines13 ++ linesFrom14
def linesFrom12 : List Line := lines12 ++ linesFrom13
def linesFrom11 : List Line := lines11 ++ linesFrom12
def linesFrom10 : List Line := lines10 ++ linesFrom11
def linesFrom9 : List Line := lines9 ++ linesFrom10
def linesFrom8 : List Line := lines8 ++ linesFrom9
def linesFrom7 : List Line := lines7 ++ linesFrom8
def linesFrom6 : List Line := lines6 ++ linesFrom7
def linesFrom5 : List Line := lines5 ++ linesFrom6
def linesFrom4 : List Line := lines4 ++ linesFrom5
def linesFrom3 : List Line := lines3 ++ linesFrom4
def linesFrom2 : List Line := lines2 ++ linesFrom3
def linesFrom1 : List Line := lines1 ++ linesFrom2
def linesFrom0 : List Line := lines0 ++ linesFrom1

def sourceLines : List Line := linesFrom0
def renderedSource : String := sourceHeader ++ renderLines sourceLines
def literalSource : String := include_str "selected_source.py"

end Shared.PNP.Record285.PythonSyntax
