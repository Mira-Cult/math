import Shared.PNP.Record285.GrammarTextCertificate

/-! Tie the exact frozen JSON suffix to the explicit root and ordered
register names; the full file binding uses only kernel-reduced data. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.Grammar

def rootIndex : Nat := 162

def registerName (i : Nat) : String := "$coalesced." ++ toString i

def renderRegister (i : Nat) : List Char :=
  ("    \"" ++ registerName i ++ "\"" ++ (if i = 14 then "\n" else ",\n")).toList

def renderRegisters : List Nat → List Char
  | [] => []
  | i::is => renderRegister i ++ renderRegisters is

def renderedSuffix : List Char :=
  "  ],\n  \"registers\": [\n".toList ++ renderRegisters (List.range 15) ++
    ("  ],\n  \"root\": " ++ toString rootIndex ++ "\n}\n").toList

theorem suffix_exact : suffixChars = renderedSuffix := by decide

/-- The frozen bytes are exactly the typed nodes followed by the ordered
register list and root index used in the physical-graph theorem. -/
theorem literal_typed_serialization :
    literal = String.ofList (headerChars ++ renderEntries entries ++ renderedSuffix) := by
  rw [← suffix_exact]
  exact literal_serialization

end Shared.PNP.Record285.Grammar
