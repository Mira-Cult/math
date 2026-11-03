import Shared.PNP.Record285.Source

/-! Executable trace for the independent source comparison. This is regression
evidence only, not a proof of source equivalence or physical execution. -/
namespace Shared.PNP.Record285.SourceFixtures
open Shared.PNP.Record285.Source

def comparisons (count : Nat) : SearchState → List (Nat × Nat × Nat × Nat × Nat × Bool)
  | s => match count with
    | 0 => []
    | count+1 =>
      let rest := comparisons count (controllerStep s).1
      match s.phase with
      | .begin => rest
      | .compare => (s.program, s.exponent, s.n, s.radix, s.remaining,
          mismatch s.program s.exponent s.n s.radix s.remaining) :: rest

#eval comparisons 280 ⟨0,1,0,1,0,.begin⟩
end Shared.PNP.Record285.SourceFixtures
