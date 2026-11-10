import PASoundness.CompactMatrix
import PASoundness.CompactProof

/-!
Independent source-comparison vectors. These executable probes are not proofs
of the Python/Lean correspondence. Universal symbolic theorems and remaining
source-stack/interpretation obligations are documented separately.

Run through `code/review_source.py`; no randomness or external input is used.
The five output lines are decimal JSON arrays, never pretty-printer truncations.
-/
namespace PASoundness.ReferenceVectors

private def matrixResult : Option Bool → Nat
  | none => 2
  | some false => 0
  | some true => 1

def matrixVectors (ρ : CompactMatrix.Environment) : List Nat :=
  (List.range 64).map fun code => matrixResult (CompactMatrix.evalQF ρ (CompactMatrix.decode code))

def theoremVectors : List Nat := (List.range 64).map CompactProof.theoremCode

def axiomVectors : List Nat :=
  (List.range 9).flatMap fun s =>
  (List.range 2).flatMap fun a =>
  (List.range 2).flatMap fun b =>
  (List.range 2).flatMap fun c =>
  (List.range 2).map fun u => CompactProof.axiomCode s a b c u

def emitArray (xs : List Nat) : IO Unit :=
  IO.println ("[" ++ String.intercalate "," (xs.map toString) ++ "]")

end PASoundness.ReferenceVectors

def main (args : List String) : IO Unit := do
  let zero : PASoundness.CompactMatrix.Environment := fun _ => 0
  PASoundness.ReferenceVectors.emitArray (PASoundness.ReferenceVectors.matrixVectors zero)
  PASoundness.ReferenceVectors.emitArray
    (PASoundness.ReferenceVectors.matrixVectors (fun x => if x = 0 then 1 else 0))
  PASoundness.ReferenceVectors.emitArray (PASoundness.ReferenceVectors.matrixVectors
    (PASoundness.CompactMatrix.bind [0, 0] [1, 0] zero))
  PASoundness.ReferenceVectors.emitArray PASoundness.ReferenceVectors.theoremVectors
  if args.contains "--axioms" then
    PASoundness.ReferenceVectors.emitArray PASoundness.ReferenceVectors.axiomVectors
