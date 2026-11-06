import Shared.ComplexityBridge.TM2LiteralEval
import Shared.ComplexityBridge.TM2CNFValidateTotal

namespace Shared.ComplexityBridge.RawCNFEval
open Shared.ComplexityBridge

/-- Evaluate literals inside one original clause frame. The option distinguishes
malformed data from a well-formed clause whose value is false. -/
def clause (vars : List (List Bool)) (witness raw : List Bool) : Option Bool :=
  (BitstringEncoding.undelimitBlocks raw).bind fun literals =>
    (literals.mapM (TM2LiteralEval.evaluate vars witness)).map (fun bs => bs.any id)

/-- Evaluate every original clause separately; an empty formula is true and an
empty clause is false. No clause-boundary flattening is used here. -/
def formula (vars : List (List Bool)) (witness raw : List Bool) : Option Bool :=
  (BitstringEncoding.undelimitBlocks raw).bind fun clauses =>
    (clauses.mapM (clause vars witness)).map (fun bs => bs.all id)

theorem mapM_option_map {α β γ : Type} (f : α → Option β) (g : β → γ) (xs : List α) :
    (xs.mapM (fun x => (f x).map g)) = (xs.mapM f).map (List.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x <;> cases hs : xs.mapM f <;> simp [List.mapM_cons,hf,hs,ih]

theorem literal_eq (vars : List (List Bool)) (witness raw : List Bool) :
    TM2LiteralEval.evaluate vars witness raw =
      ((BitstringEncoding.bitDecode raw : Option CNF.Literal).map
        (CNF.evalLiteral (CNF.assignment (vars.map Computability.decodeNat) witness))) := by
  cases h : (BitstringEncoding.bitDecode raw : Option CNF.Literal) with
  | none =>
    have he := (TM2LiteralEval.evaluate_none_iff vars witness raw).2 h
    simp [h,he]
  | some lit =>
    rw [TM2LiteralEval.evaluate_correct vars witness raw lit h]
    rfl

theorem clause_eq (vars : List (List Bool)) (witness raw : List Bool) :
    clause vars witness raw =
      ((BitstringEncoding.bitDecode raw : Option CNF.Clause).map
        (CNF.evalClause (CNF.assignment (vars.map Computability.decodeNat) witness))) := by
  change clause vars witness raw =
    ((BitstringEncoding.undelimitBlocks raw).bind (List.mapM (BitstringEncoding.bitDecode (α := CNF.Literal)))).map _
  unfold clause
  cases hb : BitstringEncoding.undelimitBlocks raw with
  | none => rfl
  | some lits =>
    simp only [Option.bind_some]
    have hfun : TM2LiteralEval.evaluate vars witness = fun raw =>
        ((BitstringEncoding.bitDecode raw : Option CNF.Literal).map
          (CNF.evalLiteral (CNF.assignment (vars.map Computability.decodeNat) witness))) := by
      funext raw; exact literal_eq vars witness raw
    rw [hfun,mapM_option_map]
    cases h : lits.mapM (BitstringEncoding.bitDecode (α := CNF.Literal)) with
    | none => rfl
    | some ls =>
      simp only [Option.map_some]
      simp [CNF.evalClause,List.any_map]

theorem formula_eq (vars : List (List Bool)) (witness raw : List Bool) :
    formula vars witness raw =
      ((CNF.parse raw).map
        (CNF.evalFormula (CNF.assignment (vars.map Computability.decodeNat) witness))) := by
  change formula vars witness raw =
    ((BitstringEncoding.undelimitBlocks raw).bind (List.mapM (BitstringEncoding.bitDecode (α := CNF.Clause)))).map _
  unfold formula
  cases hb : BitstringEncoding.undelimitBlocks raw with
  | none => rfl
  | some clauses =>
    simp only [Option.bind_some]
    have hfun : clause vars witness = fun raw =>
        ((BitstringEncoding.bitDecode raw : Option CNF.Clause).map
          (CNF.evalClause (CNF.assignment (vars.map Computability.decodeNat) witness))) := by
      funext raw; exact clause_eq vars witness raw
    rw [hfun,mapM_option_map]
    cases h : clauses.mapM (BitstringEncoding.bitDecode (α := CNF.Clause)) with
    | none => rfl
    | some cs =>
      simp only [Option.map_some]
      simp [CNF.evalFormula,List.all_map]

/-- Executable boundary-preserving certificate relation. Syntax validation is
performed before using the occurrence projection, whose flattening alone does
not validate the original clause boundaries. -/
def verify (input witness : List Bool) : Bool :=
  if TM2CNFValidate.validate input then
    match CNFOccurrences.project input with
    | true::frame =>
      match BitstringEncoding.undelimitBlocks frame with
      | some vars => (formula vars witness input).getD false
      | none => false
    | _ => false
  else false

/-- This concrete raw-bit specification agrees on all inputs with the
canonical certificate relation, including malformed CNFs. -/
theorem verify_eq (input witness : List Bool) :
    verify input witness = CNFWitness.verify (input,witness) := by
  cases hp : CNF.parse input with
  | none =>
    have hv := TM2CNFValidate.validate_correct input
    simp [hp] at hv
    simp [verify,hv,CNFWitness.verify,hp]
  | some f =>
    have hv := TM2CNFValidate.validate_correct input
    have hv' : TM2CNFValidate.validate input = true := by simpa [hp] using hv
    obtain ⟨vars,hvars,hproject⟩ := CNFOccurrences.project_correct_of_parse input f hp
    have hblocks : BitstringEncoding.undelimitBlocks (TM2WitnessLookup.frames vars) = some vars := by
      exact BitstringEncoding.undelimitBlocks_flatten_delimit vars
    simp [verify,hv',hproject,hblocks,formula_eq,hp,hvars,CNFWitness.verify]

/-- The raw relation has the same linear witness bound as the canonical
certificate relation, including noncanonical formula encodings. -/
theorem sat_iff_bounded_verify (input : List Bool) :
    CNF.sat input = true ↔ ∃ witness : List Bool,
      witness.length ≤ input.length ∧ verify input witness = true := by
  simpa only [verify_eq] using CNFWitness.sat_iff_bounded_verifier input

namespace Fixtures
example : formula [] [] [] = some true := by decide
example : formula [] [] [false] = some false := by decide
example : verify CNFOccurrences.Fixtures.crossedClauses [] = false := by
  rw [verify_eq]; decide
example : verify CNFWitness.Fixtures.noncanonical [true] = true := by
  rw [verify_eq]; decide
end Fixtures

end Shared.ComplexityBridge.RawCNFEval
