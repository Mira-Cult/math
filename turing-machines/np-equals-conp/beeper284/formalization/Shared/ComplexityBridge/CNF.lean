import Shared.ComplexityBridge.Encodings
import Shared.Codes.Inputs

/-!
An executable exhaustive reference evaluator for a proposed CNF front end.
A literal `(v, b)` is true when variable `v` has value `b`; an empty clause
is false and an empty conjunction is true. The input parser is exactly the
pinned Google `BitstringEncoding.bitDecode` for the nested list type. On a
malformed input, SAT and valid-UNSAT both reject; the total complement of SAT
accepts it.

The exhaustive search below proves its own logical correctness, not
NP-completeness, polynomial parsing or a TM2 computability/cost theorem.
-/
namespace Shared.ComplexityBridge.CNF

abbrev Literal := Nat × Bool
abbrev Clause := List Literal
abbrev Formula := List Clause
abbrev Valuation := Nat → Bool

def evalLiteral (a : Valuation) (lit : Literal) : Bool := a lit.1 == lit.2

def evalClause (a : Valuation) (clause : Clause) : Bool :=
  clause.any (evalLiteral a)

def evalFormula (a : Valuation) (formula : Formula) : Bool :=
  formula.all (evalClause a)

def Satisfiable (formula : Formula) : Prop := ∃ a : Valuation, evalFormula a formula = true

/-- Variables in occurrence order, including duplicates. Search size depends on
occurrence count, not the magnitude of a binary variable name. -/
def variableOccurrences (formula : Formula) : List Nat := formula.flatten.map Prod.fst

def assignments : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (assignments n).map (false :: ·) ++ (assignments n).map (true :: ·)

/-- The first matching occurrence determines the value; an absent variable is
false. The list arguments are finite and evaluated by structural recursion. -/
def assignment : List Nat → List Bool → Valuation
  | [], _, _ => false
  | _ :: _, [], _ => false
  | v :: vs, b :: bs, i => if i = v then b else assignment vs bs i

def satFormula (formula : Formula) : Bool :=
  let vars := variableOccurrences formula
  (assignments vars.length).any fun bits => evalFormula (assignment vars bits) formula

def parse (input : List Bool) : Option Formula := BitstringEncoding.bitDecode input

def sat (input : List Bool) : Bool :=
  match parse input with
  | none => false
  | some formula => satFormula formula

def validUnsat (input : List Bool) : Bool :=
  match parse input with
  | none => false
  | some formula => !(satFormula formula)

def complementSat (input : List Bool) : Bool := !(sat input)

@[simp] theorem parse_encode (formula : Formula) :
    parse (BitstringEncoding.bitEncode formula) = some formula :=
  BitstringEncoding.bitDecode_bitEncode formula

theorem mem_assignments_iff (bits : List Bool) (n : Nat) :
    bits ∈ assignments n ↔ bits.length = n := by
  induction n generalizing bits with
  | zero => simp [assignments]
  | succ n ih =>
    cases bits with
    | nil => simp [assignments]
    | cons b bits =>
      cases b <;> simp [assignments, ih]

theorem variable_mem {formula : Formula} {clause : Clause} {lit : Literal}
    (hc : clause ∈ formula) (hl : lit ∈ clause) : lit.1 ∈ variableOccurrences formula := by
  apply List.mem_map.mpr
  exact ⟨lit, List.mem_flatten.mpr ⟨clause, hc, hl⟩, rfl⟩

theorem assignment_map (vars : List Nat) (a : Valuation) (i : Nat) (hi : i ∈ vars) :
    assignment vars (vars.map a) i = a i := by
  induction vars with
  | nil => simp at hi
  | cons v vs ih =>
    by_cases heq : i = v
    · subst i
      simp [assignment]
    · have hm : i ∈ vs := by simpa [heq, Ne.symm heq] using hi
      simp [assignment, heq, ih hm]

theorem evalFormula_true_iff_of_agree (formula : Formula) (a b : Valuation)
    (h : ∀ i, i ∈ variableOccurrences formula → a i = b i) :
    evalFormula a formula = true ↔ evalFormula b formula = true := by
  simp only [evalFormula, List.all_eq_true, evalClause, List.any_eq_true]
  constructor <;> intro hf clause hc
  · obtain ⟨lit, hl, hv⟩ := hf clause hc
    refine ⟨lit, hl, ?_⟩
    have heq := h lit.1 (variable_mem hc hl)
    simpa [evalLiteral, heq] using hv
  · obtain ⟨lit, hl, hv⟩ := hf clause hc
    refine ⟨lit, hl, ?_⟩
    have heq := h lit.1 (variable_mem hc hl)
    simpa [evalLiteral, heq] using hv

theorem satFormula_correct (formula : Formula) :
    satFormula formula = true ↔ Satisfiable formula := by
  simp only [satFormula, List.any_eq_true, Satisfiable]
  constructor
  · rintro ⟨bits, _, hb⟩
    exact ⟨assignment (variableOccurrences formula) bits, hb⟩
  · rintro ⟨a, ha⟩
    let bits := (variableOccurrences formula).map a
    have hm : bits ∈ assignments (variableOccurrences formula).length := by
      apply (mem_assignments_iff _ _).2
      simp [bits]
    have hagree : ∀ i, i ∈ variableOccurrences formula → a i = assignment (variableOccurrences formula) bits i := by
      intro i hi
      symm
      exact assignment_map (variableOccurrences formula) a i hi
    exact ⟨bits, hm, (evalFormula_true_iff_of_agree formula a (assignment (variableOccurrences formula) bits) hagree).1 ha⟩

theorem sat_correct (input : List Bool) : sat input = true ↔
    ∃ formula, parse input = some formula ∧ Satisfiable formula := by
  cases hp : parse input with
  | none => simp [sat, hp]
  | some formula => simp [sat, hp, satFormula_correct]

theorem malformed_conventions {input : List Bool} (h : parse input = none) :
    sat input = false ∧ validUnsat input = false ∧ complementSat input = true := by
  simp [sat, validUnsat, complementSat, h]

theorem valid_conventions {input : List Bool} {formula : Formula} (h : parse input = some formula) :
    validUnsat input = complementSat input := by
  simp [sat, validUnsat, complementSat, h]

/-- A list's Google encoding has at least one bit per element. -/
theorem list_length_le_bitEncode {α : Type} [BitstringEncoding α] (xs : List α) :
    xs.length ≤ (BitstringEncoding.bitEncode xs).length := by
  change xs.length ≤ (((xs.map (fun a : α => BitstringEncoding.bitEncode a)).map
    BitstringEncoding.delimit).flatten).length
  simpa using BitstringEncoding.length_le_length_flatten_delimit
    (xs.map (fun a : α => BitstringEncoding.bitEncode a))

/-- For canonical encodings, one witness bit per literal occurrence fits in
the encoded input length. This is not a parsing-time or NP-membership proof. -/
theorem occurrences_le_canonical_input_length (formula : Formula) :
    (variableOccurrences formula).length ≤ (BitstringEncoding.bitEncode formula).length := by
  simp only [variableOccurrences, List.length_map]
  change formula.flatten.length ≤
    (((formula.map (fun clause : Clause => BitstringEncoding.bitEncode clause)).map
      BitstringEncoding.delimit).flatten).length
  induction formula with
  | nil => rfl
  | cons clause rest ih =>
    simp only [List.flatten_cons, List.map_cons, List.length_append, BitstringEncoding.length_delimit]
    have hc := list_length_le_bitEncode clause
    omega

/-- On canonical inputs, the Boolean reference agrees with semantic SAT. -/
theorem sat_encode_correct (formula : Formula) :
    sat (BitstringEncoding.bitEncode formula) = true ↔ Satisfiable formula := by
  simp [sat, parse_encode, satFormula_correct]

/-- Valid-UNSAT rejects malformed inputs and otherwise recognizes unsatisfiability. -/
theorem validUnsat_correct (input : List Bool) : validUnsat input = true ↔
    ∃ formula, parse input = some formula ∧ ¬ Satisfiable formula := by
  cases hp : parse input with
  | none => simp [validUnsat, hp]
  | some formula =>
    have hc : (!(satFormula formula) = true ↔ ¬ Satisfiable formula) := by
      rw [← satFormula_correct]
      cases satFormula formula <;> simp
    simpa [validUnsat, hp] using hc

/-- Total complement includes malformed inputs in addition to valid UNSAT. -/
theorem complementSat_correct (input : List Bool) : complementSat input = true ↔
    parse input = none ∨ ∃ formula, parse input = some formula ∧ ¬ Satisfiable formula := by
  cases hp : parse input with
  | none => simp [complementSat, sat, hp]
  | some formula =>
    have hc : (!(satFormula formula) = true ↔ ¬ Satisfiable formula) := by
      rw [← satFormula_correct]
      cases satFormula formula <;> simp
    simpa [complementSat, sat, hp] using hc

/-- A lone delimiter prefix is malformed, so the two UNSAT conventions differ. -/
theorem malformed_example : parse [true] = none := rfl

theorem validUnsat_ne_complementSat : validUnsat ≠ complementSat := by
  intro h
  have hv := congrFun h [true]
  have hm := malformed_conventions malformed_example
  rw [hm.2.1, hm.2.2] at hv
  cases hv

/-- The controller's test index selects an exhaustive enumeration of raw inputs. -/
def satAtIndex (n : Nat) : Bool := sat (Shared.Codes.Inputs.inputAt n)

theorem satAtIndex_covers (input : List Bool) :
    ∃ n, Shared.Codes.Inputs.inputAt n = input ∧ satAtIndex n = sat input := by
  refine ⟨Encodable.encode input, Shared.Codes.Inputs.inputAt_encode input, ?_⟩
  simp [satAtIndex]

end Shared.ComplexityBridge.CNF
