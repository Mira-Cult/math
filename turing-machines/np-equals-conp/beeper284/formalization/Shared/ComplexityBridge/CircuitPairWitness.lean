import Shared.ComplexityBridge.CircuitWitness

/-! Canonical Google pair encoding with a fixed-length binary witness. The
free circuit wires are constrained by explicit CNF clauses to be exactly a
valid Google-encoded Boolean list; no malformed witness encoding is accepted. -/
namespace Shared.ComplexityBridge.CircuitPairWitness
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF
open Shared.ComplexityBridge.CircuitRelocate
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitWitness

/-- Two unit clauses per witness bit enforce the delimiter bits. -/
def shapeClauses (base : Nat) : Nat → Formula
  | 0 => []
  | n+1 => [(base,true)] :: [(base+2,false)] :: shapeClauses (base+3) n

def Shape (a : Valuation) (base : Nat) : Nat → Prop
  | 0 => True
  | n+1 => a base = true ∧ a (base+2) = false ∧ Shape a (base+3) n

theorem shapeClauses_correct (a : Valuation) (base n : Nat) :
    evalFormula a (shapeClauses base n) = true ↔ Shape a base n := by
  induction n generalizing base with
  | zero => simp [shapeClauses,Shape,evalFormula]
  | succ n ih =>
    simp only [shapeClauses,Shape,evalFormula,List.all_cons,evalClause,List.any_cons,List.any_nil,
      Bool.or_false,Bool.and_eq_true,evalLiteral,beq_iff_eq]
    exact and_congr Iff.rfl (and_congr Iff.rfl (ih (base+3)))

theorem shapeClauses_length (base n : Nat) : (shapeClauses base n).length = 2*n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih => simp [shapeClauses,ih]; omega

theorem shape_congr (a b : Valuation) (base n : Nat)
    (h : ∀ i, base ≤ i → i < base+3*n → a i = b i) : Shape a base n ↔ Shape b base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [Shape]
    have h0 := h base (by omega) (by omega)
    have h2 := h (base+2) (by omega) (by omega)
    have ht : ∀ i, base+3 ≤ i → i < base+3+3*n → a i = b i := by
      intro i hi hj
      exact h i (by omega) (by omega)
    rw [h0,h2,ih (base+3) ht]

theorem shape_append (xs ys : List Bool) (offset n : Nat) :
    Shape (wire (xs++ys)) (xs.length+offset) n ↔ Shape (wire ys) offset n := by
  induction n generalizing offset with
  | zero => rfl
  | succ n ih =>
    simp only [Shape]
    have h0 := wire_append_after xs ys offset
    have h2 := wire_append_after xs ys (offset+2)
    have ht := ih (offset+3)
    simpa [Nat.add_assoc] using and_congr (iff_of_eq (congrArg (· = true) h0))
      (and_congr (iff_of_eq (congrArg (· = false) (by simpa [Nat.add_assoc] using h2)))
        (by simpa [Nat.add_assoc] using ht))

theorem encode_cons (b : Bool) (xs : List Bool) :
    BitstringEncoding.bitEncode (b::xs) = true::b::false::BitstringEncoding.bitEncode xs := by
  change (((((b::xs).map fun x => [x]).map BitstringEncoding.delimit).flatten)) =
    true::b::false::((((xs.map fun x => [x]).map BitstringEncoding.delimit).flatten))
  simp [BitstringEncoding.delimit]

theorem encode_nil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl

/-- The shape conditions and exact encoded length characterize the actual
Google Boolean-list encoding, including the empty witness. -/
theorem shape_list_iff (bits : List Bool) (n : Nat) (hlen : bits.length = 3*n) :
    Shape (wire bits) 0 n ↔ ∃ w : List Bool, w.length = n ∧ bits = BitstringEncoding.bitEncode w := by
  induction n generalizing bits with
  | zero =>
    have hb : bits = [] := List.length_eq_zero_iff.mp (by omega)
    subst bits
    simp [Shape,encode_nil]
  | succ n ih =>
    cases bits with
    | nil => simp at hlen
    | cons a bits =>
      cases bits with
      | nil => simp at hlen; omega
      | cons b bits =>
        cases bits with
        | nil => simp at hlen; omega
        | cons c rest =>
          have hrest : rest.length = 3*n := by simp at hlen; omega
          have ht : Shape (wire (a::b::c::rest)) 3 n ↔ Shape (wire rest) 0 n := by
            simpa using shape_append [a,b,c] rest 0 n
          simp only [Shape,wire,List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some]
          rw [ht,ih rest hrest]
          constructor
          · rintro ⟨ha,hc,⟨w,hw,he⟩⟩
            subst a; subst c; subst rest
            exact ⟨b::w,by simp [hw],by simp [encode_cons]⟩
          · rintro ⟨w,hw,he⟩
            cases w with
            | nil => simp at hw
            | cons x xs =>
              simp only [encode_cons,List.cons.injEq] at he
              rcases he with ⟨ha,hbx,hc,he⟩
              subst a; subst b; subst c; subst rest
              refine ⟨rfl,rfl,⟨xs,?_,rfl⟩⟩
              simp at hw
              omega

/-- Add canonical-witness shape clauses to the same circuit formula. -/
def constrainedFormula (fixed : List Bool) (n out : Nat) (gates : List Gate) : Formula :=
  shapeClauses fixed.length n ++ compileFixed fixed (3*n) out gates

/-- Both the shape and circuit constraints are witnessed by one valuation. -/
theorem constrained_sat_iff (fixed : List Bool) (n out : Nat) (gates : List Gate)
    (hv : validGates (fixed.length+3*n) gates) (hout : out < fixed.length+3*n+gates.length) :
    sat (BitstringEncoding.bitEncode (constrainedFormula fixed n out gates)) = true ↔
    ∃ inputs : List Bool, inputs.length = fixed.length+3*n ∧ Fixed (wire inputs) 0 fixed ∧
      Shape (wire inputs) fixed.length n ∧ wire (simulate inputs gates) out = true := by
  rw [sat_encode_correct]
  simp only [Satisfiable,constrainedFormula,evalFormula_append,Bool.and_eq_true,
    shapeClauses_correct,compileFixed_correct]
  constructor
  · rintro ⟨a,hshape,hfixed,ha,haccept⟩
    let base := fixed.length+3*n
    let inputs := seed base a
    have hlen : inputs.length = base := seed_length base a
    have hv' : validGates inputs.length gates := by simpa [hlen,base] using hv
    have heq : Equations (wire (simulate inputs gates)) base gates := by
      have h := simulate_equations inputs gates hv'
      simpa [hlen] using h
    have hprefix : ∀ i < base, a i = wire inputs i := by
      intro i hi
      exact (seed_wire base a i hi).symm
    have hf : Fixed (wire inputs) 0 fixed := by
      apply (Fixed_congr a (wire inputs) 0 fixed ?_).1 hfixed
      intro i _ hi
      exact hprefix i (by dsimp [base]; omega)
    have hs : Shape (wire inputs) fixed.length n := by
      apply (shape_congr a (wire inputs) fixed.length n ?_).1 hshape
      intro i _ hi
      exact hprefix i (by dsimp [base]; omega)
    have hinput : ∀ i < base, a i = wire (simulate inputs gates) i := by
      intro i hi
      rw [wire_simulate inputs gates i (by simpa [hlen] using hi)]
      exact hprefix i hi
    have hagree := equations_agree a (wire (simulate inputs gates)) base gates hv ha heq hinput
    refine ⟨inputs,hlen,hf,hs,?_⟩
    rw [← hagree out hout]
    exact haccept
  · rintro ⟨inputs,hlen,hfixed,hshape,haccept⟩
    have hv' : validGates inputs.length gates := by simpa [hlen] using hv
    have heq := simulate_equations inputs gates hv'
    have hkeep : ∀ i < fixed.length+3*n, wire inputs i = wire (simulate inputs gates) i := by
      intro i hi
      symm
      exact wire_simulate inputs gates i (by rw [hlen]; exact hi)
    refine ⟨wire (simulate inputs gates),?_,?_,?_,haccept⟩
    · apply (shape_congr (wire inputs) (wire (simulate inputs gates)) fixed.length n ?_).1 hshape
      intro i _ hi
      exact hkeep i hi
    · apply (Fixed_congr (wire inputs) (wire (simulate inputs gates)) 0 fixed ?_).1 hfixed
      intro i _ hi
      apply hkeep
      omega
    · simpa [hlen] using heq

/-- The canonical pair encoding is a fixed delimited public component
followed by the encoded witness component. -/
def pairPrefix (x : List Bool) : List Bool := BitstringEncoding.delimit (BitstringEncoding.bitEncode x)

theorem pair_encode (x w : List Bool) :
    BitstringEncoding.bitEncode (x,w) = pairPrefix x ++ BitstringEncoding.bitEncode w := rfl

def pairFormula (p : Program) (x : List Bool) (n fuel : Nat) : Formula :=
  constrainedFormula (template p (pairPrefix x) (3*n) fuel) n
    (witnessOutput p (pairPrefix x) (3*n) fuel) (witnessGates p (pairPrefix x) (3*n) fuel)

/-- A single canonical CNF is satisfiable exactly when a fixed-length witness
makes the finite program accept the actual Google pair encoding. -/
theorem sat_pairFormula_iff (p : Program) (x : List Bool) (n fuel : Nat) :
    sat (BitstringEncoding.bitEncode (pairFormula p x n fuel)) = true ↔
      ∃ w : List Bool, w.length = n ∧ bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some true := by
  let fixed := template p (pairPrefix x) (3*n) fuel
  let gates := witnessGates p (pairPrefix x) (3*n) fuel
  let out := witnessOutput p (pairPrefix x) (3*n) fuel
  have hv : validGates (fixed.length+3*n) gates := witnessGates_valid p (pairPrefix x) (3*n) fuel
  have ho : out < fixed.length+3*n+gates.length := witnessOutput_bound p (pairPrefix x) (3*n) fuel
  change sat (BitstringEncoding.bitEncode (constrainedFormula fixed n out gates)) = true ↔ _
  rw [constrained_sat_iff fixed n out gates hv ho]
  constructor
  · rintro ⟨inputs,hlen,hfixed,hshape,haccept⟩
    obtain ⟨raw,hrawlen,heq⟩ := fixed_decompose fixed inputs (3*n) hlen hfixed
    subst inputs
    have hs : Shape (wire raw) 0 n := by
      apply (shape_append fixed raw 0 n).1
      simpa using hshape
    obtain ⟨w,hw,hraw⟩ := (shape_list_iff raw n hrawlen).1 hs
    have hc := witnessCircuit_correct p (pairPrefix x) raw fuel
    rw [hrawlen] at hc
    have hb := hc.1 haccept
    refine ⟨w,hw,?_⟩
    simpa [pair_encode,hraw] using hb
  · rintro ⟨w,hw,haccept⟩
    let raw := BitstringEncoding.bitEncode w
    have hrawlen : raw.length = 3*n := by
      dsimp [raw]
      rw [Shared.ComplexityBridge.bitstring_list_encoded_length,hw]
    have hshape : Shape (wire raw) 0 n :=
      (shape_list_iff raw n hrawlen).2 ⟨w,hw,rfl⟩
    have hs : Shape (wire (fixed++raw)) fixed.length n := by
      have h := (shape_append fixed raw 0 n).2 hshape
      simpa using h
    have hf : Fixed (wire (fixed++raw)) 0 fixed := by
      apply (Fixed_congr (wire fixed) (wire (fixed++raw)) 0 fixed ?_).1 (fixed_self fixed)
      intro i _ hi
      symm
      exact wire_append fixed raw i (by simpa using hi)
    have hc := witnessCircuit_correct p (pairPrefix x) raw fuel
    rw [hrawlen] at hc
    have haccept' : bounded p (pairPrefix x++raw) fuel = some true := by
      simpa [raw,pair_encode] using haccept
    refine ⟨fixed++raw,?_,hf,hs,?_⟩
    · simp [hrawlen]
    · exact hc.2 haccept'

theorem shapeClauses_clause_length (base n : Nat) :
    ∀ c ∈ shapeClauses base n, c.length ≤ 3 := by
  induction n generalizing base with
  | zero => simp [shapeClauses]
  | succ n ih =>
    intro c hc
    simp only [shapeClauses,List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · simp
    · simp
    · exact ih (base+3) c hc

theorem shapeClauses_variable_bound (base n : Nat) :
    ∀ c ∈ shapeClauses base n, ∀ lit ∈ c, lit.1 < base+3*n := by
  induction n generalizing base with
  | zero => simp [shapeClauses]
  | succ n ih =>
    intro c hc lit hl
    simp only [shapeClauses,List.mem_cons] at hc
    rcases hc with rfl | rfl | hc
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      subst lit
      simp only
      omega
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      subst lit
      simp only
      omega
    · have h := ih (base+3) c hc lit hl
      omega

/-- The canonical serialized size includes the extra witness-shape clauses. -/
theorem constrained_encoded_length (fixed : List Bool) (n out : Nat) (gates : List Gate)
    (hv : validGates (fixed.length+3*n) gates) (hout : out < fixed.length+3*n+gates.length) :
    (BitstringEncoding.bitEncode (constrainedFormula fixed n out gates)).length ≤
      (2*n+fixed.length+3*gates.length+1)*(24*(fixed.length+3*n+gates.length)+31) := by
  let f := constrainedFormula fixed n out gates
  let bound := fixed.length+3*n+gates.length
  have hc : ∀ c ∈ f, c.length ≤ 3 := by
    intro c hm
    simp only [f,constrainedFormula,compileFixed,List.mem_append] at hm
    rcases hm with hm | hm | hm
    · exact shapeClauses_clause_length fixed.length n c hm
    · exact fixInputs_clause_length 0 fixed c hm
    · exact compile_clause_length (fixed.length+3*n) out gates c hm
  have hvars : ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ bound := by
    intro c hm lit hl
    simp only [f,constrainedFormula,compileFixed,List.mem_append] at hm
    rcases hm with hm | hm | hm
    · have h := shapeClauses_variable_bound fixed.length n c hm lit hl
      dsimp [bound]; omega
    · have h := fixInputs_variable_bound 0 fixed c hm lit hl
      dsimp [bound]; omega
    · exact compile_variable_bound (fixed.length+3*n) out gates hv hout c hm lit hl
  have hlen : f.length ≤ 2*n+fixed.length+3*gates.length+1 := by
    dsimp [f,constrainedFormula,compileFixed]
    rw [List.length_append,List.length_append,shapeClauses_length,fixInputs_length]
    have h := compile_length (fixed.length+3*n) out gates
    omega
  exact le_trans (formula_encoded_length_le f bound hc hvars)
    (Nat.mul_le_mul_right (24*bound+31) hlen)

theorem pairFormula_encoded_length (p : Program) (x : List Bool) (n fuel : Nat) :
    (BitstringEncoding.bitEncode (pairFormula p x n fuel)).length ≤
      (2*n+(template p (pairPrefix x) (3*n) fuel).length+
          3*(witnessGates p (pairPrefix x) (3*n) fuel).length+1) *
      (24*((template p (pairPrefix x) (3*n) fuel).length+3*n+
          (witnessGates p (pairPrefix x) (3*n) fuel).length)+31) :=
  constrained_encoded_length _ _ _ _ (witnessGates_valid p (pairPrefix x) (3*n) fuel)
    (witnessOutput_bound p (pairPrefix x) (3*n) fuel)

theorem constrained_clause_count (fixed : List Bool) (n out : Nat) (gates : List Gate) :
    (constrainedFormula fixed n out gates).length ≤ 2*n+fixed.length+3*gates.length+1 := by
  simp only [constrainedFormula,compileFixed,List.length_append,shapeClauses_length,fixInputs_length]
  have h := compile_length (fixed.length+3*n) out gates
  omega

theorem constrained_clause_length (fixed : List Bool) (n out : Nat) (gates : List Gate) :
    ∀ c ∈ constrainedFormula fixed n out gates, c.length ≤ 3 := by
  intro c hm
  simp only [constrainedFormula,compileFixed,List.mem_append] at hm
  rcases hm with hm | hm | hm
  · exact shapeClauses_clause_length fixed.length n c hm
  · exact fixInputs_clause_length 0 fixed c hm
  · exact compile_clause_length (fixed.length+3*n) out gates c hm

theorem constrained_variable_bound (fixed : List Bool) (n out : Nat) (gates : List Gate)
    (hv : validGates (fixed.length+3*n) gates) (hout : out < fixed.length+3*n+gates.length) :
    ∀ c ∈ constrainedFormula fixed n out gates, ∀ lit ∈ c, lit.1 ≤ fixed.length+3*n+gates.length := by
  intro c hm lit hl
  simp only [constrainedFormula,compileFixed,List.mem_append] at hm
  rcases hm with hm | hm | hm
  · have h := shapeClauses_variable_bound fixed.length n c hm lit hl
    omega
  · have h := fixInputs_variable_bound 0 fixed c hm lit hl
    omega
  · exact compile_variable_bound (fixed.length+3*n) out gates hv hout c hm lit hl

theorem pairFormula_clause_count (p : Program) (x : List Bool) (n fuel : Nat) :
    (pairFormula p x n fuel).length ≤
      2*n+(template p (pairPrefix x) (3*n) fuel).length+
        3*(witnessGates p (pairPrefix x) (3*n) fuel).length+1 :=
  constrained_clause_count _ _ _ _

theorem pairFormula_clause_length (p : Program) (x : List Bool) (n fuel : Nat) :
    ∀ c ∈ pairFormula p x n fuel, c.length ≤ 3 := constrained_clause_length _ _ _ _

theorem pairFormula_variable_bound (p : Program) (x : List Bool) (n fuel : Nat) :
    ∀ c ∈ pairFormula p x n fuel, ∀ lit ∈ c, lit.1 ≤
      (template p (pairPrefix x) (3*n) fuel).length+3*n+
        (witnessGates p (pairPrefix x) (3*n) fuel).length :=
  constrained_variable_bound _ _ _ _ (witnessGates_valid p (pairPrefix x) (3*n) fuel)
    (witnessOutput_bound p (pairPrefix x) (3*n) fuel)

end Shared.ComplexityBridge.CircuitPairWitness
