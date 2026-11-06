import Shared.ComplexityBridge.CircuitPairWitness

/-! Finite CNF disjunction with explicit, disjoint selector variables. All
original variables are mapped to even indices; selectors use odd indices. -/
namespace Shared.ComplexityBridge.CNFDisjunction
open Shared.ComplexityBridge.CNF
open Shared.ComplexityBridge.CircuitCNF

def evenLiteral (lit : Literal) : Literal := (2*lit.1,lit.2)
def evenClause (c : Clause) : Clause := c.map evenLiteral
def evenFormula (f : Formula) : Formula := f.map evenClause

def selector (i : Nat) : Nat := 2*i+1

def guardClause (i : Nat) (c : Clause) : Clause := (selector i,false)::evenClause c
def guardFormula (i : Nat) (f : Formula) : Formula := f.map (guardClause i)

def guardAll (start : Nat) : List Formula → Formula
  | [] => []
  | f::fs => guardFormula start f ++ guardAll (start+1) fs

def choices (start count : Nat) : Clause :=
  (List.range count).map fun i => (selector (start+i),true)

def disjoin (fs : List Formula) : Formula := [choices 0 fs.length] ++ guardAll 0 fs

theorem eval_evenClause (a : Valuation) (c : Clause) :
    evalClause a (evenClause c) = evalClause (fun i => a (2*i)) c := by
  simp only [evenClause,evalClause,List.any_map]
  rfl

theorem eval_guardClause (a : Valuation) (i : Nat) (c : Clause) :
    evalClause a (guardClause i c) = ((!a (selector i)) || evalClause (fun j => a (2*j)) c) := by
  change ((a (selector i) == false) || evalClause a (evenClause c)) = _
  rw [eval_evenClause]
  cases a (selector i) <;> rfl

theorem guardFormula_true (a : Valuation) (i : Nat) (f : Formula) (hs : a (selector i) = true) :
    evalFormula a (guardFormula i f) = evalFormula (fun j => a (2*j)) f := by
  simp only [guardFormula,evalFormula,List.all_map]
  have h : (evalClause a ∘ guardClause i) = evalClause (fun j => a (2*j)) := by
    funext c
    simp [Function.comp_apply,eval_guardClause,hs]
  rw [h]

theorem guardFormula_false (a : Valuation) (i : Nat) (f : Formula) (hs : a (selector i) = false) :
    evalFormula a (guardFormula i f) = true := by
  simp only [guardFormula,evalFormula,List.all_map]
  have h : (evalClause a ∘ guardClause i) = (fun _ => true) := by
    funext c
    simp [Function.comp_apply,eval_guardClause,hs]
  rw [h]
  simp

theorem guardAll_selected (a : Valuation) (start : Nat) (fs : List Formula) (j : Nat)
    (hj : j < fs.length) (he : evalFormula a (guardAll start fs) = true)
    (hs : a (selector (start+j)) = true) :
    evalFormula (fun i => a (2*i)) fs[j] = true := by
  induction fs generalizing start j with
  | nil => simp at hj
  | cons f fs ih =>
    simp only [guardAll,evalFormula_append,Bool.and_eq_true] at he
    cases j with
    | zero =>
      simp only [Nat.add_zero] at hs
      simpa [guardFormula_true a start f hs] using he.1
    | succ j =>
      have hj' : j < fs.length := by simp at hj; omega
      have hs' : a (selector ((start+1)+j)) = true := by
        have he : start+1+j = start+(j+1) := by omega
        rw [he]
        exact hs
      simpa using ih (start+1) j hj' he.2 hs'

theorem choices_selected (a : Valuation) (start count : Nat)
    (h : evalClause a (choices start count) = true) :
    ∃ j < count, a (selector (start+j)) = true := by
  simp only [choices,evalClause,List.any_eq_true,List.mem_map,List.mem_range] at h
  obtain ⟨lit,⟨j,hj,rfl⟩,hv⟩ := h
  exact ⟨j,hj,by simpa [evalLiteral] using hv⟩

theorem guardAll_allFalse (a : Valuation) (start : Nat) (fs : List Formula)
    (hs : ∀ j < fs.length, a (selector (start+j)) = false) :
    evalFormula a (guardAll start fs) = true := by
  induction fs generalizing start with
  | nil => rfl
  | cons f fs ih =>
    have h0 : a (selector start) = false := by simpa using hs 0 (by simp)
    have ht : ∀ j < fs.length, a (selector (start+1+j)) = false := by
      intro j hj
      have hh := hs (j+1) (by simp; omega)
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
    simp only [guardAll,evalFormula_append,Bool.and_eq_true]
    exact ⟨guardFormula_false a start f h0,ih (start+1) ht⟩

theorem guardAll_one (a : Valuation) (start : Nat) (fs : List Formula) (j : Nat)
    (hj : j < fs.length) (hs : ∀ i < fs.length, a (selector (start+i)) = decide (i=j))
    (hf : evalFormula (fun i => a (2*i)) fs[j] = true) :
    evalFormula a (guardAll start fs) = true := by
  induction fs generalizing start j with
  | nil => simp at hj
  | cons f fs ih =>
    simp only [guardAll,evalFormula_append,Bool.and_eq_true]
    cases j with
    | zero =>
      have h0 : a (selector start) = true := by simpa using hs 0 (by simp)
      have ht : ∀ i < fs.length, a (selector (start+1+i)) = false := by
        intro i hi
        have hh := hs (i+1) (by simp; omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
      exact ⟨by simpa [guardFormula_true a start f h0] using hf,guardAll_allFalse a (start+1) fs ht⟩
    | succ j =>
      have hj' : j < fs.length := by simp at hj; omega
      have h0 : a (selector start) = false := by simpa using hs 0 (by simp)
      have ht : ∀ i < fs.length, a (selector (start+1+i)) = decide (i=j) := by
        intro i hi
        have hh := hs (i+1) (by simp; omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
      exact ⟨guardFormula_false a start f h0,ih (start+1) j hj' ht (by simpa using hf)⟩

/-- Embed an original valuation on even variables and select exactly one odd
selector. -/
def chosenValuation (a : Valuation) (chosen : Nat) (v : Nat) : Bool :=
  if v % 2 = 0 then a (v/2) else decide (v = selector chosen)

theorem chosenValuation_even (a : Valuation) (chosen i : Nat) :
    chosenValuation a chosen (2*i) = a i := by
  simp [chosenValuation,Nat.mul_mod,Nat.mul_comm]

theorem chosenValuation_selector (a : Valuation) (chosen i : Nat) :
    chosenValuation a chosen (selector i) = decide (i = chosen) := by
  have hodd : selector i % 2 ≠ 0 := by simp [selector,Nat.add_mod,Nat.mul_mod]
  have heq : selector i = selector chosen ↔ i = chosen := by
    simp only [selector]
    omega
  simp [chosenValuation,hodd,heq]

theorem choices_has (a : Valuation) (start count j : Nat) (hj : j < count)
    (hs : a (selector (start+j)) = true) : evalClause a (choices start count) = true := by
  simp only [choices,evalClause,List.any_eq_true,List.mem_map,List.mem_range]
  exact ⟨(selector (start+j),true),⟨j,hj,rfl⟩,by simpa [evalLiteral] using hs⟩

/-- The guarded, variable-renamed CNF is satisfiable exactly when one member
of the finite family is satisfiable; the empty family is unsatisfiable. -/
theorem disjoin_satisfiable (fs : List Formula) :
    Satisfiable (disjoin fs) ↔ ∃ f ∈ fs, Satisfiable f := by
  constructor
  · rintro ⟨a,ha⟩
    simp only [disjoin,evalFormula_append,Bool.and_eq_true] at ha
    have hc : evalClause a (choices 0 fs.length) = true := by simpa [evalFormula] using ha.1
    obtain ⟨j,hj,hs⟩ := choices_selected a 0 fs.length hc
    have hf := guardAll_selected a 0 fs j hj ha.2 hs
    exact ⟨fs[j],List.getElem_mem hj,⟨fun i => a (2*i),hf⟩⟩
  · rintro ⟨f,hmem,a,ha⟩
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hmem
    let v := chosenValuation a j
    have hv : (fun i => v (2*i)) = a := by
      funext i
      exact chosenValuation_even a j i
    have hs : ∀ i < fs.length, v (selector (0+i)) = decide (i=j) := by
      intro i _
      simpa using chosenValuation_selector a j i
    have hf : evalFormula (fun i => v (2*i)) fs[j] = true := by rw [hv,he]; exact ha
    have hg := guardAll_one v 0 fs j hj hs hf
    have hc : evalClause v (choices 0 fs.length) = true := by
      apply choices_has v 0 fs.length j hj
      simpa using chosenValuation_selector a j j
    refine ⟨v,?_⟩
    simp only [disjoin,evalFormula_append,Bool.and_eq_true]
    exact ⟨by simpa [evalFormula] using hc,hg⟩

theorem sat_disjoin_iff (fs : List Formula) :
    sat (BitstringEncoding.bitEncode (disjoin fs)) = true ↔
      ∃ f ∈ fs, sat (BitstringEncoding.bitEncode f) = true := by
  rw [sat_encode_correct,disjoin_satisfiable]
  simp only [sat_encode_correct]

/-- Clause count grows additively, with one selector clause for the family. -/
theorem guardAll_length (start : Nat) (fs : List Formula) :
    (guardAll start fs).length = (fs.map List.length).sum := by
  induction fs generalizing start with
  | nil => rfl
  | cons f fs ih => simp [guardAll,guardFormula,ih]

theorem disjoin_length (fs : List Formula) :
    (disjoin fs).length = 1+(fs.map List.length).sum := by
  simp [disjoin,guardAll_length,Nat.add_comm]

/-- General canonical CNF size bound with explicit clause length and variable
index bounds. -/
theorem formula_length_bound (f : Formula) (varBound clauseBound : Nat)
    (hc : ∀ c ∈ f, c.length ≤ clauseBound)
    (hv : ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ varBound) :
    (BitstringEncoding.bitEncode f).length ≤
      f.length*(2*(clauseBound*(4*varBound+5))+1) := by
  let per := 2*(clauseBound*(4*varBound+5))+1
  have hentry : ∀ c ∈ f, (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length ≤ per := by
    intro c hm
    have h1 := clause_encoded_length_le c varBound (hv c hm)
    have h2 := Nat.mul_le_mul_right (4*varBound+5) (hc c hm)
    rw [BitstringEncoding.length_delimit]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 2 (le_trans h1 h2)) 1
  have hsum := List.sum_le_sum (l := f)
    (f := fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)
    (g := fun _ => per) hentry
  change (((f.map (fun c : Clause => BitstringEncoding.bitEncode c)).map BitstringEncoding.delimit).flatten).length ≤ _
  simp only [List.length_flatten,List.map_map]
  change (f.map (fun c => (BitstringEncoding.delimit (BitstringEncoding.bitEncode c)).length)).sum ≤ _
  simpa only [List.map_const',List.sum_replicate_nat] using hsum

theorem guardAll_clause_bound (start : Nat) (fs : List Formula)
    (hc : ∀ f ∈ fs, ∀ c ∈ f, c.length ≤ 3) :
    ∀ c ∈ guardAll start fs, c.length ≤ 4 := by
  induction fs generalizing start with
  | nil => simp [guardAll]
  | cons f fs ih =>
    intro c hm
    simp only [guardAll,List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
      have hh := hc f (by simp) d hd
      simp only [guardClause,evenClause,List.length_cons,List.length_map]
      omega
    · apply ih (start+1) ?_ c hm
      intro f hf
      exact hc f (by simp [hf])

theorem disjoin_clause_bound (fs : List Formula)
    (hc : ∀ f ∈ fs, ∀ c ∈ f, c.length ≤ 3) :
    ∀ c ∈ disjoin fs, c.length ≤ fs.length+4 := by
  intro c hm
  simp only [disjoin,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | hm
  · simp [choices]
  · have h := guardAll_clause_bound 0 fs hc c hm
    omega

theorem guardAll_variable_bound (start : Nat) (fs : List Formula) (limit : Nat)
    (hs : ∀ i < fs.length, selector (start+i) ≤ limit)
    (hv : ∀ f ∈ fs, ∀ c ∈ f, ∀ lit ∈ c, 2*lit.1 ≤ limit) :
    ∀ c ∈ guardAll start fs, ∀ lit ∈ c, lit.1 ≤ limit := by
  induction fs generalizing start with
  | nil => simp [guardAll]
  | cons f fs ih =>
    intro c hm lit hl
    simp only [guardAll,List.mem_append] at hm
    rcases hm with hm | hm
    · obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hm
      simp only [guardClause,List.mem_cons] at hl
      rcases hl with rfl | hl
      · simpa using hs 0 (by simp)
      · obtain ⟨old,hold,rfl⟩ := List.mem_map.mp hl
        exact hv f (by simp) d hd old hold
    · apply ih (start+1) ?_ ?_ c hm lit hl
      · intro i hi
        have h := hs (i+1) (by simp; omega)
        simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
      · intro f hf
        exact hv f (by simp [hf])

theorem disjoin_variable_bound (fs : List Formula) (varBound : Nat)
    (hv : ∀ f ∈ fs, ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ varBound) :
    ∀ c ∈ disjoin fs, ∀ lit ∈ c, lit.1 ≤ 2*(varBound+fs.length+1) := by
  intro c hm lit hl
  simp only [disjoin,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hm
  rcases hm with rfl | hm
  · simp only [choices,List.mem_map,List.mem_range] at hl
    obtain ⟨i,hi,rfl⟩ := hl
    simp only [selector,Prod.fst]
    omega
  · apply guardAll_variable_bound 0 fs _ ?_ ?_ c hm lit hl
    · intro i hi
      simp only [selector]
      omega
    · intro f hf d hd old hold
      have hh := hv f hf d hd old hold
      omega

/-- General serialization bound for a family of three-literal CNFs with a
uniform variable and clause-count bound. -/
theorem disjoin_encoded_length (fs : List Formula) (varBound clauses : Nat)
    (hc : ∀ f ∈ fs, ∀ c ∈ f, c.length ≤ 3)
    (hv : ∀ f ∈ fs, ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ varBound)
    (hn : ∀ f ∈ fs, f.length ≤ clauses) :
    (BitstringEncoding.bitEncode (disjoin fs)).length ≤
      (1+fs.length*clauses)*(2*((fs.length+4)*(4*(2*(varBound+fs.length+1))+5))+1) := by
  have hsum := List.sum_le_sum (l := fs) (f := List.length) (g := fun _ => clauses) hn
  have hlen : (disjoin fs).length ≤ 1+fs.length*clauses := by
    rw [disjoin_length]
    have hh : (fs.map List.length).sum ≤ fs.length*clauses := by
      simpa only [List.map_const',List.sum_replicate_nat] using hsum
    omega
  have h := formula_length_bound (disjoin fs) (2*(varBound+fs.length+1)) (fs.length+4)
    (disjoin_clause_bound fs hc) (disjoin_variable_bound fs varBound hv)
  exact le_trans h (Nat.mul_le_mul_right _ hlen)

/-- The Google pair-encoded witness length may be any value up to `bound`;
one shared fuel is used for all candidates. -/
def boundedPairFormula (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (bound fuel : Nat) : Formula :=
  disjoin ((List.range (bound+1)).map fun n =>
    Shared.ComplexityBridge.CircuitPairWitness.pairFormula p x n fuel)

/-- One CNF captures every bounded-length canonical binary witness. -/
theorem sat_boundedPairFormula_iff (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (bound fuel : Nat) :
    sat (BitstringEncoding.bitEncode (boundedPairFormula p x bound fuel)) = true ↔
      ∃ w : List Bool, w.length ≤ bound ∧
        Shared.Codes.FinitePrograms.bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some true := by
  rw [boundedPairFormula,sat_disjoin_iff]
  constructor
  · rintro ⟨f,hmem,hf⟩
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hmem
    obtain ⟨w,hw,haccept⟩ := (Shared.ComplexityBridge.CircuitPairWitness.sat_pairFormula_iff p x n fuel).1 hf
    have hn' : n < bound+1 := List.mem_range.mp hn
    exact ⟨w,by omega,haccept⟩
  · rintro ⟨w,hw,haccept⟩
    refine ⟨Shared.ComplexityBridge.CircuitPairWitness.pairFormula p x w.length fuel,?_,?_⟩
    · apply List.mem_map.mpr
      exact ⟨w.length,List.mem_range.mpr (by omega),rfl⟩
    · exact (Shared.ComplexityBridge.CircuitPairWitness.sat_pairFormula_iff p x w.length fuel).2 ⟨w,rfl,haccept⟩

/-- Conditional verifier interface: the generated formula depends only on the
finite program and explicit inputs, while the relation is used solely in the
correctness hypothesis. -/
theorem sat_boundedPairFormula_of_verifier (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (bound fuel : Nat) (relation : List Bool → List Bool → Bool)
    (hverify : ∀ w, w.length ≤ bound →
      Shared.Codes.FinitePrograms.bounded p (BitstringEncoding.bitEncode (x,w)) fuel = some (relation x w)) :
    sat (BitstringEncoding.bitEncode (boundedPairFormula p x bound fuel)) = true ↔
      ∃ w : List Bool, w.length ≤ bound ∧ relation x w = true := by
  rw [sat_boundedPairFormula_iff]
  constructor
  · rintro ⟨w,hw,ha⟩
    refine ⟨w,hw,?_⟩
    have h := hverify w hw
    rw [h] at ha
    exact Option.some.inj ha
  · rintro ⟨w,hw,ha⟩
    refine ⟨w,hw,?_⟩
    rw [hverify w hw,ha]

/-- Uniform numerical bounds for every witness length up to `bound`. -/
def maxWindow (x : List Bool) (bound fuel : Nat) : Nat := 6*x.length+1+3*bound+fuel
def maxStates (p : Shared.Codes.FinitePrograms.Program) : Nat := p.length+3
def maxWidth (p : Shared.Codes.FinitePrograms.Program) (x : List Bool) (bound fuel : Nat) : Nat :=
  maxStates p+(2*maxWindow x bound fuel+1)
def maxGates (p : Shared.Codes.FinitePrograms.Program) (x : List Bool) (bound fuel : Nat) : Nat :=
  fuel*((2*(2+4*maxStates p)+(1+4*(2*maxWindow x bound fuel+1))) +
    maxStates p*(2+4*maxStates p))
def maxClauses (p : Shared.Codes.FinitePrograms.Program) (x : List Bool) (bound fuel : Nat) : Nat :=
  2*bound+maxWidth p x bound fuel+3*maxGates p x bound fuel+1
def maxVariables (p : Shared.Codes.FinitePrograms.Program) (x : List Bool) (bound fuel : Nat) : Nat :=
  maxWidth p x bound fuel+3*bound+maxGates p x bound fuel

open Shared.ComplexityBridge.CircuitPairWitness
open Shared.ComplexityBridge.CircuitWitness
open Shared.ComplexityBridge.CircuitBounded
open Shared.ComplexityBridge.CircuitProgramMove
open Shared.Codes.FiniteProgramTotalize

theorem pairPrefix_length (x : List Bool) : (pairPrefix x).length = 6*x.length+1 := by
  simp [pairPrefix,BitstringEncoding.length_delimit,Shared.ComplexityBridge.bitstring_list_encoded_length]
  omega

theorem pair_window_bound (x : List Bool) (n bound fuel : Nat) (hn : n ≤ bound) :
    window (dummyInput (pairPrefix x) (3*n)) fuel ≤ maxWindow x bound fuel := by
  simp [window,dummyInput,pairPrefix_length,maxWindow]
  omega

theorem pair_template_bound (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (n bound fuel : Nat) (hn : n ≤ bound) :
    (template p (pairPrefix x) (3*n) fuel).length ≤ maxWidth p x bound fuel := by
  rw [template_length]
  have hw := pair_window_bound x n bound fuel hn
  dsimp [innerWidth,circuitWidth,inputWidth,maxWidth,maxStates]
  rw [totalProgram_length]
  omega

theorem pair_gates_bound (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (n bound fuel : Nat) (hn : n ≤ bound) :
    (witnessGates p (pairPrefix x) (3*n) fuel).length ≤ maxGates p x bound fuel := by
  have hw := pair_window_bound x n bound fuel hn
  have hi :
      (2*(2+4*(p.length+3))+(1+4*(2*window (dummyInput (pairPrefix x) (3*n)) fuel+1))) +
        (p.length+3)*(2+4*(p.length+3)) ≤
      (2*(2+4*(p.length+3))+(1+4*(2*maxWindow x bound fuel+1))) +
        (p.length+3)*(2+4*(p.length+3)) := by omega
  have hh := Nat.mul_le_mul_left fuel hi
  simpa [witnessGates_length,maxGates,maxStates] using hh

theorem pair_uniform_clause_bound (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (n bound fuel : Nat) (hn : n ≤ bound) : (pairFormula p x n fuel).length ≤ maxClauses p x bound fuel := by
  have hc := pairFormula_clause_count p x n fuel
  have hw := pair_template_bound p x n bound fuel hn
  have hg := pair_gates_bound p x n bound fuel hn
  dsimp [maxClauses]
  omega

theorem pair_uniform_variable_bound (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (n bound fuel : Nat) (hn : n ≤ bound) :
    ∀ c ∈ pairFormula p x n fuel, ∀ lit ∈ c, lit.1 ≤ maxVariables p x bound fuel := by
  intro c hc lit hl
  have hv := pairFormula_variable_bound p x n fuel c hc lit hl
  have hw := pair_template_bound p x n bound fuel hn
  have hg := pair_gates_bound p x n bound fuel hn
  dsimp [maxVariables]
  omega

/-- A polynomial numerical bound on the serialized bounded-witness CNF.
Fuel is its numerical value; this is not a binary-clock running-time bound. -/
theorem boundedPairFormula_encoded_length (p : Shared.Codes.FinitePrograms.Program) (x : List Bool)
    (bound fuel : Nat) :
    (BitstringEncoding.bitEncode (boundedPairFormula p x bound fuel)).length ≤
      (1+(bound+1)*maxClauses p x bound fuel)*
        (2*((bound+1+4)*(4*(2*(maxVariables p x bound fuel+(bound+1)+1))+5))+1) := by
  let fs := (List.range (bound+1)).map fun n => pairFormula p x n fuel
  have hc : ∀ f ∈ fs, ∀ c ∈ f, c.length ≤ 3 := by
    intro f hm
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
    exact pairFormula_clause_length p x n fuel
  have hv : ∀ f ∈ fs, ∀ c ∈ f, ∀ lit ∈ c, lit.1 ≤ maxVariables p x bound fuel := by
    intro f hm
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
    exact pair_uniform_variable_bound p x n bound fuel (by have h := List.mem_range.mp hn; omega)
  have hl : ∀ f ∈ fs, f.length ≤ maxClauses p x bound fuel := by
    intro f hm
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hm
    exact pair_uniform_clause_bound p x n bound fuel (by have h := List.mem_range.mp hn; omega)
  have h := disjoin_encoded_length fs (maxVariables p x bound fuel) (maxClauses p x bound fuel) hc hv hl
  simpa [boundedPairFormula,fs] using h

namespace Fixtures
def yes : Shared.Codes.FinitePrograms.Program := [((false,false,0,2),(false,false,0,2))]
def no : Shared.Codes.FinitePrograms.Program := [((false,false,0,1),(false,false,0,1))]
def witnessBit : Shared.Codes.FinitePrograms.Program :=
  [((false,true,1,0),(false,true,1,0)), ((true,true,2,0),(true,true,2,0)),
    ((false,false,0,1),(false,false,0,2))]

example : sat (BitstringEncoding.bitEncode (boundedPairFormula witnessBit [] 1 3)) = true := by
  apply (sat_boundedPairFormula_iff witnessBit [] 1 3).2
  exact ⟨[true],by decide,by decide⟩

example : sat (BitstringEncoding.bitEncode (boundedPairFormula witnessBit [] 0 3)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (boundedPairFormula witnessBit [] 0 3)) with
  | false => rfl
  | true =>
    obtain ⟨w,hw,h⟩ := (sat_boundedPairFormula_iff witnessBit [] 0 3).1 hs
    have he : w = [] := List.length_eq_zero_iff.mp (by omega)
    subst w
    cases h

example : ¬ Shared.ComplexityBridge.CircuitPairWitness.Shape (wire [true,true,true]) 0 1 := by
  simp [Shared.ComplexityBridge.CircuitPairWitness.Shape,wire]
example : sat (BitstringEncoding.bitEncode (boundedPairFormula yes [] 2 1)) = true := by
  apply (sat_boundedPairFormula_iff yes [] 2 1).2
  exact ⟨[],by decide,by decide⟩
example : sat (BitstringEncoding.bitEncode (boundedPairFormula no [] 2 1)) = false := by
  cases hs : sat (BitstringEncoding.bitEncode (boundedPairFormula no [] 2 1)) with
  | false => rfl
  | true =>
    obtain ⟨w,_,h⟩ := (sat_boundedPairFormula_iff no [] 2 1).1 hs
    simp [no,Shared.Codes.FinitePrograms.bounded,Shared.Codes.FinitePrograms.run,
      Shared.Codes.FinitePrograms.advance,Shared.Codes.FinitePrograms.step,
      Shared.Codes.FinitePrograms.initial] at h
example : sat (BitstringEncoding.bitEncode (disjoin [])) = false := by decide
end Fixtures

end Shared.ComplexityBridge.CNFDisjunction
