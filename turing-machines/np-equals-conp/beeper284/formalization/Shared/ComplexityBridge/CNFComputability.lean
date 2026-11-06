import Shared.ComplexityBridge.CNF
import Mathlib.Computability.Partrec

/-! Partial recursion-theoretic computability results for the executable
CNF reference evaluator and a canonical-input witness bound. These results
do not establish any time bound or a TM2
simulation. The raw-input parser is addressed separately in
`ParserComputability.lean`; candidate tests still need computability proofs. -/
namespace Shared.ComplexityBridge.CNF

theorem variableOccurrences_primrec : Primrec variableOccurrences := by
  unfold variableOccurrences
  exact Primrec.list_map Primrec.list_flatten (Primrec.fst.comp Primrec.snd).to₂

theorem variableOccurrences_computable : Computable variableOccurrences :=
  variableOccurrences_primrec.to_comp

theorem assignments_primrec : Primrec assignments := by
  have hf : Primrec (fun p : Nat × List (List Bool) => p.2.map (false :: ·)) :=
    Primrec.list_map Primrec.snd
      (Primrec.list_cons.comp (Primrec.const false) Primrec.snd).to₂
  have ht : Primrec (fun p : Nat × List (List Bool) => p.2.map (true :: ·)) :=
    Primrec.list_map Primrec.snd
      (Primrec.list_cons.comp (Primrec.const true) Primrec.snd).to₂
  have hs : Primrec₂ (fun (_ : Nat) (xs : List (List Bool)) =>
      xs.map (false :: ·) ++ xs.map (true :: ·)) :=
    (Primrec.list_append.comp hf ht).to₂
  have hn := Primrec.nat_rec₁ ([[]] : List (List Bool)) hs
  apply hn.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [assignments, ih]

theorem assignments_computable : Computable assignments := assignments_primrec.to_comp

/-- Every satisfiable canonically encoded formula has a satisfying occurrence
assignment no longer than its encoded input. This is not an NP-membership proof:
no polynomial-time verifier or malformed-input bound is established here. -/
theorem bounded_occurrence_witness_iff (formula : Formula) :
    Satisfiable formula ↔ ∃ bits,
      bits.length ≤ (BitstringEncoding.bitEncode formula).length ∧
      evalFormula (assignment (variableOccurrences formula) bits) formula = true := by
  constructor
  · intro hs
    have hsat := (satFormula_correct formula).2 hs
    change (assignments (variableOccurrences formula).length).any
      (fun bits => evalFormula (assignment (variableOccurrences formula) bits) formula) = true at hsat
    obtain ⟨bits, hm, hv⟩ := List.any_eq_true.mp hsat
    refine ⟨bits, ?_, hv⟩
    have hl := (mem_assignments_iff bits _).1 hm
    rw [hl]
    exact occurrences_le_canonical_input_length formula
  · rintro ⟨bits, _, hb⟩
    exact ⟨assignment (variableOccurrences formula) bits, hb⟩

theorem assignment_findIdx (vars : List Nat) (bits : List Bool) (i : Nat) :
    assignment vars bits i =
      if vars.findIdx (fun v => v == i) < vars.length then
        (bits[(vars.findIdx (fun v => v == i))]?).getD false else false := by
  induction vars generalizing bits with
  | nil => simp [assignment]
  | cons v vs ih =>
    cases bits with
    | nil => simp [assignment]
    | cons b bs =>
      by_cases h : i = v
      · subst i
        simp [assignment, List.findIdx_cons]
      · have hv : (v == i) = false := by simp [Ne.symm h]
        simp [assignment, h, List.findIdx_cons, hv, ih]


theorem assignment_primrec :
    Primrec (fun p : (List Nat × List Bool) × Nat => assignment p.1.1 p.1.2 p.2) := by
  let idx (p : (List Nat × List Bool) × Nat) := p.1.1.findIdx (fun v => v == p.2)
  have hi : Primrec idx := by
    apply Primrec.list_findIdx (Primrec.fst.comp Primrec.fst)
    exact (Primrec.beq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).to₂
  have hl : Primrec (fun p : (List Nat × List Bool) × Nat => p.1.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.fst)
  have hg : Primrec (fun p : (List Nat × List Bool) × Nat => (p.1.2[idx p]?).getD false) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) hi)
      (Primrec.const false)
  have hn := Primrec.ite (Primrec.nat_lt.comp hi hl) hg (Primrec.const false)
  apply hn.of_eq
  intro p
  exact (assignment_findIdx p.1.1 p.1.2 p.2).symm


theorem list_any_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) := by
  have hfld := Primrec.list_foldr hf (Primrec.const false)
    (Primrec.or.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply hfld.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => simp [ih]

theorem list_all_primrec {α β : Type} [Primcodable α] [Primcodable β]
    {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).all (g a)) := by
  have hfld := Primrec.list_foldr hf (Primrec.const true)
    (Primrec.and.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply hfld.of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => simp [ih]


theorem evalLiteral_primrec : Primrec (fun p : (List Nat × List Bool) × Literal =>
    evalLiteral (assignment p.1.1 p.1.2) p.2) := by
  unfold evalLiteral
  exact Primrec.beq.comp
    (assignment_primrec.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
    (Primrec.snd.comp Primrec.snd)

theorem evalClause_primrec : Primrec (fun p : (List Nat × List Bool) × Clause =>
    evalClause (assignment p.1.1 p.1.2) p.2) := by
  unfold evalClause
  apply list_any_primrec Primrec.snd
  exact (evalLiteral_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

theorem evalFormula_primrec : Primrec (fun p : (List Nat × List Bool) × Formula =>
    evalFormula (assignment p.1.1 p.1.2) p.2) := by
  unfold evalFormula
  apply list_all_primrec Primrec.snd
  exact (evalClause_primrec.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd)).to₂

theorem satFormula_primrec : Primrec satFormula := by
  unfold satFormula
  apply list_any_primrec
    (assignments_primrec.comp (Primrec.list_length.comp variableOccurrences_primrec))
  exact (evalFormula_primrec.comp
    (Primrec.pair (Primrec.pair (variableOccurrences_primrec.comp Primrec.fst) Primrec.snd)
      Primrec.fst)).to₂

theorem satFormula_computable : Computable satFormula := satFormula_primrec.to_comp

end Shared.ComplexityBridge.CNF
