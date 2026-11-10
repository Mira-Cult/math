import PASoundness.PeanoCommonMultiple
import PASoundness.PeanoBetaProductIncrement
import PASoundness.PeanoOrderTransitive
import PASoundness.PeanoBetaCRTParameter

/-! PA derivations supporting residue bounds for the conditional beta CRT endpoint.
The bounded-totality premise is explicit; no trace existence or semantic
soundness is used. -/
namespace PASoundness.PeanoBetaBoundedTotality
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoMultiplication CompactArithmetic
open PeanoAdditionAssociative PeanoMultiplyQuotientStep

theorem less_modulus (c j : Peano.Term) : FormulaProves (less c (modulus c j)) := by
  have hbase : FormulaProves (less c (succ c)) := PeanoPowerTransition.self_less_succ c
  have hplus : FormulaProves (less c (add (succ c) (mul j c))) :=
    .mp (PeanoQuotientGap.less_add_right c (succ c) (mul j c)) hbase
  have hsum : FormulaProves ((add c (mul j c)).equal (mul (succ j) c)) :=
    FOL.Derivation.eqTrans (add_comm c (mul j c))
      (FOL.Derivation.eqSymm (PeanoBetaProductIncrement.succ_mul j c))
  have he : FormulaProves ((add (succ c) (mul j c)).equal (modulus c j)) := by
    exact FOL.Derivation.eqTrans (add_succ_left c (mul j c))
      (.mp (PeanoOrderIrreflexive.succ_congr _ _) hsum)
  exact .mp (.mp (less_right_congr c (add (succ c) (mul j c)) (modulus c j)) he) hplus

theorem less_modulus_of_less (r c j : Peano.Term) :
    FormulaProves ((less r c).imp (less r (modulus c j))) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all r c (modulus c j)))
    (FOL.Context.head [] (less r c))) (.closed (less_modulus c j))

private theorem or_elim {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ χ : FOL.Formula L}
    (h : FOL.Context A Γ (φ ⊔ ψ)) (hφ : FOL.Context A Γ (φ.imp χ))
    (hψ : FOL.Context A Γ (ψ.imp χ)) : FOL.Context A Γ χ := by
  apply FOL.Context.dne
  apply FOL.Context.deduction
  have hnφ : FOL.Context A (χ.not :: Γ) φ.not :=
    .mp (FOL.Context.under (FOL.Context.contrapose hφ) χ.not) (FOL.Context.head Γ χ.not)
  have hψ' : FOL.Context A (χ.not :: Γ) ψ :=
    .mp (FOL.Context.under h χ.not) hnφ
  exact .mp (FOL.Context.head Γ χ.not) (.mp (FOL.Context.under hψ χ.not) hψ')

/-- An upper bound r≤R and strict R<c imply r is below any beta modulus. -/
theorem le_bound_less_modulus (r R c j : Peano.Term) :
    FormulaProves ((less r (succ R)).imp ((less R c).imp (less r (modulus c j)))) := by
  let A := less r (succ R)
  let B := less R c
  let E := r.equal R
  let L := less r R
  let T := less r (modulus c j)
  let Γ := [B,A]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hb : FOL.Context Peano.Axiom Γ B := FOL.Context.head _ _
  have ha : FOL.Context Peano.Axiom Γ A := FOL.Context.under (FOL.Context.head [] A) B
  have hRc : FOL.Context Peano.Axiom Γ (less R (modulus c j)) :=
    .mp (.closed (less_modulus_of_less R c j)) hb
  have he : FOL.Context Peano.Axiom Γ (E.imp T) := by
    apply FOL.Context.deduction
    have heq : FOL.Context Peano.Axiom (E :: Γ) (R.equal r) :=
      FOL.Context.eqSymm (FOL.Context.head Γ E)
    exact .mp (.mp (.closed (PeanoQuotientGap.less_left_congr R r (modulus c j))) heq)
      (FOL.Context.under hRc E)
  have hl : FOL.Context Peano.Axiom Γ (L.imp T) := by
    apply FOL.Context.deduction
    exact .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all r R (modulus c j)))
      (FOL.Context.head Γ L)) (FOL.Context.under hRc L)
  exact or_elim (.mp (.closed (PeanoCommonMultiple.BoundSplit.less_successor_cases r R)) ha) he hl

open PeanoBetaCRTResidueSelect

def boundedRows (φ : Peano.Formula) : Peano.Formula := FOL.allAt 2
  ((less (.var 2) (.var 8)).imp (FOL.existsAt 3
    (φ ⊓ less (.var 3) (succ (.var 16)))))

/-- A bound `R<C` transports every desired row with value at most R to the
literal beta-modulus bound, preserving each existential row witness. -/
theorem bounded_rows_to_totality (φ : Peano.Formula) :
    FormulaProves ((less (.var 16) (.var 1)).imp ((boundedRows φ).imp (totality φ))) := by
  let C := less (.var 16) (.var 1)
  let O := φ ⊓ less (.var 3) (succ (.var 16))
  let V := φ ⊓ less (.var 3) (modulus (.var 1) (.var 2))
  let T := FOL.existsAt 3 V
  have ht : FormulaProves (O.imp (C.imp T)) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [C,O]
    have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
    have ho : FOL.Context Peano.Axiom Γ O := FOL.Context.under (FOL.Context.head [] O) C
    have hp : FOL.Context Peano.Axiom Γ φ := FOL.Context.conjunctionLeft ho
    have hl : FOL.Context Peano.Axiom Γ (less (.var 3) (succ (.var 16))) := FOL.Context.conjunctionRight ho
    have hm : FOL.Context Peano.Axiom Γ (less (.var 3) (modulus (.var 1) (.var 2))) :=
      .mp (.mp (.closed (le_bound_less_modulus (.var 3) (.var 16) (.var 1) (.var 2))) hl) hc
    have hv : FOL.Context Peano.Axiom Γ V := FOL.Context.conjunctionIntro hp hm
    have hi := FOL.Derivation.existsIntro (A := Peano.Axiom) V 3 (.var 3)
    have hs : FOL.substAt V 3 (.var 3) = V := by
      unfold FOL.substAt
      have he : (fun y : Nat => if y = 3 then ((.var 3 : Peano.Term)) else (.var y : Peano.Term)) = (fun y => (.var y : Peano.Term)) := by
        funext y
        split <;> simp_all
      rw [he, SyntaxTransport.formula_subst_var]
    exact .mp (.closed (by simpa only [hs] using hi)) hv
  have hf : 3 ∉ (C.imp T).freeVarFinset := by
    have hc : 3 ∉ C.freeVarFinset := by decide
    have hv : 3 ∉ T.freeVarFinset := by
      simp [T, FOL.existsAt, SyntaxTransport.allAt_freeVars,
        FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset]
    simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hc, hv]
  have he := PeanoBitPositionReduction.exists_elim 3 hf ht
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl
    · simp [boundedRows, SyntaxTransport.allAt_freeVars]
    · decide
  apply FOL.Context.deduction
  let L := less (.var 2) (.var 8)
  let Γ := [L, boundedRows φ, C]
  have ho : FOL.Context Peano.Axiom Γ (FOL.existsAt 3 O) :=
    .mp (FOL.Context.allSelf (FOL.Context.under (FOL.Context.head [C] (boundedRows φ)) L))
      (FOL.Context.head _ _)
  have hc : FOL.Context Peano.Axiom Γ C := .hypothesis (by simp [Γ])
  exact .mp (.mp (.closed he) ho) hc

/-- A relation independent of the CRT parameter remains available when
quantifying over every bounded candidate parameter. -/
theorem bounded_rows_all_parameters (φ : Peano.Formula)
    (hφ1 : 1 ∉ φ.freeVarFinset) :
    FormulaProves ((boundedRows φ).imp (FOL.allAt 1
      (((less (.var 16) (.var 1)) ⊓ PeanoBetaCRTFuturePair.endpointAt8).imp (totality φ)))) := by
  have hf : 1 ∉ (boundedRows φ).freeVarFinset := by
    have hl : 1 ∉ (less (.var 2) (.var 8)).freeVarFinset := by decide
    have hr : 1 ∉ (less (.var 3) (succ (.var 16))).freeVarFinset := by decide
    have hi : 1 ∉ (φ ⊓ less (.var 3) (succ (.var 16))).freeVarFinset := by
      change 1 ∉ ((φ.imp (less (.var 3) (succ (.var 16))).not).not).freeVarFinset
      simp [FirstOrder.Language.BoundedFormula.freeVarFinset, hφ1, hr]
    simp [boundedRows, SyntaxTransport.allAt_freeVars, FOL.existsAt,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.freeVarFinset,
      hl, hi]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 1
  · intro ψ hψ
    have hp : ψ = boundedRows φ := by simpa using hψ
    subst ψ
    exact hf
  apply FOL.Context.deduction
  let Q := (less (.var 16) (.var 1)) ⊓ PeanoBetaCRTFuturePair.endpointAt8
  let Γ := [Q, boundedRows φ]
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.head _ _
  have hb : FOL.Context Peano.Axiom Γ (less (.var 16) (.var 1)) := FOL.Context.conjunctionLeft hq
  have ht : FOL.Context Peano.Axiom Γ (boundedRows φ) := FOL.Context.under (FOL.Context.head [] _) Q
  exact .mp (.mp (.closed (bounded_rows_to_totality φ)) hb) ht



/-- Standard meaning of the independently bounded input rows. This semantic
characterization is separate from the PA derivation. -/
theorem boundedRows_realize (φ : Peano.Formula) (ρ : Nat → Nat) :
    (boundedRows φ).Realize ρ ↔
      ∀ j : Nat, j < ρ 8 → ∃ r : Nat,
        φ.Realize (Function.update (Function.update ρ 2 j) 3 r) ∧ r ≤ ρ 16 := by
  classical
  simp [boundedRows, FOL.existsAt, FOL.realize_allAt, Classical.not_forall,
    CompactArithmetic.realize_less, Peano.realize_succ, Function.update, Nat.lt_succ_iff]

/-- From a relation independent of the beta parameter and having a uniformly
bounded value on each requested index, PA derives a bounded CRT solution.
The chosen parameter exceeds the same explicit bound; no power-trace or PA
soundness bridge is asserted. -/
theorem bounded_rows_solve (φ : Peano.Formula)
    (hφ1 : 1 ∉ φ.freeVarFinset) (hφ : PeanoBetaCRTAlignment.NamesSafe φ) :
    FormulaProves ((boundedRows φ).imp (PeanoBetaCRTParameter.boundedSolvedParameter φ)) := by
  have h := bounded_rows_all_parameters φ hφ1
  have h' : FormulaProves ((boundedRows φ).imp
      (PeanoBetaCRTParameter.totalityForBoundedEndpoints φ)) := by
    simpa only [PeanoBetaCRTParameter.totalityForBoundedEndpoints,
      PeanoBetaCRTParameter.boundedEndpoint] using h
  exact FOL.Derivation.compose h' (PeanoBetaCRTParameter.bounded_solution_of_totality φ hφ)

end PASoundness.PeanoBetaBoundedTotality
