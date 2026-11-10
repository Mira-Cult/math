import PASoundness.PeanoPowerGrowth
import PASoundness.PeanoBetaCRTPrefixSubst
import PASoundness.PeanoBetaCRTAlpha

/-! PA uniqueness for literal beta-coded powers. -/
namespace PASoundness.PeanoPowerUnique
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic PeanoPowerPredecessor

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := rfl

def uniqueBody (n : Peano.Term) : Peano.Formula :=
  (pow2 n (.var 6)).imp
    ((pow2 n (.var 7)).imp ((.var 6 : Peano.Term).equal (.var 7)))

def uniqueAt (n : Peano.Term) : Peano.Formula := FOL.allAt 6 (FOL.allAt 7 (uniqueBody n))
def unique : Peano.Formula := uniqueAt (.var 0)

def pred₁ : Peano.Formula :=
  (pow2 (.var 0) (.var 8)) ⊓
    ((.var 6 : Peano.Term).equal (add (.var 8) (.var 8)))

def pred₂ : Peano.Formula :=
  (pow2 (.var 0) (.var 9)) ⊓
    ((.var 7 : Peano.Term).equal (add (.var 9) (.var 9)))

/-- Two predecessor rows and the induction hypothesis force equality of
the successor outputs. All witnesses are fixed free names. -/
theorem predecessors_unique : FormulaProves
    (pred₁.imp (pred₂.imp (unique.imp ((.var 6 : Peano.Term).equal (.var 7))))) := by
  let Γ := [unique, pred₂, pred₁]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hI : FOL.Context Peano.Axiom Γ unique := FOL.Context.head _ _
  have h1 : FOL.Context Peano.Axiom Γ pred₁ := .hypothesis (by simp [Γ])
  have h2 : FOL.Context Peano.Axiom Γ pred₂ := .hypothesis (by simp [Γ])
  have hinst1 := FOL.Context.allElim hI (.var 8)
  have hinst1' : FOL.Context Peano.Axiom Γ (FOL.allAt 7
      ((pow2 (.var 0) (.var 8)).imp
        ((pow2 (.var 0) (.var 7)).imp ((.var 8 : Peano.Term).equal (.var 7))))) := by
    rw [show FOL.substAt (FOL.allAt 7 (uniqueBody (.var 0))) 6 (.var 8) =
      FOL.allAt 7 (FOL.substAt (uniqueBody (.var 0)) 6 (.var 8)) from
        PeanoBetaCRTAlpha.subst_var_allAt _ 6 8 7 (by decide) (by decide)] at hinst1
    simpa [uniqueBody, FOL.substAt, subst_imp, pow2_subst, FOL.equality_subst,
      FirstOrder.Language.Term.subst] using hinst1
  have hinst2 := FOL.Context.allElim hinst1' (.var 9)
  have hinst2' : FOL.Context Peano.Axiom Γ
      ((pow2 (.var 0) (.var 8)).imp
        ((pow2 (.var 0) (.var 9)).imp ((.var 8 : Peano.Term).equal (.var 9)))) := by
    simpa [FOL.substAt, subst_imp, pow2_subst, FOL.equality_subst,
      FirstOrder.Language.Term.subst] using hinst2
  have he : FOL.Context Peano.Axiom Γ ((.var 8 : Peano.Term).equal (.var 9)) :=
    .mp (.mp hinst2' (FOL.Context.conjunctionLeft h1)) (FOL.Context.conjunctionLeft h2)
  have hl : FOL.Context Peano.Axiom Γ
      ((add (.var 8) (.var 8)).equal (add (.var 9) (.var 8))) :=
    .mp (.closed (PeanoAdditionAssociative.add_left_congr (.var 8) (.var 8) (.var 9))) he
  have hr : FOL.Context Peano.Axiom Γ
      ((add (.var 9) (.var 8)).equal (add (.var 9) (.var 9))) :=
    .mp (.closed (PeanoAdditionAssociative.add_right_congr (.var 9) (.var 8) (.var 9))) he
  exact FOL.Context.eqTrans (FOL.Context.eqTrans
    (FOL.Context.conjunctionRight h1) (FOL.Context.eqTrans hl hr))
      (FOL.Context.eqSymm (FOL.Context.conjunctionRight h2))

private theorem subst_and (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ ⊓ ψ).subst σ = (φ.subst σ) ⊓ (ψ.subst σ) := by
  change (φ.imp ψ.not).not.subst σ = ((φ.subst σ).imp (ψ.subst σ).not).not
  have sn (α : Peano.Formula) : α.not.subst σ = (α.subst σ).not := by
    simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.mapTermRel]; rfl
  rw [sn, show (φ.imp ψ.not).subst σ = (φ.subst σ).imp (ψ.not.subst σ) from rfl, sn]

private def body (x : Nat) : Peano.Formula :=
  (pow2 (.var 0) (.var 5)) ⊓ ((.var x : Peano.Term).equal (add (.var 5) (.var 5)))

theorem output6 : FormulaProves ((pow2 (succ (.var 0)) (.var 6)).imp
    (FOL.existsAt 8 ((pow2 (.var 0) (.var 8)) ⊓
      ((.var 6 : Peano.Term).equal (add (.var 8) (.var 8)))))) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim ((pow2 (succ (.var 0)) (.var 1)).imp predecessorPower) 1 (.var 6)))
    (.generalize 1 power_successor_predecessor)
  have hs : FOL.substAt predecessorPower 1 (.var 6) = FOL.existsAt 5 (body 6) := by
    unfold predecessorPower
    rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 1 6 5 (by decide) (by decide)]
    simp [FOL.substAt, body, subst_and, pow2_subst, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst]
  have hsimp : FOL.substAt ((pow2 (succ (.var 0)) (.var 1)).imp predecessorPower) 1 (.var 6) =
      (pow2 (succ (.var 0)) (.var 6)).imp (FOL.existsAt 5 (body 6)) := by
    change ((pow2 (succ (.var 0)) (.var 1)).subst (fun x => if x = 1 then .var 6 else .var x)).imp
      (FOL.substAt predecessorPower 1 (.var 6)) = _
    rw [hs]
    simp [pow2_subst, PeanoArithmetic.succ_subst, FirstOrder.Language.Term.subst]
  have h' : FormulaProves ((pow2 (succ (.var 0)) (.var 6)).imp (FOL.existsAt 5 (body 6))) := by
    rw [hsimp] at h
    exact h
  have hfresh : 8 ∉ (body 6).freeVarFinset := by decide
  have ha := PeanoBetaCRTAlpha.exists_alpha_forward (body 6) 5 8 (by decide) hfresh
  have hs' : FOL.substAt (body 6) 5 (.var 8) =
      (pow2 (.var 0) (.var 8)) ⊓ ((.var 6 : Peano.Term).equal (add (.var 8) (.var 8))) := by
    simp [FOL.substAt, body, subst_and, pow2_subst, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst]
  exact FOL.Derivation.compose h' (by simpa only [hs'] using ha)

theorem output7 : FormulaProves ((pow2 (succ (.var 0)) (.var 7)).imp
    (FOL.existsAt 9 ((pow2 (.var 0) (.var 9)) ⊓
      ((.var 7 : Peano.Term).equal (add (.var 9) (.var 9)))))) := by
  have h := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom)
      (.allElim ((pow2 (succ (.var 0)) (.var 1)).imp predecessorPower) 1 (.var 7)))
    (.generalize 1 power_successor_predecessor)
  have hs : FOL.substAt predecessorPower 1 (.var 7) = FOL.existsAt 5 (body 7) := by
    unfold predecessorPower
    rw [PeanoBetaCRTAlpha.subst_var_existsAt _ 1 7 5 (by decide) (by decide)]
    simp [FOL.substAt, body, subst_and, pow2_subst, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst]
  have hsimp : FOL.substAt ((pow2 (succ (.var 0)) (.var 1)).imp predecessorPower) 1 (.var 7) =
      (pow2 (succ (.var 0)) (.var 7)).imp (FOL.existsAt 5 (body 7)) := by
    change ((pow2 (succ (.var 0)) (.var 1)).subst (fun x => if x = 1 then .var 7 else .var x)).imp
      (FOL.substAt predecessorPower 1 (.var 7)) = _
    rw [hs]
    simp [pow2_subst, PeanoArithmetic.succ_subst, FirstOrder.Language.Term.subst]
  have h' : FormulaProves ((pow2 (succ (.var 0)) (.var 7)).imp (FOL.existsAt 5 (body 7))) := by
    rw [hsimp] at h
    exact h
  have hfresh : 9 ∉ (body 7).freeVarFinset := by decide
  have ha := PeanoBetaCRTAlpha.exists_alpha_forward (body 7) 5 9 (by decide) hfresh
  have hs' : FOL.substAt (body 7) 5 (.var 9) =
      (pow2 (.var 0) (.var 9)) ⊓ ((.var 7 : Peano.Term).equal (add (.var 9) (.var 9))) := by
    simp [FOL.substAt, body, subst_and, pow2_subst, FOL.equality_subst, add_subst,
      FirstOrder.Language.Term.subst]
  exact FOL.Derivation.compose h' (by simpa only [hs'] using ha)

theorem successor_wrapper
    (hcore : FormulaProves (pred₁.imp (pred₂.imp (unique.imp
      ((.var 6 : Peano.Term).equal (.var 7)))))) : FormulaProves
    (unique.imp ((pow2 (succ (.var 0)) (.var 6)).imp
      ((pow2 (succ (.var 0)) (.var 7)).imp ((.var 6 : Peano.Term).equal (.var 7))))) := by
  let E := (.var 6 : Peano.Term).equal (.var 7)
  let Z := FOL.existsAt 9 pred₂
  let Y := FOL.existsAt 8 pred₁
  have hm : FormulaProves (pred₂.imp (pred₁.imp (unique.imp E))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [unique,pred₁,pred₂]
    have h2 : FOL.Context Peano.Axiom Γ pred₂ := .hypothesis (by simp [Γ])
    have h1 : FOL.Context Peano.Axiom Γ pred₁ := .hypothesis (by simp [Γ])
    have hu : FOL.Context Peano.Axiom Γ unique := FOL.Context.head _ _
    exact .mp (.mp (.mp (.closed hcore) h1) h2) hu
  have hf9 : 9 ∉ (pred₁.imp (unique.imp E)).freeVarFinset := by decide
  have hz := PeanoBitPositionReduction.exists_elim 9 hf9 hm
  have hm' : FormulaProves (pred₁.imp (Z.imp (unique.imp E))) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    let Γ := [unique,Z,pred₁]
    have hz' : FOL.Context Peano.Axiom Γ Z := .hypothesis (by simp [Γ])
    have h1 : FOL.Context Peano.Axiom Γ pred₁ := .hypothesis (by simp [Γ])
    have hu : FOL.Context Peano.Axiom Γ unique := FOL.Context.head _ _
    exact .mp (.mp (.mp (.closed hz) hz') h1) hu
  have hf8 : 8 ∉ (Z.imp (unique.imp E)).freeVarFinset := by decide
  have hy := PeanoBitPositionReduction.exists_elim 8 hf8 hm'
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let P := pow2 (succ (.var 0)) (.var 6)
  let Q := pow2 (succ (.var 0)) (.var 7)
  let Γ := [Q,P,unique]
  have hp : FOL.Context Peano.Axiom Γ P := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.head _ _
  have hu : FOL.Context Peano.Axiom Γ unique := .hypothesis (by simp [Γ])
  have hy' : FOL.Context Peano.Axiom Γ Y := .mp (.closed output6) hp
  have hz' : FOL.Context Peano.Axiom Γ Z := .mp (.closed output7) hq
  exact .mp (.mp (.mp (.closed hy) hy') hz') hu


theorem base_syntax : FOL.substAt unique 0 zero = uniqueAt zero := by
  unfold unique uniqueAt
  rw [PeanoBetaCRTPrefixSubst.Syntax.subst_zero_allAt _ 0 6 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_zero_allAt _ 0 7 (by decide)]
  simp [FOL.substAt, uniqueBody, subst_imp, pow2_subst, FOL.equality_subst,
    FirstOrder.Language.Term.subst]

theorem succ_syntax : FOL.substAt unique 0 (succ (.var 0)) = uniqueAt (succ (.var 0)) := by
  unfold unique uniqueAt
  rw [PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_allAt _ 0 6 (by decide),
    PeanoBetaCRTPrefixSubst.Syntax.subst_succSelf_allAt _ 0 7 (by decide)]
  simp [FOL.substAt, uniqueBody, subst_imp, pow2_subst, FOL.equality_subst,
    FirstOrder.Language.Term.subst]

theorem unique_base : FormulaProves (uniqueAt zero) := by
  apply FOL.Derivation.generalize
  apply FOL.Derivation.generalize
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let A := pow2 zero (.var 6)
  let B := pow2 zero (.var 7)
  let Γ := [B,A]
  have ha : FOL.Context Peano.Axiom Γ A := .hypothesis (by simp [Γ])
  have hb : FOL.Context Peano.Axiom Γ B := .hypothesis (by simp [Γ])
  have hp : FOL.Context Peano.Axiom Γ ((.var 6 : Peano.Term).equal (succ zero)) :=
    .mp (.closed (PeanoPowerZero.power_zero_endpoint (.var 6))) ha
  have hq : FOL.Context Peano.Axiom Γ ((.var 7 : Peano.Term).equal (succ zero)) :=
    .mp (.closed (PeanoPowerZero.power_zero_endpoint (.var 7))) hb
  exact FOL.Context.eqTrans hp (FOL.Context.eqSymm hq)

theorem unique_of_step (h : FormulaProves (unique.imp (uniqueAt (succ (.var 0))))) :
    FormulaProves (FOL.allAt 0 unique) := by
  have hb : FormulaProves (FOL.substAt unique 0 zero) := by rw [base_syntax]; exact unique_base
  have hs : FormulaProves (unique.imp (FOL.substAt unique 0 (succ (.var 0)))) := by
    rw [succ_syntax]; exact h
  exact .mp (.mp (.axiom (.induction unique 0)) hb) (.generalize 0 hs)

theorem unique_open_of_step (h : FormulaProves (unique.imp (uniqueAt (succ (.var 0))))) :
    FormulaProves (uniqueBody (.var 0)) := by
  have hu : FormulaProves unique := by
    have ht := FOL.Derivation.mp
      (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim unique 0 (.var 0)))
      (unique_of_step h)
    simpa only [SyntaxTransport.substAt_self] using ht
  apply FOL.Context.closeEmpty
  have h6 : FOL.Context Peano.Axiom [] (FOL.allAt 7 (uniqueBody (.var 0))) :=
    FOL.Context.allSelf (.closed hu)
  exact FOL.Context.allSelf h6


/-- PA proves the successor induction step from two predecessor traces. -/
theorem unique_step : FormulaProves (unique.imp (uniqueAt (succ (.var 0)))) := by
  have hlocal := successor_wrapper predecessors_unique
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.generalize 6
  · intro ψ hψ
    have he : ψ = unique := by simpa only [List.mem_singleton] using hψ
    subst ψ
    simp [unique, uniqueAt, SyntaxTransport.allAt_freeVars]
  · apply FOL.Context.generalize 7
    · intro ψ hψ
      have he : ψ = unique := by simpa only [List.mem_singleton] using hψ
      subst ψ
      simp [unique, uniqueAt, SyntaxTransport.allAt_freeVars]
    · exact .mp (.closed hlocal) (FOL.Context.head [] unique)

/-- The literal beta-coded power predicate has at most one value. -/
theorem power_unique_vars : FormulaProves (uniqueBody (.var 0)) :=
  unique_open_of_step unique_step

def relation (n p q : Peano.Term) : Peano.Formula :=
  (pow2 n p).imp ((pow2 n q).imp (p.equal q))
private theorem specialize (n p q : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (relation n p q)) : FormulaProves (relation
      (n.subst (fun y => if y = name then t else .var y))
      (p.subst (fun y => if y = name then t else .var y))
      (q.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (relation n p q) name t))
    (.generalize name h)
  simpa only [FOL.substAt, relation, subst_imp, pow2_subst, FOL.equality_subst] using h₁

/-- Simultaneous arbitrary term instantiation, assuming the fixed-name PA theorem. -/
theorem all_terms (hbase : FormulaProves (relation (.var 0) (.var 6) (.var 7)))
    (n p q : Peano.Term) : FormulaProves (relation n p q) := by
  let support := n.varFinset ∪ p.varFinset ∪ q.varFinset
  let k := support.sup id + 8
  have hk : 8 ≤ k := by dsimp [k]; omega
  have fresh (a : Nat) (ha : k ≤ a) : a ∉ support := by
    intro h
    have hle : a ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [k] at ha
    omega
  have fn (a : Nat) (ha : k ≤ a) : a ∉ n.varFinset := by
    intro h; apply fresh a ha; simp [support, h]
  have fp (a : Nat) (ha : k ≤ a) : a ∉ p.varFinset := by
    intro h; apply fresh a ha; simp [support, h]
  have h1 := specialize _ _ _ 0 (.var k) hbase
  have h1' : FormulaProves (relation (.var k) (.var 6) (.var 7)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ _ 6 (.var (k+1)) h1'
  have h2' : FormulaProves (relation (.var k) (.var (k+1)) (.var 7)) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 6 by omega] using h2
  have h3 := specialize _ _ _ 7 (.var (k+2)) h2'
  have h3' : FormulaProves (relation (.var k) (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k ≠ 7 by omega,
      show k+1 ≠ 7 by omega] using h3
  have h4 := specialize _ _ _ k n h3'
  have h4' : FormulaProves (relation n (.var (k+1)) (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, show k+1 ≠ k by omega,
      show k+2 ≠ k by omega] using h4
  have h5 := specialize _ _ _ (k+1) p h4'
  have h5' : FormulaProves (relation n p (.var (k+2))) := by
    simpa [FirstOrder.Language.Term.subst, FOL.term_subst_fresh n (k+1) p (fn _ (by omega)),
      show k+2 ≠ k+1 by omega] using h5
  have h6 := specialize _ _ _ (k+2) q h5'
  simpa [FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh n (k+2) q (fn _ (by omega)),
    FOL.term_subst_fresh p (k+2) q (fp _ (by omega))] using h6


/-- PA uniqueness for arbitrary, possibly overlapping, arithmetic terms. -/
theorem power_unique (n p q : Peano.Term) : FormulaProves
    ((pow2 n p).imp ((pow2 n q).imp (p.equal q))) :=
  all_terms power_unique_vars n p q

end PASoundness.PeanoPowerUnique

#print axioms PASoundness.PeanoPowerUnique.power_unique_vars
#print axioms PASoundness.PeanoPowerUnique.power_unique

