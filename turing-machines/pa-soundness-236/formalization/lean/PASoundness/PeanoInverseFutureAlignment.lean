import PASoundness.PeanoInverseFutureStep
import PASoundness.PeanoBetaCRTInvariant
import PASoundness.PeanoBetaCRTAlignment
import PASoundness.PeanoOrderTransitive
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Align the previously proved PA inverse-product step with the fixed CRT
invariant. The new-modulus inverse family remains an explicit premise; this
module neither derives it nor proves bounded CRT. The guard arithmetic is a
literal PA derivation, not a semantic rewrite. -/
namespace PASoundness.PeanoInverseFutureAlignment
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactArithmetic
open PeanoInverseFutureStep PeanoInverseProductBounded PeanoBetaCRTInvariant PeanoBetaCRTAlignment

def ren (x : Nat) : Peano.Term := if x = 10 then .var 7 else if x = 2 then .var 1 else if x = 3 then .var 2 else if x = 0 then .var 10 else .var x

theorem ren_sound (φ : Peano.Formula) (h : FormulaProves φ) : FormulaProves (φ.subst ren) := by
  have a := specialize φ 10 7 h
  have b := specialize _ 2 1 a
  have c := specialize _ 3 2 b
  have d := specialize _ 0 10 c
  have eq : ((((φ.subst (substName 10 7)).subst (substName 2 1)).subst (substName 3 2)).subst (substName 0 10)) = φ.subst ren := by
    simp only [SyntaxTransport.formula_subst_comp]
    congr 1
    funext x
    by_cases h0 : x = 0
    · subst x; rfl
    by_cases h2 : x = 2
    · subst x; rfl
    by_cases h3 : x = 3
    · subst x; rfl
    by_cases h10 : x = 10
    · subst x; rfl
    simp [ren, substName, h0,h2,h3,h10, FirstOrder.Language.Term.subst]
  rw [eq] at d
  exact d

def oldBody : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
  ((mul (.var 10) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))
def pairBody : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
  ((mul (modulus (.var 1) (.var 7)) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))
def outputBody : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
  ((mul (mul (.var 10) (modulus (.var 1) (.var 7))) (.var 3)).equal
    (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))

theorem pointwise_rename : (firstInverse.imp (targetSecond.imp targetProduct)).subst ren =
    oldBody.imp (pairBody.imp outputBody) := by
  simp [firstInverse, firstBody, targetSecond, targetSecondBody, targetProduct, targetProductMatrix,
    oldBody, pairBody, outputBody, boundaryFactor, modulus, Peano.add, Peano.mul, Peano.succ, Peano.zero,
    FOL.existsAt, FOL.allAt,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  repeat' first
    | rfl
    | constructor
    | (congr 1; funext i; fin_cases i <;>
        dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])

theorem pointwise : FormulaProves (oldBody.imp (pairBody.imp outputBody)) := by
  have h := ren_sound _ specialize_boundary
  simpa only [pointwise_rename] using h

-- The PA successor-guard argument was adapted from checked scratch by
-- Codex agent `/root/crt_pairs_uniform/gap`.
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

/-- For arbitrary terms, PA proves ¬(j<S k) → k<j. -/
theorem not_less_succ_implies_gt (j k : Peano.Term) :
    FormulaProves ((less j (succ k)).not.imp (less k j)) := by
  let H := (less j (succ k)).not
  let E := j.equal k
  let L := less j k
  let G := less k j
  let T := E ⊔ L
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hh : FOL.Context Peano.Axiom [H] H := FOL.Context.head [] H
  have he : FOL.Context Peano.Axiom [H] (E.imp G) := by
    apply FOL.Context.deduction
    have heq : FOL.Context Peano.Axiom [E,H] (k.equal j) :=
      FOL.Context.eqSymm (FOL.Context.head [H] E)
    have hj : FOL.Context Peano.Axiom [E,H] (less j (succ k)) :=
      .mp (.mp (.closed (PeanoQuotientGap.less_left_congr k j (succ k))) heq)
        (.closed (PeanoPowerTransition.self_less_succ k))
    exact FOL.Context.explode G (.mp (FOL.Context.under hh E) hj)
  have hl : FOL.Context Peano.Axiom [H] (L.imp G) := by
    apply FOL.Context.deduction
    have hj : FOL.Context Peano.Axiom [L,H] (less j (succ k)) :=
      .mp (.mp (.closed (PeanoOrderTransitive.less_transitive_all j k (succ k)))
        (FOL.Context.head [H] L)) (.closed (PeanoPowerTransition.self_less_succ k))
    exact FOL.Context.explode G (.mp (FOL.Context.under hh L) hj)
  have ht : FOL.Context Peano.Axiom [H] (T.imp G) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head [H] T)
      (FOL.Context.under he T) (FOL.Context.under hl T)
  have hg : FOL.Context Peano.Axiom [H] (G.imp G) := by
    apply FOL.Context.deduction
    exact FOL.Context.head [H] G
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all j k)) ht hg

def strictGuard : Peano.Formula := (less (.var 7) (.var 2)) ⊓ less (.var 2) (.var 8)
def targetGuard : Peano.Formula := (less (.var 2) (succ (.var 7))).not ⊓ less (.var 2) (.var 8)
def pairFamily : Peano.Formula := FOL.allAt 2 (strictGuard.imp pairBody)
def nextOutput : Peano.Formula := FOL.allAt 2 (targetGuard.imp outputBody)

/-- Under two explicit inverse families, the new product has inverse
witnesses at every index remaining after the current index. -/
theorem future_update : FormulaProves
    ((futureAt (.var 7) 10).imp (pairFamily.imp nextOutput)) := by
  let H := futureAt (.var 7) 10
  let Q := pairFamily
  let G := targetGuard
  let Γ := [G, Q, H]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  apply FOL.Context.generalize 2
  · intro ψ hψ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hψ
    rcases hψ with rfl | rfl <;> simp [pairFamily, futureAt]
  apply FOL.Context.deduction
  have hg : FOL.Context Peano.Axiom Γ G := FOL.Context.head _ _
  have hh : FOL.Context Peano.Axiom Γ H := .hypothesis (by simp [Γ])
  have hq : FOL.Context Peano.Axiom Γ Q := .hypothesis (by simp [Γ])
  have hn : FOL.Context Peano.Axiom Γ (less (.var 2) (succ (.var 7))).not :=
    FOL.Context.conjunctionLeft hg
  have hu : FOL.Context Peano.Axiom Γ (less (.var 2) (.var 8)) :=
    FOL.Context.conjunctionRight hg
  have hk : FOL.Context Peano.Axiom Γ (less (.var 7) (.var 2)) :=
    .mp (.closed (not_less_succ_implies_gt (.var 2) (.var 7))) hn
  have hnot : FOL.Context Peano.Axiom Γ (less (.var 2) (.var 7)).not :=
    .mp (.closed (PeanoOrderAsymmetry.less_asymmetric_all (.var 7) (.var 2))) hk
  have ho : FOL.Context Peano.Axiom Γ (((less (.var 2) (.var 7)).not) ⊓ less (.var 2) (.var 8)) :=
    FOL.Context.conjunctionIntro hnot hu
  have hs : FOL.Context Peano.Axiom Γ strictGuard := FOL.Context.conjunctionIntro hk hu
  have hfirst : FOL.Context Peano.Axiom Γ oldBody :=
    .mp (FOL.Context.allSelf hh) ho
  have hsecond : FOL.Context Peano.Axiom Γ pairBody :=
    .mp (FOL.Context.allSelf hq) hs
  exact .mp (.mp (.closed pointwise) hfirst) hsecond

/-- The invariant target is exactly the updated product family, with its
successor guard, after substituting the proposed output terms. -/
theorem next_future_alignment :
    FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct = nextOutput := by
  have h11 : 11 ∉ nextFuture.freeVarFinset := by decide
  rw [PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh nextFuture 11 alignedCode h11]
  have h2 : 2 ∉ alignedProduct.varFinset := by decide
  have hall (R : Peano.Formula) : FOL.substAt (FOL.allAt 2 R) 12 alignedProduct =
      FOL.allAt 2 (FOL.substAt R 12 alignedProduct) := by
    unfold FOL.substAt
    apply arbitrary_subst_all_at (fun x => if x = 12 then alignedProduct else .var x) 2
    · simp
    · intro x hx
      by_cases he : x = 12
      · subst x; simpa using h2
      · simp [he, Ne.symm hx]
  have hg : FOL.substAt targetGuard 12 alignedProduct = targetGuard :=
    substAt_fresh _ _ _ (by decide)
  let M : Peano.Formula := FOL.existsAt 3 (FOL.existsAt 4
    ((mul (.var 12) (.var 3)).equal
      (add (succ zero) (mul (.var 4) (modulus (.var 1) (.var 2))))))
  have hm : FOL.substAt M 12 alignedProduct = outputBody := by
    simp [FOL.substAt, M, outputBody, alignedProduct, modulus, FOL.existsAt, FOL.allAt,
      Peano.add, Peano.mul, Peano.succ, Peano.zero, FirstOrder.Language.Term.equal,
      FirstOrder.Language.Term.bdEqual, FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
      FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
      FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
      FirstOrder.Language.BoundedFormula.relabelAux]
    repeat' first
      | rfl
      | constructor
      | (congr 1; funext i; fin_cases i <;>
          dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst])
  change FOL.substAt (FOL.allAt 2 (targetGuard.imp M)) 12 alignedProduct = nextOutput
  rw [hall]
  change FOL.allAt 2 ((FOL.substAt targetGuard 12 alignedProduct).imp (FOL.substAt M 12 alignedProduct)) = nextOutput
  rw [hg, hm]
  rfl

theorem future_component_exact : FormulaProves
    ((futureAt (.var 7) 10).imp (pairFamily.imp
      (FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct))) := by
  rw [next_future_alignment]
  exact future_update

/-- Exact future component under the current CRT matrix and an explicitly
assumed strict-future family of inverses for the new modulus. -/
theorem future_component_of_matrix (φ : Peano.Formula) : FormulaProves
    (pairFamily.imp ((currentMatrix φ).imp
      (FOL.substAt (FOL.substAt nextFuture 11 alignedCode) 12 alignedProduct))) := by
  let C := currentMatrix φ
  let Q := pairFamily
  let Γ := [C,Q]
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have hc : FOL.Context Peano.Axiom Γ C := FOL.Context.head _ _
  have hq : FOL.Context Peano.Axiom Γ Q := FOL.Context.under (FOL.Context.head [] Q) C
  have hf : FOL.Context Peano.Axiom Γ (futureAt (.var 7) 10) :=
    FOL.Context.conjunctionRight hc
  exact .mp (.mp (.closed future_component_exact) hf) hq

end PASoundness.PeanoInverseFutureAlignment
