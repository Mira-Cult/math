import PASoundness.PeanoQuotientGap

/-! Object-level PA successor steps for explicit quotient/remainder rows. -/
namespace PASoundness.PeanoDivisionSuccessor
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic PeanoAdditionAssociative PeanoMultiplyQuotientStep

private theorem or_left {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ : FOL.Formula L} (h : FOL.Context A Γ φ) :
    FOL.Context A Γ (φ ⊔ ψ) := by
  change FOL.Context A Γ (φ.not.imp ψ)
  apply FOL.Context.deduction
  exact FOL.Context.explode ψ (.mp (FOL.Context.head Γ φ.not) (FOL.Context.under h φ.not))

private theorem or_right {L : Language} {A : FOL.Formula L → Prop}
    {Γ : List (FOL.Formula L)} {φ ψ : FOL.Formula L} (h : FOL.Context A Γ ψ) :
    FOL.Context A Γ (φ ⊔ ψ) := FOL.Context.lift h φ.not

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

/-- If the incremented remainder stays below the modulus, PA derives the next
row with the same quotient and incremented remainder. -/
theorem advance_remainder (x q m r : Peano.Term) :
    FormulaProves (((x.equal (add (mul q m) r))).imp
      ((CompactArithmetic.less (succ r) m).imp
        (((succ x).equal (add (mul q m) (succ r))) ⊓
          CompactArithmetic.less (succ r) m))) := by
  let E := x.equal (add (mul q m) r)
  let L := CompactArithmetic.less (succ r) m
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [L, E] E :=
    FOL.Context.under (FOL.Context.head [] E) L
  have hl : FOL.Context Peano.Axiom [L, E] L := FOL.Context.head _ _
  have hs : FOL.Context Peano.Axiom [L, E]
      ((succ x).equal (succ (add (mul q m) r))) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) he
  have heq : FOL.Context Peano.Axiom [L, E]
      ((succ x).equal (add (mul q m) (succ r))) :=
    FOL.Context.eqTrans hs (.closed (FOL.Derivation.eqSymm
      (.axiom (.add_succ (mul q m) r))))
  exact FOL.Context.conjunctionIntro heq hl

/-- If the incremented remainder equals the modulus, PA derives the next row
with incremented quotient and remainder zero, including the strict bound. -/
theorem wrap_remainder (x q m r : Peano.Term) :
    FormulaProves (((x.equal (add (mul q m) r))).imp
      (((succ r).equal m).imp
        (((succ x).equal (add (mul (succ q) m) zero)) ⊓
          CompactArithmetic.less zero m))) := by
  let E := x.equal (add (mul q m) r)
  let W := (succ r).equal m
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [W, E] E :=
    FOL.Context.under (FOL.Context.head [] E) W
  have hw : FOL.Context Peano.Axiom [W, E] W := FOL.Context.head _ _
  have hs : FOL.Context Peano.Axiom [W, E]
      ((succ x).equal (succ (add (mul q m) r))) :=
    .mp (.closed (PeanoOrderIrreflexive.succ_congr _ _)) he
  have hsum : FOL.Context Peano.Axiom [W, E]
      ((succ x).equal (add (mul q m) (succ r))) :=
    FOL.Context.eqTrans hs (.closed (FOL.Derivation.eqSymm
      (.axiom (.add_succ (mul q m) r))))
  have hmul : FOL.Context Peano.Axiom [W, E]
      ((succ x).equal (mul (succ q) m)) :=
    FOL.Context.eqTrans (FOL.Context.eqTrans hsum
      (.mp (.closed (add_right_congr (mul q m) _ _)) hw))
      (.closed (FOL.Derivation.eqSymm (mul_succ_left q m)))
  have heq : FOL.Context Peano.Axiom [W, E]
      ((succ x).equal (add (mul (succ q) m) zero)) :=
    FOL.Context.eqTrans hmul (.closed (FOL.Derivation.eqSymm
      (.axiom (.add_zero (mul (succ q) m)))))
  have hl : FOL.Context Peano.Axiom [W, E] (CompactArithmetic.less zero m) :=
    .mp (.mp (.closed (less_right_congr zero (succ r) m)) hw)
      (.closed (PeanoOrderTotality.zero_less_succ r))
  exact FOL.Context.conjunctionIntro heq hl

/-- A value below the modulus already has a row with quotient zero and
itself as remainder. In particular this supplies the zero-dividend base
whenever `0 < m`. -/
theorem zero_quotient_row (x m : Peano.Term) :
    FormulaProves ((CompactArithmetic.less x m).imp
      ((x.equal (add (mul zero m) x)) ⊓ CompactArithmetic.less x m)) := by
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have hzero : FormulaProves ((add (mul zero m) x).equal x) :=
    FOL.Derivation.eqTrans
      (.mp (add_left_congr x (mul zero m) zero) (PeanoMultiplication.zero_mul m))
      (zero_add x)
  exact FOL.Context.conjunctionIntro (.closed (FOL.Derivation.eqSymm hzero))
    (FOL.Context.head [] _)

private theorem less01 : CompactArithmetic.less (.var 0) (.var 1) =
    CompactArithmetic.exAt 5 ((add (.var 0) (succ (.var 5))).equal (.var 1)) := by
  simp [CompactArithmetic.less, CompactArithmetic.lessTemplate, CompactArithmetic.exAt,
    CompactArithmetic.v, FOL.allAt, Peano.add, Peano.succ,
    FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.Term.subst, FirstOrder.Language.Term.relabel,
    FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.relabel, FirstOrder.Language.BoundedFormula.mapTermRel,
    FirstOrder.Language.BoundedFormula.relabelAux]
  constructor
  · congr 1
    funext i
    fin_cases i
    · rfl
    · dsimp [FirstOrder.Language.Term.relabel, FirstOrder.Language.Term.subst]
      congr 1
      funext j
      fin_cases j
      rfl
  · rfl


theorem no_gap_vars :
    FormulaProves ((CompactArithmetic.less (.var 0) (.var 1)).imp
      (CompactArithmetic.less (.var 1) (succ (.var 0))).not) := by
  let R : Peano.Term := .var 0
  let M : Peano.Term := .var 1
  let D : Peano.Term := .var 5
  let row : Peano.Formula := (add R (succ D)).equal M
  let bad : Peano.Formula := CompactArithmetic.less M (succ R)
  have hrow : FormulaProves (row.imp bad.not) := by
    apply FOL.Context.closeEmpty
    apply FOL.Context.deduction
    apply FOL.Context.deduction
    have hr : FOL.Context Peano.Axiom [bad, row] row :=
      FOL.Context.under (FOL.Context.head [] row) bad
    have hb : FOL.Context Peano.Axiom [bad, row] bad := FOL.Context.head _ _
    have he : FOL.Context Peano.Axiom [bad, row] (M.equal (succ (add R D))) :=
      FOL.Context.eqTrans (FOL.Context.eqSymm hr) (.closed (.axiom (.add_succ R D)))
    have hs : FOL.Context Peano.Axiom [bad, row]
        (CompactArithmetic.less (succ (add R D)) (succ R)) :=
      .mp (.mp (.closed (PeanoQuotientGap.less_left_congr M (succ (add R D)) (succ R))) he) hb
    have hl : FOL.Context Peano.Axiom [bad, row] (CompactArithmetic.less (add R D) R) :=
      .mp (.closed (PeanoOrderSuccessor.less_succ_iff (add R D) R).2) hs
    exact .mp (.closed (PeanoQuotientGap.not_less_add R D)) hl
  have hfresh : 5 ∉ bad.not.freeVarFinset := by decide
  have h := PeanoBitPositionReduction.exists_elim 5 hfresh hrow
  simpa only [R, M, D, row, bad, less01, CompactArithmetic.exAt, FOL.existsAt] using h

private theorem subst_imp (φ ψ : Peano.Formula) (σ : Nat → Peano.Term) :
    (φ.imp ψ).subst σ = (φ.subst σ).imp (ψ.subst σ) := by rfl

private theorem subst_not (φ : Peano.Formula) (σ : Nat → Peano.Term) :
    φ.not.subst σ = (φ.subst σ).not := by
  simp [FirstOrder.Language.BoundedFormula.not, FirstOrder.Language.BoundedFormula.subst,
    FirstOrder.Language.BoundedFormula.mapTermRel]
  rfl

private def noGap (a b : Peano.Term) : Peano.Formula :=
  (CompactArithmetic.less a b).imp (CompactArithmetic.less b (succ a)).not

private theorem specialize (a b : Peano.Term) (name : Nat) (t : Peano.Term)
    (h : FormulaProves (noGap a b)) :
    FormulaProves (noGap
      (a.subst (fun y => if y = name then t else .var y))
      (b.subst (fun y => if y = name then t else .var y))) := by
  have h₁ := FOL.Derivation.mp
    (FOL.Derivation.logical (Axiom := Peano.Axiom) (.allElim (noGap a b) name t))
    (.generalize name h)
  simpa only [FOL.substAt, noGap, subst_imp, subst_not, CompactArithmetic.less_subst, PeanoArithmetic.succ_subst] using h₁

/-- No term lies strictly between a term and its successor for arbitrary arithmetic terms, including
terms sharing variables, by a capture-safe finite PA proof transformation. -/
theorem no_gap_all (a b : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a b).imp (CompactArithmetic.less b (succ a)).not) := by
  let support := a.varFinset ∪ b.varFinset
  let m := support.sup id + 2
  have hm : 2 ≤ m := by dsimp [m]; omega
  have fresh (n : Nat) (hn : m ≤ n) : n ∉ support := by
    intro h
    have hle : n ≤ support.sup id := Finset.le_sup (f := id) h
    dsimp [m] at hn
    omega
  have fa : m+1 ∉ a.varFinset := by
    intro h
    apply fresh (m+1) (by omega)
    simp [support, h]
  have h0 : FormulaProves (noGap (.var 0) (.var 1)) := no_gap_vars
  have h1 := specialize _ _ 0 (.var m) h0
  have h1' : FormulaProves (noGap (.var m) (.var 1)) := by
    simpa [FirstOrder.Language.Term.subst] using h1
  have h2 := specialize _ _ 1 (.var (m+1)) h1'
  have h2' : FormulaProves (noGap (.var m) (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m ≠ 1 by omega] using h2
  have h3 := specialize _ _ m a h2'
  have h3' : FormulaProves (noGap a (.var (m+1))) := by
    simpa [FirstOrder.Language.Term.subst, show m+1 ≠ m by omega] using h3
  have h4 := specialize _ _ (m+1) b h3'
  simpa [noGap, FirstOrder.Language.Term.subst,
    FOL.term_subst_fresh a (m+1) b fa] using h4

theorem next_remainder_cases (a m : Peano.Term) :
    FormulaProves ((CompactArithmetic.less a m).imp
      (((succ a).equal m) ⊔ CompactArithmetic.less (succ a) m)) := by
  let P := CompactArithmetic.less a m
  let E := (succ a).equal m
  let L := CompactArithmetic.less (succ a) m
  let G := CompactArithmetic.less m (succ a)
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  have htri : FOL.Context Peano.Axiom [P] ((E ⊔ L) ⊔ G) := by
    simpa only [E, L, G, PeanoOrderTotality.trichotomy] using
      (FOL.Context.closed (Γ := [P]) (PeanoOrderTotality.trichotomy_all (succ a) m))
  have hgood : FOL.Context Peano.Axiom [P] ((E ⊔ L).imp (E ⊔ L)) := by
    apply FOL.Context.deduction
    exact FOL.Context.head [P] (E ⊔ L)
  have hbad : FOL.Context Peano.Axiom [P] (G.imp (E ⊔ L)) := by
    apply FOL.Context.deduction
    have hp : FOL.Context Peano.Axiom [G, P] P :=
      FOL.Context.under (FOL.Context.head [] P) G
    have hn : FOL.Context Peano.Axiom [G, P] G.not :=
      .mp (.closed (no_gap_all a m)) hp
    exact FOL.Context.explode (E ⊔ L) (.mp hn (FOL.Context.head [P] G))
  exact or_elim htri hgood hbad


/-- Given an explicit no-gap premise, PA combines trichotomy and both row
updates into a disjunction of concrete valid successor rows. -/
theorem successor_rows_of_no_gap (x q m r : Peano.Term) :
    FormulaProves ((x.equal (add (mul q m) r)).imp
      ((CompactArithmetic.less m (succ r)).not.imp
        ((((succ x).equal (add (mul q m) (succ r))) ⊓
            CompactArithmetic.less (succ r) m) ⊔
          (((succ x).equal (add (mul (succ q) m) zero)) ⊓
            CompactArithmetic.less zero m)))) := by
  let E := x.equal (add (mul q m) r)
  let W := (succ r).equal m
  let L := CompactArithmetic.less (succ r) m
  let G := CompactArithmetic.less m (succ r)
  let A := ((succ x).equal (add (mul q m) (succ r))) ⊓ L
  let B := ((succ x).equal (add (mul (succ q) m) zero)) ⊓ CompactArithmetic.less zero m
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  let Γ := [G.not, E]
  have he : FOL.Context Peano.Axiom Γ E := FOL.Context.under (FOL.Context.head [] E) G.not
  have hn : FOL.Context Peano.Axiom Γ G.not := FOL.Context.head _ _
  have hw : FOL.Context Peano.Axiom Γ (W.imp (A ⊔ B)) := by
    apply FOL.Context.deduction
    apply or_right
    exact .mp (.mp (.closed (wrap_remainder x q m r)) (FOL.Context.under he W))
      (FOL.Context.head Γ W)
  have hl : FOL.Context Peano.Axiom Γ (L.imp (A ⊔ B)) := by
    apply FOL.Context.deduction
    apply or_left
    exact .mp (.mp (.closed (advance_remainder x q m r)) (FOL.Context.under he L))
      (FOL.Context.head Γ L)
  have hi : FOL.Context Peano.Axiom Γ ((W ⊔ L).imp (A ⊔ B)) := by
    apply FOL.Context.deduction
    exact or_elim (FOL.Context.head Γ (W ⊔ L))
      (FOL.Context.under hw (W ⊔ L)) (FOL.Context.under hl (W ⊔ L))
  have hg : FOL.Context Peano.Axiom Γ (G.imp (A ⊔ B)) := by
    apply FOL.Context.deduction
    exact FOL.Context.explode _ (.mp (FOL.Context.under hn G) (FOL.Context.head Γ G))
  exact or_elim (.closed (PeanoOrderTotality.trichotomy_all (succ r) m)) hi hg

/-- Every bounded quotient/remainder row advances to one of the two concrete
successor rows in PA. This does not assert existence of an initial row. -/
theorem successor_rows (x q m r : Peano.Term) :
    FormulaProves ((x.equal (add (mul q m) r)).imp
      ((CompactArithmetic.less r m).imp
        ((((succ x).equal (add (mul q m) (succ r))) ⊓
            CompactArithmetic.less (succ r) m) ⊔
          (((succ x).equal (add (mul (succ q) m) zero)) ⊓
            CompactArithmetic.less zero m)))) := by
  let E := x.equal (add (mul q m) r)
  let L := CompactArithmetic.less r m
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  have he : FOL.Context Peano.Axiom [L, E] E :=
    FOL.Context.under (FOL.Context.head [] E) L
  have hl : FOL.Context Peano.Axiom [L, E] L := FOL.Context.head _ _
  have hg : FOL.Context Peano.Axiom [L, E] (CompactArithmetic.less m (succ r)).not :=
    .mp (.closed (no_gap_all r m)) hl
  exact .mp (.mp (.closed (successor_rows_of_no_gap x q m r)) he) hg

end PASoundness.PeanoDivisionSuccessor
