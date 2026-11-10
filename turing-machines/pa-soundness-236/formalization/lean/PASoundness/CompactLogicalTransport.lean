import PASoundness.FOLQuantifierDerivations
import PASoundness.CompactSyntaxBridge
import PASoundness.CompactArithmetic
import PASoundness.CompactSemantics

/-!
# Finite logical proof transport for the exact compact interpretation

The numeric implication constructor has a zero alias: `imp 0 0 = 0`. The
expression language here names finite constructor expressions while retaining
raw numeric formulas as leaves. `Expr.proofEquivalent` proves that expanding
such an expression before interpretation is interderivable with interpreting
its exact numeric code. This is an object-level finite proof, not semantic
completeness. It lets the compact logical schemas be transported without
silently changing their numeric ABI.
-/

namespace PASoundness.CompactLogicalTransport

open FirstOrder FirstOrder.Language
open CompactProof CompactMatrix CompactArithmetic
open FOL (Derivation)

abbrev interpreted (code : Nat) : Peano.Formula := translate (decode code)

variable {A : Peano.Formula → Prop}

/-- The actual implication alias is handled by two finite propositional proofs. -/
theorem interpreted_imp (a b : Nat) :
    Derivation.Equivalent A ((interpreted a).imp (interpreted b))
      (interpreted (imp a b)) := by
  by_cases h : imp a b = 0
  · obtain ⟨rfl,rfl⟩ := (CompactSemantics.imp_eq_zero a b).mp h
    simp only [interpreted, h, CompactSemantics.decode_zero, translate]
    exact Derivation.Equivalent.of_provable (Derivation.identity ⊤) Derivation.top
  · simp only [interpreted, CompactSemantics.decode_imp a b h, translate]
    exact Derivation.Equivalent.refl _

/-- Constructor expressions preserve raw numeric subformulas and all literal
named variables. They are finite syntax used in the proof translation only. -/
inductive Expr
  | raw : Nat → Expr
  | imp : Expr → Expr → Expr
  | member : Nat → Nat → Expr
  | equal : Nat → Nat → Expr
  | all : Nat → Expr → Expr

namespace Expr

def code : Expr → Nat
  | .raw a => a
  | .imp a b => CompactProof.imp a.code b.code
  | .member a b => CompactProof.member a b
  | .equal a b => CompactProof.equal a b
  | .all x a => allCode x a.code

def formula : Expr → Peano.Formula
  | .raw a => interpreted a
  | .imp a b => a.formula.imp b.formula
  | .member a b => bitFormula (.var a) (.var b)
  | .equal a b => (Term.var a).equal (.var b)
  | .all x a => FOL.allAt x a.formula

/-- Actual finite proof transport through every constructor expression. -/
theorem proofEquivalent (e : Expr) :
    Derivation.Equivalent A e.formula (interpreted e.code) := by
  induction e with
  | raw a => exact .refl _
  | imp a b ia ib => exact (ia.imp ib).trans (interpreted_imp a.code b.code)
  | member a b =>
    rw [code, interpreted, CompactSemantics.decode_member]
    exact .refl _
  | equal a b =>
    rw [code, interpreted, CompactSemantics.decode_equal]
    exact .refl _
  | all x a ih =>
    rw [code, interpreted, CompactSemantics.decode_all]
    exact ih.all x

theorem transport {e : Expr} (d : Derivation A e.formula) :
    Derivation A (interpreted e.code) := (proofEquivalent e).forward d

def neg (a : Expr) : Expr := .imp a (.raw 1)
def ex (x : Nat) (a : Expr) : Expr := neg (.all x (neg a))
def both (a b : Expr) : Expr := neg (.imp a (neg b))

end Expr

/-- A finite constructor expression for each source schema. No arithmetic
axiom or proof-transport conclusion is hidden in this definition. -/
def axiomExpr (selector a b c u : Nat) : Expr :=
  match selector with
  | 0 => .ex a (.equal a b)
  | 1 => .imp (.all a (.imp (.raw b) (.raw c)))
      (.imp (.all a (.raw b)) (.all a (.raw c)))
  | 2 => .imp (.member a b) (.imp (.equal b c) (.member a c))
  | 3 => .imp (.all a (.all b (.raw c))) (.all b (.all a (.raw c)))
  | 4 => .imp (.equal a b) (.imp (.member a c) (.member b c))
  | 5 => .imp (.ex a (.all a (.raw b))) (.raw b)
  | 6 => .imp (.equal a b) (.imp (.equal a c) (.equal b c))
  | 7 => .imp (.imp (.imp (.raw c) (.raw u)) (.raw a))
      (.imp (.imp (.raw a) (.raw c)) (.imp (.raw b) (.raw c)))
  | _ => if c = a ∨ c = b then .raw 0 else
      .both
        (.ex c (.both
          (.all b (.both
            (.imp (.member a b) (.imp (.raw c) (.member c b)))
            (.imp (.member c b) (.raw c))))
          (.imp (.raw c) (.member c b))))
        (.both
          (.imp (.equal a b) (.all c (.equal a b)))
          (.imp (.member a b) (.all c (.member a b))))

theorem axiomExpr_code (selector a b c u : Nat) :
    (axiomExpr selector a b c u).code = axiomCode selector a b c u := by
  unfold axiomExpr axiomCode
  split <;> simp only [Expr.code, Expr.ex, Expr.neg, Expr.both,
    CompactProof.existsCode, CompactProof.neg, CompactProof.both]
  split <;> rfl

theorem transport_axiom {selector a b c u : Nat}
    (d : Derivation A (axiomExpr selector a b c u).formula) :
    Derivation A (interpreted (axiomCode selector a b c u)) := by
  rw [← axiomExpr_code]
  exact Expr.transport d


/-- Capture-avoiding substitution of an equality is exact finite syntax. -/
theorem equality_subst {L : Language} {α β : Type} (t u : L.Term α)
    (σ : α → L.Term β) :
    (t.equal u).subst σ = (t.subst σ).equal (u.subst σ) :=
  FOL.equality_subst t u σ

private def v (x : Nat) : Peano.Term := .var x

/-- Ordinary equality substitution for the right argument of the expanded bit
formula, using a fresh placeholder rather than an implicit capture convention. -/
theorem bit_right_equality (a b c : Nat) :
    Derivation A (((v b).equal (v c)).imp
      ((bitFormula (v a) (v b)).imp (bitFormula (v a) (v c)))) := by
  have h := Derivation.logical (Axiom := A)
    (FOL.LogicalAxiom.eqSubst (bitFormula (v a) (v (a+1))) (a+1) (v b) (v c))
  simpa only [FOL.substAt, bitFormula_subst, v, Term.subst,
    if_neg (show a ≠ a+1 by omega), ↓reduceIte] using h

theorem bit_left_equality (a b c : Nat) :
    Derivation A (((v a).equal (v b)).imp
      ((bitFormula (v a) (v c)).imp (bitFormula (v b) (v c)))) := by
  have h := Derivation.logical (Axiom := A)
    (FOL.LogicalAxiom.eqSubst (bitFormula (v (c+1)) (v c)) (c+1) (v a) (v b))
  simpa only [FOL.substAt, bitFormula_subst, v, Term.subst,
    if_neg (show c ≠ c+1 by omega), ↓reduceIte] using h

/-- AX2 uses that genuine equality-substitution instance, then exchanges the
two temporary hypotheses using actual deduction. -/
theorem axiom2 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 2 a b c u)) := by
  apply transport_axiom
  apply FOL.Context.closeEmpty
  apply FOL.Context.deduction
  apply FOL.Context.deduction
  exact .mp (.mp (.closed (bit_right_equality a b c))
    (FOL.Context.head _ ((v b).equal (v c))))
    (FOL.Context.under (FOL.Context.head [] (bitFormula (v a) (v b))) ((v b).equal (v c)))

/-- AX4 is the left-argument equality-substitution instance. -/
theorem axiom4 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 4 a b c u)) := by
  apply transport_axiom
  exact bit_left_equality a b c

/-- AX6 is equality substitutivity, with an explicitly fresh placeholder. -/
theorem axiom6 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 6 a b c u)) := by
  apply transport_axiom
  have h := Derivation.logical (Axiom := A)
    (FOL.LogicalAxiom.eqSubst ((v (c+1)).equal (v c)) (c+1) (v a) (v b))
  simpa only [FOL.substAt, equality_subst, v, Term.subst,
    if_neg (show c ≠ c+1 by omega), ↓reduceIte, axiomExpr, Expr.formula] using h

/-- AX1 transports with a finite instance of genuine FOL quantifier distribution. -/
theorem axiom1 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 1 a b c u)) := by
  apply transport_axiom
  exact .logical (.allImp (interpreted b) (interpreted c) a)


/-- AX3 is transported by the proved named-quantifier commutation derivation. -/
theorem axiom3 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 3 a b c u)) := by
  apply transport_axiom
  exact Derivation.allCommute (interpreted c) a b

/-- Encoded compact negation is interderivable with genuine logical negation
once the single arithmetic bottom atom has an actual target-theory refutation. -/
theorem encoded_neg_equivalent (hbottom : Derivation A (interpreted 1).not)
    (φ : Peano.Formula) :
    Derivation.Equivalent A (φ.imp (interpreted 1)) φ.not :=
  (Derivation.Equivalent.refl φ).imp ⟨hbottom, Derivation.explosion _⟩

/-- The same finite proof equivalence through the literal two-negation encoding
of existential quantification, with all binder scopes preserved. -/
theorem encoded_exists_equivalent (hbottom : Derivation A (interpreted 1).not)
    (φ : Peano.Formula) (x : Nat) :
    Derivation.Equivalent A
      ((FOL.allAt x (φ.imp (interpreted 1))).imp (interpreted 1))
      (FOL.existsAt x φ) :=
  ((encoded_neg_equivalent hbottom φ).all x).imp
    ⟨hbottom, Derivation.explosion _⟩


/-- AX0's ordinary existential-equality proof is built from reflexivity and
all-elimination. The only arithmetic premise converts literal code-one
negation into the ordinary logical falsity used by genuine PA. -/
theorem axiom0 (hbottom : Derivation A (interpreted 1).not) (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 0 a b c u)) := by
  apply transport_axiom
  apply (encoded_exists_equivalent hbottom ((v a).equal (v b)) a).backward
  apply Derivation.mp (Derivation.existsIntro ((v a).equal (v b)) a (v b))
  have he : FOL.substAt ((v a).equal (v b)) a (v b) = (v b).equal (v b) := by
    simp only [FOL.substAt, equality_subst, v, Term.subst, ite_self, ↓reduceIte]
  rw [he]
  exact .logical (.eqRefl _)

/-- AX5 proof transport reduces only to the displayed arithmetic bottom
refutation; its quantifier logic and numeric aliases are fully constructed. -/
theorem axiom5 (hbottom : Derivation A (interpreted 1).not) (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 5 a b c u)) := by
  apply transport_axiom
  have he := (encoded_exists_equivalent hbottom (FOL.allAt a (interpreted b)) a).imp
    (Derivation.Equivalent.refl (interpreted b))
  exact he.backward (Derivation.existsAll (interpreted b) a)

/-- AX7 transports through the explicit K/S/classical derivation above,
including every possible numeric zero alias. -/
theorem axiom7 (a b c u : Nat) :
    Derivation A (interpreted (axiomCode 7 a b c u)) := by
  apply transport_axiom
  exact Derivation.compactPropositional _ _ _ _



/-- Connective transport may be composed with already-constructed finite
proof equivalences for the two arguments. -/
theorem encoded_both_congr (hbottom : Derivation A (interpreted 1).not)
    {φ φ' ψ ψ' : Peano.Formula}
    (hφ : Derivation.Equivalent A φ φ') (hψ : Derivation.Equivalent A ψ ψ') :
    Derivation.Equivalent A ((φ.imp (ψ.imp (interpreted 1))).imp (interpreted 1))
      (φ' ⊓ ψ') :=
  (hφ.imp (hψ.imp ⟨hbottom, Derivation.explosion _⟩)).imp
    ⟨hbottom, Derivation.explosion _⟩

theorem encoded_exists_congr (hbottom : Derivation A (interpreted 1).not)
    {φ φ' : Peano.Formula} (hφ : Derivation.Equivalent A φ φ') (x : Nat) :
    Derivation.Equivalent A ((FOL.allAt x (φ.imp (interpreted 1))).imp (interpreted 1))
      (FOL.existsAt x φ') :=
  ((hφ.imp ⟨hbottom, Derivation.explosion _⟩).all x).imp
    ⟨hbottom, Derivation.explosion _⟩

theorem encoded_both_intro (hbottom : Derivation A (interpreted 1).not)
    {φ ψ : Peano.Formula} (hφ : Derivation A φ) (hψ : Derivation A ψ) :
    Derivation A ((φ.imp (ψ.imp (interpreted 1))).imp (interpreted 1)) :=
  (encoded_both_congr hbottom (.refl φ) (.refl ψ)).backward
    (FOL.Context.closeEmpty (FOL.Context.conjunctionIntro (.closed hφ) (.closed hψ)))

/-- The remaining substantive arithmetic instance of AX8, written with native
logical conjunction and existential quantification. The parameter c is also
the fresh set name; exact decoded-code freshness was proved separately. -/
def comprehensionFormula (a b c : Nat) : Peano.Formula :=
  FOL.existsAt c
    ((FOL.allAt b
      (((bitFormula (v a) (v b)).imp
        ((interpreted c).imp (bitFormula (v c) (v b)))) ⊓
       ((bitFormula (v c) (v b)).imp (interpreted c)))) ⊓
     ((interpreted c).imp (bitFormula (v c) (v b))))

/-- The guarded AX8 bundle reduces to its explicit comprehension formula.
Its two atomic vacuity clauses are constructed from the actual free-variable
sets and genuine FOL vacuity, not assumed as arithmetic obligations. -/
theorem axiom8_from_comprehension
    (hbottom : Derivation A (interpreted 1).not)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Derivation A (comprehensionFormula a b c))
    (a b c u : Nat) : Derivation A (interpreted (axiomCode 8 a b c u)) := by
  apply transport_axiom
  by_cases hcollision : c = a ∨ c = b
  · simp only [axiomExpr, if_pos hcollision, Expr.formula, interpreted,
      CompactSemantics.decode_zero, translate]
    exact Derivation.top
  have hca : c ≠ a := fun h => hcollision (Or.inl h)
  have hcb : c ≠ b := fun h => hcollision (Or.inr h)
  simp only [axiomExpr, if_neg hcollision, Expr.both, Expr.ex, Expr.neg, Expr.formula]
  apply encoded_both_intro hbottom
  · apply (encoded_exists_congr hbottom
      (encoded_both_congr hbottom
        ((encoded_both_congr hbottom (.refl _) (.refl _)).all b) (.refl _)) c).backward
    exact hcomprehension a b c hca hcb
  · apply encoded_both_intro hbottom
    · apply Derivation.logical
      apply FOL.LogicalAxiom.vacuous
      simp [Term.equal, Term.bdEqual, Term.relabel, BoundedFormula.freeVarFinset,
        Term.varFinsetLeft, hca, hcb]
    · apply Derivation.logical
      apply FOL.LogicalAxiom.vacuous
      simp [bitFormula_freeVars, Term.varFinset, hca, hcb]

/-- The logical portion of the literal nine-schema source has now been reduced
to a single explicit arithmetic refutation. The ninth schema is separately
exposed as the actual interpreted formula, not an opaque correspondence field. -/
theorem axiom_transport
    (hbottom : Derivation A (interpreted 1).not)
    (hcomprehension : ∀ a b c u,
      Derivation A (interpreted (axiomCode 8 a b c u)))
    (selector : Fin 9) (a b c u : Nat) :
    Derivation A (interpreted (axiomCode selector a b c u)) := by
  rcases selector with ⟨s,hs⟩
  have h : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨
      s = 6 ∨ s = 7 ∨ s = 8 := by omega
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact axiom0 hbottom a b c u
  · exact axiom1 a b c u
  · exact axiom2 a b c u
  · exact axiom3 a b c u
  · exact axiom4 a b c u
  · exact axiom5 hbottom a b c u
  · exact axiom6 a b c u
  · exact axiom7 a b c u
  · exact hcomprehension a b c u

/-- Actual induction on finite compact proof data. The two displayed object-
level arithmetic obligations remain unproved here; neither is a semantic
soundness hypothesis or the desired whole proof-transport conclusion. -/
theorem derivation_transport
    (hbottom : Derivation A (interpreted 1).not)
    (hcomprehension : ∀ a b c u,
      Derivation A (interpreted (axiomCode 8 a b c u)))
    {f : Nat} (d : KDerivation f) : Derivation A (interpreted f) := by
  induction d with
  | truth =>
    simp only [interpreted, CompactSemantics.decode_zero, translate]
    exact Derivation.top
  | «axiom» s a b c u => exact axiom_transport hbottom hcomprehension s a b c u
  | generalize x d ih =>
    rw [interpreted, CompactSemantics.decode_all]
    exact .generalize x ih
  | @mp a b da dab ia iab => exact .mp ((interpreted_imp a b).backward iab) ia

/-- Literal compact contradiction transports to an actual target-calculus
contradiction using the displayed finite proof construction. No consistency
of either calculus is used in this implication. -/
theorem contradiction_transport
    (hbottom : Derivation A (interpreted 1).not)
    (hcomprehension : ∀ a b c u,
      Derivation A (interpreted (axiomCode 8 a b c u)))
    (d : KDerivation 1) : Derivation A (⊥ : Peano.Formula) :=
  .mp hbottom (derivation_transport hbottom hcomprehension d)


/-- A sharper, explicit reduction to arithmetic bottom and the native
comprehension formula; all logical proof transformations are discharged. -/
theorem derivation_transport_from_comprehension
    (hbottom : Derivation A (interpreted 1).not)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Derivation A (comprehensionFormula a b c))
    {f : Nat} (d : KDerivation f) : Derivation A (interpreted f) :=
  derivation_transport hbottom (axiom8_from_comprehension hbottom hcomprehension) d


/-- The source's closed arithmetic interpretation is exactly finite grounding
followed by the canonical sentence embedding, as an equality of syntax trees. -/
theorem open_toPA (f : Nat) :
    FOL.openSentence (toPA f) = (interpreted f).subst (fun _ => Peano.zero) := by
  unfold FOL.openSentence toPA
  rw [SyntaxTransport.formula_subst_relabel]
  congr 1
  funext x
  unfold Peano.zero
  simp only [Term.relabel]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Conditional closed-sentence proof transport with only the two explicit
arithmetic derivability obligations. Grounding is a finite GEN/allElim proof;
standard-model soundness is not used to manufacture any PA derivation. -/
theorem proofToPA_of_arithmetic_obligations
    (hbottom : Peano.FormulaProves (interpreted 1).not)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Peano.FormulaProves (comprehensionFormula a b c))
    {f : Nat} (d : KDerivation f) : Peano.Proves (toPA f) := by
  change Derivation Peano.Axiom (FOL.openSentence (toPA f))
  rw [open_toPA]
  exact Derivation.ground Peano.FunctionSymbol.zero
    (derivation_transport_from_comprehension hbottom hcomprehension d)

/-- The same explicit finite proof transport covers every actual numeric
source certificate, using the separately proved origin of its postfix run. -/
theorem theoremCode_toPA_of_arithmetic_obligations
    (hbottom : Peano.FormulaProves (interpreted 1).not)
    (hcomprehension : ∀ a b c, c ≠ a → c ≠ b →
      Peano.FormulaProves (comprehensionFormula a b c))
    (code : Nat) : Peano.Proves (toPA (theoremCode code)) := by
  obtain ⟨d⟩ := theorem_origin code
  exact proofToPA_of_arithmetic_obligations hbottom hcomprehension d

end PASoundness.CompactLogicalTransport
