import PASoundness.FOLDerivations
import PASoundness.SyntaxTransport

/-! Finite quantified derived rules with explicit named-variable side conditions. -/
namespace PASoundness.FOL
open FirstOrder FirstOrder.Language
open SyntaxTransport
variable {L : Language} {A : Formula L → Prop}


/-- Equality atoms commute exactly with capture-avoiding term substitution. -/
theorem equality_subst {α β : Type} (t u : L.Term α) (σ : α → L.Term β) :
    (t.equal u).subst σ = (t.subst σ).equal (u.subst σ) := by
  simp only [FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    BoundedFormula.subst, BoundedFormula.mapTermRel,
    term_relabel_subst, term_subst_relabel]
  rfl

def existsAt (x : Nat) (φ : Formula L) : Formula L := (allAt x φ.not).not

namespace Context

theorem allElim {Γ : List (Formula L)} {φ : Formula L} {x : Nat}
    (h : Context A Γ (allAt x φ)) (t : Term L) : Context A Γ (substAt φ x t) :=
  .mp (.closed (.logical (.allElim φ x t))) h

theorem allSelf {Γ : List (Formula L)} {φ : Formula L} {x : Nat}
    (h : Context A Γ (allAt x φ)) : Context A Γ φ := by
  simpa only [substAt_self] using allElim h (.var x)

end Context

namespace Derivation

theorem allSelf (φ : Formula L) (x : Nat) : Derivation A ((allAt x φ).imp φ) := by
  simpa only [substAt_self] using
    (Derivation.logical (Axiom := A) (LogicalAxiom.allElim φ x (.var x)))

/-- Two ordinary eliminations followed by freshness-checked generalizations. -/
theorem allCommute (φ : Formula L) (x y : Nat) :
    Derivation A ((allAt x (allAt y φ)).imp (allAt y (allAt x φ))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.generalize y
  · intro ψ hψ
    have he : ψ = allAt x (allAt y φ) := by simpa only [List.mem_singleton] using hψ
    subst ψ
    simp only [allAt_freeVars, Finset.mem_erase]
    rintro ⟨_,hy,_⟩
    exact hy rfl
  · apply Context.generalize x
    · intro ψ hψ
      have he : ψ = allAt x (allAt y φ) := by simpa only [List.mem_singleton] using hψ
      subst ψ
      simp [allAt_freeVars]
    · exact Context.allSelf (Context.allSelf (Context.head [] (allAt x (allAt y φ))))

/-- Existential introduction is derived through all-elimination and classical
negation; the actual capture-avoiding substituted instance is the premise. -/
theorem existsIntro (φ : Formula L) (x : Nat) (t : Term L) :
    Derivation A ((substAt φ x t).imp (existsAt x φ)) := by
  have he : Derivation A ((allAt x φ.not).imp (substAt φ x t).not) :=
    .logical (.allElim φ.not x t)
  exact compose (doubleNegIntro _) (contrapose he)

theorem existsVacuous (φ : Formula L) (x : Nat) (hx : x ∉ φ.freeVarFinset) :
    Derivation A ((existsAt x φ).imp φ) := by
  have hn : x ∉ φ.not.freeVarFinset := by
    simpa only [BoundedFormula.not, BoundedFormula.freeVarFinset, Finset.union_empty] using hx
  exact compose (contrapose (.logical (.vacuous φ.not x hn)))
    (.logical (.classical φ))

/-- The compact exists-all logical schema has a finite ordinary FOL proof. -/
theorem existsAll (φ : Formula L) (x : Nat) :
    Derivation A ((existsAt x (allAt x φ)).imp φ) :=
  compose (existsVacuous (allAt x φ) x (by simp [allAt_freeVars]))
    (allSelf φ x)


/-- Replace finitely many named free variables by one language constant. -/
def groundNames (c : L.Functions 0) (xs : List Nat) (φ : Formula L) : Formula L :=
  φ.subst (fun x => if x ∈ xs then .func c Fin.elim0 else .var x)

theorem groundNames_nil (c : L.Functions 0) (φ : Formula L) :
    groundNames c [] φ = φ := by
  simp only [groundNames, List.not_mem_nil, ↓reduceIte, formula_subst_var]

theorem groundNames_cons (c : L.Functions 0) (x : Nat) (xs : List Nat) (φ : Formula L) :
    substAt (groundNames c xs φ) x (.func c Fin.elim0) = groundNames c (x :: xs) φ := by
  unfold substAt groundNames
  rw [formula_subst_comp]
  congr 1
  funext y
  by_cases hy : y ∈ xs
  · simp only [hy, ↓reduceIte, List.mem_cons, or_true, Term.subst]
    congr 1
    funext i
    exact Fin.elim0 i
  · by_cases he : y = x
    · subst y
      simp [hy, Term.subst]
    · simp only [hy, he, ↓reduceIte, List.mem_cons, or_self, Term.subst]

/-- Each replacement is justified by an actual generalization and an actual
all-elimination instance. This works for any nonlogical axiom predicate,
without assuming closure of that predicate under substitution. -/
theorem groundNames_proves (c : L.Functions 0) (xs : List Nat) {φ : Formula L}
    (h : Derivation A φ) : Derivation A (groundNames c xs φ) := by
  induction xs with
  | nil => simpa only [groundNames_nil] using h
  | cons x xs ih =>
    rw [← groundNames_cons]
    exact .mp (.logical (.allElim _ x (.func c Fin.elim0))) (.generalize x ih)

theorem groundNames_complete (c : L.Functions 0) (φ : Formula L) :
    groundNames c φ.freeVarFinset.toList φ = φ.subst (fun _ => .func c Fin.elim0) := by
  apply formula_subst_agree
  intro x hx
  simp only [Finset.mem_toList.mpr hx, ↓reduceIte]

/-- Finite free-variable grounding is a derived syntactic rule, not a
semantic-to-syntactic completeness step. -/
theorem ground (c : L.Functions 0) {φ : Formula L} (h : Derivation A φ) :
    Derivation A (φ.subst (fun _ => .func c Fin.elim0)) := by
  rw [← groundNames_complete c φ]
  exact groundNames_proves c _ h

end Derivation
end PASoundness.FOL
