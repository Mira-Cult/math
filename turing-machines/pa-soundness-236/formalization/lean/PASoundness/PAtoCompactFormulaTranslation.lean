import PASoundness.PAtoCompactTermTranslation
import PASoundness.PAtoCompactOpenScope

/-! Concrete recursion over mathlib's PA syntax, using the separately stated
term-graph construction. This is candidate syntax only: no truth preservation,
K axiom transport, quotient congruence, or full capture invariant is asserted. -/
namespace PASoundness.PAtoCompactFormulaTranslation

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.CompactProof

/-- A fresh label larger than the scope's free variables and all currently
active de Bruijn-level labels. -/
def scopeBase {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) : Nat :=
  (φ.freeVarFinset ∪ Finset.univ.image bound).sup id + 1

/-- For every free variable actually occurring in the scope, the selected
label lies strictly above it. -/
theorem free_lt_scopeBase {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) (x : Nat) (hx : x ∈ φ.freeVarFinset) : x < scopeBase φ bound := by
  unfold scopeBase
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id) (Finset.mem_union_left _ hx))

/-- Every currently active de Bruijn label is below the selected label. -/
theorem bound_lt_scopeBase {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) (i : Fin n) : bound i < scopeBase φ bound := by
  unfold scopeBase
  exact Nat.lt_succ_of_le (Finset.le_sup (f := id)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))

/-- In particular, adjoining this label preserves injectivity of an existing
mapping of active bound levels. -/
theorem bound_snoc_injective {n : Nat} (φ : Peano.language.BoundedFormula Nat n)
    (bound : Fin n → Nat) (hinj : Function.Injective bound) :
    Function.Injective (Fin.snoc bound (scopeBase φ bound)) := by
  apply Fin.snoc_injective_of_injective hinj
  rintro ⟨i, hi⟩
  exact (Nat.ne_of_lt (bound_lt_scopeBase φ bound i)) hi

/-- Explicit formula translation. Under equality, two fresh existential
labels receive candidate representatives of the term values, and candidate
isomorphism compares them. Each term subtree receives its own fresh block.
For `.all`, `Fin.snoc` maps mathlib's newest bound level to the new label;
the target quantifier is guarded by the candidate-domain formula. -/
def scopedFormula : (n : Nat) → Peano.language.BoundedFormula Nat n → (Fin n → Nat) → Formula
  | _, .falsum, _ => .bottom
  | n, .equal t u, bound =>
      let source : Peano.language.BoundedFormula Nat n := .equal t u
      let base := scopeBase source bound
      let varName : Nat ⊕ Fin n → Nat := Sum.elim id bound
      .ex base (.ex (base + 1)
        (andF (termGraph varName t base (base + 2))
          (andF (termGraph varName u (base + 1) (base + 2 + termCost t))
            (equivAt (base + 2 + termCost t + termCost u) base (base + 1)))))
  | _, .rel r _, _ => nomatch r
  | _, .imp a b, bound => .imp (scopedFormula _ a bound) (scopedFormula _ b bound)
  | n, .all body, bound =>
      let source : Peano.language.BoundedFormula Nat n := .all body
      let x := scopeBase source bound
      .all x (.imp (domainAt (x + 1) x) (scopedFormula _ body (Fin.snoc bound x)))

/-- Closed scope translation preserves each original free variable's literal
name. No alpha or semantic correctness result follows from this definition. -/
def formula (φ : Peano.Formula) : Formula := scopedFormula 0 φ Fin.elim0

def code (φ : Peano.Formula) : Nat := (formula φ).encode

/-- The implication requirement of the checked-PA-proof compiler is literal. -/
theorem code_imp (φ ψ : Peano.Formula) :
    code (φ.imp ψ) = CompactProof.imp (code φ) (code ψ) := rfl

/-- The dynamically freshened domain template encodes the literal reviewed
candidate with its exact renamed internal binders. -/
theorem domainAt_code (base x : Nat) : (domainAt base x).encode =
    PASoundness.PAtoCompactCandidateExact.candidateCode x
      (base + 32) (base + 33) (base + 34) (base + 35)
      (base + 36) (base + 37) (base + 38) (base + 39) := by rfl

/-- One top-level scoped universal has the intended standard-HF truth
provided the generated body preserves the actual scope opened at the chosen
fresh label. This is an explicit premise, not a full formula-truth theorem. -/
theorem topAll_truth_of_body (φ : Peano.language.BoundedFormula Nat 1)
    (bodyTruth : ∀ v : Nat → Nat,
      let x := scopeBase (φ.all : Peano.Formula) Fin.elim0
      let body := (scopedFormula 1 φ (Fin.snoc Fin.elim0 x)).encode
      (PASoundness.CompactMatrix.decode body).Realize
          (PASoundness.PAtoCompactOpenScope.ordinalAssignment v) ↔
        (PASoundness.PAtoCompactOpenScope.openOne φ x).Realize v)
    (v : Nat → Nat) :
    (PASoundness.CompactMatrix.decode (code (φ.all : Peano.Formula))).Realize
        (PASoundness.PAtoCompactOpenScope.ordinalAssignment v) ↔
      FirstOrder.Language.Formula.Realize φ.all v := by
  let x := scopeBase (φ.all : Peano.Formula) Fin.elim0
  have hf : x ∉ φ.freeVarFinset := by
    intro hx
    have hl := free_lt_scopeBase (φ.all : Peano.Formula) Fin.elim0 x hx
    exact Nat.lt_irrefl x hl
  have hn : [x,x+33,x+34,x+35,x+36,x+37,x+38,x+39,x+40].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, List.nodup_nil, not_false_eq_true, and_true]
    repeat' apply And.intro
    all_goals omega
  change (PASoundness.CompactMatrix.decode
      (allCode x (imp (domainAt (x+1) x).encode
        (scopedFormula 1 φ (Fin.snoc Fin.elim0 x)).encode))).Realize _ ↔ _
  rw [domainAt_code]
  simp only [PASoundness.PAtoCompactCandidateExact.candidateCode]
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    PASoundness.PAtoCompactOpenScope.guarded_scope_all_truth φ x
      (x+33) (x+34) (x+35) (x+36) (x+37) (x+38) (x+39) (x+40)
      (scopedFormula 1 φ (Fin.snoc Fin.elim0 x)).encode hf hn bodyTruth v

end PASoundness.PAtoCompactFormulaTranslation

#print axioms PASoundness.PAtoCompactFormulaTranslation.code_imp
#print axioms PASoundness.PAtoCompactFormulaTranslation.bound_snoc_injective
#print axioms PASoundness.PAtoCompactFormulaTranslation.domainAt_code
#print axioms PASoundness.PAtoCompactFormulaTranslation.topAll_truth_of_body
