import PASoundness.PAtoCompactLogicalFragment
import PASoundness.CompactFreshen
import PASoundness.CompactQuantifiers
import PASoundness.FOLQuantifierDerivations

/-! Capture-safe variable instantiation for the shared PA/compact logical
fragment. Freshening yields an alpha-equivalent K target; arbitrary arithmetic
terms and nonlogical PA axioms remain outside this construction. -/
namespace PASoundness.PAtoCompactVariableInstance
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactLogicalFragment
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactNamed

/-- Embed the shared syntax into K's richer named proof-transformation syntax. -/
def named : Form → CompactNamed.Formula
  | .bottom => .bottom
  | .equal x y => .equal x y
  | .imp a b => .imp (named a) (named b)
  | .all x a => .all x (named a)

@[simp] theorem named_encode (a : Form) : (named a).encode = compactCode a := by
  induction a <;> simp_all [named, CompactNamed.Formula.encode, compactCode]

theorem named_realize (a : Form) (ρ : Nat → Nat) :
    (named a).Realize ρ ↔ (paFormula a).Realize ρ := by
  rw [← CompactNamed.Formula.encode_realize, named_encode]
  exact (truth_preserved a ρ).symm

/-- On quantifier-free syntax, replacement is structurally literal: the PA
formula is exactly capture-avoiding substitution, not only semantically equal. -/
def QuantifierFree : Form → Prop
  | .bottom | .equal _ _ => True
  | .imp a b => QuantifierFree a ∧ QuantifierFree b
  | .all _ _ => False

/-- Uniform replacement is used only after a quantifier-free check; the
arbitrary-binder construction below uses freshening instead. -/
def replaceForm (x y : Nat) : Form → Form
  | .bottom => .bottom
  | .equal a b => .equal (CompactNamed.rename x y a) (CompactNamed.rename x y b)
  | .imp a b => .imp (replaceForm x y a) (replaceForm x y b)
  | .all z a => .all z (replaceForm x y a)

theorem pa_replace_quantifier_free (a : Form) (x y : Nat) (h : QuantifierFree a) :
    paFormula (replaceForm x y a) = FOL.substAt (paFormula a) x (.var y) := by
  induction a with
  | bottom => rfl
  | equal a b =>
    simp only [paFormula, replaceForm, CompactNamed.rename, FOL.substAt, FOL.equality_subst, FirstOrder.Language.Term.subst]
    split_ifs <;> rfl
  | imp a b ia ib =>
    change (paFormula (replaceForm x y a)).imp (paFormula (replaceForm x y b)) =
      (FOL.substAt (paFormula a) x (.var y)).imp (FOL.substAt (paFormula b) x (.var y))
    rw [ia h.1, ib h.2]
  | all z a ih => exact False.elim h

theorem named_replace (a : Form) (x y : Nat) :
    named (replaceForm x y a) = replace x y (named a) := by
  induction a <;> simp_all [named, replaceForm, replace]

theorem quantifier_free_binders (a : Form) (h : QuantifierFree a) :
    (named a).binders = ∅ := by
  induction a with
  | bottom | equal => rfl
  | imp a b ia ib => simp [named, CompactNamed.Formula.binders, ia h.1, ib h.2]
  | all _ _ _ => exact False.elim h

/-- Literal identity replacement, including under arbitrarily nested binders. -/
theorem replace_self (x : Nat) (f : CompactNamed.Formula) : replace x x f = f := by
  induction f <;> simp_all [replace, rename]

/-- On quantifier-free formulas, K proves the exact syntactic variable instance
without any alpha-freshened target. -/
def quantifier_free_instance (a : Form) (x y : Nat) (h : QuantifierFree a) :
    KDerivation (imp (allCode x (compactCode a)) (compactCode (replaceForm x y a))) := by
  have hbind := quantifier_free_binders a h
  have hx : x ∉ (named a).binders := by rw [hbind]; simp
  have hy : y ∉ (named a).binders := by rw [hbind]; simp
  have henc : compactCode (replaceForm x y a) = (replace x y (named a)).encode := by
    rw [← named_replace, named_encode]
  rw [henc, ← named_encode a]
  by_cases he : x = y
  · subst y
    rw [replace_self]
    exact allSpecialize x (named a) hx
  · exact universalInstance x y (named a) he hx hy

/-- Freshening plus replacement builds an actual K universal-instantiation
proof, together with a capture-safe semantics theorem. The result formula may
use new bound names. This applies even with repeated or shadowed binders. -/
structure SafeInstance (x y : Nat) (f : CompactNamed.Formula) where
  result : CompactNamed.Formula
  proof : KDerivation (imp (allCode x f.encode) result.encode)
  semantic : ∀ ρ : Nat → Nat, result.Realize ρ ↔ f.Realize (CompactMatrix.update ρ x (ρ y))
  binders_fresh : x ∉ result.binders ∧ y ∉ result.binders

noncomputable def safeInstance (x y : Nat) (f : CompactNamed.Formula) : SafeInstance x y f := by
  let start := f.names.sup id + x + y + 1
  have hnames : ∀ v ∈ f.names, v < start := by
    intro v hv
    have hl : v ≤ f.names.sup id := Finset.le_sup (f := id) hv
    dsimp [start]
    omega
  let h := freshen f start hnames
  have hx : x ∉ h.formula.binders := by
    intro hm
    have ht := h.binders_ge x hm
    dsimp [start] at ht
    omega
  have hy : y ∉ h.formula.binders := by
    intro hm
    have ht := h.binders_ge y hm
    dsimp [start] at ht
    omega
  refine ⟨replace x y h.formula, ?_, ?_, ?_⟩
  · have hquant := allCongr x h.equivalent.forward
    by_cases hxy : x = y
    · subst y
      rw [replace_self]
      exact compose hquant (CompactNamed.allSpecialize x h.formula hx)
    · exact compose hquant (universalInstance x y h.formula hxy hx hy)
  · intro ρ
    exact (replace_realize x y h.formula hx hy ρ).trans
      (h.equivalent.semantic (CompactMatrix.update ρ x (ρ y))).symm
  · simpa [replace_binders] using And.intro hx hy

/-- The compact target has exactly the truth of PA's capture-avoiding
substitution by a variable, for all natural-number assignments. The proof
translation itself is syntactic and does not use this theorem. -/
theorem safeInstance_matches_PA (a : Form) (x y : Nat) (ρ : Nat → Nat) :
    (safeInstance x y (named a)).result.Realize ρ ↔
      (FOL.substAt (paFormula a) x (.var y)).Realize ρ := by
  rw [(safeInstance x y (named a)).semantic]
  rw [named_realize]
  rw [FOL.realize_substAt]
  have he : CompactMatrix.update ρ x (ρ y) = Function.update ρ x (ρ y) := by
    funext z
    by_cases h : z = x <;> simp [CompactMatrix.update, h]
  rw [he]
  rfl

/-- The instantiated K implication and the genuine PA variable-elimination
axiom agree on every assignment, including formulas with shadowed binders. -/
theorem instance_axiom_truth_matches (a : Form) (x y : Nat) (ρ : Nat → Nat) :
    ((FOL.allAt x (paFormula a)).imp (FOL.substAt (paFormula a) x (.var y))).Realize ρ ↔
      (CompactMatrix.decode (imp (allCode x (compactCode a))
        (safeInstance x y (named a)).result.encode)).Realize ρ := by
  simp only [FirstOrder.Language.Formula.realize_imp, CompactSemantics.realize_imp]
  apply imp_congr
  · rw [FOL.realize_allAt, CompactSemantics.realize_all]
    apply forall_congr'
    intro v
    have he : Function.update ρ x v = CompactMatrix.update ρ x v := by
      funext z
      by_cases h : z = x <;> simp [CompactMatrix.update, h]
    rw [he]
    exact truth_preserved a _
  · rw [CompactNamed.Formula.encode_realize]
    exact (safeInstance_matches_PA a x y ρ).symm

/-- The corresponding variable-instance axiom is a genuine PA logical axiom. -/
theorem pa_variable_instance (a : Form) (x y : Nat) :
    Peano.FormulaProves ((FOL.allAt x (paFormula a)).imp
      (FOL.substAt (paFormula a) x (.var y))) :=
  FOL.Derivation.logical (.allElim (paFormula a) x (.var y))

/-- The constructed universal instance has an executable K certificate. -/
theorem instance_certificate (a : Form) (x y : Nat) :
    CompactProof.theoremCode (CompactProof.certificate (safeInstance x y (named a)).proof) =
      CompactProof.imp (CompactProof.allCode x (compactCode a))
        (safeInstance x y (named a)).result.encode := by
  simpa using CompactProof.certificate_correct (safeInstance x y (named a)).proof

end PASoundness.PAtoCompactVariableInstance
