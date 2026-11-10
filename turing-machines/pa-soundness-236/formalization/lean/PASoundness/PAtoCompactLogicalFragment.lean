import PASoundness.Peano
import PASoundness.CompactDerivations
import PASoundness.CompactSemantics

/-! A syntax-directed common logical fragment of PA and K. It does not
translate arithmetic terms, arithmetic axioms, induction, or full PA proofs. -/
namespace PASoundness.PAtoCompactLogicalFragment
open FirstOrder FirstOrder.Language
open PASoundness.CompactProof

/-- Named first-order equality, bottom, implication, and universal quantifiers.
This fragment contains no arithmetic function symbols. -/
inductive Form where
  | bottom
  | equal (x y : Nat)
  | imp (a b : Form)
  | all (x : Nat) (a : Form)

def paFormula : Form → Peano.Formula
  | .bottom => ⊥
  | .equal x y => (FirstOrder.Language.Term.var x : Peano.Term).equal (.var y)
  | .imp a b => (paFormula a).imp (paFormula b)
  | .all x a => FOL.allAt x (paFormula a)

def compactCode : Form → Nat
  | .bottom => 1
  | .equal x y => CompactProof.equal x y
  | .imp a b => CompactProof.imp (compactCode a) (compactCode b)
  | .all x a => CompactProof.allCode x (compactCode a)

/-- A finite syntactic derivation fragment of the actual PA Hilbert calculus.
The constructors list exactly the instances treated by this translation. -/
inductive Derivation : Form → Type where
  | k (a b : Form) : Derivation (.imp a (.imp b a))
  | s (a b c : Form) : Derivation (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | classical (a : Form) : Derivation (.imp (.imp (.imp a .bottom) .bottom) a)
  | equalRefl (x : Nat) : Derivation (.equal x x)
  | allImp (x : Nat) (a b : Form) :
      Derivation (.imp (.all x (.imp a b)) (.imp (.all x a) (.all x b)))
  | mp {a b : Form} : Derivation (.imp a b) → Derivation a → Derivation b
  | generalize {a : Form} (x : Nat) : Derivation a → Derivation (.all x a)

/-- Every displayed derivation is an actual syntactic PA derivation. -/
theorem toPA : {a : Form} → Derivation a → Peano.FormulaProves (paFormula a)
  | _, .k a b => FOL.Derivation.logical (.k (paFormula a) (paFormula b))
  | _, .s a b c => FOL.Derivation.logical (.s (paFormula a) (paFormula b) (paFormula c))
  | _, .classical a => FOL.Derivation.logical (.classical (paFormula a))
  | _, .equalRefl x => FOL.Derivation.logical (.eqRefl (.var x))
  | _, .allImp x a b => FOL.Derivation.logical (.allImp (paFormula a) (paFormula b) x)
  | _, .mp h p => FOL.Derivation.mp (toPA h) (toPA p)
  | _, .generalize x p => FOL.Derivation.generalize x (toPA p)

/-- The same finite derivation gives explicit K proof data, using the checked
constructive K Hilbert basis and derived rules. -/
def toCompact : {a : Form} → Derivation a → KDerivation (compactCode a)
  | _, .k a b => CompactHilbertBasis.weakening (compactCode a) (compactCode b)
  | _, .s a b c => CompactHilbertBasis.distribution (compactCode a) (compactCode b) (compactCode c)
  | _, .classical a => CompactDerivations.doubleNegElim (compactCode a)
  | _, .equalRefl x => CompactDerivations.equalityReflexive x
  | _, .allImp x a b => CompactDerivations.allDistribution x (compactCode a) (compactCode b)
  | _, .mp h p => KDerivation.mp (toCompact p) (toCompact h)
  | _, .generalize x p => KDerivation.generalize x (toCompact p)

/-- On the shared natural-number assignment domain, the fragment's PA formula
and decoded K formula have the same truth value. This is a separate semantic
fact; the proof translator above is entirely syntactic. -/
theorem truth_preserved (a : Form) (ρ : Nat → Nat) :
    (paFormula a).Realize ρ ↔ (CompactMatrix.decode (compactCode a)).Realize ρ := by
  induction a generalizing ρ with
  | bottom => simp [paFormula, compactCode]
  | equal x y => simp [paFormula, compactCode]
  | imp a b ia ib =>
    simp only [paFormula, compactCode, FirstOrder.Language.Formula.realize_imp,
      CompactSemantics.realize_imp]
    exact imp_congr (ia ρ) (ib ρ)
  | all x a ih =>
    simp only [paFormula, compactCode, FOL.realize_allAt, CompactSemantics.realize_all]
    apply forall_congr'
    intro v
    have hupdate : Function.update ρ x v = CompactMatrix.update ρ x v := by
      funext y
      by_cases h : y = x <;> simp [CompactMatrix.update, h]
    rw [← hupdate]
    exact ih _

/-- The target proof is executable by the exact K certificate producer. -/
theorem translated_certificate {a : Form} (d : Derivation a) :
    CompactProof.theoremCode (CompactProof.certificate (toCompact d)) = compactCode a :=
  CompactProof.certificate_correct (toCompact d)

end PASoundness.PAtoCompactLogicalFragment
