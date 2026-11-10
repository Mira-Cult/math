import PASoundness.PAtoCompactGuardedPropositional
import PASoundness.FOLFreshEquality

/-! A genuinely changing PA equality-substitution leaf reduces to symmetry
of the translated equality. The required symmetry is explicit finite K proof
data, not an appeal to PA or K soundness. -/
namespace PASoundness.PAtoCompactEqSubstSymmetryLeaf

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedPropositional

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- If x is fresh for a, substitution into x=a changes only its left side. -/
theorem subst_left_atom (x : Nat) (a t : Peano.Term) (hx : x ∉ a.varFinset) :
    FOL.substAt ((.var x : Peano.Term).equal a) x t = t.equal a := by
  simp only [FOL.substAt, FOL.equality_subst, Term.subst, ↓reduceIte,
    PASoundness.FOL.term_subst_fresh a x t hx]

/-- For a fresh x, a K proof that the translated equality t=u implies u=t
supplies the equality-substitution leaf whose formula is x=t. This handles
arbitrary t and u; translated equality symmetry remains an explicit premise. -/
def leaf_of_symmetry (x : Nat) (t u : Peano.Term) (hx : x ∉ t.varFinset)
    (hsym : KDerivation (imp (code (t.equal u)) (code (u.equal t)))) :
    KDerivation (guardedCode ((t.equal u).imp
      ((FOL.substAt ((.var x : Peano.Term).equal t) x t).imp
        (FOL.substAt ((.var x : Peano.Term).equal t) x u)))) := by
  rw [subst_left_atom x t t hx, subst_left_atom x t u hx]
  apply guardedOfUnconditional
  simp only [code_imp]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [code (t.equal t), code (t.equal u)]
  have htu : Context Γ (code (t.equal u)) := .hypothesis (List.Mem.tail _ (List.Mem.head _))
  exact .mp htu (.closed hsym)

theorem leaf_of_symmetry_certificate (x : Nat) (t u : Peano.Term) (hx : x ∉ t.varFinset)
    (hsym : KDerivation (imp (code (t.equal u)) (code (u.equal t)))) :
    theoremCode (certificate (leaf_of_symmetry x t u hx hsym)) =
      guardedCode ((t.equal u).imp
        ((FOL.substAt ((.var x : Peano.Term).equal t) x t).imp
          (FOL.substAt ((.var x : Peano.Term).equal t) x u))) := certificate_correct _

#print axioms subst_left_atom
#print axioms leaf_of_symmetry
#print axioms leaf_of_symmetry_certificate
end PASoundness.PAtoCompactEqSubstSymmetryLeaf
