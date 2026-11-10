import PASoundness.PAtoCompactEqSubstSymmetryLeaf
import PASoundness.PAtoCompactEqualityFrameSymmetry

/-! A genuine, generally changing PA equality-substitution leaf. The proof
uses finite K equality symmetry and no semantic soundness theorem. -/
namespace PASoundness.PAtoCompactEqSubstSymmetryFullLeaf

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactEqSubstSymmetryLeaf PASoundness.PAtoCompactEqualityFrameSymmetry

/-- For arbitrary PA terms t,u and a name x absent from t, the full guarded
PA equality-substitution leaf for source formula x=t is derivable in K.
The two substitution results t=t and u=t need not coincide. -/
noncomputable def symmetry_leaf (x : Nat) (t u : Peano.Term) (hx : x ∉ t.varFinset) :
    KDerivation (guardedCode ((t.equal u).imp
      ((FOL.substAt ((.var x : Peano.Term).equal t) x t).imp
        (FOL.substAt ((.var x : Peano.Term).equal t) x u)))) :=
  leaf_of_symmetry x t u hx (code_symmetry t u)

theorem symmetry_leaf_certificate (x : Nat) (t u : Peano.Term) (hx : x ∉ t.varFinset) :
    theoremCode (certificate (symmetry_leaf x t u hx)) =
      guardedCode ((t.equal u).imp
        ((FOL.substAt ((.var x : Peano.Term).equal t) x t).imp
          (FOL.substAt ((.var x : Peano.Term).equal t) x u))) := certificate_correct _

#print axioms symmetry_leaf
#print axioms symmetry_leaf_certificate
end PASoundness.PAtoCompactEqSubstSymmetryFullLeaf
