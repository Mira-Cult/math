import PASoundness.PAtoCompactKuratowskiSyntax
import PASoundness.CompactNamed

/-! Capture-safe syntactic renaming for the explicit Kuratowski formula.
No graph existence or quotient property is established here. -/
set_option maxRecDepth 65536
namespace PASoundness.PAtoCompactKuratowskiRename
open PASoundness.CompactNamed PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactKuratowskiSyntax PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSingleton PASoundness.PAtoCompactUnorderedPair

/-- Replacing a name distinct from all internal binders acts on the three
parameters of the relational pair formula. -/
theorem replace_pair (x y p a b : Nat) (h20 : x ≠ 20) (h21 : x ≠ 21) (h22 : x ≠ 22) :
    replace x y (pairFormula p a b) =
      pairFormula (rename x y p) (rename x y a) (rename x y b) := by
  simp [pair_formula_named, namedSingleton, namedPair, namedBoth, namedEither,
    replace, rename, Ne.symm h20, Ne.symm h21, Ne.symm h22]

end PASoundness.PAtoCompactKuratowskiRename

#print axioms PASoundness.PAtoCompactKuratowskiRename.replace_pair
