import PASoundness.PAtoCompactFilteredSubset
import PASoundness.PAtoCompactZeroSuccessor

/-! Capture-safe instantiation of a represented K filter at a named element.
This is a finite proof transformation, not a semantic soundness argument. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFilterInstantiation
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactFilteredSubset

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Named body of the literal filter membership equivalence. -/
def namedFilterBody (x y t : Nat) (P : CompactNamed.Formula) : CompactNamed.Formula :=
  let Q := namedBoth (.member x t) P
  namedBoth (.imp (.member y t) Q) (.imp Q (.member y t))

/-- Instantiate the filter at `v`; the two names must not bind inside the
supplied predicate, and the test name must differ from both set names.
The resulting predicate is the literal capture-safe named replacement, not
an assumption that an arbitrary code admits unrestricted substitution. -/
def filter_at (x y t v : Nat) (P : CompactNamed.Formula)
    (htx : t ≠ x) (hty : t ≠ y) (htv : t ≠ v)
    (ht : t ∉ P.binders) (hv : v ∉ P.binders) :
    KDerivation (imp (filterGraph x y t P.encode)
      (both (imp (member y v) (both (member x v) (CompactNamed.replace t v P).encode))
        (imp (both (member x v) (CompactNamed.replace t v P).encode) (member y v)))) := by
  let body := namedFilterBody x y t P
  have ht' : t ∉ body.binders := by simpa [body, namedFilterBody, namedBoth, CompactNamed.Formula.binders] using ht
  have hv' : v ∉ body.binders := by simpa [body, namedFilterBody, namedBoth, CompactNamed.Formula.binders] using hv
  have hi := CompactNamed.universalInstance t v body htv ht' hv'
  simpa [body, namedFilterBody, namedBoth, CompactNamed.Formula.encode,
    CompactNamed.replace, CompactNamed.rename, filterGraph, filterPredicate,
    CompactProof.both, CompactProof.neg, htx, hty, htv, Ne.symm htx, Ne.symm hty] using hi

theorem filter_at_certificate (x y t v : Nat) (P : CompactNamed.Formula)
    (htx : t ≠ x) (hty : t ≠ y) (htv : t ≠ v)
    (ht : t ∉ P.binders) (hv : v ∉ P.binders) :
    theoremCode (certificate (filter_at x y t v P htx hty htv ht hv)) =
      imp (filterGraph x y t P.encode)
        (both (imp (member y v) (both (member x v) (CompactNamed.replace t v P).encode))
          (imp (both (member x v) (CompactNamed.replace t v P).encode) (member y v))) :=
  certificate_correct (filter_at x y t v P htx hty htv ht hv)

end PASoundness.PAtoCompactFilterInstantiation

#print axioms PASoundness.PAtoCompactFilterInstantiation.filter_at
#print axioms PASoundness.PAtoCompactFilterInstantiation.filter_at_certificate
