import PASoundness.CompactLogicalTransport
import PASoundness.PeanoBetaCRTPrefixSubst

/-! Syntactic freshness for the literal AX8 formula-code parameter.

This records the arithmetic translation's free variables, not semantic truth
or a proof of the comprehension axiom. -/
namespace PASoundness.PeanoAX8DecodedFresh
open FirstOrder FirstOrder.Language
open Peano CompactLogicalTransport

/-- The variable named by a formula code is absent from that code's exact
arithmetic interpretation. -/
theorem interpreted_self_fresh (c : Nat) :
    c ∉ (interpreted c).freeVarFinset := by
  change c ∉ (CompactArithmetic.translate (CompactMatrix.decode c)).freeVarFinset
  rw [CompactArithmetic.translate_freeVars]
  exact CompactSemantics.decode_self_free_fresh c

/-- An output witness substituted at the formula-code name leaves the decoded
arithmetic predicate unchanged, even for an arbitrary witness term. -/
theorem interpreted_subst_self (c : Nat) (t : Peano.Term) :
    FOL.substAt (interpreted c) c t = interpreted c :=
  PeanoBetaCRTPrefixSubst.Syntax.substAt_of_fresh _ _ _ (interpreted_self_fresh c)

end PASoundness.PeanoAX8DecodedFresh

#print axioms PASoundness.PeanoAX8DecodedFresh.interpreted_self_fresh
#print axioms PASoundness.PeanoAX8DecodedFresh.interpreted_subst_self
