import PASoundness.PAtoCompactPartialInversePairAlias

/-! Reorient the two endpoint equalities for the inverse-prefix consumer.
This is a K proof adapter, not an inverse graph or quotient construction. -/
namespace PASoundness.PAtoCompactPartialInversePairAliasSymm
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactPartialInversePairAlias

/-- The reversed new-edge case in the consumer's equality orientation. -/
def reversed_new_edge_symm : KDerivation (imp (equal 19 11)
    (imp (pairFormula 19 3 2).encode (imp (pairFormula 11 13 12).encode
      (both (equal 3 13) (equal 2 12))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 11 13 12).encode,(pairFormula 19 3 2).encode,equal 19 11]
  have he : Context Γ (equal 19 11) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 3 2).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (pairFormula 11 13 12).encode := .hypothesis (by simp [Γ])
  have hs : Context Γ (both (equal 13 3) (equal 12 2)) :=
    .mp hb (.mp ha (.mp he (.closed reversed_new_edge)))
  exact Context.conjunctionIntro (Context.eqSymm (Context.conjunctionLeft hs))
    (Context.eqSymm (Context.conjunctionRight hs))

theorem reversed_new_edge_symm_certificate : theoremCode (certificate reversed_new_edge_symm) =
    imp (equal 19 11) (imp (pairFormula 19 3 2).encode (imp (pairFormula 11 13 12).encode
      (both (equal 3 13) (equal 2 12)))) := certificate_correct reversed_new_edge_symm

end PASoundness.PAtoCompactPartialInversePairAliasSymm

#print axioms PASoundness.PAtoCompactPartialInversePairAliasSymm.reversed_new_edge_symm
#print axioms PASoundness.PAtoCompactPartialInversePairAliasSymm.reversed_new_edge_symm_certificate
