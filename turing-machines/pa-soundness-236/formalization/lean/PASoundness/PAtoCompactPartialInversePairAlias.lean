import PASoundness.PAtoCompactKuratowskiInjectivity

/-! K equality transport and pair-coordinate injectivity for a fresh edge
witness and the designated new pair object in the inverse-prefix argument.
These fixed-name interfaces do not construct an inverse graph or quotient. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInversePairAlias
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactKuratowskiInjectivity

/-- If an alleged reversed edge object is the designated new object, its
coordinates agree with the designated pair. Names 19 and 11 do not collide
with the pair formula's bound names 20–22. -/
def reversed_new_edge : KDerivation (imp (equal 19 11)
    (imp (pairFormula 19 3 2).encode (imp (pairFormula 11 13 12).encode
      (both (equal 13 3) (equal 12 2))))) := by
  have hrepl : CompactNamed.replace 19 11 (pairFormula 19 3 2) = pairFormula 11 3 2 := by decide
  have ht := (CompactNamed.equalityReplace 19 11 (pairFormula 19 3 2)
    (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 11 13 12).encode,(pairFormula 19 3 2).encode,equal 19 11]
  have he : Context Γ (equal 19 11) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 3 2).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (pairFormula 11 13 12).encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (pairFormula 11 3 2).encode := .mp ha (.mp he (.closed ht))
  exact .mp ha' (.mp hb (.closed (pair_coordinates 11 13 12 3 2 (by decide))))

theorem reversed_new_edge_certificate : theoremCode (certificate reversed_new_edge) =
    imp (equal 19 11) (imp (pairFormula 19 3 2).encode (imp (pairFormula 11 13 12).encode
      (both (equal 13 3) (equal 12 2)))) := certificate_correct reversed_new_edge

/-- The alternative endpoint ordering, useful when the alleged pair uses
names 2,3 rather than 3,2. -/
def ordered_new_edge : KDerivation (imp (equal 19 11)
    (imp (pairFormula 19 2 3).encode (imp (pairFormula 11 13 12).encode
      (both (equal 2 13) (equal 3 12))))) := by
  have hrepl : CompactNamed.replace 19 11 (pairFormula 19 2 3) = pairFormula 11 2 3 := by decide
  have ht := (CompactNamed.equalityReplace 19 11 (pairFormula 19 2 3)
    (by decide) (by decide)).1
  rw [hrepl] at ht
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [(pairFormula 11 13 12).encode,(pairFormula 19 2 3).encode,equal 19 11]
  have he : Context Γ (equal 19 11) := .hypothesis (by simp [Γ])
  have ha : Context Γ (pairFormula 19 2 3).encode := .hypothesis (by simp [Γ])
  have hb : Context Γ (pairFormula 11 13 12).encode := .hypothesis (by simp [Γ])
  have ha' : Context Γ (pairFormula 11 2 3).encode := .mp ha (.mp he (.closed ht))
  have hs : Context Γ (both (equal 13 2) (equal 12 3)) :=
    .mp ha' (.mp hb (.closed (pair_coordinates 11 13 12 2 3 (by decide))))
  exact Context.conjunctionIntro (Context.eqSymm (Context.conjunctionLeft hs))
    (Context.eqSymm (Context.conjunctionRight hs))

theorem ordered_new_edge_certificate : theoremCode (certificate ordered_new_edge) =
    imp (equal 19 11) (imp (pairFormula 19 2 3).encode (imp (pairFormula 11 13 12).encode
      (both (equal 2 13) (equal 3 12)))) := certificate_correct ordered_new_edge

end PASoundness.PAtoCompactPartialInversePairAlias

#print axioms PASoundness.PAtoCompactPartialInversePairAlias.reversed_new_edge
#print axioms PASoundness.PAtoCompactPartialInversePairAlias.reversed_new_edge_certificate
#print axioms PASoundness.PAtoCompactPartialInversePairAlias.ordered_new_edge
#print axioms PASoundness.PAtoCompactPartialInversePairAlias.ordered_new_edge_certificate
