import PASoundness.PAtoCompactPartialInverseAdjoinInspect
import PASoundness.PAtoCompactPartialInverseOldGraph
import PASoundness.PAtoCompactPartialInverseVacuitySymm
import PASoundness.PAtoCompactGraphContextElim

/-! An adjoined graph has no spurious selected edge, conditional on supplied
adjunction, appended pair and finite pair-alias derivation. The explicit K
proof argument can be instantiated by PartialInversePairAliasSymm; it is not
an axiom. No inverse graph existence or induction is claimed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseNoSpurious
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactPartialInverseAdjoinInspect
open PASoundness.PAtoCompactPartialInversePointCase PASoundness.PAtoCompactPartialInverseOldGraph
open PASoundness.PAtoCompactPartialInverseVacuitySymm PASoundness.PAtoCompactGraphContextElim
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private def adjunction_vacuity : KDerivation
    (imp (adjoinCode 7 11 9 14) (allCode 19 (adjoinCode 7 11 9 14))) := by
  let f := namedAdjoin 7 11 9 14
  have hv := f.vacuity 19 (by decide)
  simpa [f, namedAdjoin, namedBoth, namedEither, Formula.encode, adjoinCode,
    CompactProof.both, CompactProof.neg, CompactDerivations.either] using hv

private def pair_vacuity : KDerivation
    (imp (pairFormula 11 13 12).encode (allCode 19 (pairFormula 11 13 12).encode)) :=
  (pairFormula 11 13 12).vacuity 19 (by decide)

/-- Every selected edge of h′=h∪{p} was in h or has the appended pair's
coordinates. The required pair-alias derivation is an explicit proof-data
argument; graph and pair assumptions remain object-level antecedents. -/
def no_spurious_edge (hAlias : KDerivation pairAliasCode) : KDerivation
    (imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
      (imp (graphFormula 9 3 2).encode conclusion.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let A := adjoinCode 7 11 9 14
  let Q := (pairFormula 11 13 12).encode
  let P := (pairFormula 19 3 2).encode
  let B := both (member 9 19) P
  let Γ := [Q,A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hq : Context Γ Q := Context.head _ _
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 19 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = Q
    · subst h
      exact pair_vacuity
    · have he' : h = A := hh.resolve_left he
      subst h
      exact adjunction_vacuity
  have hs : Context Γ (imp B conclusion.encode) := by
    apply Context.deduction
    have hb : Context (B :: Γ) B := Context.head _ _
    have hm : Context (B :: Γ) (member 9 19) := Context.conjunctionLeft hb
    have hp : Context (B :: Γ) P := Context.conjunctionRight hb
    have ha' : Context (B :: Γ) A := Context.under ha _
    have hq' : Context (B :: Γ) Q := Context.under hq _
    have hc : Context (B :: Γ)
        (imp (member 9 19) (either (member 7 19) (equal 19 11))) :=
      .mp ha' (.closed adjoin_forward_instance)
    exact .mp hq' (.mp hp (.mp hm (.mp hc (.closed (no_spurious_old_graph hAlias)))))
  exact graph_context_imp Γ 9 3 2 conclusion hv conclusion_vacuity hs

theorem no_spurious_edge_certificate (hAlias : KDerivation pairAliasCode) :
    theoremCode (certificate (no_spurious_edge hAlias)) =
      imp (adjoinCode 7 11 9 14) (imp (pairFormula 11 13 12).encode
        (imp (graphFormula 9 3 2).encode conclusion.encode)) :=
  certificate_correct (no_spurious_edge hAlias)

end PASoundness.PAtoCompactPartialInverseNoSpurious

#print axioms PASoundness.PAtoCompactPartialInverseNoSpurious.no_spurious_edge
#print axioms PASoundness.PAtoCompactPartialInverseNoSpurious.no_spurious_edge_certificate
