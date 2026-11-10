import PASoundness.PAtoCompactRestrictionEdgeEquivalence
import PASoundness.PAtoCompactTransitiveClosure
import PASoundness.PAtoCompactOldImageContainedAligned

/-! Pointwise transfer into a supplied endpoint restriction. All graph,
successor and order assumptions are explicit; no witness totality or
quotient law is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedBackwardPoint
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactGraphRestriction PASoundness.PAtoCompactRestrictionEdgeEquivalence
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def sourceSuccessor : Nat := successorCode 2 0 9
def targetSuccessor : Nat := successorCode 5 1 10
def restriction : Nat := filterGraph 6 8 14 (edgePredicate 14 2 5).encode
def oldEdge : Nat := (graphFormula 6 7 3).encode
def restrictedEdge : Nat := (graphFormula 8 7 3).encode
def topEdge : Nat := (graphFormula 6 2 5).encode

/-- The old-source containment derivation is an explicit proof-data premise.
Given that derivation, this produces K proof data that an original edge from
a supplied source member to an old target member is retained by the endpoint
filter. Fixed numeric names are pairwise fresh for the filter binders; their
denoted objects may coincide. Code 1 is literal `member 0 0`. -/
def backward_point_of_containment
    (contain : KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp (member 0 7) (imp (member 5 3)
        (imp oldEdge (imp topEdge (member 2 7))))))))) :
    KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp restriction (imp topEdge
        (imp (member 0 7) (imp (member 5 3)
          (imp oldEdge (both (member 2 7) restrictedEdge))))))))) := by
  let SX := sourceSuccessor
  let SY := targetSuccessor
  let O := orderFormula.encode
  let F := restriction
  let T := topEdge
  let U := member 0 7
  let V := member 5 3
  let E := oldEdge
  let P := member 2 7
  let H := restrictedEdge
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [E,V,U,T,F,O,SY,SX]
  have hsx : Context Γ SX := .hypothesis (by simp [Γ])
  have hsy : Context Γ SY := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hf : Context Γ F := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have he : Context Γ E := .head _ _
  have hp : Context Γ P := .mp ht (.mp he (.mp hv (.mp hu (.mp ho
    (.mp hsy (.mp hsx (.closed contain)))))))
  have hequiv : Context Γ (both (imp E H) (imp H E)) := by
    have h := restricted_edge_iff 6 8 14 2 5 7 3 (by decide)
    exact .mp hv (.mp hp (.mp hf (.closed h)))
  have hh : Context Γ H := .mp he (Context.conjunctionLeft hequiv)
  exact Context.conjunctionIntro hp hh

/-- Construct the containment interface from a supplied guarded equivalence
between old-source and old-target membership. The target-successor graph
provides the missing target-domain guard. -/
def containment_of_guarded_order
    (guarded : KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp (member 0 7) (imp (member 1 3)
        (imp oldEdge (imp topEdge
          (both (imp (member 2 7) (member 5 3))
            (imp (member 5 3) (member 2 7))))))))))) :
    KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp (member 0 7) (imp (member 5 3)
        (imp oldEdge (imp topEdge (member 2 7)))))))) := by
  let SX := sourceSuccessor
  let SY := targetSuccessor
  let O := orderFormula.encode
  let U := member 0 7
  let V := member 5 3
  let E := oldEdge
  let T := topEdge
  let J := member 1 3
  let P := member 2 7
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [T,E,V,U,O,SY,SX]
  have hsx : Context Γ SX := .hypothesis (by simp [Γ])
  have hsy : Context Γ SY := .hypothesis (by simp [Γ])
  have ho : Context Γ O := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .head _ _
  have hj : Context Γ J := .mp (Context.disjunctionRight hv)
    (.mp hsy (.closed (successor_include 5 1 10 3 (by decide) (by decide) (by decide))))
  have hiff : Context Γ (both (imp P V) (imp V P)) :=
    .mp ht (.mp he (.mp hj (.mp hu (.mp ho (.mp hsy (.mp hsx (.closed guarded)))))))
  exact .mp hv (Context.conjunctionRight hiff)

/-- The pointwise restricted-edge conclusion conditional on the exact
guarded order-equivalence proof data. -/
def backward_point_of_guarded_order
    (guarded : KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp (member 0 7) (imp (member 1 3)
        (imp oldEdge (imp topEdge
          (both (imp (member 2 7) (member 5 3))
            (imp (member 5 3) (member 2 7))))))))))) :
    KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp restriction (imp topEdge
        (imp (member 0 7) (imp (member 5 3)
          (imp oldEdge (both (member 2 7) restrictedEdge))))))))) :=
  backward_point_of_containment (containment_of_guarded_order guarded)

/-- For the literal two successor graphs and order clause, an original
edge from a source-domain point to an old target member has an old-source
endpoint and is retained by the supplied endpoint restriction. This is a
pointwise implication only: the edge and filtered graph are not constructed
by this theorem. -/
def backward_point : KDerivation (imp sourceSuccessor (imp targetSuccessor
    (imp orderFormula.encode (imp restriction (imp topEdge
      (imp (member 0 7) (imp (member 5 3)
        (imp oldEdge (both (member 2 7) restrictedEdge))))))))) :=
  backward_point_of_guarded_order
    PAtoCompactOldImageContainedAligned.old_image_preimage_iff

theorem backward_point_certificate : theoremCode (certificate backward_point) =
    imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp restriction (imp topEdge
        (imp (member 0 7) (imp (member 5 3)
          (imp oldEdge (both (member 2 7) restrictedEdge)))))))) :=
  certificate_correct backward_point

theorem backward_point_of_containment_certificate
    (contain : KDerivation (imp sourceSuccessor (imp targetSuccessor
      (imp orderFormula.encode (imp (member 0 7) (imp (member 5 3)
        (imp oldEdge (imp topEdge (member 2 7))))))))) :
    theoremCode (certificate (backward_point_of_containment contain)) =
      imp sourceSuccessor (imp targetSuccessor
        (imp orderFormula.encode (imp restriction (imp topEdge
          (imp (member 0 7) (imp (member 5 3)
            (imp oldEdge (both (member 2 7) restrictedEdge)))))))) :=
  certificate_correct (backward_point_of_containment contain)

end PASoundness.PAtoCompactRestrictedBackwardPoint

#print axioms PASoundness.PAtoCompactRestrictedBackwardPoint.backward_point_of_containment
#print axioms PASoundness.PAtoCompactRestrictedBackwardPoint.backward_point_of_containment_certificate
#print axioms PASoundness.PAtoCompactRestrictedBackwardPoint.backward_point
#print axioms PASoundness.PAtoCompactRestrictedBackwardPoint.backward_point_certificate
