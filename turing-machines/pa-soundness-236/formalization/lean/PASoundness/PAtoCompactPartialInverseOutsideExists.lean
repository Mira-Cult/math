import PASoundness.PAtoCompactPartialInverseOutside
import PASoundness.PAtoCompactTransitiveWitness

/-! Existential lifting of the outside-source successor case. The same graph
witness is retained; this module proves no inside-source step or induction. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialInverseOutsideExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactPartialInverseBase PASoundness.PAtoCompactPartialInverseOutside
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Reorder the already-derived outside step for uniform graph lifting. -/
def reordered_outside_step : KDerivation
    (imp (successorCode 8 10 15) (imp (neg (member 0 8))
      (imp partialInverse.encode nextPartialInverse.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 8 10 15
  let N := neg (member 0 8)
  let P := partialInverse.encode
  let Γ := [P,N,S]
  have hp : Context Γ P := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  exact .mp hn (.mp hs (.mp hp (.closed outside_successor)))

/-- A graph witnessing the old prefix remains a graph witnessing the next
prefix when that endpoint lies outside the full source. -/
def outside_successor_exists : KDerivation
    (imp (successorCode 8 10 15) (imp (neg (member 0 8))
      (imp (existsCode 7 partialInverse.encode)
        (existsCode 7 nextPartialInverse.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 8 10 15
  let N := neg (member 0 8)
  let P := partialInverse.encode
  let Q := nextPartialInverse.encode
  let Γ := [existsCode 7 P,N,S]
  have he : Context Γ (existsCode 7 P) := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hS : Context Γ (allCode 7 S) := .mp hs
    (.closed (successor_vacuity 8 10 15 7 (by decide) (by decide) (by decide)))
  have hN : Context Γ (allCode 7 N) := .mp hn
    (.closed (negationVacuity 7 (membershipVacuity 0 8 7 (by decide) (by decide))))
  have hall : Context Γ (allCode 7 (imp P Q)) :=
    Context.allMP hN (Context.allMP hS (.closed (.generalize 7 reordered_outside_step)))
  exact exists_map_context hall he

theorem outside_successor_exists_certificate :
    theoremCode (certificate outside_successor_exists) =
      imp (successorCode 8 10 15) (imp (neg (member 0 8))
        (imp (existsCode 7 partialInverse.encode)
          (existsCode 7 nextPartialInverse.encode))) :=
  certificate_correct outside_successor_exists

end PASoundness.PAtoCompactPartialInverseOutsideExists

#print axioms PASoundness.PAtoCompactPartialInverseOutsideExists.outside_successor_exists
#print axioms PASoundness.PAtoCompactPartialInverseOutsideExists.outside_successor_exists_certificate
