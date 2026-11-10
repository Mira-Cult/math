import PASoundness.PAtoCompactPartialCompositionOutside
import PASoundness.PAtoCompactTransitiveWitness

/-! Existential lifting of the outside-source successor step for partial
composition. The same supplied graph witness remains valid; this establishes
neither an inside-source step nor composition-graph collection. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPartialCompositionOutsideExists
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactPartialCompositionBase PASoundness.PAtoCompactPartialCompositionOutside
open PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Reorder the derived outside step for uniform lifting under the graph binder. -/
def reordered_outside_step : KDerivation
    (imp (successorCode 10 13 15) (imp (neg (member 0 10))
      (imp partialComposition.encode nextPartialComposition.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 10 13 15
  let N := neg (member 0 10)
  let P := partialComposition.encode
  let Γ := [P,N,S]
  have hp : Context Γ P := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  exact .mp hn (.mp hs (.mp hp (.closed outside_successor)))

/-- An old graph witness remains a witness at the successor prefix when the
old prefix lies outside the source domain. All graph/domain parameters remain
free and the same bound graph value is retained by existential monotonicity. -/
def outside_successor_exists : KDerivation
    (imp (successorCode 10 13 15) (imp (neg (member 0 10))
      (imp (existsCode 9 partialComposition.encode)
        (existsCode 9 nextPartialComposition.encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let S := successorCode 10 13 15
  let N := neg (member 0 10)
  let P := partialComposition.encode
  let Q := nextPartialComposition.encode
  let Γ := [existsCode 9 P,N,S]
  have he : Context Γ (existsCode 9 P) := Context.head _ _
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hS : Context Γ (allCode 9 S) := .mp hs
    (.closed (successor_vacuity 10 13 15 9 (by decide) (by decide) (by decide)))
  have hN : Context Γ (allCode 9 N) := .mp hn
    (.closed (negationVacuity 9 (membershipVacuity 0 10 9 (by decide) (by decide))))
  have hall : Context Γ (allCode 9 (imp P Q)) :=
    Context.allMP hN (Context.allMP hS (.closed (.generalize 9 reordered_outside_step)))
  exact exists_map_context hall he

theorem outside_successor_exists_certificate :
    theoremCode (certificate outside_successor_exists) =
      imp (successorCode 10 13 15) (imp (neg (member 0 10))
        (imp (existsCode 9 partialComposition.encode)
          (existsCode 9 nextPartialComposition.encode))) :=
  certificate_correct outside_successor_exists

end PASoundness.PAtoCompactPartialCompositionOutsideExists

#print axioms PASoundness.PAtoCompactPartialCompositionOutsideExists.outside_successor_exists
#print axioms PASoundness.PAtoCompactPartialCompositionOutsideExists.outside_successor_exists_certificate
