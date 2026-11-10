import PASoundness.PAtoCompactCleanImageWitness
import PASoundness.PAtoCompactInverseBijection

/-! Quantified K lifting of an explicit image-witness transfer. The pointwise
transfer, graph correspondence and old image clause remain visible inputs;
no filter or isomorphism existence is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanImageTransfer
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanImageWitness
open PASoundness.PAtoCompactInverseBijection PASoundness.PAtoCompactTransitiveWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Distribute a shared antecedent over implication. -/
def guarded_distribution (X A B : Nat) : KDerivation
    (imp (imp X (imp A B)) (imp (imp X A) (imp X B))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [X,imp X A,imp X (imp A B)]
  have hx : Context Γ X := Context.head _ _
  have ha : Context Γ (imp X A) := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp X (imp A B)) := .hypothesis (by simp [Γ])
  exact .mp (.mp hx ha) (.mp hx hb)

def oldImage : Nat := allCode 2 (imp (member 0 2) (existsCode 3 oldWitness.encode))
def newImage : Nat := allCode 2 (imp (member 0 2) (existsCode 3 newWitness.encode))

/-- Lift a supplied guarded pointwise witness transfer through the target
existential and source universal, preserving literal K proof data. -/
def transfer_image (hpoint : KDerivation (imp guardedEdges.encode
    (imp (member 0 2) (imp oldWitness.encode newWitness.encode)))) :
    KDerivation (imp guardedEdges.encode (imp oldImage newImage)) := by
  let G := guardedEdges.encode
  let X := member 0 2
  let A := existsCode 3 oldWitness.encode
  let B := existsCode 3 newWitness.encode
  have hvG3 : KDerivation (imp G (allCode 3 G)) := guardedEdges.vacuity 3 (by decide)
  have hvX3 : KDerivation (imp X (allCode 3 X)) := membershipVacuity 0 2 3 (by decide) (by decide)
  have hlocal : Context [X,G] (imp oldWitness.encode newWitness.encode) :=
    .mp (Context.head [G] X) (.mp (Context.under (Context.head [] G) X) (.closed hpoint))
  have hall : Context [X,G] (allCode 3 (imp oldWitness.encode newWitness.encode)) :=
    Context.generalize 3 (by
      intro z hz
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
      by_cases he : z = X
      · subst z; exact hvX3
      · have hz' : z = G := hz.resolve_left he
        subst z; exact hvG3) hlocal
  have hmap : Context [X,G] (imp A B) := by
    apply Context.deduction
    have hall' : Context [A,X,G] (allCode 3 (imp oldWitness.encode newWitness.encode)) := Context.under hall A
    exact exists_map_context hall' (Context.head [X,G] A)
  have hpoint2 : Context [G] (imp X (imp A B)) := Context.deduction hmap
  have hvG2 : KDerivation (imp G (allCode 2 G)) := guardedEdges.vacuity 2 (by decide)
  have hall2 : Context [G] (allCode 2 (imp X (imp A B))) :=
    Context.generalize 2 (by
      intro z hz
      have he : z = G := by simpa using hz
      subst z
      exact hvG2) hpoint2
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldImage,G]
  have hold : Context Γ oldImage := Context.head _ _
  have htrans : Context Γ (allCode 2 (imp X (imp A B))) := Context.under hall2 oldImage
  have hcomp : Context Γ (allCode 2
      (imp (imp X (imp A B)) (imp (imp X A) (imp X B)))) :=
    .closed (.generalize 2 (guarded_distribution X A B))
  exact Context.allMP hold (Context.allMP htrans hcomp)

theorem transfer_image_certificate (hpoint : KDerivation (imp guardedEdges.encode
    (imp (member 0 2) (imp oldWitness.encode newWitness.encode)))) :
    theoremCode (certificate (transfer_image hpoint)) =
      imp guardedEdges.encode (imp oldImage newImage) := certificate_correct (transfer_image hpoint)

end PASoundness.PAtoCompactCleanImageTransfer

#print axioms PASoundness.PAtoCompactCleanImageTransfer.transfer_image
#print axioms PASoundness.PAtoCompactCleanImageTransfer.transfer_image_certificate
