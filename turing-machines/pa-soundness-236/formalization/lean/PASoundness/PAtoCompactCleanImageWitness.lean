import PASoundness.PAtoCompactCleanBijectionInstance

/-! Pointwise image-witness transfer from a supplied old graph to a supplied
endpoint-restricted graph under the explicit guarded edge-equivalence schema.
The K derivation uses no semantic soundness or graph-existence assumption. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanImageWitness
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanBijectionInstance
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def oldUniqueBody (v : Nat) : Formula :=
  .imp (namedBoth (.member 1 v) (graphFormula 10 2 v)) (.equal v 3)

def oldUnique : Formula := .all 4 (oldUniqueBody 4)
def oldUniqueFresh : Formula := .all 30 (oldUniqueBody 30)

def oldWitness : Formula := namedBoth (.member 1 3)
  (namedBoth (graphFormula 10 2 3) oldUnique)

def oldWitnessFresh : Formula := namedBoth (.member 1 3)
  (namedBoth (graphFormula 10 2 3) oldUniqueFresh)

def newUnique : Formula := .all 4 (.imp
  (namedBoth (.member 1 4) (graphFormula 6 2 4)) (.equal 4 3))

def newWitness : Formula := namedBoth (.member 1 3)
  (namedBoth (graphFormula 6 2 3) newUnique)

/-- Rename the uniqueness binder before generalizing a new uniqueness proof. -/
def freshen_old_witness : KDerivation (imp oldWitness.encode oldWitnessFresh.encode) := by
  have ha := (universalAlpha 4 30 (oldUniqueBody 4) (by decide) (by decide) (by decide)).1
  have he : replace 4 30 (oldUniqueBody 4) = oldUniqueBody 30 := by decide
  rw [he] at ha
  apply Context.closeEmpty
  apply Context.deduction
  have hw : Context [oldWitness.encode] oldWitness.encode := Context.head [] _
  have hm : Context [oldWitness.encode] (member 1 3) := Context.conjunctionLeft hw
  have hc := Context.conjunctionRight hw
  have hg : Context [oldWitness.encode] (graphFormula 10 2 3).encode := Context.conjunctionLeft hc
  have hu : Context [oldWitness.encode] oldUnique.encode := Context.conjunctionRight hc
  have hu' : Context [oldWitness.encode] oldUniqueFresh.encode := .mp hu (.closed ha)
  exact Context.conjunctionIntro hm (Context.conjunctionIntro hg hu')

/-- A fresh old uniqueness binder instantiates at the new target name 4. -/
def fresh_unique_at_four : KDerivation (imp oldUniqueFresh.encode (oldUniqueBody 4).encode) := by
  have hi := universalInstance 30 4 (oldUniqueBody 30) (by decide) (by decide) (by decide)
  have he : replace 30 4 (oldUniqueBody 30) = oldUniqueBody 4 := by decide
  rw [he] at hi
  exact hi

/-- Under the supplied guarded comparison and source membership, a single old
image witness with its uniqueness property transfers to the filtered graph. -/
def image_witness : KDerivation (imp guardedEdges.encode
    (imp (member 0 2) (imp oldWitness.encode newWitness.encode))) := by
  let G := guardedEdges.encode
  let X := member 0 2
  let W := oldWitnessFresh.encode
  let Γ := [W,X,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hw : Context Γ W := Context.head _ _
  have hy : Context Γ (member 1 3) := Context.conjunctionLeft hw
  have hrest := Context.conjunctionRight hw
  have hold : Context Γ (graphFormula 10 2 3).encode := Context.conjunctionLeft hrest
  have hu : Context Γ oldUniqueFresh.encode := Context.conjunctionRight hrest
  have hcmp23 := Context.mp hg (.closed instance_23)
  change Context Γ (imp X (imp (member 1 3)
    (both (imp (graphFormula 10 2 3).encode (graphFormula 6 2 3).encode)
      (imp (graphFormula 6 2 3).encode (graphFormula 10 2 3).encode)))) at hcmp23
  have hpair23 := Context.mp hy (Context.mp hx hcmp23)
  have hnew : Context Γ (graphFormula 6 2 3).encode := .mp hold (Context.conjunctionLeft hpair23)
  have huniqpoint : Context Γ (imp (both (member 1 4) (graphFormula 6 2 4).encode) (equal 4 3)) := by
    apply Context.deduction
    let B := both (member 1 4) (graphFormula 6 2 4).encode
    have hp : Context (B :: Γ) B := Context.head Γ B
    have hy4 : Context (B :: Γ) (member 1 4) := Context.conjunctionLeft hp
    have hnew4 : Context (B :: Γ) (graphFormula 6 2 4).encode := Context.conjunctionRight hp
    have hcmp24 := Context.mp (Context.under hg B) (.closed instance_24)
    change Context (B :: Γ) (imp X (imp (member 1 4)
      (both (imp (graphFormula 10 2 4).encode (graphFormula 6 2 4).encode)
        (imp (graphFormula 6 2 4).encode (graphFormula 10 2 4).encode)))) at hcmp24
    have hp24 := Context.mp hy4 (Context.mp (Context.under hx B) hcmp24)
    have hold4 : Context (B :: Γ) (graphFormula 10 2 4).encode :=
      .mp hnew4 (Context.conjunctionRight hp24)
    have hinst := Context.mp (Context.under hu B) (.closed fresh_unique_at_four)
    change Context (B :: Γ) (imp (both (member 1 4) (graphFormula 10 2 4).encode) (equal 4 3)) at hinst
    exact .mp (Context.conjunctionIntro hy4 hold4) hinst
  have hvG : KDerivation (imp G (allCode 4 G)) := guardedEdges.vacuity 4 (by decide)
  have hvX : KDerivation (imp X (allCode 4 X)) := membershipVacuity 0 2 4 (by decide) (by decide)
  have hvW : KDerivation (imp W (allCode 4 W)) := oldWitnessFresh.vacuity 4 (by decide)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases hW : h = W
    · subst h; exact hvW
    · by_cases hX : h = X
      · subst h; exact hvX
      · have hG : h = G := (hh.resolve_left hW).resolve_left hX
        subst h; exact hvG
  have huniq : Context Γ newUnique.encode := Context.generalize 4 hv huniqpoint
  have hfinal : Context Γ newWitness.encode :=
    Context.conjunctionIntro hy (Context.conjunctionIntro hnew huniq)
  have hF : KDerivation (imp G (imp X (imp W newWitness.encode))) := by
    exact Context.closeEmpty (Context.deduction (Context.deduction (Context.deduction hfinal)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [oldWitness.encode,X,G]
  have hOld : Context Δ oldWitness.encode := Context.head _ _
  have hX : Context Δ X := .hypothesis (by simp [Δ])
  have hG : Context Δ G := .hypothesis (by simp [Δ])
  have hWF : Context Δ W := .mp hOld (.closed freshen_old_witness)
  exact .mp hWF (.mp hX (.mp hG (.closed hF)))

theorem image_witness_certificate : theoremCode (certificate image_witness) =
    imp guardedEdges.encode (imp (member 0 2) (imp oldWitness.encode newWitness.encode)) :=
  certificate_correct image_witness

end PASoundness.PAtoCompactCleanImageWitness

#print axioms PASoundness.PAtoCompactCleanImageWitness.image_witness
#print axioms PASoundness.PAtoCompactCleanImageWitness.image_witness_certificate
