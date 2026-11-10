import PASoundness.PAtoCompactReversePreimageWitness

/-! Fixed-witness transfer for the complementary inverse-bijection clause,
using correspondence restricted to the two candidate domains. No inverse
graph is constructed and no full symmetry or interpretation is asserted.
Code 1 is literal K self-membership. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactRestrictedInverseSecondWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactReversePreimageWitness
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def guardX : Nat := member 0 2
def guardY : Nat := member 1 3
def guardY4 : Nat := member 1 4
def forwardAt3 : Nat := imp (both guardY guardX) (imp oldGraph newGraph)
def backwardAt4 : Nat := imp (both guardY4 guardX) (imp newAt4 oldAt4)
def backwardAll : Nat := allCode 4 backwardAt4

/-- The fixed domain guard and an explicitly guarded reverse edge preserve
an old uniqueness test for each competing output. The guard order here is
`both X Y`, matching the literal restricted inverse matrix. -/
def guarded_uniqueness_reversed (Y X G H E : Nat) : KDerivation
    (imp Y (imp (imp (both X Y) (imp H G))
      (imp (imp (both X G) E) (imp (both X H) E)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [both X H,imp (both X G) E,imp (both X Y) (imp H G),Y]
  have hxh : Context Γ (both X H) := Context.head _ _
  have hx : Context Γ X := Context.conjunctionLeft hxh
  have hh : Context Γ H := Context.conjunctionRight hxh
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have hc : Context Γ (imp (both X Y) (imp H G)) := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .mp hh (.mp (Context.conjunctionIntro hx hy) hc)
  have hu : Context Γ (imp (both X G) E) := .hypothesis (by simp [Γ])
  exact .mp (Context.conjunctionIntro hx hg) hu

/-- A fixed old image witness transfers to a reverse preimage witness under
explicit source-domain membership and guarded edge-conversion hypotheses. -/
def guarded_inverse_witness : KDerivation
    (imp guardX (imp forwardAt3 (imp backwardAll (imp oldWitness newWitness)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldWitness,backwardAll,forwardAt3,guardX]
  have hw : Context Γ oldWitness := Context.head _ _
  have hx : Context Γ guardX := .hypothesis (by simp [Γ])
  have hf : Context Γ forwardAt3 := .hypothesis (by simp [Γ])
  have hb : Context Γ backwardAll := .hypothesis (by simp [Γ])
  have hy : Context Γ guardY := Context.conjunctionLeft hw
  have hw' : Context Γ (both oldGraph oldUnique) := Context.conjunctionRight hw
  have he : Context Γ oldGraph := Context.conjunctionLeft hw'
  have hu : Context Γ oldUnique := Context.conjunctionRight hw'
  have hn : Context Γ newGraph := .mp he (.mp (Context.conjunctionIntro hy hx) hf)
  have hxall : Context Γ (allCode 4 guardX) := by
    exact .mp hx (.closed (membershipVacuity 0 2 4 (by decide) (by decide)))
  have hlocal : Context Γ (allCode 4 (imp guardX (imp backwardAt4
      (imp (imp (both guardY4 oldAt4) (equal 4 3))
        (imp (both guardY4 newAt4) (equal 4 3)))))) :=
    .closed (.generalize 4 (guarded_uniqueness_reversed guardX guardY4 oldAt4 newAt4 (equal 4 3)))
  have hnew : Context Γ newUnique := Context.allMP hu
    (Context.allMP hb (Context.allMP hxall hlocal))
  exact Context.conjunctionIntro hy (Context.conjunctionIntro hn hnew)

theorem guarded_inverse_witness_certificate :
    theoremCode (certificate guarded_inverse_witness) =
      imp guardX (imp forwardAt3 (imp backwardAll (imp oldWitness newWitness))) :=
  certificate_correct guarded_inverse_witness

end PASoundness.PAtoCompactRestrictedInverseSecondWitness

#print axioms PASoundness.PAtoCompactRestrictedInverseSecondWitness.guarded_inverse_witness
#print axioms PASoundness.PAtoCompactRestrictedInverseSecondWitness.guarded_inverse_witness_certificate
