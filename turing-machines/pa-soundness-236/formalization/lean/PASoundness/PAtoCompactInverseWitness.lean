import PASoundness.PAtoCompactOrderIsomorphism
import PASoundness.CompactDerivations

/-! A pointwise witness-transfer component for a proposed inverse relation.
The old and new graph codes are the exact Kuratowski graphFormula instances.
The inverse implications are explicit K antecedents; no inverse graph is
constructed and no isomorphism symmetry or arithmetic interpretation follows.
Compact code 1 remains the literal encoded falsum. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInverseWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactOrderIsomorphism
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Purely syntactic local uniqueness transport: if H entails G and G
suffices in a guarded uniqueness test, then H suffices in the same test. -/
def uniqueness_transport (X G H E : Nat) : KDerivation
    (imp (imp H G) (imp (imp (both X G) E) (imp (both X H) E))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [both X H, imp (both X G) E, imp H G]
  have hxh : Context Γ (both X H) := Context.head _ _
  have hx : Context Γ X := Context.conjunctionLeft hxh
  have hh : Context Γ H := Context.conjunctionRight hxh
  have hconv : Context Γ (imp H G) := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .mp hh hconv
  have hu : Context Γ (imp (both X G) E) := .hypothesis (by simp [Γ])
  exact .mp (Context.conjunctionIntro hx hg) hu

/-- Lifting a family of reverse graph implications transports the entire
quantified uniqueness test. No freshness premise is needed for this closed
proof-rule transformation; reading particular named instances still requires
capture-safe graph names. -/
def all_uniqueness_transport (v X G H E : Nat) : KDerivation
    (imp (allCode v (imp H G))
      (imp (allCode v (imp (both X G) E))
        (allCode v (imp (both X H) E)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [allCode v (imp (both X G) E), allCode v (imp H G)]
  have hi : Context Γ (allCode v (imp H G)) := .hypothesis (by simp [Γ])
  have hu : Context Γ (allCode v (imp (both X G) E)) := Context.head _ _
  have hl : Context Γ (allCode v (imp (imp H G)
      (imp (imp (both X G) E) (imp (both X H) E)))) :=
    .closed (.generalize v (uniqueness_transport X G H E))
  exact Context.allMP hu (Context.allMP hi hl)

def oldGraph : Nat := (graphFormula 6 2 3).encode
def newGraph : Nat := (graphFormula 7 3 2).encode
def oldAt4 : Nat := (graphFormula 6 4 3).encode
def newAt4 : Nat := (graphFormula 7 3 4).encode
def oldUnique : Nat := allCode 4 (imp (both (member 0 4) oldAt4) (equal 4 2))
def newUnique : Nat := allCode 4 (imp (both (member 0 4) newAt4) (equal 4 2))
def oldWitness : Nat := both (member 0 2) (both oldGraph oldUnique)
def newWitness : Nat := both (member 0 2) (both newGraph newUnique)

/-- For a fixed old preimage witness, the explicitly supplied graph
conversion at that witness and universally quantified reverse conversion
transfer its domain membership, graph edge, and uniqueness to the inverse
orientation. Names 0,2,3,4,6,7 are distinct from internal graph binders
19–22. This is only a witness transformation, not an inverse graph existence
or whole-bijection theorem. -/
def inverse_witness : KDerivation
    (imp (imp oldGraph newGraph)
      (imp (allCode 4 (imp newAt4 oldAt4)) (imp oldWitness newWitness))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let C := imp oldGraph newGraph
  let R := allCode 4 (imp newAt4 oldAt4)
  let Γ := [oldWitness,R,C]
  have hw : Context Γ oldWitness := Context.head _ _
  have hx : Context Γ (member 0 2) := Context.conjunctionLeft hw
  have hw' : Context Γ (both oldGraph oldUnique) := Context.conjunctionRight hw
  have hg : Context Γ oldGraph := Context.conjunctionLeft hw'
  have hu : Context Γ oldUnique := Context.conjunctionRight hw'
  have hc : Context Γ C := .hypothesis (by simp [Γ])
  have hr : Context Γ R := .hypothesis (by simp [Γ])
  have hn : Context Γ newGraph := .mp hg hc
  have hnu : Context Γ newUnique := by
    exact .mp hu (.mp hr (.closed
      (all_uniqueness_transport 4 (member 0 4) oldAt4 newAt4 (equal 4 2))))
  exact Context.conjunctionIntro hx (Context.conjunctionIntro hn hnu)

theorem inverse_witness_certificate : theoremCode (certificate inverse_witness) =
    imp (imp oldGraph newGraph)
      (imp (allCode 4 (imp newAt4 oldAt4)) (imp oldWitness newWitness)) :=
  certificate_correct inverse_witness

end PASoundness.PAtoCompactInverseWitness

#print axioms PASoundness.PAtoCompactInverseWitness.inverse_witness
#print axioms PASoundness.PAtoCompactInverseWitness.inverse_witness_certificate
