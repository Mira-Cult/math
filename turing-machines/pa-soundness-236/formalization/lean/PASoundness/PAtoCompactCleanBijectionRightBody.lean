import PASoundness.PAtoCompactCleanBijectionInstance
import PASoundness.PAtoCompactCleanRightUniqueAlpha
import PASoundness.CompactQuantifiers

/-! Pointwise K transfer of a preimage witness from a supplied original graph
to a supplied endpoint-filtered graph under the explicit guarded edge
correspondence. It does not construct a graph or establish bijection by itself. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanBijectionRightBody
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactCleanBijectionInstance
open PASoundness.PAtoCompactCleanRightUniqueAlpha
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def uniquePoint (g : Nat) : Formula := .imp
  (namedBoth (.member 0 4) (graphFormula g 4 3)) (.equal 4 2)

def witnessBody (g : Nat) : Formula := namedBoth (.member 0 2)
  (namedBoth (graphFormula g 2 3) (.all 4 (uniquePoint g)))

/-- The supplied source witness gives a target witness for the same endpoints;
the target endpoint's membership and guarded edge equivalence are explicit. -/
def transfer_body : KDerivation (imp guardedEdges.encode
    (imp (member 1 3) (imp (witnessBody 10).encode (witnessBody 6).encode))) := by
  let H := guardedEdges.encode
  let Y := member 1 3
  let B := (witnessBody 10).encode
  let Γ := [B,Y,H]
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hy : Context Γ Y := .hypothesis (by simp [Γ])
  have hb : Context Γ B := Context.head _ _
  have hx : Context Γ (member 0 2) := Context.conjunctionLeft hb
  have htail := Context.conjunctionRight hb
  have hedge : Context Γ (graphFormula 10 2 3).encode := Context.conjunctionLeft htail
  have huniq : Context Γ (allCode 4 (uniquePoint 10).encode) := Context.conjunctionRight htail
  have hguard := Context.mp hy (.mp hx (.mp hh (.closed instance_23)))
  have hnewedge : Context Γ (graphFormula 6 2 3).encode :=
    .mp hedge (Context.conjunctionLeft hguard)
  have hpoint : Context Γ (uniquePoint 6).encode := by
    apply Context.deduction
    let A := both (member 0 4) (graphFormula 6 4 3).encode
    have ha : Context (A :: Γ) A := Context.head _ _
    have hx4 : Context (A :: Γ) (member 0 4) := Context.conjunctionLeft ha
    have hnew : Context (A :: Γ) (graphFormula 6 4 3).encode := Context.conjunctionRight ha
    have hguard4 := Context.mp (Context.under hy A)
      (.mp hx4 (.mp (Context.under hh A) (.closed instance_43)))
    have hold : Context (A :: Γ) (graphFormula 10 4 3).encode :=
      .mp hnew (Context.conjunctionRight hguard4)
    have hu4 : Context (A :: Γ) (uniquePoint 10).encode := by
      have hi := CompactNamed.allSpecialize 4 (uniquePoint 10) (by decide)
      exact .mp (Context.under huniq A) (.closed hi)
    exact .mp (Context.conjunctionIntro hx4 hold) hu4
  have hvH : KDerivation (imp H (allCode 4 H)) := guardedEdges.vacuity 4 (by decide)
  have hvY : KDerivation (imp Y (allCode 4 Y)) := membershipVacuity 1 3 4 (by decide) (by decide)
  have hvB : KDerivation (imp B (allCode 4 B)) := old_body_vacuity_4
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode 4 h)) := by
    intro h hh'
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh'
    by_cases heB : h = B
    · subst h; exact hvB
    · by_cases heY : h = Y
      · subst h; exact hvY
      · have heH : h = H := (hh'.resolve_left heB).resolve_left heY
        subst h; exact hvH
  have hnewuniq : Context Γ (allCode 4 (uniquePoint 6).encode) := Context.generalize 4 hv hpoint
  exact Context.conjunctionIntro hx (Context.conjunctionIntro hnewedge hnewuniq)

theorem transfer_body_certificate : theoremCode (certificate transfer_body) =
    imp guardedEdges.encode (imp (member 1 3) (imp (witnessBody 10).encode (witnessBody 6).encode)) :=
  certificate_correct transfer_body

end PASoundness.PAtoCompactCleanBijectionRightBody

#print axioms PASoundness.PAtoCompactCleanBijectionRightBody.transfer_body
#print axioms PASoundness.PAtoCompactCleanBijectionRightBody.transfer_body_certificate
