import PASoundness.PAtoCompactCleanMatrixData
import PASoundness.PAtoCompactDiagonalBijectionRight
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactCleanBijectionRightBody

/-! Transfer of the right bijection clause between two supplied graph
relations with guarded edge equivalence. The quantified lifting is parameterized
by explicit pointwise proof data and then instantiated by a separately proved
K witness transfer. No filter/graph existence or quotient law is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCleanBijectionRight
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactOrderIsomorphism
open PASoundness.PAtoCompactCleanMatrixData PASoundness.PAtoCompactDiagonalBijectionRight
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Exact witness matrix with graph name 6 replaced capture-safely by 10. -/
def oldWitness : Formula := replace 6 10 witnessBody

def oldRight : Formula := replace 6 10 rightClause

theorem old_right_shape : oldRight = .all 3 (.imp (.member 1 3) (.ex 2 oldWitness)) := by decide

/-- Propositional distribution of a guarded implication. -/
def guarded_compose (G A B : Nat) : KDerivation
    (imp (imp G (imp A B)) (imp (imp G A) (imp G B))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [G,imp G A,imp G (imp A B)]
  have hg : Context Γ G := Context.head _ _
  have ha : Context Γ (imp G A) := .hypothesis (by simp [Γ])
  have hb : Context Γ (imp G (imp A B)) := .hypothesis (by simp [Γ])
  exact .mp (.mp hg ha) (.mp hg hb)

/-- Quantify a supplied pointwise witness-matrix transfer, then lift it to the
literal right/preimage clause. No assumption here supplies that pointwise
transfer; it is explicit K proof data. -/
def right_clause_of_body
    (hBody : KDerivation (imp guardedEdges.encode (imp (member 1 3)
      (imp oldWitness.encode witnessBody.encode)))) :
    KDerivation (imp guardedEdges.encode (imp oldRight.encode rightClause.encode)) := by
  let H := guardedEdges.encode
  let Y := member 1 3
  let A := oldWitness.encode
  let B := witnessBody.encode
  let HA := both H Y
  let oldEx := existsCode 2 A
  let newEx := existsCode 2 B
  let F : Formula := namedBoth guardedEdges (.member 1 3)
  have hF : F.encode = HA := by rfl
  have hvF : KDerivation (imp HA (allCode 2 HA)) := by
    have h := F.vacuity 2 (by decide)
    simpa only [hF] using h
  have hlocal : KDerivation (imp HA (imp A B)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [A,HA]
    have ha : Context Γ A := Context.head _ _
    have hf : Context Γ HA := .hypothesis (by simp [Γ])
    exact .mp ha (.mp (Context.conjunctionRight hf) (.mp (Context.conjunctionLeft hf) (.closed hBody)))
  have hex : KDerivation (imp HA (imp oldEx newEx)) :=
    conditionalExistsCongr 2 hvF hlocal
  have hpoint : KDerivation (imp H (imp Y (imp oldEx newEx))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [Y,H]
    have hy : Context Γ Y := Context.head _ _
    have hh : Context Γ H := .hypothesis (by simp [Γ])
    exact .mp (Context.conjunctionIntro hh hy) (.closed hex)
  have hvH : KDerivation (imp H (allCode 3 H)) := guardedEdges.vacuity 3 (by decide)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [oldRight.encode,H]
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have ho : Context Γ (allCode 3 (imp Y oldEx)) := by
    have h := Context.head [H] oldRight.encode
    change Context Γ (allCode 3 (imp Y oldEx)) at h
    exact h
  have hallH : Context Γ (allCode 3 H) := .mp hh (.closed hvH)
  have hp : Context Γ (allCode 3 (imp Y (imp oldEx newEx))) :=
    Context.allMP hallH (.closed (.generalize 3 hpoint))
  have hc : Context Γ (allCode 3 (imp (imp Y (imp oldEx newEx))
      (imp (imp Y oldEx) (imp Y newEx)))) :=
    .closed (.generalize 3 (guarded_compose Y oldEx newEx))
  have htransfer := Context.allMP hp hc
  have hresult := Context.allMP ho htransfer
  change Context Γ (allCode 3 (imp Y newEx))
  exact hresult

theorem right_clause_of_body_certificate
    (hBody : KDerivation (imp guardedEdges.encode (imp (member 1 3)
      (imp oldWitness.encode witnessBody.encode)))) :
    theoremCode (certificate (right_clause_of_body hBody)) =
      imp guardedEdges.encode (imp oldRight.encode rightClause.encode) :=
  certificate_correct (right_clause_of_body hBody)

/-- The separately proved pointwise witness transfer has the exact old and
new witness matrices consumed above. -/
theorem witness_alignment_old : oldWitness = PAtoCompactCleanBijectionRightBody.witnessBody 10 := by decide

theorem witness_alignment_new : witnessBody = PAtoCompactCleanBijectionRightBody.witnessBody 6 := rfl

/-- The exact old preimage clause transfers to the filtered graph's exact
preimage clause under the supplied guarded edge equivalence. -/
def right_clause : KDerivation (imp guardedEdges.encode (imp oldRight.encode rightClause.encode)) := by
  apply right_clause_of_body
  rw [witness_alignment_old, witness_alignment_new]
  exact PAtoCompactCleanBijectionRightBody.transfer_body

theorem right_clause_certificate : theoremCode (certificate right_clause) =
    imp guardedEdges.encode (imp oldRight.encode rightClause.encode) :=
  certificate_correct right_clause

end PASoundness.PAtoCompactCleanBijectionRight

#print axioms PASoundness.PAtoCompactCleanBijectionRight.right_clause_of_body
#print axioms PASoundness.PAtoCompactCleanBijectionRight.right_clause_of_body_certificate
#print axioms PASoundness.PAtoCompactCleanBijectionRight.right_clause
#print axioms PASoundness.PAtoCompactCleanBijectionRight.right_clause_certificate
