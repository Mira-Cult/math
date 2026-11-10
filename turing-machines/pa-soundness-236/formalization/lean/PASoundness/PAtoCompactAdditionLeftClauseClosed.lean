import PASoundness.PAtoCompactAdditionLeftPremises
import PASoundness.PAtoCompactAdditionLeftQuantified

/-! The left bijection clause for the unequal-top addition graph follows in K
from the displayed old bijection, clean graph, successor and adjunction data.
No K proof-data inputs or suffix-transitivity assumption remain. This proves
one clause only, not the full bijection or addition totality. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionLeftClauseClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactPointAdjoin PASoundness.PAtoCompactAdditionSuccessorGraphClean
open PASoundness.PAtoCompactAdditionOldSourceWitness PASoundness.PAtoCompactAdditionOldSourceClosed
open PASoundness.PAtoCompactAdditionLeftPointClosed PASoundness.PAtoCompactAdditionLeftPremises
open PASoundness.PAtoCompactAdditionLeftQuantified PASoundness.PAtoCompactSuccCongruenceData
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- This is the first literal conjunct of the full bijection formula after
its source and target are renamed to 38 and 40. -/
theorem left_of_bijection :
    (match replace 8 40 (replace 7 38 newBijection) with
      | .imp (.imp first _) _ => first
      | _ => .truth) = leftClause := by decide

/-- The proved point case is an implication from the common conjunction. -/
def point_from_premises : KDerivation (imp premisesCode
    (imp (member 38 2) (existsCode 3 strongBody.encode))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [member 38 2,premisesCode]
  have hm : Context Γ (member 38 2) := .head _ _
  have hp : Context Γ premisesCode := .hypothesis (by simp [Γ])
  have hb : Context Γ oldBijection.encode := Context.conjunctionLeft hp
  have h1 := Context.conjunctionRight hp
  have hc : Context Γ oldClean.encode := Context.conjunctionLeft h1
  have h2 := Context.conjunctionRight h1
  have hg : Context Γ (adjoinCode 6 11 9 16) := Context.conjunctionLeft h2
  have h3 := Context.conjunctionRight h2
  have hpair : Context Γ (pairFormula 11 31 32).encode := Context.conjunctionLeft h3
  have h4 := Context.conjunctionRight h3
  have ht : Context Γ (adjoinCode 34 32 40 41) := Context.conjunctionLeft h4
  have hs : Context Γ (successorCode 31 38 39) := Context.conjunctionRight h4
  have hout : Context Γ (existsCode 3 newBody.encode) := .mp hm (.mp hs (.mp ht
    (.mp hpair (.mp hg (.mp hc (.mp hb (.closed source_point_closed)))))))
  simpa [strongBody,newBody] using hout

/-- The exact left source-bijection clause follows from the explicit common
hypotheses. This proof retains no separately assumed point-case or vacuity
proof and requires no transitivity of the old suffix. -/
def left_clause_closed : KDerivation (imp premisesCode leftClause.encode) :=
  left_from_point premisesCode premises_vacuity point_from_premises

theorem left_clause_closed_certificate : theoremCode (certificate left_clause_closed) =
    imp premisesCode leftClause.encode := certificate_correct left_clause_closed
end PASoundness.PAtoCompactAdditionLeftClauseClosed
#print axioms PASoundness.PAtoCompactAdditionLeftClauseClosed.left_of_bijection
#print axioms PASoundness.PAtoCompactAdditionLeftClauseClosed.point_from_premises
#print axioms PASoundness.PAtoCompactAdditionLeftClauseClosed.left_clause_closed
#print axioms PASoundness.PAtoCompactAdditionLeftClauseClosed.left_clause_closed_certificate
