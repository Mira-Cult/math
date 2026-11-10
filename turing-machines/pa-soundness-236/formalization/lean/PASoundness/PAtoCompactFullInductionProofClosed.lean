import PASoundness.PAtoCompactFullInductionConditional
import PASoundness.PAtoCompactInductionJointEngineProof
import PASoundness.PAtoCompactInductionJointAllocation

/-! A finite K proof of the guarded full PA induction schema, including
parameterized formulas with nested quantifiers. Name allocation, engine, base,
step and universal packaging are constructed. The remaining PA-to-K logical
and arithmetic axiom handlers are separate obligations. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFullInductionProofClosed
open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardedAllElim PASoundness.PAtoCompactDirectGeneralization
open PASoundness.PAtoCompactVacuousQuantifierFree PASoundness.PAtoCompactFullInductionConditional
open PASoundness.PAtoCompactInductionJointEngineProof PASoundness.PAtoCompactInductionJointAllocation
open PASoundness.PAtoCompactInductionJointLowAllocation PASoundness.PAtoCompactInductionJointHighAllocation
open PASoundness.PAtoCompactInductionJointNumericAllocation
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Construct the literal guarded PA induction axiom for every PA formula.
No finite K proof data, formula-fragment evidence, or name premises are
supplied by the caller. The result is noncomputable proof data. -/
noncomputable def full_induction_closed (φ : Peano.Formula) (x : Nat) :
    KDerivation (guardedCode (Peano.inductionAxiom φ x)) := by
  let N := lowBound φ x
  let B := highBase φ x
  have hlow := low_allocation φ x
  dsimp only at hlow
  rcases hlow with ⟨heq, hpGt, hpLt, hvLt, hmLt, hpChild, hpFree, hvFree,
    hmFree, hpNames, hvNames, hmNames, htBind⟩
  have hhigh := high_allocation φ x
  dsimp only at hhigh
  rcases hhigh with ⟨hB, hf, hbase, hmB, hYf, hYfree, hvGraph, hmGraph, hgraphGuard,
    hfilter, hW, hY⟩
  have hvBase : N+1 < B := lt_trans (Nat.add_lt_add_left (by decide : 1 < 101) N) hB
  let f := scopeAt φ x (N+101)
  have hf' : f.names.sup id < B := by change (scopeAt φ x (N+101)).names.sup id < B; rw [← heq]; exact hf
  have hm' : N+100 ∉ f.names := by change N+100 ∉ (scopeAt φ x (N+101)).names; rw [← heq]; exact hmNames
  have hv' : N+1 ∉ f.names := by change N+1 ∉ (scopeAt φ x (N+101)).names; rw [← heq]; exact hvNames
  have hp' : N+2 ∉ f.names := by change N+2 ∉ (scopeAt φ x (N+101)).names; rw [← heq]; exact hpNames
  have ht' : N+101 ∉ f.binders := by change N+101 ∉ (scopeAt φ x (N+101)).binders; rw [heq] at htBind; exact htBind
  have heng := joint_engine N B f hB hf' hm' hv' hp' ht'
  have hnum := joint_numeric_freshness N B (N+2) rfl hB
  dsimp only at hnum
  rcases hnum with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _,
    hmem, hsucc, hcy, hcz, hg, hl, hp⟩
  apply full_induction_of_engine φ x (N+100) B (N+2) (B+100) (N+1) (B+24)
    (B+6) (B+7) (B+8) (B+12) (B+15) (B+13)
    (B+25) (B+26) (B+27) (B+28) (B+29) (B+30) (B+31)
    (B+32) (B+33) (B+34) (B+35) (B+36)
  all_goals first | assumption | (rw [heq]; assumption)

end PASoundness.PAtoCompactFullInductionProofClosed

#print axioms PASoundness.PAtoCompactFullInductionProofClosed.full_induction_closed
