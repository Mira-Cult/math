import PASoundness.PeanoAX8AliasPermutation
import PASoundness.PeanoAX8RenamedFresh
import PASoundness.PeanoAX8DecodedFresh
import PASoundness.PeanoFreeNamePermutationInverse

/-! The literal aliased-input AX8 comprehension formula inside PA.

The quantified input becomes bit(i,i); the separate outer position remains
outside that quantifier. The proof uses one finite selector code and does not
assume semantic truth of PA or compact arithmetic. -/
namespace PASoundness.PeanoAX8AliasClosed
open FirstOrder FirstOrder.Language
open Peano PeanoArithmetic CompactLogicalTransport
open PeanoFreeNamePermutation PeanoFreeNamePermutationInverse

/-- PA derives the literal alias case when the output name is distinct from
the common input/index name. The same code witness serves both clauses. -/
theorem alias_comprehension (b c : Nat) (hbc : b ≠ c) :
    FormulaProves (comprehensionFormula b b c) := by
  obtain ⟨xs, hb, hc, hf⟩ := PeanoAX8RenamedFresh.alias_fresh (interpreted c) b c
    hbc (PeanoAX8DecodedFresh.interpreted_self_fresh c)
  let ρ := applyFormula xs (interpreted c)
  have hcanon : FormulaProves (PeanoAX8SingletonFormula.canonicalReduced ρ) :=
    PeanoAX8SingletonFormula.canonical_reduced ρ
      (hf 0 (by decide)) (hf 1 (by decide)) (hf 2 (by decide)) (hf 3 (by decide))
  have hpermuted : FormulaProves (applyFormula xs (PeanoAX8AliasExtraction.aliasReduced b c)) := by
    rw [PeanoAX8AliasPermutation.alias_permute xs b c hb hc]
    exact hcanon
  have hback := applyFormula_proves xs.reverse _ hpermuted
  have hred : FormulaProves (PeanoAX8AliasExtraction.aliasReduced b c) := by
    simpa only [reverse_applyFormula] using hback
  exact .mp (PeanoAX8AliasExtraction.alias_of_reduced b c) hred

end PASoundness.PeanoAX8AliasClosed

#print axioms PASoundness.PeanoAX8AliasClosed.alias_comprehension
