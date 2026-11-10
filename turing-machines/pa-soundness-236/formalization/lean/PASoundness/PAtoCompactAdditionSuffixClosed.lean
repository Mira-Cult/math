import PASoundness.PAtoCompactAdditionSuffix
import PASoundness.PAtoCompactAdditionSuffixAlignment

/-! The selector-generated suffix witness can be renamed to the exact
addition-formula output binder. This is a finite K proof of suffix existence;
it does not assert existence of the complete addition graph. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionSuffixClosed
open PASoundness.CompactProof PASoundness.CompactDerivations PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactAdditionSuffix

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

private theorem suffix_binders : 34 ∉ suffixFormula.binders := by decide

private theorem suffix_fresh (w : Nat) (hw : 35 < w) : w ∉ suffixFormula.names := by
  have hn : suffixFormula.names = {32,33,34,35} := by decide
  rw [hn]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  omega

private theorem replacement (w : Nat) : (replace 34 w suffixFormula).encode =
    filterGraph 32 w 35 (neg (member 33 35)) := by rfl

/-- Parametric alpha conversion keeps the selector witness opaque during
proof construction, avoiding normalization of its very large numeric code. -/
def alpha (w : Nat) (hw : 35 < w) :
    KDerivation (imp (existsCode w (filterGraph 32 w 35 (neg (member 33 35))))
      (existsCode 34 suffixFormula.encode)) := by
  have h := (existentialAlpha 34 w suffixFormula (by omega) suffix_binders (suffix_fresh w hw)).2
  rw [replacement] at h
  exact h

attribute [local irreducible] suffixWitness PAtoCompactFilteredSubset.filterPredicate

/-- K constructs a suffix at exactly the output binder used by the proposed
addition relation. The proof is syntactic and does not use standard HF truth. -/
def suffix_exists : KDerivation (existsCode 34 suffixFormula.encode) := by
  let w := suffixWitness 32 33 35
  have hw : 35 < w := (suffixWitness_bounds 32 33 35).2.2
  have hd : KDerivation (existsCode w (filterGraph 32 w 35 (neg (member 33 35)))) :=
    PAtoCompactAdditionSuffix.suffix_exists 32 33 35 (by decide) (by decide)
  exact .mp hd (alpha w hw)

theorem suffix_exists_certificate :
    theoremCode (certificate suffix_exists) = existsCode 34 suffixFormula.encode :=
  certificate_correct suffix_exists

end PASoundness.PAtoCompactAdditionSuffixClosed

#print axioms PASoundness.PAtoCompactAdditionSuffixClosed.alpha
#print axioms PASoundness.PAtoCompactAdditionSuffixClosed.suffix_exists
#print axioms PASoundness.PAtoCompactAdditionSuffixClosed.suffix_exists_certificate
