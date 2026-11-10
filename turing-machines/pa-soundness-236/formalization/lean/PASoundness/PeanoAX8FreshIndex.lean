import PASoundness.PeanoAX8DecodedFresh
import PASoundness.PeanoBetaCRTAlpha

/-! Capture-safe normalization of a decoded AX8 predicate to a fresh index.
These are syntactic facts, not an AX8 derivation or a semantic soundness proof. -/
namespace PASoundness.PeanoAX8FreshIndex
open FirstOrder FirstOrder.Language
open Peano CompactLogicalTransport

/-- A free index renamed to a fresh name and then renamed back recovers the
exact decoded arithmetic formula, including all parameters. -/
theorem decoded_roundtrip (b c j : Nat) (hbj : b ≠ j)
    (hj : j ∉ (interpreted c).freeVarFinset) :
    FOL.substAt (FOL.substAt (interpreted c) b (.var j)) j (.var b) = interpreted c :=
  PeanoBetaCRTAlpha.subst_roundtrip (interpreted c) b j hbj hj

/-- Renaming any free index to a name different from c preserves the decoded
formula's established freshness at its own code name c. -/
theorem decoded_code_fresh (b c j : Nat) (hcj : c ≠ j) :
    c ∉ (FOL.substAt (interpreted c) b (.var j)).freeVarFinset := by
  unfold FOL.substAt
  rw [SyntaxTransport.formula_subst_freeVars]
  rintro ⟨x, hx, hc⟩
  by_cases hxb : x = b
  · subst x
    simp [FirstOrder.Language.Term.varFinset, hcj] at hc
  · have he : c = x := by simpa [hxb, FirstOrder.Language.Term.varFinset] using hc
    subst x
    exact PeanoAX8DecodedFresh.interpreted_self_fresh c hx

/-- Renaming b to a distinct j removes b from the normalized predicate. -/
theorem decoded_old_index_fresh (b c j : Nat) (hbj : b ≠ j) :
    b ∉ (FOL.substAt (interpreted c) b (.var j)).freeVarFinset :=
  PeanoBetaCRTAlpha.subst_rename_fresh (interpreted c) b j hbj

/-- There is a normalization index fresh for the decoded predicate and
distinct from both the original index and code names. -/
theorem exists_fresh_index (b c : Nat) :
    ∃ j, b ≠ j ∧ c ≠ j ∧ j ∉ (interpreted c).freeVarFinset := by
  let j := (interpreted c).freeVarFinset.sup id + b + c + 1
  have hb : b ≠ j := by dsimp [j]; omega
  have hc : c ≠ j := by dsimp [j]; omega
  have hf : j ∉ (interpreted c).freeVarFinset := by
    intro h
    have hle : j ≤ (interpreted c).freeVarFinset.sup id := Finset.le_sup (f := id) h
    dsimp [j] at hle
    omega
  exact ⟨j,hb,hc,hf⟩

end PASoundness.PeanoAX8FreshIndex

#print axioms PASoundness.PeanoAX8FreshIndex.decoded_roundtrip
#print axioms PASoundness.PeanoAX8FreshIndex.decoded_code_fresh
#print axioms PASoundness.PeanoAX8FreshIndex.exists_fresh_index
