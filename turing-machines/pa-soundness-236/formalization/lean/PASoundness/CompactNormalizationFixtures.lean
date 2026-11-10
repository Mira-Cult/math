import PASoundness.CompactNormalization

/-!
Executable structural controls for compact normalization. Positive fixtures
reduce the actual arbitrary-formula algorithm, including duplicated input
binder labels. Negative fixtures exercise literal prefix recognition and an
explicit variable-capture counterexample. No source or table is changed.
-/
namespace PASoundness.CompactNormalizationFixtures

open CompactNamed CompactNormalization

/-- The positive-rank convention includes quantifier-free truth. -/
theorem truth_rank : (normalizeNamed Formula.truth).rank = 1 := by decide

theorem truth_shape : (normalizeNamed Formula.truth).formula = .ex 1 .truth := by decide

/-- Both branches reuse name zero before freshening, and neither input is
already an alternating prefix of the whole implication. -/
def branchReuse : Formula :=
  .imp (.all 0 (.equal 0 1)) (.ex 0 (.member 0 1))

def branchReuseExpected : Formula :=
  .ex 6 (.all 5 (.ex 2 (.all 4 (.ex 3 (.imp (.equal 2 1) (.member 3 1))))))

theorem branchReuse_rank : (normalizeNamed branchReuse).rank = 5 := by decide

theorem branchReuse_shape : (normalizeNamed branchReuse).formula = branchReuseExpected := by decide

/-- Repeated nested binders in the input are handled before quantifier
movement. Generated vacuous names may later coincide with an outer binder;
the proved meaning and the source's newest-binding convention cover this. -/
def nestedShadow : Formula := .all 0 (.all 0 (.equal 0 0))

def nestedShadowExpected : Formula := .ex 3 (.all 2 (.ex 2 (.all 1 (.equal 1 1))))

theorem nestedShadow_rank : (normalizeNamed nestedShadow).rank = 4 := by decide

theorem nestedShadow_shape : (normalizeNamed nestedShadow).formula = nestedShadowExpected := by decide

/-- Wrong leading polarity is rejected by the actual source recognizer. -/
theorem rejects_wrong_leading_polarity :
    CompactMatrix.normalize .ex 1 (.all 0 (.equal 0 0)) = none := rfl

/-- A residual quantifier cannot masquerade as a quantifier-free matrix. -/
theorem rejects_short_rank :
    CompactMatrix.normalize .ex 1
      (CompactMatrix.existsAt 0 (.all 1 (.equal 0 0))) = none := rfl

/-- Consecutive existentials need a dummy universal; the literal recognizer
does not silently reinterpret their syntactic rank. -/
theorem rejects_unpadded_existentials :
    CompactMatrix.normalize .ex 2
      (CompactMatrix.existsAt 0 (CompactMatrix.existsAt 1 .truth)) = none := rfl

/-- Dropping the freshness premise from quantifier movement changes truth. -/
def captureBefore : Formula := .imp (.equal 0 1) (.all 0 (.equal 0 1))

def captureAfter : Formula := .all 0 (.imp (.equal 0 1) (.equal 0 1))

theorem captureBefore_false : ¬ captureBefore.Realize (fun _ => 0) := by
  intro h
  have hh := h (show Formula.Realize (fun _ => 0) (.equal 0 1) from rfl) 1
  simpa [Formula.Realize, CompactMatrix.update] using hh

theorem captureAfter_true : captureAfter.Realize (fun _ => 0) := by
  intro v h
  exact h

theorem capture_counterexample :
    ¬ (captureBefore.Realize (fun _ => 0) ↔ captureAfter.Realize (fun _ => 0)) :=
  fun h => captureBefore_false (h.mpr captureAfter_true)

/-- Actual normalized certificate generation is available for a nontrivial
closed K equality theorem; the formula proof is transported, not reinterpreted. -/
def equalityCertificate : Nat :=
  CompactProof.certificate (.generalize 0 (CompactDerivations.equalityReflexive 0))

theorem equality_certificate_normalized :
    CompactProof.theoremCode (certificateFrom equalityCertificate) =
      normalizeCode (CompactProof.allCode 0 (CompactProof.equal 0 0)) := by
  rw [certificateFrom_correct]
  congr 1
  exact CompactProof.certificate_correct _

end PASoundness.CompactNormalizationFixtures
