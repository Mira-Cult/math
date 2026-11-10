import PASoundness.PAtoCompactInductionSelectorAuxiliary
import PASoundness.PAtoCompactInductionContextFreshnessHelpers
import PASoundness.PAtoCompactNamedEncodingNameBound
import PASoundness.PAtoCompactAdjunction

/-! Syntactic selector and named-context side conditions for the joint numeric
allocation used by the candidate-restricted induction engine. The predicate is
arbitrary: a supplied absence for its low name m and an upper bound on its
names are the only predicate-specific hypotheses. No K derivation or induction
axiom is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactInductionJointSelectorFreshness
open PASoundness.CompactProof PASoundness.CompactNamed
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactQuantifiedRefutation
open PASoundness.PAtoCompactInductionContextFreshnessHelpers PASoundness.PAtoCompactInductionSelectorAuxiliary
open PASoundness.PAtoCompactNamedEncodingNameBound PASoundness.PAtoCompactAdjunction

/-- The numeric offsets satisfy all selector and named-context freshness
conditions in `candidate_restricted_induction`. This does not discharge the
predicate's remaining binders, the arithmetic base or the induction theorem. -/
theorem joint_selector_context_freshness (N B : Nat) (f : Formula)
    (hB : N+101 < B) (hf : f.names.sup id < B) (hmf : N+100 ∉ f.names) :
    let X := N+2
    let v := N+1
    let m := N+100
    let t := N+101
    let Y := B+100
    let W := B+5
    let p := B+7
    let q := B+8
    let u := B+12
    let r := B+13
    let w := B+24
    let point := B+101
    let z := B+3
    let C := filterPredicate Y t (neg f.encode)
    C ∉ [X,u,m,r] ∧ C ∉ f.names ∧ v ≠ C ∧ r ≠ C ∧
    m ∉ (namedFilterGraph Y t f).names ∧
    C ∉ (namedAllBase t m z f).names ∧
    C ∉ (namedAllSteps Y t v m w p q f).names ∧
    C ∉ (namedAllClassification Y v m z w p q).names ∧
    Y ∉ (namedAllBase t m z f).names ∧
    Y ∉ (replace t X f).names ∧
    W ≠ adjunctionPredicate X point ∧ Y ≠ adjunctionPredicate X point := by
  dsimp only
  let X := N+2
  let v := N+1
  let m := N+100
  let t := N+101
  let Y := B+100
  let W := B+5
  let p := B+7
  let q := B+8
  let u := B+12
  let r := B+13
  let w := B+24
  let point := B+101
  let z := B+3
  let C := filterPredicate Y t (neg f.encode)
  have hcy : B+100 < filterPredicate (B+100) (N+101) (neg f.encode) :=
    (filterPredicate_bounds (B+100) (N+101) (neg f.encode)).1
  have hcf : C ∉ f.names := filter_selector_not_in_names Y t f
  have hYf : Y ∉ f.names := by
    intro h
    have hh : Y ≤ f.names.sup id := Finset.le_sup (f := id) h
    dsimp [Y] at *
    omega
  have haux : ∀ a ∈ [v,m,z,w,p,q], a ≤ Y := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
      dsimp [v,m,z,w,p,q,Y] <;> omega
  have hschemas := selector_schemas_fresh_of_aux_le Y t v m z w p q f hcf haux
  have hg := filter_graph_fresh Y t m f (by dsimp [m,Y]; omega)
    (by dsimp [m,t]; omega) hmf
  have hb := container_base_fresh Y t m z f (by dsimp [Y,t]; omega)
    (by dsimp [Y,m]; omega) (by dsimp [Y,z]; omega) hYf
  have hi := container_instance_fresh Y t X f (by dsimp [Y,t]; omega)
    (by dsimp [Y,X]; omega) hYf
  have ha : B+101 < adjunctionPredicate (N+2) (B+101) :=
    (predicate_names_lt (N+2) (B+101)).2
  refine ⟨?_, hcf, ?_, ?_, hg, hschemas.1, hschemas.2.1, hschemas.2.2, hb, hi, ?_, ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    dsimp [X,u,m,r,Y,C,t] at *
    omega
  · dsimp [v,Y,C,t] at *; omega
  · dsimp [r,Y,C,t] at *; omega
  · change B+5 ≠ adjunctionPredicate (N+2) (B+101); omega
  · change B+100 ≠ adjunctionPredicate (N+2) (B+101); omega
end PASoundness.PAtoCompactInductionJointSelectorFreshness

#print axioms PASoundness.PAtoCompactInductionJointSelectorFreshness.joint_selector_context_freshness
