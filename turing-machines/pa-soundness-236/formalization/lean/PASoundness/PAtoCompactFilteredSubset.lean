import PASoundness.CompactSemantics
import PASoundness.CompactDerivations

/-! Literal selector-8 finite filtering, including its optional singleton. The
formula code is also the witness-variable name. Compact conjunction and
existence use code 1, literally `member 0 0`; the ordinary logical reading is
established separately for standard HF semantics. This proves a K existence
statement, not induction or a fixed arithmetic domain. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactFilteredSubset
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactMatrix PASoundness.CompactSemantics

/-- The predicate is conjoined with membership in x before invoking selector
8. Thus its optional singleton can be included only when it is already in x. -/
def filterPredicate (x t P : Nat) : Nat := both (member x t) P

def filterBody (x t P : Nat) : Nat :=
  let c := filterPredicate x t P
  both (allCode t (both
      (imp (member x t) (imp c (member c t)))
      (imp (member c t) c)))
    (imp c (member c t))

/-- Exact filtered membership equivalence, using K's conjunction encoding. -/
def filterGraph (x y t P : Nat) : Nat :=
  allCode t (both
    (imp (member y t) (filterPredicate x t P))
    (imp (filterPredicate x t P) (member y t)))

/-- The predicate/witness code exceeds both input names and the entire
predicate code, so the literal selector guard cannot collide. -/
theorem filterPredicate_bounds (x t P : Nat) :
    x < filterPredicate x t P ∧ t < filterPredicate x t P ∧ P < filterPredicate x t P := by
  have h1 := Cantor.left_le_pair x t
  have h2 := Cantor.right_le_pair x t
  have h3 := Cantor.left_le_pair P 1
  have h4 := Cantor.left_le_pair (member x t) (neg P)
  have h5 := Cantor.right_le_pair (member x t) (neg P)
  have h6 := Cantor.left_le_pair (imp (member x t) (neg P)) 1
  unfold filterPredicate both neg imp member at *
  omega

/-- Predicate code c cannot occur as any variable name in the decoded
original P. This is syntactic freshness, not a semantic assumption. -/
theorem filter_witness_fresh_in_predicate (x t P : Nat) :
    filterPredicate x t P ∉ (decode P).vars := by
  intro h
  have hv := vars_decode_lt P (filterPredicate x t P) h
  have hp := (filterPredicate_bounds x t P).2.2
  omega

/-- Projection of literal selector 8, with its optional singleton retained. -/
def filter_selector_witness (x t P : Nat) :
    KDerivation (existsCode (filterPredicate x t P) (filterBody x t P)) := by
  let c := filterPredicate x t P
  have hc := filterPredicate_bounds x t P
  have hguard : ¬ (c = x ∨ c = t) := by dsimp [c]; omega
  have h := KDerivation.axiom (⟨8, by decide⟩ : Fin 9) x t c 0
  simp only [axiomCode, if_neg hguard] at h
  exact Context.closeEmpty (Context.conjunctionLeft (.closed h))

/-- One selector interior entails the exact membership equivalence. The
forward condition includes x-membership, so no extra member can leak in. -/
def filter_inner_exact (x t P : Nat) :
    let c := filterPredicate x t P
    let A := member x t
    let W := member c t
    let I := both (imp A (imp c W)) (imp W c)
    let J := both (imp W c) (imp c W)
    KDerivation (imp I J) := by
  dsimp only
  let c := filterPredicate x t P
  let A := member x t
  let W := member c t
  let I := both (imp A (imp c W)) (imp W c)
  apply Context.closeEmpty
  apply Context.deduction
  have hi : Context [I] I := Context.head [] I
  have hforward : Context [I] (imp W c) := Context.conjunctionRight hi
  have hpositive : Context [I] (imp A (imp c W)) := Context.conjunctionLeft hi
  have hreverse : Context [I] (imp c W) := by
    apply Context.deduction
    have hc : Context (c :: [I]) c := Context.head [I] c
    have ha : Context (c :: [I]) A := Context.conjunctionLeft hc
    exact .mp hc (.mp ha (Context.under hpositive c))
  exact Context.conjunctionIntro hforward hreverse

/-- Every selector witness has exactly the displayed filtered-membership
graph; the optional singleton adds nothing outside the selected filter. -/
def filter_body_exact (x t P : Nat) :
    KDerivation (imp (filterBody x t P) (filterGraph x (filterPredicate x t P) t P)) := by
  let c := filterPredicate x t P
  let A := member x t
  let W := member c t
  let I := both (imp A (imp c W)) (imp W c)
  let J := both (imp W c) (imp c W)
  have hp : KDerivation (imp (filterBody x t P) (allCode t I)) := by
    apply Context.closeEmpty
    apply Context.deduction
    exact Context.conjunctionLeft (Context.head [] (filterBody x t P))
  exact compose hp (allCongr t (filter_inner_exact x t P))

/-- Selector 8 constructs a represented set with exactly the requested
filtered membership relation. `x ≠ t` ensures the quantified element name does
not bind the input-set name. No predicate/domain/induction hypothesis is used. -/
def filtered_subset_exists (x t P : Nat) (_hxt : x ≠ t) :
    KDerivation (existsCode (filterPredicate x t P)
      (filterGraph x (filterPredicate x t P) t P)) :=
  .mp (filter_selector_witness x t P) (existsCongr _ (filter_body_exact x t P))

theorem filtered_subset_exists_certificate (x t P : Nat) (hxt : x ≠ t) :
    theoremCode (certificate (filtered_subset_exists x t P hxt)) =
      existsCode (filterPredicate x t P) (filterGraph x (filterPredicate x t P) t P) :=
  certificate_correct (filtered_subset_exists x t P hxt)

/-- In standard HF semantics, the graph is exactly membership in x and truth
of P under the test-variable assignment. The two names must avoid the binder. -/
theorem filterGraph_standard (x y t P : Nat) (ρ : Environment)
    (hxt : x ≠ t) (hyt : y ≠ t) :
    (decode (filterGraph x y t P)).Realize ρ ↔
      ∀ v, (bit (ρ y) v = true ↔
        (bit (ρ x) v = true ∧ (decode P).Realize (update ρ t v))) := by
  simp only [filterGraph, filterPredicate, realize_all, realize_both, realize_imp, realize_member]
  simp only [update_same, update_other ρ t x _ hxt, update_other ρ t y _ hyt]
  apply forall_congr'
  intro v
  tauto

/-- The entire existential K formula has the advertised finite-filter
semantics in the standard model. The automatically fresh witness name does
not alter P, even if P has arbitrary internal binders or other free names. -/
theorem filtered_subset_standard (x t P : Nat) (ρ : Environment) (hxt : x ≠ t) :
    (decode (existsCode (filterPredicate x t P)
      (filterGraph x (filterPredicate x t P) t P))).Realize ρ ↔
      ∃ code, ∀ v, (bit code v = true ↔
        (bit (ρ x) v = true ∧ (decode P).Realize (update ρ t v))) := by
  let c := filterPredicate x t P
  have hc := filterPredicate_bounds x t P
  have hxc : x ≠ c := by dsimp [c]; omega
  have hct : c ≠ t := by dsimp [c]; omega
  have hcfree : c ∉ (decode P).freeVars := by
    intro h
    exact filter_witness_fresh_in_predicate x t P ((decode P).freeVars_subset_vars h)
  rw [realize_exists]
  apply exists_congr
  intro code
  rw [filterGraph_standard x c t P (update ρ c code) hxt hct]
  simp only [update_same, update_other ρ c x code hxc]
  apply forall_congr'
  intro v
  have hp : (decode P).Realize (update (update ρ c code) t v) ↔
      (decode P).Realize (update ρ t v) := by
    rw [update_commute ρ c t code v hct]
    exact realize_update_fresh _ _ _ _ hcfree
  exact iff_congr Iff.rfl (and_congr Iff.rfl hp)

end PASoundness.PAtoCompactFilteredSubset
