import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactZeroTransitive

/-! A transitive input has an existential transitive successor witness in K.
No witness uniqueness, fixed domain predicate, or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTransitiveWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactZeroTransitive

/-- Existential monotonicity under an arbitrary proof context. This derives the
conclusion directly and does not assume a vacuity theorem for its bound name. -/
def exists_map_context {Γ : List Nat} {x A B : Nat}
    (h : Context Γ (allCode x (imp A B))) (ha : Context Γ (existsCode x A)) :
    Context Γ (existsCode x B) := by
  apply Context.deduction
  have hcontra : Context (allCode x (neg B) :: Γ) (allCode x (imp (neg B) (neg A))) :=
    Context.allMP (Context.under h (allCode x (neg B))) (.closed (.generalize x (contrapositionFormula A B)))
  have hnotA : Context (allCode x (neg B) :: Γ) (allCode x (neg A)) :=
    Context.allMP (Context.head Γ (allCode x (neg B))) hcontra
  exact .mp hnotA (Context.under ha (allCode x (neg B)))

/-- Given syntactic transitivity of x, selector 8 constructs a successor
witness satisfying transitivity. All auxiliary names are chosen explicitly,
above the input's bound names and the selector's formula/witness code. -/
def transitive_successor_exists (x p q : Nat)
    (hpx : p ≠ x) (hqx : q ≠ x) (hpq : p ≠ q) :
    let point := x+1
    let code := adjunctionPredicate x point
    let w := code+p+q+1
    let d := w+1
    let r := d+1
    let s := d+2
    KDerivation (imp (transitiveCode x p q)
      (existsCode d (both (successorCode x d w) (transitiveCode d r s)))) := by
  dsimp only
  let point := x+1
  let code := adjunctionPredicate x point
  let w := code+p+q+1
  let d := w+1
  let r := d+1
  let s := d+2
  have hc := predicate_names_lt x point
  have hpoint : point ≠ x := by dsimp [point]; omega
  have hwp : w ≠ point := by dsimp [w,code]; omega
  have hwx : w ≠ x := by dsimp [w,code]; omega
  have hwc : w ≠ adjunctionPredicate x point := by dsimp [w,code]; omega
  have hdx : d ≠ x := by dsimp [d,w,code]; omega
  have hdp : d ≠ point := by dsimp [d,w,code]; omega
  have hdw : d ≠ w := by dsimp [d,w]; omega
  have hdc : d ≠ adjunctionPredicate x point := by dsimp [d,w,code]; omega
  have hdp' : d ≠ p := by dsimp [d,w]; omega
  have hdq : d ≠ q := by dsimp [d,w]; omega
  have hrx : r ≠ x := by dsimp [r,d,w,code]; omega
  have hrd : r ≠ d := by dsimp [r]; omega
  have hrw : r ≠ w := by dsimp [r,d]; omega
  have hrp : r ≠ p := by dsimp [r,d,w]; omega
  have hrq : r ≠ q := by dsimp [r,d,w]; omega
  have hsx : s ≠ x := by dsimp [s,d,w,code]; omega
  have hsd : s ≠ d := by dsimp [s]; omega
  have hsw : s ≠ w := by dsimp [s,d]; omega
  have hsp : s ≠ p := by dsimp [s,d,w]; omega
  have hsq : s ≠ q := by dsimp [s,d,w]; omega
  have hf : ∀ t ∈ [r,s], ∀ z ∈ [x,d,w,p,q], t ≠ z := by
    intro t ht z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht hz
    rcases ht with rfl | rfl <;> rcases hz with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hsucc : KDerivation (existsCode d (successorCode x d w)) :=
    successor_graph_exists_fresh x point w d hpoint hwp hwx hwc hdx hdp hdw hdc
  have hclosure : KDerivation (imp (transitiveCode x p q)
      (imp (successorCode x d w) (transitiveCode d r s))) :=
    successor_transitive_closed x d w p q r s hwx (Ne.symm hdw) hpx hpq hqx hf
  let T := transitiveCode x p q
  let G := successorCode x d w
  let D := both G (transitiveCode d r s)
  let Γ := [T]
  have ht : Context Γ T := Context.head [] T
  have himp : Context Γ (imp G D) := by
    apply Context.deduction
    have hg : Context (G :: Γ) G := Context.head Γ G
    have ht' := Context.under ht G
    exact Context.conjunctionIntro hg (.mp hg (.mp ht' (.closed hclosure)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode d h)) := by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    exact transitive_vacuity x p q d hdx hdp' hdq
  have hall : Context Γ (allCode d (imp G D)) := Context.generalize d hv himp
  have hex : Context Γ (existsCode d G) := .closed hsucc
  have hresult : Context Γ (existsCode d D) := exists_map_context hall hex
  apply Context.closeEmpty
  apply Context.deduction
  exact hresult

theorem transitive_successor_certificate (x p q : Nat)
    (hpx : p ≠ x) (hqx : q ≠ x) (hpq : p ≠ q) :
    let point := x+1
    let code := adjunctionPredicate x point
    let w := code+p+q+1
    let d := w+1
    let r := d+1
    let s := d+2
    theoremCode (certificate (transitive_successor_exists x p q hpx hqx hpq)) =
      imp (transitiveCode x p q)
        (existsCode d (both (successorCode x d w) (transitiveCode d r s))) :=
  certificate_correct (transitive_successor_exists x p q hpx hqx hpq)

/-- A concrete K theorem exhibits a zero-graph/transitive witness together
with a transitive successor witness. This finite nesting is not an induction
principle or a single globally successor-closed domain. -/
def zero_and_transitive_successor :
    let code := adjunctionPredicate 1 2
    let w := code+3+4+1
    let d := w+1
    let r := d+1
    let s := d+2
    KDerivation (existsCode 1
      (both (both (zeroCode 1 2) (transitiveCode 1 3 4))
        (existsCode d (both (successorCode 1 d w) (transitiveCode d r s))))) := by
  dsimp only
  let Z := both (zeroCode 1 2) (transitiveCode 1 3 4)
  let code := adjunctionPredicate 1 2
  let w := code+3+4+1
  let d := w+1
  let r := d+1
  let s := d+2
  let E := existsCode d (both (successorCode 1 d w) (transitiveCode d r s))
  have himp : KDerivation (imp Z (both Z E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hz : Context [Z] Z := Context.head [] Z
    have ht : Context [Z] (transitiveCode 1 3 4) := Context.conjunctionRight hz
    have he : Context [Z] E := .mp ht (.closed (transitive_successor_exists 1 3 4 (by decide) (by decide) (by decide)))
    exact Context.conjunctionIntro hz he
  exact .mp transitive_zero_exists (existsCongr 1 himp)

theorem zero_and_transitive_successor_certificate :
    let code := adjunctionPredicate 1 2
    let w := code+3+4+1
    let d := w+1
    let r := d+1
    let s := d+2
    theoremCode (certificate zero_and_transitive_successor) =
      existsCode 1 (both (both (zeroCode 1 2) (transitiveCode 1 3 4))
        (existsCode d (both (successorCode 1 d w) (transitiveCode d r s)))) :=
  certificate_correct zero_and_transitive_successor

end PASoundness.PAtoCompactTransitiveWitness
