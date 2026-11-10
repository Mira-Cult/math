import PASoundness.PAtoCompactSuccessorInjective

/-! A restricted K successor-injectivity step from an explicit transitivity
condition and non-self-membership. No domain closure or PA interpretation is
asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.CompactMatrix PASoundness.CompactSemantics
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective

/-- The finite-set value assigned to x is transitive. Compact `member a b`
means the value of b belongs to the value of a. -/
def transitiveCode (x p q : Nat) : Nat :=
  allCode p (allCode q (imp (member x p) (imp (member p q) (member x q))))

def transitiveBody (x p q : Nat) : CompactNamed.Formula :=
  .imp (.member x p) (.imp (.member p q) (.member x q))

/-- Two explicit variable instantiations of the transitivity formula. The
test labels p and q must be distinct from one another and both free names. -/
def transitive_instance (x u p q : Nat)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    KDerivation (imp (transitiveCode x p q)
      (imp (member x u) (imp (member u x) (member x x)))) := by
  let body := transitiveBody x p q
  have hfirst := CompactNamed.universalInstance p u (.all q body) hpu
    (by simp [body, transitiveBody, CompactNamed.Formula.binders, hpq])
    (by simp [body, transitiveBody, CompactNamed.Formula.binders, Ne.symm hqu])
  have hfirst' : KDerivation (imp (transitiveCode x p q)
      (allCode q (imp (member x u) (imp (member u q) (member x q))))) := by
    simpa [transitiveCode, body, transitiveBody, CompactNamed.Formula.encode,
      CompactNamed.replace, CompactNamed.rename, hpx, hpu, hpq, hqx, hqu,
      Ne.symm hpx, Ne.symm hpu, Ne.symm hpq, Ne.symm hqx, Ne.symm hqu] using hfirst
  have hsecond := CompactNamed.universalInstance q x (transitiveBody x u q) hqx
    (by simp [transitiveBody, CompactNamed.Formula.binders])
    (by simp [transitiveBody, CompactNamed.Formula.binders])
  have hsecond' : KDerivation (imp (allCode q (imp (member x u) (imp (member u q) (member x q))))
      (imp (member x u) (imp (member u x) (member x x)))) := by
    simpa [transitiveBody, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      hqx, hqu, Ne.symm hqx, Ne.symm hqu] using hsecond
  exact compose hfirst' hsecond'

/-- Transitivity and non-self-membership construct the exact no-two-cycle
implication needed by the conditional K injectivity theorem. -/
def no_cycle_from_transitive (x u p q : Nat)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    KDerivation (imp (transitiveCode x p q)
      (imp (neg (member x x)) (imp (member u x) (neg (member x u))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member x u, member u x, neg (member x x), transitiveCode x p q]
  have ha : Context Γ (member x u) := .hypothesis (by simp [Γ])
  have hb : Context Γ (member u x) := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member x x)) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode x p q) := .hypothesis (by simp [Γ])
  have hself : Context Γ (member x x) :=
    .mp hb (.mp ha (.mp ht (.closed (transitive_instance x u p q hpx hpu hpq hqx hqu))))
  exact .mp hself hn

/-- Restricted successor injectivity is a literal K derivation. The explicit
transitivity and non-self-membership hypotheses are not asserted as K
axioms, and no zero uniqueness, closure, or induction follows. -/
def successor_injective_from_transitive (x u y v w p q : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    KDerivation (imp (transitiveCode x p q)
      (imp (neg (member x x)) (imp (successorCode x y w)
        (imp (successorCode u v w) (imp (equal y v) (equal x u)))))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [equal y v, successorCode u v w, successorCode x y w,
    neg (member x x), transitiveCode x p q]
  have he : Context Γ (equal y v) := .hypothesis (by simp [Γ])
  have hu : Context Γ (successorCode u v w) := .hypothesis (by simp [Γ])
  have hx : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hn : Context Γ (neg (member x x)) := .hypothesis (by simp [Γ])
  have ht : Context Γ (transitiveCode x p q) := .hypothesis (by simp [Γ])
  have hcycle : Context Γ (imp (member u x) (neg (member x u))) :=
    .mp hn (.mp ht (.closed (no_cycle_from_transitive x u p q hpx hpu hpq hqx hqu)))
  exact .mp hcycle (.mp he (.mp hu (.mp hx
    (.closed (successor_injective_from_no_cycle x u y v w hwx hwu hwy hwv)))))

theorem successor_injective_certificate (x u y v w p q : Nat)
    (hwx : w ≠ x) (hwu : w ≠ u) (hwy : w ≠ y) (hwv : w ≠ v)
    (hpx : p ≠ x) (hpu : p ≠ u) (hpq : p ≠ q)
    (hqx : q ≠ x) (hqu : q ≠ u) :
    theoremCode (certificate (successor_injective_from_transitive x u y v w p q
      hwx hwu hwy hwv hpx hpu hpq hqx hqu)) =
      imp (transitiveCode x p q)
        (imp (neg (member x x)) (imp (successorCode x y w)
          (imp (successorCode u v w) (imp (equal y v) (equal x u))))) :=
  certificate_correct (successor_injective_from_transitive x u y v w p q
    hwx hwu hwy hwv hpx hpu hpq hqx hqu)

/-- Every represented finite ordinal satisfies the transitivity condition in
the standard HF model. This separate semantic fact is not used to construct
any K derivation above. -/
theorem ordinal_transitive_true (x p q n : Nat) (ρ : Environment)
    (hxp : x ≠ p) (hxq : x ≠ q) (hpq : p ≠ q)
    (hx : ρ x = (HFCoding.ordinal n).code) :
    (decode (transitiveCode x p q)).Realize ρ := by
  simp only [transitiveCode, realize_all, realize_imp, realize_member]
  intro a b
  simp only [update_same, update_other _ q x _ hxq,
    update_other _ q p _ hpq, update_other ρ p x _ hxp]
  intro ha hb
  have ha' : (⟨a⟩ : HFCoding.Object) ∈ HFCoding.ordinal n := by
    change bit (HFCoding.ordinal n).code a = true
    simpa [hx] using ha
  obtain ⟨i, hi, hai⟩ := (HFCoding.mem_ordinal ⟨a⟩ n).mp ha'
  have hb' : (⟨b⟩ : HFCoding.Object) ∈ HFCoding.ordinal i := by
    have hcode : a = (HFCoding.ordinal i).code := congrArg HFCoding.Object.code hai
    change bit (HFCoding.ordinal i).code b = true
    simpa [hcode] using hb
  obtain ⟨j, hj, hbj⟩ := (HFCoding.mem_ordinal ⟨b⟩ i).mp hb'
  have hb'' : (⟨b⟩ : HFCoding.Object) ∈ HFCoding.ordinal n := by
    exact (HFCoding.mem_ordinal ⟨b⟩ n).mpr ⟨j, by omega, hbj⟩
  change bit (HFCoding.ordinal n).code b = true at hb''
  simpa only [hx] using hb''

/-- Irreflexivity holds in the standard code model for every represented
object, not merely for ordinals. This is not a K derivation. -/
theorem nonself_true (x : Nat) (ρ : Environment) :
    (decode (neg (member x x))).Realize ρ := by
  rw [realize_neg, realize_member]
  simp [bit_self_false]

end PASoundness.PAtoCompactTransitiveSuccessor
