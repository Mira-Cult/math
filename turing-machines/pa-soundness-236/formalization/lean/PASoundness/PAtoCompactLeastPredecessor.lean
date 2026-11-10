import PASoundness.PAtoCompactLeastCounterexample
import PASoundness.PAtoCompactTransitiveClosure

/-! A conditional K least-counterexample predecessor contradiction.
Code 1 is literally `member 0 0`; no global induction or domain is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastPredecessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactCounterexampleSet
open PASoundness.PAtoCompactLeastCounterexample

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Instantiate the order clause of the least-member code at y. -/
def least_member_at (c m r y : Nat) (hrc : r ≠ c) (hrm : r ≠ m) (hry : r ≠ y) :
    KDerivation (imp (leastMemberCode c m r)
      (imp (member c y) (either (equal y m) (member y m)))) := by
  let f : CompactNamed.Formula :=
    .imp (.member c r) (namedEither (.equal r m) (.member r m))
  have hi := CompactNamed.universalInstance r y f hry
    (by simp [f, namedEither, CompactNamed.Formula.binders])
    (by simp [f, namedEither, CompactNamed.Formula.binders])
  have hi' : KDerivation (imp
      (allCode r (imp (member c r) (either (equal r m) (member r m))))
      (imp (member c y) (either (equal y m) (member y m)))) := by
    simpa [f, namedEither, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.neg, CompactDerivations.either,
      hrc, hrm, hry, Ne.symm hrc, Ne.symm hrm, Ne.symm hry] using hi
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp (Context.conjunctionRight (Context.head [] (leastMemberCode c m r))) (.closed hi')

/-- At exposed names, a least filtered counterexample m contradicts successor
preservation when y is an in-domain predecessor with the separately supplied
properness implication `m∈y → code 1`. The preservation premise is the
object-level K code `f(y) → f(m)`. This proof returns literal code 1, not an
unqualified semantic falsity in arbitrary raw models. -/
def least_predecessor_contradiction (x t y m r w : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (member x y) (imp (successorCode y m w) (imp (neg (member y m))
        (imp (imp fy fm) 1)))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fy := (CompactNamed.replace t y f).encode
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let X := member x y
  let S := successorCode y m w
  let Q := neg (member y m)
  let H := imp fy fm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,Q,S,X,L,G]
  have hG : Context Γ G := .hypothesis (by simp [Γ])
  have hL : Context Γ L := .hypothesis (by simp [Γ])
  have hX : Context Γ X := .hypothesis (by simp [Γ])
  have hS : Context Γ S := .hypothesis (by simp [Γ])
  have hQ : Context Γ Q := .hypothesis (by simp [Γ])
  have hH : Context Γ H := .hypothesis (by simp [Γ])
  have hmy : Context Γ (member m y) := .mp hS (.closed (successor_contains_input y m w hwy hwm))
  have horder : Context Γ (imp (member c y) (either (equal y m) (member y m))) :=
    .mp hL (.closed (least_member_at c m r y hrc hrm hry))
  have hnotMember : Context Γ (neg (member c y)) := by
    apply Context.deduction
    have hy : Context (member c y :: Γ) (member c y) := Context.head Γ _
    have hcase := Context.mp hy (Context.under horder (member c y))
    apply Context.disjunctionElim hcase
    · have he : Context (equal y m :: member c y :: Γ) (equal y m) := Context.head _ _
      have hmy' : Context (equal y m :: member c y :: Γ) (member m y) :=
        Context.under (Context.under hmy (member c y)) (equal y m)
      have hself : Context (equal y m :: member c y :: Γ) (member m m) :=
        .mp he (.mp hmy' (.closed (memberRightEquality m y m)))
      exact .mp hself (.closed (self_membership_implies_code_one m))
    · have hb : Context (member y m :: member c y :: Γ) (member y m) := Context.head _ _
      exact .mp hb (Context.under (Context.under hQ (member c y)) (member y m))
  have hgy := Context.mp hG (.closed (counterexample_graph_at x t y f hxt hty htf hyf))
  have hgm := Context.mp hG (.closed (counterexample_graph_at x t m f hxt htm htf hmf))
  have hmm : Context Γ (member c m) := Context.conjunctionLeft hL
  have hnotM : Context Γ (neg fm) := Context.conjunctionRight (.mp hmm (Context.conjunctionLeft hgm))
  have hytrue : Context Γ fy := by
    apply Context.dne
    apply Context.deduction
    have hyfalse : Context (neg fy :: Γ) (neg fy) := Context.head Γ _
    have hx' : Context (neg fy :: Γ) X := Context.under hX (neg fy)
    have htest := Context.conjunctionIntro hx' hyfalse
    have hback := Context.under (Context.conjunctionRight hgy) (neg fy)
    have hyMem : Context (neg fy :: Γ) (member c y) := .mp htest hback
    exact .mp hyMem (Context.under hnotMember (neg fy))
  exact .mp (.mp hytrue hH) hnotM

theorem least_predecessor_certificate (x t y m r w : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (least_predecessor_contradiction x t y m r w f hxt hty htm
      htf hyf hmf hrc hrm hry hwy hwm)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (member x y) (imp (successorCode y m w) (imp (neg (member y m))
          (imp (imp fy fm) 1))))) :=
  certificate_correct (least_predecessor_contradiction x t y m r w f hxt hty htm
    htf hyf hmf hrc hrm hry hwy hwm)

/-- A transitive successor output m supplies the explicit properness
implication needed above. The derivation uses only literal K proof data; code
1 remains the displayed `member 0 0` formula. -/
def predecessor_proper_on_transitive (y m w p q : Nat)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q)
    (hqm : q ≠ m) (hqy : q ≠ y) :
    KDerivation (imp (transitiveCode m p q) (imp (successorCode y m w) (neg (member y m)))) := by
  let T := transitiveCode m p q
  let S := successorCode y m w
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member y m, S, T]
  have hb : Context Γ (member y m) := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hmember : Context Γ (member m y) := .mp hs (.closed (successor_contains_input y m w hwy hwm))
  have hno : Context Γ (imp (member y m) (neg (member m y))) :=
    .mp (.closed (self_membership_implies_code_one m))
      (.mp ht (.closed (no_cycle_from_transitive m y p q hpm hpy hpq hqm hqy)))
  exact .mp hmember (.mp hb hno)

/-- Fully explicit local induction step using transitivity of the least
counterexample to discharge predecessor properness. A witness for the zero
case, global closure/induction, and uniqueness are separate obligations. -/
def least_predecessor_contradiction_transitive (x t y m r w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    KDerivation (imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
      (imp (member x y) (imp (successorCode y m w) (imp (transitiveCode m p q)
        (imp (imp fy fm) 1)))))) := by
  dsimp only
  let c := filterPredicate x t (neg f.encode)
  let fy := (CompactNamed.replace t y f).encode
  let fm := (CompactNamed.replace t m f).encode
  let G := filterGraph x c t (neg f.encode)
  let L := leastMemberCode c m r
  let X := member x y
  let S := successorCode y m w
  let T := transitiveCode m p q
  let H := imp fy fm
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,T,S,X,L,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hx : Context Γ X := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  have hp : Context Γ (neg (member y m)) := .mp hs (.mp ht
    (.closed (predecessor_proper_on_transitive y m w p q hwy hwm hpm hpy hpq hqm hqy)))
  exact .mp hh (.mp hp (.mp hs (.mp hx (.mp hl (.mp hg
    (.closed (least_predecessor_contradiction x t y m r w f hxt hty htm htf hyf hmf hrc hrm hry hwy hwm)))))))

theorem least_predecessor_transitive_certificate (x t y m r w p q : Nat) (f : CompactNamed.Formula)
    (hxt : x ≠ t) (hty : t ≠ y) (htm : t ≠ m)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (hrc : r ≠ filterPredicate x t (neg f.encode)) (hrm : r ≠ m) (hry : r ≠ y)
    (hwy : w ≠ y) (hwm : w ≠ m)
    (hpm : p ≠ m) (hpy : p ≠ y) (hpq : p ≠ q) (hqm : q ≠ m) (hqy : q ≠ y) :
    let c := filterPredicate x t (neg f.encode)
    let fy := (CompactNamed.replace t y f).encode
    let fm := (CompactNamed.replace t m f).encode
    theoremCode (certificate (least_predecessor_contradiction_transitive x t y m r w p q f
      hxt hty htm htf hyf hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)) =
      imp (filterGraph x c t (neg f.encode)) (imp (leastMemberCode c m r)
        (imp (member x y) (imp (successorCode y m w) (imp (transitiveCode m p q)
          (imp (imp fy fm) 1))))) :=
  certificate_correct (least_predecessor_contradiction_transitive x t y m r w p q f
    hxt hty htm htf hyf hmf hrc hrm hry hwy hwm hpm hpy hpq hqm hqy)

/-- The local step code means preservation from y to m in the standard HF
interpretation. This semantic correspondence is separate from the K proof. -/
theorem local_step_standard (t y m : Nat) (f : CompactNamed.Formula)
    (htf : t ∉ f.binders) (hyf : y ∉ f.binders) (hmf : m ∉ f.binders)
    (ρ : CompactMatrix.Environment) :
    (CompactMatrix.decode (imp (CompactNamed.replace t y f).encode
      (CompactNamed.replace t m f).encode)).Realize ρ ↔
      (f.Realize (CompactMatrix.update ρ t (ρ y)) →
        f.Realize (CompactMatrix.update ρ t (ρ m))) := by
  rw [CompactSemantics.realize_imp, CompactNamed.Formula.encode_realize,
    CompactNamed.Formula.encode_realize, CompactNamed.replace_realize t y f htf hyf ρ,
    CompactNamed.replace_realize t m f htf hmf ρ]

/-- Successor properness holds in standard HF semantics, independently of the
restricted K derivation above. -/
theorem standard_successor_proper (y m w : Nat) (ρ : CompactMatrix.Environment)
    (hyw : y ≠ w) (hmw : m ≠ w)
    (hs : (CompactMatrix.decode (successorCode y m w)).Realize ρ) :
    (CompactMatrix.decode (neg (member y m))).Realize ρ := by
  rw [CompactSemantics.realize_neg, CompactSemantics.realize_member]
  intro hmy
  have hlower := CompactSemantics.member_lt (ρ y) (ρ m) hmy
  have he := (successorCode_realize y m w ρ hyw hmw).mp hs
  have hin : (⟨ρ y⟩ : HFCoding.Object) ∈ HFCoding.successor ⟨ρ y⟩ := by
    rw [HFCoding.mem_successor]
    exact Or.inl rfl
  have hupper := HFCoding.member_code_lt hin
  simp only at hupper
  omega

end PASoundness.PAtoCompactLeastPredecessor
