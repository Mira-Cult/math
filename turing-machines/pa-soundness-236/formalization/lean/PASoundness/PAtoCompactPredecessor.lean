import PASoundness.PAtoCompactGreatestSuccessor
import PASoundness.PAtoCompactTransitiveWitness

/-! A conditional K predecessor witness under an explicit greatest-subset
hypothesis. Compact negation and existential/conjunction encodings use code 1,
which is literally `member 0 0`; their ordinary set-theoretic reading needs
an interpretation where that code is false under the relevant assignments.
No induction or uniqueness is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactPredecessor
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactGreatestSuccessor

def subsetCode (u x k : Nat) : Nat := allCode k (imp (member u k) (member x k))
def nonemptyCode (u m : Nat) : Nat := existsCode m (member u m)
def hasGreatestCode (u m t : Nat) : Nat :=
  existsCode m (both (member u m) (greatestCode u m t))

/-- Every represented subset u of x with an element has a greatest member.
The hypothesis quantifies over the full represented K universe, not a claimed
ordinal domain; no theorem here asserts that this property holds. -/
def greatestSubsetsCode (x u k m t : Nat) : Nat :=
  allCode u (imp (subsetCode u x k) (imp (nonemptyCode u m) (hasGreatestCode u m t)))

def namedGreatestSubsetsBody (x u k m t : Nat) : CompactNamed.Formula :=
  .imp (.all k (.imp (.member u k) (.member x k)))
    (.imp (.ex m (.member u m))
      (.ex m (namedBoth (.member u m) (.all t (namedGreatestBody u m t)))))

/-- Instantiate the greatest-subset hypothesis at the set x itself. -/
def greatest_subsets_self (x u k m t : Nat)
    (hux : u ≠ x) (huk : u ≠ k) (hum : u ≠ m) (hut : u ≠ t)
    (hxk : x ≠ k) (hxm : x ≠ m) (hxt : x ≠ t) :
    KDerivation (imp (greatestSubsetsCode x u k m t)
      (imp (nonemptyCode x m) (hasGreatestCode x m t))) := by
  let f := namedGreatestSubsetsBody x u k m t
  have hi := CompactNamed.universalInstance u x f hux
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.binders, huk, hum, hut])
    (by simp [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      CompactNamed.Formula.binders, hxk, hxm, hxt])
  have hi' : KDerivation (imp (greatestSubsetsCode x u k m t)
      (imp (subsetCode x x k) (imp (nonemptyCode x m) (hasGreatestCode x m t)))) := by
    simpa [f, namedGreatestSubsetsBody, namedBoth, namedGreatestBody, namedEither,
      greatestSubsetsCode, subsetCode, nonemptyCode, hasGreatestCode, greatestCode,
      CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hux, huk, hum, hut, hxk, hxm, hxt, Ne.symm hux, Ne.symm huk,
      Ne.symm hum, Ne.symm hut, Ne.symm hxk, Ne.symm hxm, Ne.symm hxt] using hi
  have href : KDerivation (subsetCode x x k) := .generalize k (CompactHilbertBasis.identity _)
  apply Context.closeEmpty
  apply Context.deduction
  exact .mp (.closed href) (.mp (Context.head [] (greatestSubsetsCode x u k m t)) (.closed hi'))

/-- Given transitivity, nonemptiness, and the hypothesis that every represented
nonempty subset has a greatest member, x has a successor predecessor. All
syntax names are pairwise distinct; the conclusion makes no uniqueness or
induction claim. -/
def predecessor_from_greatest_subsets (x p q u k m t r : Nat)
    (fresh : [x,p,q,u,k,m,t,r].Nodup) :
    KDerivation (imp (transitiveCode x p q)
      (imp (nonemptyCode x m) (imp (greatestSubsetsCode x u k m t)
        (existsCode m (both (member x m) (successorCode m x r)))))) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hxk : x ≠ k := by intro h; subst k; simp at fresh
  have hxm : x ≠ m := by intro h; subst m; simp at fresh
  have hxt : x ≠ t := by intro h; subst t; simp at fresh
  have hpx : p ≠ x := by intro h; subst p; simp at fresh
  have hpm : p ≠ m := by intro h; subst p; simp at fresh
  have hpq : p ≠ q := by intro h; subst p; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  have hqr : q ≠ r := by intro h; subst q; simp at fresh
  have htx : t ≠ x := by intro h; subst t; simp at fresh
  have htm : t ≠ m := by intro h; subst t; simp at fresh
  have htr : t ≠ r := by intro h; subst t; simp at fresh
  have hrx : r ≠ x := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hrp : r ≠ p := by intro h; subst r; simp at fresh
  have hrq : r ≠ q := by intro h; subst r; simp at fresh
  have hrt : r ≠ t := by intro h; subst r; simp at fresh
  let T := transitiveCode x p q
  let A := both (member x m) (greatestCode x m t)
  let B := both (member x m) (successorCode m x r)
  let Γ := [T]
  have ht : Context Γ T := Context.head [] T
  have himp : Context Γ (imp A B) := by
    apply Context.deduction
    have ha : Context (A :: Γ) A := Context.head Γ A
    have hm : Context (A :: Γ) (member x m) := Context.conjunctionLeft ha
    have hg : Context (A :: Γ) (greatestCode x m t) := Context.conjunctionRight ha
    have ht' : Context (A :: Γ) T := Context.under ht A
    have hs : Context (A :: Γ) (successorCode m x r) :=
      .mp hg (.mp hm (.mp ht' (.closed (greatest_member_successor x m p q t r
        hpx hpm hpq hqx hqm hqr htx htm htr hrx hrm hrp hrq hrt))))
    exact Context.conjunctionIntro hm hs
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    exact transitive_vacuity x p q m (Ne.symm hxm) (Ne.symm hpm) (Ne.symm hqm)
  have hall : Context Γ (allCode m (imp A B)) := Context.generalize m hv himp
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [greatestSubsetsCode x u k m t, nonemptyCode x m, T]
  have hf : Context Δ (greatestSubsetsCode x u k m t) := .hypothesis (by simp [Δ])
  have hn : Context Δ (nonemptyCode x m) := .hypothesis (by simp [Δ])
  have hw : Context Δ (hasGreatestCode x m t) :=
    .mp hn (.mp hf (.closed (greatest_subsets_self x u k m t hux huk hum hut hxk hxm hxt)))
  have hall' : Context Δ (allCode m (imp A B)) := Context.weaken hall (by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    simp [Δ])
  exact exists_map_context hall' hw

theorem predecessor_from_greatest_subsets_certificate (x p q u k m t r : Nat)
    (fresh : [x,p,q,u,k,m,t,r].Nodup) :
    theoremCode (certificate (predecessor_from_greatest_subsets x p q u k m t r fresh)) =
      imp (transitiveCode x p q)
        (imp (nonemptyCode x m) (imp (greatestSubsetsCode x u k m t)
          (existsCode m (both (member x m) (successorCode m x r))))) :=
  certificate_correct (predecessor_from_greatest_subsets x p q u k m t r fresh)

end PASoundness.PAtoCompactPredecessor
