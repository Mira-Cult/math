import PASoundness.PAtoCompactPredecessor
import PASoundness.PAtoCompactUniformStep

/-! Conditional syntactic classification of one represented transitive
object. The greatest-subset property is a premise, not a theorem. Compact
code 1 is literally `member 0 0`; ordinary falsity is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactClassification
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveWitness
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactUniformStep

/-- Literal encodings make failure of nonemptiness the double negation of
the corresponding zero graph, with the same test/bound name. -/
def not_nonempty_implies_zero (x m : Nat) :
    KDerivation (imp (neg (nonemptyCode x m)) (zeroCode x m)) := by
  exact doubleNegElim (zeroCode x m)

/-- A transitive input can be retained inside an existential predecessor
witness. The predecessor binder m is fresh for the input transitivity code. -/
def predecessor_add_transitivity (x p q m r : Nat)
    (hmx : m ≠ x) (hmp : m ≠ p) (hmq : m ≠ q) :
    KDerivation (imp (transitiveCode x p q)
      (imp (existsCode m (both (member x m) (successorCode m x r)))
        (existsCode m (both (member x m)
          (both (successorCode m x r) (transitiveCode x p q)))))) := by
  let T := transitiveCode x p q
  let A := both (member x m) (successorCode m x r)
  let B := both (member x m) (both (successorCode m x r) T)
  let Γ := [T]
  have ht : Context Γ T := Context.head [] T
  have hpoint : Context Γ (imp A B) := by
    apply Context.deduction
    have ha : Context (A :: Γ) A := Context.head Γ A
    exact Context.conjunctionIntro (Context.conjunctionLeft ha)
      (Context.conjunctionIntro (Context.conjunctionRight ha) (Context.under ht A))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    have he : h = T := by simpa [Γ] using hh
    subst h
    exact transitive_vacuity x p q m hmx hmp hmq
  have hall : Context Γ (allCode m (imp A B)) := Context.generalize m hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  have hex : Context (existsCode m A :: Γ) (existsCode m A) := Context.head Γ _
  exact exists_map_context (Context.under hall (existsCode m A)) hex

/-- A transitive represented object whose every nonempty represented subset
has a greatest member is zero or has an in-object successor predecessor. The
predecessor branch retains the transitivity premise. This is conditional; no
least-subset principle, induction, uniqueness or PA domain is asserted. -/
def transitive_zero_or_predecessor (x p q u k m t r : Nat)
    (fresh : [x,p,q,u,k,m,t,r].Nodup) :
    KDerivation (imp (transitiveCode x p q) (imp (greatestSubsetsCode x u k m t)
      (zeroOrPredecessorCore x m x m r p q))) := by
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hmp : m ≠ p := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  let T := transitiveCode x p q
  let H := greatestSubsetsCode x u k m t
  let N := nonemptyCode x m
  let Z := zeroCode x m
  let E := existsCode m (both (member x m) (successorCode m x r))
  let E' := existsCode m (both (member x m) (both (successorCode m x r) T))
  have excluded : KDerivation (either N (neg N)) := CompactHilbertBasis.identity (neg N)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [H,T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hh : Context Γ H := .hypothesis (by simp [Γ])
  apply Context.disjunctionElim (Context.closed excluded : Context Γ (either N (neg N)))
  · have hn : Context (N :: Γ) N := Context.head Γ N
    have hp : Context (N :: Γ) E := .mp (Context.under hh N)
      (.mp hn (.mp (Context.under ht N) (.closed (predecessor_from_greatest_subsets x p q u k m t r fresh))))
    have hp' : Context (N :: Γ) E' := .mp hp (.mp (Context.under ht N)
      (.closed (predecessor_add_transitivity x p q m r hmx hmp hmq)))
    exact Context.disjunctionRight (a := Z) hp'
  · have hn : Context (neg N :: Γ) (neg N) := Context.head Γ (neg N)
    have hz : Context (neg N :: Γ) Z := .mp hn (.closed (not_nonempty_implies_zero x m))
    exact Context.disjunctionLeft (b := E') hz

theorem transitive_zero_or_predecessor_certificate (x p q u k m t r : Nat)
    (fresh : [x,p,q,u,k,m,t,r].Nodup) :
    theoremCode (certificate (transitive_zero_or_predecessor x p q u k m t r fresh)) =
      imp (transitiveCode x p q) (imp (greatestSubsetsCode x u k m t)
        (zeroOrPredecessorCore x m x m r p q)) :=
  certificate_correct (transitive_zero_or_predecessor x p q u k m t r fresh)

end PASoundness.PAtoCompactClassification
