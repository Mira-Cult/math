import PASoundness.PAtoCompactLeastCounterexample
import PASoundness.PAtoCompactEmptySubset

/-! Syntactic construction of vacuous least/greatest subset conditions from
an empty-object premise. Code 1 is literally self-membership; no appeal to its
truth or falsity in an arbitrary model is made. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEmptyExtrema
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactEmptySubset
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A zero-code assumption is vacuous at a name distinct from its object and
its own test binder. -/
def zero_vacuity (x z u : Nat) (hux : u ≠ x) (huz : u ≠ z) :
    KDerivation (imp (zeroCode x z) (allCode u (zeroCode x z))) := by
  let f : CompactNamed.Formula := .all z (.imp (.member x z) .bottom)
  have hn : u ∉ f.names := by simp [f, CompactNamed.Formula.names, hux, huz]
  have h := f.vacuity u hn
  simpa [f, zeroCode, neg, CompactNamed.Formula.encode] using h

/-- If K rules out a nonempty represented subset of x, then it proves every
such subset has an arbitrary displayed property; the quantified subset name
is fresh for the zero assumption. -/
def vacuous_subset_family (x z u k a R : Nat) (hux : u ≠ x) (huz : u ≠ z)
    (emptySubset : KDerivation (imp (zeroCode x z)
      (imp (subsetCode u x k) (neg (nonemptyCode u a))))) :
    KDerivation (imp (zeroCode x z)
      (allCode u (imp (subsetCode u x k) (imp (nonemptyCode u a) R)))) := by
  let Z := zeroCode x z
  let S := subsetCode u x k
  let N := nonemptyCode u a
  let Γ := [Z]
  have hp : Context Γ (imp S (imp N R)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [N,S,Z]
    have hz : Context Δ Z := .hypothesis (by simp [Δ])
    have hs : Context Δ S := .hypothesis (by simp [Δ])
    have hn : Context Δ N := Context.head [S,Z] N
    have hnot : Context Δ (neg N) := .mp hs (.mp hz (.closed emptySubset))
    exact Context.explode R (.mp hn hnot)
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode u h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity x z u hux huz
  apply Context.closeEmpty
  apply Context.deduction
  exact Context.generalize u hv hp

/-- From a zero-graph hypothesis, K derives both explicit represented-subset
extrema conditions. All binder and object labels are pairwise distinct. -/
def zero_has_subset_extrema (x z u k a m r : Nat)
    (fresh : [x,z,u,k,a,m,r].Nodup) :
    KDerivation (imp (zeroCode x z)
      (both (leastSubsetsCode x u k a m r) (greatestSubsetsCode x u k m r))) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huz : u ≠ z := by intro h; subst u; simp at fresh
  have hleastFresh : [x,z,u,k,a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  have hgreatFresh : [x,z,u,k,m].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, not_false_eq_true] at fresh ⊢
    tauto
  have hl : KDerivation (imp (zeroCode x z) (leastSubsetsCode x u k a m r)) := by
    exact vacuous_subset_family x z u k a (existsCode m (leastMemberCode u m r))
      hux huz (empty_subset_nonempty_impossible x z u k a hleastFresh)
  have hg : KDerivation (imp (zeroCode x z) (greatestSubsetsCode x u k m r)) := by
    exact vacuous_subset_family x z u k m (hasGreatestCode u m r)
      hux huz (empty_subset_nonempty_impossible x z u k m hgreatFresh)
  apply Context.closeEmpty
  apply Context.deduction
  have hz : Context [zeroCode x z] (zeroCode x z) := Context.head [] _
  exact Context.conjunctionIntro (.mp hz (.closed hl)) (.mp hz (.closed hg))

theorem zero_has_subset_extrema_certificate (x z u k a m r : Nat)
    (fresh : [x,z,u,k,a,m,r].Nodup) :
    theoremCode (certificate (zero_has_subset_extrema x z u k a m r fresh)) =
      imp (zeroCode x z)
        (both (leastSubsetsCode x u k a m r) (greatestSubsetsCode x u k m r)) :=
  certificate_correct (zero_has_subset_extrema x z u k a m r fresh)

end PASoundness.PAtoCompactEmptyExtrema

#print axioms PASoundness.PAtoCompactEmptyExtrema.vacuous_subset_family
#print axioms PASoundness.PAtoCompactEmptyExtrema.zero_has_subset_extrema
#print axioms PASoundness.PAtoCompactEmptyExtrema.zero_has_subset_extrema_certificate
