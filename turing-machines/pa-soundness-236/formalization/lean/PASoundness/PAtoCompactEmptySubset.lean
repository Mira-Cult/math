import PASoundness.PAtoCompactGreatestDownward

/-! In K, a represented subset of a zero-graph object cannot be nonempty.
The derivation is syntactic and does not use semantic soundness. Literal code 1
is self-membership, so the ordinary negation reading is model dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactEmptySubset
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactZeroTransitive
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactGreatestDownward
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- For pairwise-fresh labels, a subset of an explicit zero object has no
member. This proves the encoded implication, not existence or uniqueness of
zero objects and not a complete arithmetic-domain interpretation. -/
def empty_subset_nonempty_impossible (x z u k a : Nat)
    (fresh : [x,z,u,k,a].Nodup) :
    KDerivation (imp (zeroCode x z)
      (imp (subsetCode u x k) (neg (nonemptyCode u a)))) := by
  have hza : z ≠ a := by intro h; subst z; simp at fresh
  have hzx : z ≠ x := by intro h; subst z; simp at fresh
  have hka : k ≠ a := by intro h; subst k; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hax : a ≠ x := by intro h; subst a; simp at fresh
  have haz : a ≠ z := by intro h; subst a; simp at fresh
  have hau : a ≠ u := by intro h; subst a; simp at fresh
  have hak : a ≠ k := by intro h; subst a; simp at fresh
  let Z := zeroCode x z
  let S := subsetCode u x k
  let Γ := [S,Z]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hno : Context Γ (neg (member u a)) := by
    apply Context.deduction
    have hm : Context (member u a :: Γ) (member u a) := Context.head Γ _
    have hmx : Context (member u a :: Γ) (member x a) :=
      .mp hm (.mp (Context.under hs _) (.closed (subset_instance u x k a hka hku hkx)))
    have hnx : Context (member u a :: Γ) (neg (member x a)) :=
      .mp (Context.under hz _) (.closed (zero_excludes x z a hza hzx))
    exact .mp hmx hnx
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode a h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = S
    · subst h
      exact subset_vacuity u x k a hau hax hak
    · have he' : h = Z := hh.resolve_left he
      subst h
      exact zero_graph_vacuity x z a hax haz
  have hall : Context Γ (allCode a (neg (member u a))) := Context.generalize a hv hno
  have hnot : Context Γ (neg (nonemptyCode u a)) := by
    simpa [nonemptyCode, existsCode, zeroCode] using
      (Context.mp hall (.closed (doubleNegIntro (allCode a (neg (member u a))))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hnot

theorem empty_subset_nonempty_impossible_certificate (x z u k a : Nat)
    (fresh : [x,z,u,k,a].Nodup) :
    theoremCode (certificate (empty_subset_nonempty_impossible x z u k a fresh)) =
      imp (zeroCode x z) (imp (subsetCode u x k) (neg (nonemptyCode u a))) :=
  certificate_correct (empty_subset_nonempty_impossible x z u k a fresh)

end PASoundness.PAtoCompactEmptySubset

#print axioms PASoundness.PAtoCompactEmptySubset.empty_subset_nonempty_impossible
#print axioms PASoundness.PAtoCompactEmptySubset.empty_subset_nonempty_impossible_certificate
