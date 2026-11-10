import PASoundness.PAtoCompactLeastSuccessorCase
import PASoundness.PAtoCompactGreatestDownward

/-! Existential packaging of the nonempty-intersection successor case. The
least-subset condition and exact intersection graph remain explicit hypotheses;
no full domain or arithmetic interpretation is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorNonempty
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactLeastSuccessorCase PASoundness.PAtoCompactGreatestSuccessorCase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- The exact intersection graph makes c a subset of x. -/
def intersection_subset_right (u x c q : Nat) :
    KDerivation (imp (intersectionGraph u x c q) (subsetCode c x q)) := by
  let A := member c q
  let B := both (member u q) (member x q)
  let J := both (imp A B) (imp B A)
  have hp : KDerivation (imp J (imp A (member x q))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    have ha : Context [A,J] A := Context.head [J] A
    have hj : Context [A,J] J := Context.under (Context.head [] J) A
    exact Context.conjunctionRight (.mp ha (Context.conjunctionLeft hj))
  exact allCongr q hp

/-- When the represented intersection is nonempty, the least-subset property
of x provides a least member of u⊆Succ(x). The intersection graph remains
an explicit premise and the least witness is transported under one binder. -/
def nonempty_intersection_has_least (x y w u k c q a z m r b : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (leastSubsetsCode x b k a m r)
        (imp (nonemptyCode c a) (existsCode m (leastMemberCode u m z))))))) := by
  have hcase : [x,y,w,u,k,c,q,m,r,z].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hbx : b ≠ x := by intro h; subst b; simp at fresh
  have hbc : b ≠ c := by intro h; subst b; simp at fresh
  have hbk : b ≠ k := by intro h; subst b; simp at fresh
  have hba : b ≠ a := by intro h; subst b; simp at fresh
  have hbm : b ≠ m := by intro h; subst b; simp at fresh
  have hbr : b ≠ r := by intro h; subst b; simp at fresh
  have hck : c ≠ k := by intro h; subst c; simp at fresh
  have hca : c ≠ a := by intro h; subst c; simp at fresh
  have hcm : c ≠ m := by intro h; subst c; simp at fresh
  have hcr : c ≠ r := by intro h; subst c; simp at fresh
  have hqk : q ≠ k := by intro h; subst q; simp at fresh
  have hqc : q ≠ c := by intro h; subst q; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hkc : k ≠ c := by intro h; subst k; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hmy : m ≠ y := by intro h; subst m; simp at fresh
  have hmw : m ≠ w := by intro h; subst m; simp at fresh
  have hmu : m ≠ u := by intro h; subst m; simp at fresh
  have hmk : m ≠ k := by intro h; subst m; simp at fresh
  have hmc : m ≠ c := by intro h; subst m; simp at fresh
  have hmq : m ≠ q := by intro h; subst m; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let L := leastSubsetsCode x b k a m r
  let N := nonemptyCode c a
  let Γ := [I,U,S]
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (leastMemberCode c m r) (leastMemberCode u m z)) :=
    .mp hi (.mp hu (.mp hs (.closed (least_intersection_preserved x y w u k c q m r z hcase))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode m h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = I
    · subst h
      exact intersection_vacuity u x c q m hmu hmx hmc hmq
    · by_cases h2 : h = U
      · subst h
        exact subset_vacuity u y k m hmu hmy hmk
      · have h3 : h = S := (hh.resolve_left h1).resolve_left h2
        subst h
        exact successor_vacuity x y w m hmx hmy hmw
  have hall : Context Γ (allCode m (imp (leastMemberCode c m r) (leastMemberCode u m z))) :=
    Context.generalize m hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [N,L,I,U,S]
  have hn : Context Δ N := .hypothesis (by simp [Δ])
  have hl : Context Δ L := .hypothesis (by simp [Δ])
  have hi' : Context Δ I := .hypothesis (by simp [Δ])
  have hcq : Context Δ (subsetCode c x q) := .mp hi' (.closed (intersection_subset_right u x c q))
  have hck' : Context Δ (subsetCode c x k) := .mp hcq
    (.closed (PAtoCompactGreatestDownward.subset_rename c x q k hqk hqc hqx hkc hkx))
  have hex : Context Δ (existsCode m (leastMemberCode c m r)) := .mp hn (.mp hck' (.mp hl
    (.closed (least_subsets_instance x b k a m r c hbx hbc hbk hba hbm hbr hck hca hcm hcr))))
  have hall' : Context Δ (allCode m (imp (leastMemberCode c m r) (leastMemberCode u m z))) :=
    Context.weaken hall (by intro h hh; simp only [Γ, Δ, List.mem_cons, List.not_mem_nil, or_false] at hh ⊢; tauto)
  exact exists_map_context hall' hex

theorem nonempty_intersection_has_least_certificate (x y w u k c q a z m r b : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,m,r,b].Nodup) :
    theoremCode (certificate (nonempty_intersection_has_least x y w u k c q a z m r b fresh)) =
      imp (successorCode x y w) (imp (subsetCode u y k)
        (imp (intersectionGraph u x c q) (imp (leastSubsetsCode x b k a m r)
          (imp (nonemptyCode c a) (existsCode m (leastMemberCode u m z)))))) :=
  certificate_correct (nonempty_intersection_has_least x y w u k c q a z m r b fresh)

end PASoundness.PAtoCompactLeastSuccessorNonempty

#print axioms PASoundness.PAtoCompactLeastSuccessorNonempty.nonempty_intersection_has_least
#print axioms PASoundness.PAtoCompactLeastSuccessorNonempty.nonempty_intersection_has_least_certificate
