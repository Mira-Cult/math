import PASoundness.PAtoCompactLeastSuccessorEmpty

/-! Existential packaging of the empty-intersection least-member case.
All filtering and greatest/least-domain hypotheses remain explicit. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorEmptyExists
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestSuccessorCase
open PASoundness.PAtoCompactLeastSuccessorCase PASoundness.PAtoCompactLeastSuccessorEmpty

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Package a displayed least member x using a fresh existential binder. -/
def least_member_exists_intro (u x z m : Nat)
    (hmx : m ≠ x) (hmu : m ≠ u) (hmz : m ≠ z) (hxz : x ≠ z) :
    KDerivation (imp (leastMemberCode u x z) (existsCode m (leastMemberCode u m z))) := by
  let f := namedLeastMember u m z
  have hi := exists_variable_intro m x f hmx
    (by simp [f, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.binders, hmz])
    (by simp [f, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.binders, hxz])
  simpa [f, namedLeastMember, namedBoth, namedEither, leastMemberCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hmx, hmu, hmz, hxz, Ne.symm hmx, Ne.symm hmu, Ne.symm hmz, Ne.symm hxz] using hi

/-- An inhabited u with empty u∩x has a least member when u⊆Succ(x).
The intersection graph is supplied, and existential witnesses are eliminated
inside the literal K derivation. -/
def empty_intersection_has_least (x y w u k c q a z v m : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,v,m].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (neg (nonemptyCode c a))
        (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z))))))) := by
  have hf : [x,y,w,u,k,c,q,a,z,v].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,u,k,c,q,a,z,v] [m]) fresh
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hmu : m ≠ u := by intro h; subst m; simp at fresh
  have hmz : m ≠ z := by intro h; subst m; simp at fresh
  have hxz : x ≠ z := by intro h; subst x; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvy : v ≠ y := by intro h; subst v; simp at fresh
  have hvw : v ≠ w := by intro h; subst v; simp at fresh
  have hvu : v ≠ u := by intro h; subst v; simp at fresh
  have hvk : v ≠ k := by intro h; subst v; simp at fresh
  have hvc : v ≠ c := by intro h; subst v; simp at fresh
  have hvq : v ≠ q := by intro h; subst v; simp at fresh
  have hva : v ≠ a := by intro h; subst v; simp at fresh
  have hvz : v ≠ z := by intro h; subst v; simp at fresh
  have hvm : v ≠ m := by intro h; subst v; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let N := neg (nonemptyCode c a)
  let H := existsCode m (leastMemberCode u m z)
  let Γ := [N,I,U,S]
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member u v) H) := by
    apply Context.deduction
    have hv : Context (member u v :: Γ) (member u v) := Context.head Γ _
    have hl : Context (member u v :: Γ) (leastMemberCode u x z) := .mp hv
      (.mp (Context.under hn _) (.mp (Context.under hi _) (.mp (Context.under hu _)
        (.mp (Context.under hs _) (.closed (empty_intersection_least x y w u k c q a z v hf))))))
    exact .mp hl (.closed (least_member_exists_intro u x z m hmx hmu hmz hxz))
  have hvars : ∀ h, h ∈ Γ → KDerivation (imp h (allCode v h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = N
    · subst h
      exact not_nonempty_vacuity c a v hvc hva
    · by_cases h2 : h = I
      · subst h
        exact intersection_vacuity u x c q v hvu hvx hvc hvq
      · by_cases h3 : h = U
        · subst h
          exact subset_vacuity u y k v hvu hvy hvk
        · have h4 : h = S := ((hh.resolve_left h1).resolve_left h2).resolve_left h3
          subst h
          exact successor_vacuity x y w v hvx hvy hvw
  have hall : Context Γ (allCode v (imp (member u v) H)) := Context.generalize v hvars hpoint
  let f : CompactNamed.Formula := .ex m (namedLeastMember u m z)
  have hfH : v ∉ f.names := by
    simp [f, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.names, hvu, hvm, hvz]
  have hvH : KDerivation (imp H (allCode v H)) := by
    simpa [f, H, namedLeastMember, namedBoth, namedEither, leastMemberCode,
      CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
      CompactDerivations.either] using f.vacuity v hfH
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Δ := [nonemptyCode u v,N,I,U,S]
  have hex : Context Δ (existsCode v (member u v)) := .hypothesis (by simp [Δ, nonemptyCode])
  exact Context.existsElim hvH (Context.under hall _) hex

theorem empty_intersection_has_least_certificate (x y w u k c q a z v m : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,v,m].Nodup) :
    theoremCode (certificate (empty_intersection_has_least x y w u k c q a z v m fresh)) =
      imp (successorCode x y w) (imp (subsetCode u y k)
        (imp (intersectionGraph u x c q) (imp (neg (nonemptyCode c a))
          (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m z)))))) :=
  certificate_correct (empty_intersection_has_least x y w u k c q a z v m fresh)

end PASoundness.PAtoCompactLeastSuccessorEmptyExists

#print axioms PASoundness.PAtoCompactLeastSuccessorEmptyExists.empty_intersection_has_least
#print axioms PASoundness.PAtoCompactLeastSuccessorEmptyExists.empty_intersection_has_least_certificate
