import PASoundness.PAtoCompactLeastPredecessor
import PASoundness.PAtoCompactGreatestSuccessorCase

/-! A bounded least-subset successor step: a least member of a represented
intersection stays least when the successor's new top is added. The filter
graph is an explicit hypothesis; no domain closure or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactFilteredSubset PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactLeastPredecessor PASoundness.PAtoCompactGreatestSuccessorCase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- A represented intersection's exact membership graph, with test binder q. -/
def intersectionGraph (u x c q : Nat) : Nat := filterGraph u c q (member x q)

def namedIntersectionBody (u x c q : Nat) : CompactNamed.Formula :=
  let p := namedBoth (.member u q) (.member x q)
  namedBoth (.imp (.member c q) p) (.imp p (.member c q))

/-- Instantiate the intersection graph at a fresh named element. -/
def intersection_instance (u x c q z : Nat)
    (hqu : q ≠ u) (hqx : q ≠ x) (hqc : q ≠ c) (hqz : q ≠ z) :
    KDerivation (imp (intersectionGraph u x c q)
      (both (imp (member c z) (both (member u z) (member x z)))
        (imp (both (member u z) (member x z)) (member c z)))) := by
  let f := namedIntersectionBody u x c q
  have hi := CompactNamed.universalInstance q z f hqz
    (by simp [f, namedIntersectionBody, namedBoth, CompactNamed.Formula.binders])
    (by simp [f, namedIntersectionBody, namedBoth, CompactNamed.Formula.binders])
  simpa [f, namedIntersectionBody, intersectionGraph, filterGraph, filterPredicate, namedBoth,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, hqu, hqx, hqc, hqz,
    Ne.symm hqu, Ne.symm hqx, Ne.symm hqc, Ne.symm hqz] using hi

/-- Pointwise preservation: if m is least in the displayed intersection, it
is below every element z of u when u is contained in x's successor. -/
def least_intersection_point (x y w u k c q m r z : Nat)
    (fresh : [x,y,w,u,k,c,q,m,r,z].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (leastMemberCode c m r)
        (imp (member u z) (either (equal z m) (member z m))))))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hwz : w ≠ z := by intro h; subst w; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hky : k ≠ y := by intro h; subst k; simp at fresh
  have hkz : k ≠ z := by intro h; subst k; simp at fresh
  have hqu : q ≠ u := by intro h; subst q; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqc : q ≠ c := by intro h; subst q; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  have hqz : q ≠ z := by intro h; subst q; simp at fresh
  have hrc : r ≠ c := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hrz : r ≠ z := by intro h; subst r; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let L := leastMemberCode c m r
  let Z := member u z
  let Γ := [Z,L,I,U,S]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hm : Context Γ (member c m) := Context.conjunctionLeft hl
  have him : Context Γ (both (member u m) (member x m)) :=
    .mp hm (Context.conjunctionLeft (.mp hi (.closed (intersection_instance u x c q m hqu hqx hqc hqm))))
  have hxm : Context Γ (member x m) := Context.conjunctionRight him
  have hyz : Context Γ (member y z) := .mp hz (.mp hu (.closed (subset_instance u y k z hku hky hkz)))
  have hc : Context Γ (either (equal z x) (member x z)) :=
    .mp hyz (.mp hs (.closed (successor_inspect x y w z hwx hwy hwz)))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.disjunctionElim hc
  · have he : Context (equal z x :: Γ) (equal z x) := Context.head Γ _
    have hmem : Context (equal z x :: Γ) (member x m) := Context.under hxm _
    have hzm : Context (equal z x :: Γ) (member z m) :=
      .mp hmem (.mp (Context.eqSymm he) (.closed (memberLeftEquality x z m)))
    exact Context.disjunctionRight (a := equal z m) hzm
  · have hxz : Context (member x z :: Γ) (member x z) := Context.head Γ _
    have hz' : Context (member x z :: Γ) (member u z) := Context.under hz _
    have hi' : Context (member x z :: Γ) I := Context.under hi _
    have hcz : Context (member x z :: Γ) (member c z) :=
      .mp (Context.conjunctionIntro hz' hxz)
        (Context.conjunctionRight (.mp hi' (.closed (intersection_instance u x c q z hqu hqx hqc hqz))))
    exact .mp hcz (.mp (Context.under hl _) (.closed (least_member_at c m r z hrc hrm hrz)))

def intersection_vacuity (u x c q z : Nat)
    (hzu : z ≠ u) (hzx : z ≠ x) (hzc : z ≠ c) (hzq : z ≠ q) :
    KDerivation (imp (intersectionGraph u x c q) (allCode z (intersectionGraph u x c q))) := by
  let f : CompactNamed.Formula := .all q (namedIntersectionBody u x c q)
  have hf : z ∉ f.names := by
    simp [f, namedIntersectionBody, namedBoth, CompactNamed.Formula.names, hzu, hzx, hzc, hzq]
  simpa [f, namedIntersectionBody, namedBoth, intersectionGraph, filterGraph, filterPredicate,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg] using f.vacuity z hf

def least_member_vacuity (c m r z : Nat) (hzc : z ≠ c) (hzm : z ≠ m) (hzr : z ≠ r) :
    KDerivation (imp (leastMemberCode c m r) (allCode z (leastMemberCode c m r))) := by
  let f := namedLeastMember c m r
  have hf : z ∉ f.names := by
    simp [f, namedLeastMember, namedBoth, namedEither, CompactNamed.Formula.names, hzc, hzm, hzr]
  simpa [f, namedLeastMember, namedBoth, namedEither, leastMemberCode,
    CompactNamed.Formula.encode, CompactProof.both, CompactProof.neg,
    CompactDerivations.either] using f.vacuity z hf

/-- A least element of u intersect x is a least element of u, provided u is a
subset of x's successor. The filter graph is retained as an explicit premise. -/
def least_intersection_preserved (x y w u k c q m r z : Nat)
    (fresh : [x,y,w,u,k,c,q,m,r,z].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (leastMemberCode c m r)
        (leastMemberCode u m z))))) := by
  have hzx : z ≠ x := by intro h; subst z; simp at fresh
  have hzy : z ≠ y := by intro h; subst z; simp at fresh
  have hzw : z ≠ w := by intro h; subst z; simp at fresh
  have hzu : z ≠ u := by intro h; subst z; simp at fresh
  have hzk : z ≠ k := by intro h; subst z; simp at fresh
  have hzc : z ≠ c := by intro h; subst z; simp at fresh
  have hzq : z ≠ q := by intro h; subst z; simp at fresh
  have hzm : z ≠ m := by intro h; subst z; simp at fresh
  have hzr : z ≠ r := by intro h; subst z; simp at fresh
  have hqu : q ≠ u := by intro h; subst q; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqc : q ≠ c := by intro h; subst q; simp at fresh
  have hqm : q ≠ m := by intro h; subst q; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let L := leastMemberCode c m r
  let Γ := [L,I,U,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hl : Context Γ L := .hypothesis (by simp [Γ])
  have hm : Context Γ (member c m) := Context.conjunctionLeft hl
  have him : Context Γ (both (member u m) (member x m)) :=
    .mp hm (Context.conjunctionLeft (.mp hi (.closed (intersection_instance u x c q m hqu hqx hqc hqm))))
  have hum : Context Γ (member u m) := Context.conjunctionLeft him
  have hpoint : Context Γ (imp (member u z) (either (equal z m) (member z m))) :=
    .mp hl (.mp hi (.mp hu (.mp hs (.closed (least_intersection_point x y w u k c q m r z fresh)))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode z h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = L
    · subst h
      exact least_member_vacuity c m r z hzc hzm hzr
    · by_cases h2 : h = I
      · subst h
        exact intersection_vacuity u x c q z hzu hzx hzc hzq
      · by_cases h3 : h = U
        · subst h
          exact subset_vacuity u y k z hzu hzy hzk
        · have h4 : h = S := ((hh.resolve_left h1).resolve_left h2).resolve_left h3
          subst h
          exact successor_vacuity x y w z hzx hzy hzw
  have hall : Context Γ (allCode z (imp (member u z) (either (equal z m) (member z m)))) :=
    Context.generalize z hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hum hall

theorem least_intersection_preserved_certificate (x y w u k c q m r z : Nat)
    (fresh : [x,y,w,u,k,c,q,m,r,z].Nodup) :
    theoremCode (certificate (least_intersection_preserved x y w u k c q m r z fresh)) =
      imp (successorCode x y w) (imp (subsetCode u y k)
        (imp (intersectionGraph u x c q) (imp (leastMemberCode c m r)
          (leastMemberCode u m z)))) :=
  certificate_correct (least_intersection_preserved x y w u k c q m r z fresh)

end PASoundness.PAtoCompactLeastSuccessorCase

#print axioms PASoundness.PAtoCompactLeastSuccessorCase.least_intersection_point
#print axioms PASoundness.PAtoCompactLeastSuccessorCase.least_intersection_preserved
#print axioms PASoundness.PAtoCompactLeastSuccessorCase.least_intersection_preserved_certificate
