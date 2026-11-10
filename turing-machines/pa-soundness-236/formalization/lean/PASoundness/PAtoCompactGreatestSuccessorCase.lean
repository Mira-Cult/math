import PASoundness.PAtoCompactPredecessor
import PASoundness.PAtoCompactAdjunction

/-! A bounded step toward successor preservation of greatest-subset
conditions: a subset of a successor has the input as an upper bound. No
successor preservation of the whole condition is asserted here. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestSuccessorCase
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactGreatestSuccessor
open PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactAdjunction

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def subset_instance (u y k t : Nat) (hku : k ≠ u) (hky : k ≠ y) (hkt : k ≠ t) :
    KDerivation (imp (subsetCode u y k) (imp (member u t) (member y t))) := by
  let f : CompactNamed.Formula := .imp (.member u k) (.member y k)
  have h := CompactNamed.universalInstance k t f hkt
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.binders])
  simpa [f, subsetCode, CompactNamed.Formula.encode, CompactNamed.replace,
    CompactNamed.rename, hku, hky, hkt, Ne.symm hku, Ne.symm hky, Ne.symm hkt] using h

def subset_vacuity (u y k t : Nat) (htu : t ≠ u) (hty : t ≠ y) (htk : t ≠ k) :
    KDerivation (imp (subsetCode u y k) (allCode t (subsetCode u y k))) := by
  let f : CompactNamed.Formula := .all k (.imp (.member u k) (.member y k))
  have hf : t ∉ f.names := by simp [f, CompactNamed.Formula.names, htu, hty, htk]
  simpa [f, subsetCode, CompactNamed.Formula.encode] using f.vacuity t hf

def not_member_vacuity (u x t : Nat) (htu : t ≠ u) (htx : t ≠ x) :
    KDerivation (imp (neg (member u x)) (allCode t (neg (member u x)))) := by
  let f : CompactNamed.Formula := (CompactNamed.Formula.member u x).not
  have hf : t ∉ f.names := by simp [f, CompactNamed.Formula.not, CompactNamed.Formula.names, htu, htx]
  simpa [f, CompactNamed.Formula.not, CompactNamed.Formula.encode, CompactProof.neg] using f.vacuity t hf

/-- Every member of u is either the successor's input x or a member of x.
Membership of x in u is deliberately not assumed in this upper-bound lemma. -/
def successor_subset_upper_bound (x y w u k t : Nat)
    (fresh : [x,y,w,u,k,t].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k) (greatestCode u x t))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hwt : w ≠ t := by intro h; subst w; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hky : k ≠ y := by intro h; subst k; simp at fresh
  have hkt : k ≠ t := by intro h; subst k; simp at fresh
  have htx : t ≠ x := by intro h; subst t; simp at fresh
  have hty : t ≠ y := by intro h; subst t; simp at fresh
  have htw : t ≠ w := by intro h; subst t; simp at fresh
  have htu : t ≠ u := by intro h; subst t; simp at fresh
  have htk : t ≠ k := by intro h; subst t; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let Γ := [U,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member u t) (either (equal t x) (member x t))) := by
    apply Context.deduction
    have hmem : Context (member u t :: Γ) (member u t) := Context.head Γ _
    have hy : Context (member u t :: Γ) (member y t) :=
      .mp hmem (.mp (Context.under hu _) (.closed (subset_instance u y k t hku hky hkt)))
    exact .mp hy (.mp (Context.under hs _) (.closed (successor_inspect x y w t hwx hwy hwt)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode t h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = U
    · subst h
      exact subset_vacuity u y k t htu hty htk
    · have h2 : h = S := hh.resolve_left h1
      subst h
      exact successor_vacuity x y w t htx hty htw
  have hg : Context Γ (greatestCode u x t) := Context.generalize t hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hg

/-- A subset of the successor that contains the input has that input as an
actual greatest member; the existential uses a fresh binder. -/
def successor_subset_has_top (x y w u k t m : Nat)
    (fresh : [x,y,w,u,k,t,m].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (member u x) (hasGreatestCode u m t)))) := by
  have h6 : [x,y,w,u,k,t].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,u,k,t] [m]) fresh
  have hmx : m ≠ x := by intro h; subst m; simp at fresh
  have hmu : m ≠ u := by intro h; subst m; simp at fresh
  have hmt : m ≠ t := by intro h; subst m; simp at fresh
  have hxt : x ≠ t := by intro h; subst x; simp at fresh
  let f := namedBoth (.member u m) (.all t (namedGreatestBody u m t))
  have hi := exists_variable_intro m x f hmx
    (by simp [f, namedBoth, namedGreatestBody, namedEither, CompactNamed.Formula.binders, hmt])
    (by simp [f, namedBoth, namedGreatestBody, namedEither, CompactNamed.Formula.binders, hxt])
  have hi' : KDerivation (imp (both (member u x) (greatestCode u x t))
      (hasGreatestCode u m t)) := by
    simpa [f, namedBoth, namedGreatestBody, namedEither, greatestCode, hasGreatestCode,
      CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
      CompactProof.both, CompactProof.neg, CompactDerivations.either,
      hmx, hmu, hmt, hxt, Ne.symm hmx, Ne.symm hmu, Ne.symm hmt, Ne.symm hxt] using hi
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [member u x, subsetCode u y k, successorCode x y w]
  have hm : Context Γ (member u x) := .hypothesis (by simp [Γ])
  have hu : Context Γ (subsetCode u y k) := .hypothesis (by simp [Γ])
  have hs : Context Γ (successorCode x y w) := .hypothesis (by simp [Γ])
  have hg : Context Γ (greatestCode u x t) :=
    .mp hu (.mp hs (.closed (successor_subset_upper_bound x y w u k t h6)))
  exact .mp (Context.conjunctionIntro hm hg) (.closed hi')

/-- If u is a subset of the successor and omits x, it is a subset of x.
This is the second case needed for greatest-subset successor preservation. -/
def successor_subset_without_top (x y w u k t : Nat)
    (fresh : [x,y,w,u,k,t].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (neg (member u x)) (subsetCode u x t)))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hwt : w ≠ t := by intro h; subst w; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hky : k ≠ y := by intro h; subst k; simp at fresh
  have hkt : k ≠ t := by intro h; subst k; simp at fresh
  have htx : t ≠ x := by intro h; subst t; simp at fresh
  have hty : t ≠ y := by intro h; subst t; simp at fresh
  have htw : t ≠ w := by intro h; subst t; simp at fresh
  have htu : t ≠ u := by intro h; subst t; simp at fresh
  have htk : t ≠ k := by intro h; subst t; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let N := neg (member u x)
  let Γ := [N,U,S]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (member u t) (member x t)) := by
    apply Context.deduction
    have ht : Context (member u t :: Γ) (member u t) := Context.head Γ _
    have hy : Context (member u t :: Γ) (member y t) :=
      .mp ht (.mp (Context.under hu _) (.closed (subset_instance u y k t hku hky hkt)))
    have hc : Context (member u t :: Γ) (either (equal t x) (member x t)) :=
      .mp hy (.mp (Context.under hs _) (.closed (successor_inspect x y w t hwx hwy hwt)))
    apply Context.disjunctionElim hc
    · have he : Context (equal t x :: member u t :: Γ) (equal t x) := Context.head _ _
      have hm : Context (equal t x :: member u t :: Γ) (member u t) := Context.under ht _
      have hx : Context (equal t x :: member u t :: Γ) (member u x) :=
        .mp he (.mp hm (.closed (memberRightEquality u t x)))
      have hf : Context (equal t x :: member u t :: Γ) 1 :=
        .mp hx (Context.under (Context.under hn _) _)
      exact .mp hf (.closed (explosion _))
    · exact Context.head _ _
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode t h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = N
    · subst h
      exact not_member_vacuity u x t htu htx
    · by_cases h2 : h = U
      · subst h
        exact subset_vacuity u y k t htu hty htk
      · have h3 : h = S := (hh.resolve_left h1).resolve_left h2
        subst h
        exact successor_vacuity x y w t htx hty htw
  have hout : Context Γ (subsetCode u x t) := Context.generalize t hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact hout

end PASoundness.PAtoCompactGreatestSuccessorCase

#print axioms PASoundness.PAtoCompactGreatestSuccessorCase.successor_subset_upper_bound
#print axioms PASoundness.PAtoCompactGreatestSuccessorCase.successor_subset_has_top
#print axioms PASoundness.PAtoCompactGreatestSuccessorCase.successor_subset_without_top
