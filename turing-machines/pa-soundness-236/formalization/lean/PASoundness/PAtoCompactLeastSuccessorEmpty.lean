import PASoundness.PAtoCompactLeastSuccessorCase
import PASoundness.PAtoCompactAdjunction

/-! Pointwise empty-intersection branch for least-subset successor closure.
The graph and the absence of a represented intersection member are explicit
K hypotheses. No global least-subset theorem or induction is asserted. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastSuccessorEmpty
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccessorInjective
open PASoundness.PAtoCompactPredecessor PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactLeastSuccessorCase PASoundness.PAtoCompactGreatestSuccessorCase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Introduce a fresh existential member name using an explicit witness. -/
def nonempty_from_member (c a z : Nat) (hac : a ≠ c) (haz : a ≠ z) :
    KDerivation (imp (member c z) (nonemptyCode c a)) := by
  let f : CompactNamed.Formula := .member c a
  have h := exists_variable_intro a z f haz
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.binders])
  simpa [f, nonemptyCode, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    hac, haz, Ne.symm hac, Ne.symm haz] using h

/-- If the represented intersection c of u and x is empty, every member of
u⊆Succ(x) is the top x. Negation is the literal compact encoding. -/
def empty_intersection_point (x y w u k c q a z : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (neg (nonemptyCode c a))
        (imp (member u z) (equal z x)))))) := by
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hwy : w ≠ y := by intro h; subst w; simp at fresh
  have hwz : w ≠ z := by intro h; subst w; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hky : k ≠ y := by intro h; subst k; simp at fresh
  have hkz : k ≠ z := by intro h; subst k; simp at fresh
  have hqu : q ≠ u := by intro h; subst q; simp at fresh
  have hqx : q ≠ x := by intro h; subst q; simp at fresh
  have hqc : q ≠ c := by intro h; subst q; simp at fresh
  have hqz : q ≠ z := by intro h; subst q; simp at fresh
  have hac : a ≠ c := by intro h; subst a; simp at fresh
  have haz : a ≠ z := by intro h; subst a; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let N := neg (nonemptyCode c a)
  let Z := member u z
  let Γ := [Z,N,I,U,S]
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
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
  · exact Context.head Γ _
  · have hxz : Context (member x z :: Γ) (member x z) := Context.head Γ _
    have hz' : Context (member x z :: Γ) Z := Context.under hz _
    have hi' : Context (member x z :: Γ) I := Context.under hi _
    have hcz : Context (member x z :: Γ) (member c z) :=
      .mp (Context.conjunctionIntro hz' hxz)
        (Context.conjunctionRight (.mp hi' (.closed (intersection_instance u x c q z hqu hqx hqc hqz))))
    have hne : Context (member x z :: Γ) (nonemptyCode c a) :=
      .mp hcz (.closed (nonempty_from_member c a z hac haz))
    have hf : Context (member x z :: Γ) 1 := .mp hne (Context.under hn _)
    exact .mp hf (.closed (explosion _))

def not_nonempty_vacuity (c a z : Nat) (hzc : z ≠ c) (hza : z ≠ a) :
    KDerivation (imp (neg (nonemptyCode c a)) (allCode z (neg (nonemptyCode c a)))) := by
  let f : CompactNamed.Formula := (CompactNamed.Formula.ex a (.member c a)).not
  have hf : z ∉ f.names := by
    simp [f, CompactNamed.Formula.not, CompactNamed.Formula.names, hzc, hza]
  simpa [f, nonemptyCode, CompactNamed.Formula.not, CompactNamed.Formula.encode,
    CompactProof.neg] using f.vacuity z hf

/-- If the intersection is empty and v is any member of u, the successor's
input x is a least member of u. The explicit member v witnesses nonemptiness. -/
def empty_intersection_least (x y w u k c q a z v : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,v].Nodup) :
    KDerivation (imp (successorCode x y w) (imp (subsetCode u y k)
      (imp (intersectionGraph u x c q) (imp (neg (nonemptyCode c a))
        (imp (member u v) (leastMemberCode u x z)))))) := by
  have hfz : [x,y,w,u,k,c,q,a,z].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,u,k,c,q,a,z] [v]) fresh
  have hfv : [x,y,w,u,k,c,q,a,v].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hzx : z ≠ x := by intro h; subst z; simp at fresh
  have hzy : z ≠ y := by intro h; subst z; simp at fresh
  have hzw : z ≠ w := by intro h; subst z; simp at fresh
  have hzu : z ≠ u := by intro h; subst z; simp at fresh
  have hzk : z ≠ k := by intro h; subst z; simp at fresh
  have hzc : z ≠ c := by intro h; subst z; simp at fresh
  have hzq : z ≠ q := by intro h; subst z; simp at fresh
  have hza : z ≠ a := by intro h; subst z; simp at fresh
  have hzv : z ≠ v := by intro h; subst z; simp at fresh
  let S := successorCode x y w
  let U := subsetCode u y k
  let I := intersectionGraph u x c q
  let N := neg (nonemptyCode c a)
  let V := member u v
  let Γ := [V,N,I,U,S]
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hn : Context Γ N := .hypothesis (by simp [Γ])
  have hi : Context Γ I := .hypothesis (by simp [Γ])
  have hu : Context Γ U := .hypothesis (by simp [Γ])
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hev : Context Γ (equal v x) := .mp hv (.mp hn (.mp hi (.mp hu (.mp hs
    (.closed (empty_intersection_point x y w u k c q a v hfv))))))
  have hux : Context Γ (member u x) := .mp hev (.mp hv (.closed (memberRightEquality u v x)))
  have hpoint : Context Γ (imp (member u z) (either (equal z x) (member z x))) := by
    apply Context.deduction
    have hm : Context (member u z :: Γ) (member u z) := Context.head Γ _
    have he : Context (member u z :: Γ) (equal z x) := .mp hm
      (.mp (Context.under hn _) (.mp (Context.under hi _) (.mp (Context.under hu _)
        (.mp (Context.under hs _) (.closed (empty_intersection_point x y w u k c q a z hfz))))))
    exact Context.disjunctionLeft (b := member z x) he
  have hvac : ∀ h, h ∈ Γ → KDerivation (imp h (allCode z h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = V
    · subst h
      exact membershipVacuity u v z hzu hzv
    · by_cases h2 : h = N
      · subst h
        exact not_nonempty_vacuity c a z hzc hza
      · by_cases h3 : h = I
        · subst h
          exact intersection_vacuity u x c q z hzu hzx hzc hzq
        · by_cases h4 : h = U
          · subst h
            exact subset_vacuity u y k z hzu hzy hzk
          · have h5 : h = S := (((hh.resolve_left h1).resolve_left h2).resolve_left h3).resolve_left h4
            subst h
            exact successor_vacuity x y w z hzx hzy hzw
  have hall : Context Γ (allCode z (imp (member u z) (either (equal z x) (member z x)))) :=
    Context.generalize z hvac hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  exact Context.conjunctionIntro hux hall

theorem empty_intersection_least_certificate (x y w u k c q a z v : Nat)
    (fresh : [x,y,w,u,k,c,q,a,z,v].Nodup) :
    theoremCode (certificate (empty_intersection_least x y w u k c q a z v fresh)) =
      imp (successorCode x y w) (imp (subsetCode u y k)
        (imp (intersectionGraph u x c q) (imp (neg (nonemptyCode c a))
          (imp (member u v) (leastMemberCode u x z))))) :=
  certificate_correct (empty_intersection_least x y w u k c q a z v fresh)

end PASoundness.PAtoCompactLeastSuccessorEmpty

#print axioms PASoundness.PAtoCompactLeastSuccessorEmpty.empty_intersection_point
#print axioms PASoundness.PAtoCompactLeastSuccessorEmpty.empty_intersection_least
#print axioms PASoundness.PAtoCompactLeastSuccessorEmpty.empty_intersection_least_certificate
