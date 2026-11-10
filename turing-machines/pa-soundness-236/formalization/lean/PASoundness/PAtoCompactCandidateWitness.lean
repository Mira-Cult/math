import PASoundness.PAtoCompactCandidateExact
import PASoundness.PAtoCompactAdjunction
import PASoundness.PAtoCompactGreatestDownward

/-! K successor-graph witness in the exact transitivity/extrema candidate.
All syntactic freshness and selector-code inequalities are explicit. This
does not establish a fixed-binder invariant, equality quotient, induction,
arithmetic operations, or a PA proof translation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateWitness
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveSuccessor
open PASoundness.PAtoCompactTransitiveClosure PASoundness.PAtoCompactTransitiveDomain
open PASoundness.PAtoCompactTransitiveWitness PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactGreatestDownward PASoundness.PAtoCompactLeastCounterexample
open PASoundness.PAtoCompactAdjunction PASoundness.PAtoCompactCandidateExact

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Vacuity is preserved under the literal K conjunction encoding. -/
def both_vacuity (A B y : Nat)
    (ha : KDerivation (imp A (allCode y A))) (hb : KDerivation (imp B (allCode y B))) :
    KDerivation (imp (both A B) (allCode y (both A B))) := by
  have hi : KDerivation (imp A (imp B (both A B))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    exact Context.conjunctionIntro (Context.under (Context.head [] A) B) (Context.head [A] B)
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [both A B]
  have hd : Context Γ (both A B) := Context.head [] _
  have hal : Context Γ (allCode y A) := .mp (Context.conjunctionLeft hd) (.closed ha)
  have hbl : Context Γ (allCode y B) := .mp (Context.conjunctionRight hd) (.closed hb)
  exact Context.allMP hbl (Context.allMP hal (.closed (.generalize y hi)))

/-- Vacuity of the entire candidate at a syntax name fresh for its displayed
object and binders. -/
def candidate_vacuity (x b p q a k l m g y : Nat)
    (fresh : [x,b,p,q,a,k,l,m,g,y].Nodup) :
    KDerivation (imp (candidateCode x b p q a k l m g)
      (allCode y (candidateCode x b p q a k l m g))) := by
  have hyx : y ≠ x := by intro h; subst y; simp at fresh
  have hyb : y ≠ b := by intro h; subst y; simp at fresh
  have hyp : y ≠ p := by intro h; subst y; simp at fresh
  have hyq : y ≠ q := by intro h; subst y; simp at fresh
  have hya : y ≠ a := by intro h; subst y; simp at fresh
  have hyk : y ≠ k := by intro h; subst y; simp at fresh
  have hyl : y ≠ l := by intro h; subst y; simp at fresh
  have hym : y ≠ m := by intro h; subst y; simp at fresh
  have hyg : y ≠ g := by intro h; subst y; simp at fresh
  have hT := transitive_vacuity x p q y hyx hyp hyq
  have hM := members_transitive_vacuity x b p q y hyx hyb hyp hyq
  have hG := greatest_subsets_vacuity x a k m g y hyx hya hyk hym hyg
  have hL := least_subsets_vacuity x a k l m g y hyx hya hyk hyl hym hyg
  exact both_vacuity _ _ y (both_vacuity _ _ y hT hM) (both_vacuity _ _ y hG hL)

/-- From an exact candidate, K derives an existential successor graph whose
output is an exact candidate with fresh displayed output binder names. The
adjunction selector's code must differ from the displayed graph/output names. -/
def candidate_successor_exists (x y w b p q d s t a k m g u l r z v j point : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j,point].Nodup)
    (hwc : w ≠ adjunctionPredicate x point)
    (hyc : y ≠ adjunctionPredicate x point) :
    KDerivation (imp (candidateCode x b p q a k l m g)
      (existsCode y (both (successorCode x y w) (candidateCode y d p q u k v m g)))) := by
  have hclosure : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j].Nodup := by
    exact List.Nodup.sublist (List.sublist_append_left [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j] [point]) fresh
  have hvac : [x,b,p,q,a,k,l,m,g,y].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hpx : point ≠ x := by intro h; subst point; simp at fresh
  have hwp : w ≠ point := by intro h; subst w; simp at fresh
  have hwx : w ≠ x := by intro h; subst w; simp at fresh
  have hyx : y ≠ x := by intro h; subst y; simp at fresh
  have hyp : y ≠ point := by intro h; subst y; simp at fresh
  have hyw : y ≠ w := by intro h; subst y; simp at fresh
  have hsucc : KDerivation (existsCode y (successorCode x y w)) :=
    successor_graph_exists_fresh x point w y hpx hwp hwx hwc hyx hyp hyw hyc
  let D := candidateCode x b p q a k l m g
  let S := successorCode x y w
  let E := candidateCode y d p q u k v m g
  let Γ := [D]
  have hd : Context Γ D := Context.head [] D
  have hlocal : Context Γ (imp S (both S E)) := by
    apply Context.deduction
    have hs : Context (S :: Γ) S := Context.head Γ S
    have he : Context (S :: Γ) E := .mp hs (.mp (Context.under hd S)
      (.closed (candidate_exact_successor x y w b p q d s t a k m g u l r z v j hclosure)))
    exact Context.conjunctionIntro hs he
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode y h)) := by
    intro h hh
    have he : h = D := by simpa [Γ] using hh
    subst h
    exact candidate_vacuity x b p q a k l m g y hvac
  have hall : Context Γ (allCode y (imp S (both S E))) := Context.generalize y hv hlocal
  have hex : Context Γ (existsCode y S) := .closed hsucc
  exact Context.closeEmpty (Context.deduction (exists_map_context hall hex))

theorem candidate_successor_exists_certificate (x y w b p q d s t a k m g u l r z v j point : Nat)
    (fresh : [x,y,w,b,p,q,d,s,t,a,k,m,g,u,l,r,z,v,j,point].Nodup)
    (hwc : w ≠ adjunctionPredicate x point)
    (hyc : y ≠ adjunctionPredicate x point) :
    theoremCode (certificate (candidate_successor_exists x y w b p q d s t a k m g u l r z v j point fresh hwc hyc)) =
      imp (candidateCode x b p q a k l m g)
        (existsCode y (both (successorCode x y w) (candidateCode y d p q u k v m g))) :=
  certificate_correct (candidate_successor_exists x y w b p q d s t a k m g u l r z v j point fresh hwc hyc)

end PASoundness.PAtoCompactCandidateWitness

#print axioms PASoundness.PAtoCompactCandidateWitness.candidate_successor_exists
#print axioms PASoundness.PAtoCompactCandidateWitness.candidate_successor_exists_certificate
