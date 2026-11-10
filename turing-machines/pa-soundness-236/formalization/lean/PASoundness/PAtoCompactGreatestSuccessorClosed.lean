import PASoundness.PAtoCompactGreatestDownward
import PASoundness.PAtoCompactGreatestSuccessorCase

/-! Successor preservation of the represented greatest-subset property.
This does not supply an arithmetic domain, extensional equality, or induction.
Compact code 1 is self-membership, whose ordinary falsity is model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactGreatestSuccessorClosed
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactTransitiveClosure
open PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactGreatestDownward PASoundness.PAtoCompactGreatestSuccessorCase

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If every nonempty represented subset of x has a greatest member, the
same holds for the explicit successor y. Output subset binder u is fresh;
this does not assert closure of a single named domain formula. -/
def successor_greatest_subsets (x y w a k m t u r : Nat)
    (fresh : [x,y,w,a,k,m,t,u,r].Nodup) :
    KDerivation (imp (greatestSubsetsCode x a k m t) (imp (successorCode x y w)
      (greatestSubsetsCode y u k m t))) := by
  have hf7 : [x,y,w,u,k,t,m].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hf6 : [x,y,w,u,k,r].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  have hax : a ≠ x := by intro h; subst a; simp at fresh
  have hau : a ≠ u := by intro h; subst a; simp at fresh
  have hak : a ≠ k := by intro h; subst a; simp at fresh
  have ham : a ≠ m := by intro h; subst a; simp at fresh
  have hat : a ≠ t := by intro h; subst a; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hrk : r ≠ k := by intro h; subst r; simp at fresh
  have hru : r ≠ u := by intro h; subst r; simp at fresh
  have hrx : r ≠ x := by intro h; subst r; simp at fresh
  have hku : k ≠ u := by intro h; subst k; simp at fresh
  have hkx : k ≠ x := by intro h; subst k; simp at fresh
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huy : u ≠ y := by intro h; subst u; simp at fresh
  have huw : u ≠ w := by intro h; subst u; simp at fresh
  have hua : u ≠ a := by intro h; subst u; simp at fresh
  let G := greatestSubsetsCode x a k m t
  let S := successorCode x y w
  let U := subsetCode u y k
  let N := nonemptyCode u m
  let M := member u x
  let H := hasGreatestCode u m t
  let Γ := [S,G]
  have hs : Context Γ S := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp U (imp N H)) := by
    apply Context.deduction
    apply Context.deduction
    let Δ := [N,U,S,G]
    have hn : Context Δ N := .hypothesis (by simp [Δ])
    have hu : Context Δ U := .hypothesis (by simp [Δ])
    have hs' : Context Δ S := .hypothesis (by simp [Δ])
    have hg' : Context Δ G := .hypothesis (by simp [Δ])
    have he : KDerivation (either M (neg M)) := CompactHilbertBasis.identity (neg M)
    apply Context.disjunctionElim (Context.closed he : Context Δ (either M (neg M)))
    · have hm : Context (M :: Δ) M := Context.head Δ M
      exact .mp hm (.mp (Context.under hu M) (.mp (Context.under hs' M)
        (.closed (successor_subset_has_top x y w u k t m hf7))))
    · have hnm : Context (neg M :: Δ) (neg M) := Context.head Δ (neg M)
      have hsubr : Context (neg M :: Δ) (subsetCode u x r) :=
        .mp hnm (.mp (Context.under hu _) (.mp (Context.under hs' _)
          (.closed (successor_subset_without_top x y w u k r hf6))))
      have hsubk : Context (neg M :: Δ) (subsetCode u x k) :=
        .mp hsubr (.closed (PAtoCompactGreatestDownward.subset_rename u x r k hrk hru hrx hku hkx))
      have hi := greatest_subsets_instance x a k m t u hax hau hak ham hat huk hum hut
      exact .mp (Context.under hn _) (.mp hsubk (.mp (Context.under hg' _) (.closed hi)))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode u h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases h1 : h = S
    · subst h
      exact successor_vacuity x y w u hux huy huw
    · have h2 : h = G := hh.resolve_left h1
      subst h
      exact greatest_subsets_vacuity x a k m t u hux hua huk hum hut
  have hout : Context Γ (greatestSubsetsCode y u k m t) := Context.generalize u hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem successor_greatest_subsets_certificate (x y w a k m t u r : Nat)
    (fresh : [x,y,w,a,k,m,t,u,r].Nodup) :
    theoremCode (certificate (successor_greatest_subsets x y w a k m t u r fresh)) =
      imp (greatestSubsetsCode x a k m t) (imp (successorCode x y w)
        (greatestSubsetsCode y u k m t)) :=
  certificate_correct (successor_greatest_subsets x y w a k m t u r fresh)

end PASoundness.PAtoCompactGreatestSuccessorClosed

#print axioms PASoundness.PAtoCompactGreatestSuccessorClosed.successor_greatest_subsets
#print axioms PASoundness.PAtoCompactGreatestSuccessorClosed.successor_greatest_subsets_certificate
