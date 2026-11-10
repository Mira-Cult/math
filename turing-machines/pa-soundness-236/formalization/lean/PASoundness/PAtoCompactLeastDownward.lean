import PASoundness.PAtoCompactGreatestDownward
import PASoundness.PAtoCompactLeastCounterexample

/-! A conditional K proof that the represented least-subset property descends
to represented subsets. No domain, induction or extensionality is asserted.
Code 1 is literally self-membership; its ordinary falsity reading is
model-dependent. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastDownward
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactGreatestDownward
attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- K proves that the least-subset property descends to any represented
subset. The output uses a fresh outer subset binder r; other displayed labels
are retained. The original least-subset property is an explicit assumption. -/
def least_subsets_downward (x y u k a m t r s : Nat)
    (fresh : [x,y,u,k,a,m,t,r,s].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m t) (imp (subsetCode y x k)
      (leastSubsetsCode y r k a m t))) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have hur : u ≠ r := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hua : u ≠ a := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hut : u ≠ t := by intro h; subst u; simp at fresh
  have hrx : r ≠ x := by intro h; subst r; simp at fresh
  have hry : r ≠ y := by intro h; subst r; simp at fresh
  have hru : r ≠ u := by intro h; subst r; simp at fresh
  have hrk : r ≠ k := by intro h; subst r; simp at fresh
  have hra : r ≠ a := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hrt : r ≠ t := by intro h; subst r; simp at fresh
  have hf : [x,y,r,k,s].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    aesop
  let G := leastSubsetsCode x u k a m t
  let A := subsetCode y x k
  let Γ := [A,G]
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hpoint : Context Γ (imp (subsetCode r y k)
      (imp (nonemptyCode r a) (existsCode m (leastMemberCode r m t)))) := by
    apply Context.deduction
    apply Context.deduction
    have hs : Context (nonemptyCode r a :: subsetCode r y k :: Γ) (subsetCode r y k) :=
      .hypothesis (by simp [Γ])
    have hn : Context (nonemptyCode r a :: subsetCode r y k :: Γ) (nonemptyCode r a) :=
      Context.head _ _
    have ha' := Context.under (Context.under ha (subsetCode r y k)) (nonemptyCode r a)
    have hg' := Context.under (Context.under hg (subsetCode r y k)) (nonemptyCode r a)
    have hsub : Context (nonemptyCode r a :: subsetCode r y k :: Γ) (subsetCode r x k) :=
      .mp hs (.mp ha' (.closed (subset_trans x y r k s hf)))
    exact .mp hn (.mp hsub (.mp hg' (.closed
      (least_subsets_instance x u k a m t r hux hur huk hua hum hut hrk hra hrm hrt))))
  have hv : ∀ h, h ∈ Γ → KDerivation (imp h (allCode r h)) := by
    intro h hh
    simp only [Γ, List.mem_cons, List.not_mem_nil, or_false] at hh
    by_cases he : h = A
    · subst h
      exact subset_vacuity y x k r hry hrx hrk
    · have he' : h = G := hh.resolve_left he
      subst h
      exact least_subsets_vacuity x u k a m t r hrx hru hrk hra hrm hrt
  have hout : Context Γ (leastSubsetsCode y r k a m t) := Context.generalize r hv hpoint
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  exact hout

theorem least_subsets_downward_certificate (x y u k a m t r s : Nat)
    (fresh : [x,y,u,k,a,m,t,r,s].Nodup) :
    theoremCode (certificate (least_subsets_downward x y u k a m t r s fresh)) =
      imp (leastSubsetsCode x u k a m t) (imp (subsetCode y x k)
        (leastSubsetsCode y r k a m t)) :=
  certificate_correct (least_subsets_downward x y u k a m t r s fresh)

end PASoundness.PAtoCompactLeastDownward

#print axioms PASoundness.PAtoCompactLeastDownward.least_subsets_downward
#print axioms PASoundness.PAtoCompactLeastDownward.least_subsets_downward_certificate
