import PASoundness.PAtoCompactLeastCounterexample

/-! Capture-safe K alpha conversion for the outer subset binder and the
nonemptiness-witness binder of the displayed least-subsets formula. No
extensionality, soundness, arithmetic domain, or induction is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactCandidateAlphaLeast
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactPredecessor
open PASoundness.PAtoCompactLeastCounterexample

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- Rename the outer subset binder, without capturing any inner binder or the
free set name. -/
def least_subsets_outer_rename (x u k a m r v : Nat) (fresh : [x,u,k,a,m,r,v].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m r) (leastSubsetsCode x v k a m r)) := by
  have hux : u ≠ x := by intro h; subst u; simp at fresh
  have huv : u ≠ v := by intro h; subst u; simp at fresh
  have huk : u ≠ k := by intro h; subst u; simp at fresh
  have hua : u ≠ a := by intro h; subst u; simp at fresh
  have hum : u ≠ m := by intro h; subst u; simp at fresh
  have hur : u ≠ r := by intro h; subst u; simp at fresh
  have hvx : v ≠ x := by intro h; subst v; simp at fresh
  have hvk : v ≠ k := by intro h; subst v; simp at fresh
  have hva : v ≠ a := by intro h; subst v; simp at fresh
  have hvm : v ≠ m := by intro h; subst v; simp at fresh
  have hvr : v ≠ r := by intro h; subst v; simp at fresh
  let f := namedLeastSubsetsBody x u k a m r
  have ha := CompactNamed.universalAlpha u v f huv
    (by simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.binders, huk, hua, hum, hur])
    (by simp [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
      CompactNamed.Formula.names, hvx, hvk, hva, hvm, hvr, Ne.symm huv])
  simpa [f, namedLeastSubsetsBody, namedLeastMember, namedBoth, namedEither,
    leastSubsetsCode, leastMemberCode, subsetCode, nonemptyCode,
    CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    CompactProof.both, CompactProof.neg, CompactDerivations.either,
    hux, huv, huk, hua, hum, hur, hvx, hvk, hva, hvm, hvr,
    Ne.symm hux, Ne.symm huv, Ne.symm huk, Ne.symm hua, Ne.symm hum, Ne.symm hur,
    Ne.symm hvx, Ne.symm hvk, Ne.symm hva, Ne.symm hvm, Ne.symm hvr] using ha.1

/-- Rename the bound member name of a literal nonemptiness formula. -/
def nonempty_rename (u v a : Nat) (fresh : [u,v,a].Nodup) :
    KDerivation (imp (nonemptyCode u v) (nonemptyCode u a)) := by
  have hvu : v ≠ u := by intro h; subst v; simp at fresh
  have hva : v ≠ a := by intro h; subst v; simp at fresh
  have hau : a ≠ u := by intro h; subst a; simp at fresh
  let f : CompactNamed.Formula := .member u v
  have ha := CompactNamed.existentialAlpha v a f hva
    (by simp [f, CompactNamed.Formula.binders])
    (by simp [f, CompactNamed.Formula.names, hau, Ne.symm hva])
  simpa [f, nonemptyCode, CompactNamed.Formula.encode, CompactNamed.replace, CompactNamed.rename,
    hvu, hva, hau, Ne.symm hvu, Ne.symm hva, Ne.symm hau] using ha.1

/-- Rename the nonemptiness existential binder throughout the least-subsets
formula. The implication antecedent requires the reverse nonempty renaming. -/
def least_subsets_nonempty_rename (x u k a m r v : Nat) (fresh : [x,u,k,a,m,r,v].Nodup) :
    KDerivation (imp (leastSubsetsCode x u k a m r) (leastSubsetsCode x u k v m r)) := by
  have hn : [u,v,a].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil] at fresh ⊢
    tauto
  have hrename := nonempty_rename u v a hn
  have hp : KDerivation (imp
      (imp (subsetCode u x k) (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r))))
      (imp (subsetCode u x k) (imp (nonemptyCode u v) (existsCode m (leastMemberCode u m r))))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [nonemptyCode u v, subsetCode u x k,
      imp (subsetCode u x k) (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r)))]
    have hn' : Context Γ (nonemptyCode u v) := .hypothesis (by simp [Γ])
    have hs : Context Γ (subsetCode u x k) := .hypothesis (by simp [Γ])
    have hi : Context Γ (imp (subsetCode u x k)
        (imp (nonemptyCode u a) (existsCode m (leastMemberCode u m r)))) := .hypothesis (by simp [Γ])
    exact .mp (.mp hn' (.closed hrename)) (.mp hs hi)
  exact allCongr u hp

end PASoundness.PAtoCompactCandidateAlphaLeast

#print axioms PASoundness.PAtoCompactCandidateAlphaLeast.least_subsets_outer_rename
#print axioms PASoundness.PAtoCompactCandidateAlphaLeast.least_subsets_nonempty_rename
