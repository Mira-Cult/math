import PASoundness.PAtoCompactGuardedUniversalAlignment
import PASoundness.PAtoCompactScopedActiveAll
import PASoundness.PAtoCompactGuardedLogicalCongruence

/-! A bounded universal node preserves guarded alignment under two arbitrary
source substitutions. The same fixed guard remains outside both universals;
the body hypothesis is needed for any active-name environment. -/
namespace PASoundness.PAtoCompactScopedSuccSubstUniversal

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactFormulaTranslation PASoundness.PAtoCompactScopedActiveAll
open PASoundness.PAtoCompactVacuousUniversal PASoundness.PAtoCompactVacuousQuantifierFree
open PASoundness.PAtoCompactGuardedLogicalCongruence PASoundness.PAtoCompactGuardedUniversalAlignment

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def BodyIH {n : Nat} (body : Peano.language.BoundedFormula Nat n)
    (σ τ : Nat → Peano.Term) (H : Formula) :=
  ∀ bound : Fin n → Nat,
    GuardedBoth H (scopedFormula n (body.subst σ) bound)
      (scopedFormula n (body.subst τ) bound)

/-- Move a guarded implication through unconditional K implications on its
source and target sides. -/
def guarded_compose (H A B C D : Formula)
    (left : KDerivation (imp A.encode B.encode))
    (middle : KDerivation (imp H.encode (imp B.encode C.encode)))
    (right : KDerivation (imp C.encode D.encode)) :
    KDerivation (imp H.encode (imp A.encode D.encode)) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [A.encode, H.encode]
  have ha : Context Γ A.encode := Context.head _ _
  have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
  exact .mp (.mp (.mp ha (.closed left)) (.mp hh (.closed middle))) (.closed right)

/-- The universal case. The new common name is chosen fresh for both
children and the retained guard; active labels may alias one another or free
source names. -/
noncomputable def universal_step {n : Nat}
    (body : Peano.language.BoundedFormula Nat (n+1))
    (σ τ : Nat → Peano.Term) (H : Formula) (ih : BodyIH body σ τ H)
    (bound : Fin n → Nat) :
    GuardedBoth H (scopedFormula n ((.all body : Peano.language.BoundedFormula Nat n).subst σ) bound)
      (scopedFormula n ((.all body : Peano.language.BoundedFormula Nat n).subst τ) bound) := by
  let a := body.subst σ
  let b := body.subst τ
  let p := universalName a bound
  let q := universalName b bound
  let F := scopedFormula (n+1) a (Fin.snoc bound p)
  let G := scopedFormula (n+1) b (Fin.snoc bound q)
  let z := max (max p q) ((F.names ∪ G.names ∪ H.free).sup id) + 1
  have hpz : p < z := by dsimp [z]; omega
  have hqz : q < z := by dsimp [z]; omega
  have hzF : z ∉ F.names := by
    intro h
    have hl : z ≤ (F.names ∪ G.names ∪ H.free).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ (Finset.mem_union_left _ h))
    dsimp [z] at hl; omega
  have hzG : z ∉ G.names := by
    intro h
    have hl : z ≤ (F.names ∪ G.names ∪ H.free).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_left _ (Finset.mem_union_right _ h))
    dsimp [z] at hl; omega
  have hzH : z ∉ H.free := by
    intro h
    have hl : z ≤ (F.names ∪ G.names ∪ H.free).sup id :=
      Finset.le_sup (f := id) (Finset.mem_union_right _ h)
    dsimp [z] at hl; omega
  have hpFree : p ∉ a.freeVarFinset := by
    intro h
    have h' : p ∈ (.all a : Peano.language.BoundedFormula Nat n).freeVarFinset := by simpa using h
    have ht := free_lt_scopeBase (.all a) bound p h'
    dsimp [p, universalName] at ht; omega
  have hqFree : q ∉ b.freeVarFinset := by
    intro h
    have h' : q ∈ (.all b : Peano.language.BoundedFormula Nat n).freeVarFinset := by simpa using h
    have ht := free_lt_scopeBase (.all b) bound q h'
    dsimp [q, universalName] at ht; omega
  have hpbind : p ∉ F.binders := by
    have hh := active_not_binder a (Fin.snoc bound p) (Fin.last n)
    simpa [F] using hh
  have hqbind : q ∉ G.binders := by
    have hh := active_not_binder b (Fin.snoc bound q) (Fin.last n)
    simpa [G] using hh
  have hboundp : ∀ j, bound j ≠ p := fun j => Nat.ne_of_lt (bound_lt_scopeBase (.all a) bound j)
  have hboundq : ∀ j, bound j ≠ q := fun j => Nat.ne_of_lt (bound_lt_scopeBase (.all b) bound j)
  have leftRaw := scoped_active_replace a (Fin.snoc bound p) (Fin.last n) z
    (by simpa using hpFree) (by simpa using hpz) (by simpa [F] using hzF)
  have rightRaw := scoped_active_replace b (Fin.snoc bound q) (Fin.last n) z
    (by simpa using hqFree) (by simpa using hqz) (by simpa [G] using hzG)
  have left : KBoth (replace p z F) (scopedFormula (n+1) a (Fin.snoc bound z)) := by
    simpa [F, rename_snoc_nonhit bound p z hboundp] using leftRaw
  have right : KBoth (replace q z G) (scopedFormula (n+1) b (Fin.snoc bound z)) := by
    simpa [G, rename_snoc_nonhit bound q z hboundq] using rightRaw
  have mid := ih (Fin.snoc bound z)
  have forward := guarded_compose H _ _ _ _ left.1 mid.1 right.2
  have backward := guarded_compose H _ _ _ _ right.1 mid.2 left.2
  have result := guarded_raw_align_of_free p q z (z+1) F G H hpz hqz (by omega)
    hpbind hqbind hzF hzG hzH forward backward
  simpa [GuardedBoth, BoundedFormula.subst, BoundedFormula.mapTermRel,
    scopedFormula, rawGuard, a, b, p, q, F, G, universalName] using result

end PASoundness.PAtoCompactScopedSuccSubstUniversal

#print axioms PASoundness.PAtoCompactScopedSuccSubstUniversal.guarded_compose
#print axioms PASoundness.PAtoCompactScopedSuccSubstUniversal.universal_step
