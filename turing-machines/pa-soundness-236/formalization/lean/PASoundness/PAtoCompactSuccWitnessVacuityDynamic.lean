import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactSuccessorQuotientIntro

/-! Free-name bounds and finite K vacuity for quotient successor witnesses.
Only free names are constrained; private bound labels can overlap the names
selected for witnesses in unrelated subformulas. -/
namespace PASoundness.PAtoCompactSuccWitnessVacuityDynamic
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactFreeNames
open PASoundness.PAtoCompactFreeVacuity PASoundness.PAtoCompactAdjunction
open PASoundness.PAtoCompactZeroSuccessor

/-- The opened quotient-successor matrix. -/
def openedBody (b x y w : Nat) : Formula :=
  andF (domainAt b x) (andF (domainAt b y) (andF (domainAt b w)
    (andF (namedSuccessor x w (b+10)) (equivAt b w y))))

theorem raw_free (x w q : Nat) :
    (namedSuccessor x w q).free ⊆ {x,w} := by
  intro z hz
  simp only [namedSuccessor, namedSuccessorBody, namedBoth, namedEither,
    Formula.free, Finset.mem_erase, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at hz ⊢
  aesop

theorem opened_free (b x y w : Nat) :
    (openedBody b x y w).free ⊆ {x,y,w} := by
  intro z hz
  simp only [openedBody, andF_free, Finset.mem_union] at hz
  rcases hz with hx | hy | hw | hr | he
  · have hh := domainAt_free b x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    exact Or.inl hh
  · have hh := domainAt_free b y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    exact Or.inr (Or.inl hh)
  · have hh := domainAt_free b w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    exact Or.inr (Or.inr hh)
  · have hh := raw_free x w (b+10) hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    aesop
  · have hh := equivAt_free b w y he
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    aesop

/-- Candidate quotient-equivalence is vacuous at a third distinct name. -/
def equiv_vacuity (b x y z : Nat) (hzx : z ≠ x) (hzy : z ≠ y) :
    KDerivation (imp (equivAt b x y).encode (allCode z (equivAt b x y).encode)) := by
  apply free_vacuity
  intro hz
  have h := equivAt_free b x y hz
  simp [hzx,hzy] at h

/-- Quotient successor is vacuous at a third distinct name. -/
def succ_vacuity (b x y z : Nat) (hzx : z ≠ x) (hzy : z ≠ y) :
    KDerivation (imp (succAt b x y).encode (allCode z (succAt b x y).encode)) := by
  apply free_vacuity
  intro hz
  have h := succAt_free b x y hz
  simp [hzx,hzy] at h

/-- The first opened witness body is vacuous in an independent second
witness name, even if that name is a private bound label. -/
def opened_vacuity (b x y w z : Nat) (hzx : z ≠ x) (hzy : z ≠ y) (hzw : z ≠ w) :
    KDerivation (imp (openedBody b x y w).encode (allCode z (openedBody b x y w).encode)) := by
  apply free_vacuity
  intro hz
  have h := opened_free b x y w hz
  simp [hzx,hzy,hzw] at h

/-- Existentially closing the opened witness body leaves only the successor
input and output free. The independently quantified name may coincide with the
existential binder. -/
def opened_exists_vacuity (b x y w z : Nat) (hzx : z ≠ x) (hzy : z ≠ y) :
    KDerivation (imp (Formula.ex w (openedBody b x y w)).encode
      (allCode z (Formula.ex w (openedBody b x y w)).encode)) := by
  apply free_vacuity
  intro hz
  simp only [Formula.free, Finset.mem_erase] at hz
  have h := opened_free b x y w hz.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  exact h.elim hzx (fun h' => h'.elim hzy hz.1)

end PASoundness.PAtoCompactSuccWitnessVacuityDynamic
#print axioms PASoundness.PAtoCompactSuccWitnessVacuityDynamic.equiv_vacuity
#print axioms PASoundness.PAtoCompactSuccWitnessVacuityDynamic.succ_vacuity
#print axioms PASoundness.PAtoCompactSuccWitnessVacuityDynamic.opened_vacuity

#print axioms PASoundness.PAtoCompactSuccWitnessVacuityDynamic.opened_exists_vacuity
