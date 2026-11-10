import PASoundness.PAtoCompactLeastPairCompare
import PASoundness.PAtoCompactZeroSuccessor

/-! Existential least-element elimination for the conditional two-member
comparison. Existence of the pair and its least element are still premises. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactLeastPairExists
open PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactLeastCounterexample PASoundness.PAtoCompactLeastPairCompare
open PASoundness.PAtoCompactZeroSuccessor

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

/-- If a and b belong to c, each member of c is a or b, and c has a least
member, then a and b are comparable in the encoded order. -/
def compare_exists_least (c m r a b : Nat)
    (fresh : [c,m,r,a,b].Nodup) :
    KDerivation (imp (member c a) (imp (member c b)
      (imp (allCode m (imp (member c m) (either (equal m a) (equal m b))))
        (imp (existsCode m (leastMemberCode c m r))
          (either (equal a b) (either (member b a) (member a b))))))) := by
  have hrc : r ≠ c := by intro h; subst r; simp at fresh
  have hrm : r ≠ m := by intro h; subst r; simp at fresh
  have hra : r ≠ a := by intro h; subst r; simp at fresh
  have hrb : r ≠ b := by intro h; subst r; simp at fresh
  have hmc : m ≠ c := by intro h; subst m; simp at fresh
  have hma : m ≠ a := by intro h; subst m; simp at fresh
  have hmb : m ≠ b := by intro h; subst m; simp at fresh
  let L := leastMemberCode c m r
  let A := member c a
  let B := member c b
  let E := imp (member c m) (either (equal m a) (equal m b))
  let C := either (equal a b) (either (member b a) (member a b))
  let f : CompactNamed.Formula := namedEither (.equal a b)
    (namedEither (.member b a) (.member a b))
  have hf : m ∉ f.names := by
    simp [f, namedEither, CompactNamed.Formula.names, hma, hmb]
  have hv : KDerivation (imp C (allCode m C)) := by
    have h := f.vacuity m hf
    simpa [f, C, namedEither, CompactNamed.Formula.encode,
      CompactDerivations.either, CompactProof.neg] using h
  have hrot : KDerivation (imp A (imp B (imp E (imp L C)))) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    apply Context.deduction
    let Γ := [L,E,B,A]
    have hl : Context Γ L := .hypothesis (by simp [Γ])
    have ha : Context Γ A := .hypothesis (by simp [Γ])
    have hb : Context Γ B := .hypothesis (by simp [Γ])
    have he : Context Γ E := .hypothesis (by simp [Γ])
    exact .mp he (.mp hb (.mp ha (.mp hl
      (.closed (compare_from_least c m r a b hrc hrm hra hrb)))))
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [existsCode m L, allCode m E, B, A]
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have hb : Context Γ B := .hypothesis (by simp [Γ])
  have he : Context Γ (allCode m E) := .hypothesis (by simp [Γ])
  have hl : Context Γ (existsCode m L) := .hypothesis (by simp [Γ])
  have haa : Context Γ (allCode m A) := .mp ha (.closed (membershipVacuity c a m hmc hma))
  have hbb : Context Γ (allCode m B) := .mp hb (.closed (membershipVacuity c b m hmc hmb))
  have h1 := Context.allMP haa (.closed (.generalize m hrot))
  have h2 := Context.allMP hbb h1
  have h3 : Context Γ (allCode m (imp L C)) := Context.allMP he h2
  exact Context.existsElim hv h3 hl

theorem compare_exists_least_certificate (c m r a b : Nat)
    (fresh : [c,m,r,a,b].Nodup) :
    theoremCode (certificate (compare_exists_least c m r a b fresh)) =
      imp (member c a) (imp (member c b)
        (imp (allCode m (imp (member c m) (either (equal m a) (equal m b))))
          (imp (existsCode m (leastMemberCode c m r))
            (either (equal a b) (either (member b a) (member a b)))))) :=
  certificate_correct (compare_exists_least c m r a b fresh)

end PASoundness.PAtoCompactLeastPairExists

#print axioms PASoundness.PAtoCompactLeastPairExists.compare_exists_least
#print axioms PASoundness.PAtoCompactLeastPairExists.compare_exists_least_certificate
