import PASoundness.PAtoCompactGuardedBridge
import PASoundness.CompactDerivations

/-! Proof-data ingredients for guarded equality reflexivity. This establishes
only projection of an individual candidate guard; term-graph totality and
alignment of independently allocated equivalence templates remain open. -/
namespace PASoundness.PAtoCompactGuardedEqualityReflexivity

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge

/-- Finite K proof data projecting a listed candidate condition from a
guard conjunction. No semantic or arithmetic assumptions are used. -/
def guardList_projection (base x : Nat) (xs : List Nat) (hx : x ∈ xs) :
    KDerivation (imp (guardList base xs).encode (domainAt base x).encode) := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      apply Context.closeEmpty
      apply Context.deduction
      let Γ := [(guardList base (y :: ys)).encode]
      have hh : Context Γ (guardList base (y :: ys)).encode := Context.head [] _
      have hc : Context Γ (both (domainAt base y).encode (guardList base ys).encode) := by
        simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not,
          both, neg] using hh
      by_cases he : x = y
      · subst x
        exact Context.conjunctionLeft hc
      · have hm : x ∈ ys := by simpa [he] using hx
        exact .mp (Context.conjunctionRight hc) (.closed (ih hm))

/-- Every occurring free variable has a finite K projection from the formula's
actual sorted free-variable guard. -/
def guardFormula_projection (φ : Peano.Formula) (x : Nat) (hx : x ∈ φ.freeVarFinset) :
    KDerivation (imp (guardFormula φ).encode (domainAt (guardBase φ) x).encode) :=
  guardList_projection (guardBase φ) x (φ.freeVarFinset.sort (· ≤ ·))
    ((Finset.mem_sort (· ≤ ·)).mpr hx)

/-- The guard for the PA leaf `x = x` supplies the candidate predicate for
the variable. This does not yet construct the equality translation. -/
def variableGuard_projection (x : Nat) :
    let φ : Peano.Formula := (.var x : Peano.Term).equal (.var x)
    KDerivation (imp (guardFormula φ).encode (domainAt (guardBase φ) x).encode) := by
  apply guardFormula_projection
  simp [FirstOrder.Language.Term.equal, FirstOrder.Language.Term.bdEqual,
    FirstOrder.Language.BoundedFormula.freeVarFinset,
    FirstOrder.Language.Term.varFinsetLeft]

end PASoundness.PAtoCompactGuardedEqualityReflexivity

#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivity.guardList_projection
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivity.guardFormula_projection
#print axioms PASoundness.PAtoCompactGuardedEqualityReflexivity.variableGuard_projection
