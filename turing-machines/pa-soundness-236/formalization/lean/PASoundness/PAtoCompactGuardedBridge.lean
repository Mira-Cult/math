import PASoundness.PAtoCompactConcreteBridge
import PASoundness.PAtoCompactTermGraphTruth

/-! A guarded replacement for the impossible unguarded open-proof interface.
Each translated formula is guarded by candidate-domain conditions for its
source free variables. The axiom and proof-rule handlers remain explicit K
proof-data inputs; this file does not claim they have been constructed. -/
namespace PASoundness.PAtoCompactGuardedBridge

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactTermGraphTruth
open PASoundness.PAtoCompactTermRenamingSemantics PASoundness.PAtoCompactFormulaTranslation
open PASoundness.PAtoCompactFormulaFullTruth PASoundness.HFCoding
open PASoundness.Observer PASoundness.UnaryCodec PASoundness.M236Observer
open Shared.Beeping Shared.Beeping.Machines

/-- A conjunction of candidate-domain guards, one for each listed name. -/
def guardList (base : Nat) : List Nat → CompactNamed.Formula
  | [] => .truth
  | x :: xs => andF (domainAt base x) (guardList base xs)

/-- The fixed block begins above all source free variable names. -/
def guardBase (φ : Peano.Formula) : Nat := φ.freeVarFinset.sup id + 1

def guardFormula (φ : Peano.Formula) : CompactNamed.Formula :=
  guardList (guardBase φ) (φ.freeVarFinset.sort (· ≤ ·))

/-- The concrete formula translated under its source free-variable guard. -/
def guardedCode (φ : Peano.Formula) : Nat := imp (guardFormula φ).encode (code φ)

theorem guardList_realize (base : Nat) (xs : List Nat) (ρ : CompactMatrix.Environment) :
    (guardList base xs).Realize ρ ↔ ∀ x ∈ xs, (domainAt base x).Realize ρ := by
  induction xs with
  | nil => simp [guardList, CompactNamed.Formula.Realize]
  | cons x xs ih => simp [guardList, andF_realize, ih]

/-- Every guard is true on a standard ordinal-coded PA assignment. -/
theorem guard_true (φ : Peano.Formula) (v : Nat → Nat) :
    (guardFormula φ).Realize (PAtoCompactOpenScope.ordinalAssignment v) := by
  rw [guardFormula, guardList_realize]
  intro x hx
  have hx' : x ∈ φ.freeVarFinset := (Finset.mem_sort (· ≤ ·)).mp hx
  have hle : x ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hx'
  apply domainAt_ordinal (guardBase φ) x (v x) (by unfold guardBase; omega)
    (PAtoCompactOpenScope.ordinalAssignment v)
  rfl

/-- The guarded concrete translation has the same standard truth as the PA
formula, because its guard holds on every ordinal-coded assignment. -/
theorem guarded_truth (φ : Peano.Formula) (v : Nat → Nat) :
    (CompactMatrix.decode (guardedCode φ)).Realize (PAtoCompactOpenScope.ordinalAssignment v) ↔
      φ.Realize v := by
  rw [guardedCode, CompactSemantics.realize_imp, CompactNamed.Formula.encode_realize,
    formula_truth]
  simp [guard_true φ v]

/-- Remaining syntactic proof obligations for the guarded translation.
Modus ponens and generalization receive actual finite K proofs and must return
finite K proofs, handling changes in free-variable guards. -/
structure Handlers where
  logical : ∀ c φ, Certificates.logicalDecode c = some φ → KDerivation (guardedCode φ)
  arithmetic : ∀ c φ, Certificates.paDecode c = some φ → KDerivation (guardedCode φ)
  modusPonens : ∀ φ ψ, KDerivation (guardedCode (φ.imp ψ)) →
    KDerivation (guardedCode φ) → KDerivation (guardedCode ψ)
  generalization : ∀ x φ, KDerivation (guardedCode φ) →
    KDerivation (guardedCode (FOL.allAt x φ))

/-- Structurally compile an actual checked PA certificate into finite K proof
data under the explicit guarded axiom and rule handlers. -/
def translateChecked (h : Handlers) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode φ) := by
  cases c with
  | logical c => exact h.logical c φ hc
  | nonlogical c => exact h.arithmetic c φ hc
  | generalize x c =>
      cases hp : Certificates.check Certificates.paDecode c with
      | none => simp [Certificates.paCheck, Certificates.check, hp] at hc
      | some ψ =>
          simp only [Certificates.paCheck, Certificates.check, hp, Option.map_some,
            Option.some.injEq] at hc
          subst φ
          exact h.generalization x ψ (translateChecked h c ψ hp)
  | mp p q =>
      cases hp : Certificates.check Certificates.paDecode p with
      | none => simp [Certificates.paCheck, Certificates.check, hp] at hc
      | some ψ =>
          cases ψ with
          | falsum => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | equal _ _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | rel _ _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | all _ => simp [Certificates.paCheck, Certificates.check, hp] at hc
          | imp a b =>
              cases hq : Certificates.check Certificates.paDecode q with
              | none => simp [Certificates.paCheck, Certificates.check, hp, hq] at hc
              | some χ =>
                  by_cases he : a = χ
                  · subst χ
                    simp [Certificates.paCheck, Certificates.check, hp, hq] at hc
                    subst φ
                    exact h.modusPonens a b (translateChecked h p _ hp) (translateChecked h q _ hq)
                  · simp [Certificates.paCheck, Certificates.check, hp, hq, he] at hc
termination_by c

theorem translated_certificate (h : Handlers) (c : Certificates.PAProofCode)
    (φ : Peano.Formula) (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked h c φ hc)) = guardedCode φ := certificate_correct _

/-- Ordinary PA derivability gives only a Prop-valued existence of a guarded
K derivation; no certificate is computed from an erased PA proof. -/
theorem transport (h : Handlers) {φ : Peano.Formula} (hp : Peano.FormulaProves φ) :
    KProves (guardedCode φ) := by
  obtain ⟨c, hc⟩ := Certificates.paCheck_complete hp
  exact ⟨translateChecked h c φ hc⟩

theorem pa_formula_of_compact_sound (h : Handlers) (hs : M236Reverse.CompactSound)
    {φ : Peano.Formula} (hp : Peano.FormulaProves φ) (v : Nat → Nat) : φ.Realize v := by
  obtain ⟨d⟩ := transport h hp
  exact (guarded_truth φ v).mp (hs (guardedCode φ) d (PAtoCompactOpenScope.ordinalAssignment v))

theorem pa_soundness_of_selected_accepts (h : Handlers)
    (ha : TraceAccept (machineWordSystem M236.machine M236.machineLabels))
    (s : Peano.Sentence) (hp : Peano.Proves s) : Nat ⊨ s := by
  apply (FOL.realize_openSentence s (fun _ => 0)).mp
  exact pa_formula_of_compact_sound h
    (M236MachineCompact.selected_trace_iff_compact_sound.mp ha) hp (fun _ => 0)

/-- Literal machine acceptance is equivalent to PA soundness provided all
guarded axiom and proof-rule handlers are constructed. -/
theorem selected_accepts_iff_pa_soundness (h : Handlers) :
    TraceAccept (machineWordSystem M236.machine M236.machineLabels) ↔
      (∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s) := by
  constructor
  · intro ha s hp
    exact pa_soundness_of_selected_accepts h ha s hp
  · exact PASoundnessToM236Closed.selected_accepts_of_pa_soundness

end PASoundness.PAtoCompactGuardedBridge

#print axioms PASoundness.PAtoCompactGuardedBridge.guard_true
#print axioms PASoundness.PAtoCompactGuardedBridge.guarded_truth
#print axioms PASoundness.PAtoCompactGuardedBridge.translateChecked
#print axioms PASoundness.PAtoCompactGuardedBridge.selected_accepts_iff_pa_soundness
