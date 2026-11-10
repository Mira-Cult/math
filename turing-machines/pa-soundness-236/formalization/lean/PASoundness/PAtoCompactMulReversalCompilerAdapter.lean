import PASoundness.PAtoCompactMappedLogicalCompiler
import PASoundness.PAtoCompactMulReversalTarget
import PASoundness.PAtoCompactGuardedMulZeroCompatibility

/-! Instantiate the mapped checked-proof compiler with multiplication reversal.
The mapped PA-axiom leaves and three guarded logical proof families remain
explicit finite K proof-data inputs; this does not construct those inputs. -/

namespace PASoundness.PAtoCompactMulReversalCompilerAdapter

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactLogicalMorphism
open PASoundness.PAtoCompactMulReversalSyntax
open PASoundness.PAtoCompactMulReversalFormulaNaturality
open PASoundness.PAtoCompactMulReversalTarget
open PASoundness.PAtoCompactGuardedMulZeroCompatibility

/-- Multiplication reversal preserves the logical structure required for the
checked-proof compiler, including capture-safe binding and substitution. -/
def reversal : LogicalMorphism where
  formula := reverseBounded 0
  term := reverseTerm
  imp := by intro φ ψ; rfl
  neg := by intro φ; rfl
  equal := reverse_term_equal
  allAt := reverse_allAt
  substAt := reverse_substAt
  free := reverseBounded_freeVarFinset

/-- A finite K proof family for the reversal of every checked PA arithmetic
leaf. In particular, the original multiplication-successor leaf becomes a
first-factor successor equation; this definition does not supply its proof. -/
abbrev ReversedArithmeticLeaves := ∀ c φ, Certificates.paDecode c = some φ →
  KDerivation (guardedCode (reverseBounded 0 φ))

/-- Use the checked genuine-PA first-factor equation at reversed operands and
compile its reversed proof, under the displayed proof-family inputs. This
constructs the exact second-factor PA axiom family in K conditionally; it
uses no PA or K semantic soundness theorem. Certificate selection is
noncomputable. -/
noncomputable def mulSucc (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ReversedArithmeticLeaves) : MulSuccHandler := by
  intro t u
  let existence := source_certificate t u
  let c := Classical.choose existence
  have hc : Certificates.paCheck c = some (source t u) := Classical.choose_spec existence
  have h : KDerivation (guardedCode (reverseBounded 0 (source t u))) :=
    PAtoCompactMappedLogicalCompiler.translateChecked reversal logical arithmetic c (source t u) hc
  rw [reverse_source] at h
  exact h

theorem mulSucc_certificate (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ReversedArithmeticLeaves) (t u : Peano.Term) :
    theoremCode (certificate (mulSucc logical arithmetic t u)) =
      guardedCode ((Peano.mul t (Peano.succ u)).equal (Peano.add (Peano.mul t u) t)) :=
  certificate_correct _

end PASoundness.PAtoCompactMulReversalCompilerAdapter

#print axioms PASoundness.PAtoCompactMulReversalCompilerAdapter.reversal
#print axioms PASoundness.PAtoCompactMulReversalCompilerAdapter.ReversedArithmeticLeaves
#print axioms PASoundness.PAtoCompactMulReversalCompilerAdapter.mulSucc
#print axioms PASoundness.PAtoCompactMulReversalCompilerAdapter.mulSucc_certificate
