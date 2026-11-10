import PASoundness.PAtoCompactLogicalMorphism
import PASoundness.PAtoCompactFormulaTransformCompiler

/-! Compose mapped checked logical-leaf proofs with a mapped checked-PA
compiler. Transformed arithmetic leaves and the three logical proof families
remain explicit finite K proof-data inputs. This module supplies no concrete
formula transformation, arithmetic handlers, or soundness theorem. -/

namespace PASoundness.PAtoCompactMappedLogicalCompiler

open FirstOrder FirstOrder.Language
open PASoundness.CompactProof PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactLogicalMorphism
open PASoundness.PAtoCompactFormulaTransformCompiler

/-- Supply the mapped logical leaves; mapped arithmetic leaves remain an
explicit family of finite K proofs. -/
noncomputable def leaves (m : LogicalMorphism)
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ →
      KDerivation (guardedCode (m.formula φ))) : TransformedLeaves m.formula where
  logical := guarded_logical m logical
  arithmetic := arithmetic

/-- Compile a checked PA proof through a logical morphism, given its mapped
arithmetic leaf proofs and the three guarded logical families. No semantic
soundness premise is used. -/
noncomputable def translateChecked (m : LogicalMorphism)
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ →
      KDerivation (guardedCode (m.formula φ)))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) : KDerivation (guardedCode (m.formula φ)) :=
  PAtoCompactFormulaTransformCompiler.translateChecked m.formula m.imp m.allAt
    (leaves m logical arithmetic) c φ hc

theorem translated_certificate (m : LogicalMorphism)
    (logical : PAtoCompactGuardedThreeLogical.ThreeLogical)
    (arithmetic : ∀ c φ, Certificates.paDecode c = some φ →
      KDerivation (guardedCode (m.formula φ)))
    (c : Certificates.PAProofCode) (φ : Peano.Formula)
    (hc : Certificates.paCheck c = some φ) :
    theoremCode (certificate (translateChecked m logical arithmetic c φ hc)) =
      guardedCode (m.formula φ) := certificate_correct _

end PASoundness.PAtoCompactMappedLogicalCompiler

#print axioms PASoundness.PAtoCompactMappedLogicalCompiler.leaves
#print axioms PASoundness.PAtoCompactMappedLogicalCompiler.translateChecked
#print axioms PASoundness.PAtoCompactMappedLogicalCompiler.translated_certificate
