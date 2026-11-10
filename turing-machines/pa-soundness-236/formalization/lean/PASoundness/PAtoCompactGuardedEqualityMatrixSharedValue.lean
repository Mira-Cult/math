import PASoundness.PAtoCompactGuardedSharedValueFormulaSubst
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactDynamicSymmetry
import PASoundness.PAtoCompactAllTermTransport

/-! A pointwise bridge from an equality frame matrix to two term graphs at a
shared output. The target term's finite K graph-output transport remains an
explicit input. No existential witnesses or graph laws are constructed here. -/

namespace PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactDynamicSymmetry
open PASoundness.PAtoCompactTermSubstPolyReplacement PASoundness.PAtoCompactGuardedSharedValueFormulaSubst
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactGuardedOutputReplacement

/-- From a guard and the actual equality matrix, reuse the left graph's
output for both terms. The original two outputs may be syntactically equal;
their represented values are never assumed distinct. -/
noncomputable def matrix_to_shared
    (g : Formula) (t u : Peano.Term) (w z p s e d : Nat)
    (hwp : w < p) (hwd : w < d) (hzs : z < s) (hzd : z < d)
    (hwe : w < e+2) (hze : z < e+2)
    (htp : ∀ a ∈ t.varFinset, a < p) (htd : ∀ a ∈ t.varFinset, a < d)
    (hus : ∀ a ∈ u.varFinset, a < s) (hud : ∀ a ∈ u.varFinset, a < d)
    (hgd : ∀ a ∈ g.free, a < d)
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (uout : GuardedOutputTransport g u) :
    KDerivation (imp g.encode (imp (matrix id t u w z p s e).encode
      (sharedGuard g t u w d).encode)) := by
  have hT := (termGraph_base_transport id t p d w hwp hwd
    (by intro a ha; simpa only [id_eq] using htp a ha)
    (by intro a ha; simpa only [id_eq] using htd a ha)).1
  have hU := (termGraph_base_transport id u s d z hzs hzd
    (by intro a ha; simpa only [id_eq] using hus a ha)
    (by intro a ha; simpa only [id_eq] using hud a ha)).1
  have hD := termGraph_domain id t w p
  have hDmove := domainAt_transport p d w (by omega) (by omega)
  have hE := (equivAt_base_alpha e d w z hwe hze (by omega) (by omega)).forward
  have hsym := dynamic_symmetry d w z (by omega) (by omega)
  have hout := uout d z w hzd hwd hud hgd hudom
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let M := (matrix id t u w z p s e).encode
  let Γ := [M, g.encode]
  have hG : Context Γ g.encode := .hypothesis (by simp [Γ])
  have hM : Context Γ M := Context.head _ _
  have hparts : Context Γ (both (termGraph id t w p).encode
      (both (termGraph id u z s).encode (equivAt e w z).encode)) := by
    simpa [M, matrix, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hM
  have hTp : Context Γ (termGraph id t w p).encode := Context.conjunctionLeft hparts
  have hrest := Context.conjunctionRight hparts
  have hUs : Context Γ (termGraph id u z s).encode := Context.conjunctionLeft hrest
  have hEwz : Context Γ (equivAt e w z).encode := Context.conjunctionRight hrest
  have hTd : Context Γ (termGraph id t w d).encode := .mp hTp (.closed hT)
  have hUd : Context Γ (termGraph id u z d).encode := .mp hUs (.closed hU)
  have hDw : Context Γ (domainAt d w).encode := .mp (.mp hTp (.closed hD)) (.closed hDmove)
  have hEd : Context Γ (equivAt d w z).encode := .mp hEwz (.closed hE)
  have hEzw : Context Γ (equivAt d z w).encode := .mp hEd (.mp hDw (.closed hsym))
  have hUw : Context Γ (termGraph id u w d).encode :=
    .mp hEzw (.mp hUd (.mp hDw (.mp hG (.closed hout))))
  have hret : Context Γ (retained g t w d).encode := by
    have hh := Context.conjunctionIntro hG hTd
    simpa [retained, andF, CompactNamed.Formula.not,
      CompactNamed.Formula.encode, both, neg] using hh
  have hshared := Context.conjunctionIntro hret hUw
  simpa [sharedGuard, andF, CompactNamed.Formula.not,
    CompactNamed.Formula.encode, both, neg] using hshared

theorem matrix_to_shared_certificate
    (g : Formula) (t u : Peano.Term) (w z p s e d : Nat)
    (hwp : w < p) (hwd : w < d) (hzs : z < s) (hzd : z < d)
    (hwe : w < e+2) (hze : z < e+2)
    (htp : ∀ a ∈ t.varFinset, a < p) (htd : ∀ a ∈ t.varFinset, a < d)
    (hus : ∀ a ∈ u.varFinset, a < s) (hud : ∀ a ∈ u.varFinset, a < d)
    (hgd : ∀ a ∈ g.free, a < d)
    (hudom : ∀ a ∈ u.varFinset, KDerivation (imp g.encode (domainAt d a).encode))
    (uout : GuardedOutputTransport g u) :
    theoremCode (certificate (matrix_to_shared g t u w z p s e d hwp hwd hzs hzd
      hwe hze htp htd hus hud hgd hudom uout)) =
      imp g.encode (imp (matrix id t u w z p s e).encode (sharedGuard g t u w d).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue

#print axioms PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue.matrix_to_shared
#print axioms PASoundness.PAtoCompactGuardedEqualityMatrixSharedValue.matrix_to_shared_certificate
