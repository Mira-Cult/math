import PASoundness.PAtoCompactDynamicSymmetry
import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactAllTermTransport
import PASoundness.PAtoCompactSuccTermTotality

/-! Finite K reversal of the two-witness translation of a PA equality.
The output witnesses are exchanged and term-graph allocator blocks are
transported. No term totality, functionality or model truth is assumed. -/
namespace PASoundness.PAtoCompactEqualityMatrixSymmetry

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactDynamicSymmetry PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Reverse the equality matrix with its witnesses swapped. Bounds concern
names, not represented values; in particular the witnesses may coincide. -/
noncomputable def matrix_swap {α : Type} [DecidableEq α] (v : α → Nat)
    (t u : Peano.language.Term α) (w z p q r p' q' r' : Nat)
    (hwp : w < p) (hwq' : w < q') (hzq : z < q) (hzp' : z < p')
    (hwr : w < r+2) (hzr : z < r+2) (hwr' : w < r'+2) (hzr' : z < r'+2)
    (htp : ∀ a ∈ t.varFinset, v a < p) (htq' : ∀ a ∈ t.varFinset, v a < q')
    (huq : ∀ a ∈ u.varFinset, v a < q) (hup' : ∀ a ∈ u.varFinset, v a < p') :
    KDerivation (imp (matrix v t u w z p q r).encode
      (matrix v u t z w p' q' r').encode) := by
  have ht := (termGraph_base_transport v t p q' w hwp hwq' htp htq').1
  have hu := (termGraph_base_transport v u q p' z hzq hzp' huq hup').1
  have hdom := termGraph_domain v t w p
  have hdomr := domainAt_transport p r w (by omega) (by omega)
  have hsym := dynamic_symmetry r w z hwr hzr
  have halpha := (equivAt_base_alpha r r' z w hzr hwr hzr' hwr').forward
  apply Context.closeEmpty
  apply Context.deduction
  let Γ := [(matrix v t u w z p q r).encode]
  have hm : Context Γ (matrix v t u w z p q r).encode := Context.head [] _
  have hc : Context Γ (both (termGraph v t w p).encode
      (both (termGraph v u z q).encode (equivAt r w z).encode)) := by
    simpa [matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm
  have ht0 : Context Γ (termGraph v t w p).encode := Context.conjunctionLeft hc
  have hc1 : Context Γ (both (termGraph v u z q).encode (equivAt r w z).encode) := Context.conjunctionRight hc
  have hu0 : Context Γ (termGraph v u z q).encode := Context.conjunctionLeft hc1
  have he0 : Context Γ (equivAt r w z).encode := Context.conjunctionRight hc1
  have ht1 : Context Γ (termGraph v t w q').encode := .mp ht0 (.closed ht)
  have hu1 : Context Γ (termGraph v u z p').encode := .mp hu0 (.closed hu)
  have hd0 : Context Γ (domainAt p w).encode := .mp ht0 (.closed hdom)
  have hd1 : Context Γ (domainAt r w).encode := .mp hd0 (.closed hdomr)
  have he1 : Context Γ (imp (equivAt r w z).encode (equivAt r z w).encode) := .mp hd1 (.closed hsym)
  have he2 : Context Γ (equivAt r z w).encode := .mp he0 he1
  have he3 : Context Γ (equivAt r' z w).encode := .mp he2 (.closed halpha)
  have hh := Context.conjunctionIntro hu1 (Context.conjunctionIntro ht1 he3)
  change Context Γ (both (termGraph v u z p').encode
    (both (termGraph v t w q').encode (equivAt r' z w).encode))
  exact hh

#print axioms matrix_swap
end PASoundness.PAtoCompactEqualityMatrixSymmetry
