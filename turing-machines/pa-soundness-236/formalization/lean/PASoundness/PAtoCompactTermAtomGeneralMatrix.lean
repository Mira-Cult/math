import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactEquivMultiAlpha

/-! Matrix-level graph substitution with an arbitrary unchanged right term.
The candidate-relative transitivity K proof is an explicit input. -/
namespace PASoundness.PAtoCompactTermAtomGeneralMatrix

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactVacuousEqualityAlignment
open PASoundness.PAtoCompactSuccTermTotality PASoundness.PAtoCompactAllTermTransport
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactEquivMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The substituted graph value `q` can supply the left side of a target
equality matrix while the arbitrary unchanged right term keeps its own graph
value `r`. Only the graph's allocator is transported; graph functionality is
not assumed. All operand and source-name bounds, and the candidate-relative
transitivity K proof, are explicit. -/
noncomputable def matrix_of_graph_rebased (t w : Peano.Term) (q a r p s e d u f : Nat)
    (hqD : q < d+2) (hqP : q < p+2) (haP : a < p+2)
    (haE : a < e+2) (hrE : r < e+2)
    (hqF : q < f+2) (haF : a < f+2) (hrF : r < f+2)
    (hrS : r < s) (hrU : r < u)
    (hwS : ∀ v ∈ w.varFinset, v < s) (hwU : ∀ v ∈ w.varFinset, v < u)
    (trans : KDerivation (imp (domainAt f q).encode
      (imp (equivAt f q a).encode (imp (equivAt f a r).encode (equivAt f q r).encode)))) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (matrix id (.var q) w a r p s e).encode
        (matrix id t w q r d u f).encode)) := by
  have hd := domainAt_transport d f q (by omega) (by omega)
  have hqa := (equivAt_base_alpha p f q a hqP haP hqF haF).forward
  have har := (equivAt_base_alpha e f a r haE hrE haF hrF).forward
  have hw := (termGraph_base_transport id w s u r hrS hrU
    (by intro v hv; simpa only [id_eq] using hwS v hv)
    (by intro v hv; simpa only [id_eq] using hwU v hv)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let T := (termGraph id t q d).encode
  let M := (matrix id (.var q) w a r p s e).encode
  let Γ := [M, T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hm' : Context Γ (both (termGraph id (.var q) a p).encode
      (both (termGraph id w r s).encode (equivAt e a r).encode)) := by
    simpa [M, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm
  have hv := Context.conjunctionLeft hm'
  have hp := Context.conjunctionRight hm'
  have hws := Context.conjunctionLeft hp
  have hars := Context.conjunctionRight hp
  have hv' : Context Γ (both (domainAt p a).encode (equivAt p q a).encode) := by
    simpa [termGraph, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hv
  have hqap : Context Γ (equivAt p q a).encode := Context.conjunctionRight hv'
  have hqaf : Context Γ (equivAt f q a).encode := .mp hqap (.closed hqa)
  have harf : Context Γ (equivAt f a r).encode := .mp hars (.closed har)
  have hwf : Context Γ (termGraph id w r u).encode := .mp hws (.closed hw)
  have hdf : Context Γ (domainAt f q).encode := .mp (.mp ht (.closed (termGraph_domain id t q d))) (.closed hd)
  have hqr : Context Γ (equivAt f q r).encode := .mp harf (.mp hqaf (.mp hdf (.closed trans)))
  have h := Context.conjunctionIntro ht (Context.conjunctionIntro hwf hqr)
  simpa [T, M, Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h

theorem matrix_of_graph_rebased_certificate (t w : Peano.Term) (q a r p s e d u f : Nat)
    (hqD : q < d+2) (hqP : q < p+2) (haP : a < p+2)
    (haE : a < e+2) (hrE : r < e+2)
    (hqF : q < f+2) (haF : a < f+2) (hrF : r < f+2)
    (hrS : r < s) (hrU : r < u)
    (hwS : ∀ v ∈ w.varFinset, v < s) (hwU : ∀ v ∈ w.varFinset, v < u)
    (trans : KDerivation (imp (domainAt f q).encode
      (imp (equivAt f q a).encode (imp (equivAt f a r).encode (equivAt f q r).encode)))) :
    theoremCode (certificate (matrix_of_graph_rebased t w q a r p s e d u f hqD hqP haP
      haE hrE hqF haF hrF hrS hrU hwS hwU trans)) =
      imp (termGraph id t q d).encode
        (imp (matrix id (.var q) w a r p s e).encode
          (matrix id t w q r d u f).encode) := certificate_correct _

end PASoundness.PAtoCompactTermAtomGeneralMatrix

#print axioms PASoundness.PAtoCompactTermAtomGeneralMatrix.matrix_of_graph_rebased
#print axioms PASoundness.PAtoCompactTermAtomGeneralMatrix.matrix_of_graph_rebased_certificate
