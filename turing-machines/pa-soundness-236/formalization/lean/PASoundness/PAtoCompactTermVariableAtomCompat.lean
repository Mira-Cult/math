import PASoundness.PAtoCompactVacuousEqualityAlignment
import PASoundness.PAtoCompactSuccTermTotality
import PASoundness.PAtoCompactEquivMultiAlpha

/-! One shared term-graph witness can supply the substituted term in an
atomic equality.  The result is a matrix-level finite K construction; the
indicated transitivity proof remains an explicit input. -/
namespace PASoundness.PAtoCompactTermVariableAtomCompat

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactScopedEqualityReplace
open PASoundness.PAtoCompactVacuousEqualityAlignment PASoundness.PAtoCompactSuccTermTotality
open PASoundness.PAtoCompactAllTermTransport PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactEquivMultiAlpha

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- A graph value for t, the two source value graphs and the source
equivalence give the target equality matrix.  The term t is arbitrary, and
its graph need not have a unique value. -/
noncomputable def matrix_of_graph (t : Peano.Term) (q z a r b : Nat)
    (trans : KDerivation (imp (domainAt b q).encode
      (imp (equivAt b q a).encode (imp (equivAt b a r).encode (equivAt b q r).encode)))) :
    KDerivation (imp (termGraph id t q b).encode
      (imp (termGraph id (.var q) a b).encode
        (imp (termGraph id (.var z) r b).encode
          (imp (equivAt b a r).encode
            (matrix id t (.var z) q r b b b).encode)))) := by
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let T := (termGraph id t q b).encode
  let V := (termGraph id (.var q) a b).encode
  let Z := (termGraph id (.var z) r b).encode
  let E := (equivAt b a r).encode
  let Γ := [E, Z, V, T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hv : Context Γ V := .hypothesis (by simp [Γ])
  have hz : Context Γ Z := .hypothesis (by simp [Γ])
  have he : Context Γ E := Context.head _ _
  have hd : Context Γ (domainAt b q).encode := .mp ht (.closed (termGraph_domain id t q b))
  have hqa : Context Γ (equivAt b q a).encode := by
    change Context Γ (both (domainAt b a).encode (equivAt b q a).encode) at hv
    exact Context.conjunctionRight hv
  have hqr : Context Γ (equivAt b q r).encode :=
    .mp he (.mp hqa (.mp hd (.closed trans)))
  have h := Context.conjunctionIntro ht (Context.conjunctionIntro hz hqr)
  simpa [matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h

/-- The matrix construction also works at the distinct allocator bases used
by source and target equality frames. The transitivity proof is explicit. -/
noncomputable def matrix_of_graph_rebased (t : Peano.Term) (q z a r p s e d u f : Nat)
    (hqD : q < d+2) (hqP : q < p+2) (haP : a < p+2)
    (haE : a < e+2) (hrE : r < e+2)
    (hqF : q < f+2) (haF : a < f+2) (hrF : r < f+2)
    (hrS : r < s) (hrU : r < u) (hzS : z < s) (hzU : z < u)
    (trans : KDerivation (imp (domainAt f q).encode
      (imp (equivAt f q a).encode (imp (equivAt f a r).encode (equivAt f q r).encode)))) :
    KDerivation (imp (termGraph id t q d).encode
      (imp (matrix id (.var q) (.var z) a r p s e).encode
        (matrix id t (.var z) q r d u f).encode)) := by
  have hd := domainAt_transport d f q (by omega) (by omega)
  have hqa := (equivAt_base_alpha p f q a hqP haP hqF haF).forward
  have har := (equivAt_base_alpha e f a r haE hrE haF hrF).forward
  have hz := (termGraph_base_transport id (.var z) s u r hrS hrU
    (by
      intro v hv
      have he : v = z := by simpa [Term.varFinset] using hv
      simpa [he] using hzS)
    (by
      intro v hv
      have he : v = z := by simpa [Term.varFinset] using hv
      simpa [he] using hzU)).1
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let T := (termGraph id t q d).encode
  let M := (matrix id (.var q) (.var z) a r p s e).encode
  let Γ := [M, T]
  have ht : Context Γ T := .hypothesis (by simp [Γ])
  have hm : Context Γ M := Context.head _ _
  have hm' : Context Γ (both (termGraph id (.var q) a p).encode
      (both (termGraph id (.var z) r s).encode (equivAt e a r).encode)) := by
    simpa [M, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hm
  have hv := Context.conjunctionLeft hm'
  have hp := Context.conjunctionRight hm'
  have hzs := Context.conjunctionLeft hp
  have hars := Context.conjunctionRight hp
  have hv' : Context Γ (both (domainAt p a).encode (equivAt p q a).encode) := by
    simpa [termGraph, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hv
  have hqap : Context Γ (equivAt p q a).encode := Context.conjunctionRight hv'
  have hqaf : Context Γ (equivAt f q a).encode := .mp hqap (.closed hqa)
  have harf : Context Γ (equivAt f a r).encode := .mp hars (.closed har)
  have hzf : Context Γ (termGraph id (.var z) r u).encode := .mp hzs (.closed hz)
  have hdf : Context Γ (domainAt f q).encode := .mp (.mp ht (.closed (termGraph_domain id t q d))) (.closed hd)
  have hqr : Context Γ (equivAt f q r).encode := .mp harf (.mp hqaf (.mp hdf (.closed trans)))
  have h := Context.conjunctionIntro ht (Context.conjunctionIntro hzf hqr)
  simpa [T, M, Γ, matrix, andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using h

theorem matrix_of_graph_certificate (t : Peano.Term) (q z a r b : Nat)
    (trans : KDerivation (imp (domainAt b q).encode
      (imp (equivAt b q a).encode (imp (equivAt b a r).encode (equivAt b q r).encode)))) :
    theoremCode (certificate (matrix_of_graph t q z a r b trans)) =
      imp (termGraph id t q b).encode
      (imp (termGraph id (.var q) a b).encode
        (imp (termGraph id (.var z) r b).encode
          (imp (equivAt b a r).encode (matrix id t (.var z) q r b b b).encode))) :=
  certificate_correct _

end PASoundness.PAtoCompactTermVariableAtomCompat

#print axioms PASoundness.PAtoCompactTermVariableAtomCompat.matrix_of_graph
#print axioms PASoundness.PAtoCompactTermVariableAtomCompat.matrix_of_graph_rebased
#print axioms PASoundness.PAtoCompactTermVariableAtomCompat.matrix_of_graph_certificate
