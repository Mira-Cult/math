import PASoundness.PAtoCompactEquivMultiAlpha
import PASoundness.PAtoCompactGuardBaseTransport
import PASoundness.CompactQuantifiers
import PASoundness.PAtoCompactTermGraphReplace

/-! Proof ingredients for variable term-graph totality. The existence proof
is conditional on an explicit candidate-relative reflexivity derivation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactVariableTermTotality

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open FirstOrder FirstOrder.Language
open PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactEquivMultiAlpha PASoundness.PAtoCompactGuardBaseTransport
open PASoundness.PAtoCompactTermGraphReplace PASoundness.PAtoCompactTermGraphBinderRange

/-- If a capture-safe named instance has a proof, existentially introduce
its bound name. This is a literal finite K proof, not semantic reasoning. -/
def exists_from_instance (x y : Nat) (f : Formula) (hxy : x ≠ y)
    (hx : x ∉ f.binders) (hy : y ∉ f.binders) :
    KDerivation (imp (replace x y f).encode (existsCode x f.encode)) := by
  have hi := universalInstance x y f.not hxy
    (by simpa [CompactNamed.Formula.not, CompactNamed.Formula.binders] using hx)
    (by simpa [CompactNamed.Formula.not, CompactNamed.Formula.binders] using hy)
  have hh := compose (doubleNegIntro (replace x y f).encode) (contrapose hi)
  simpa [CompactNamed.Formula.not, CompactNamed.Formula.encode, replace, existsCode, neg] using hh

/-- A supplied candidate-relative reflexivity proof is transportable to any
other candidate and equivalence private blocks, retaining the operand. -/
def reflexivity_rebase (d e b a : Nat)
    (had : a < d + 32) (hab : a < b + 32)
    (hae : a < e + 2) (hab' : a < b + 2)
    (h : KDerivation (imp (domainAt d a).encode (equivAt e a a).encode)) :
    KDerivation (imp (domainAt b a).encode (equivAt b a a).encode) :=
  compose (domainAt_transport b d a hab had)
    (compose h (equivAt_base_alpha e b a a hae hae hab' hab').forward)

/-- The source itself satisfies the variable graph when the explicit
candidate-relative reflexivity derivation is supplied. -/
def variable_graph_at_source (b a : Nat)
    (h : KDerivation (imp (domainAt b a).encode (equivAt b a a).encode)) :
    KDerivation (imp (domainAt b a).encode
      (andF (domainAt b a) (equivAt b a a)).encode) := by
  apply Context.closeEmpty
  apply Context.deduction
  let D := (domainAt b a).encode
  have hd : Context [D] D := Context.head [] _
  have he : Context [D] (equivAt b a a).encode := .mp hd (.closed h)
  have hc := Context.conjunctionIntro hd he
  simpa [andF, CompactNamed.Formula.not, CompactNamed.Formula.encode, both, neg] using hc

theorem var_replace (b a o : Nat) (ho : o < b) :
    replace o a (andF (domainAt b o) (equivAt b a o)) =
      andF (domainAt b a) (equivAt b a a) := by
  have h := replace_termGraph (fun x : Nat => x) (.var a : Peano.language.Term Nat) o b o a ho
  simpa only [termGraph, Function.comp_apply, id_eq, rename, if_pos rfl, ite_self,
    ↓reduceIte] using h

theorem var_below_not_binder (b a o x : Nat) (hx : x < b) :
    x ∉ (andF (domainAt b o) (equivAt b a o)).binders := by
  have h := termGraph_below_not_binder (fun x : Nat => x) (.var a : Peano.language.Term Nat)
    o b x hx
  simpa only [termGraph] using h

/-- Under an explicitly supplied K reflexivity proof, the variable graph has
an output: the witness is the source itself. Names are capture-safe. -/
def variable_graph_total (b a o : Nat) (ha : a < b) (ho : o < b) (hoa : o ≠ a)
    (h : KDerivation (imp (domainAt b a).encode (equivAt b a a).encode)) :
    KDerivation (imp (domainAt b a).encode
      (existsCode o (termGraph (fun x : Nat => x) (.var a : Peano.language.Term Nat) o b).encode)) := by
  let f := andF (domainAt b o) (equivAt b a o)
  have hi := exists_from_instance o a f hoa
    (var_below_not_binder b a o o ho) (var_below_not_binder b a o a ha)
  rw [var_replace b a o ho] at hi
  exact compose (variable_graph_at_source b a h) hi

/-- The same variable-graph witness when the supplied reflexivity proof and
the incoming candidate guard use different private blocks. -/
def variable_graph_total_rebased (g d e b a o : Nat)
    (hag : a < g + 32) (had : a < d + 32) (hae : a < e + 2)
    (ha : a < b) (ho : o < b) (hoa : o ≠ a)
    (h : KDerivation (imp (domainAt d a).encode (equivAt e a a).encode)) :
    KDerivation (imp (domainAt g a).encode
      (existsCode o (termGraph (fun x : Nat => x) (.var a : Peano.language.Term Nat) o b).encode)) := by
  have hab : a < b + 32 := by omega
  have hab' : a < b + 2 := by omega
  exact compose (domainAt_transport g b a hag hab)
    (variable_graph_total b a o ha ho hoa (reflexivity_rebase d e b a had hab hae hab' h))

end PASoundness.PAtoCompactVariableTermTotality

#print axioms PASoundness.PAtoCompactVariableTermTotality.exists_from_instance
#print axioms PASoundness.PAtoCompactVariableTermTotality.reflexivity_rebase
#print axioms PASoundness.PAtoCompactVariableTermTotality.variable_graph_at_source
#print axioms PASoundness.PAtoCompactVariableTermTotality.var_replace
#print axioms PASoundness.PAtoCompactVariableTermTotality.var_below_not_binder
#print axioms PASoundness.PAtoCompactVariableTermTotality.variable_graph_total
#print axioms PASoundness.PAtoCompactVariableTermTotality.variable_graph_total_rebased
