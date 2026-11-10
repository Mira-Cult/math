import PASoundness.PAtoCompactProductMatchPathOrderPoint
import PASoundness.PAtoCompactProductMatchRelation
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactSuccGraphOutputLift

/-! Order preservation for two existential product-matching paths. The two
product matrices, two factor-order clauses, first factor bijection and both
source-output membership guards remain explicit. This is not yet the
quantified order clause for the represented matching graph. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchPathOrder

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactScopedActiveReplace
open PASoundness.PAtoCompactSuccGraphOutputLift PASoundness.PAtoCompactProductIsoPointwiseLex
open PASoundness.PAtoCompactProductMatchSourceWitness (retainedMatchBody)
open PASoundness.PAtoCompactProductMatchPathUnique
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactProductMatchPathOrderPoint

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def otherPath : Formula := .ex 50 (.ex 51 (.ex 53 (.ex 54 otherBody)))
def otherInput : Formula := replace 32 52 (replace 35 55 path)
def result : Formula := namedBoth (.imp (.member 52 32) (.member 55 35))
  (.imp (.member 55 35) (.member 52 32))

theorem other_path_shape : replace 32 52 rivalPath = otherPath := by decide

/-- The second matching path can be moved to distinct private witness names
without changing either output variable. -/
def other_path_forward : KDerivation (imp otherInput.encode otherPath.encode) := by
  have h := replace_implications 32 52 (replace 35 55 path) rivalPath
    (by decide) (by decide) (by decide) (by decide) rival_alpha.forward rival_alpha.backward
  have hr := h.1
  rw [other_path_shape] at hr
  exact hr

/-- Eliminate both sets of local path witnesses to obtain pointwise order
preservation/reflection between the two source and target outputs. -/
def path_order : KDerivation (imp guard.encode (imp path.encode
    (imp otherInput.encode (iffCode (member 52 32) (member 55 35))))) := by
  let E := result.encode
  let G := guard.encode
  let R := retainedMatchBody.encode
  let O := otherBody.encode
  let H : Formula := namedBoth guard retainedMatchBody
  have hpoint : KDerivation (imp H.encode (imp O E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,H.encode]
    have ho : Context Γ O := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hh' : Context Γ (both G R) := by
      simpa [H, G, R, namedBoth, Formula.not, Formula.encode, both, neg] using hh
    have hg := Context.conjunctionLeft hh'
    have hr := Context.conjunctionRight hh'
    have h := Context.mp ho (Context.mp hr (Context.mp hg (.closed path_point_order)))
    simpa [E, result, iffCode, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have ho54 := guarded_exists_left 54 H.encode O E
    (H.vacuity 54 (by decide)) (result.vacuity 54 (by decide)) hpoint
  have ho53 := guarded_exists_left 53 H.encode (existsCode 54 O) E
    (H.vacuity 53 (by decide)) (result.vacuity 53 (by decide)) ho54
  have ho51 := guarded_exists_left 51 H.encode (existsCode 53 (existsCode 54 O)) E
    (H.vacuity 51 (by decide)) (result.vacuity 51 (by decide)) ho53
  have ho50 := guarded_exists_left 50 H.encode (existsCode 51 (existsCode 53 (existsCode 54 O))) E
    (H.vacuity 50 (by decide)) (result.vacuity 50 (by decide)) ho51
  let K : Formula := namedBoth guard otherPath
  have hsecond : KDerivation (imp K.encode (imp R E)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [R,K.encode]
    have hr : Context Γ R := .head _ _
    have hk : Context Γ K.encode := .hypothesis (by simp [Γ])
    have hk' : Context Γ (both G otherPath.encode) := by
      simpa [K, G, namedBoth, Formula.not, Formula.encode, both, neg] using hk
    have hg := Context.conjunctionLeft hk'
    have ho := Context.conjunctionRight hk'
    have hh : Context Γ H.encode := by
      have h := Context.conjunctionIntro hg hr
      simpa [H, G, R, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have h := Context.mp ho (Context.mp hh (.closed ho50))
    simpa [Γ, otherPath, O, Formula.encode] using h
  have hs34 := guarded_exists_left 34 K.encode R E
    (K.vacuity 34 (by decide)) (result.vacuity 34 (by decide)) hsecond
  have hs33 := guarded_exists_left 33 K.encode (existsCode 34 R) E
    (K.vacuity 33 (by decide)) (result.vacuity 33 (by decide)) hs34
  have hs31 := guarded_exists_left 31 K.encode (existsCode 33 (existsCode 34 R)) E
    (K.vacuity 31 (by decide)) (result.vacuity 31 (by decide)) hs33
  have hs30 := guarded_exists_left 30 K.encode (existsCode 31 (existsCode 33 (existsCode 34 R))) E
    (K.vacuity 30 (by decide)) (result.vacuity 30 (by decide)) hs31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherInput.encode,path.encode,G]
  have ho : Context Γ otherInput.encode := .head _ _
  have hp : Context Γ path.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ho' : Context Γ otherPath.encode := .mp ho (.closed other_path_forward)
  have hk : Context Γ K.encode := by
    have h := Context.conjunctionIntro hg ho'
    simpa [K, G, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have h := Context.mp hp (Context.mp hk (.closed hs30))
  simpa [Γ, path, R, E, result, iffCode, namedBoth, Formula.not, Formula.encode, both, neg] using h

theorem path_order_certificate : theoremCode (certificate path_order) =
    imp guard.encode (imp path.encode (imp otherInput.encode
      (iffCode (member 52 32) (member 55 35)))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchPathOrder

#print axioms PASoundness.PAtoCompactProductMatchPathOrder.other_path_forward
#print axioms PASoundness.PAtoCompactProductMatchPathOrder.path_order
#print axioms PASoundness.PAtoCompactProductMatchPathOrder.path_order_certificate
