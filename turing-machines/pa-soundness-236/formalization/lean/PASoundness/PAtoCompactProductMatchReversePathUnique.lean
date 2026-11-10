import PASoundness.PAtoCompactProductMatchReversePointUnique
import PASoundness.PAtoCompactProductMatchPathOrder
import PASoundness.PAtoCompactProductMatchReverseTotality

/-! Eliminate private witnesses from two paths sharing one target. Both
product matrices, factor bijections and endpoint memberships remain guards. -/
set_option maxRecDepth 262144
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactProductMatchReversePathUnique

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactSuccGraphOutputLift
open PASoundness.PAtoCompactProductMatchRelation PASoundness.PAtoCompactProductMatchPathOrderPoint
open PASoundness.PAtoCompactProductMatchPathOrder PASoundness.PAtoCompactProductMatchReverseReconstruct
open PASoundness.PAtoCompactProductMatchReverseTotality PASoundness.PAtoCompactProductMatchReversePointUnique

attribute [local irreducible] CompactProof.imp Cantor.pair Cantor.triangle

def firstInput : Formula := replace 35 55 path

def reverse_path_unique : KDerivation (imp assumptions.encode (imp firstInput.encode
    (imp otherInput.encode (equal 32 52)))) := by
  let E : Formula := .equal 32 52
  let G := assumptions.encode
  let R := pathBody55.encode
  let O := otherBody.encode
  let H : Formula := namedBoth assumptions pathBody55
  have hpoint : KDerivation (imp H.encode (imp O E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [O,H.encode]
    have ho : Context Γ O := .head _ _
    have hh : Context Γ H.encode := .hypothesis (by simp [Γ])
    have hh' : Context Γ (both G R) := by
      simpa [H, G, R, namedBoth, Formula.not, Formula.encode, both, neg] using hh
    have h := Context.mp ho (Context.mp (Context.conjunctionRight hh')
      (Context.mp (Context.conjunctionLeft hh') (.closed reverse_point_unique)))
    simpa [Γ, E, Formula.encode] using h
  have ho54 := guarded_exists_left 54 H.encode O E.encode
    (H.vacuity 54 (by decide)) (E.vacuity 54 (by decide)) hpoint
  have ho53 := guarded_exists_left 53 H.encode (existsCode 54 O) E.encode
    (H.vacuity 53 (by decide)) (E.vacuity 53 (by decide)) ho54
  have ho51 := guarded_exists_left 51 H.encode (existsCode 53 (existsCode 54 O)) E.encode
    (H.vacuity 51 (by decide)) (E.vacuity 51 (by decide)) ho53
  have ho50 := guarded_exists_left 50 H.encode (existsCode 51 (existsCode 53 (existsCode 54 O))) E.encode
    (H.vacuity 50 (by decide)) (E.vacuity 50 (by decide)) ho51
  let K : Formula := namedBoth assumptions otherPath
  have hsecond : KDerivation (imp K.encode (imp R E.encode)) := by
    apply Context.closeEmpty
    apply Context.deduction
    apply Context.deduction
    let Γ := [R,K.encode]
    have hr : Context Γ R := .head _ _
    have hk : Context Γ K.encode := .hypothesis (by simp [Γ])
    have hk' : Context Γ (both G otherPath.encode) := by
      simpa [K, G, namedBoth, Formula.not, Formula.encode, both, neg] using hk
    have hh : Context Γ H.encode := by
      have h := Context.conjunctionIntro (Context.conjunctionLeft hk') hr
      simpa [H, G, R, namedBoth, Formula.not, Formula.encode, both, neg] using h
    have h := Context.mp (Context.conjunctionRight hk') (Context.mp hh (.closed ho50))
    simpa [Γ, otherPath, O, Formula.encode] using h
  have hs34 := guarded_exists_left 34 K.encode R E.encode
    (K.vacuity 34 (by decide)) (E.vacuity 34 (by decide)) hsecond
  have hs33 := guarded_exists_left 33 K.encode (existsCode 34 R) E.encode
    (K.vacuity 33 (by decide)) (E.vacuity 33 (by decide)) hs34
  have hs31 := guarded_exists_left 31 K.encode (existsCode 33 (existsCode 34 R)) E.encode
    (K.vacuity 31 (by decide)) (E.vacuity 31 (by decide)) hs33
  have hs30 := guarded_exists_left 30 K.encode (existsCode 31 (existsCode 33 (existsCode 34 R))) E.encode
    (K.vacuity 30 (by decide)) (E.vacuity 30 (by decide)) hs31
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let Γ := [otherInput.encode,firstInput.encode,G]
  have ho : Context Γ otherInput.encode := .head _ _
  have hp : Context Γ firstInput.encode := .hypothesis (by simp [Γ])
  have hg : Context Γ G := .hypothesis (by simp [Γ])
  have ho' : Context Γ otherPath.encode := .mp ho (.closed other_path_forward)
  have hk : Context Γ K.encode := by
    have h := Context.conjunctionIntro hg ho'
    simpa [K, G, namedBoth, Formula.not, Formula.encode, both, neg] using h
  have hp' : Context Γ (existsCode 30 (existsCode 31 (existsCode 33 (existsCode 34 R)))) := by
    simpa [firstInput, path_at_55_shape, R, Formula.encode] using hp
  simpa [Γ, E, Formula.encode] using Context.mp hp' (Context.mp hk (.closed hs30))

theorem reverse_path_unique_certificate : theoremCode (certificate reverse_path_unique) =
    imp assumptions.encode (imp firstInput.encode (imp otherInput.encode (equal 32 52))) := certificate_correct _

end PASoundness.PAtoCompactProductMatchReversePathUnique

#print axioms PASoundness.PAtoCompactProductMatchReversePathUnique.reverse_path_unique
#print axioms PASoundness.PAtoCompactProductMatchReversePathUnique.reverse_path_unique_certificate
