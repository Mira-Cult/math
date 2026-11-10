import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactMapNamesCongr

/-! Literal syntactic transport of finite templates across allocator blocks.
No K-level alpha equivalence or semantic transport is claimed here. -/
namespace PASoundness.PAtoCompactTemplateBlockShift

open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactGuardElimination
open PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactOrderIsomorphism PASoundness.PAtoCompactOrdinalAddition
open PASoundness.PAtoCompactMultiplicationCandidate

theorem oneMap_shift (a : Formula) (p x b c : Nat) (g : Nat → Nat)
    (ha : a.names ⊆ Finset.range 38)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (mapNames (oneMap b p x) a) =
      mapNames (oneMap c p (g x)) a := by
  rw [mapNames_compose]
  apply mapNames_congr
  intro z hz
  have hbound : z < 38 := Finset.mem_range.mp (ha hz)
  by_cases hp : z = p
  · simp only [Function.comp_apply, oneMap, if_pos hp]
  · simp only [Function.comp_apply, oneMap, if_neg hp]
    simpa [Nat.add_assoc] using hg (2 + z) (by omega)

theorem twoMap_shift (a : Formula) (p q x y b c : Nat) (g : Nat → Nat)
    (ha : a.names ⊆ Finset.range 38)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (mapNames (twoMap b p q x y) a) =
      mapNames (twoMap c p q (g x) (g y)) a := by
  rw [mapNames_compose]
  apply mapNames_congr
  intro z hz
  have hbound : z < 38 := Finset.mem_range.mp (ha hz)
  by_cases hp : z = p
  · simp only [Function.comp_apply, twoMap, if_pos hp]
  · by_cases hq : z = q
    · simp only [Function.comp_apply, twoMap, if_neg hp, if_pos hq]
    · simp only [Function.comp_apply, twoMap, if_neg hp, if_neg hq]
      simpa [Nat.add_assoc] using hg (2 + z) (by omega)

theorem threeMap_shift (a : Formula) (p q r x y z b c : Nat) (g : Nat → Nat)
    (ha : a.names ⊆ Finset.range 38)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (mapNames (threeMap b p q r x y z) a) =
      mapNames (threeMap c p q r (g x) (g y) (g z)) a := by
  rw [mapNames_compose]
  apply mapNames_congr
  intro w hw
  have hbound : w < 38 := Finset.mem_range.mp (ha hw)
  by_cases hp : w = p
  · simp only [Function.comp_apply, threeMap, if_pos hp]
  · by_cases hq : w = q
    · simp only [Function.comp_apply, threeMap, if_neg hp, if_pos hq]
    · by_cases hr : w = r
      · simp only [Function.comp_apply, threeMap, if_neg hp, if_neg hq, if_pos hr]
      · simp only [Function.comp_apply, threeMap, if_neg hp, if_neg hq, if_neg hr]
        simpa [Nat.add_assoc] using hg (2 + w) (by omega)

theorem domainAt_shift (g : Nat → Nat) (b c x : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (domainAt b x) = domainAt c (g x) :=
  oneMap_shift _ _ _ _ _ _ templates_names_bounded.1 hg

theorem equivAt_shift (g : Nat → Nat) (b c x y : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (equivAt b x y) = equivAt c (g x) (g y) :=
  twoMap_shift _ _ _ _ _ _ _ _ templates_names_bounded.2.1 hg

theorem zeroAt_shift (g : Nat → Nat) (b c x : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (zeroAt b x) = zeroAt c (g x) :=
  oneMap_shift _ _ _ _ _ _ templates_names_bounded.2.2.1 hg

theorem succAt_shift (g : Nat → Nat) (b c x y : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (succAt b x y) = succAt c (g x) (g y) :=
  twoMap_shift _ _ _ _ _ _ _ _ templates_names_bounded.2.2.2.1 hg

theorem addAt_shift (g : Nat → Nat) (b c x y z : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (addAt b x y z) = addAt c (g x) (g y) (g z) :=
  threeMap_shift _ _ _ _ _ _ _ _ _ _ templates_names_bounded.2.2.2.2.1 hg

theorem mulAt_shift (g : Nat → Nat) (b c x y z : Nat)
    (hg : ∀ i < 64, g (b + i) = c + i) :
    mapNames g (mulAt b x y z) = mulAt c (g x) (g y) (g z) :=
  threeMap_shift _ _ _ _ _ _ _ _ _ _ templates_names_bounded.2.2.2.2.2 hg

end PASoundness.PAtoCompactTemplateBlockShift

#print axioms PASoundness.PAtoCompactTemplateBlockShift.domainAt_shift
#print axioms PASoundness.PAtoCompactTemplateBlockShift.equivAt_shift
#print axioms PASoundness.PAtoCompactTemplateBlockShift.zeroAt_shift
#print axioms PASoundness.PAtoCompactTemplateBlockShift.succAt_shift
#print axioms PASoundness.PAtoCompactTemplateBlockShift.addAt_shift
#print axioms PASoundness.PAtoCompactTemplateBlockShift.mulAt_shift
