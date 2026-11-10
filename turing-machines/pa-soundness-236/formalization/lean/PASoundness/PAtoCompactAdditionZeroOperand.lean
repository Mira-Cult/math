import PASoundness.PAtoCompactAdditionZeroRebased
import PASoundness.PAtoCompactScopedActiveReplace
import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactMapNamesCongr
import PASoundness.PAtoCompactTemplateBlockShift
import PASoundness.PAtoCompactTermGraphBinderRange
import PASoundness.PAtoCompactTermTranslation
/-! Capture-safe simultaneous relabeling of the fixed right-zero witness. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactAdditionZeroOperand

open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactAlphaMapOne
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactMapNamesCongr
open PASoundness.PAtoCompactScopedActiveReplace

theorem simultaneous_syntax (f : Formula) (u v x y : Nat)
    (h30 : 30 ∉ f.binders) (h31 : 31 ∉ f.binders)
    (huB : u ∉ f.binders) (hvB : v ∉ f.binders)
    (huN : u ∉ f.names) (hvN : v ∉ f.names)
    (hu : 31 < u) (huv : u < v) (hxv : x < v) :
    replace v y (replace u x (replace 31 v (replace 30 u f))) =
      mapNames (fun n => if n = 30 then x else if n = 31 then y else n) f := by
  have h31' : 31 ∉ (replace 30 u f).binders := by simpa [replace_binders] using h31
  have hu' : u ∉ (replace 31 v (replace 30 u f)).binders := by simpa [replace_binders] using huB
  have hv' : v ∉ (replace u x (replace 31 v (replace 30 u f))).binders := by simpa [replace_binders] using hvB
  rw [← map_eq_replace v y _ hv', ← map_eq_replace u x _ hu',
      ← map_eq_replace 31 v _ h31', ← map_eq_replace 30 u f h30]
  rw [mapNames_compose, mapNames_compose, mapNames_compose]
  apply mapNames_congr
  intro n hn
  have hnu : n ≠ u := fun h => huN (h ▸ hn)
  have hnv : n ≠ v := fun h => hvN (h ▸ hn)
  have hu30 : u ≠ 30 := by omega
  have hu31 : u ≠ 31 := by omega
  have hv30 : v ≠ 30 := by omega
  have hv31 : v ≠ 31 := by omega
  have hvu : v ≠ u := by omega
  have hxv' : x ≠ v := by omega
  by_cases h : n = 30
  · subst n; simp [Function.comp_apply, rename, hu31, hxv']
  · by_cases h' : n = 31
    · subst n; simp [Function.comp_apply, rename, hvu]
    · simp [Function.comp_apply, rename, h, h', hnu, hnv]

def simultaneous_derivation (f : Formula) (u v x y : Nat)
    (h30 : 30 ∉ f.binders) (h31 : 31 ∉ f.binders)
    (huB : u ∉ f.binders) (hvB : v ∉ f.binders)
    (hxB : x ∉ f.binders) (hyB : y ∉ f.binders)
    (huN : u ∉ f.names) (hvN : v ∉ f.names)
    (hu : 31 < u) (huv : u < v) (hxv : x < v)
    (d : KDerivation f.encode) :
    KDerivation (mapNames (fun n => if n = 30 then x else if n = 31 then y else n) f).encode := by
  have d1 := replace_derivation 30 u f h30 huB d
  have d2 := replace_derivation 31 v _ (by simpa [replace_binders] using h31) (by simpa [replace_binders] using hvB) d1
  have d3 := replace_derivation u x _ (by simpa [replace_binders] using huB) (by simpa [replace_binders] using hxB) d2
  have d4 := replace_derivation v y _ (by simpa [replace_binders] using hvB) (by simpa [replace_binders] using hyB) d3
  rw [simultaneous_syntax f u v x y h30 h31 huB hvB huN hvN hu huv hxv] at d4
  exact d4
namespace M236AddMapOutputDesign
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactMapNamesCongr PASoundness.PAtoCompactTemplateBlockShift

def sigma (x y n : Nat) : Nat := if n = 30 then x else if n = 31 then y else n

theorem fixed_block (x y base : Nat) (hbase : 31 < base) :
    ∀ i < 64, sigma x y (base + i) = base + i := by
  intro i hi
  simp [sigma, show base+i ≠ 30 by omega, show base+i ≠ 31 by omega]

theorem operand_map (x y d z c out : Nat) (hd : 31 < d) (hz : 31 < z)
    (hc : 31 < c) (ho0 : out ≠ 30) (ho1 : out ≠ 31) :
    mapNames (sigma x y)
      (.imp (domainAt d 30) (.imp (zeroAt z 31)
        (.ex out (andF (domainAt d out) (addAt c 30 31 out))))) =
    .imp (domainAt d x) (.imp (zeroAt z y)
        (.ex out (andF (domainAt d out) (addAt c x y out)))) := by
  have hD0 := domainAt_shift (sigma x y) d d 30 (fixed_block x y d hd)
  have hD := domainAt_shift (sigma x y) d d out (fixed_block x y d hd)
  have hZ := zeroAt_shift (sigma x y) z z 31 (fixed_block x y z hz)
  have hA := addAt_shift (sigma x y) c c 30 31 out (fixed_block x y c hc)
  simp [sigma, ho0, ho1] at hD0 hD hZ hA
  simp only [mapNames, mapNames_andF, sigma, ho0, ho1, if_false]
  rw [hD0, hZ, hD, hA]

end M236AddMapOutputDesign

namespace M236AddMapBinders
open PASoundness.CompactNamed PASoundness.PAtoCompactTermTranslation
open PASoundness.PAtoCompactTermGraphBinderRange

def source (d z c out : Nat) : Formula :=
  .imp (domainAt d 30) (.imp (zeroAt z 31)
    (.ex out (andF (domainAt d out) (addAt c 30 31 out))))

theorem outside_binders (d z c out k : Nat)
    (hd : k < d+2) (hz : k < z+2) (hc : k < c+2) (hne : k ≠ out) :
    k ∉ (source d z c out).binders := by
  intro h
  simp only [source, Formula.binders, andF_binders, Finset.mem_union,
    Finset.mem_insert] at h
  rcases h with h | h | h | h | h
  · have hh := domainAt_private d 30 k h; omega
  · have hh := zeroAt_private z 31 k h; omega
  · exact hne h
  · have hh := domainAt_private d out k h; omega
  · have hh := addAt_private c 30 31 out k h; omega

end M236AddMapBinders
namespace M236FreshPair
open PASoundness.CompactNamed

def firstFresh (f : Formula) (x y : Nat) : Nat :=
  max 31 (max (max x y) (f.names.sup id)) + 1

theorem fresh_pair (f : Formula) (x y : Nat) :
    let u := firstFresh f x y
    let v := u + 1
    31 < u ∧ u < v ∧ x < v ∧ u ∉ f.names ∧ v ∉ f.names ∧
      u ∉ f.binders ∧ v ∉ f.binders := by
  dsimp only
  have hsup (z : Nat) (hz : z ∈ f.names) : z ≤ f.names.sup id :=
    Finset.le_sup (f := id) hz
  have hu : firstFresh f x y ∉ f.names := by
    intro h
    have h' := hsup _ h
    unfold firstFresh at h'
    omega
  have hv : firstFresh f x y + 1 ∉ f.names := by
    intro h
    have h' := hsup _ h
    unfold firstFresh at h'
    omega
  refine ⟨?_, by omega, ?_, hu, hv, ?_, ?_⟩
  · unfold firstFresh; omega
  · unfold firstFresh; omega
  · intro h; exact hu (Formula.binders_subset_names f h)
  · intro h; exact hv (Formula.binders_subset_names f h)
end M236FreshPair

namespace M236AddOperandInstantiation
open PASoundness.CompactNamed PASoundness.CompactProof
open PASoundness.PAtoCompactTermTranslation

def instantiated (b out x y : Nat) (hb : 38 ≤ b) (houtlow : 32 < out)
    (houtbound : out < b+2) (hx : x < b+2) (hy : y < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    KDerivation (imp (domainAt b x).encode (imp (zeroAt b y).encode
      (existsCode out (andF (domainAt b out) (addAt b x y out)).encode))) := by
  let f := M236AddMapBinders.source b b b out
  have base : KDerivation f.encode := by
    simpa [f, M236AddMapBinders.source, Formula.encode,
      PASoundness.PAtoCompactAdditionOutputAlpha.body] using
      PASoundness.PAtoCompactAdditionZeroRebased.rebased b out hb houtlow houtbound
  let u := M236FreshPair.firstFresh f x y
  let v := u+1
  have hs := M236FreshPair.fresh_pair f x y
  change 31 < u ∧ u < v ∧ x < v ∧ u ∉ f.names ∧ v ∉ f.names ∧
      u ∉ f.binders ∧ v ∉ f.binders at hs
  rcases hs with ⟨hu, huv, hxv, huN, hvN, huB, hvB⟩
  have h30 : 30 ∉ f.binders := by
    apply M236AddMapBinders.outside_binders b b b out 30 <;> omega
  have h31 : 31 ∉ f.binders := by
    apply M236AddMapBinders.outside_binders b b b out 31 <;> omega
  have hxB : x ∉ f.binders := M236AddMapBinders.outside_binders b b b out x hx hx hx hxo
  have hyB : y ∉ f.binders := M236AddMapBinders.outside_binders b b b out y hy hy hy hyo
  have k := simultaneous_derivation f u v x y h30 h31 huB hvB hxB hyB huN hvN hu huv hxv base
  change KDerivation (mapNames (M236AddMapOutputDesign.sigma x y) f).encode at k
  rw [show f = M236AddMapBinders.source b b b out from rfl,
      M236AddMapBinders.source,
      M236AddMapOutputDesign.operand_map x y b b b out (by omega) (by omega)
        (by omega) (by omega) (by omega)] at k
  exact k
end M236AddOperandInstantiation
theorem instantiated_certificate (b out x y : Nat) (hb : 38 ≤ b) (houtlow : 32 < out)
    (houtbound : out < b+2) (hx : x < b+2) (hy : y < b+2)
    (hxo : x ≠ out) (hyo : y ≠ out) :
    theoremCode (certificate (M236AddOperandInstantiation.instantiated b out x y hb houtlow
      houtbound hx hy hxo hyo)) =
      imp (domainAt b x).encode (imp (zeroAt b y).encode
        (existsCode out (andF (domainAt b out) (addAt b x y out)).encode)) := certificate_correct _

end PASoundness.PAtoCompactAdditionZeroOperand
#print axioms PASoundness.PAtoCompactAdditionZeroOperand.M236AddOperandInstantiation.instantiated
#print axioms PASoundness.PAtoCompactAdditionZeroOperand.instantiated_certificate
