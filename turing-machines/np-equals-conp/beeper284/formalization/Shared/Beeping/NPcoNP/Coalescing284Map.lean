import Mathlib.Tactic

/-! Finite index arithmetic for the 284 producer's reported bank sharing.
These literal maps are not yet proved equal to the external coalescence
certificate, source grammar, or physical tape allocation. `suffix` uses the
numeric suffix of `$coalesced.i`; `array` uses the actual position in the
12-element grammar `registers` array. -/
namespace Shared.Beeping.NPcoNP.Coalescing284Map

/-- Map a grammar-array position to its coalesced-name suffix. -/
def arrayToSuffix : Fin 12 → Fin 12 := ![9,0,1,2,3,4,5,6,7,8,10,11]

/-- The inverse index conversion, from suffix to grammar-array position. -/
def suffixToArray : Fin 12 → Fin 12 := ![1,2,3,4,5,6,7,8,9,0,10,11]

/-- Map the 15 logical register indices to coalesced-name suffixes. -/
def logicalToSuffix : Fin 15 → Fin 12 :=
  ![9,0,1,2,9,11,10,3,4,10,5,6,7,8,11]

/-- The same mapping, in the producer's grammar-array indexing. -/
def logicalToArray : Fin 15 → Fin 12 :=
  ![0,1,2,3,0,11,10,4,5,10,6,7,8,9,11]

theorem suffix_array_inverse : ∀ i, arrayToSuffix (suffixToArray i) = i := by decide
theorem array_suffix_inverse : ∀ i, suffixToArray (arrayToSuffix i) = i := by decide
theorem logical_maps_agree : ∀ i, arrayToSuffix (logicalToArray i) = logicalToSuffix i := by decide
theorem logical_maps_agree_inverse : ∀ i, suffixToArray (logicalToSuffix i) = logicalToArray i := by decide

theorem shared_fiber9 : ∀ i, logicalToSuffix i = 9 ↔ i = 0 ∨ i = 4 := by decide
theorem shared_fiber10 : ∀ i, logicalToSuffix i = 10 ↔ i = 6 ∨ i = 9 := by decide
theorem shared_fiber11 : ∀ i, logicalToSuffix i = 11 ↔ i = 5 ∨ i = 14 := by decide

/-- The logical work and temporary register share suffix 10, while the
swap's left and right operands are suffixes 8 and 1. -/
theorem swap_registers :
    logicalToSuffix 6 = 10 ∧ logicalToSuffix 9 = 10 ∧
    logicalToSuffix 13 = 8 ∧ logicalToSuffix 2 = 1 := by decide

end Shared.Beeping.NPcoNP.Coalescing284Map
