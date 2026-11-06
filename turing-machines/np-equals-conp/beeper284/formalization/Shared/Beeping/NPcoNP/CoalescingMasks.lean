import Shared.Beeping.NPcoNP.CoalescingActions

/-! Bridge from a sound finite mask invariant to the per-operation ownership
condition required by register coalescing. Concrete mask and row certificates
remain separate obligations. -/

namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.AbstractMasks
open Shared.Beeping.NPcoNP.MaskInvariant

def MaskExclusive {n m : Nat} (f : Fin n → Fin m) (masks : MaskBank n)
    (r : Fin n) : Prop :=
  ∀ i, f i = f r → i ≠ r → masks i ⊆ {Category.zero}

theorem exclusive_of_masks {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (masks : MaskBank n) (r : Fin n) (hcover : Covers masks b)
    (hmask : MaskExclusive f masks r) : Exclusive f b r := by
  intro i hi hne
  exact only_zero (hmask i hi hne (hcover i))

def MaskAccessOK {n m : Nat} (f : Fin n → Fin m) (masks : MaskBank n) :
    Action n → Prop
  | .base (.inc r) => MaskExclusive f masks r
  | .base (.decNZ r) => MaskExclusive f masks r
  | .base (.emit _) => True
  | .half r => MaskExclusive f masks r

theorem accessOK_of_masks {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (masks : MaskBank n) (a : Action n) (hcover : Covers masks b)
    (hmask : MaskAccessOK f masks a) : AccessOK f b a := by
  cases a with
  | half r => exact exclusive_of_masks f b masks r hcover hmask
  | base a =>
    cases a with
    | inc r => exact exclusive_of_masks f b masks r hcover hmask
    | decNZ r => exact exclusive_of_masks f b masks r hcover hmask
    | emit bit => trivial

/-- If the mask table is inductive, covers the blank start, and guarantees
exclusive ownership at every source row, then every actual source step has
the ownership condition required by `translate_execute`. -/
theorem accessOK_on_run {n m states : Nat} (f : Fin n → Fin m)
    (p : MaskInvariant.Program n states) (masks : Fin states → MaskBank n)
    (hclosed : Closed p masks) (hinit : Covers (masks p.start) (fun _ => 0))
    (howners : ∀ s, MaskAccessOK f (masks s) p.code[s].action) (t : Nat) :
    AccessOK f (p.system.run t).bank p.code[(p.system.run t).state].action := by
  exact accessOK_of_masks f _ _ _ (closed_run p masks hclosed hinit t)
    (howners (p.system.run t).state)

end Shared.Beeping.NPcoNP.CoalescingAlgebra
