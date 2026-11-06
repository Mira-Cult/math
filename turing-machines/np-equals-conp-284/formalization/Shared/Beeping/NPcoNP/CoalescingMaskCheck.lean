import Shared.Beeping.NPcoNP.CoalescingMasks

/-! Executable per-row ownership check. Success provides the mathematical
mask-side ownership condition, not any producer or physical-table binding. -/
namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open Shared.Beeping.NPcoNP.AbstractMasks
open Shared.Beeping.NPcoNP.MaskInvariant

def ownerCheck {n m : Nat} (f : Fin n → Fin m) (masks : MaskBank n)
    (r : Fin n) : Bool :=
  (List.finRange n).all fun i =>
    decide (f i ≠ f r ∨ i = r ∨ masks i ⊆ {Category.zero})

def maskAccessCheck {n m : Nat} (f : Fin n → Fin m) (masks : MaskBank n) :
    Action n → Bool
  | .base (.inc r) => ownerCheck f masks r
  | .base (.decNZ r) => ownerCheck f masks r
  | .base (.emit _) => true
  | .half r => ownerCheck f masks r

theorem maskExclusive_of_ownerCheck {n m : Nat} (f : Fin n → Fin m)
    (masks : MaskBank n) (r : Fin n) (h : ownerCheck f masks r = true) :
    MaskExclusive f masks r := by
  intro i hi hne
  have hrow := (List.all_eq_true.mp h) i (List.mem_finRange i)
  have hp := of_decide_eq_true hrow
  rcases hp with hnot | heq | hsub
  · exact False.elim (hnot hi)
  · exact False.elim (hne heq)
  · exact hsub

theorem maskAccessOK_of_check {n m : Nat} (f : Fin n → Fin m)
    (masks : MaskBank n) (a : Action n) (h : maskAccessCheck f masks a = true) :
    MaskAccessOK f masks a := by
  cases a with
  | half r => exact maskExclusive_of_ownerCheck f masks r h
  | base a =>
    cases a with
    | inc r => exact maskExclusive_of_ownerCheck f masks r h
    | decNZ r => exact maskExclusive_of_ownerCheck f masks r h
    | emit bit => trivial

end Shared.Beeping.NPcoNP.CoalescingAlgebra
