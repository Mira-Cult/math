import Shared.Beeping.NPcoNP.CoalescingAlgebra
import Shared.Beeping.NPcoNP.MaskInvariant

/-! Single-instruction semantic preservation for register coalescing. It
assumes exclusive ownership of the addressed carrier at the source step; it
does not prove that property for any concrete program or reachable run. -/

namespace Shared.Beeping.NPcoNP.CoalescingAlgebra
open PASoundness.RegisterMachine
open Shared.Beeping.NPcoNP.MaskInvariant

def translate {n m : Nat} (f : Fin n → Fin m) : Action n → Action m
  | .base (.inc r) => .base (.inc (f r))
  | .base (.decNZ r) => .base (.decNZ (f r))
  | .base (.emit bit) => .base (.emit bit)
  | .half r => .half (f r)

def AccessOK {n m : Nat} (f : Fin n → Fin m) (b : Bank n) : Action n → Prop
  | .base (.inc r) => Exclusive f b r
  | .base (.decNZ r) => Exclusive f b r
  | .base (.emit _) => True
  | .half r => Exclusive f b r

theorem translate_execute {n m : Nat} (f : Fin n → Fin m) (b : Bank n)
    (a : Action n) (h : AccessOK f b a) :
    (translate f a).execute (pack f b) =
      let o := a.execute b
      ⟨pack f o.bank, o.success, o.output⟩ := by
  cases a with
  | half r =>
    change Exclusive f b r at h
    simp only [translate, Action.execute]
    rw [read_of_exclusive f b r h, pack_write_of_exclusive f b r (b r / 2) h]
  | base a =>
    cases a with
    | inc r =>
      change Exclusive f b r at h
      simp only [translate, Action.execute, PASoundness.RegisterMachine.execute]
      rw [read_of_exclusive f b r h, pack_write_of_exclusive f b r (b r + 1) h]
    | decNZ r =>
      change Exclusive f b r at h
      simp only [translate, Action.execute, PASoundness.RegisterMachine.execute]
      rw [read_of_exclusive f b r h]
      cases hb : b r with
      | zero => simp [hb]
      | succ k => simp [hb, pack_write_of_exclusive f b r k h]
    | emit bit => rfl

end Shared.Beeping.NPcoNP.CoalescingAlgebra
