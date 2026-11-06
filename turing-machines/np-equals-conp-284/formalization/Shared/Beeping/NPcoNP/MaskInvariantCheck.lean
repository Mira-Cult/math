import Shared.Beeping.NPcoNP.MaskInvariant

/-! A finite Boolean certificate checker for the mask invariant. This file
does not identify a producer program, table or particular certificate. -/
namespace Shared.Beeping.NPcoNP.MaskInvariant
open Shared.Beeping.NPcoNP.AbstractMasks
open PASoundness.RegisterMachine

/-- An executable guard for all sources and selected action branch. -/
def enabledCheck {registers : Nat} (a : Action registers) (b : Bool)
    (m : MaskBank registers) : Bool :=
  (List.finRange registers).all (fun q => decide (m q).Nonempty) &&
    match a with
    | .base (.inc _) => b
    | .base (.decNZ r) => decide (image a b m r).Nonempty
    | .base (.emit _) => b
    | .half r => decide (image a b m r).Nonempty

def closedCheck {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) : Bool :=
  (List.finRange states).all fun s =>
    [false, true].all fun branch =>
      if enabledCheck p.code[s].action branch (m s) then
        (List.finRange registers).all fun q =>
          decide (image p.code[s].action branch (m s) q ⊆
            m (if branch then p.code[s].yes else p.code[s].no) q)
      else true

theorem enabledCheck_of_enabled {registers : Nat} (a : Action registers)
    (branch : Bool) (m : MaskBank registers) (h : Enabled a branch m) :
    enabledCheck a branch m = true := by
  rcases h with ⟨hall, hbranch⟩
  unfold enabledCheck
  simp only [Bool.and_eq_true]
  constructor
  · apply List.all_eq_true.mpr
    intro q _
    exact decide_eq_true (hall q)
  · cases a with
    | half r => exact decide_eq_true hbranch
    | base op =>
      cases op with
      | inc r => exact hbranch
      | decNZ r => exact decide_eq_true hbranch
      | emit bit => exact hbranch

theorem closed_of_closedCheck {registers states : Nat}
    (p : Program registers states) (m : Fin states → MaskBank registers)
    (h : closedCheck p m = true) : Closed p m := by
  intro s branch henabled q
  have hs := (List.all_eq_true.mp h) s (List.mem_finRange s)
  have hb := (List.all_eq_true.mp hs) branch (by cases branch <;> simp)
  have he := enabledCheck_of_enabled _ _ _ henabled
  simp only [he, if_true] at hb
  have hq := (List.all_eq_true.mp hb) q (List.mem_finRange q)
  exact of_decide_eq_true hq

end Shared.Beeping.NPcoNP.MaskInvariant
