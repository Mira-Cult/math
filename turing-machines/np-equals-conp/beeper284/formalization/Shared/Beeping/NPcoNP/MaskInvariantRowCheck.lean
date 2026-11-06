import Shared.Beeping.NPcoNP.MaskInvariantCheck

/-! Per-state form of the finite Boolean mask-closure check. This permits
kernel checking to be split into separately audited row proofs; it does not
assert any particular source program or certificate. -/
namespace Shared.Beeping.NPcoNP.MaskInvariant

/-- The two branches and every register are checked for a single state. -/
def rowCheck {registers states : Nat} (p : Program registers states)
    (m : Fin states → MaskBank registers) (s : Fin states) : Bool :=
  [false, true].all fun branch =>
    if enabledCheck p.code[s].action branch (m s) then
      (List.finRange registers).all fun q =>
        decide (image p.code[s].action branch (m s) q ⊆
          m (if branch then p.code[s].yes else p.code[s].no) q)
    else true

theorem closedCheck_eq_all_rowCheck {registers states : Nat}
    (p : Program registers states) (m : Fin states → MaskBank registers) :
    closedCheck p m = (List.finRange states).all (rowCheck p m) := rfl

/-- A separately kernel-checked successful result for each row gives the
global inductive invariant. No native computation is used in this theorem. -/
theorem closed_of_all_rowCheck {registers states : Nat}
    (p : Program registers states) (m : Fin states → MaskBank registers)
    (h : ∀ s, rowCheck p m s = true) : Closed p m := by
  apply closed_of_closedCheck p m
  rw [closedCheck_eq_all_rowCheck]
  apply List.all_eq_true.mpr
  intro s _
  exact h s

end Shared.Beeping.NPcoNP.MaskInvariant
