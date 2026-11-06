import Shared.Beeping.NPcoNP.Source284LoaderAlgebra

/-! A finite two-stack transfer is reversible after swapping the halves.
This is arithmetic on arbitrary natural tape halves, including virtual high
zeroes; no source transition table or physical machine is asserted here. -/
namespace Shared.Beeping.NPcoNP.Source284TransferInvolution

open Shared.Beeping.NPcoNP.Source284LoaderAlgebra (transfer)

/-- Splitting a transfer into two consecutive finite segments. -/
theorem transfer_add (n m left right : Nat) :
    transfer (n+m) left right =
      (let p := transfer n left right; transfer m p.1 p.2) := by
  induction n generalizing left right with
  | zero => simp [transfer]
  | succ n ih =>
      simpa [Nat.succ_add, transfer] using
        ih (2*left+right%2) (right/2)

/-- Swapping the output halves and reversing exactly the same number of
transfers restores the two original arbitrary natural-number halves. -/
theorem transfer_involution (n left right : Nat) :
    transfer n (transfer n left right).2 (transfer n left right).1 = (right,left) := by
  induction n generalizing left right with
  | zero => rfl
  | succ n ih =>
      let nextLeft := 2*left+right%2
      let nextRight := right/2
      have h := ih nextLeft nextRight
      rw [show n+1=n+1 from rfl, transfer_add]
      change transfer 1 (transfer n (transfer n nextLeft nextRight).2
        (transfer n nextLeft nextRight).1).1
        (transfer n (transfer n nextLeft nextRight).2
          (transfer n nextLeft nextRight).1).2 = (right,left)
      rw [h]
      simp only [transfer]
      dsimp [nextLeft, nextRight]
      have hm := Nat.mod_lt right (by decide : 0 < 2)
      have hd := Nat.mod_add_div right 2
      congr 1 <;> omega

end Shared.Beeping.NPcoNP.Source284TransferInvolution
