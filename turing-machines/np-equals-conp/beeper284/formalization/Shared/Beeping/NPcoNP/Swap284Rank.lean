import Shared.Beeping.NPcoNP.Swap284Steps

/-! Exact first-exit time for the abstract six-row graph. This rank does not
yet identify the graph with the producer's grammar or the binary table. -/

namespace Shared.Beeping.NPcoNP.Swap284Steps

def rank {α : Type} (c : Config α) : Nat :=
  match c.pc with
  | .testL => 4*c.left+2*c.right+2*c.work+3
  | .incQ => 4*c.left+2*c.right+2*c.work+6
  | .testR => 2*c.right+2*c.work+2
  | .incL => 2*c.right+2*c.work+3
  | .testQ => 2*c.work+1
  | .incR => 2*c.work+2
  | .exit => 0

theorem rank_step {α : Type} (c : Config α) : rank (step c) = rank c - 1 := by
  rcases c with ⟨pc,l,r,q,o⟩
  cases pc <;> cases l <;> cases r <;> cases q <;> simp_all [rank,step] <;> omega

theorem rank_iter {α : Type} (c : Config α) (n : Nat) :
    rank ((step^[n]) c) = rank c - n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', rank_step, ih]
    omega

theorem no_early_exit {α : Type} (l r q t : Nat) (o : α)
    (h : t < 4*l+2*r+2*q+3) :
    ((step^[t]) (cfg .testL l r q o)).pc ≠ .exit := by
  intro he
  have hr := rank_iter (cfg .testL l r q o) t
  have hz : rank ((step^[t]) (cfg .testL l r q o)) = 0 := by
    simp [rank,he]
  rw [hz] at hr
  simp only [cfg,rank] at hr
  omega

/-- Together with `swap_run`, this proves the first exit is exactly at the
advertised count from a zero-work external entry. -/
theorem swap_no_early_exit {α : Type} (l r t : Nat) (o : α)
    (h : t < 4*l+2*r+3) :
    ((step^[t]) (cfg .testL l r 0 o)).pc ≠ .exit := by
  apply no_early_exit l r 0 t o
  simpa using h

end Shared.Beeping.NPcoNP.Swap284Steps
