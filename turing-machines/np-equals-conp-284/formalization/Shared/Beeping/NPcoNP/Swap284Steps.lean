import Shared.Beeping.NPcoNP.Swap284

/-! Six-row abstract register control graph from the selected 284-state
producer's `phase_swap/PROOF.md`. One step is one retained INC or DECNZ,
including the unsuccessful zero test. `exit` is an absorbing boundary for
the purpose of this local graph. This model is not yet tied to the producer's
grammar rows, its zero-entry invariant, or the binary machine. -/

namespace Shared.Beeping.NPcoNP.Swap284Steps

inductive PC where
  | testL | incQ | testR | incL | testQ | incR | exit
  deriving DecidableEq, Repr

structure Config (α : Type) where
  pc : PC
  left : Nat
  right : Nat
  work : Nat
  other : α
  deriving DecidableEq, Repr

def step {α : Type} (c : Config α) : Config α :=
  match c.pc with
  | .testL => if c.left = 0 then { c with pc := .testR }
      else { c with pc := .incQ, left := c.left - 1 }
  | .incQ => { c with pc := .testL, work := c.work + 1 }
  | .testR => if c.right = 0 then { c with pc := .testQ }
      else { c with pc := .incL, right := c.right - 1 }
  | .incL => { c with pc := .testR, left := c.left + 1 }
  | .testQ => if c.work = 0 then { c with pc := .exit }
      else { c with pc := .incR, work := c.work - 1 }
  | .incR => { c with pc := .testQ, right := c.right + 1 }
  | .exit => c

def cfg {α : Type} (pc : PC) (l r q : Nat) (other : α) : Config α :=
  ⟨pc, l, r, q, other⟩

theorem first_transfer {α : Type} (l r q : Nat) (o : α) :
    (step^[2*l+1]) (cfg .testL l r q o) = cfg .testR 0 r (q+l) o := by
  induction l generalizing q with
  | zero => simp [cfg, step, Function.iterate_succ_apply]
  | succ n ih =>
    have hn : 2 * (n + 1) + 1 = (2*n+1)+2 := by omega
    rw [hn, Function.iterate_add_apply]
    simpa [cfg, step, Function.iterate_succ_apply, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (q+1)

theorem second_transfer {α : Type} (l r q : Nat) (o : α) :
    (step^[2*r+1]) (cfg .testR l r q o) = cfg .testQ (l+r) 0 q o := by
  induction r generalizing l with
  | zero => simp [cfg, step, Function.iterate_succ_apply]
  | succ n ih =>
    have hn : 2 * (n + 1) + 1 = (2*n+1)+2 := by omega
    rw [hn, Function.iterate_add_apply]
    simpa [cfg, step, Function.iterate_succ_apply, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (l+1)

theorem third_transfer {α : Type} (l r q : Nat) (o : α) :
    (step^[2*q+1]) (cfg .testQ l r q o) = cfg .exit l (r+q) 0 o := by
  induction q generalizing r with
  | zero => simp [cfg, step, Function.iterate_succ_apply]
  | succ n ih =>
    have hn : 2 * (n + 1) + 1 = (2*n+1)+2 := by omega
    rw [hn, Function.iterate_add_apply]
    simpa [cfg, step, Function.iterate_succ_apply, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using ih (r+1)

/-- Without the external zero premise, the old work value is added to the
new right value, and the third transfer must also consume it. -/
theorem swap_run_general {α : Type} (l r q : Nat) (o : α) :
    (step^[4*l+2*r+2*q+3]) (cfg .testL l r q o) =
      cfg .exit r (q+l) 0 o := by
  have h : 4*l+2*r+2*q+3 = (2*(q+l)+1) + (2*r+1) + (2*l+1) := by omega
  rw [h, Function.iterate_add_apply, Function.iterate_add_apply]
  rw [first_transfer, second_transfer]
  simpa using third_transfer r 0 (q+l) o

/-- The first loop header can be revisited with nonzero work; work-zero is
an entry condition, not an invariant of all visits to that header. -/
theorem internal_header_nonzero :
    (step^[2]) (cfg .testL 2 0 0 ()) = cfg .testL 1 0 1 () := by
  decide

/-- All six rows execute in the advertised exact number of primitive steps,
preserving every value carried in `other`. -/
theorem swap_run {α : Type} (l r : Nat) (o : α) :
    (step^[4*l+2*r+3]) (cfg .testL l r 0 o) = cfg .exit r l 0 o := by
  have h : 4*l+2*r+3 = (2*l+1) + (2*r+1) + (2*l+1) := by omega
  rw [h, Function.iterate_add_apply, Function.iterate_add_apply]
  simp only [first_transfer, Nat.zero_add, second_transfer, third_transfer]

end Shared.Beeping.NPcoNP.Swap284Steps
