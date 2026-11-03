import Lean

namespace CollatzTM

/- Absolute integer coordinates, complete tape equality, and a distinct halt state. -/
abbrev Tape := Int → Bool

inductive Dir where
  | L | R
  deriving DecidableEq, Repr

structure Config (S : Type) where
  state : Option S
  head : Int
  tape : Tape

structure Instr (S : Type) where
  write : Bool
  dir : Dir
  next : Option S

def move : Dir → Int
  | .L => -1
  | .R => 1

def put (t : Tape) (p : Int) (b : Bool) : Tape :=
  fun z => if z = p then b else t z

def step (δ : S → Bool → Instr S) (c : Config S) : Config S :=
  match c.state with
  | none => c
  | some q =>
      let i := δ q (c.tape c.head)
      ⟨i.next, c.head + move i.dir, put c.tape c.head i.write⟩

def run (δ : S → Bool → Instr S) : Nat → Config S → Config S
  | 0, c => c
  | n+1, c => run δ n (step δ c)

def Halts (δ : S → Bool → Instr S) (c : Config S) : Prop :=
  ∃ n, (run δ n c).state = none

/-- Exact duration and absence of premature halting. -/
def Reaches (δ : S → Bool → Instr S) (n : Nat) (a b : Config S) : Prop :=
  run δ n a = b ∧ ∀ j, j < n → (run δ j a).state ≠ none

def FiniteTape (t : Tape) : Prop :=
  ∃ lo hi : Int, ∀ z, z < lo ∨ hi < z → t z = false

theorem run_add (δ : S → Bool → Instr S) (m n : Nat) (c : Config S) :
    run δ (m+n) c = run δ n (run δ m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih => simpa [Nat.succ_add, run] using ih (step δ c)

theorem run_halt (δ : S → Bool → Instr S) (c : Config S) (h : c.state = none)
    (n : Nat) : run δ n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [run, step, h] using ih

theorem reaches_no_early (δ : S → Bool → Instr S) (n : Nat) (a b : Config S)
    (h : run δ n a = b) (hb : b.state ≠ none) : Reaches δ n a b := by
  refine ⟨h, ?_⟩
  intro j hj he
  have e := run_add δ j (n-j) a
  rw [Nat.add_sub_of_le (Nat.le_of_lt hj), run_halt δ _ he] at e
  rw [h] at e
  exact hb (by rw [e]; exact he)

theorem halts_iff_of_run (δ : S → Bool → Instr S) (n : Nat) (a b : Config S)
    (h : run δ n a = b) : Halts δ a ↔ Halts δ b := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j, ?_⟩
    have e := run_add δ n j a
    have e' := run_add δ j n a
    rw [Nat.add_comm n j, e', run_halt δ _ hj] at e
    rw [h] at e
    rw [← e]
    exact hj
  · rintro ⟨j, hj⟩
    exact ⟨n+j, by rw [run_add, h]; exact hj⟩

end CollatzTM
