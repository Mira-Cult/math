import PASoundness.M236BootstrapLeft

/-!
Third recurring literal bootstrap sweep: raw states 0 and 76 cross pairs
leftward, preserving the first one and filling the adjacent zero. We prove
its complete tape effect and its possible two-step exit. These are local
blocks; the blank-start reachability of their preconditions remains open.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.BootstrapFill

open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.BootstrapScan

def filled : Nat → Int → (Int → Bool) → (Int → Bool)
  | 0, _, tape => tape
  | n + 1, h, tape => filled n (h - 2) (setOne tape (h - 1))

theorem first_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 0 h tape) = (config 75 (h + 1) (setOne tape h), []) := by
  have hr : raw.table.row 0 false = ⟨true, .right, 75, false⟩ := by decide
  have he : rawLabels.at 0 false = none := by decide
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  rfl

theorem first_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    rawWord.step (config 0 h tape) = (config 76 (h - 1) tape, []) := by
  have hr : raw.table.row 0 true = ⟨true, .left, 76, false⟩ := by decide
  have he : rawLabels.at 0 true = none := by decide
  have hw : (config 0 h tape).write true = tape := by
    simpa [config, ht] using write_same (config 0 h tape)
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  simpa [config] using hw

theorem second_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 76 h tape) = (config 0 (h - 1) (setOne tape h), []) := by
  have hr : raw.table.row 76 false = ⟨true, .left, 0, false⟩ := by decide
  have he : rawLabels.at 76 false = none := by decide
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  rfl

theorem second_one_exit (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    rawWord.step (config 76 h tape) = (config 58 (h + 1) tape, []) := by
  have hr : raw.table.row 76 true = ⟨true, .right, 58, false⟩ := by decide
  have he : rawLabels.at 76 true = none := by decide
  have hw : (config 76 h tape).write true = tape := by
    simpa [config, ht] using write_same (config 76 h tape)
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  simpa [config] using hw

theorem fill_pair (h : Int) (tape : Int → Bool)
    (h1 : tape h = true) (h0 : tape (h - 1) = false) :
    rawWord.Block (config 0 h tape) 2 (config 0 (h - 2) (setOne tape (h - 1))) [] := by
  have ha := WordEventSystem.Block.single rawWord (first_one h tape h1)
  have hb := WordEventSystem.Block.single rawWord (second_zero (h - 1) tape h0)
  have he : h - 1 - 1 = h - 2 := by omega
  simpa [he] using ha.trans rawWord hb

theorem filled_outside (n : Nat) (h x : Int) (tape : Int → Bool)
    (outside : x > h ∨ x ≤ h - 2 * (n : Int)) : filled n h tape x = tape x := by
  induction n generalizing h tape with
  | zero => rfl
  | succ n ih =>
    have hr : x > h - 2 ∨ x ≤ (h - 2) - 2 * (n : Int) := by omega
    rw [filled, ih (h - 2) (setOne tape (h - 1)) hr]
    have hn : x ≠ h - 1 := by omega
    simp [setOne, hn]

theorem filled_pair (n : Nat) (h : Int) (tape : Int → Bool) (i : Nat) (hi : i < n) :
    filled n h tape (h - 2 * (i : Int)) = tape (h - 2 * (i : Int)) ∧
      filled n h tape (h - 2 * (i : Int) - 1) = true := by
  induction n generalizing h tape i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have h0 := filled_outside n (h - 2) h (setOne tape (h - 1)) (Or.inl (by omega))
      have h1 := filled_outside n (h - 2) (h - 1) (setOne tape (h - 1)) (Or.inl (by omega))
      simp only [filled, Int.ofNat_zero]
      have hz : h - 2 * (0 : Int) = h := by omega
      rw [hz, h0, h1]
      have hn : h ≠ h - 1 := by omega
      simp [setOne, hn]
    | succ i =>
      have hr := ih (h - 2) (setOne tape (h - 1)) i (by omega)
      have he : h - 2 * ((i + 1 : Nat) : Int) = (h - 2) - 2 * (i : Int) := by omega
      have hn : (h - 2) - 2 * (i : Int) ≠ h - 1 := by omega
      simp only [filled]
      rw [he]
      simpa [setOne, hn] using hr

theorem fill_pairs (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false) :
    rawWord.Block (config 0 h tape) (2 * n)
      (config 0 (h - 2 * (n : Int)) (filled n h tape)) [] := by
  induction n generalizing h tape with
  | zero => simpa [filled] using WordEventSystem.Block.refl rawWord (config 0 h tape)
  | succ n ih =>
    have first := pattern 0 (by omega)
    have rest : ∀ i < n, setOne tape (h - 1) ((h - 2) - 2 * (i : Int)) = true ∧
        setOne tape (h - 1) ((h - 2) - 2 * (i : Int) - 1) = false := by
      intro i hi
      have hp := pattern (i + 1) (by omega)
      have he : h - 2 * ((i + 1 : Nat) : Int) = (h - 2) - 2 * (i : Int) := by omega
      rw [he] at hp
      have h0 : (h - 2) - 2 * (i : Int) ≠ h - 1 := by omega
      have h1 : (h - 2) - 2 * (i : Int) - 1 ≠ h - 1 := by omega
      simpa [setOne, h0, h1] using hp
    have step := fill_pair h tape (by simpa using first.1) (by simpa using first.2)
    have tail := ih (h - 2) (setOne tape (h - 1)) rest
    have whole := step.trans rawWord tail
    have hh : (h - 2) - 2 * (n : Int) = h - 2 * ((n + 1 : Nat) : Int) := by omega
    have ht : 2 + 2 * n = 2 * (n + 1) := by omega
    simpa only [List.nil_append, filled, hh, ht] using whole

/-- A boundary zero is set to one and transfers control to the other
leftward sweep. -/
theorem fill_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop : tape (h - 2 * (n : Int)) = false) :
    rawWord.Block (config 0 h tape) (2 * n + 1)
      (config 75 (h - 2 * (n : Int) + 1)
        (setOne (filled n h tape) (h - 2 * (n : Int)))) [] := by
  have hread : filled n h tape (h - 2 * (n : Int)) = false := by
    rw [filled_outside n h (h - 2 * (n : Int)) tape (Or.inr (by omega))]
    exact stop
  have hscan := fill_pairs n h tape pattern
  have hstop := WordEventSystem.Block.single rawWord (first_zero _ _ hread)
  simpa using hscan.trans rawWord hstop

/-- The first two one-bits beyond the filled interval take the unique exit;
neither of those two transitions changes the full tape. -/
theorem fill_pairs_exit (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop0 : tape (h - 2 * (n : Int)) = true)
    (stop1 : tape (h - 2 * (n : Int) - 1) = true) :
    rawWord.Block (config 0 h tape) (2 * n + 2)
      (config 58 (h - 2 * (n : Int)) (filled n h tape)) [] := by
  let p := h - 2 * (n : Int)
  have hp0 : filled n h tape p = true := by
    rw [filled_outside n h p tape (Or.inr (by dsimp [p]; omega))]
    exact stop0
  have hp1 : filled n h tape (p - 1) = true := by
    rw [filled_outside n h (p - 1) tape (Or.inr (by dsimp [p]; omega))]
    exact stop1
  have hscan := fill_pairs n h tape pattern
  have ha := WordEventSystem.Block.single rawWord (first_one p _ hp0)
  have hb := WordEventSystem.Block.single rawWord (second_one_exit (p - 1) _ hp1)
  have htwo := ha.trans rawWord hb
  have he : p - 1 + 1 = p := by omega
  have htwo' : rawWord.Block (config 0 p (filled n h tape)) 2
      (config 58 p (filled n h tape)) [] := by simpa [he] using htwo
  simpa [p] using hscan.trans rawWord htwo'

theorem selected_fill_pairs_exit (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop0 : tape (h - 2 * (n : Int)) = true)
    (stop1 : tape (h - 2 * (n : Int) - 1) = true) :
    selectedWord.Block ⟨0, h, tape⟩ (2 * n + 2)
      ⟨57, h - 2 * (n : Int), filled n h tape⟩ [] := by
  have h0 : mapState 0 = 0 := by decide
  have h58 : mapState 58 = 57 := by decide
  simpa [mapConfig, config, h0, h58] using
    mapped_block (fill_pairs_exit n h tape pattern stop0 stop1)

theorem selected_fill_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop : tape (h - 2 * (n : Int)) = false) :
    selectedWord.Block ⟨0, h, tape⟩ (2 * n + 1)
      ⟨74, h - 2 * (n : Int) + 1,
        setOne (filled n h tape) (h - 2 * (n : Int))⟩ [] := by
  have h0 : mapState 0 = 0 := by decide
  have h75 : mapState 75 = 74 := by decide
  simpa [mapConfig, config, h0, h75] using
    mapped_block (fill_pairs_stop n h tape pattern stop)

end PASoundness.M236.BootstrapFill
