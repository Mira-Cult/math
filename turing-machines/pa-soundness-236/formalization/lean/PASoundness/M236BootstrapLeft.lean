import PASoundness.M236BootstrapScan

/-!
Literal leftward bootstrap sweep across pairs. Each pair changes from
`0,1` to `1,0` in tape order. The recursive tape transformer is accompanied
by exact inside/outside invariants, not merely observations at the head.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.BootstrapLeft

open Shared.Beeping Shared.Beeping.Machines PASoundness.M236.BootstrapScan

def setZero (tape : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then false else tape x

def swapPair (tape : Int → Bool) (h : Int) : Int → Bool :=
  setOne (setZero tape h) (h - 1)

def swept : Nat → Int → (Int → Bool) → (Int → Bool)
  | 0, _, tape => tape
  | n + 1, h, tape => swept n (h - 2) (swapPair tape h)

theorem left_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    rawWord.step (config 75 h tape) = (config 77 (h - 1) (setZero tape h), []) := by
  have hr : raw.table.row 75 true = ⟨false, .left, 77, false⟩ := by decide
  have he : rawLabels.at 75 true = none := by decide
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  rfl

theorem left_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 77 h tape) = (config 75 (h - 1) (setOne tape h), []) := by
  have hr : raw.table.row 77 false = ⟨true, .left, 75, false⟩ := by decide
  have he : rawLabels.at 77 false = none := by decide
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  rfl

theorem left_stop (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 75 h tape) = (config 0 (h - 1) tape, []) := by
  have hr : raw.table.row 75 false = ⟨false, .left, 0, false⟩ := by decide
  have he : rawLabels.at 75 false = none := by decide
  have hw : (config 75 h tape).write false = tape := by
    simpa [config, ht] using write_same (config 75 h tape)
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  simpa [config] using hw

theorem left_pair (h : Int) (tape : Int → Bool)
    (h1 : tape h = true) (h0 : tape (h - 1) = false) :
    rawWord.Block (config 75 h tape) 2 (config 75 (h - 2) (swapPair tape h)) [] := by
  have ha := WordEventSystem.Block.single rawWord (left_one h tape h1)
  have hn : h - 1 ≠ h := by omega
  have hz : setZero tape h (h - 1) = false := by simpa [setZero, hn] using h0
  have hb := WordEventSystem.Block.single rawWord (left_zero (h - 1) (setZero tape h) hz)
  have he : h - 1 - 1 = h - 2 := by omega
  simpa [he, swapPair] using ha.trans rawWord hb

/-- Cells outside the traversed interval are unchanged. -/
theorem swept_outside (n : Nat) (h x : Int) (tape : Int → Bool)
    (outside : x > h ∨ x ≤ h - 2 * (n : Int)) : swept n h tape x = tape x := by
  induction n generalizing h tape with
  | zero => rfl
  | succ n ih =>
    have hr : x > h - 2 ∨ x ≤ (h - 2) - 2 * (n : Int) := by omega
    rw [swept, ih (h - 2) (swapPair tape h) hr]
    have h1 : x ≠ h := by omega
    have h2 : x ≠ h - 1 := by omega
    simp [swapPair, setOne, setZero, h1, h2]

/-- Every traversed pair has its precise final values, independently of the
initial tape; the scan precondition is needed only for the execution proof. -/
theorem swept_pair (n : Nat) (h : Int) (tape : Int → Bool) (i : Nat) (hi : i < n) :
    swept n h tape (h - 2 * (i : Int)) = false ∧
      swept n h tape (h - 2 * (i : Int) - 1) = true := by
  induction n generalizing h tape i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero =>
      have h0 := swept_outside n (h - 2) h (swapPair tape h) (Or.inl (by omega))
      have h1 := swept_outside n (h - 2) (h - 1) (swapPair tape h) (Or.inl (by omega))
      simp only [swept, Int.ofNat_zero]
      have hz : h - 2 * (0 : Int) = h := by omega
      rw [hz]
      rw [h0, h1]
      have hn : h ≠ h - 1 := by omega
      simp [swapPair, setOne, setZero, hn]
    | succ i =>
      have hr := ih (h - 2) (swapPair tape h) i (by omega)
      have he : h - 2 * ((i + 1 : Nat) : Int) = (h - 2) - 2 * (i : Int) := by omega
      simpa only [swept, he] using hr

/-- Every finite leftward sweep has exact duration, exact full tape and no
events. Each indexed input pair is read in the order one then zero. -/
theorem left_pairs (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false) :
    rawWord.Block (config 75 h tape) (2 * n)
      (config 75 (h - 2 * (n : Int)) (swept n h tape)) [] := by
  induction n generalizing h tape with
  | zero => simpa [swept] using WordEventSystem.Block.refl rawWord (config 75 h tape)
  | succ n ih =>
    have first := pattern 0 (by omega)
    have rest : ∀ i < n, swapPair tape h ((h - 2) - 2 * (i : Int)) = true ∧
        swapPair tape h ((h - 2) - 2 * (i : Int) - 1) = false := by
      intro i hi
      have hp := pattern (i + 1) (by omega)
      have he : h - 2 * ((i + 1 : Nat) : Int) = (h - 2) - 2 * (i : Int) := by omega
      rw [he] at hp
      have h0 : (h - 2) - 2 * (i : Int) ≠ h := by omega
      have h1 : (h - 2) - 2 * (i : Int) ≠ h - 1 := by omega
      have h2 : (h - 2) - 2 * (i : Int) - 1 ≠ h := by omega
      have h3 : (h - 2) - 2 * (i : Int) - 1 ≠ h - 1 := by omega
      simpa [swapPair, setOne, setZero, h0, h1, h2, h3] using hp
    have step := left_pair h tape (by simpa using first.1) (by simpa using first.2)
    have tail := ih (h - 2) (swapPair tape h) rest
    have whole := step.trans rawWord tail
    have hh : (h - 2) - 2 * (n : Int) = h - 2 * ((n + 1 : Nat) : Int) := by omega
    have ht : 2 + 2 * n = 2 * (n + 1) := by omega
    simpa only [List.nil_append, swept, hh, ht] using whole

theorem selected_left_pairs (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false) :
    selectedWord.Block ⟨74, h, tape⟩ (2 * n)
      ⟨74, h - 2 * (n : Int), swept n h tape⟩ [] := by
  have hm : mapState 75 = 74 := by decide
  simpa [mapConfig, config, hm] using mapped_block (left_pairs n h tape pattern)

theorem left_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop : tape (h - 2 * (n : Int)) = false) :
    rawWord.Block (config 75 h tape) (2 * n + 1)
      (config 0 (h - 2 * (n : Int) - 1) (swept n h tape)) [] := by
  have hread : swept n h tape (h - 2 * (n : Int)) = false := by
    rw [swept_outside n h (h - 2 * (n : Int)) tape (Or.inr (by omega))]
    exact stop
  have hsweep := left_pairs n h tape pattern
  have hstop := WordEventSystem.Block.single rawWord (left_stop _ _ hread)
  simpa using hsweep.trans rawWord hstop

theorem selected_left_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h - 2 * (i : Int)) = true ∧
      tape (h - 2 * (i : Int) - 1) = false)
    (stop : tape (h - 2 * (n : Int)) = false) :
    selectedWord.Block ⟨74, h, tape⟩ (2 * n + 1)
      ⟨0, h - 2 * (n : Int) - 1, swept n h tape⟩ [] := by
  have h75 : mapState 75 = 74 := by decide
  have h0 : mapState 0 = 0 := by decide
  simpa [mapConfig, config, h75, h0] using mapped_block (left_pairs_stop n h tape pattern stop)

end PASoundness.M236.BootstrapLeft
