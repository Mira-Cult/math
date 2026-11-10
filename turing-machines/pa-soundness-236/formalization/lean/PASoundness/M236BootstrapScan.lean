import PASoundness.M236Bootstrap
import PASoundness.LocalSimulation

/-!
An unbounded literal bootstrap scan. Raw state 77 reading 1 and state 78
reading 0 move right without changing the tape. This exact positive-time
segment is intended for a later certificate of the blank bootstrap, not as a
claim that the whole bootstrap terminates.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.BootstrapScan

open Shared.Beeping Shared.Beeping.Machines

def rawWord := machineWordSystem raw rawLabels
def selectedWord := machineWordSystem machine machineLabels

def config (q : Fin 237) (h : Int) (tape : Int → Bool) : Config 237 := ⟨q, h, tape⟩

/-- Quotient transport for an arbitrary configuration and transition word,
not only for the blank-start execution. -/
theorem mapped_step (c : Config 237) :
    selectedWord.step (mapConfig c) = (mapConfig (rawWord.step c).1, (rawWord.step c).2) := by
  have hr := (quotient_rows c.state (c.tape c.head)).2.2.2
  apply Prod.ext
  · exact (map_step c).symm
  · simpa [rawWord, selectedWord, machineWordSystem, mapConfig] using
      (congrArg Option.toList hr).symm

theorem mapped_advance (c : Config 237) (n : Nat) :
    selectedWord.advance (mapConfig c) n = mapConfig (rawWord.advance c n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [WordEventSystem.advance, ih, mapped_step]

theorem mapped_word (c : Config 237) (n : Nat) :
    selectedWord.wordFrom (mapConfig c) n = rawWord.wordFrom c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [WordEventSystem.wordFrom, ih, mapped_advance, mapped_step]

theorem mapped_block {c d : Config 237} {n : Nat} {w : List Bool}
    (h : rawWord.Block c n d w) :
    selectedWord.Block (mapConfig c) n (mapConfig d) w := by
  constructor
  · rw [mapped_advance, h.endpoint]
  · rw [mapped_word, h.output]

theorem write_same {n : Nat} (c : Config n) : c.write (c.tape c.head) = c.tape := by
  funext x
  by_cases h : x = c.head <;> simp [Config.write, h]

theorem right_one (h : Int) (tape : Int → Bool) (ht : tape h = true) :
    rawWord.step (config 77 h tape) = (config 78 (h + 1) tape, []) := by
  have hr : raw.table.row 77 true = ⟨true, .right, 78, false⟩ := by decide
  have he : rawLabels.at 77 true = none := by decide
  have hw : (config 77 h tape).write true = tape := by
    simpa [config, ht] using write_same (config 77 h tape)
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  simpa [config] using hw

theorem right_zero (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 78 h tape) = (config 77 (h + 1) tape, []) := by
  have hr : raw.table.row 78 false = ⟨false, .right, 77, false⟩ := by decide
  have he : rawLabels.at 78 false = none := by decide
  have hw : (config 78 h tape).write false = tape := by
    simpa [config, ht] using write_same (config 78 h tape)
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  simpa [config] using hw

def setOne (tape : Int → Bool) (h : Int) : Int → Bool :=
  fun x => if x = h then true else tape x

theorem right_stop (h : Int) (tape : Int → Bool) (ht : tape h = false) :
    rawWord.step (config 77 h tape) =
      (config 75 (h - 1) (setOne tape h), []) := by
  have hr : raw.table.row 77 false = ⟨true, .left, 75, false⟩ := by decide
  have he : rawLabels.at 77 false = none := by decide
  simp [rawWord, machineWordSystem, Machine.step, config, ht, hr, he, Move.apply]
  rfl

theorem right_pair (h : Int) (tape : Int → Bool)
    (h1 : tape h = true) (h0 : tape (h + 1) = false) :
    rawWord.Block (config 77 h tape) 2 (config 77 (h + 2) tape) [] := by
  have ha := WordEventSystem.Block.single rawWord (right_one h tape h1)
  have hb := WordEventSystem.Block.single rawWord (right_zero (h + 1) tape h0)
  have he : h + 1 + 1 = h + 2 := by omega
  simpa [he] using ha.trans rawWord hb

/-- Every finite run of alternating 1,0 cells is traversed in exactly two
physical transitions per pair, with no writes changing the tape or events. -/
theorem right_pairs (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h + 2 * (i : Int)) = true ∧
      tape (h + 2 * (i : Int) + 1) = false) :
    rawWord.Block (config 77 h tape) (2 * n) (config 77 (h + 2 * (n : Int)) tape) [] := by
  induction n generalizing h with
  | zero => simpa using WordEventSystem.Block.refl rawWord (config 77 h tape)
  | succ n ih =>
    have first := pattern 0 (by omega)
    have rest : ∀ i < n, tape ((h + 2) + 2 * (i : Int)) = true ∧
        tape ((h + 2) + 2 * (i : Int) + 1) = false := by
      intro i hi
      have hp := pattern (i + 1) (by omega)
      have he : h + 2 * ((i + 1 : Nat) : Int) = (h + 2) + 2 * (i : Int) := by
        omega
      rw [he] at hp
      exact hp
    have step := right_pair h tape (by simpa using first.1) (by simpa using first.2)
    have tail := ih (h + 2) rest
    have whole := step.trans rawWord tail
    have hn : (h + 2) + 2 * (n : Int) = h + 2 * ((n + 1 : Nat) : Int) := by
      omega
    have ht : 2 + 2 * n = 2 * (n + 1) := by omega
    simpa only [List.nil_append, hn, ht] using whole

/-- The first zero after the scan is overwritten with one; every other tape
cell is retained. The final transition is included in the exact step count. -/
theorem right_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h + 2 * (i : Int)) = true ∧
      tape (h + 2 * (i : Int) + 1) = false)
    (stop : tape (h + 2 * (n : Int)) = false) :
    rawWord.Block (config 77 h tape) (2 * n + 1)
      (config 75 (h + 2 * (n : Int) - 1) (setOne tape (h + 2 * (n : Int)))) [] := by
  have hscan := right_pairs n h tape pattern
  have hstop := WordEventSystem.Block.single rawWord (right_stop _ tape stop)
  simpa using hscan.trans rawWord hstop

theorem selected_right_pairs_stop (n : Nat) (h : Int) (tape : Int → Bool)
    (pattern : ∀ i < n, tape (h + 2 * (i : Int)) = true ∧
      tape (h + 2 * (i : Int) + 1) = false)
    (stop : tape (h + 2 * (n : Int)) = false) :
    selectedWord.Block ⟨76, h, tape⟩ (2 * n + 1)
      ⟨74, h + 2 * (n : Int) - 1, setOne tape (h + 2 * (n : Int))⟩ [] := by
  have h77 : mapState 77 = 76 := by decide
  have h75 : mapState 75 = 74 := by decide
  simpa [mapConfig, config, h77, h75] using
    mapped_block (right_pairs_stop n h tape pattern stop)

end PASoundness.M236.BootstrapScan
