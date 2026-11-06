import Shared.ComplexityBridge.TM0FiniteReindex
import Shared.Codes.FiniteProgramTapeTerminal

/-! Uniformly halted post-Turing control states become finite-program states
whose returned Boolean is the scanned bit. Both read rows must halt: halting
on just the current tape does not justify replacing the entire state. -/
namespace Shared.ComplexityBridge.TM0FiniteTerminal
open Turing
open Shared.Codes.FinitePrograms
open Shared.ComplexityBridge.TM0FiniteProgram
open Shared.ComplexityBridge.TM0FiniteReindex
open Shared.ComplexityBridge.TM2Symbols

variable {m : Nat}

theorem mainIndex_bound (M : Machine m) (q : Fin m) :
    mainIndex q < (program M).length := by
  rw [program_length]
  have h := q.isLt
  dsimp [mainIndex]
  omega

theorem halted_all_tapes (M : Machine m) (q : Fin m)
    (hh : ∀ b, M q b = none) (t : Tape) :
    step (program M) (mainIndex q,t) = some (.inl t.2.1) := by
  have h := halted_step M q t (hh t.2.1)
  simpa [run,advance] using h

theorem terminal_all_tapes (M : Machine m) (q : Fin m)
    (hh : ∀ b, M q b = none) :
    ∀ t, ∃ b, step (program M) (mainIndex q,t) = some (.inl b) := by
  intro t
  exact ⟨t.2.1, halted_all_tapes M q hh t⟩

/-- A supported, uniformly halting source control remains uniformly terminal
after finite reindexing; no successful input is needed to establish it. -/
theorem reindexed_terminal {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
    (q : Λ) (hq : q ∈ S) (hh : ∀ b, M q b = none) :
    ∀ t, ∃ b, step (program (machine M S hs)) (mainIndex (index M S hs q),t) =
      some (.inl b) := by
  apply terminal_all_tapes
  intro b
  rw [machine_row M S hs q hq b, hh b]
  rfl

/-- A fixed finite table reaches the same fixed control for every source run
ending at `q`, preserving the entire tape within twice the source steps. -/
theorem reindexed_run_to_control {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
    (q : Λ) (input : List Bool) (n : Nat) (last : TM0.Cfg Bool Λ)
    (hrun : runSteps (TM0.step M) n (TM0.init input) = some last)
    (hcontrol : last.q = q) :
    ∃ d ≤ 2*n, ∃ t,
      run (program (machine M S hs)) (initial input) d =
        some (.inr (mainIndex (index M S hs q),t)) ∧ tape t = last.Tape := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  let N := machine M S hs
  obtain ⟨hr,_⟩ := run_map M S hs n (TM0.init input) last hs.1 hrun
  rw [initial_config M S hs input] at hr
  have hsrun : runSteps (TM0.step N) n
      ⟨zero M S hs,tape (initial input).2⟩ =
        some ⟨index M S hs q,last.Tape⟩ := by
    simpa [N,config,TM0.init,tape_initial,hcontrol] using hr
  obtain ⟨d,t,_,hd,ht,hfinish⟩ := run_simulation N n (zero M S hs)
    (index M S hs q) (initial input).2 last.Tape hsrun
  have hstart : (mainIndex (zero M S hs),(initial input).2) = initial input := by
    simp [mainIndex,zero,initial]
  rw [hstart] at hfinish
  exact ⟨d,hd,t,hfinish,ht⟩

/-- One fixed linked table executes any source run ending at a supported,
uniformly halted control, charges two handoff moves, and then executes an
arbitrary finite amount of the supplied continuation. -/
theorem reindexed_run_continuation {Λ : Type} [Inhabited Λ]
    (M : TM0.Machine Bool Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
    (q : Λ) (hq : q ∈ S) (hh : ∀ b, M q b = none)
    (continuation : Program) (hcont : valid continuation = true)
    (input : List Bool) (n fuel : Nat) (last : TM0.Cfg Bool Λ)
    (hrun : runSteps (TM0.step M) n (TM0.init input) = some last)
    (hcontrol : last.q = q) :
    ∃ d ≤ 2*n, ∃ t,
      tape t = last.Tape ∧
      run (Shared.Codes.FiniteProgramOneExit.program (program (machine M S hs))
        continuation (mainIndex (index M S hs q))) (initial input) (d+2+fuel) =
      Shared.Codes.FiniteProgramLink.shiftStatus
        (Shared.Codes.FiniteProgramOneExit.offset (program (machine M S hs)))
        (run continuation (0,Shared.Codes.FiniteProgramThreeExit.bounce t) fuel) := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  let p := program (machine M S hs)
  let stop := mainIndex (index M S hs q)
  have hp : valid p = true := TM0FiniteProgram.program_valid _
  have hc : (initial input).1 < p.length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty p hp
  have he : stop < p.length := mainIndex_bound _ _
  have hstop : ∀ t, ∃ b, step p (stop,t) = some (.inl b) :=
    reindexed_terminal M S hs q hq hh
  obtain ⟨d,hd,t,hr,ht⟩ := reindexed_run_to_control M S hs q input n last hrun hcontrol
  refine ⟨d,hd,t,ht,?_⟩
  exact Shared.Codes.FiniteProgramTapeTerminal.run_continuation p continuation stop
    (initial input) t d fuel hp hcont hc he hstop hr

end Shared.ComplexityBridge.TM0FiniteTerminal
