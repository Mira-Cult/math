import Shared.ComplexityBridge.TM0FiniteReindex

/-! A supported post-Turing computation compiles to a finite binary table
while retaining the complete final tape, immediately before the table's
halt/output transition. -/
namespace Shared.ComplexityBridge.TM0FiniteFullTape
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM0FiniteProgram
open Shared.ComplexityBridge.TM0FiniteReindex
open Shared.Codes.FinitePrograms

variable {Λ : Type} [Inhabited Λ]
variable (M : TM0.Machine Bool Λ) (S : Finset Λ) (hs : TM0.Supports M (S : Set Λ))
include S hs

/-- The table is independent of the input and source run. Its entire tape
represents the source's final tape modulo trailing blanks, and the next
transition returns the source head bit. -/
theorem finite_program_full_tape :
    ∃ p : Program, valid p = true ∧
      ∀ (input : List Bool) (n : Nat) (last : TM0.Cfg Bool Λ),
        runSteps (TM0.step M) n (TM0.init input) = some last →
        TM0.step M last = none →
        ∃ d ≤ 2*n, ∃ q t,
          run p (initial input) d = some (.inr (q,t)) ∧
          tape t = last.Tape ∧ step p (q,t) = some (.inl last.Tape.head) := by
  letI : Inhabited (Fin S.card) := ⟨zero M S hs⟩
  let N := machine M S hs
  let p := TM0FiniteProgram.program N
  refine ⟨p,TM0FiniteProgram.program_valid N,?_⟩
  intro input n last hrun hhalt
  have hinit : (TM0.init input : TM0.Cfg Bool Λ).q ∈ S := hs.1
  obtain ⟨hr,hl⟩ := run_map M S hs n (TM0.init input) last hinit hrun
  rw [initial_config M S hs input] at hr
  have hh := halt_row M S hs last hl hhalt
  have hsrun : runSteps (TM0.step N) n ⟨zero M S hs,tape (initial input).2⟩ =
      some ⟨index M S hs last.q,last.Tape⟩ := by
    simpa [N,config,TM0.init,tape_initial] using hr
  obtain ⟨d,t,_,hd,ht,htarget⟩ := run_simulation N n (zero M S hs)
    (index M S hs last.q) (initial input).2 last.Tape hsrun
  have hstart : (mainIndex (zero M S hs),(initial input).2) = initial input := by
    simp [mainIndex,zero,initial]
  rw [hstart] at htarget
  have hrow : N (index M S hs last.q) t.2.1 = none := by
    change N (index M S hs last.q) (tape t).head = none
    rw [ht]
    exact hh
  have hhead : t.2.1 = last.Tape.head := congrArg Turing.Tape.head ht
  have hfinal := halted_step N (index M S hs last.q) t hrow
  refine ⟨d,hd,mainIndex (index M S hs last.q),t,htarget,ht,?_⟩
  change run (TM0FiniteProgram.program N) (mainIndex (index M S hs last.q),t) 1 = _
  simpa [hhead] using hfinal

end Shared.ComplexityBridge.TM0FiniteFullTape
