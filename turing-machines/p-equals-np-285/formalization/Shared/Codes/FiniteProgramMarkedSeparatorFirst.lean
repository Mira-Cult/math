import Shared.Codes.FiniteProgramFirstStart
import Shared.Codes.FiniteProgramSeparatorFirst
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! The marked separator of an empty-witness pair is encoded with its own
word before the guarded first-component scan. The separator is already restored. -/
namespace Shared.Codes.FiniteProgramMarkedSeparatorFirst
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev first := Shared.Codes.FiniteProgramFirstStart.program
abbrev firstTape := Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
abbrev firstOutput := Shared.Codes.FiniteProgramFirstBlocksController.loopOutput
abbrev firstCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost

def phase (zero one : List Bool) : Program := Shared.Codes.FiniteProgramPhase.program zero one
def offset (zero one : List Bool) : Nat := (phase zero one).length - 1
def program (mzero mone zero one : List Bool) : Program := Shared.Codes.FiniteProgramSplice.program (phase mzero mone) (first zero one)

theorem program_valid (mzero mone zero one : List Bool) : valid (program mzero mone zero one) = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _
    (Shared.Codes.FiniteProgramPhase.program_valid mzero mone)
    (Shared.Codes.FiniteProgramFirstStart.program_valid zero one)

theorem program_length (mzero mone zero one : List Bool) :
    (program mzero mone zero one).length = 291 + 3*mzero.length + 3*mone.length + 18*zero.length + 18*one.length := by
  have ho : offset mzero mone = 40+3*mzero.length+3*mone.length := by
    exact Shared.Codes.FiniteProgramPhaseProbe.stride_length mzero mone
  simp only [program,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
    List.length_append,List.length_map,List.length_nil,Nat.add_zero,Shared.Codes.FiniteProgramSplice.stem_length]
  change offset mzero mone + (first zero one).length = _
  rw [ho,Shared.Codes.FiniteProgramFirstStart.program_length]
  omega

attribute [local irreducible] Shared.Codes.FinitePrograms.run

/-- Starting with the restored false separator under the head and a tagged
buffer to its right, one charged phase appends the separator's word and
moves onto the first-component boundary. -/
theorem separator_phase (mzero mone zero one x xs L : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((expanded x).reverse ++ false::false::L) false xs).2) :
    ∃ d, run (program mzero mone zero one) c (cost mzero mone false xs) = some (.inr d) ∧
      d.1 = offset mzero mone ∧ TapeRel d.2 (firstTape x (output mzero mone false xs) L) := by
  let source := (expanded x).reverse ++ false::false::L
  have hs : false::source.tail = source :=
    Shared.Codes.FiniteProgramFirstBlocksController.source_cons x L
  have hc := Shared.Codes.FiniteProgramPhase.cycle mzero mone false false false xs source.tail
  have hin : (canonical source false xs).1 < (phase mzero mone).length := by
    simp [canonical,phase,Shared.Codes.FiniteProgramPhase.length]
  have hp := Shared.Codes.FiniteProgramSplice.first_run (phase mzero mone) (first zero one)
    (Shared.Codes.FiniteProgramPhase.program_valid mzero mone)
    (canonical source false xs) _ _ false hin
    (Shared.Codes.FiniteProgramPhase.terminal_step mzero mone) (by
      rw [← hs]
      exact hc)
  change run (program mzero mone zero one) (canonical source false xs) _ = _ at hp
  have hr := run_related (program mzero mone zero one) c (canonical source false xs)
    (by simpa [canonical] using hq) ht (cost mzero mone false xs)
  rw [hp] at hr
  cases hv : run (program mzero mone zero one) c (cost mzero mone false xs) with
  | none => rw [hv] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [hv] at hr; exact False.elim hr
    | inr d =>
      rw [hv] at hr
      have hd : d.1 = offset mzero mone ∧ TapeRel d.2
          (tapeAt source.tail (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
            (output mzero mone false xs) ++ [false,false])) := hr
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hpad := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank source.tail
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (output mzero mone false xs) ++ [false,false]) false
      have hhead : source.head?.getD false = false :=
        Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head x L
      have htgt : firstTape x (output mzero mone false xs) L =
          tapeAt source.tail (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
            (output mzero mone false xs) ++ [false,false,false]) := by
        change (source.tail,source.head?.getD false,
          false::Shared.Codes.FiniteProgramBitShuttle.tagged (output mzero mone false xs) ++ [false,false,false]) = _
        simp [tapeAt,hhead]
      rw [htgt]
      unfold TapeRel at hpad
      simpa [List.cons_append, List.append_assoc] using hpad


/-- The separator phase appends its word, then the guarded first-component
scan handles both empty and nonempty inputs. -/
theorem run_separator_first (mzero mone zero one x xs L : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((expanded x).reverse ++ false::false::L) false xs).2) :
    ∃ d, run (program mzero mone zero one) c
        (cost mzero mone false xs + (4+firstCost zero one x.reverse (output mzero mone false xs))) = some (.inr d) ∧
      d.1 = offset mzero mone + (6+Shared.Codes.FiniteProgramFirstBlocksController.boundary zero one) ∧
      TapeRel d.2 (firstTape [] (firstOutput zero one x.reverse (output mzero mone false xs)) L) := by
  obtain ⟨mid,hm,hmid,htape⟩ := separator_phase mzero mone zero one x xs L c hq ht
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramFirstStart.run_first
    zero one x (output mzero mone false xs) L (0,mid.2) rfl htape
  have hstart : ((0,mid.2) : Config).1 < (first zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramFirstStart.program_valid zero one)
  have hs := Shared.Codes.FiniteProgramSplice.second_run (phase mzero mone) (first zero one)
    (Shared.Codes.FiniteProgramFirstStart.program_valid zero one) (0,mid.2) hstart
    (4+firstCost zero one x.reverse (output mzero mone false xs))
  rw [hlast] at hs
  have he := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state mid (offset mzero mone) hmid
  refine ⟨shiftConfig (offset mzero mone) last,?_,?_,hlastt⟩
  · rw [run_continue _ _ _ _ _ hm,he]
    simpa only [program,offset,shiftStatus] using hs
  · simp only [shiftConfig,hlastq]


/-- Bound for the marked separator and subsequent ordinary first blocks. -/
theorem total_cost_bound (mzero mone zero one x xs : List Bool) :
    let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
    let gain := 6*(1+w)
    cost mzero mone false xs + (4+firstCost zero one x.reverse (output mzero mone false xs)) ≤
      (16*xs.length+16*mzero.length+31) +
        (4+x.length*(6*(16*(xs.length+1+mzero.length+x.length*gain+gain)+16*w+31)+4)) := by
  dsimp only
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one
  let gain := 6*(1+w)
  let buf := output mzero mone false xs
  have hb : buf.length = xs.length+1+mzero.length := by
    simp [buf,output,Nat.add_comm,Nat.add_left_comm]
  have hc : cost mzero mone false xs ≤ 16*xs.length+16*mzero.length+31 := by
    simp only [cost,Bool.false_eq_true,reduceIte]
    omega
  have hf := Shared.Codes.FiniteProgramFirstStart.cost_bound zero one x buf
  dsimp only at hf
  change 4+firstCost zero one x.reverse buf ≤ _ at hf
  rw [hb] at hf
  dsimp [buf,w,gain] at *
  omega

namespace Fixtures
example : valid (program [true] [false] [false] [true]) = true :=
  program_valid [true] [false] [false] [true]
end Fixtures

end Shared.Codes.FiniteProgramMarkedSeparatorFirst
