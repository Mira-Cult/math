import Shared.Codes.FiniteProgramFirstBlocksController
import Shared.Codes.FiniteProgramWitnessController
import Shared.ComplexityBridge.FirstBlocksContent
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! A charged separator phase linked to the nonempty first-component loop.
The separator has already been restored to false at entry. -/
namespace Shared.Codes.FiniteProgramSeparatorFirst
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev first := Shared.Codes.FiniteProgramFirstBlocksController.program
abbrev firstTape := Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape
abbrev firstOutput := Shared.Codes.FiniteProgramFirstBlocksController.loopOutput
abbrev firstCost := Shared.Codes.FiniteProgramFirstBlocksController.loopCost

def phase (zero one : List Bool) : Program := Shared.Codes.FiniteProgramPhase.program zero one
def offset (zero one : List Bool) : Nat := (phase zero one).length - 1
def program (zero one : List Bool) : Program := Shared.Codes.FiniteProgramSplice.program (phase zero one) (first zero one)

theorem program_valid (zero one : List Bool) : valid (program zero one) = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _
    (Shared.Codes.FiniteProgramPhase.program_valid zero one)
    (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one)

theorem program_length (zero one : List Bool) :
    (program zero one).length = 285 + 21*zero.length + 21*one.length := by
  have ho : offset zero one = 40+3*zero.length+3*one.length := by
    exact Shared.Codes.FiniteProgramPhaseProbe.stride_length zero one
  simp only [program,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
    List.length_append,List.length_map,List.length_nil,Nat.add_zero,Shared.Codes.FiniteProgramSplice.stem_length]
  change offset zero one + (first zero one).length = _
  rw [ho,Shared.Codes.FiniteProgramFirstBlocksController.program_length]
  omega

attribute [local irreducible] Shared.Codes.FinitePrograms.run

/-- Starting with the restored false separator under the head and a tagged
buffer to its right, one charged phase appends the separator's word and
moves onto the first-component boundary. -/
theorem separator_phase (zero one x xs L : List Bool) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((expanded x).reverse ++ false::false::L) false xs).2) :
    ∃ d, run (program zero one) c (cost zero one false xs) = some (.inr d) ∧
      d.1 = offset zero one ∧ TapeRel d.2 (firstTape x (output zero one false xs) L) := by
  let source := (expanded x).reverse ++ false::false::L
  have hs : false::source.tail = source :=
    Shared.Codes.FiniteProgramFirstBlocksController.source_cons x L
  have hc := Shared.Codes.FiniteProgramPhase.cycle zero one false false false xs source.tail
  have hin : (canonical source false xs).1 < (phase zero one).length := by
    simp [canonical,phase,Shared.Codes.FiniteProgramPhase.length]
  have hp := Shared.Codes.FiniteProgramSplice.first_run (phase zero one) (first zero one)
    (Shared.Codes.FiniteProgramPhase.program_valid zero one)
    (canonical source false xs) _ _ false hin
    (Shared.Codes.FiniteProgramPhase.terminal_step zero one) (by
      rw [← hs]
      exact hc)
  change run (program zero one) (canonical source false xs) _ = _ at hp
  have hr := run_related (program zero one) c (canonical source false xs)
    (by simpa [canonical] using hq) ht (cost zero one false xs)
  rw [hp] at hr
  cases hv : run (program zero one) c (cost zero one false xs) with
  | none => rw [hv] at hr; exact False.elim hr
  | some v => cases v with
    | inl out => rw [hv] at hr; exact False.elim hr
    | inr d =>
      rw [hv] at hr
      have hd : d.1 = offset zero one ∧ TapeRel d.2
          (tapeAt source.tail (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
            (output zero one false xs) ++ [false,false])) := hr
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hpad := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank source.tail
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one false xs) ++ [false,false]) false
      have hhead : source.head?.getD false = false :=
        Shared.Codes.FiniteProgramFirstBlockProbe.first_component_head x L
      have htgt : firstTape x (output zero one false xs) L =
          tapeAt source.tail (false::false::Shared.Codes.FiniteProgramBitShuttle.tagged
            (output zero one false xs) ++ [false,false,false]) := by
        change (source.tail,source.head?.getD false,
          false::Shared.Codes.FiniteProgramBitShuttle.tagged (output zero one false xs) ++ [false,false,false]) = _
        simp [tapeAt,hhead]
      rw [htgt]
      unfold TapeRel at hpad
      simpa [List.cons_append, List.append_assoc] using hpad


/-- A restored separator and every nonempty first-component block are
processed by the same finite table. The existing tagged buffer is retained. -/
theorem run_separator_first (zero one x xs L : List Bool) (hne : x ≠ []) (c : Config)
    (hq : c.1 = 0)
    (ht : TapeRel c.2 (canonical ((expanded x).reverse ++ false::false::L) false xs).2) :
    ∃ d, run (program zero one) c
        (cost zero one false xs + firstCost zero one x.reverse (output zero one false xs)) = some (.inr d) ∧
      d.1 = offset zero one + Shared.Codes.FiniteProgramFirstBlocksController.boundary zero one ∧
      TapeRel d.2 (firstTape [] (firstOutput zero one x.reverse (output zero one false xs)) L) := by
  obtain ⟨mid,hm,hmid,htape⟩ := separator_phase zero one x xs L c hq ht
  have hne' : x.reverse ≠ [] := by simpa using hne
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramFirstBlocksController.run_blocks
    zero one x.reverse (output zero one false xs) L hne' (0,mid.2) rfl (by simpa using htape)
  have hstart : ((0,mid.2) : Config).1 < (first zero one).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one)
  have hs := Shared.Codes.FiniteProgramSplice.second_run (phase zero one) (first zero one)
    (Shared.Codes.FiniteProgramFirstBlocksController.program_valid zero one) (0,mid.2) hstart
    (firstCost zero one x.reverse (output zero one false xs))
  rw [hlast] at hs
  have he := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state mid (offset zero one) hmid
  refine ⟨shiftConfig (offset zero one) last,?_,?_,hlastt⟩
  · rw [run_continue _ _ _ _ _ hm,he]
    simpa only [program,offset,shiftStatus] using hs
  · simp only [shiftConfig,hlastq]

/-- The data bits processed in each reversed witness block. -/
def witnessRaw (todo : List Bool) : List Bool :=
  todo.flatMap (fun b => [false,b,true])

theorem witness_group_buffer (zero one : List Bool) (b : Bool) (xs : List Bool) :
    Shared.Codes.FiniteProgramWitnessController.groupOutput zero one b xs =
      xs ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one [false,b,true] := by
  simpa [Shared.Codes.FiniteProgramWitnessController.groupOutput,
    Shared.Codes.FiniteProgramWitnessPhases.witnessOutput,
    Shared.Codes.FiniteProgramWitnessPhases.witnessPred,
    Shared.ComplexityBridge.FirstBlocksContent.processed] using
    Shared.ComplexityBridge.FirstBlocksContent.result_buffer zero one [b,true,true] false xs

theorem witness_loop_buffer (zero one todo xs : List Bool) :
    Shared.Codes.FiniteProgramWitnessController.loopOutput zero one todo xs =
      xs ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one (witnessRaw todo) := by
  induction todo generalizing xs with
  | nil => simp [Shared.Codes.FiniteProgramWitnessController.loopOutput,witnessRaw,
      Shared.ComplexityBridge.FirstBlocksContent.frames]
  | cons b todo ih =>
    simp only [Shared.Codes.FiniteProgramWitnessController.loopOutput]
    rw [ih,witness_group_buffer]
    change (xs ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one [false,b,true]) ++
        Shared.ComplexityBridge.FirstBlocksContent.frames zero one (witnessRaw todo) =
      xs ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one ([false,b,true] ++ witnessRaw todo)
    rw [Shared.ComplexityBridge.FirstBlocksContent.frames_append]
    simp [List.append_assoc]

theorem witnessRaw_eq (todo : List Bool) :
    witnessRaw todo = (BitstringEncoding.bitEncode todo.reverse).reverse := by
  induction todo with
  | nil => rfl
  | cons b todo ih =>
    simp only [witnessRaw,List.flatMap_cons,List.reverse_cons]
    change [false,b,true] ++ witnessRaw todo =
      (BitstringEncoding.bitEncode (todo.reverse ++ [b])).reverse
    rw [Shared.ComplexityBridge.PairReverseWitness.encode_append,
      Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
    simp only [hnil,List.append_nil,List.reverse_append,List.reverse_cons,List.reverse_nil,List.nil_append,List.cons_append]
    exact congrArg (fun a => false::b::true::a) ih

/-- The buffer contains exactly the reversed witness, separator, and expanded
first component, each represented by its metadata and selected code word.
This statement uses the same word selection for all cells, including the
rightmost cell; the TM2 marked-cell word requires a separate initial phase. -/
theorem combined_buffer (zero one x w xs : List Bool) :
    firstOutput zero one x.reverse
      (output zero one false (Shared.Codes.FiniteProgramWitnessController.loopOutput zero one w.reverse xs)) =
    xs ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one
      ((BitstringEncoding.bitEncode w).reverse ++ [false] ++ (expanded x).reverse) := by
  unfold firstOutput
  rw [Shared.ComplexityBridge.FirstBlocksContent.loop_buffer,witness_loop_buffer]
  have hw := witnessRaw_eq w.reverse
  have hx := Shared.ComplexityBridge.FirstBlocksContent.rawBlocks_eq_reverse_expanded x.reverse
  simp only [List.reverse_reverse] at hw hx
  rw [hw,hx]
  simp [output,
    Shared.ComplexityBridge.FirstBlocksContent.frames,
    Shared.ComplexityBridge.FirstBlocksContent.selected,List.append_assoc]

end Shared.Codes.FiniteProgramSeparatorFirst
