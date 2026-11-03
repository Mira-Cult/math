import Shared.Codes.FiniteProgramSeparatorFirst
import Shared.ComplexityBridge.TM2SelectInputWord
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! The first reversed witness block uses a distinct marked word for the
rightmost input cell, then ordinary words for the other two cells. The probe
outcomes remain continuation boundaries. -/
namespace Shared.Codes.FiniteProgramMarkedWitness
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramTaggedLoop (canonical output cost result totalCost)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel run_related)
open Shared.Codes.FiniteProgramLink (shiftConfig shiftStatus)
open Shared.Codes.FiniteProgramWitnessPhases (witnessTape witnessSource witnessPred stride)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

def markedPhase (mzero mone : List Bool) : Program :=
  Shared.Codes.FiniteProgramPhase.program mzero mone

def offset (mzero mone : List Bool) : Nat := (markedPhase mzero mone).length-1

def program (mzero mone zero one : List Bool) : Program :=
  Shared.Codes.FiniteProgramSplice.program (markedPhase mzero mone)
    (Shared.Codes.FiniteProgramWitnessPhases.phases zero one 2)

theorem program_valid (mzero mone zero one : List Bool) : valid (program mzero mone zero one) = true :=
  Shared.Codes.FiniteProgramSplice.program_valid _ _
    (Shared.Codes.FiniteProgramPhase.program_valid mzero mone)
    (Shared.Codes.FiniteProgramWitnessPhases.phases_valid zero one 2)

theorem program_length (mzero mone zero one : List Bool) :
    (program mzero mone zero one).length =
      125+3*mzero.length+3*mone.length+6*zero.length+6*one.length := by
  have hm : offset mzero mone = 40+3*mzero.length+3*mone.length :=
    Shared.Codes.FiniteProgramPhaseProbe.stride_length mzero mone
  have hu := Shared.Codes.FiniteProgramPhaseProbe.stride_length zero one
  simp only [program,Shared.Codes.FiniteProgramSplice.program,Shared.Codes.FiniteProgramLink.link,
    List.length_append,List.length_map,List.length_nil,Nat.add_zero,Shared.Codes.FiniteProgramSplice.stem_length,
    Shared.Codes.FiniteProgramWitnessPhases.phases_length]
  change offset mzero mone + (2*stride zero one + Shared.Codes.FiniteProgramWitnessPhases.probe.length) = _
  rw [hm]
  change Shared.Codes.FiniteProgramWitnessPhases.stride zero one = _ at hu
  rw [hu]
  simp [Shared.Codes.FiniteProgramWitnessPhases.probe]
  omega

attribute [local irreducible] Shared.Codes.FinitePrograms.run

/-- The marked phase executes in the same table as its unmarked continuation.
Its exact cost is charged and its output becomes the continuing buffer. -/
theorem marked_first (mzero mone zero one : List Bool) (b p : Bool) (xs L : List Bool) (c : Config)
    (hq : c.1 = 0) (ht : TapeRel c.2 (canonical (p::L) b xs).2) :
    ∃ d, run (program mzero mone zero one) c (cost mzero mone b xs) = some (.inr d) ∧
      d.1 = offset mzero mone ∧ TapeRel d.2 (canonical L p (output mzero mone b xs)).2 := by
  let phase := markedPhase mzero mone
  let rest := Shared.Codes.FiniteProgramWitnessPhases.phases zero one 2
  have hp := Shared.Codes.FiniteProgramPhase.cycle mzero mone b false p xs L
  change run phase (canonical (p::L) b xs) (cost mzero mone b xs) =
    some (.inr (offset mzero mone,tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged
      (output mzero mone b xs) ++ [false,false]))) at hp
  have hp' := Shared.Codes.FiniteProgramSplice.first_run phase rest
    (Shared.Codes.FiniteProgramPhase.program_valid mzero mone) (canonical (p::L) b xs) _ _ false
    (by simp [canonical,phase,markedPhase,Shared.Codes.FiniteProgramPhase.length])
    (Shared.Codes.FiniteProgramPhase.terminal_step mzero mone) hp
  change run (program mzero mone zero one) (canonical (p::L) b xs) _ = _ at hp'
  have h := run_related (program mzero mone zero one) c (canonical (p::L) b xs)
    (by simpa [canonical] using hq) ht (cost mzero mone b xs)
  rw [hp'] at h
  cases hs : run (program mzero mone zero one) c (cost mzero mone b xs) with
  | none => rw [hs] at h; exact False.elim h
  | some v => cases v with
    | inl out => rw [hs] at h; exact False.elim h
    | inr d =>
      rw [hs] at h
      have hd : d.1 = offset mzero mone ∧ TapeRel d.2
          (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output mzero mone b xs) ++ [false,false])) := h
      refine ⟨d,rfl,hd.1,?_⟩
      apply Eq.trans hd.2
      have hpad := Shared.Codes.FiniteProgramTaggedLoop.tapeAt_append_blank L
        (false::Shared.Codes.FiniteProgramBitShuttle.tagged (output mzero mone b xs) ++ [false,false]) p
      change TapeRel (tapeAt L (p::false::Shared.Codes.FiniteProgramBitShuttle.tagged (output mzero mone b xs) ++ [false,false]))
        (canonical L p (output mzero mone b xs)).2
      simpa [canonical,List.append_assoc] using hpad

private theorem program_splice (mzero mone zero one : List Bool) :
    Shared.Codes.FiniteProgramSplice.program (markedPhase mzero mone)
      (Shared.Codes.FiniteProgramWitnessPhases.phases zero one 2) =
        program mzero mone zero one := rfl

/-- Process the final witness block with the rightmost false cell marked.
The probe selects the next block or the marked separator in the same table. -/
theorem run_marked_block (mzero mone zero one earlier : List Bool) (b : Bool) (xs L : List Bool)
    (c : Config) (hq : c.1 = 0) (ht : TapeRel c.2 (witnessTape (earlier++[b]) xs L)) :
    let buf0 := output mzero mone false xs
    let buf := (result zero one [true,earlier.isEmpty] b buf0).2
    ∃ d, run (program mzero mone zero one) c
        (cost mzero mone false xs + (totalCost zero one [true,earlier.isEmpty] b buf0 + 2)) = some (.inr d) ∧
      d.1 = offset mzero mone + (2*stride zero one + (if earlier.isEmpty then 4 else 3)) ∧
      TapeRel d.2 (witnessTape earlier buf L) := by
  dsimp only
  let source := witnessSource earlier L
  let buf0 := output mzero mone false xs
  let remaining := [true,earlier.isEmpty]
  let buf := (result zero one remaining b buf0).2
  have ht' : TapeRel c.2 (canonical ((witnessPred earlier b) ++ source.tail) false xs).2 := by
    rw [Shared.Codes.FiniteProgramWitnessPhases.witness_aligned]
    exact ht
  change TapeRel c.2 (canonical (b::(remaining++source.tail)) false xs).2 at ht'
  obtain ⟨mid,hm,hmid,htape⟩ := marked_first mzero mone zero one false b xs
    (remaining++source.tail) c hq ht'
  obtain ⟨last,hlast,hlastq,hlastt⟩ := Shared.Codes.FiniteProgramWitnessPhases.run_phases_and_probe
    zero one 2 remaining (by simp [remaining]) b buf0 source.tail (0,mid.2) rfl htape
  have hin : ((0,mid.2) : Config).1 < (Shared.Codes.FiniteProgramWitnessPhases.phases zero one 2).length :=
    Shared.Codes.FiniteProgramLink.valid_nonempty _ (Shared.Codes.FiniteProgramWitnessPhases.phases_valid zero one 2)
  have hshift := Shared.Codes.FiniteProgramSplice.second_run (markedPhase mzero mone)
    (Shared.Codes.FiniteProgramWitnessPhases.phases zero one 2)
    (Shared.Codes.FiniteProgramWitnessPhases.phases_valid zero one 2) (0,mid.2) hin
    (totalCost zero one remaining b buf0 + 2)
  rw [hlast,program_splice] at hshift
  have hcfg := Shared.Codes.FiniteProgramWitnessPhases.shift_from_state mid (offset mzero mone) hmid
  have hh : (result zero one remaining b buf0).1 = earlier.isEmpty := by simp [remaining,result]
  have htgt : (canonical source.tail earlier.isEmpty buf).2 = witnessTape earlier buf L := by
    have hhead : source.head?.getD false = earlier.isEmpty :=
      Shared.Codes.FiniteProgramWitnessPhases.witness_boundary_head earlier L
    change (source.tail,earlier.isEmpty,
      false::Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false]) =
      (source.tail,source.head?.getD false,
        false::Shared.Codes.FiniteProgramBitShuttle.tagged buf ++ [false,false,false])
    rw [hhead]
  refine ⟨shiftConfig (offset mzero mone) last,?_,?_,?_⟩
  · rw [run_continue _ _ _ _ _ hm,hcfg]
    simpa only [shiftStatus,offset] using hshift
  · simp only [shiftConfig,hlastq,hh]
  · change TapeRel last.2 (canonical source.tail (result zero one remaining b buf0).1 buf).2 at hlastt
    rw [hh,htgt] at hlastt
    exact hlastt

def markedBuffer (mzero mone zero one : List Bool) (earlier : List Bool) (b : Bool) (xs : List Bool) : List Bool :=
  (result zero one [true,earlier.isEmpty] b (output mzero mone false xs)).2

/-- The marked cell contributes the marked-zero word; the other two cells
contribute the ordinary words in their physical reverse-scan order. -/
theorem marked_buffer (mzero mone zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    markedBuffer mzero mone zero one earlier b xs =
      xs ++ (false::mzero) ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one [b,true] := by
  have h := Shared.ComplexityBridge.FirstBlocksContent.result_buffer zero one [true,earlier.isEmpty] b
    (output mzero mone false xs)
  simpa [markedBuffer,output,Shared.ComplexityBridge.FirstBlocksContent.processed,List.append_assoc] using h

theorem marked_block_cost_bound (mzero mone zero one earlier : List Bool) (b : Bool) (xs : List Bool) :
    cost mzero mone false xs +
      (totalCost zero one [true,earlier.isEmpty] b (output mzero mone false xs) + 2) ≤
      16*xs.length+16*mzero.length+31 +
        (2*(16*(xs.length+1+mzero.length+2*(1+Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one)) +
          16*Shared.Codes.FiniteProgramTaggedLoop.maxWord zero one+31)+2) := by
  have h := Shared.Codes.FiniteProgramTaggedLoop.totalCost_bound zero one [true,earlier.isEmpty] b
    (output mzero mone false xs)
  simp only [List.length_cons,List.length_nil,output,Bool.false_eq_true,reduceIte,
    List.length_append] at h
  simp only [cost,output,Bool.false_eq_true,reduceIte]
  omega

/-- Exact reversed raw pair layout for a nonempty witness. -/
theorem pair_reverse (x earlier : List Bool) (b : Bool) :
    (BitstringEncoding.bitEncode (x,earlier++[b])).reverse =
      false::([b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
        (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse) := by
  rw [Shared.ComplexityBridge.PairReverseFirst.pair_encoding,
    Shared.ComplexityBridge.PairReverseWitness.encode_append,
    Shared.ComplexityBridge.PairReverseWitness.encode_cons]
  have hnil : BitstringEncoding.bitEncode ([] : List Bool) = [] := rfl
  simp [hnil,List.reverse_append,List.append_assoc]

/-- The marked word and following ordinary words are exactly the canonical
TM2-to-binary translated input for a nonempty encoded witness. -/
theorem tm2_pair_words (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
      (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse
    Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) =
      Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false ++
        rest.flatMap (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false) := by
  dsimp only
  let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
      (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse
  have hrev : ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm).reverse =
      inp.symm false :: rest.map inp.symm := by
    rw [← List.map_reverse,pair_reverse]
    rfl
  rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
  simp only [List.flatMap_map]
  rfl

/-- Buffer contents after the marked block, the remaining witness blocks,
separator, and first-component blocks have all been accumulated. -/
theorem marked_combined_buffer (mzero mone zero one x earlier xs : List Bool) (b : Bool) :
    Shared.Codes.FiniteProgramSeparatorFirst.firstOutput zero one x.reverse
      (output zero one false (Shared.Codes.FiniteProgramWitnessController.loopOutput zero one earlier.reverse
        (markedBuffer mzero mone zero one earlier b xs))) =
      xs ++ (false::mzero) ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one
        ([b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
          (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse) := by
  have h := Shared.Codes.FiniteProgramSeparatorFirst.combined_buffer zero one x earlier
    (markedBuffer mzero mone zero one earlier b xs)
  rw [marked_buffer] at h ⊢
  rw [h]
  simp [Shared.ComplexityBridge.FirstBlocksContent.frames,List.flatMap_append,List.append_assoc]

/-- Removing complete fixed-width metadata frames keeps the marked first
word and all ordinary words in order. -/
theorem unframe_marked (mzero zero one : List Bool) (width : Nat)
    (hm : mzero.length = width) (hz : zero.length = width) (ho : one.length = width)
    (rest : List Bool) :
    Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1)
        ((false::mzero) ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one rest) =
      mzero ++ rest.flatMap (Shared.ComplexityBridge.FirstBlocksContent.selected zero one) := by
  have h := Shared.ComplexityBridge.FirstBlocksContent.unframe_frames zero one width hz ho rest
  simp [Shared.ComplexityBridge.FirstBlocksContent.unframe,hm,h]

/-- At the list level, decoding the marked and ordinary frames yields the
actual translated TM2 input for the encoded pair. This does not yet connect
the finite tape frame decoder to the combined scan. -/
theorem unframe_tm2_pair (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let marked := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let zero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let one := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
      (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse
    Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1)
        ((false::marked) ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one rest) =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
  dsimp only
  rw [unframe_marked _ _ _ width
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)]
  rw [tm2_pair_words]
  congr 1
  apply List.flatMap_congr
  intro bit _
  cases bit <;> rfl

/-- When the buffer begins empty and the fixed words are the TM2 input-cell
codec, the complete framed list decodes to the exact translated pair input.
The construction of this list on tape still needs the probe continuations. -/
theorem marked_buffer_unframes_tm2 (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let mzero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mone := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let zero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let one := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let rest := [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++
      (Shared.ComplexityBridge.PairReverseFirst.expanded x).reverse
    let buf := markedBuffer mzero mone zero one earlier b []
    Shared.ComplexityBridge.FirstBlocksContent.unframe width (rest.length+1)
      (Shared.Codes.FiniteProgramSeparatorFirst.firstOutput zero one x.reverse
        (output zero one false (Shared.Codes.FiniteProgramWitnessController.loopOutput zero one earlier.reverse buf))) =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
  dsimp only
  rw [marked_combined_buffer]
  simpa only [List.nil_append] using unframe_tm2_pair tm enc inp x earlier b

/-- The literal marked-block table writes the correct first framed TM2 word,
then the two ordinary words of that witness block, before its probe. -/
theorem run_tm2_marked_block (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (earlier : List Bool) (b : Bool) (L : List Bool)
    (c : Config) (hq : c.1 = 0) (ht : TapeRel c.2 (witnessTape (earlier++[b]) [] L)) :
    let mzero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mone := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let zero := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let one := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    ∃ d, run (program mzero mone zero one) c
        (cost mzero mone false [] + (totalCost zero one [true,earlier.isEmpty] b (output mzero mone false []) + 2)) =
          some (.inr d) ∧
      d.1 = offset mzero mone + (2*stride zero one + (if earlier.isEmpty then 4 else 3)) ∧
      TapeRel d.2 (witnessTape earlier
        ((false::mzero) ++ Shared.ComplexityBridge.FirstBlocksContent.frames zero one [b,true]) L) := by
  dsimp only
  obtain ⟨d,hr,hq',ht'⟩ := run_marked_block
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true) earlier b [] L c hq ht
  refine ⟨d,hr,hq',?_⟩
  change TapeRel d.2 (witnessTape earlier
    (markedBuffer _ _ _ _ earlier b []) L) at ht'
  simpa [marked_buffer] using ht'

namespace Fixtures
example : markedBuffer [true] [false] [false] [true] [] false [] =
    [false,true,false,false,true,true] := by decide
example : (BitstringEncoding.bitEncode (([] : List Bool),[true])).reverse = [false,true,true,false] := by decide
end Fixtures

end Shared.Codes.FiniteProgramMarkedWitness
