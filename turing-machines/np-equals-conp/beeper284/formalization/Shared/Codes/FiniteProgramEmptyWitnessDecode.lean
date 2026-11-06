import Shared.Codes.FiniteProgramMarkedFrameStart
import Shared.Codes.FiniteProgramScanDecode
import Shared.Codes.FiniteProgramEmptyWitness
import Shared.Codes.FiniteProgramPairDecodeAll
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Connect the empty-witness raw-pair serializer to the physical frame decoder.
The distinguished first word may differ from the ordinary zero word. -/
namespace Shared.Codes.FiniteProgramEmptyWitnessDecode
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus step_shift run_shift)
open Shared.Codes.FiniteProgramSplice (stem stem_length)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramBitShuttle (tagged)
open Shared.Codes.FiniteProgramTaggedLoop (output cost totalCost)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (selectedItems padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (frames selected)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.PairReverseFirst (expanded)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev scan := Shared.Codes.FiniteProgramEmptyWitness.program
abbrev sep := Shared.Codes.FiniteProgramMarkedSeparatorFirst.program
abbrev firstScan := Shared.Codes.FiniteProgramFirstStart.program
abbrev firstStop := Shared.Codes.FiniteProgramPairDecodeAll.firstStop
abbrev sepOffset := Shared.Codes.FiniteProgramMarkedSeparatorFirst.offset

def sepStop (mz mo z o : List Bool) : Nat := sepOffset mz mo + firstStop z o
def stop (mz mo z o : List Bool) : Nat := 7 + sepStop mz mo z o

def handoffPre (mz mo z o : List Bool) : Program :=
  (scan mz mo z o).set (stop mz mo z o) (branch (scan mz mo z o).length) ++
    [bridge ((scan mz mo z o).length+1)]
def program (mz mo z o : List Bool) (width : Nat) : Program :=
  link (handoffPre mz mo z o) (Shared.Codes.FiniteProgramFrameStart.program width) []

theorem handoffPre_length (mz mo z o : List Bool) :
    (handoffPre mz mo z o).length = (scan mz mo z o).length+1 := by simp [handoffPre]

theorem program_length (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width).length =
      401+3*mz.length+3*mo.length+18*z.length+18*o.length+8*width := by
  simp [program,link,handoffPre_length,Shared.Codes.FiniteProgramEmptyWitness.program_length,
    Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

theorem sepStop_bound (mz mo z o : List Bool) : sepStop mz mo z o < (sep mz mo z o).length := by
  have h := Shared.Codes.FiniteProgramPairDecodeAll.firstStop_bound z o
  change firstStop z o < (firstScan z o).length at h
  change sepOffset mz mo + firstStop z o < (sep mz mo z o).length
  simp only [sep,Shared.Codes.FiniteProgramMarkedSeparatorFirst.program,
    Shared.Codes.FiniteProgramSplice.program,link,List.length_append,List.length_map,
    List.length_nil,Nat.add_zero,stem_length]
  change sepOffset mz mo + firstStop z o < sepOffset mz mo + (firstScan z o).length
  omega

theorem stop_bound (mz mo z o : List Bool) : stop mz mo z o < (scan mz mo z o).length := by
  have h := sepStop_bound mz mo z o
  change 7+sepStop mz mo z o < (link Shared.Codes.FiniteProgramEmptyWitness.pre (sep mz mo z o) []).length
  simp only [link,List.length_append,List.length_map,List.length_nil,Nat.add_zero,
    Shared.Codes.FiniteProgramEmptyWitness.prefix_length]
  omega

private theorem link_stop (pre p suffix : Program) (q : Nat) (t : Tape)
    (hq : q < p.length) (h : step p (q,t) = some (.inl false)) :
    step (link pre p suffix) (pre.length+q,t) = some (.inl false) := by
  have hs := step_shift pre p suffix (q,t) hq
  rw [h] at hs
  simpa [shiftConfig,shiftStatus] using hs

theorem scan_stop (mz mo z o : List Bool) (t : Tape) :
    step (scan mz mo z o) (stop mz mo z o,t) = some (.inl false) := by
  have hb := Shared.Codes.FiniteProgramScanDecode.boundary_bound z o
  have hbase := Shared.Codes.FiniteProgramScanDecode.scanner_boundary z o t
  have h0' := link_stop (Shared.Codes.FiniteProgramFirstStart.pre z o)
    (Shared.Codes.FiniteProgramFirstBlocksController.program z o) []
    (Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) t hb hbase
  have h0 : step (firstScan z o) (firstStop z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramFirstStart.program,
      Shared.Codes.FiniteProgramFirstStart.pre_length,Shared.Codes.FiniteProgramPairDecodeAll.firstStop] using h0'
  have h1 := link_stop (stem (Shared.Codes.FiniteProgramMarkedSeparatorFirst.phase mz mo))
    (firstScan z o) [] (firstStop z o) t
    (Shared.Codes.FiniteProgramPairDecodeAll.firstStop_bound z o) h0
  have hs : step (sep mz mo z o) (sepStop mz mo z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramMarkedSeparatorFirst.program,Shared.Codes.FiniteProgramSplice.program,
      stem_length,Shared.Codes.FiniteProgramMarkedSeparatorFirst.offset,sepStop] using h1
  have h2 := link_stop Shared.Codes.FiniteProgramEmptyWitness.pre (sep mz mo z o) []
    (sepStop mz mo z o) t (sepStop_bound mz mo z o) hs
  simpa only [Shared.Codes.FiniteProgramEmptyWitness.program,
    Shared.Codes.FiniteProgramEmptyWitness.prefix_length,stop] using h2

theorem scan_other (mz mo z o : List Bool) (width : Nat) (d : Config)
    (hd : d.1 < (scan mz mo z o).length) (hne : d.1 ≠ stop mz mo z o) :
    step (scan mz mo z o) d = step (program mz mo z o width) d := by
  have hl : (program mz mo z o width)[d.1]? = (scan mz mo z o)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,hl]

theorem stop_row (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width)[stop mz mo z o]? = some (branch (scan mz mo z o).length) := by
  have h := stop_bound mz mo z o
  simp [program,link,handoffPre,List.getElem?_append_left,h]

theorem bridge_row (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width)[(scan mz mo z o).length]? =
      some (bridge ((scan mz mo z o).length+1)) := by simp [program,link,handoffPre]

theorem handoff (mz mo z o : List Bool) (width : Nat) (b : Bool) (L R : List Bool) :
    run (program mz mo z o width) (stop mz mo z o,tapeAt L (b::false::R)) 2 =
      some (.inr ((handoffPre mz mo z o).length,tapeAt L (b::false::R))) := by
  have hs := stop_row mz mo z o width
  have hb := bridge_row mz mo z o width
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (mz mo z o : List Bool) (width : Nat) : valid (program mz mo z o width) = true := by
  let s := scan mz mo z o
  let d := Shared.Codes.FiniteProgramFrameStart.program width
  let k := s.length+1
  let m := k+d.length
  have hl : (program mz mo z o width).length = m := by simp [program,link,handoffPre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramEmptyWitness.program_valid mz mo z o
    change valid s = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramFrameStart.program_valid width
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 0 < d.length := Shared.Codes.FiniteProgramLink.valid_nonempty d
    (Shared.Codes.FiniteProgramFrameStart.program_valid width)
  have hsm : s.length ≤ m := by dsimp [m,k]; omega
  have hbranch : validRow m (branch s.length).1 = true ∧ validRow m (branch s.length).2 = true := by
    have hlt : s.length < m := by dsimp [m,k]; omega
    simp [branch,validRow,hlt]
  have hbridge : validRow m (bridge k).1 = true ∧ validRow m (bridge k).2 = true := by
    have hlt : k < m := by dsimp [m]; omega
    simp [bridge,validRow,hlt]
  have hall : (program mz mo z o width).all
      (fun r => validRow (program mz mo z o width).length r.1 &&
        validRow (program mz mo z o width).length r.2) = true := by
    rw [List.all_eq_true]
    intro r hr
    have hr' : r ∈ s.set (stop mz mo z o) (branch s.length) ∨ r = bridge k ∨
        r ∈ d.map (shiftPair k) := by
      simpa [program,link,handoffPre,handoffPre_length,s,d,k,List.mem_append] using hr
    rw [hl]
    rcases hr' with hset | hbridge' | hmap
    · rcases List.mem_or_eq_of_mem_set hset with ho | he
      · obtain ⟨h₁,h₂⟩ := hs r ho
        simp only [Bool.and_eq_true]
        exact ⟨Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hsm h₁,
          Shared.Codes.FiniteProgramShuttleSelect.validRow_mono _ _ _ hsm h₂⟩
      · subst r; simpa only [Bool.and_eq_true] using hbranch
    · subst r; simpa only [Bool.and_eq_true] using hbridge
    · obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hmap
      obtain ⟨h₁,h₂⟩ := hd r' hr'
      simp only [Bool.and_eq_true]
      exact ⟨Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.1 k d.length h₁,
        Shared.Codes.FiniteProgramTaggedExtend.shifted_valid r'.2 k d.length h₂⟩
  have hn : (program mz mo z o width).isEmpty = false := by
    cases h : program mz mo z o width with
    | nil => simp [h] at hl; dsimp [m,k] at hl; omega
    | cons r rs => rfl
  change (!(program mz mo z o width).isEmpty && (program mz mo z o width).all
    (fun r => validRow (program mz mo z o width).length r.1 &&
      validRow (program mz mo z o width).length r.2)) = true
  rw [hn,hall]
  rfl

def restBits (x : List Bool) : List Bool := (expanded x).reverse

def finalBuf (mz mo z o x : List Bool) : List Bool :=
  Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstOutput z o x.reverse (output mz mo false [])

def words (mz z o x : List Bool) : List Bool := mz ++ (restBits x).flatMap (selected z o)

def scanCost (mz mo z o x : List Bool) : Nat :=
  (BitstringEncoding.bitEncode (x,([] : List Bool))).length+1+2+
    (cost mz mo false [] + (4+Shared.Codes.FiniteProgramMarkedSeparatorFirst.firstCost z o x.reverse (output mz mo false [])))

def decodeCost (z o x : List Bool) (width : Nat) : Nat :=
  let bits := restBits x
  30*(width+bits.length*(width+1))+20 +
    Shared.Codes.FiniteProgramFrameLoop.totalCost width (selectedItems z o bits)

private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (mz mo z o : List Bool) (width : Nat) :
    link (handoffPre mz mo z o) (Shared.Codes.FiniteProgramFrameStart.program width) [] =
      program mz mo z o width := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

/-- From the canonical pair input with empty witness, execute the physical marked-word
frame decoder in the same finite table. Its output words remain tagged. -/
theorem run_empty_decode (mz mo z o x : List Bool) (width : Nat)
    (hmark : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let bits := restBits x
    let allWords := words mz z o x
    let finalTape := tapeAt (cursor false [false] allWords).2
      ((cursor false [false] allWords).1::false::false::padding bits.length [false,false,false,false,false])
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
        (scanCost mz mo z o x + 2 + decodeCost z o x width) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o).length+47+empty width ∧ TapeRel d.2 finalTape := by
  dsimp only
  let bits := restBits x
  let allWords := words mz z o x
  let fb := finalBuf mz mo z o x
  let source := tapeAt [false] (false::false::tagged fb ++ [false,false,false])
  let finalTape := tapeAt (cursor false [false] allWords).2
    ((cursor false [false] allWords).1::false::false::padding bits.length [false,false,false,false,false])
  let dc := decodeCost z o x width
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramEmptyWitness.run_empty_witness mz mo z o x
  change run (scan mz mo z o) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
    (scanCost mz mo z o x) = _ at hm
  have hq : mid.1 = stop mz mo z o := by
    simpa [stop,sepStop,Shared.Codes.FiniteProgramPairDecodeAll.firstStop,Nat.add_assoc] using hstate
  have hc : (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).1 < (scan mz mo z o).length := by
    change 0 < _
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramEmptyWitness.program_valid mz mo z o)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (scan mz mo z o) (program mz mo z o width)
    _ mid _ (stop mz mo z o) false (Shared.Codes.FiniteProgramEmptyWitness.program_valid mz mo z o)
    hc (scan_stop mz mo z o) (scan_other mz mo z o width) hm
  have hsource : TapeRel mid.2 source := by
    simpa [source,fb,finalBuf,Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape,
      Shared.ComplexityBridge.PairReverseFirst.expanded,
      Shared.ComplexityBridge.PairReverseWitness.tapeLeft,tapeAt,List.cons_append] using htape
  have htwo := handoff mz mo z o width false [false] (tagged fb ++ [false,false,false])
  change run (program mz mo z o width) (stop mz mo z o,source) 2 = _ at htwo
  have hrel := run_related (program mz mo z o width) mid (stop mz mo z o,source) hq hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hb : fb = (false::mz) ++ frames z o bits := by
    have h := Shared.Codes.FiniteProgramEmptyWitness.buffer_content mz mo z o x
    simpa [fb,finalBuf,bits,restBits] using h
  have hdec := Shared.Codes.FiniteProgramMarkedFrameStart.run_marked mz z o width hmark hz ho
    false false bits [false] [false,false]
  rw [← hb] at hdec
  change run (Shared.Codes.FiniteProgramFrameStart.program width) (0,source) dc =
    some (.inr (47+empty width,finalTape)) at hdec
  have hshift := run_shift (handoffPre mz mo z o) (Shared.Codes.FiniteProgramFrameStart.program width) []
    (Shared.Codes.FiniteProgramFrameStart.program_valid width) (0,source)
    (by simp [Shared.Codes.FiniteProgramFrameStart.program_length]) dc
  rw [hdec,program_link] at hshift
  have hshift' : run (program mz mo z o width) ((handoffPre mz mo z o).length,source) dc =
      some (.inr ((handoffPre mz mo z o).length+47+empty width,finalTape)) := by
    simpa only [shiftConfig,shiftStatus,Nat.add_zero,Nat.add_assoc] using hshift
  have hrel' := run_related (program mz mo z o width) after ((handoffPre mz mo z o).length,source)
    hqafter htafter dc
  rw [hshift'] at hrel'
  obtain ⟨d,hf,hqd,htd⟩ := status_live _ _ _ hrel'
  refine ⟨d,?_,hqd,htd⟩
  change run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
    (scanCost mz mo z o x+2+dc) = _
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
  exact hf


def scanBound (mz z o x : List Bool) : Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
  let gain := 6*(1+w)
  (6*x.length+4) + (16*mz.length+31) +
    (4+x.length*(6*(16*(1+mz.length+x.length*gain+gain)+16*w+31)+4))

abbrev decodeBound := Shared.Codes.FiniteProgramPairDecodeAll.decodeBound

theorem restBits_length (x : List Bool) : (restBits x).length = 6*x.length := by
  simp [restBits,Shared.Codes.FiniteProgramPairDecodeAll.expanded_length]

theorem total_cost_bound (mz mo z o x : List Bool) (width : Nat)
    (hz : z.length = width) (ho : o.length = width) :
    scanCost mz mo z o x + 2 + decodeCost z o x width ≤
      scanBound mz z o x + 2 + decodeBound width (6*x.length) := by
  have hs := Shared.Codes.FiniteProgramEmptyWitness.total_cost_bound mz mo z o x
  change scanCost mz mo z o x ≤ scanBound mz z o x at hs
  have hd := Shared.Codes.FiniteProgramMarkedFrameStart.run_marked_cost_bound z o width hz ho (restBits x)
  change decodeCost z o x width ≤ decodeBound width (restBits x).length at hd
  rw [restBits_length] at hd
  exact Nat.add_le_add (Nat.add_le_add hs (Nat.le_refl 2)) hd

/-- The decoded tagged words are the canonical translated TM2 input. -/
theorem run_tm2_empty_decode (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,([] : List Bool))
    let allWords := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm)
    let finalTape := tapeAt (cursor false [false] allWords).2
      ((cursor false [false] allWords).1::false::false::padding (restBits x).length
        [false,false,false,false,false])
    ∃ d, run (program mz mo z o width) (initial input)
        (scanCost mz mo z o x + 2 + decodeCost z o x width) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o).length+47+empty width ∧ TapeRel d.2 finalTape := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  have hs : selected z o = Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
    funext bit; cases bit <;> rfl
  have hrev : ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm).reverse =
      inp.symm false :: (restBits x).map inp.symm := by
    rw [← List.map_reverse,Shared.Codes.FiniteProgramEmptyWitness.pair_reverse]
    rfl
  have hw : words mz z o x = Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm) := by
    rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
    simp only [words,hs,List.flatMap_map]
    rfl
  obtain ⟨d,hr,hstate,htape⟩ := run_empty_decode mz mo z o x width
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)
  rw [hw] at htape
  exact ⟨d,hr,hstate,htape⟩

namespace Fixtures
example : valid (program [true] [false] [false] [true] 1) = true :=
  program_valid [true] [false] [false] [true] 1
example : (program [true] [false] [false] [true] 1).length = 451 := by
  simpa using program_length [true] [false] [false] [true] 1
end Fixtures

end Shared.Codes.FiniteProgramEmptyWitnessDecode
