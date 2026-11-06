import Shared.Codes.FiniteProgramMarkedFrameStart
import Shared.Codes.FiniteProgramScanDecode
import Shared.Codes.FiniteProgramPairStartupAll
import Shared.Codes.FiniteProgramPairDecode
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Connect the nonempty-witness raw-pair serializer to the physical frame decoder.
The distinguished first word may differ from the ordinary zero word. -/
namespace Shared.Codes.FiniteProgramPairDecodeAll
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

abbrev scan := Shared.Codes.FiniteProgramPairStartupAll.program
abbrev marked := Shared.Codes.FiniteProgramMarkedContinuationAll.program
abbrev first := Shared.Codes.FiniteProgramWitnessFirstAll.program
abbrev sep := Shared.Codes.FiniteProgramSeparatorFirstAll.program
abbrev firstScan := Shared.Codes.FiniteProgramFirstStart.program
def firstStop (z o : List Bool) : Nat := 6 + Shared.Codes.FiniteProgramFirstBlocksController.boundary z o
abbrev sepOffset := Shared.Codes.FiniteProgramSeparatorFirstAll.offset
abbrev firstPre := Shared.Codes.FiniteProgramWitnessFirst.handoffPre
abbrev markedPre := Shared.Codes.FiniteProgramMarkedContinuationAll.pre
abbrev scanPre := Shared.Codes.FiniteProgramPairStartupAll.scanPrefix

def sepStop (z o : List Bool) : Nat := sepOffset z o + firstStop z o
def firstLinkedStop (z o : List Bool) : Nat := (firstPre z o).length + sepStop z o
def markedStop (mz mo z o : List Bool) : Nat := (markedPre mz mo z o).length + firstLinkedStop z o
def stop (mz mo z o : List Bool) : Nat := 5 + markedStop mz mo z o

def handoffPre (mz mo z o : List Bool) : Program :=
  (scan mz mo z o).set (stop mz mo z o) (branch (scan mz mo z o).length) ++
    [bridge ((scan mz mo z o).length+1)]
def program (mz mo z o : List Bool) (width : Nat) : Program :=
  link (handoffPre mz mo z o) (Shared.Codes.FiniteProgramFrameStart.program width) []

theorem handoffPre_length (mz mo z o : List Bool) :
    (handoffPre mz mo z o).length = (scan mz mo z o).length+1 := by simp [handoffPre]

theorem program_length (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width).length =
      653+3*mz.length+3*mo.length+36*z.length+36*o.length+8*width := by
  simp [program,link,handoffPre_length,Shared.Codes.FiniteProgramPairStartupAll.program_length,
    Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

theorem firstStop_bound (z o : List Bool) : firstStop z o < (firstScan z o).length := by
  have hb := Shared.Codes.FiniteProgramScanDecode.boundary_bound z o
  change Shared.Codes.FiniteProgramFirstBlocksController.boundary z o <
    (Shared.Codes.FiniteProgramFirstBlocksController.program z o).length at hb
  change 6 + Shared.Codes.FiniteProgramFirstBlocksController.boundary z o <
    (link (Shared.Codes.FiniteProgramFirstStart.pre z o)
      (Shared.Codes.FiniteProgramFirstBlocksController.program z o) []).length
  simp only [link,List.length_append,List.length_map,List.length_nil,Nat.add_zero,
    Shared.Codes.FiniteProgramFirstStart.pre_length]
  omega

theorem sepStop_bound (z o : List Bool) : sepStop z o < (sep z o).length := by
  have hs := firstStop_bound z o
  have hf := Shared.Codes.FiniteProgramFirstStart.program_length z o
  have hz := Shared.Codes.FiniteProgramSeparatorFirstAll.program_length z o
  have ho : sepOffset z o = 40+3*z.length+3*o.length :=
    Shared.Codes.FiniteProgramPhaseProbe.stride_length z o
  change sepOffset z o + firstStop z o < (sep z o).length
  change (firstScan z o).length = _ at hf
  change (sep z o).length = _ at hz
  rw [ho,hz]
  rw [hf] at hs
  omega

theorem firstLinkedStop_bound (z o : List Bool) : firstLinkedStop z o < (first z o).length := by
  have h := sepStop_bound z o
  change (firstPre z o).length + sepStop z o <
    (link (firstPre z o) (sep z o) []).length
  simp only [link,List.length_append,List.length_map,List.length_nil,Nat.add_zero]
  omega

theorem markedStop_bound (mz mo z o : List Bool) : markedStop mz mo z o < (marked mz mo z o).length := by
  have h := firstLinkedStop_bound z o
  change (markedPre mz mo z o).length + firstLinkedStop z o <
    (link (markedPre mz mo z o) (first z o) []).length
  simp only [link,List.length_append,List.length_map,List.length_nil,Nat.add_zero]
  omega

theorem stop_bound (mz mo z o : List Bool) : stop mz mo z o < (scan mz mo z o).length := by
  have h := markedStop_bound mz mo z o
  change 5+markedStop mz mo z o < (link scanPre (marked mz mo z o) []).length
  simp only [link,List.length_append,List.length_map,List.length_nil,Nat.add_zero,
    Shared.Codes.FiniteProgramPairStartupAll.scanPrefix_length]
  omega

private theorem link_stop (pre p suffix : Program) (q : Nat) (t : Tape)
    (hq : q < p.length) (h : step p (q,t) = some (.inl false)) :
    step (link pre p suffix) (pre.length+q,t) = some (.inl false) := by
  have hs := step_shift pre p suffix (q,t) hq
  rw [h] at hs
  simpa [shiftConfig,shiftStatus] using hs

/-- The nested scanner exits at an actual result row of its table. -/
theorem scan_stop (mz mo z o : List Bool) (t : Tape) :
    step (scan mz mo z o) (stop mz mo z o,t) = some (.inl false) := by
  have hb := Shared.Codes.FiniteProgramScanDecode.boundary_bound z o
  have hbase := Shared.Codes.FiniteProgramScanDecode.scanner_boundary z o t
  have h0' := link_stop (Shared.Codes.FiniteProgramFirstStart.pre z o)
    (Shared.Codes.FiniteProgramFirstBlocksController.program z o) []
    (Shared.Codes.FiniteProgramFirstBlocksController.boundary z o) t hb hbase
  have h0 : step (firstScan z o) (firstStop z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramFirstStart.program,
      Shared.Codes.FiniteProgramFirstStart.pre_length,firstStop] using h0'
  have h1 := link_stop (stem (Shared.Codes.FiniteProgramSeparatorFirstAll.phase z o))
    (firstScan z o) [] (firstStop z o) t (firstStop_bound z o) h0
  have hs : step (sep z o) (sepStop z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramSeparatorFirstAll.program,Shared.Codes.FiniteProgramSplice.program,
      stem_length,Shared.Codes.FiniteProgramSeparatorFirstAll.offset,sepStop] using h1
  have h2 := link_stop (firstPre z o) (sep z o) [] (sepStop z o) t (sepStop_bound z o) hs
  have hw : step (first z o) (firstLinkedStop z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramWitnessFirstAll.program,firstLinkedStop] using h2
  have h3 := link_stop (markedPre mz mo z o) (first z o) [] (firstLinkedStop z o) t
    (firstLinkedStop_bound z o) hw
  have hm : step (marked mz mo z o) (markedStop mz mo z o,t) = some (.inl false) := by
    simpa only [Shared.Codes.FiniteProgramMarkedContinuationAll.program,markedStop] using h3
  have h4 := link_stop scanPre (marked mz mo z o) [] (markedStop mz mo z o) t
    (markedStop_bound mz mo z o) hm
  simpa only [Shared.Codes.FiniteProgramPairStartupAll.program,
    Shared.Codes.FiniteProgramPairStartupAll.scanPrefix_length,stop] using h4

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
    have hv := Shared.Codes.FiniteProgramPairStartupAll.program_valid mz mo z o
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


def restBits (x earlier : List Bool) (b : Bool) : List Bool :=
  [b,true] ++ (BitstringEncoding.bitEncode earlier).reverse ++ [false] ++ (expanded x).reverse

def firstBuf (mz mo z o earlier : List Bool) (b : Bool) : List Bool :=
  Shared.Codes.FiniteProgramMarkedWitness.markedBuffer mz mo z o earlier b []

def finalBuf (mz mo z o x earlier : List Bool) (b : Bool) : List Bool :=
  Shared.Codes.FiniteProgramSeparatorFirstAll.firstOutput z o x.reverse
    (output z o false (Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse
      (firstBuf mz mo z o earlier b)))

def words (mz z o x earlier : List Bool) (b : Bool) : List Bool :=
  mz ++ (restBits x earlier b).flatMap (selected z o)

def scanCost (mz mo z o x earlier : List Bool) (b : Bool) : Nat :=
  let input := BitstringEncoding.bitEncode (x,earlier++[b])
  let fb := firstBuf mz mo z o earlier b
  let buf := Shared.Codes.FiniteProgramWitnessController.loopOutput z o earlier.reverse fb
  let mc := cost mz mo false [] + (totalCost z o [true,earlier.isEmpty] b (output mz mo false [])+2)
  input.length+1+(mc+2+(Shared.Codes.FiniteProgramWitnessController.loopCost z o earlier.reverse fb+2+
    (cost z o false buf + (4+Shared.Codes.FiniteProgramSeparatorFirstAll.firstCost z o x.reverse
      (output z o false buf)))))

def decodeCost (z o x earlier : List Bool) (width : Nat) (b : Bool) : Nat :=
  let bits := restBits x earlier b
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

/-- From the canonical pair input with nonempty witness, execute the physical marked-word
frame decoder in the same finite table. Its output words remain tagged. -/
theorem run_pair_decode (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hmark : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let bits := restBits x earlier b
    let allWords := words mz z o x earlier b
    let finalTape := tapeAt (cursor false [false] allWords).2
      ((cursor false [false] allWords).1::false::false::padding bits.length [false,false,false,false,false])
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
        (scanCost mz mo z o x earlier b + 2 + decodeCost z o x earlier width b) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o).length+47+empty width ∧ TapeRel d.2 finalTape := by
  dsimp only
  let bits := restBits x earlier b
  let allWords := words mz z o x earlier b
  let fb := finalBuf mz mo z o x earlier b
  let source := tapeAt [false] (false::false::tagged fb ++ [false,false,false])
  let finalTape := tapeAt (cursor false [false] allWords).2
    ((cursor false [false] allWords).1::false::false::padding bits.length [false,false,false,false,false])
  let dc := decodeCost z o x earlier width b
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramPairStartupAll.run_pair mz mo z o x earlier b
  change run (scan mz mo z o) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
    (scanCost mz mo z o x earlier b) = _ at hm
  have hq : mid.1 = stop mz mo z o := by
    simpa [stop,markedStop,firstLinkedStop,sepStop,firstStop,Nat.add_assoc] using hstate
  have hc : (initial (BitstringEncoding.bitEncode (x,earlier++[b]))).1 < (scan mz mo z o).length := by
    change 0 < _
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramPairStartupAll.program_valid mz mo z o)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (scan mz mo z o) (program mz mo z o width)
    _ mid _ (stop mz mo z o) false (Shared.Codes.FiniteProgramPairStartupAll.program_valid mz mo z o)
    hc (scan_stop mz mo z o) (scan_other mz mo z o width) hm
  have hsource : TapeRel mid.2 source := by
    simpa [source,fb,finalBuf,firstBuf,Shared.Codes.FiniteProgramFirstBlocksController.boundaryTape,
      Shared.ComplexityBridge.PairReverseFirst.expanded,
      Shared.ComplexityBridge.PairReverseWitness.tapeLeft,tapeAt,List.cons_append] using htape
  have htwo := handoff mz mo z o width false [false] (tagged fb ++ [false,false,false])
  change run (program mz mo z o width) (stop mz mo z o,source) 2 = _ at htwo
  have hrel := run_related (program mz mo z o width) mid (stop mz mo z o,source) hq hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hb : fb = (false::mz) ++ frames z o bits := by
    have h := Shared.Codes.FiniteProgramMarkedWitness.marked_combined_buffer mz mo z o x earlier [] b
    simpa [fb,finalBuf,firstBuf,bits,restBits] using h
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
  change run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
    (scanCost mz mo z o x earlier b+2+dc) = _
  rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
  exact hf

theorem expanded_length (x : List Bool) : (expanded x).length = 6*x.length := by
  induction x with
  | nil => rfl
  | cons b xs ih =>
    simp only [Shared.ComplexityBridge.PairReverseFirst.expanded_cons,List.length_append,
      List.length_cons,List.length_nil,ih]
    omega

theorem restBits_length (x earlier : List Bool) (b : Bool) :
    (restBits x earlier b).length = 6*x.length+3*earlier.length+3 := by
  simp [restBits,expanded_length,Shared.ComplexityBridge.bitstring_list_encoded_length]
  omega

def scanBound (mz z o x earlier : List Bool) : Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
  let gw := 3*(1+w)
  let gx := 6*(1+w)
  let start := 1+mz.length+2*(1+w)
  let bulk := start+earlier.length*gw
  (6*x.length+3*(earlier.length+1)+2) +
    ((16*mz.length+31 + (2*(16*(1+mz.length+2*(1+w))+16*w+31)+2)) + 2 +
      (earlier.length*(3*(16*(start+earlier.length*gw+gw)+16*w+31)+4)+2+
        (16*bulk+16*w+31 + (4+x.length*(6*(16*(bulk+1+w+x.length*gx+gx)+16*w+31)+4)))))

def decodeBound (width n : Nat) : Nat :=
  30*(width+n*(width+1))+20 + (n+1)*(7*width+30*((n+1)*(width+1))+26)

/-- Explicit polynomial bound for pair setup, scan, handoff and physical
frame removal. The variable `n` is exactly the number of ordinary frames. -/
theorem total_cost_bound (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hz : z.length = width) (ho : o.length = width) :
    scanCost mz mo z o x earlier b + 2 + decodeCost z o x earlier width b ≤
      scanBound mz z o x earlier + 2 + decodeBound width (6*x.length+3*earlier.length+3) := by
  have hs := Shared.Codes.FiniteProgramPairStartupAll.pair_cost_bound mz mo z o x earlier b
  change scanCost mz mo z o x earlier b ≤ scanBound mz z o x earlier at hs
  have hd := Shared.Codes.FiniteProgramMarkedFrameStart.run_marked_cost_bound z o width hz ho (restBits x earlier b)
  change decodeCost z o x earlier width b ≤ decodeBound width (restBits x earlier b).length at hd
  rw [restBits_length] at hd
  exact Nat.add_le_add (Nat.add_le_add hs (Nat.le_refl 2)) hd

/-- The physically decoded tagged words are precisely the translated TM2
input words. Raw-bit conversion and head positioning are separate steps. -/
theorem run_tm2_pair_decode (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let input := BitstringEncoding.bitEncode (x,earlier++[b])
    let allWords := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc (input.map inp.symm)
    let finalTape := tapeAt (cursor false [false] allWords).2
      ((cursor false [false] allWords).1::false::false::padding (restBits x earlier b).length
        [false,false,false,false,false])
    ∃ d, run (program mz mo z o width) (initial input)
        (scanCost mz mo z o x earlier b + 2 + decodeCost z o x earlier width b) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o).length+47+empty width ∧ TapeRel d.2 finalTape := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  have hs : selected z o = Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
    funext bit
    cases bit <;> rfl
  have hw : words mz z o x earlier b =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
    change mz ++ (restBits x earlier b).flatMap (selected z o) = _
    rw [hs]
    exact (Shared.Codes.FiniteProgramMarkedWitness.tm2_pair_words tm enc inp x earlier b).symm
  obtain ⟨d,hr,hstate,htape⟩ := run_pair_decode mz mo z o x earlier width b
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)
  rw [hw] at htape
  exact ⟨d,hr,hstate,htape⟩

namespace Fixtures
example : valid (program [true] [false] [false] [true] 1) = true :=
  program_valid [true] [false] [false] [true] 1
example : (program [true] [false] [false] [true] 1).length = 739 := by
  simpa using program_length [true] [false] [false] [true] 1
example : (restBits [false] [] true).length = 9 := by decide
end Fixtures

end Shared.Codes.FiniteProgramPairDecodeAll
