import Shared.Codes.FiniteProgramEmptyWitnessDecode
import Shared.Codes.FiniteProgramScanHead
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Link the raw-pair serializer and physical frame decoder to the reflected
untagger and head positioning table. -/
namespace Shared.Codes.FiniteProgramEmptyWitnessHead
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus step_shift run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (selected)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base := Shared.Codes.FiniteProgramEmptyWitnessDecode.program
def stop (mz mo z o : List Bool) (width : Nat) : Nat :=
  (Shared.Codes.FiniteProgramEmptyWitnessDecode.handoffPre mz mo z o).length+47+empty width

theorem base_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (base mz mo z o width) (stop mz mo z o width,t) = some (.inl false) := by
  have hc : ((47+empty width,t) : Config).1 < (Shared.Codes.FiniteProgramFrameStart.program width).length := by
    simp [empty,Shared.Codes.FiniteProgramFrameStart.program_length]; omega
  have h := step_shift (Shared.Codes.FiniteProgramEmptyWitnessDecode.handoffPre mz mo z o)
    (Shared.Codes.FiniteProgramFrameStart.program width) [] (47+empty width,t) hc
  rw [Shared.Codes.FiniteProgramScanRaw.frame_start_empty width t] at h
  simpa [base,stop,Shared.Codes.FiniteProgramEmptyWitnessDecode.program,shiftConfig,shiftStatus,Nat.add_assoc] using h

theorem stop_bound (mz mo z o : List Bool) (width : Nat) : stop mz mo z o width < (base mz mo z o width).length := by
  simp [stop,empty,base,Shared.Codes.FiniteProgramEmptyWitnessDecode.program,link,
    Shared.Codes.FiniteProgramEmptyWitnessDecode.handoffPre_length,Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

def handoffPre (mz mo z o : List Bool) (width : Nat) : Program :=
  (base mz mo z o width).set (stop mz mo z o width) (branch (base mz mo z o width).length) ++
    [bridge ((base mz mo z o width).length+1)]

def program (mz mo z o : List Bool) (width : Nat) : Program :=
  link (handoffPre mz mo z o width) Shared.Codes.FiniteProgramMirror.positioned []

theorem handoffPre_length (mz mo z o : List Bool) (width : Nat) :
    (handoffPre mz mo z o width).length = (base mz mo z o width).length+1 := by simp [handoffPre]

theorem program_length (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width).length = 447+3*mz.length+3*mo.length+18*z.length+18*o.length+8*width := by
  simp [program,link,handoffPre_length,base,Shared.Codes.FiniteProgramEmptyWitnessDecode.program_length,
    Shared.Codes.FiniteProgramMirror.positioned_length]
  omega

theorem base_other (mz mo z o : List Bool) (width : Nat) (d : Config)
    (hd : d.1 < (base mz mo z o width).length) (hne : d.1 ≠ stop mz mo z o width) :
    step (base mz mo z o width) d = step (program mz mo z o width) d := by
  have h : (program mz mo z o width)[d.1]? = (base mz mo z o width)[d.1]? := by
    simp [program,link,handoffPre,List.getElem?_append_left,hd,Ne.symm hne]
  simp [step,h]

theorem stop_row (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width)[stop mz mo z o width]? = some (branch (base mz mo z o width).length) := by
  have hs := stop_bound mz mo z o width
  simp [program,link,handoffPre,List.getElem?_append_left,hs]

theorem bridge_row (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width)[(base mz mo z o width).length]? =
      some (bridge ((base mz mo z o width).length+1)) := by
  simp [program,link,handoffPre]

theorem handoff (mz mo z o : List Bool) (width : Nat) (b : Bool) (L R : List Bool) :
    run (program mz mo z o width) (stop mz mo z o width,tapeAt L (b::false::R)) 2 =
      some (.inr ((handoffPre mz mo z o width).length,tapeAt L (b::false::R))) := by
  have hs := stop_row mz mo z o width
  have hb := bridge_row mz mo z o width
  cases b <;> simp [run,advance,step,hs,hb,branch,bridge,tapeAt,moveTape,handoffPre_length]

theorem program_valid (mz mo z o : List Bool) (width : Nat) : valid (program mz mo z o width) = true := by
  let s := base mz mo z o width
  let d := Shared.Codes.FiniteProgramMirror.positioned
  let k := s.length+1
  let m := k+d.length
  have hl : (program mz mo z o width).length = m := by simp [program,link,handoffPre_length,m,k,s,d]
  have hs : ∀ r ∈ s, validRow s.length r.1 = true ∧ validRow s.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramEmptyWitnessDecode.program_valid mz mo z o width
    change valid s = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hd : ∀ r ∈ d, validRow d.length r.1 = true ∧ validRow d.length r.2 = true := by
    intro r hr
    have hv := Shared.Codes.FiniteProgramMirror.positioned_valid
    change valid d = true at hv
    simp only [valid,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at hv
    simpa only [Bool.and_eq_true] using hv.2 r hr
  have hdp : 0 < d.length := by simp [d,Shared.Codes.FiniteProgramMirror.positioned_length]
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
    have hr' : r ∈ s.set (stop mz mo z o width) (branch s.length) ∨ r = bridge k ∨
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


private theorem status_live (s : Status) (q : Nat) (t : Tape)
    (h : StatusRel s (some (.inr (q,t)))) :
    ∃ c, s = some (.inr c) ∧ c.1 = q ∧ TapeRel c.2 t := by
  cases s with
  | none => exact False.elim h
  | some v => cases v with
    | inl b => exact False.elim h
    | inr c => exact ⟨c,rfl,h.1,h.2⟩

private theorem program_link (mz mo z o : List Bool) (width : Nat) :
    link (handoffPre mz mo z o width) Shared.Codes.FiniteProgramMirror.positioned [] =
      program mz mo z o width := rfl

attribute [local irreducible] Shared.Codes.FinitePrograms.run
attribute [local irreducible] program handoffPre

/-- From a canonical pair with empty witness, a single table performs the scan,
physical frame removal, untagging, and head positioning. Its final tape is
blank-equivalent to the finite evaluator's input tape. -/
theorem run_empty_head (mz mo z o x : List Bool) (width : Nat)
    (hmark : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
    let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
      Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
        (sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o width).length+14 ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let bits := Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits x
  let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
  let r := padding bits.length [false,false,false,false,false]
  let source := tapeAt (cursor false [false] words).2 ((cursor false [false] words).1::false::false::r)
  let result := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length [false])
    (words ++ false::r)
  let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramEmptyWitnessDecode.run_empty_decode
    mz mo z o x width hmark hz ho
  change run (base mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))) sc = _ at hm
  change mid.1 = stop mz mo z o width at hstate
  have hc : (initial (BitstringEncoding.bitEncode (x,([] : List Bool)))).1 < (base mz mo z o width).length := by
    change 0 < _
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramEmptyWitnessDecode.program_valid mz mo z o width)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (base mz mo z o width) (program mz mo z o width)
    _ mid sc (stop mz mo z o width) false (Shared.Codes.FiniteProgramEmptyWitnessDecode.program_valid mz mo z o width)
    hc (base_stop mz mo z o width) (base_other mz mo z o width) hm
  have hsource : TapeRel mid.2 source := htape
  have htwo := handoff mz mo z o width (cursor false [false] words).1
    (cursor false [false] words).2 (false::r)
  change run (program mz mo z o width) (stop mz mo z o width,source) 2 = _ at htwo
  have hrel := run_related (program mz mo z o width) mid (stop mz mo z o width,source) hstate hsource 2
  rw [htwo] at hrel
  obtain ⟨after,hr,hqafter,htafter⟩ := status_live _ _ _ hrel
  have hdec := Shared.Codes.FiniteProgramMirror.positioned_run words [] r
  change run Shared.Codes.FiniteProgramMirror.positioned (0,source)
    (2+Shared.Codes.FiniteProgramUntag.cost words.reverse) = some (.inr (14,result)) at hdec
  have hshift := run_shift (handoffPre mz mo z o width) Shared.Codes.FiniteProgramMirror.positioned []
    Shared.Codes.FiniteProgramMirror.positioned_valid (0,source)
    (by simp [Shared.Codes.FiniteProgramMirror.positioned_length])
    (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  rw [hdec,program_link] at hshift
  have hshift' : run (program mz mo z o width) ((handoffPre mz mo z o width).length,source)
      (2+Shared.Codes.FiniteProgramUntag.cost words.reverse) =
      some (.inr ((handoffPre mz mo z o width).length+14,result)) := by
    simpa only [shiftConfig,shiftStatus,Nat.add_zero] using hshift
  have hrel' := run_related (program mz mo z o width) after ((handoffPre mz mo z o width).length,source)
    hqafter htafter (2+Shared.Codes.FiniteProgramUntag.cost words.reverse)
  rw [hshift'] at hrel'
  obtain ⟨d,hf,hqd,htd⟩ := status_live _ _ _ hrel'
  refine ⟨d,?_,hqd,?_⟩
  · change run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
      (sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
    exact hf
  · exact Eq.trans htd (Shared.Codes.FiniteProgramScanHead.result_tape_initial words bits.length)

/-- The number of raw output bits is the number of encoded pair cells times
codec width. -/
theorem words_length (mz z o x : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    (Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x).length =
      (6*x.length+1)*width := by
  let bits := Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits x
  have hbits : (bits.flatMap (selected z o)).length = bits.length*width := by
    induction bits with
    | nil => simp
    | cons bit bits ih =>
      simp only [List.flatMap_cons,List.length_append,ih,List.length_cons,Nat.succ_mul]
      rw [Shared.ComplexityBridge.FirstBlocksContent.selected_length z o width hz ho bit]
      omega
  unfold Shared.Codes.FiniteProgramEmptyWitnessDecode.words
  change (mz ++ bits.flatMap (selected z o)).length = _
  simp only [List.length_append,hm,hbits]
  have hn := Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits_length x
  change bits.length = _ at hn
  rw [hn]
  simp only [Nat.add_mul]
  omega

/-- The raw-pair initialization through final head positioning is bounded by
an explicit polynomial in the first-component length, word sizes, and codec width. -/
theorem total_cost_bound (mz mo z o x : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x
    let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
      Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
    let n := 6*x.length
    let k := (n+1)*width
    sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse) ≤
      Shared.Codes.FiniteProgramEmptyWitnessDecode.scanBound mz z o x + 2 +
        Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeBound width n + 2 + (k*(20*k+21)+6) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramEmptyWitnessDecode.total_cost_bound mz mo z o x width hz ho
  have hu := Shared.Codes.FiniteProgramMirror.positioned_cost_bound
    (Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x)
  rw [words_length mz z o x width hm hz ho] at hu
  exact Nat.add_le_add (Nat.add_le_add hs (Nat.le_refl 2)) hu

/-- The initialized raw tape is the actual translated TM2 input. The proof
covers any first component and an empty witness. -/
theorem run_tm2_empty_head (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x : List Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let words := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm)
    let sc := Shared.Codes.FiniteProgramEmptyWitnessDecode.scanCost mz mo z o x + 2 +
      Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeCost z o x width
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,([] : List Bool))))
        (sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o width).length+14 ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
  let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
  let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
  let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
  have hs : selected z o = Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false := by
    funext bit
    cases bit <;> rfl
  have hrev : ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm).reverse =
      inp.symm false :: (Shared.Codes.FiniteProgramEmptyWitnessDecode.restBits x).map inp.symm := by
    rw [← List.map_reverse,Shared.Codes.FiniteProgramEmptyWitness.pair_reverse]
    rfl
  have hw : Shared.Codes.FiniteProgramEmptyWitnessDecode.words mz z o x =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,([] : List Bool))).map inp.symm) := by
    rw [Shared.ComplexityBridge.TM2InputWords.inputBits_reverse_cons tm enc _ _ _ hrev]
    simp only [Shared.Codes.FiniteProgramEmptyWitnessDecode.words,hs,List.flatMap_map]
    rfl
  have h := run_empty_head mz mo z o x width
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)
  rw [hw] at h
  exact h

namespace Fixtures
example : valid (program [true] [false] [false] [true] 1) = true :=
  program_valid [true] [false] [false] [true] 1
example : (program [true] [false] [false] [true] 1).length = 497 := by
  simpa using program_length [true] [false] [false] [true] 1
example : ∃ n d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([] : List Bool),([] : List Bool)))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_empty_head [] [] [] [] [] 0 rfl rfl rfl
  exact ⟨_,d,hr⟩
example : ∃ n d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([true] : List Bool),([] : List Bool)))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_empty_head [] [] [] [] [true] 0 rfl rfl rfl
  exact ⟨_,d,hr⟩
end Fixtures

end Shared.Codes.FiniteProgramEmptyWitnessHead
