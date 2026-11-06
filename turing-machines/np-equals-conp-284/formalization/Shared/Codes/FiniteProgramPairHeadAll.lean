import Shared.Codes.FiniteProgramPairDecodeAll
import Shared.Codes.FiniteProgramScanHead
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Link the raw-pair serializer and physical frame decoder to the reflected
untagger and head positioning table. -/
namespace Shared.Codes.FiniteProgramPairHeadAll
open Shared.Codes.FinitePrograms
open Shared.Codes.FiniteProgramLink (link shiftPair shiftConfig shiftStatus step_shift run_shift)
open Shared.Codes.FiniteProgramExtendAdvance (branch bridge)
open Shared.Codes.FiniteProgramTapeEquiv (TapeRel StatusRel run_related)
open Shared.Codes.FiniteProgramCrossTag (cursor)
open Shared.Codes.FiniteProgramFrameLoop (padding empty)
open Shared.ComplexityBridge.FirstBlocksContent (selected)
open Shared.ComplexityBridge.PairMarkedScanner (tapeAt)
open Shared.ComplexityBridge.TM0FiniteProgram (run_continue)

abbrev base := Shared.Codes.FiniteProgramPairDecodeAll.program
def stop (mz mo z o : List Bool) (width : Nat) : Nat :=
  (Shared.Codes.FiniteProgramPairDecodeAll.handoffPre mz mo z o).length+47+empty width

theorem base_stop (mz mo z o : List Bool) (width : Nat) (t : Tape) :
    step (base mz mo z o width) (stop mz mo z o width,t) = some (.inl false) := by
  have hc : ((47+empty width,t) : Config).1 < (Shared.Codes.FiniteProgramFrameStart.program width).length := by
    simp [empty,Shared.Codes.FiniteProgramFrameStart.program_length]; omega
  have h := step_shift (Shared.Codes.FiniteProgramPairDecodeAll.handoffPre mz mo z o)
    (Shared.Codes.FiniteProgramFrameStart.program width) [] (47+empty width,t) hc
  rw [Shared.Codes.FiniteProgramScanRaw.frame_start_empty width t] at h
  simpa [base,stop,Shared.Codes.FiniteProgramPairDecodeAll.program,shiftConfig,shiftStatus,Nat.add_assoc] using h

theorem stop_bound (mz mo z o : List Bool) (width : Nat) : stop mz mo z o width < (base mz mo z o width).length := by
  simp [stop,empty,base,Shared.Codes.FiniteProgramPairDecodeAll.program,link,
    Shared.Codes.FiniteProgramPairDecodeAll.handoffPre_length,Shared.Codes.FiniteProgramFrameStart.program_length]
  omega

def handoffPre (mz mo z o : List Bool) (width : Nat) : Program :=
  (base mz mo z o width).set (stop mz mo z o width) (branch (base mz mo z o width).length) ++
    [bridge ((base mz mo z o width).length+1)]

def program (mz mo z o : List Bool) (width : Nat) : Program :=
  link (handoffPre mz mo z o width) Shared.Codes.FiniteProgramMirror.positioned []

theorem handoffPre_length (mz mo z o : List Bool) (width : Nat) :
    (handoffPre mz mo z o width).length = (base mz mo z o width).length+1 := by simp [handoffPre]

theorem program_length (mz mo z o : List Bool) (width : Nat) :
    (program mz mo z o width).length = 699+3*mz.length+3*mo.length+36*z.length+36*o.length+8*width := by
  simp [program,link,handoffPre_length,base,Shared.Codes.FiniteProgramPairDecodeAll.program_length,
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
    have hv := Shared.Codes.FiniteProgramPairDecodeAll.program_valid mz mo z o width
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

/-- From a canonical pair with nonempty witness, a single table performs the scan,
physical frame removal, untagging, and head positioning. Its final tape is
blank-equivalent to the finite evaluator's input tape. -/
theorem run_pair_head (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hmark : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
    let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
      Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
        (sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = some (.inr d) ∧
      d.1 = (handoffPre mz mo z o width).length+14 ∧ TapeRel d.2 (initial words).2 := by
  dsimp only
  let bits := Shared.Codes.FiniteProgramPairDecodeAll.restBits x earlier b
  let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
  let r := padding bits.length [false,false,false,false,false]
  let source := tapeAt (cursor false [false] words).2 ((cursor false [false] words).1::false::false::r)
  let result := tapeAt (false::false::Shared.Codes.FiniteProgramUntag.padding words.length [false])
    (words ++ false::r)
  let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
    Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
  obtain ⟨mid,hm,hstate,htape⟩ := Shared.Codes.FiniteProgramPairDecodeAll.run_pair_decode
    mz mo z o x earlier width b hmark hz ho
  change run (base mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b]))) sc = _ at hm
  change mid.1 = stop mz mo z o width at hstate
  have hc : (initial (BitstringEncoding.bitEncode (x,earlier++[b]))).1 < (base mz mo z o width).length := by
    change 0 < _
    exact Shared.Codes.FiniteProgramLink.valid_nonempty _
      (Shared.Codes.FiniteProgramPairDecodeAll.program_valid mz mo z o width)
  have hfirst := Shared.Codes.FiniteProgramFirstEntry.first_entry (base mz mo z o width) (program mz mo z o width)
    _ mid sc (stop mz mo z o width) false (Shared.Codes.FiniteProgramPairDecodeAll.program_valid mz mo z o width)
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
  · change run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
      (sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse)) = _
    rw [Nat.add_assoc,run_continue _ _ _ _ _ hfirst,run_continue _ _ _ _ _ hr]
    exact hf
  · exact Eq.trans htd (Shared.Codes.FiniteProgramScanHead.result_tape_initial words bits.length)

/-- The number of raw output bits is the number of encoded pair cells times
codec width. -/
theorem words_length (mz z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    (Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b).length =
      (6*x.length+3*earlier.length+4)*width := by
  let bits := Shared.Codes.FiniteProgramPairDecodeAll.restBits x earlier b
  have hbits : (bits.flatMap (selected z o)).length = bits.length*width := by
    induction bits with
    | nil => simp
    | cons bit bits ih =>
      simp only [List.flatMap_cons,List.length_append,ih,List.length_cons,Nat.succ_mul]
      rw [Shared.ComplexityBridge.FirstBlocksContent.selected_length z o width hz ho bit]
      omega
  unfold Shared.Codes.FiniteProgramPairDecodeAll.words
  change (mz ++ bits.flatMap (selected z o)).length = _
  simp only [List.length_append,hm,hbits]
  have hn := Shared.Codes.FiniteProgramPairDecodeAll.restBits_length x earlier b
  change bits.length = _ at hn
  rw [hn]
  simp only [Nat.add_mul]
  omega

/-- The raw-pair initialization through final head positioning is bounded by
an explicit polynomial in both input lengths and the codec width. -/
theorem total_cost_bound (mz mo z o x earlier : List Bool) (width : Nat) (b : Bool)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    let words := Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b
    let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
      Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
    let n := 6*x.length+3*earlier.length+3
    let k := (n+1)*width
    sc+2+(2+Shared.Codes.FiniteProgramUntag.cost words.reverse) ≤
      Shared.Codes.FiniteProgramPairDecodeAll.scanBound mz z o x earlier + 2 +
        Shared.Codes.FiniteProgramPairDecodeAll.decodeBound width n + 2 + (k*(20*k+21)+6) := by
  dsimp only
  have hs := Shared.Codes.FiniteProgramPairDecodeAll.total_cost_bound mz mo z o x earlier width b hz ho
  have hu := Shared.Codes.FiniteProgramMirror.positioned_cost_bound
    (Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b)
  rw [words_length mz z o x earlier width b hm hz ho] at hu
  exact Nat.add_le_add (Nat.add_le_add hs (Nat.le_refl 2)) hu

/-- The initialized raw tape is the actual translated TM2 input. The proof
covers any first component and nonempty witnesses. -/
theorem run_tm2_pair_head (tm : Turing.FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (inp : tm.Γ tm.k₀ ≃ Bool) (x earlier : List Bool) (b : Bool) :
    let mz := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true false
    let mo := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp true true
    let z := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false false
    let o := Shared.ComplexityBridge.TM2SelectInputWord.word tm enc inp false true
    let words := Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
      ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm)
    let sc := Shared.Codes.FiniteProgramPairDecodeAll.scanCost mz mo z o x earlier b + 2 +
      Shared.Codes.FiniteProgramPairDecodeAll.decodeCost z o x earlier width b
    ∃ d, run (program mz mo z o width) (initial (BitstringEncoding.bitEncode (x,earlier++[b])))
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
  have hw : Shared.Codes.FiniteProgramPairDecodeAll.words mz z o x earlier b =
      Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc
        ((BitstringEncoding.bitEncode (x,earlier++[b])).map inp.symm) := by
    change mz ++ (Shared.Codes.FiniteProgramPairDecodeAll.restBits x earlier b).flatMap (selected z o) = _
    rw [hs]
    exact (Shared.Codes.FiniteProgramMarkedWitness.tm2_pair_words tm enc inp x earlier b).symm
  have h := run_pair_head mz mo z o x earlier width b
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp true false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false false)
    (Shared.ComplexityBridge.TM2SelectInputWord.word_length tm enc inp false true)
  rw [hw] at h
  exact h

namespace Fixtures
-- Both singleton and longer witnesses initialize a raw pair with empty input.
example : ∃ n d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([] : List Bool),[true]))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_pair_head [] [] [] [] [] [] 0 true rfl rfl rfl
  exact ⟨_,d,hr⟩
example : ∃ n d, run (program [] [] [] [] 0)
    (initial (BitstringEncoding.bitEncode (([] : List Bool),[false,true]))) n = some (.inr d) := by
  obtain ⟨d,hr,_,_⟩ := run_pair_head [] [] [] [] [] [false] 0 true rfl rfl rfl
  exact ⟨_,d,hr⟩
example : valid (program [true] [false] [false] [true] 1) = true :=
  program_valid [true] [false] [false] [true] 1
example : (program [true] [false] [false] [true] 1).length = 785 := by
  simpa using program_length [true] [false] [false] [true] 1
example : (Shared.Codes.FiniteProgramPairDecodeAll.words [true] [false] [true] [false] [] true).length = 10 := by decide
end Fixtures

end Shared.Codes.FiniteProgramPairHeadAll
