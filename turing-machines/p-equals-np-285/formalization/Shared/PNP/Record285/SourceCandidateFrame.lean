import Shared.PNP.Record285.SourceCandidateStep

/-! Candidate input-frame construction, at graph rows 93--119. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceCandidateFrame
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceCandidateStep

/-- The five checked rows add register 14 into register 2 and restore the
source; the arbitrary initial auxiliary value is included in the exact effect. -/
def copyAddRaw (bank : Nat → Nat) : Nat → Nat :=
  update (.move 4 14) (splitResult 14 2 4 bank)

theorem copy_add_run (rows : Array Row) (head a b restore body exit : Nat)
    (h0 : rows[head]? = some ⟨.dec 14,a,restore⟩)
    (h1 : rows[a]? = some ⟨.inc 2,b,b⟩)
    (h2 : rows[b]? = some ⟨.inc 4,head,head⟩)
    (h3 : rows[restore]? = some ⟨.dec 4,body,exit⟩)
    (h4 : rows[body]? = some ⟨.inc 14,restore,restore⟩)
    (bank : Nat → Nat) :
    Silent rows ⟨head,bank⟩ ⟨exit,copyAddRaw bank⟩
      (3*bank 14+1 + (2*(bank 4+bank 14)+1)) := by
  let mid := splitResult 14 2 4 bank
  have hsplit := split_run rows head a b restore 14 2 4 (bank 14) bank h0 h1 h2
    (by decide) (by decide) (by decide) rfl
  have hv : mid 4 = bank 4+bank 14 := by simp [mid,splitResult]
  have hmove := expanded_move_run rows restore body exit 4 14 (bank 4+bank 14) mid
    h3 h4 (by decide) hv
  exact silent_trans rows _ _ _ _ _ hsplit hmove

theorem copy_add_clean (bank : Nat → Nat) (h4 : bank 4 = 0) :
    copyAddRaw bank = put 2 (bank 2+bank 14) bank := by
  funext j
  by_cases h14 : j=14
  · subst j; simp [copyAddRaw,update,splitResult,put,h4]
  · by_cases h2 : j=2
    · subst j; simp [copyAddRaw,update,splitResult,put]
    · by_cases h4j : j=4
      · subst j; simp [copyAddRaw,update,put,h4]
      · simp [copyAddRaw,update,splitResult,put,h14,h2,h4j]

/-- One complete cycle of the input-frame multiplication loop. -/
def frameCycle (bank : Nat → Nat) : Nat → Nat :=
  put 6 (bank 6+1) (put 15 (bank 15-1) (put 2 (bank 2+2*bank 14) bank))

theorem frame_cycle_run (bank : Nat → Nat) (h4 : bank 4 = 0) (hp : 0 < bank 15) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨102,bank⟩ ⟨102,frameCycle bank⟩ duration := by
  let first := update (.inc 6) (update (.dec 15) bank)
  have hn : bank 15 ≠ 0 := by omega
  have hs : step originalRows ⟨102,bank⟩ = (⟨103,update (.dec 15) bank⟩,false) := by
    simp [step,originalRows,observe,hn]
  have ht : step originalRows ⟨103,update (.dec 15) bank⟩ = (⟨104,first⟩,false) := by
    simp [step,originalRows,observe,first]
  have hfirst := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  have h4first : first 4 = 0 := by simp [first,update,h4]
  let middle := copyAddRaw first
  have hcopy1 := copy_add_run originalRows 104 105 106 107 108 109
    (by decide) (by decide) (by decide) (by decide) (by decide) first
  have hmiddle : middle = put 2 (first 2+first 14) first := copy_add_clean first h4first
  have h4middle : middle 4 = 0 := by simp [hmiddle,put,h4first]
  have hcopy2 := copy_add_run originalRows 109 110 111 112 113 102
    (by decide) (by decide) (by decide) (by decide) (by decide) middle
  have hlast := copy_add_clean middle h4middle
  have heffect : copyAddRaw middle = frameCycle bank := by
    rw [hlast,hmiddle]
    funext j
    by_cases h6 : j=6
    · subst j; simp [frameCycle,first,put,update]
    · by_cases h15 : j=15
      · subst j; simp [frameCycle,first,put,update]
      · by_cases h2 : j=2
        · subst j; simp [frameCycle,first,put,update]; omega
        · simp [frameCycle,first,put,update,h6,h15,h2]
  have h := silent_trans originalRows _ _ _ _ _ hfirst hcopy1
  have h := silent_trans originalRows _ _ _ _ _ h hcopy2
  refine ⟨2 + (3*first 14+1 + (2*(first 4+first 14)+1)) +
    (3*middle 14+1 + (2*(middle 4+middle 14)+1)),by omega,?_⟩
  simpa [heffect] using h

def frameLoopResult (bank : Nat → Nat) : Nat → Nat :=
  put 6 (bank 6+bank 15) (put 15 0 (put 2 (bank 2+2*bank 14*bank 15) bank))

theorem frame_loop_cycle (bank : Nat → Nat) (hp : 0 < bank 15) :
    frameLoopResult (frameCycle bank) = frameLoopResult bank := by
  funext j
  by_cases h6 : j=6
  · subst j; simp [frameLoopResult,frameCycle,put]; omega
  · by_cases h15 : j=15
    · subst j; simp [frameLoopResult,put]
    · by_cases h2 : j=2
      · subst j
        simp [frameLoopResult,frameCycle,put]
        have hh : bank 15-1+1 = bank 15 := by omega
        have hm : 2*bank 14*bank 15 = 2*bank 14*(bank 15-1) + 2*bank 14 := by
          calc
            2*bank 14*bank 15 = 2*bank 14*(bank 15-1+1) := congrArg (fun x => 2*bank 14*x) hh.symm
            _ = _ := by simp [Nat.mul_add]
        rw [hm]
        omega
      · simp [frameLoopResult,frameCycle,put,h6,h15,h2]

/-- The complete multiplication loop terminates for arbitrary finite input,
with a precise whole-bank effect and no event. -/
theorem frame_loop (n : Nat) (bank : Nat → Nat) (h4 : bank 4 = 0) (hn : bank 15 = n) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨102,bank⟩ ⟨114,frameLoopResult bank⟩ duration := by
  induction n generalizing bank with
  | zero =>
    have hz : bank 15 = 0 := hn
    have hid := dec_at_zero 15 bank hz
    have hs : step originalRows ⟨102,bank⟩ = (⟨114,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    have heffect : frameLoopResult bank = bank := by
      funext j
      by_cases h6 : j=6
      · subst j; simp [frameLoopResult,put,hz]
      · by_cases h15 : j=15
        · subst j; simp [frameLoopResult,put,hz]
        · by_cases h2 : j=2
          · subst j; simp [frameLoopResult,put,hz]
          · simp [frameLoopResult,put,h6,h15,h2]
    exact ⟨1,by decide,by simpa [heffect] using silent_one originalRows _ _ hs⟩
  | succ n ih =>
    have hp : 0 < bank 15 := by omega
    obtain ⟨d,hd,hcycle⟩ := frame_cycle_run bank h4 hp
    have h4' : frameCycle bank 4 = 0 := by simp [frameCycle,put,h4]
    have hn' : frameCycle bank 15 = n := by simp [frameCycle,put]; omega
    obtain ⟨e,he,hrest⟩ := ih (frameCycle bank) h4' hn'
    rw [frame_loop_cycle bank hp] at hrest
    exact ⟨d+e,by omega,silent_trans originalRows _ _ _ _ _ hcycle hrest⟩

/-- The three scratch-clears, initial radix copy and saturating predecessor. -/
def frameStart (bank : Nat → Nat) : Nat → Nat :=
  update (.dec 2) (copyAddRaw (clear 2 (clear 3 (clear 19 bank))))

theorem frame_start_run (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨93,bank⟩ ⟨102,frameStart bank⟩ duration := by
  let b1 := clear 19 bank
  let b2 := clear 3 b1
  let b3 := clear 2 b2
  let b4 := copyAddRaw b3
  have h93 : originalRows[93]? = some ⟨.dec 19,93,94⟩ := by decide
  have h94 : originalRows[94]? = some ⟨.dec 3,94,95⟩ := by decide
  have h95 : originalRows[95]? = some ⟨.dec 2,95,96⟩ := by decide
  have hc1 := clear_run originalRows 93 94 19 (bank 19) bank h93 rfl
  have hc2 := clear_run originalRows 94 95 3 (b1 3) b1 h94 rfl
  have hc3 := clear_run originalRows 95 96 2 (b2 2) b2 h95 rfl
  have hcopy := copy_add_run originalRows 96 97 98 99 100 101
    (by decide) (by decide) (by decide) (by decide) (by decide) b3
  have h101 : step originalRows ⟨101,b4⟩ = (⟨102,update (.dec 2) b4⟩,false) := by
    simp [step,originalRows,observe]
  have h := silent_trans originalRows _ _ _ _ _ hc1 hc2
  have h := silent_trans originalRows _ _ _ _ _ h hc3
  have h := silent_trans originalRows _ _ _ _ _ h hcopy
  have h := silent_trans originalRows _ _ _ _ _ h (silent_one _ _ _ h101)
  refine ⟨(bank 19+1)+(b1 3+1)+(b2 2+1)+
    (3*b3 14+1+(2*(b3 4+b3 14)+1))+1,by omega,?_⟩
  simpa [frameStart,b4,b3,b2,b1] using h

def frameRestored (bank : Nat → Nat) : Nat → Nat :=
  update (.move 6 15) (frameLoopResult (frameStart bank))

def frameOutput (bank : Nat → Nat) : Nat → Nat :=
  let b := frameRestored bank
  put 3 (2*(b 2%2)) (put 2 (b 2/2) b)

/-- The final move and input-bit extraction reach the evaluator entry. -/
theorem frame_finish_run (bank : Nat → Nat) (h3 : frameRestored bank 3 = 0) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨114,frameLoopResult (frameStart bank)⟩
      ⟨119,frameOutput bank⟩ duration := by
  let b := frameLoopResult (frameStart bank)
  let r := frameRestored bank
  have h114 : originalRows[114]? = some ⟨.dec 6,115,116⟩ := by decide
  have h115 : originalRows[115]? = some ⟨.inc 15,114,114⟩ := by decide
  have hm := expanded_move_run originalRows 114 115 116 6 15 (b 6) b h114 h115 (by decide) rfl
  change Silent originalRows ⟨114,b⟩ ⟨116,r⟩ (2*b 6+1) at hm
  let half := update (.half 2) r
  by_cases hz : r 2%2=0
  · have hs : step originalRows ⟨116,r⟩ = (⟨119,half⟩,false) := by
      simp [step,originalRows,observe,hz,half]
    have heffect : half = frameOutput bank := by
      funext j
      by_cases h2 : j=2
      · subst j; simp [frameOutput,r,half,put,update]
      · by_cases h3j : j=3
        · subst j; simp [frameOutput,r,half,put,update,h3,hz]
        · simp [frameOutput,r,half,put,update,h2,h3j]
    have h := silent_trans originalRows _ _ _ _ 1 hm (silent_one _ _ _ hs)
    exact ⟨2*b 6+1+1,by omega,by simpa [heffect] using h⟩
  · have ho : r 2%2=1 := by omega
    let one := update (.inc 3) half
    let two := update (.inc 3) one
    have hs : step originalRows ⟨116,r⟩ = (⟨117,half⟩,false) := by
      simp [step,originalRows,observe,hz,half]
    have ht : step originalRows ⟨117,half⟩ = (⟨118,one⟩,false) := by
      simp [step,originalRows,observe,one]
    have hu : step originalRows ⟨118,one⟩ = (⟨119,two⟩,false) := by
      simp [step,originalRows,observe,two]
    have heffect : two = frameOutput bank := by
      funext j
      by_cases h2 : j=2
      · subst j; simp [frameOutput,r,two,one,half,put,update]
      · by_cases h3j : j=3
        · subst j; simp [frameOutput,r,two,one,half,put,update,h3,ho]
        · simp [frameOutput,r,two,one,half,put,update,h2,h3j]
    have h := silent_trans originalRows _ _ _ _ 1 hm (silent_one _ _ _ hs)
    have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ ht)
    have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ hu)
    exact ⟨2*b 6+1+1+1+1,by omega,by simpa [heffect] using h⟩

/-- Candidate frame construction always finishes for finite stores. -/
theorem frame_raw_terminates (bank : Nat → Nat) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨93,bank⟩ ⟨119,frameOutput bank⟩ duration := by
  have h4 : frameStart bank 4 = 0 := by
    simp [frameStart,copyAddRaw,update]
  have h3 : frameRestored bank 3 = 0 := by
    simp [frameRestored,frameLoopResult,frameStart,copyAddRaw,splitResult,clear,put,update]
  obtain ⟨d,hd,hstart⟩ := frame_start_run bank
  obtain ⟨e,he,hloop⟩ := frame_loop ((frameStart bank) 15) (frameStart bank) h4 rfl
  obtain ⟨f,hf,hfinish⟩ := frame_finish_run bank h3
  have h := silent_trans originalRows _ _ _ _ _ hstart hloop
  have h := silent_trans originalRows _ _ _ _ _ h hfinish
  exact ⟨d+e+f,by omega,h⟩

theorem frame_start_clean (bank : Nat → Nat) (h4 : bank 4 = 0) :
    frameStart bank = put 2 (bank 14-1) (clear 3 (clear 19 bank)) := by
  have h4' : (clear 2 (clear 3 (clear 19 bank))) 4 = 0 := by simp [clear,h4]
  unfold frameStart
  rw [copy_add_clean _ h4']
  funext j
  by_cases h2 : j=2
  · subst j; simp [put,clear,update]
  · simp [put,clear,update,h2]

/-- With the zero auxiliary values supplied by the clock builder, the whole
bank entering the evaluator has exactly the source frame and retains all other
cells. Zero radix is included. -/
theorem frame_output_clean (bank : Nat → Nat) (h4 : bank 4 = 0) (h6 : bank 6 = 0) :
    frameOutput bank =
      put 3 (2*(Source.frame (bank 14) (bank 15)%2))
        (put 2 (Source.frame (bank 14) (bank 15)/2) (clear 19 bank)) := by
  have hs := frame_start_clean bank h4
  have hframe : bank 14-1+2*bank 14*bank 15 = Source.frame (bank 14) (bank 15) := by
    by_cases hz : bank 14 = 0
    · simp [Source.frame,hz]
    · have hp : 0 < bank 14 := by omega
      have hm : 2*bank 14*bank 15 = 2*(bank 15*bank 14) := by
        simp [Nat.mul_assoc,Nat.mul_comm]
      rw [hm]
      simp only [Source.frame]
      omega
  funext j
  by_cases h3 : j=3
  · subst j
    simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h6,hframe]
  · by_cases h2 : j=2
    · subst j
      simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h6,hframe]
    · by_cases h19 : j=19
      · subst j; simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h6]
      · by_cases h15 : j=15
        · subst j; simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h6]
        · by_cases h6j : j=6
          · subst j; simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h6]
          · by_cases h4j : j=4
            · subst j; simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h4,h6]
            · simp [frameOutput,frameRestored,frameLoopResult,hs,put,clear,update,h3,h2,h19,h15,h6j]

/-- The checked frame constructor and bounded evaluator compose into one
source-candidate evaluation. The clock equation is an explicit premise here, discharged by the
preceding exponentiation proof in `SourceCandidateClock`. -/
theorem frame_candidate_evaluate (bank : Nat → Nat) (hready : ReferenceReady bank)
    (h6 : bank 6 = 0) (hclock : bank 20 = (bank 13+2)^(bank 12)) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨93,bank⟩ ⟨154,out⟩ duration ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.candidate (bank 11) (bank 12) (bank 13) (bank 14) (bank 15)
        then (if bank 16=0 then 1 else 0) else bank 16) := by
  let mid := frameOutput bank
  have hv := frame_output_clean bank hready.1 h6
  have hmidready : ReferenceReady mid := by
    simp [ReferenceReady,mid,hv,put,clear,hready.1,hready.2.1,hready.2.2]
  have hmidframe : ∀ j, Protected j → mid j = bank j := by
    intro j hj
    have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
    have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
    have h19 : j ≠ 19 := by simp only [Protected] at hj; omega
    simp [mid,hv,put,clear,h3,h2,h19]
  have hstate : candidateState mid =
      ⟨0,Source.frame (bank 14) (bank 15)/2,2*(Source.frame (bank 14) (bank 15)%2),0⟩ := by
    simp [candidateState,mid,hv,put,clear]
  have hprog : mid 11 = bank 11 := by simp [mid,hv,put,clear]
  have hclock' : mid 20 = (bank 13+2)^(bank 12) := by simp [mid,hv,put,clear,hclock]
  have hexpected : mid 16 = bank 16 := by simp [mid,hv,put,clear]
  obtain ⟨d,hd,hframe⟩ := frame_raw_terminates bank
  obtain ⟨out,e,he,heval,hout,hprotected,hresult⟩ := candidate_evaluator (mid 20) mid hmidready rfl
  have hframes : ∀ j, Protected j → out j = bank j := by
    intro j hj; exact (hprotected j hj).trans (hmidframe j hj)
  refine ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hframe heval,hout,hframes,?_⟩
  simp only [hprog,hclock',hstate,hexpected] at hresult
  exact hresult

/-- Reachable pre-control grammar composition, retaining exact event silence
and the complete output bank. -/
theorem frame_candidate_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨93,bank⟩)
    (hready : ReferenceReady bank) (h6 : bank 6 = 0)
    (hclock : bank 20 = (bank 13+2)^(bank 12)) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t < PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.acceptedRefinement.boundary (t+duration) ≤
        PreControlGrammar.acceptedRefinement.boundary t + 32*duration ∧
      PreControlGrammar.positions[154]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.candidate (bank 11) (bank 12) (bank 13) (bank 14) (bank 15)
        then (if bank 16=0 then 1 else 0) else bank 16) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hout,hframe,hresult⟩ := frame_candidate_evaluate bank hready h6 hclock
  have h := transfer_silent_graph t d 93 154 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.1,h.2.2.1,h.2.2.2.1,hout,hframe,hresult,h.2.2.2.2⟩

end Shared.PNP.Record285.SourceCandidateFrame
