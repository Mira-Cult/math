import Shared.Beeping.NPcoNP.Source284CertificateHandoff
import Shared.Beeping.NPcoNP.Source284TaggedWitnessCodec

/-! Two paid source transitions dispatch on the tagged witness codec's two
low bits. Both outcomes retain the complete tape; the success continuation
sees the quotient after those bits, while the failure continuation is reached
for every malformed tag. This does not decode the witness, enforce its
original cutoff, or provide a physical 284-state refinement. -/
set_option maxRecDepth 4096
namespace Shared.Beeping.NPcoNP.Source284TaggedHandoff

open Shared.Beeping.NPcoNP.Source284TableEncode
open Shared.Beeping.NPcoNP.Source284TableRun
open Shared.Beeping.NPcoNP.Source284HardwireTable (shiftRow shiftConfig)
open Shared.Beeping.NPcoNP.Source284Parser (encodeFrame)

/-- Three tag-test states followed by disjoint supplied continuations. -/
def table (goodStates : Nat) (good bad : Nat → Bool → Row) (q : Nat) (b : Bool) : Row :=
  if q = 0 then ⟨b,false,some (if b then 2 else 1)⟩
  else if q = 1 then ⟨b,false,some (if b then 3+goodStates else 3)⟩
  else if q = 2 then ⟨b,false,some (3+goodStates)⟩
  else if q < 3+goodStates then shiftRow 3 (good (q-3) b)
  else shiftRow (3+goodStates) (bad (q-(3+goodStates)) b)

theorem closed (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (hg : 0 < goodStates) (hb : 0 < badStates)
    (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    Closed (3+goodStates+badStates) (table goodStates good bad) := by
  intro q hq b q' hnext
  by_cases h0 : q = 0
  · subst q; cases b <;> simp [table] at hnext <;> omega
  · by_cases h1 : q = 1
    · subst q; cases b <;> simp [table] at hnext <;> omega
    · by_cases h2 : q = 2
      · subst q; simp [table] at hnext; omega
      · by_cases hqg : q < 3+goodStates
        · have ht : (shiftRow 3 (good (q-3) b)).next = some q' := by
            simpa [table,h0,h1,h2,hqg] using hnext
          cases he : (good (q-3) b).next with
          | none => simp [shiftRow,he] at ht
          | some r =>
            have h := hgood (q-3) (by omega) b r he
            simp [shiftRow,he] at ht
            subst q'; omega
        · have ht : (shiftRow (3+goodStates) (bad (q-(3+goodStates)) b)).next = some q' := by
            simpa [table,h0,h1,h2,hqg] using hnext
          cases he : (bad (q-(3+goodStates)) b).next with
          | none => simp [shiftRow,he] at ht
          | some r =>
            have h := hbad (q-(3+goodStates)) (by omega) b r he
            simp [shiftRow,he] at ht
            subst q'; omega

/-- All four tag patterns consume exactly two steps. The two bits are moved
onto the other tape half in scan order, so even malformed tags are preserved. -/
theorem dispatch (goodStates : Nat) (good bad : Nat → Bool → Row) (left certificate : Nat) :
    run (table goodStates good bad) ⟨left,certificate,some 0⟩ 2 =
      ⟨4*left+2*(certificate%2)+(certificate/2)%2,certificate/4,
        some (if certificate%4 = 0 then 3 else 3+goodStates)⟩ := by
  have h0 : step (table goodStates good bad) ⟨left,certificate,some 0⟩ =
      ⟨2*left+certificate%2,certificate/2,some (if certificate%2=1 then 2 else 1)⟩ := by
    simp [step,table,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]
  have h1 (a c : Nat) : step (table goodStates good bad) ⟨a,c,some 1⟩ =
      ⟨2*a+c%2,c/2,some (if c%2=1 then 3+goodStates else 3)⟩ := by
    simp [step,table,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]
  have h2 (a c : Nat) : step (table goodStates good bad) ⟨a,c,some 2⟩ =
      ⟨2*a+c%2,c/2,some (3+goodStates)⟩ := by
    simp [step,table,Nat.testBit_zero,Source284WitnessScanner.bit_decide_mod]
  have hr : certificate%4 = certificate%2+2*((certificate/2)%2) := by omega
  have hd : certificate/2/2 = certificate/4 := by omega
  simp only [run,h0]
  by_cases h : certificate%2=1
  · simp only [h,↓reduceIte,h2]
    have hm : certificate%4 ≠ 0 := by omega
    simp only [hm,↓reduceIte,hd]
    congr 1 <;> omega
  · simp only [h,↓reduceIte,h1]
    by_cases h' : (certificate/2)%2=1
    · simp only [h',↓reduceIte]
      have hm : certificate%4 ≠ 0 := by omega
      simp only [hm,↓reduceIte,hd]
      congr 1 <;> omega
    · simp only [h',↓reduceIte]
      have hm : certificate%4 = 0 := by
        have ha := Nat.mod_lt certificate (by decide : 0 < 2)
        have hb := Nat.mod_lt (certificate/2) (by decide : 0 < 2)
        omega
      simp only [hm,↓reduceIte,hd]
      congr 1 <;> omega

theorem good_row (goodStates : Nat) (good bad : Nat → Bool → Row) (q : Nat) (b : Bool)
    (hq : q < goodStates) :
    table goodStates good bad (3+q) b = shiftRow 3 (good q b) := by
  simp [table,show 3+q ≠ 1 by omega,show 3+q ≠ 2 by omega,show 3+q < 3+goodStates by omega]

theorem bad_row (goodStates : Nat) (good bad : Nat → Bool → Row) (q : Nat) (b : Bool) :
    table goodStates good bad (3+goodStates+q) b = shiftRow (3+goodStates) (bad q b) := by
  simp [table,show 3+goodStates+q ≠ 1 by omega,show 3+goodStates+q ≠ 2 by omega,
    show ¬ 3+goodStates+q < 3+goodStates by omega]

theorem good_step (goodStates : Nat) (good bad : Nat → Bool → Row) (c : Config)
    (hv : Valid goodStates c) :
    step (table goodStates good bad) (shiftConfig 3 c) = shiftConfig 3 (step good c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      have hq : q < goodStates := hv q rfl
      simp only [shiftConfig,Option.map_some,step,good_row goodStates good bad q _ hq,shiftRow]
      split <;> rfl

theorem good_run (goodStates : Nat) (good bad : Nat → Bool → Row) (c : Config)
    (hc : Closed goodStates good) (hv : Valid goodStates c) (fuel : Nat) :
    run (table goodStates good bad) (shiftConfig 3 c) fuel = shiftConfig 3 (run good c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    simp only [run,ih]
    exact good_step goodStates good bad _ (valid_run goodStates good c hc hv fuel)

theorem bad_step (goodStates : Nat) (good bad : Nat → Bool → Row) (c : Config) :
    step (table goodStates good bad) (shiftConfig (3+goodStates) c) =
      shiftConfig (3+goodStates) (step bad c) := by
  cases c with
  | mk left right state =>
    cases state with
    | none => rfl
    | some q =>
      simp only [shiftConfig,Option.map_some,step,bad_row goodStates good bad q,shiftRow]
      split <;> rfl

theorem bad_run (goodStates : Nat) (good bad : Nat → Bool → Row) (c : Config) (fuel : Nat) :
    run (table goodStates good bad) (shiftConfig (3+goodStates) c) fuel =
      shiftConfig (3+goodStates) (run bad c fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [run,ih,bad_step]

/-- A rejected tag is rejected by the actual tagged witness decoder at every
witness limit, independently of the high certificate bits. -/
theorem malformed_decode (limit certificate : Nat) (h : certificate%4 ≠ 0) :
    Source284TaggedWitnessCodec.decode limit certificate = none := by
  simp [Source284TaggedWitnessCodec.decode,h]

def description (goodStates badStates : Nat) (good bad : Nat → Bool → Row) : Nat :=
  Source284CertificateHandoff.description (3+goodStates+badStates) (table goodStates good bad)

theorem source_dispatch (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (left certificate : Nat) (hg : 0 < goodStates) (hb : 0 < badStates)
    (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    Source284Relative.run (description goodStates badStates good bad)
      ⟨left,certificate,active 390⟩ 2 =
    ⟨4*left+2*(certificate%2)+(certificate/2)%2,certificate/4,
      active (390+(if certificate%4 = 0 then 3 else 3+goodStates))⟩ := by
  have hc := closed goodStates badStates good bad hg hb hgood hbad
  have hr := Source284CertificateHandoff.source_after (3+goodStates+badStates)
    (table goodStates good bad) 0 left certificate 2 (by omega) (by omega) hc
  change Source284Relative.run (description goodStates badStates good bad)
    ⟨left,certificate,active (390+0)⟩ 2 = _ at hr
  rw [dispatch] at hr
  simpa [Source284CertificateHandoff.preparedShift,shiftConfig,toSource,nextState,active,
    ← Nat.add_assoc] using hr

/-- After a valid tag, the supplied good continuation really runs in the
same encoded source table, with its finite-state invariant preserved. -/
theorem source_after_good (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (mode left right fuel : Nat) (hg : 0 < goodStates) (hb : 0 < badStates)
    (hm : mode < goodStates) (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    Source284Relative.run (description goodStates badStates good bad)
      ⟨left,right,active (393+mode)⟩ fuel =
      toSource (Source284CertificateHandoff.preparedShift
        (shiftConfig 3 (shiftConfig 1 (shiftConfig 3
          (shiftConfig 3 (run good ⟨left,right,some mode⟩ fuel)))))) := by
  have hc := closed goodStates badStates good bad hg hb hgood hbad
  have hr := Source284CertificateHandoff.source_after (3+goodStates+badStates)
    (table goodStates good bad) (3+mode) left right fuel (by omega) (by omega) hc
  have he : 390+(3+mode) = 393+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description goodStates badStates good bad) _ _ = _ at hr
  change Source284Relative.run (description goodStates badStates good bad) _ _ =
    toSource (Source284CertificateHandoff.preparedShift
      (shiftConfig 3 (shiftConfig 1 (shiftConfig 3
        (run (table goodStates good bad) (shiftConfig 3 ⟨left,right,some mode⟩) fuel))))) at hr
  have hv : Valid goodStates ⟨left,right,some mode⟩ := by
    intro q hq; simp at hq; subst q; exact hm
  rw [good_run goodStates good bad _ hgood hv] at hr
  exact hr

/-- The malformed-tag continuation is likewise a real branch of the same
encoded source table. Its behavior is supplied explicitly by the caller. -/
theorem source_after_bad (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (mode left right fuel : Nat) (hg : 0 < goodStates) (hb : 0 < badStates)
    (hm : mode < badStates) (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    Source284Relative.run (description goodStates badStates good bad)
      ⟨left,right,active (393+goodStates+mode)⟩ fuel =
      toSource (Source284CertificateHandoff.preparedShift
        (shiftConfig 3 (shiftConfig 1 (shiftConfig 3
          (shiftConfig (3+goodStates) (run bad ⟨left,right,some mode⟩ fuel)))))) := by
  have hc := closed goodStates badStates good bad hg hb hgood hbad
  have hr := Source284CertificateHandoff.source_after (3+goodStates+badStates)
    (table goodStates good bad) (3+goodStates+mode) left right fuel (by omega) (by omega) hc
  have he : 390+(3+goodStates+mode) = 393+goodStates+mode := by omega
  rw [he] at hr
  change Source284Relative.run (description goodStates badStates good bad) _ _ = _ at hr
  change Source284Relative.run (description goodStates badStates good bad) _ _ =
    toSource (Source284CertificateHandoff.preparedShift
      (shiftConfig 3 (shiftConfig 1 (shiftConfig 3
        (run (table goodStates good bad) (shiftConfig (3+goodStates) ⟨left,right,some mode⟩) fuel))))) at hr
  rw [bad_run] at hr
  exact hr

def totalCost (n : Nat) : Nat := Source284CertificateHandoff.totalCost n+2

theorem source_pipeline (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (w : List Bool) (certificate suffix : Nat) (hg : 0 < goodStates) (hb : 0 < badStates)
    (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    let right := encodeFrame w (8*Source284EqualityPipeline.finalTail w.length suffix+1)
    let left := 4^(w.length+1)*(2*right)+1
    Source284Relative.run (description goodStates badStates good bad)
      (Source284Relative.initial (encodeFrame w suffix) certificate) (totalCost w.length) =
      ⟨4*left+2*(certificate%2)+(certificate/2)%2,certificate/4,
        active (390+(if certificate%4 = 0 then 3 else 3+goodStates))⟩ := by
  have hc := closed goodStates badStates good bad hg hb hgood hbad
  have hp := Source284CertificateHandoff.source_pipeline (3+goodStates+badStates)
    (table goodStates good bad) w certificate suffix (by omega) hc
  dsimp only
  unfold totalCost
  rw [Source284Relative.run_add_clock]
  change Source284Relative.run (description goodStates badStates good bad)
    (Source284Relative.run (Source284CertificateHandoff.description (3+goodStates+badStates)
      (table goodStates good bad)) _ _) _ = _
  rw [hp,source_dispatch goodStates badStates good bad _ certificate hg hb hgood hbad]

theorem totalCost_le (n : Nat) : totalCost n ≤ 4*n*n*n+42*n*n+130*n+125 := by
  have h := Source284CertificateHandoff.totalCost_le n
  unfold totalCost
  omega

/-- On every input and certificate, the same finite source table reaches the
appropriate tag continuation within a cubic bound while retaining the exact
canonical input window inside the opposite tape half. -/
theorem source_total_progress (goodStates badStates : Nat) (good bad : Nat → Bool → Row)
    (input certificate : Nat) (hg : 0 < goodStates) (hb : 0 < badStates)
    (hgood : Closed goodStates good) (hbad : Closed badStates bad) :
    ∃ (right t : Nat),
      t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        130*(Source284Parser.length input)+125 ∧
      Source284Relative.run (description goodStates badStates good bad)
        (Source284Relative.initial input certificate) t =
      ⟨4*(4^(Source284Parser.length input+1)*(2*right)+1)+
          2*(certificate%2)+(certificate/2)%2,certificate/4,
        active (390+(if certificate%4 = 0 then 3 else 3+goodStates))⟩ ∧
      Source284CanonicalPairWindow.window (Source284PackedGuardWindow.inputBits input.bits).length right =
        Source284PackedGuardWindow.inputBits input.bits := by
  have hc := closed goodStates badStates good bad hg hb hgood hbad
  obtain ⟨right,t,ht,hr,hw⟩ := Source284CertificateHandoff.source_canonical_window
    (3+goodStates+badStates) (table goodStates good bad) input certificate (by omega) hc
  refine ⟨right,t+2,?_,?_,hw⟩
  · omega
  · rw [Source284Relative.run_add_clock]
    change Source284Relative.run (description goodStates badStates good bad)
      (Source284Relative.run (Source284CertificateHandoff.description (3+goodStates+badStates)
        (table goodStates good bad)) _ _) _ = _
    rw [hr,source_dispatch goodStates badStates good bad _ certificate hg hb hgood hbad]

/-- A total nonaccepting continuation for a malformed tag. -/
def rejectTable (_ : Nat) (b : Bool) : Row := ⟨b,false,some 0⟩

theorem reject_closed : Closed 1 rejectTable := by
  intro q hq b q' hn
  simp [rejectTable] at hn
  subst q'
  omega

theorem reject_run_state (left right fuel : Nat) :
    (run rejectTable ⟨left,right,some 0⟩ fuel).state = some 0 := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    cases hc : run rejectTable ⟨left,right,some 0⟩ fuel with
    | mk l r q =>
      have hq : q = some 0 := by simpa [hc] using ih
      subst q
      simp [run,hc,step,rejectTable]

theorem source_bad_never_accepts (goodStates : Nat) (good : Nat → Bool → Row)
    (left right fuel : Nat) (hg : 0 < goodStates) (hgood : Closed goodStates good) :
    (Source284Relative.run (description goodStates 1 good rejectTable)
      ⟨left,right,active (393+goodStates)⟩ fuel).state ≠ 0 := by
  have hr := source_after_bad goodStates 1 good rejectTable 0 left right fuel
    hg (by omega) (by omega) hgood reject_closed
  have he : 393+goodStates+0 = 393+goodStates := by omega
  rw [he] at hr
  rw [hr]
  have hs := reject_run_state left right fuel
  cases hc : run rejectTable ⟨left,right,some 0⟩ fuel with
  | mk l r q =>
    have hq : q = some 0 := by simpa [hc] using hs
    subst q
    simp [Source284CertificateHandoff.preparedShift,shiftConfig,toSource,nextState,active]

/-- Every malformed tag reaches the nonaccepting continuation in bounded
time and never accepts afterward. The original witness decoder also rejects. -/
theorem source_malformed_rejected (goodStates : Nat) (good : Nat → Bool → Row)
    (input certificate limit : Nat) (hg : 0 < goodStates) (hgood : Closed goodStates good)
    (hbad : certificate%4 ≠ 0) :
    Source284TaggedWitnessCodec.decode limit certificate = none ∧
    ∃ t, t ≤ 4*(Source284Parser.length input)^3+42*(Source284Parser.length input)^2+
        130*(Source284Parser.length input)+125 ∧
      ∀ extra, (Source284Relative.run (description goodStates 1 good rejectTable)
        (Source284Relative.initial input certificate) (t+extra)).state ≠ 0 := by
  refine ⟨malformed_decode limit certificate hbad,?_⟩
  obtain ⟨right,t,ht,hr,_⟩ := source_total_progress goodStates 1 good rejectTable
    input certificate hg (by omega) hgood reject_closed
  refine ⟨t,ht,?_⟩
  intro extra
  rw [Source284Relative.run_add_clock,hr]
  simp only [hbad,↓reduceIte]
  have he : 390+(3+goodStates) = 393+goodStates := by omega
  rw [he]
  exact source_bad_never_accepts goodStates good _ _ extra hg hgood

/-- Since source acceptance is absorbing, a malformed tag cannot have
accepted even during preparation before the rejecting continuation. -/
theorem source_malformed_never_accepts (goodStates : Nat) (good : Nat → Bool → Row)
    (input certificate : Nat) (hg : 0 < goodStates) (hgood : Closed goodStates good)
    (hbad : certificate%4 ≠ 0) :
    ∀ clock, Source284Relative.accepts (description goodStates 1 good rejectTable)
      input certificate clock = false := by
  obtain ⟨_,t,_,hfuture⟩ := source_malformed_rejected goodStates good input certificate 0 hg hgood hbad
  intro clock
  apply Bool.eq_false_iff.mpr
  intro haccept
  have hs := (Source284Relative.accepts_iff _ _ _ _).mp haccept
  by_cases ht : t ≤ clock
  · have he : clock = t+(clock-t) := by omega
    rw [he] at hs
    exact hfuture (clock-t) hs
  · have he : t = clock+(t-clock) := by omega
    have hr : Source284Relative.run (description goodStates 1 good rejectTable)
        (Source284Relative.initial input certificate) t =
      Source284Relative.run (description goodStates 1 good rejectTable)
        (Source284Relative.run (description goodStates 1 good rejectTable)
          (Source284Relative.initial input certificate) clock) (t-clock) := by
      conv_lhs => rw [he,Source284Relative.run_add_clock]
    have habs := Source284Relative.run_absorbing (description goodStates 1 good rejectTable)
      (Source284Relative.run (description goodStates 1 good rejectTable)
        (Source284Relative.initial input certificate) clock) hs (t-clock)
    have hf := hfuture 0
    simp only [Nat.add_zero] at hf
    apply hf
    rw [hr,habs]
    exact hs

namespace Fixtures
example (g b : Nat → Bool → Row) :
    run (table 1 g b) ⟨17,0,some 0⟩ 2 = ⟨68,0,some 3⟩ := by
  simpa using dispatch 1 g b 17 0
example (g b : Nat → Bool → Row) :
    run (table 1 g b) ⟨17,1,some 0⟩ 2 = ⟨70,0,some 4⟩ := by
  simpa using dispatch 1 g b 17 1
example (g b : Nat → Bool → Row) :
    run (table 1 g b) ⟨17,2,some 0⟩ 2 = ⟨69,0,some 4⟩ := by
  simpa using dispatch 1 g b 17 2
example (g b : Nat → Bool → Row) :
    run (table 1 g b) ⟨17,3,some 0⟩ 2 = ⟨71,0,some 4⟩ := by
  simpa using dispatch 1 g b 17 3
example (g b : Nat → Bool → Row) :
    run (table 1 g b) ⟨17,44,some 0⟩ 2 = ⟨68,11,some 3⟩ := by
  simpa using dispatch 1 g b 17 44
example (goodStates : Nat) (good : Nat → Bool → Row) (hg : 0 < goodStates)
    (hgood : Closed goodStates good) :
    Source284Relative.run (description goodStates 1 good rejectTable)
      (Source284Relative.initial 0 4) 125 = ⟨68,1,active 393⟩ := by
  simpa [encodeFrame,totalCost,Source284CertificateHandoff.totalCost,
    Source284PreparedFramePipeline.totalCost,Source284EqualityPipeline.totalCost,
    Source284EqualityPipeline.finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,Source284ScratchFlip.flipped,bit]
    using source_pipeline goodStates 1 good rejectTable [] 4 0 hg (by omega) hgood reject_closed

example (goodStates : Nat) (good : Nat → Bool → Row) (hg : 0 < goodStates)
    (hgood : Closed goodStates good) :
    Source284Relative.run (description goodStates 1 good rejectTable)
      (Source284Relative.initial 0 7) 125 = ⟨71,1,active (393+goodStates)⟩ := by
  simpa [encodeFrame,totalCost,Source284CertificateHandoff.totalCost,
    Source284PreparedFramePipeline.totalCost,Source284EqualityPipeline.totalCost,
    Source284EqualityPipeline.finalTail,Source284RetryInitPipeline.totalCost,
    Source284PayloadSentinelPipeline.totalCost_formula,Source284RetryLoopComplete.totalCost,
    Source284RetryLoopComplete.retriesCost,Source284OneRetry.cost,Source284ScratchFlip.flipped,bit,
    ← Nat.add_assoc]
    using source_pipeline goodStates 1 good rejectTable [] 7 0 hg (by omega) hgood reject_closed
end Fixtures

end Shared.Beeping.NPcoNP.Source284TaggedHandoff
