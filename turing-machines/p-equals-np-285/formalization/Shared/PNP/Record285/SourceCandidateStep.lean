import Shared.PNP.Record285.SourceCandidateDecode

/-! The candidate evaluator's checked action, continuation and HALT toggle. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceCandidateStep
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualAction
open Shared.PNP.Record285.SourceVirtualFinish
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceCandidateDecode

def candidateState (bank : Nat → Nat) : Source.SimState := ⟨bank 19,bank 2,bank 3,0⟩
def packed (bank : Nat → Nat) : Nat := (Source.popUnary (Source.skipUnary (bank 3) (bank 11))).1
def virtualLeft (bank : Nat → Nat) : Nat := if (packed bank/2)%2=0 then bank 19 else bank 2
def virtualRight (bank : Nat → Nat) : Nat := if (packed bank/2)%2=0 then bank 2 else bank 19
def virtualNext (bank : Nat → Nat) : Source.SimState :=
  ⟨2*virtualLeft bank + packed bank%2,virtualRight bank/2,
   packed bank/4-1+2*(virtualRight bank%2),0⟩

theorem source_step_view (bank : Nat → Nat) :
    Source.simStep (bank 11) (candidateState bank) =
      if packed bank/4=0 then none else some (virtualNext bank) := by
  simp [Source.simStep,candidateState,packed,virtualNext,virtualLeft,virtualRight] <;> rfl

structure CoreFacts (bank core : Nat → Nat) : Prop where
  selector : core 3 = packed bank/4
  right : core 2 = virtualRight bank
  left : core 19 = 2*virtualLeft bank + packed bank%2
  clock : core 20 = bank 20-1
  scratch4 : core 4 = 0
  scratch5 : core 5 = 0
  scratch17 : core 17 = 0
  expected : core 16 = bank 16
  frame : ∀ j, Protected j → core j = bank j

/-- The candidate uses the same action arithmetic but always supplies choice
zero. All protected registers, including its program, are retained. -/
theorem prepared_core_facts (bank : Nat → Nat) (hready : ReferenceReady bank) :
    CoreFacts bank (actionCore (candidateDecodedBank bank)) := by
  obtain ⟨h4,h5,h17⟩ := hready
  let record := candidateDecodedBank bank
  have hm := candidate_decode_source bank h4 h17
  change record 3 = _ ∧ record 1 = _ ∧ record 20 = _ ∧ _ at hm
  obtain ⟨hr3,hr1,hr20,hrframe⟩ := hm
  change ∀ j, j ≠ 1 → j ≠ 3 → j ≠ 20 → record j = bank j at hrframe
  have hp : record 3 = packed bank := by simpa [packed] using hr3
  have hr2 : record 2 = bank 2 := hrframe 2 (by decide) (by decide) (by decide)
  have hr19 : record 19 = bank 19 := hrframe 19 (by decide) (by decide) (by decide)
  have hr5 : record 5 = 0 := by rw [hrframe 5 (by decide) (by decide) (by decide),h5]
  have hl : actionLeft record = virtualLeft bank := by simp [actionLeft,virtualLeft,hp,hr2,hr19]
  have hr : actionRight record = virtualRight bank := by simp [actionRight,virtualRight,hp,hr2,hr19]
  obtain ⟨hc3,hc2,hc19,hc5,hcf⟩ := action_core_values record
  refine ⟨?_,?_,?_,?_,?_,hc5,?_,?_,?_⟩
  · rw [hc3,hp]
  · rw [hc2,hr]
  · rw [hc19,hr5,hp,hl]; omega
  · exact (hcf 20 (by decide) (by decide) (by decide) (by decide)).trans hr20
  · rw [hcf 4 (by decide) (by decide) (by decide) (by decide),hrframe 4 (by decide) (by decide) (by decide),h4]
  · rw [hcf 17 (by decide) (by decide) (by decide) (by decide),hrframe 17 (by decide) (by decide) (by decide),h17]
  · rw [hcf 16 (by decide) (by decide) (by decide) (by decide),hrframe 16 (by decide) (by decide) (by decide)]
  · intro j hj
    have h1 : j ≠ 1 := by simp only [Protected] at hj; omega
    have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
    have h20 : j ≠ 20 := by simp only [Protected] at hj; omega
    have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
    have h19 : j ≠ 19 := by simp only [Protected] at hj; omega
    have h5j : j ≠ 5 := by simp only [Protected] at hj; omega
    exact (hcf j h3 h2 h19 h5j).trans (hrframe j h1 h3 h20)

/-- Full candidate decode and action, for arbitrary initial banks. -/
theorem candidate_action_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨119,bank⟩
      ⟨146,actionCore (candidateDecodedBank bank)⟩ duration := by
  have hdecode := candidate_decode_raw bank hp
  obtain ⟨d,hd,hact⟩ := action_core_generic originalRows 133 candidateActionLayout (candidateDecodedBank bank)
  have h := silent_trans originalRows _ _ _ _ _ hdecode hact
  exact ⟨candidateDecodeTime bank+d,by omega,by simpa using h⟩

def candidateHaltBank (bank : Nat → Nat) : Nat → Nat :=
  put 16 (if bank 16=0 then 1 else 0) (put 2 (bank 2/2) bank)

theorem candidateHaltBank_read (bank : Nat → Nat) (j : Nat) :
    candidateHaltBank bank j = if j=16 then (if bank 16=0 then 1 else 0)
      else if j=2 then bank 2/2 else bank j := by rfl

/-- HALT toggles the expected bit and returns, even for arbitrary natural
contents of that register; no reference-branch counter is altered. -/
theorem candidate_halt_run (bank : Nat → Nat) (hz : bank 3 = 0) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨146,bank⟩ ⟨154,candidateHaltBank bank⟩ duration := by
  let k1 := put 2 (bank 2/2) bank
  have hid := dec_at_zero 3 bank hz
  have h146 : step originalRows ⟨146,bank⟩ = (⟨150,bank⟩,false) := by
    simp [step,originalRows,observe,hz,hid]
  have h150 : step originalRows ⟨150,bank⟩ = (⟨151,k1⟩,false) := by
    have heq : update (.half 2) bank = k1 := by
      funext j; by_cases hj : j=2 <;> simp [k1,put,update,hj]
    simp [step,originalRows,observe,heq]
  have hpref := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ h146) (silent_one _ _ _ h150)
  by_cases he : bank 16 = 0
  · have hv : k1 16 = 0 := by simp [k1,put,he]
    have hdec := dec_at_zero 16 k1 hv
    have h151 : step originalRows ⟨151,k1⟩ = (⟨153,k1⟩,false) := by
      simp [step,originalRows,observe,hv,hdec]
    have h153 : step originalRows ⟨153,k1⟩ = (⟨154,update (.inc 16) k1⟩,false) := by
      simp [step,originalRows,observe]
    have heffect : update (.inc 16) k1 = candidateHaltBank bank := by
      funext j; by_cases hj : j=16 <;> simp [candidateHaltBank,k1,put,update,he,hj]
    have h := silent_trans originalRows _ _ _ 2 1 hpref (silent_one _ _ _ h151)
    have h := silent_trans originalRows _ _ _ 3 1 h (silent_one _ _ _ h153)
    exact ⟨4,by decide,by simpa [heffect] using h⟩
  · let k2 := update (.dec 16) k1
    have hv : k1 16 ≠ 0 := by simp [k1,put,he]
    have h151 : step originalRows ⟨151,k1⟩ = (⟨152,k2⟩,false) := by
      simp [step,originalRows,observe,hv,k2]
    have hr : originalRows[152]? = some ⟨.dec 16,152,154⟩ := by decide
    have hclear := clear_run originalRows 152 154 16 (k2 16) k2 hr rfl
    have heffect : clear 16 k2 = candidateHaltBank bank := by
      funext j; by_cases hj : j=16 <;> simp [candidateHaltBank,clear,k2,k1,put,update,he,hj]
    have h := silent_trans originalRows _ _ _ 2 1 hpref (silent_one _ _ _ h151)
    have h := silent_trans originalRows _ _ _ 3 (k2 16+1) h hclear
    exact ⟨3+(k2 16+1),by omega,by simpa [heffect] using h⟩

/-- One complete positive-clock candidate step. HALT toggles the comparison
bit; a live step retains it and represents exactly one source transition. -/
theorem candidate_single_step (bank : Nat → Nat) (hready : ReferenceReady bank) (hp : 0 < bank 20) :
    ∃ out duration, 0 < duration ∧ ReferenceReady out ∧
      (∀ j, Protected j → out j = bank j) ∧
      (match Source.simStep (bank 11) (candidateState bank) with
       | none => Silent originalRows ⟨119,bank⟩ ⟨154,out⟩ duration ∧
           out 16 = (if bank 16=0 then 1 else 0)
       | some next => Silent originalRows ⟨119,bank⟩ ⟨119,out⟩ duration ∧
           out 20+1 = bank 20 ∧ candidateState out = next ∧ out 16 = bank 16) := by
  let core := actionCore (candidateDecodedBank bank)
  obtain ⟨d,hd,hprefix⟩ := candidate_action_raw bank hp
  change Silent originalRows ⟨119,bank⟩ ⟨146,core⟩ d at hprefix
  have hf : CoreFacts bank core := prepared_core_facts bank hready
  by_cases hz : packed bank/4 = 0
  · have hc : core 3 = 0 := by rw [hf.selector,hz]
    let out := candidateHaltBank core
    obtain ⟨e,he,hlast⟩ := candidate_halt_run core hc
    have hseg := silent_trans originalRows _ _ _ _ _ hprefix hlast
    have hout : ReferenceReady out := by
      simp [ReferenceReady,out,candidateHaltBank_read,hf.scratch4,hf.scratch5,hf.scratch17]
    have hframe : ∀ j, Protected j → out j = bank j := by
      intro j hj
      have h16 : j ≠ 16 := by simp only [Protected] at hj; omega
      have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
      simp [out,candidateHaltBank_read,h16,h2,hf.frame j hj]
    have hresult : out 16 = (if bank 16=0 then 1 else 0) := by
      simp [out,candidateHaltBank_read,hf.expected]
    refine ⟨out,d+e,by omega,hout,hframe,?_⟩
    rw [source_step_view]
    simp only [hz,if_pos]
    exact ⟨hseg,hresult⟩
  · have hc : 0 < core 3 := by rw [hf.selector]; omega
    let out := liveBank core
    have hlast := live_generic originalRows 146 150 119 candidateLiveLayout core hc
    have hseg := silent_trans originalRows _ _ _ _ _ hprefix hlast
    have hout : ReferenceReady out := by
      simp [ReferenceReady,out,liveBank_read,hf.scratch4,hf.scratch5,hf.scratch17]
    have hframe : ∀ j, Protected j → out j = bank j := by
      intro j hj
      have h3 : j ≠ 3 := by simp only [Protected] at hj; omega
      have h2 : j ≠ 2 := by simp only [Protected] at hj; omega
      simp [out,liveBank_read,h3,h2,hf.frame j hj]
    have hclock : out 20+1 = bank 20 := by simp [out,liveBank_read,hf.clock]; omega
    have hstate : candidateState out = virtualNext bank := by
      simp [candidateState,virtualNext,out,liveBank_read,hf.left,hf.right,hf.selector]
    have hresult : out 16 = bank 16 := by simp [out,liveBank_read,hf.expected]
    refine ⟨out,d+liveTime core,by omega,hout,hframe,?_⟩
    rw [source_step_view]
    simp only [hz,if_false]
    exact ⟨hseg,hclock,hstate,hresult⟩

/-- The candidate evaluator terminates on every finite clock. The comparison
bit is toggled exactly when the deterministic candidate halts within it. -/
theorem candidate_evaluator (clock : Nat) (bank : Nat → Nat)
    (hready : ReferenceReady bank) (hclock : bank 20 = clock) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨119,bank⟩ ⟨154,out⟩ duration ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.haltedWithin (bank 11) clock (candidateState bank)
        then (if bank 16=0 then 1 else 0) else bank 16) := by
  induction clock generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hclock
    have hid := dec_at_zero 20 bank hz
    have hs : step originalRows ⟨119,bank⟩ = (⟨154,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    refine ⟨bank,1,by decide,silent_one originalRows _ _ hs,hready,?_,?_⟩
    · intro j hj; rfl
    · simp [Source.haltedWithin]
  | succ clock ih =>
    have hp : 0 < bank 20 := by omega
    obtain ⟨mid,d,hd,hmready,hmframe,hcase⟩ := candidate_single_step bank hready hp
    cases hs : Source.simStep (bank 11) (candidateState bank) with
    | none =>
      simp only [hs] at hcase
      obtain ⟨hseg,hresult⟩ := hcase
      refine ⟨mid,d,hd,hseg,hmready,hmframe,?_⟩
      simpa [Source.haltedWithin,hs] using hresult
    | some next =>
      simp only [hs] at hcase
      obtain ⟨hseg,hnext,hstate,hresult⟩ := hcase
      have hc : mid 20 = clock := by omega
      obtain ⟨out,e,he,hrest,hout,hframe,hres⟩ := ih mid hmready hc
      have hp11 : Protected 11 := by simp [Protected]
      have hprog : mid 11 = bank 11 := hmframe 11 hp11
      have hframes : ∀ j, Protected j → out j = bank j := by
        intro j hj; exact (hframe j hj).trans (hmframe j hj)
      refine ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hseg hrest,hout,hframes,?_⟩
      simpa [Source.haltedWithin,hs,hprog,hstate,hresult] using hres

/-- The raw candidate prefix decrements the clock even with dirty scratch. -/
theorem decoded_clock (bank : Nat → Nat) : candidateDecodedBank bank 20 = bank 20-1 := by
  simp [candidateDecodedBank,recordBank,afterSkip,candidateProgramBank,copyRaw,splitResult,clear,put,update]

/-- Termination and silence do not depend on the source encoding invariant. -/
theorem candidate_raw_terminates (clock : Nat) (bank : Nat → Nat) (hclock : bank 20 = clock) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨119,bank⟩ ⟨154,out⟩ duration := by
  induction clock generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hclock
    have hid := dec_at_zero 20 bank hz
    have hs : step originalRows ⟨119,bank⟩ = (⟨154,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    exact ⟨bank,1,by decide,silent_one originalRows _ _ hs⟩
  | succ clock ih =>
    have hp : 0 < bank 20 := by omega
    let core := actionCore (candidateDecodedBank bank)
    obtain ⟨d,hd,hprefix⟩ := candidate_action_raw bank hp
    change Silent originalRows ⟨119,bank⟩ ⟨146,core⟩ d at hprefix
    by_cases hz : core 3 = 0
    · obtain ⟨e,he,hlast⟩ := candidate_halt_run core hz
      exact ⟨candidateHaltBank core,d+e,by omega,silent_trans originalRows _ _ _ _ _ hprefix hlast⟩
    · have hc : 0 < core 3 := by omega
      let mid := liveBank core
      have hlast := live_generic originalRows 146 150 119 candidateLiveLayout core hc
      have hf := (action_core_values (candidateDecodedBank bank)).2.2.2.2 20
        (by decide) (by decide) (by decide) (by decide)
      have hmid : mid 20 = clock := by
        simp [mid,liveBank_read,core,hf,decoded_clock]
        omega
      obtain ⟨out,e,he,hrest⟩ := ih mid hmid
      have hseg := silent_trans originalRows _ _ _ _ _ hprefix hlast
      exact ⟨out,d+liveTime core+e,by omega,silent_trans originalRows _ _ _ _ _ hseg hrest⟩

/-- The complete evaluator transfers to the accepted pre-control grammar with
positive bounded progress and exact event silence. -/
theorem candidate_evaluator_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨119,bank⟩) (hready : ReferenceReady bank) :
    ∃ out duration, 0 < duration ∧
      PreControlGrammar.acceptedRefinement.boundary t <
        PreControlGrammar.acceptedRefinement.boundary (t+duration) ∧
      PreControlGrammar.acceptedRefinement.boundary (t+duration) ≤
        PreControlGrammar.acceptedRefinement.boundary t + 32*duration ∧
      PreControlGrammar.positions[154]? = some
        ((ProducerGrammar.system PreControlGrammar.grammar).run
          (PreControlGrammar.acceptedRefinement.boundary (t+duration))).pc ∧
      ((ProducerGrammar.system PreControlGrammar.grammar).run
        (PreControlGrammar.acceptedRefinement.boundary (t+duration))).bank = out ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.haltedWithin (bank 11) (bank 20) (candidateState bank)
        then (if bank 16=0 then 1 else 0) else bank 16) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hready',hframe,hresult⟩ := candidate_evaluator (bank 20) bank hready rfl
  have h := transfer_silent_graph t d 119 154 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.1,h.2.2.1,h.2.2.2.1,hready',hframe,hresult,h.2.2.2.2⟩

end Shared.PNP.Record285.SourceCandidateStep
