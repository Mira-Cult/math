import Shared.PNP.Record285.SourceCandidateFrame

/-! Candidate polynomial-clock construction at graph rows 77--93. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceCandidateClock
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceReferenceSearch
open Shared.PNP.Record285.SourceUnarySkip
open Shared.PNP.Record285.SourceVirtualStep
open Shared.PNP.Record285.SourceCandidateFrame

def clockCopy (bank : Nat → Nat) : Nat → Nat :=
  update (.move 4 13) (splitResult 13 7 4 bank)

theorem clock_copy_clean (bank : Nat → Nat) (h4 : bank 4 = 0) :
    clockCopy bank = put 7 (bank 7+bank 13) bank := by
  funext j
  by_cases h13 : j=13
  · subst j; simp [clockCopy,update,splitResult,put,h4]
  · by_cases h7 : j=7
    · subst j; simp [clockCopy,update,splitResult,put]
    · by_cases h4j : j=4
      · subst j; simp [clockCopy,update,put,h4]
      · simp [clockCopy,update,splitResult,put,h13,h7,h4j]

theorem clock_copy_run (bank : Nat → Nat) :
    Silent originalRows ⟨82,bank⟩ ⟨87,clockCopy bank⟩
      (3*bank 13+1 + (2*(bank 4+bank 13)+1)) := by
  let mid := splitResult 13 7 4 bank
  have hsplit := split_run originalRows 82 83 84 85 13 7 4 (bank 13) bank
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
  have hv : mid 4 = bank 4+bank 13 := by simp [mid,splitResult]
  have hmove := expanded_move_run originalRows 85 86 87 4 13 (bank 4+bank 13) mid
    (by decide) (by decide) (by decide) hv
  exact silent_trans originalRows _ _ _ _ _ hsplit hmove

def multiplyCycle (bank : Nat → Nat) : Nat → Nat :=
  put 20 (bank 20-1) (put 7 (bank 7+bank 13+2) bank)

theorem multiply_cycle_run (bank : Nat → Nat) (h4 : bank 4 = 0) (hp : 0 < bank 20) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨81,bank⟩ ⟨81,multiplyCycle bank⟩ duration := by
  let first := update (.dec 20) bank
  let mid := clockCopy first
  have hn : bank 20 ≠ 0 := by omega
  have hs : step originalRows ⟨81,bank⟩ = (⟨82,first⟩,false) := by
    simp [step,originalRows,observe,hn,first]
  have hcopy := clock_copy_run first
  let one := update (.inc 7) mid
  let two := update (.inc 7) one
  have h87 : step originalRows ⟨87,mid⟩ = (⟨88,one⟩,false) := by
    simp [step,originalRows,observe,one]
  have h88 : step originalRows ⟨88,one⟩ = (⟨81,two⟩,false) := by
    simp [step,originalRows,observe,two]
  have hf : first 4 = 0 := by simp [first,update,h4]
  have hm := clock_copy_clean first hf
  have heffect : two = multiplyCycle bank := by
    funext j
    by_cases h20 : j=20
    · subst j; simp [multiplyCycle,two,one,mid,hm,first,put,update]
    · by_cases h7 : j=7
      · subst j; simp [multiplyCycle,two,one,mid,hm,first,put,update]
      · simp [multiplyCycle,two,one,mid,hm,first,put,update,h20,h7]
  have h := silent_trans originalRows _ _ _ 1 _ (silent_one _ _ _ hs) hcopy
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h87)
  have h := silent_trans originalRows _ _ _ _ 1 h (silent_one _ _ _ h88)
  exact ⟨1+(3*first 13+1+(2*(first 4+first 13)+1))+1+1,by omega,by simpa [heffect] using h⟩

def multiplyResult (bank : Nat → Nat) : Nat → Nat :=
  put 20 0 (put 7 (bank 7+bank 20*(bank 13+2)) bank)

theorem multiply_cycle_result (bank : Nat → Nat) (hp : 0 < bank 20) :
    multiplyResult (multiplyCycle bank) = multiplyResult bank := by
  funext j
  by_cases h20 : j=20
  · subst j; simp [multiplyResult,put]
  · by_cases h7 : j=7
    · subst j
      simp [multiplyResult,multiplyCycle,put]
      have hh : bank 20-1+1 = bank 20 := by omega
      have hm : bank 20*(bank 13+2) = (bank 20-1)*(bank 13+2)+(bank 13+2) := by
        calc
          bank 20*(bank 13+2) = (bank 20-1+1)*(bank 13+2) := congrArg (fun x => x*(bank 13+2)) hh.symm
          _ = _ := by simp [Nat.add_mul]
      rw [hm]; omega
    · simp [multiplyResult,multiplyCycle,put,h20,h7]

theorem multiply_loop (n : Nat) (bank : Nat → Nat) (h4 : bank 4 = 0) (hn : bank 20 = n) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨81,bank⟩ ⟨89,multiplyResult bank⟩ duration := by
  induction n generalizing bank with
  | zero =>
    have hz : bank 20 = 0 := hn
    have hid := dec_at_zero 20 bank hz
    have hs : step originalRows ⟨81,bank⟩ = (⟨89,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    have heffect : multiplyResult bank = bank := by
      funext j
      by_cases h20 : j=20
      · subst j; simp [multiplyResult,put,hz]
      · by_cases h7 : j=7
        · subst j; simp [multiplyResult,put,hz]
        · simp [multiplyResult,put,h20,h7]
    exact ⟨1,by decide,by simpa [heffect] using silent_one originalRows _ _ hs⟩
  | succ n ih =>
    have hp : 0 < bank 20 := by omega
    obtain ⟨d,hd,hcycle⟩ := multiply_cycle_run bank h4 hp
    have h4' : multiplyCycle bank 4 = 0 := by simp [multiplyCycle,put,h4]
    have hn' : multiplyCycle bank 20 = n := by simp [multiplyCycle,put]; omega
    obtain ⟨e,he,hrest⟩ := ih (multiplyCycle bank) h4' hn'
    rw [multiply_cycle_result bank hp] at hrest
    exact ⟨d+e,by omega,silent_trans originalRows _ _ _ _ _ hcycle hrest⟩

def powerCycle (bank : Nat → Nat) : Nat → Nat :=
  put 12 (bank 12-1) (put 6 (bank 6+1) (put 20 (bank 20*(bank 13+2)) bank))

theorem power_cycle_run (bank : Nat → Nat) (h4 : bank 4 = 0) (h7 : bank 7 = 0) (hp : 0 < bank 12) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨79,bank⟩ ⟨79,powerCycle bank⟩ duration := by
  let first := update (.inc 6) (update (.dec 12) bank)
  let mid := multiplyResult first
  let last := update (.move 7 20) mid
  have hn : bank 12 ≠ 0 := by omega
  have hs : step originalRows ⟨79,bank⟩ = (⟨80,update (.dec 12) bank⟩,false) := by
    simp [step,originalRows,observe,hn]
  have ht : step originalRows ⟨80,update (.dec 12) bank⟩ = (⟨81,first⟩,false) := by
    simp [step,originalRows,observe,first]
  have hfirst := silent_trans originalRows _ _ _ 1 1 (silent_one _ _ _ hs) (silent_one _ _ _ ht)
  have hf : first 4 = 0 := by simp [first,update,h4]
  obtain ⟨d,hd,hmul⟩ := multiply_loop (first 20) first hf rfl
  have h89 : originalRows[89]? = some ⟨.dec 7,90,79⟩ := by decide
  have h90 : originalRows[90]? = some ⟨.inc 20,89,89⟩ := by decide
  have hmove := expanded_move_run originalRows 89 90 79 7 20 (mid 7) mid h89 h90 (by decide) rfl
  have heffect : last = powerCycle bank := by
    funext j
    by_cases h12 : j=12
    · subst j; simp [last,mid,multiplyResult,powerCycle,first,put,update]
    · by_cases h6 : j=6
      · subst j; simp [last,mid,multiplyResult,powerCycle,first,put,update]
      · by_cases h20 : j=20
        · subst j; simp [last,mid,multiplyResult,powerCycle,first,put,update,h7]
        · by_cases h7j : j=7
          · subst j; simp [last,mid,multiplyResult,powerCycle,first,put,update,h7]
          · simp [last,mid,multiplyResult,powerCycle,first,put,update,h12,h6,h20,h7j]
  have h := silent_trans originalRows _ _ _ _ _ hfirst hmul
  have h := silent_trans originalRows _ _ _ _ _ h hmove
  change Silent originalRows ⟨79,bank⟩ ⟨79,last⟩ (2+d+(2*mid 7+1)) at h
  exact ⟨2+d+(2*mid 7+1),by omega,by simpa [heffect] using h⟩

def powerResult (bank : Nat → Nat) : Nat → Nat :=
  put 12 0 (put 6 (bank 6+bank 12) (put 20 (bank 20*(bank 13+2)^(bank 12)) bank))

theorem power_cycle_result (bank : Nat → Nat) (hp : 0 < bank 12) :
    powerResult (powerCycle bank) = powerResult bank := by
  funext j
  by_cases h12 : j=12
  · subst j; simp [powerResult,put]
  · by_cases h6 : j=6
    · subst j; simp [powerResult,powerCycle,put]; omega
    · by_cases h20 : j=20
      · subst j
        simp [powerResult,powerCycle,put]
        have hh : bank 12-1+1 = bank 12 := by omega
        calc
          bank 20 * (bank 13+2) * (bank 13+2)^(bank 12-1) =
              bank 20 * ((bank 13+2)^(bank 12-1) * (bank 13+2)) := by
                simp [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]
          _ = bank 20*(bank 13+2)^bank 12 := by
            have hh' : (bank 12-1).succ = bank 12 := by omega
            rw [←Nat.pow_succ,hh']
      · simp [powerResult,powerCycle,put,h12,h6,h20]

theorem power_loop (n : Nat) (bank : Nat → Nat) (h4 : bank 4 = 0) (h7 : bank 7 = 0) (hn : bank 12 = n) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨79,bank⟩ ⟨91,powerResult bank⟩ duration := by
  induction n generalizing bank with
  | zero =>
    have hz : bank 12 = 0 := hn
    have hid := dec_at_zero 12 bank hz
    have hs : step originalRows ⟨79,bank⟩ = (⟨91,bank⟩,false) := by
      simp [step,originalRows,observe,hz,hid]
    have heffect : powerResult bank = bank := by
      funext j
      by_cases h12 : j=12
      · subst j; simp [powerResult,put,hz]
      · by_cases h6 : j=6
        · subst j; simp [powerResult,put,hz]
        · by_cases h20 : j=20
          · subst j; simp [powerResult,put,hz]
          · simp [powerResult,put,h12,h6,h20]
    exact ⟨1,by decide,by simpa [heffect] using silent_one originalRows _ _ hs⟩
  | succ n ih =>
    have hp : 0 < bank 12 := by omega
    obtain ⟨d,hd,hcycle⟩ := power_cycle_run bank h4 h7 hp
    have h4' : powerCycle bank 4 = 0 := by simp [powerCycle,put,h4]
    have h7' : powerCycle bank 7 = 0 := by simp [powerCycle,put,h7]
    have hn' : powerCycle bank 12 = n := by simp [powerCycle,put]; omega
    obtain ⟨e,he,hrest⟩ := ih (powerCycle bank) h4' h7' hn'
    rw [power_cycle_result bank hp] at hrest
    exact ⟨d+e,by omega,silent_trans originalRows _ _ _ _ _ hcycle hrest⟩

def clockInitial (bank : Nat → Nat) : Nat → Nat := put 20 1 bank

def clockOutput (bank : Nat → Nat) : Nat → Nat :=
  update (.move 6 12) (powerResult (clockInitial bank))

/-- The clock builder includes clearing any previous clock, setting one,
repeated multiplication and exponent restoration. -/
theorem clock_build_run (bank : Nat → Nat) (h4 : bank 4 = 0) (h7 : bank 7 = 0) :
    ∃ duration, 0 < duration ∧ Silent originalRows ⟨77,bank⟩ ⟨93,clockOutput bank⟩ duration := by
  let cleared := clear 20 bank
  let init := clockInitial bank
  let mid := powerResult init
  have h77 : originalRows[77]? = some ⟨.dec 20,77,78⟩ := by decide
  have hc := clear_run originalRows 77 78 20 (bank 20) bank h77 rfl
  have heffect : update (.inc 20) cleared = init := by
    funext j
    by_cases hj : j=20 <;> simp [init,clockInitial,cleared,clear,put,update,hj]
  have h78 : step originalRows ⟨78,cleared⟩ = (⟨79,init⟩,false) := by
    simp [step,originalRows,observe,heffect]
  have h4' : init 4 = 0 := by simp [init,clockInitial,put,h4]
  have h7' : init 7 = 0 := by simp [init,clockInitial,put,h7]
  obtain ⟨d,hd,hpow⟩ := power_loop (init 12) init h4' h7' rfl
  have h91 : originalRows[91]? = some ⟨.dec 6,92,93⟩ := by decide
  have h92 : originalRows[92]? = some ⟨.inc 12,91,91⟩ := by decide
  have hm := expanded_move_run originalRows 91 92 93 6 12 (mid 6) mid h91 h92 (by decide) rfl
  have h := silent_trans originalRows _ _ _ _ 1 hc (silent_one _ _ _ h78)
  have h := silent_trans originalRows _ _ _ _ _ h hpow
  have h := silent_trans originalRows _ _ _ _ _ h hm
  exact ⟨(bank 20+1)+1+d+(2*mid 6+1),by omega,by simpa [clockOutput,mid,init] using h⟩

/-- Zero scratch yields precisely the source polynomial clock and retains
all other slots, including the exponent, arbitrary suffix and candidate. -/
theorem clock_output_clean (bank : Nat → Nat) (h6 : bank 6 = 0) :
    clockOutput bank = put 20 ((bank 13+2)^(bank 12)) bank := by
  funext j
  by_cases h20 : j=20
  · subst j; simp [clockOutput,clockInitial,powerResult,put,update]
  · by_cases h12 : j=12
    · subst j; simp [clockOutput,clockInitial,powerResult,put,update,h6]
    · by_cases h6j : j=6
      · subst j; simp [clockOutput,put,update,h6]
      · simp [clockOutput,clockInitial,powerResult,put,update,h20,h12,h6j]

/-- Clock construction, input frame and bounded candidate simulation form one
finite silent run with the exact source candidate result. -/
theorem candidate_phase_graph (bank : Nat → Nat) (hready : ReferenceReady bank)
    (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨77,bank⟩ ⟨154,out⟩ duration ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.candidate (bank 11) (bank 12) (bank 13) (bank 14) (bank 15)
        then (if bank 16=0 then 1 else 0) else bank 16) := by
  let mid := clockOutput bank
  have hv := clock_output_clean bank h6
  have hmidready : ReferenceReady mid := by
    simp [ReferenceReady,mid,hv,put,hready.1,hready.2.1,hready.2.2]
  have hmid6 : mid 6 = 0 := by simp [mid,hv,put,h6]
  have hclock : mid 20 = (mid 13+2)^(mid 12) := by simp [mid,hv,put]
  have hmidframe : ∀ j, Protected j → mid j = bank j := by
    intro j hj
    have h20 : j ≠ 20 := by simp only [Protected] at hj; omega
    simp [mid,hv,put,h20]
  obtain ⟨d,hd,hbuild⟩ := clock_build_run bank hready.1 h7
  obtain ⟨out,e,he,hphase,hout,hprotected,hresult⟩ := frame_candidate_evaluate mid hmidready hmid6 hclock
  have hframes : ∀ j, Protected j → out j = bank j := by
    intro j hj; exact (hprotected j hj).trans (hmidframe j hj)
  refine ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ hbuild hphase,hout,hframes,?_⟩
  simpa [mid,hv,put] using hresult

/-- Source candidate evaluation on the accepted pre-control grammar, with
finite positive progress, exact output bank and no marked events. -/
theorem candidate_phase_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨77,bank⟩)
    (hready : ReferenceReady bank) (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
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
  obtain ⟨out,d,hd,hseg,hout,hframe,hresult⟩ := candidate_phase_graph bank hready h6 h7
  have h := transfer_silent_graph t d 77 154 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.1,h.2.2.1,h.2.2.2.1,hout,hframe,hresult,h.2.2.2.2⟩

/-- Full reference and candidate computation for a comparison, through the
actual decision boundary. The comparison register is exactly the mismatch. -/
theorem comparison_compute_graph (bank : Nat → Nat) (hready : ReferenceReady bank)
    (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
    ∃ out duration, 0 < duration ∧ Silent originalRows ⟨6,bank⟩ ⟨154,out⟩ duration ∧
      ReferenceReady out ∧ (∀ j, Protected j → out j = bank j) ∧
      out 16 = (if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) then 1 else 0) := by
  obtain ⟨mid,d,hd,href,hmready,h18,hmresult,hmframe⟩ := reference_phase_all_clocks bank hready
  have hmid6 : mid 6 = 0 := (hmframe 6 (by unfold Protected; omega)).trans h6
  have hmid7 : mid 7 = 0 := (hmframe 7 (by unfold Protected; omega)).trans h7
  obtain ⟨out,e,he,hcand,hout,houtframe,hresult⟩ := candidate_phase_graph mid hmready hmid6 hmid7
  have hframes : ∀ j, Protected j → out j = bank j := by
    intro j hj; exact (houtframe j hj).trans (hmframe j hj)
  have h11 : mid 11 = bank 11 := hmframe 11 (by unfold Protected; omega)
  have h12 : mid 12 = bank 12 := hmframe 12 (by unfold Protected; omega)
  have h13 : mid 13 = bank 13 := hmframe 13 (by unfold Protected; omega)
  have h14 : mid 14 = bank 14 := hmframe 14 (by unfold Protected; omega)
  have h15 : mid 15 = bank 15 := hmframe 15 (by unfold Protected; omega)
  refine ⟨out,d+e,by omega,silent_trans originalRows _ _ _ _ _ href hcand,hout,hframes,?_⟩
  rw [h11,h12,h13,h14,h15,hmresult] at hresult
  cases hr : Source.reference (bank 13) (bank 14) (bank 15) <;>
    cases hc : Source.candidate (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) <;>
    simp [Source.mismatch,hr,hc] at hresult ⊢ <;> exact hresult

/-- The full comparison computation transfers to the exact pre-control
grammar with finite bounded progress and no marked events. -/
theorem comparison_compute_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (hready : ReferenceReady bank) (h6 : bank 6 = 0) (h7 : bank 7 = 0) :
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
      out 16 = (if Source.mismatch (bank 11) (bank 12) (bank 13) (bank 14) (bank 15) then 1 else 0) ∧
      (∀ u, PreControlGrammar.acceptedRefinement.boundary t ≤ u →
        u < PreControlGrammar.acceptedRefinement.boundary (t+duration) →
        ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  obtain ⟨out,d,hd,hseg,hout,hframe,hresult⟩ := comparison_compute_graph bank hready h6 h7
  have h := transfer_silent_graph t d 6 154 bank out hstate hd hseg
  exact ⟨out,d,hd,h.1,h.2.1,h.2.2.1,h.2.2.2.1,hout,hframe,hresult,h.2.2.2.2⟩

end Shared.PNP.Record285.SourceCandidateClock
