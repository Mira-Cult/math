import Shared.PNP.Record285.SourceBegin
import Shared.PNP.Record285.OwnershipExpandedLoop

/-! Source reference-search preparation, with the complete register frame.
The scratch-zero premises are explicit; proving them at every source boundary
and completing the bounded evaluator remain separate obligations. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceReferenceStart
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin

def splitCycle (src dst aux : Nat) (bank : Nat → Nat) : Nat → Nat :=
  update (.inc aux) (update (.inc dst) (update (.dec src) bank))

def splitResult (src dst aux : Nat) (bank : Nat → Nat) : Nat → Nat :=
  fun j => if j = src then 0 else if j = dst then bank dst + bank src
    else if j = aux then bank aux + bank src else bank j

theorem splitCycle_read (src dst aux j : Nat) (bank : Nat → Nat)
    (hsd : src ≠ dst) (hsa : src ≠ aux) (hda : dst ≠ aux) :
    splitCycle src dst aux bank j =
      if j = src then bank src-1 else if j = dst then bank dst+1
      else if j = aux then bank aux+1 else bank j := by
  by_cases hs : j = src
  · subst j; simp [splitCycle,update,hsd,hsa]
  · by_cases hd : j = dst
    · subst j; simp [splitCycle,update,Ne.symm hsd,hda]
    · by_cases ha : j = aux
      · subst j; simp [splitCycle,update,Ne.symm hsa,Ne.symm hda]
      · simp [splitCycle,update,hs,hd,ha]

theorem splitResult_zero (src dst aux : Nat) (bank : Nat → Nat) (hz : bank src = 0) :
    splitResult src dst aux bank = bank := by
  funext j
  by_cases hs : j = src
  · subst j; simp [splitResult,hz]
  · by_cases hd : j = dst
    · subst j; simp [splitResult,hs,hz]
    · by_cases ha : j = aux
      · subst j; simp [splitResult,hs,hd,hz]
      · simp [splitResult,hs,hd,ha]

theorem splitResult_cycle (src dst aux : Nat) (bank : Nat → Nat)
    (hsd : src ≠ dst) (hsa : src ≠ aux) (hda : dst ≠ aux) (hp : 0 < bank src) :
    splitResult src dst aux (splitCycle src dst aux bank) = splitResult src dst aux bank := by
  funext j
  have hv := splitCycle_read src dst aux j bank hsd hsa hda
  have hs := splitCycle_read src dst aux src bank hsd hsa hda
  have hd := splitCycle_read src dst aux dst bank hsd hsa hda
  have ha := splitCycle_read src dst aux aux bank hsd hsa hda
  simp only [if_true] at hs
  simp only [if_neg (Ne.symm hsd),if_true] at hd
  simp only [if_neg (Ne.symm hsa),if_neg (Ne.symm hda),if_true] at ha
  by_cases hjs : j = src
  · simp [splitResult,hjs]
  · by_cases hjd : j = dst
    · simp only [splitResult,if_neg hjs,if_pos hjd]
      rw [hs,hd]
      omega
    · by_cases hja : j = aux
      · simp only [splitResult,if_neg hjs,if_neg hjd,if_pos hja]
        rw [hs,ha]
        omega
      · simp only [splitResult,if_neg hjs,if_neg hjd,if_neg hja]
        simpa [hjs,hjd,hja] using hv

theorem silent_one (rows : Array Row) (s t : State) (h : step rows s = (t,false)) :
    Silent rows s t 1 := by
  constructor
  · change (step rows s).1 = t
    simp [h]
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    change ¬ (step rows s).2 = true
    simp [h]

theorem split_cycle_run (rows : Array Row) (head a b exit src dst aux : Nat)
    (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,a,exit⟩)
    (ha : rows[a]? = some ⟨.inc dst,b,b⟩)
    (hb : rows[b]? = some ⟨.inc aux,head,head⟩)
    (hp : 0 < bank src) :
    Silent rows ⟨head,bank⟩ ⟨head,splitCycle src dst aux bank⟩ 3 := by
  have hn : bank src ≠ 0 := by omega
  let b1 := update (.dec src) bank
  let b2 := update (.inc dst) b1
  have h1 : step rows ⟨head,bank⟩ = (⟨a,b1⟩,false) := by simp [step,hhead,observe,hn,b1]
  have h2 : step rows ⟨a,b1⟩ = (⟨b,b2⟩,false) := by simp [step,ha,observe,b2]
  have h3 : step rows ⟨b,b2⟩ = (⟨head,splitCycle src dst aux bank⟩,false) := by
    simp [step,hb,observe,splitCycle,b2,b1]
  have hp12 := silent_trans rows _ _ _ 1 1 (silent_one rows _ _ h1) (silent_one rows _ _ h2)
  have hp123 := silent_trans rows _ _ _ 2 1 hp12 (silent_one rows _ _ h3)
  simpa using hp123

/-- A checked decrement/two-increment loop always finishes and transfers the
whole source count into both destinations, without changing other slots. -/
theorem split_run (rows : Array Row) (head a b exit src dst aux n : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,a,exit⟩)
    (ha : rows[a]? = some ⟨.inc dst,b,b⟩)
    (hb : rows[b]? = some ⟨.inc aux,head,head⟩)
    (hsd : src ≠ dst) (hsa : src ≠ aux) (hda : dst ≠ aux) (hval : bank src = n) :
    Silent rows ⟨head,bank⟩ ⟨exit,splitResult src dst aux bank⟩ (3*n+1) := by
  induction n generalizing bank with
  | zero =>
    have hid := dec_at_zero src bank hval
    have hresult := splitResult_zero src dst aux bank hval
    have hs : step rows ⟨head,bank⟩ = (⟨exit,bank⟩,false) := by
      simp [step,hhead,observe,hval,hid]
    simpa [hresult] using silent_one rows ⟨head,bank⟩ ⟨exit,bank⟩ hs
  | succ n ih =>
    have hp : 0 < bank src := by omega
    have hcycle := split_cycle_run rows head a b exit src dst aux bank hhead ha hb hp
    have hsrc : splitCycle src dst aux bank src = n := by
      have hh := splitCycle_read src dst aux src bank hsd hsa hda
      simp only [if_true] at hh
      omega
    have hrest := ih (splitCycle src dst aux bank) hsrc
    have heffect := splitResult_cycle src dst aux bank hsd hsa hda hp
    rw [heffect] at hrest
    have h := silent_trans rows _ _ _ 3 (3*n+1) hcycle hrest
    have htime : 3*(n+1)+1 = 3+(3*n+1) := by omega
    simpa only [htime] using h

/-- Raw effect of the compiler's copy block, with arbitrary scratch values. -/
def copyRaw (src tmp aux dst : Nat) (bank : Nat → Nat) : Nat → Nat :=
  update (.move tmp dst) (clear dst (update (.move aux src) (splitResult src tmp aux bank)))

def copyTime (src tmp aux dst : Nat) (bank : Nat → Nat) : Nat :=
  bank dst + 7*bank src + 2*bank aux + 2*bank tmp + 4

/-- Verify a complete compiled copy block for every bank, including arbitrary
scratch and overwritten destination contents. -/
theorem copy_block (rows : Array Row) (head a b restore restoreBody clearDst transfer transferBody exit : Nat)
    (src tmp aux dst : Nat) (bank : Nat → Nat)
    (hhead : rows[head]? = some ⟨.dec src,a,restore⟩)
    (ha : rows[a]? = some ⟨.inc tmp,b,b⟩)
    (hb : rows[b]? = some ⟨.inc aux,head,head⟩)
    (hrestore : rows[restore]? = some ⟨.dec aux,restoreBody,clearDst⟩)
    (hrestoreBody : rows[restoreBody]? = some ⟨.inc src,restore,restore⟩)
    (hclear : rows[clearDst]? = some ⟨.dec dst,clearDst,transfer⟩)
    (htransfer : rows[transfer]? = some ⟨.dec tmp,transferBody,exit⟩)
    (htransferBody : rows[transferBody]? = some ⟨.inc dst,transfer,transfer⟩)
    (hst : src ≠ tmp) (hsa : src ≠ aux) (hsd : src ≠ dst)
    (hta : tmp ≠ aux) (htd : tmp ≠ dst) (had : aux ≠ dst) :
    Silent rows ⟨head,bank⟩ ⟨exit,copyRaw src tmp aux dst bank⟩ (copyTime src tmp aux dst bank) := by
  let k1 := splitResult src tmp aux bank
  let k2 := update (.move aux src) k1
  let k3 := clear dst k2
  let k4 := update (.move tmp dst) k3
  have hsplit : Silent rows ⟨head,bank⟩ ⟨restore,k1⟩ (3*bank src+1) :=
    split_run rows head a b restore src tmp aux (bank src) bank hhead ha hb hst hsa hta rfl
  have haux : k1 aux = bank aux + bank src := by
    simp [k1,splitResult,Ne.symm hsa,Ne.symm hta]
  have hmove : Silent rows ⟨restore,k1⟩ ⟨clearDst,k2⟩ (2*(bank aux+bank src)+1) := by
    exact expanded_move_run rows restore restoreBody clearDst aux src (bank aux+bank src) k1
      hrestore hrestoreBody (Ne.symm hsa) haux
  have hdst : k2 dst = bank dst := by
    simp [k2,k1,update,splitResult,Ne.symm had,Ne.symm hsd,Ne.symm htd]
  have htarget : Silent rows ⟨clearDst,k2⟩ ⟨transfer,k3⟩ (bank dst+1) :=
    clear_run rows clearDst transfer dst (bank dst) k2 hclear hdst
  have htmp : k3 tmp = bank tmp + bank src := by
    simp [k3,k2,k1,clear,update,splitResult,htd,hta,Ne.symm hst]
  have hfinish : Silent rows ⟨transfer,k3⟩ ⟨exit,k4⟩ (2*(bank tmp+bank src)+1) := by
    exact expanded_move_run rows transfer transferBody exit tmp dst (bank tmp+bank src) k3
      htransfer htransferBody htd htmp
  have hq := silent_trans rows _ _ _ _ _ hsplit hmove
  have hq := silent_trans rows _ _ _ _ _ hq htarget
  have hq := silent_trans rows _ _ _ _ _ hq hfinish
  have heq : copyTime src tmp aux dst bank =
      (3*bank src+1)+(2*(bank aux+bank src)+1)+(bank dst+1)+(2*(bank tmp+bank src)+1) := by
    simp only [copyTime]; omega
  rw [heq]
  exact hq

/-- When scratch is initially zero, a verified copy block implements an
assignment and preserves the complete unbounded frame. -/
theorem copyRaw_clean (src tmp aux dst : Nat) (bank : Nat → Nat)
    (hst : src ≠ tmp) (hsa : src ≠ aux) (hsd : src ≠ dst)
    (hta : tmp ≠ aux) (htd : tmp ≠ dst) (had : aux ≠ dst)
    (htmp : bank tmp = 0) (haux : bank aux = 0) :
    copyRaw src tmp aux dst bank = (fun j => if j = dst then bank src else bank j) := by
  have hts : tmp ≠ src := Ne.symm hst
  have has : aux ≠ src := Ne.symm hsa
  have hds : dst ≠ src := Ne.symm hsd
  have hat : aux ≠ tmp := Ne.symm hta
  have hdt : dst ≠ tmp := Ne.symm htd
  have hda : dst ≠ aux := Ne.symm had
  funext j
  by_cases hs : j = src
  · subst j; simp_all [copyRaw,update,clear,splitResult]
  · by_cases ht : j = tmp
    · subst j; simp_all [copyRaw,update]
    · by_cases ha : j = aux
      · subst j; simp_all [copyRaw,update,clear]
      · by_cases hd : j = dst
        · subst j; simp_all [copyRaw,update,clear,splitResult]
        · simp_all [copyRaw,update,clear,splitResult]

/-- Exact result for arbitrary scratch values. Nonzero scratch modifies the
radix and branch registers, so its zero invariant cannot be omitted. -/
def afterReferenceRaw (bank : Nat → Nat) : Nat → Nat := fun j =>
  if j = 16 then 0 else if j = 4 then 0 else if j = 17 then 0
  else if j = 14 then bank 4 + bank 14
  else if j = 18 then bank 17 + bank 14 else bank j

def setupTime (bank : Nat → Nat) : Nat :=
  bank 16 + bank 18 + 7 * bank 14 + 2 * bank 4 + 2 * bank 17 + 5

/-- The whole compiled reference-preparation block, from the actual checked
row 6 through row 15. Its exact finite run and all-register effect hold even
when either scratch register is initially nonzero. -/
theorem reference_setup_raw (bank : Nat → Nat) :
    Silent originalRows ⟨6,bank⟩ ⟨15,afterReferenceRaw bank⟩ (setupTime bank) := by
  let k0 := clear 16 bank
  have hr6 : originalRows[6]? = some ⟨.dec 16,6,7⟩ := by decide
  have hr7 : originalRows[7]? = some ⟨.dec 14,8,10⟩ := by decide
  have hr8 : originalRows[8]? = some ⟨.inc 17,9,9⟩ := by decide
  have hr9 : originalRows[9]? = some ⟨.inc 4,7,7⟩ := by decide
  have hr10 : originalRows[10]? = some ⟨.dec 4,11,12⟩ := by decide
  have hr11 : originalRows[11]? = some ⟨.inc 14,10,10⟩ := by decide
  have hr12 : originalRows[12]? = some ⟨.dec 18,12,13⟩ := by decide
  have hr13 : originalRows[13]? = some ⟨.dec 17,14,15⟩ := by decide
  have hr14 : originalRows[14]? = some ⟨.inc 18,13,13⟩ := by decide
  have hclear : Silent originalRows ⟨6,bank⟩ ⟨7,k0⟩ (bank 16+1) :=
    clear_run originalRows 6 7 16 (bank 16) bank hr6 rfl
  have hcopy := copy_block originalRows 7 8 9 10 11 12 13 14 15 14 17 4 18 k0
    hr7 hr8 hr9 hr10 hr11 hr12 hr13 hr14
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have heffect : copyRaw 14 17 4 18 k0 = afterReferenceRaw bank := by
    funext j
    by_cases h16 : j = 16
    · subst j; simp [copyRaw,k0,update,splitResult,clear,afterReferenceRaw]
    · by_cases h4 : j = 4
      · subst j; simp [copyRaw,update,clear,afterReferenceRaw]
      · by_cases h17 : j = 17
        · subst j; simp [copyRaw,update,afterReferenceRaw]
        · by_cases h14 : j = 14
          · subst j; simp [copyRaw,k0,update,splitResult,clear,afterReferenceRaw]
          · by_cases h18 : j = 18
            · subst j; simp [copyRaw,k0,update,splitResult,clear,afterReferenceRaw]
            · simp [copyRaw,k0,update,splitResult,clear,afterReferenceRaw,h16,h4,h17,h14,h18]
  have htime : setupTime bank = (bank 16+1) + copyTime 14 17 4 18 k0 := by
    simp [setupTime,copyTime,k0,clear]; omega
  rw [htime,← heffect]
  exact silent_trans originalRows _ _ _ _ _ hclear hcopy

/-- Each zero-scratch premise is necessary for its corresponding source
field to have the intended value, for every initial bank. -/
theorem scratch_zero_necessary (bank : Nat → Nat) :
    (afterReferenceRaw bank 14 = bank 14 ↔ bank 4 = 0) ∧
    (afterReferenceRaw bank 18 = bank 14 ↔ bank 17 = 0) := by
  simp [afterReferenceRaw]

/-- With the two scratch slots zero, the operation is exactly
`expected := 0; branches := radix`, with the rest of the bank preserved. -/
theorem reference_setup_effect (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    afterReferenceRaw bank = (fun j => if j = 16 then 0 else if j = 18 then bank 14 else bank j) := by
  funext j
  by_cases h16 : j = 16
  · subst j; simp [afterReferenceRaw]
  · by_cases hj4 : j = 4
    · subst j; simp [afterReferenceRaw,h4]
    · by_cases hj17 : j = 17
      · subst j; simp [afterReferenceRaw,h17]
      · by_cases hj14 : j = 14
        · subst j; simp [afterReferenceRaw,h4]
        · by_cases hj18 : j = 18
          · subst j; simp [afterReferenceRaw,h17]
          · simp [afterReferenceRaw,h16,hj4,hj17,hj14,hj18]

/-- The checked grammar identifies the reference-result, branch, radix, and
scratch slots used by the source-side projection. The source allocation itself
is still a separate translation obligation. -/
theorem reference_slots_named :
    PreControlGrammar.grammar.names[14]? = some "$liveframe.0.3" ∧
    PreControlGrammar.grammar.names[16]? = some "$liveframe.0.5" ∧
    PreControlGrammar.grammar.names[18]? = some "$liveframe.0.6" ∧
    PreControlGrammar.grammar.names[4]? = some "$scratch.copy" ∧
    PreControlGrammar.grammar.names[17]? = some "$pool0.tmp0" := by decide

/-- With zero scratch, reference preparation preserves every controller field
and initializes the two reference-search registers. -/
theorem reference_source_projection (bank : Nat → Nat) (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    sourceState (afterReferenceRaw bank) .compare = sourceState bank .compare ∧
    afterReferenceRaw bank 16 = 0 ∧ afterReferenceRaw bank 18 = bank 14 := by
  rw [reference_setup_effect bank h4 h17]
  simp [sourceState]

/-- Any checked event refinement preserves silence over a whole finite source
segment, not merely at its endpoints. -/
theorem silent_interval_transfer {S T : Type} {src : EventSystem S} {dst : EventSystem T}
    (r : EventRefinement src dst) (start duration : Nat)
    (hquiet : ∀ i, start ≤ i → i < start+duration → ¬ src.BeepAt i) :
    ∀ u, r.boundary start ≤ u → u < r.boundary (start+duration) → ¬ dst.BeepAt u := by
  intro u hlo hhi hb
  obtain ⟨i,hilo,hihi,hulo,huhi⟩ := r.covers_between hlo hhi
  exact hquiet i hilo hihi ((r.event_iff i).2 ⟨u,hulo,huhi,hb⟩)

/-- The checked grammar takes at most 32 grammar transitions per graph
step, uniformly over the full unbounded bank. -/
theorem grammar_boundary_bound (t n : Nat) :
    PreControlGrammar.acceptedRefinement.boundary (t+n) ≤
      PreControlGrammar.acceptedRefinement.boundary t + 32*n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs := PreControlGrammar.checked_boundary_bound PreControlGrammar.grammar originalRows
      PreControlGrammar.positions PreControlGrammar.graph_checked (t+n)
    change PreControlGrammar.acceptedRefinement.boundary (t+n+1) ≤
      PreControlGrammar.acceptedRefinement.boundary (t+n) + 32 at hs
    have ht : t+(n+1) = t+n+1 := by omega
    rw [ht,Nat.mul_succ]
    omega

/-- At every reachable row-6 boundary the pre-control grammar performs the
whole reference setup in finite positive time and emits no event. -/
theorem reachable_setup_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩) :
    let r := PreControlGrammar.acceptedRefinement
    r.boundary t < r.boundary (t+setupTime bank) ∧
    ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+setupTime bank))).bank = afterReferenceRaw bank ∧
    ∀ u, r.boundary t ≤ u → u < r.boundary (t+setupTime bank) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u := by
  dsimp only
  let r := PreControlGrammar.acceptedRefinement
  have hp : 0 < setupTime bank := by simp only [setupTime]; omega
  have hseg := reference_setup_raw bank
  have hend : (system originalRows).run (t+setupTime bank) = ⟨15,afterReferenceRaw bank⟩ := by
    rw [EventSystem.run_add,hstate]
    exact hseg.1
  have hrel := r.related (t+setupTime bank)
  change ProducerGrammar.Rel originalRows PreControlGrammar.positions _ _ at hrel
  have hbank : ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+setupTime bank))).bank = afterReferenceRaw bank := by
    rw [hend] at hrel
    exact hrel.2.1.symm
  have hquiet : ∀ i, t ≤ i → i < t+setupTime bank → ¬ (system originalRows).BeepAt i := by
    intro i hlo hhi hb
    have heq : i = t+(i-t) := by omega
    have hb' : (system originalRows).BeepFrom ⟨6,bank⟩ (i-t) := by
      rw [heq] at hb
      have ht := ((system originalRows).beepAt_add_iff t (i-t)).1 hb
      simpa [hstate] using ht
    exact hseg.2 (i-t) (by omega) hb'
  exact ⟨r.boundary_strict (by omega),hbank,silent_interval_transfer r t (setupTime bank) hquiet⟩

/-- With zero scratch slots the checked finite grammar segment prepares
exactly the intended reference-search registers. -/
theorem reachable_setup_source_effect (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    ((ProducerGrammar.system PreControlGrammar.grammar).run
      (PreControlGrammar.acceptedRefinement.boundary (t+setupTime bank))).bank =
      (fun j => if j = 16 then 0 else if j = 18 then bank 14 else bank j) := by
  have h := (reachable_setup_to_grammar t bank hstate).2.1
  rw [h,reference_setup_effect bank h4 h17]

/-- The reachable grammar boundary satisfies the source-reference projection,
with no event during the interval and an explicit grammar-time bound. -/
theorem reachable_setup_source_projection (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨6,bank⟩)
    (h4 : bank 4 = 0) (h17 : bank 17 = 0) :
    let r := PreControlGrammar.acceptedRefinement
    let b := ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+setupTime bank))).bank
    r.boundary t < r.boundary (t+setupTime bank) ∧
    r.boundary (t+setupTime bank) ≤ r.boundary t + 32*setupTime bank ∧
    sourceState b .compare = sourceState bank .compare ∧ b 16 = 0 ∧ b 18 = bank 14 ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+setupTime bank) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  have h := reachable_setup_to_grammar t bank hstate
  have hp := reference_source_projection bank h4 h17
  rw [h.2.1]
  exact ⟨h.1,grammar_boundary_bound t (setupTime bank),hp.1,hp.2.1,hp.2.2,h.2.2⟩

/-- After the previously proved candidate-begin segment, the first reference
setup starts from the exact all-zero-entry bank. -/
theorem first_setup_graph :
    (system originalRows).run 6 = ⟨6,afterBegin firstBank⟩ := by
  have h := begin_segment firstBank
  have h13 : firstBank 13 = 0 := by simp [firstBank,update]
  have h14 : firstBank 14 = 0 := by simp [firstBank,update]
  have h15 : firstBank 15 = 0 := by simp [firstBank,update]
  simp only [h13,h14,h15,Nat.zero_add,Nat.add_zero] at h
  have he : 6 = 1+5 := by decide
  rw [he,EventSystem.run_add,first_begin_graph]
  exact h.1

/-- Starting from zero, reference preparation is reached silently and ends
with one branch, zero expected value and restored scratch cells. -/
theorem first_reference_setup :
    let r := PreControlGrammar.acceptedRefinement
    let b := ((ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary 18)).bank
    b 14 = 1 ∧ b 18 = 1 ∧ b 16 = 0 ∧ b 4 = 0 ∧ b 17 = 0 ∧
    (∀ u, r.boundary 6 ≤ u → u < r.boundary 18 →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  let bank := afterBegin firstBank
  let r := PreControlGrammar.acceptedRefinement
  have htime : setupTime bank = 12 := by
    simp [bank,setupTime,afterBegin,firstBank,clear,update]
  have h := reachable_setup_to_grammar 6 bank first_setup_graph
  simp only [htime,Nat.reduceAdd] at h
  have hvals : afterReferenceRaw bank 14 = 1 ∧ afterReferenceRaw bank 18 = 1 ∧
      afterReferenceRaw bank 16 = 0 ∧ afterReferenceRaw bank 4 = 0 ∧ afterReferenceRaw bank 17 = 0 := by
    simp [afterReferenceRaw,bank,afterBegin,firstBank,clear,update]
  rw [h.2.1]
  exact ⟨hvals.1,hvals.2.1,hvals.2.2.1,hvals.2.2.2.1,hvals.2.2.2.2,h.2.2⟩

/-- From the all-zero entry through the first prepared reference-search
boundary, the pre-control grammar has exactly one event. -/
theorem first_reference_unique_event :
    let r := PreControlGrammar.acceptedRefinement
    ∃ event, (event < r.boundary 18 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt event) ∧
      ∀ other, (other < r.boundary 18 ∧ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt other) → other = event := by
  dsimp only
  let r := PreControlGrammar.acceptedRefinement
  have hfirst := first_comparison_at_grammar
  have hsetup := first_reference_setup
  have hbound : r.boundary 6 ≤ r.boundary 18 := r.boundary_mono (by decide)
  dsimp only [r] at hbound
  obtain ⟨event,hevent,hunique⟩ := hfirst.2.2
  refine ⟨event,⟨by omega,hevent.2⟩,?_⟩
  intro other hother
  by_cases hbefore : other < PreControlGrammar.acceptedRefinement.boundary 6
  · exact hunique other ⟨hbefore,hother.2⟩
  · have hq := hsetup.2.2.2.2.2
    exact False.elim (hq other (by omega) hother.1 hother.2)

end Shared.PNP.Record285.SourceReferenceStart
