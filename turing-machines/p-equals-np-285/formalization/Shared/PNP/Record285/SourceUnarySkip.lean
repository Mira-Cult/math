import Shared.PNP.Record285.SourceReferenceProgram

/-! Exact unary-record skipping for the reference evaluator. This covers the
checked graph's selector loop for arbitrary natural streams and full banks;
the subsequent graph action and virtual tape transition are proved separately
in `SourceVirtualStep`. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.SourceUnarySkip
open Shared.Beeping
open Shared.PNP.Record285.OwnershipCore
open Shared.PNP.Record285.RegisterProjection
open Shared.PNP.Record285.SourceBegin
open Shared.PNP.Record285.SourceReferenceStart
open Shared.PNP.Record285.SourceReferenceBranch
open Shared.PNP.Record285.SourceChoiceStep
open Shared.PNP.Record285.SourceReferenceProgram

def put (reg value : Nat) (bank : Nat → Nat) : Nat → Nat :=
  fun j => if j = reg then value else bank j

theorem put_same (reg x y : Nat) (bank : Nat → Nat) :
    put reg x (put reg y bank) = put reg x bank := by
  funext j
  by_cases hj : j = reg <;> simp [put,hj]

theorem half_as_put (bank : Nat → Nat) :
    update (.half 1) bank = put 1 (bank 1/2) bank := by
  funext j
  by_cases hj : j = 1 <;> simp [update,put,hj]

/-- A half-and-skip unary-record loop, for any checked control rows. -/
theorem pop_loop_generic (rows : Array Row) (head exit : Nat)
    (hrow : rows[head]? = some ⟨.half 1,head,exit⟩)
    (stream : Nat) (bank : Nat → Nat) (hstream : bank 1 = stream) :
    Silent rows ⟨head,bank⟩ ⟨exit,put 1 (Source.popUnary stream).2 bank⟩
      ((Source.popUnary stream).1+1) := by
  induction stream using Nat.strongRecOn generalizing bank with
  | ind stream ih =>
    by_cases hodd : stream % 2 = 1
    · have hlt : stream/2 < stream := by omega
      have heven : stream % 2 ≠ 0 := by omega
      let mid := update (.half 1) bank
      have hval : mid 1 = stream/2 := by simp [mid,update,hstream]
      have hstep : step rows ⟨head,bank⟩ = (⟨head,mid⟩,false) := by
        simp [step,hrow,observe,hstream,heven,mid]
      have hfirst := silent_one rows _ _ hstep
      have hrest := ih (stream/2) hlt mid hval
      have hresult : put 1 (Source.popUnary (stream/2)).2 mid =
          put 1 (Source.popUnary (stream/2)).2 bank := by
        rw [show mid = put 1 (stream/2) bank by simpa [mid,hstream] using half_as_put bank]
        exact put_same 1 _ _ bank
      rw [hresult] at hrest
      have h := silent_trans rows _ _ _ 1 ((Source.popUnary (stream/2)).1+1) hfirst hrest
      have hpop : Source.popUnary stream =
          ((Source.popUnary (stream/2)).1+1,(Source.popUnary (stream/2)).2) := by
        rw [Source.popUnary]
        simp [hodd]
      rw [hpop]
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    · have heven : stream % 2 = 0 := by omega
      let mid := update (.half 1) bank
      have hstep : step rows ⟨head,bank⟩ = (⟨exit,mid⟩,false) := by
        simp [step,hrow,observe,hstream,heven,mid]
      have hmid : mid = put 1 (stream/2) bank := by simpa [mid,hstream] using half_as_put bank
      have hpop : Source.popUnary stream = (0,stream/2) := by
        rw [Source.popUnary]
        simp [hodd]
      rw [hpop]
      simpa [hmid] using silent_one rows ⟨head,bank⟩ ⟨exit,mid⟩ hstep

/-- The reference row-52 loop consumes one complete unary record. -/
theorem pop_loop (stream : Nat) (bank : Nat → Nat) (hstream : bank 1 = stream) :
    Silent originalRows ⟨52,bank⟩ ⟨51,put 1 (Source.popUnary stream).2 bank⟩
      ((Source.popUnary stream).1+1) :=
  pop_loop_generic originalRows 52 51 (by decide) stream bank hstream

/-- Exact number of graph transitions for the selector loop. -/
def skipTime : Nat → Nat → Nat
  | 0,_ => 1
  | n+1,stream => 1 + ((Source.popUnary stream).1+1) + skipTime n (Source.popUnary stream).2

/-- A source bit-length bound gives a uniform finite graph-time bound for
all selectors, including records beyond the finite stream. -/
theorem skipTime_le (count stream bits : Nat) (hstream : stream < 2^bits) :
    skipTime count stream ≤ count*(bits+2)+1 := by
  induction count generalizing stream with
  | zero => simp [skipTime]
  | succ count ih =>
    have hpop := Source.popUnary_count_le_bits stream bits hstream
    have htail : (Source.popUnary stream).2 < 2^bits := by
      have hle := Nat.le_trans (Source.popUnary_tail_le_half stream) (Nat.div_le_self stream 2)
      exact Nat.lt_of_le_of_lt hle hstream
    have hrec := ih (Source.popUnary stream).2 htail
    simp only [skipTime,Nat.succ_mul]
    omega

/-- A checked selector and unary-skip loop at arbitrary control rows. -/
theorem skip_loop_generic (rows : Array Row) (head body exit : Nat)
    (hhead : rows[head]? = some ⟨.dec 3,body,exit⟩)
    (hbody : rows[body]? = some ⟨.half 1,body,head⟩)
    (count stream : Nat) (bank : Nat → Nat)
    (hcount : bank 3 = count) (hstream : bank 1 = stream) :
    Silent rows ⟨head,bank⟩
      ⟨exit,put 3 0 (put 1 (Source.skipUnary count stream) bank)⟩ (skipTime count stream) := by
  induction count generalizing stream bank with
  | zero =>
    have hz : bank 3 = 0 := hcount
    have hdec := dec_at_zero 3 bank hz
    have hs : step rows ⟨head,bank⟩ = (⟨exit,bank⟩,false) := by
      simp [step,hhead,observe,hz,hdec]
    have hresult : put 3 0 (put 1 stream bank) = bank := by
      funext j
      by_cases h3 : j = 3
      · subst j; simp [put,hz]
      · by_cases h1 : j = 1
        · subst j; simp [put,← hstream]
        · simp [put,h3,h1]
    simpa [skipTime,Source.skipUnary,hresult] using silent_one rows ⟨head,bank⟩ ⟨exit,bank⟩ hs
  | succ n ih =>
    have hp : bank 3 ≠ 0 := by omega
    let mid := update (.dec 3) bank
    let next := put 1 (Source.popUnary stream).2 mid
    have hs : step rows ⟨head,bank⟩ = (⟨body,mid⟩,false) := by
      simp [step,hhead,observe,hp,mid]
    have hfirst := silent_one rows _ _ hs
    have hmid : mid 1 = stream := by simp [mid,update,hstream]
    have hpop := pop_loop_generic rows body head hbody stream mid hmid
    change Silent rows ⟨body,mid⟩ ⟨head,next⟩ ((Source.popUnary stream).1+1) at hpop
    have hn : next 3 = n := by simp [next,put,mid,update]; omega
    have htail : next 1 = (Source.popUnary stream).2 := by simp [next,put]
    have hrest := ih (Source.popUnary stream).2 next hn htail
    have heffect : put 3 0 (put 1 (Source.skipUnary n (Source.popUnary stream).2) next) =
        put 3 0 (put 1 (Source.skipUnary (n+1) stream) bank) := by
      funext j
      by_cases h3 : j = 3
      · subst j; simp [put]
      · by_cases h1 : j = 1
        · subst j; simp [put,Source.skipUnary]
        · simp [next,put,mid,update,h3,h1]
    rw [heffect] at hrest
    have h := silent_trans rows _ _ _ 1 ((Source.popUnary stream).1+1) hfirst hpop
    have h := silent_trans rows _ _ _ _ _ h hrest
    simpa only [skipTime] using h

/-- The reference selector loop, instantiated from the generic checker. -/
theorem skip_loop (count stream : Nat) (bank : Nat → Nat)
    (hcount : bank 3 = count) (hstream : bank 1 = stream) :
    Silent originalRows ⟨51,bank⟩
      ⟨53,put 3 0 (put 1 (Source.skipUnary count stream) bank)⟩ (skipTime count stream) :=
  skip_loop_generic originalRows 51 52 53 (by decide) (by decide) count stream bank hcount hstream

/-- A checked unary-record counter at arbitrary control rows. -/
theorem pop_count_loop_generic (rows : Array Row) (head body exit : Nat)
    (hhead : rows[head]? = some ⟨.half 1,body,exit⟩)
    (hbody : rows[body]? = some ⟨.inc 3,head,head⟩)
    (stream : Nat) (bank : Nat → Nat) (hstream : bank 1 = stream) :
    Silent rows ⟨head,bank⟩
      ⟨exit,put 3 (bank 3 + (Source.popUnary stream).1) (put 1 (Source.popUnary stream).2 bank)⟩
      (2*(Source.popUnary stream).1+1) := by
  induction stream using Nat.strongRecOn generalizing bank with
  | ind stream ih =>
    by_cases hodd : stream % 2 = 1
    · have hlt : stream/2 < stream := by omega
      have heven : stream % 2 ≠ 0 := by omega
      let halfBank := update (.half 1) bank
      let mid := update (.inc 3) halfBank
      have h54 : step rows ⟨head,bank⟩ = (⟨body,halfBank⟩,false) := by
        simp [step,hhead,observe,hstream,heven,halfBank]
      have h55 : step rows ⟨body,halfBank⟩ = (⟨head,mid⟩,false) := by
        simp [step,hbody,observe,mid]
      have hfirst := silent_trans rows _ _ _ 1 1 (silent_one _ _ _ h54) (silent_one _ _ _ h55)
      have hmid : mid 1 = stream/2 := by simp [mid,halfBank,update,hstream]
      have hrest := ih (stream/2) hlt mid hmid
      have hpop : Source.popUnary stream =
          ((Source.popUnary (stream/2)).1+1,(Source.popUnary (stream/2)).2) := by
        rw [Source.popUnary]
        simp [hodd]
      have heffect :
          put 3 (mid 3 + (Source.popUnary (stream/2)).1)
            (put 1 (Source.popUnary (stream/2)).2 mid) =
          put 3 (bank 3 + ((Source.popUnary (stream/2)).1+1))
            (put 1 (Source.popUnary (stream/2)).2 bank) := by
        funext j
        by_cases h3 : j = 3
        · subst j; simp [put,mid,halfBank,update]; omega
        · by_cases h1 : j = 1
          · subst j; simp [put]
          · simp [put,mid,halfBank,update,h3,h1]
      rw [heffect] at hrest
      have h := silent_trans rows _ _ _ 2 (2*(Source.popUnary (stream/2)).1+1) hfirst hrest
      rw [hpop]
      have htime : 2*((Source.popUnary (stream/2)).1+1)+1 =
          2+(2*(Source.popUnary (stream/2)).1+1) := by omega
      simpa only [htime] using h
    · have heven : stream % 2 = 0 := by omega
      let mid := update (.half 1) bank
      have hs : step rows ⟨head,bank⟩ = (⟨exit,mid⟩,false) := by
        simp [step,hhead,observe,hstream,heven,mid]
      have hpop : Source.popUnary stream = (0,stream/2) := by
        rw [Source.popUnary]
        simp [hodd]
      have heffect : put 3 (bank 3+0) (put 1 (stream/2) bank) = mid := by
        funext j
        by_cases h3 : j = 3
        · subst j; simp [put,mid,update]
        · by_cases h1 : j = 1
          · subst j; simp [put,mid,update,hstream]
          · simp [put,mid,update,h3,h1]
      simp only [Nat.add_zero] at heffect
      rw [hpop]
      simp only [Nat.add_zero,Nat.mul_zero]
      rw [heffect]
      exact silent_one rows ⟨head,bank⟩ ⟨exit,mid⟩ hs

/-- The reference record counter, instantiated from the generic checker. -/
theorem pop_count_loop (stream : Nat) (bank : Nat → Nat) (hstream : bank 1 = stream) :
    Silent originalRows ⟨54,bank⟩
      ⟨56,put 3 (bank 3 + (Source.popUnary stream).1) (put 1 (Source.popUnary stream).2 bank)⟩
      (2*(Source.popUnary stream).1+1) :=
  pop_count_loop_generic originalRows 54 55 56 (by decide) (by decide) stream bank hstream

def afterSkip (bank : Nat → Nat) : Nat → Nat :=
  put 3 0 (put 1 (Source.skipUnary (bank 3) (bank 1)) bank)

/-- The executable graph has exactly the `skipUnary` data effect. -/
theorem skip_loop_bank (bank : Nat → Nat) :
    Silent originalRows ⟨51,bank⟩ ⟨53,afterSkip bank⟩ (skipTime (bank 3) (bank 1)) :=
  skip_loop (bank 3) (bank 1) bank rfl rfl

theorem afterSkip_read (bank : Nat → Nat) :
    afterSkip bank 1 = Source.skipUnary (bank 3) (bank 1) ∧ afterSkip bank 3 = 0 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → afterSkip bank j = bank j) := by
  refine ⟨by simp [afterSkip,put],by simp [afterSkip,put],?_⟩
  intro j h1 h3
  simp [afterSkip,put,h1,h3]

/-- Virtual-zero padding is part of the exact unbounded graph semantics. -/
theorem afterSkip_virtual_zero (bank : Nat → Nat) (h : bank 1 < 2^(bank 3)) :
    afterSkip bank 1 = 0 := by
  rw [(afterSkip_read bank).1]
  exact Source.skipUnary_zero_of_lt (bank 3) (bank 1) h

def recordBank (bank : Nat → Nat) : Nat → Nat :=
  put 3 (Source.popUnary (bank 1)).1 (put 1 (Source.popUnary (bank 1)).2 bank)

def recordTime (bank : Nat → Nat) : Nat :=
  (bank 3+1) + (2*(Source.popUnary (bank 1)).1+1)

/-- Clear and decode a complete record using checked control rows. -/
theorem record_decode_generic (rows : Array Row) (clearPc countPc countBody exit : Nat)
    (hrow : rows[clearPc]? = some ⟨.dec 3,clearPc,countPc⟩)
    (hcount : rows[countPc]? = some ⟨.half 1,countBody,exit⟩)
    (hbody : rows[countBody]? = some ⟨.inc 3,countPc,countPc⟩)
    (bank : Nat → Nat) :
    Silent rows ⟨clearPc,bank⟩ ⟨exit,recordBank bank⟩ (recordTime bank) := by
  let cleared := clear 3 bank
  have hc : Silent rows ⟨clearPc,bank⟩ ⟨countPc,cleared⟩ (bank 3+1) :=
    clear_run rows clearPc countPc 3 (bank 3) bank hrow rfl
  have hstream : cleared 1 = bank 1 := by simp [cleared,clear]
  have hv : cleared 3 = 0 := by simp [cleared,clear]
  have hp := pop_count_loop_generic rows countPc countBody exit hcount hbody (bank 1) cleared hstream
  have heffect : put 3 (cleared 3 + (Source.popUnary (bank 1)).1)
      (put 1 (Source.popUnary (bank 1)).2 cleared) = recordBank bank := by
    funext j
    by_cases h3 : j = 3
    · subst j; simp [put,recordBank,hv]
    · by_cases h1 : j = 1
      · subst j; simp [put,recordBank]
      · simp [put,recordBank,cleared,clear,h3,h1]
  rw [heffect] at hp
  exact silent_trans rows _ _ _ _ _ hc hp

/-- The reference record decoder, instantiated from the generic checker. -/
theorem record_decode (bank : Nat → Nat) :
    Silent originalRows ⟨53,bank⟩ ⟨56,recordBank bank⟩ (recordTime bank) :=
  record_decode_generic originalRows 53 54 55 56 (by decide) (by decide) (by decide) bank

theorem recordBank_read (bank : Nat → Nat) :
    recordBank bank 3 = (Source.popUnary (bank 1)).1 ∧
    recordBank bank 1 = (Source.popUnary (bank 1)).2 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → recordBank bank j = bank j) := by
  refine ⟨by simp [recordBank,put],by simp [recordBank,put],?_⟩
  intro j h1 h3
  simp [recordBank,put,h1,h3]

def preparedBank (bank : Nat → Nat) : Nat → Nat := afterProgramRaw (choiceBank bank)
def decodedBank (bank : Nat → Nat) : Nat → Nat := afterSkip (preparedBank bank)
def prefixTime (bank : Nat → Nat) : Nat :=
  choiceTime bank + programTime (choiceBank bank) +
    skipTime ((preparedBank bank) 3) ((preparedBank bank) 1)

/-- Positive-clock execution reaches the end of record skipping in a finite
silent segment, with exact full-bank effect for every input bank. -/
theorem virtual_prefix_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨35,bank⟩ ⟨53,decodedBank bank⟩ (prefixTime bank) := by
  have hprepare := reference_prepare_raw bank hp
  have hskip := skip_loop_bank (preparedBank bank)
  exact silent_trans originalRows _ _ _ _ _ hprepare hskip

/-- With the explicit clean-scratch premises, the skipped program is exactly
`Source.simStep`'s selected unary record; every unrelated register is retained. -/
theorem decoded_matches_source (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    decodedBank bank 1 = Source.skipUnary
      ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15) ∧
    decodedBank bank 3 = 0 ∧
    decodedBank bank 0 = (referenceSimState bank).choices/2 ∧ decodedBank bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → decodedBank bank j = bank j) := by
  have hm := prepared_matches_source bank h4 h5
  have hs := afterSkip_read (preparedBank bank)
  change (preparedBank bank) 1 = _ ∧ (preparedBank bank) 3 = _ ∧
    (preparedBank bank) 0 = _ ∧ (preparedBank bank) 20 = _ ∧ _ at hm
  refine ⟨?_,?_,?_,?_,?_⟩
  · change afterSkip (preparedBank bank) 1 = _
    rw [hs.1,hm.2.1,hm.1]
  · exact hs.2.1
  · change afterSkip (preparedBank bank) 0 = _
    rw [hs.2.2 0 (by decide) (by decide),hm.2.2.1]
  · change afterSkip (preparedBank bank) 20 = _
    rw [hs.2.2 20 (by decide) (by decide),hm.2.2.2.1]
  · intro j h1 h3 h0 h20
    change afterSkip (preparedBank bank) j = bank j
    rw [hs.2.2 j h1 h3]
    exact hm.2.2.2.2 j h1 h3 h0 h20

/-- The composed prefix refines to the exact grammar with a positive bounded
boundary map and no event. -/
theorem virtual_prefix_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20) :
    let d := prefixTime bank
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[53]? = some g.pc ∧ g.bank = decodedBank bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hpTime : 0 < prefixTime bank := by
    unfold prefixTime choiceTime
    split <;> omega
  exact transfer_silent_graph t _ 35 53 bank _ hstate hpTime (virtual_prefix_raw bank hp)

/-- If the requested record lies beyond the finite program, the checked
prefix sees the virtual all-zero suffix. -/
theorem decoded_source_virtual_zero (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0)
    (h : bank 14+bank 15 < 2^((referenceSimState bank).selector + (referenceSimState bank).choices%2)) :
    decodedBank bank 1 = 0 := by
  rw [(decoded_matches_source bank h4 h5).1]
  exact Source.skipUnary_zero_of_lt _ _ h

/-- At a reachable positive-clock boundary, the exact grammar reaches the
source-selected record and preserves the unbounded frame. -/
theorem virtual_prefix_matches_source (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20)
    (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    let d := prefixTime bank
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[53]? = some g.pc ∧
    g.bank 1 = Source.skipUnary
      ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15) ∧
    g.bank 3 = 0 ∧ g.bank 0 = (referenceSimState bank).choices/2 ∧ g.bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → g.bank j = bank j) ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  have h := virtual_prefix_to_grammar t bank hstate hp
  have hm := decoded_matches_source bank h4 h5
  rw [h.2.2.2.1]
  exact ⟨h.1,h.2.1,h.2.2.1,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,h.2.2.2.2⟩

def recordDecodedBank (bank : Nat → Nat) : Nat → Nat := recordBank (decodedBank bank)
def recordPrefixTime (bank : Nat → Nat) : Nat := prefixTime bank + recordTime (decodedBank bank)

/-- The complete positive-clock prefix through selected-record decoding has
exact finite time, full-bank effect and no event. -/
theorem record_prefix_raw (bank : Nat → Nat) (hp : 0 < bank 20) :
    Silent originalRows ⟨35,bank⟩ ⟨56,recordDecodedBank bank⟩ (recordPrefixTime bank) :=
  silent_trans originalRows _ _ _ _ _ (virtual_prefix_raw bank hp) (record_decode (decodedBank bank))

/-- The decoded count and remaining stream are exactly the selected record in
`Source.simStep`; unrelated registers, including the full tail, are retained. -/
theorem record_matches_source (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    let stream := Source.skipUnary
      ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15)
    recordDecodedBank bank 3 = (Source.popUnary stream).1 ∧
    recordDecodedBank bank 1 = (Source.popUnary stream).2 ∧
    recordDecodedBank bank 0 = (referenceSimState bank).choices/2 ∧
    recordDecodedBank bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → recordDecodedBank bank j = bank j) := by
  dsimp only
  have hd := decoded_matches_source bank h4 h5
  have hr := recordBank_read (decodedBank bank)
  refine ⟨?_,?_,?_,?_,?_⟩
  · change recordBank (decodedBank bank) 3 = _
    rw [hr.1,hd.1]
  · change recordBank (decodedBank bank) 1 = _
    rw [hr.2.1,hd.1]
  · change recordBank (decodedBank bank) 0 = _
    rw [hr.2.2 0 (by decide) (by decide),hd.2.2.1]
  · change recordBank (decodedBank bank) 20 = _
    rw [hr.2.2 20 (by decide) (by decide),hd.2.2.2.1]
  · intro j h1 h3 h0 h20
    change recordBank (decodedBank bank) j = bank j
    rw [hr.2.2 j h1 h3]
    exact hd.2.2.2.2 j h1 h3 h0 h20

/-- Beyond the finite source program, the selected action record decodes to
zero and the source virtual step is the default HALT action. -/
theorem record_source_virtual_zero (bank : Nat → Nat) (h4 : bank 4 = 0) (h5 : bank 5 = 0)
    (h : bank 14+bank 15 < 2^((referenceSimState bank).selector + (referenceSimState bank).choices%2)) :
    recordDecodedBank bank 3 = 0 ∧ recordDecodedBank bank 1 = 0 ∧
      Source.simStep (bank 14+bank 15) (referenceSimState bank) = none := by
  have hskip : Source.skipUnary
      ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15) = 0 :=
    Source.skipUnary_zero_of_lt _ _ h
  have hm := record_matches_source bank h4 h5
  refine ⟨?_,?_,?_⟩
  · simpa [hskip,Source.popUnary] using hm.1
  · simpa [hskip,Source.popUnary] using hm.2.1
  · simp [Source.simStep,hskip,Source.popUnary]

/-- The selected-record decoder refines to the exact pre-control grammar with
a positive bounded time map and no spurious event. -/
theorem record_prefix_to_grammar (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20) :
    let d := recordPrefixTime bank
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[56]? = some g.pc ∧ g.bank = recordDecodedBank bank ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  have hpTime : 0 < recordPrefixTime bank := by
    unfold recordPrefixTime prefixTime choiceTime
    split <;> omega
  exact transfer_silent_graph t _ 35 56 bank _ hstate hpTime (record_prefix_raw bank hp)

/-- Source-level action-record values at the corresponding grammar boundary;
the two clean-scratch hypotheses are explicit. -/
theorem record_prefix_matches_source (t : Nat) (bank : Nat → Nat)
    (hstate : (system originalRows).run t = ⟨35,bank⟩) (hp : 0 < bank 20)
    (h4 : bank 4 = 0) (h5 : bank 5 = 0) :
    let stream := Source.skipUnary
      ((referenceSimState bank).selector + (referenceSimState bank).choices%2) (bank 14+bank 15)
    let d := recordPrefixTime bank
    let r := PreControlGrammar.acceptedRefinement
    let g := (ProducerGrammar.system PreControlGrammar.grammar).run (r.boundary (t+d))
    r.boundary t < r.boundary (t+d) ∧ r.boundary (t+d) ≤ r.boundary t + 32*d ∧
    PreControlGrammar.positions[56]? = some g.pc ∧
    g.bank 3 = (Source.popUnary stream).1 ∧ g.bank 1 = (Source.popUnary stream).2 ∧
    g.bank 0 = (referenceSimState bank).choices/2 ∧ g.bank 20 = bank 20-1 ∧
    (∀ j, j ≠ 1 → j ≠ 3 → j ≠ 0 → j ≠ 20 → g.bank j = bank j) ∧
    (∀ u, r.boundary t ≤ u → u < r.boundary (t+d) →
      ¬ (ProducerGrammar.system PreControlGrammar.grammar).BeepAt u) := by
  dsimp only
  have h := record_prefix_to_grammar t bank hstate hp
  have hm := record_matches_source bank h4 h5
  rw [h.2.2.2.1]
  exact ⟨h.1,h.2.1,h.2.2.1,hm.1,hm.2.1,hm.2.2.1,hm.2.2.2.1,hm.2.2.2.2,h.2.2.2.2⟩

end Shared.PNP.Record285.SourceUnarySkip
