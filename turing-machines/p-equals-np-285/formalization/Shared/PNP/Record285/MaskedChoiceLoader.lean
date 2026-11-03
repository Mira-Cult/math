import Shared.PNP.Record285.HardwireChoiceLoader
import Shared.ComplexityBridge.PairReverseWitness

/-! A choice loader with independently fixed or free cells. Fixed framing
bits are written by the actual source table; free cells still consume the
corresponding source choice bits. The complete tape and choice suffix are
preserved at the verifier handoff. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.MaskedChoiceLoader
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.ChoiceLoader
open Shared.PNP.Record285.HardwireChoiceLoader

/-- `some b` fixes a cell, while `none` keeps its corresponding choice bit. -/
def select : List (Option Bool) → Nat → Nat → List Bool
  | [], _, _ => []
  | a::rest, choices, pos => a.getD (choices.testBit pos) :: select rest choices (pos+1)

@[simp] theorem select_length (mask : List (Option Bool)) (choices pos : Nat) :
    (select mask choices pos).length = mask.length := by
  induction mask generalizing pos with
  | nil => rfl
  | cons a rest ih => simp [select,ih]

theorem select_get (mask : List (Option Bool)) (choices pos i : Nat) (hi : i < mask.length) :
    (select mask choices pos)[i]?.getD false = ((mask[i]?).getD none).getD (choices.testBit (pos+i)) := by
  induction mask generalizing pos i with
  | nil => simp at hi
  | cons a rest ih =>
    cases i with
    | zero => simp [select]
    | succ i =>
      have h : i < rest.length := by simpa using hi
      simpa [select,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (pos+1) i h

/-- Replace only the masked low window, retaining the complete high suffix. -/
def forced (mask : List (Option Bool)) (choices : Nat) : Nat :=
  value (select mask choices 0) + 2^mask.length*(choices/2^mask.length)

theorem forced_bit (mask : List (Option Bool)) (choices i : Nat) (hi : i < mask.length) :
    (forced mask choices).testBit i = ((mask[i]?).getD none).getD (choices.testBit i) := by
  have hb : value (select mask choices 0) < 2^mask.length := by
    simpa using value_lt_pow (select mask choices 0)
  have he : forced mask choices = 2^mask.length*(choices/2^mask.length)+value (select mask choices 0) := by
    simp [forced,Nat.add_comm]
  rw [he,Nat.testBit_two_pow_mul_add _ hb]
  simp only [hi,if_true,value_bit]
  simpa using select_get mask choices 0 i hi

theorem forced_tail (mask : List (Option Bool)) (choices : Nat) :
    forced mask choices / 2^mask.length = choices/2^mask.length := by
  simp [forced,Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2)),
    Nat.div_eq_of_lt (by simpa using value_lt_pow (select mask choices 0))]

theorem forced_tail_after (mask : List (Option Bool)) (choices i : Nat) (hi : mask.length ≤ i) :
    forced mask choices / 2^i = choices/2^i := by
  have he : i = mask.length+(i-mask.length) := by omega
  rw [he,Nat.pow_add,← Nat.div_div_eq_div_mul,forced_tail]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add,←he]

/-- The table overrides a choice only during the outward writing phase. -/
def table (k n : Nat) (hn : 0 < n) (mask : List (Option Bool))
    (f : Fin n → Bool → Bool → FiniteAction n)
    (q : Fin (offset k+n)) (read choice : Bool) : FiniteAction (offset k+n) :=
  ChoiceLoader.table k n hn f q read
    (if q.val < k then ((mask[q.val]?).getD none).getD choice else choice)

theorem table_after (k n : Nat) (hn : 0 < n) (mask : List (Option Bool))
    (f : Fin n → Bool → Bool → FiniteAction n) (q : Fin (offset k+n))
    (read choice : Bool) (hq : k ≤ q.val) :
    table k n hn mask f q read choice = ChoiceLoader.table k n hn f q read choice := by
  simp [table,show ¬ q.val < k by omega]

theorem safe_step (k n : Nat) (hn : 0 < n) (mask : List (Option Bool))
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig (offset k+n))
    (hc : k ≤ c.state.val) :
    finiteStep (table k n hn mask f) c = finiteStep (ChoiceLoader.table k n hn f) c := by
  unfold finiteStep
  rw [table_after k n hn mask f c.state _ _ hc]

theorem safe_run (k n : Nat) (hn : 0 < n) (mask : List (Option Bool))
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig (offset k+n))
    (hc : k ≤ c.state.val) (clock : Nat) :
    finiteRun (table k n hn mask f) clock c = finiteRun (ChoiceLoader.table k n hn f) clock c := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    simp only [finiteRun,safe_step k n hn mask f c hc]
    cases hs : finiteStep (ChoiceLoader.table k n hn f) c with
    | none => rfl
    | some next => exact ih next (HardwireChoiceLoader.base_step_stays_after k n hn k (by omega) f c next hc hs)

/-- During writing the entire tape is the normalized masked stream, while
the actual unconsumed choice stream remains independent. -/
def writingConfig (k n : Nat) (hn : 0 < n) (mask : List (Option Bool))
    (tape : Int → Bool) (choices i : Nat) (hi : i ≤ k) : FiniteConfig (offset k+n) :=
  ⟨⟨i,by unfold offset; omega⟩,⟨written tape (forced mask choices) i,(i : Int),false⟩,choices/2^i⟩

theorem writing_step (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (choices i : Nat) (hi : i < k) :
    finiteStep (table k n hn mask f) (writingConfig k n hn mask tape choices i (by omega)) =
    some (writingConfig k n hn mask tape choices (i+1) (by omega)) := by
  have hidx : i < offset k := by unfold offset; omega
  have hturn : ¬ (i = k ∨ i = 2*k+1) := by omega
  have htail : (choices/2^i)/2 = choices/2^(i+1) := by rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
  have hbit : (choices/2^i).testBit 0 = choices.testBit i := by rw [Nat.testBit_div_two_pow]; simp
  have hf := forced_bit mask choices i (by omega)
  simp only [finiteStep,writingConfig,table,ChoiceLoader.table,hidx, ↓reduceDIte,
    hi, ↓reduceIte,hturn,decide_false,Option.map_some,htail,hbit,physicalStep,
    Bool.false_eq_true,Bool.xor_self]
  rw [← hf,written_step]
  simp

theorem writing_run (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices i steps : Nat)
    (h : i+steps ≤ k) :
    finiteRun (table k n hn mask f) steps (writingConfig k n hn mask tape choices i (by omega)) =
      some (writingConfig k n hn mask tape choices (i+steps) (by omega)) := by
  induction steps generalizing i with
  | zero => simp [finiteRun]
  | succ steps ih =>
    have hs := writing_step k n hn mask hm f tape choices i (by omega)
    simp only [finiteRun,hs]
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (i+1) (by omega)

/-- Exact handoff after writing all masked cells. -/
theorem writing_handoff (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (tape : Int → Bool) (choices : Nat) :
    writingConfig k n hn mask tape choices k (by omega) =
      ChoiceLoader.writingConfig k n hn tape (forced mask choices) k (by omega) := by
  simp only [writingConfig,ChoiceLoader.writingConfig]
  rw [←hm,forced_tail]

/-- All finite loader phases terminate, with exact time and the whole tape
(including cells outside the written window) retained. -/
theorem loader_run (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices : Nat) :
    finiteRun (table k n hn mask f) (offset k)
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
    some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape (forced mask choices) k,0,false⟩,choices/2^(offset k)⟩) := by
  have hfirst := writing_run k n hn mask hm f tape choices 0 k (by omega)
  have hstart : writingConfig k n hn mask tape choices 0 (by omega) =
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ := by simp [writingConfig,written_zero]
  rw [hstart] at hfirst
  simp only [Nat.zero_add,writing_handoff k n hn mask hm] at hfirst
  have hrest := HardwireChoiceLoader.base_remainder k n hn k (by omega) f tape (forced mask choices)
  have hs : k ≤ (ChoiceLoader.writingConfig k n hn tape (forced mask choices) k (by omega)).state.val := by
    simp [ChoiceLoader.writingConfig]
  have hr := safe_run k n hn mask f _ hs (offset k-k)
  rw [hrest] at hr
  have ht : forced mask choices/2^(offset k) = choices/2^(offset k) :=
    forced_tail_after mask choices _ (by rw [hm]; unfold offset; omega)
  rw [ht] at hr
  have he : offset k = k+(offset k-k) := by unfold offset; omega
  have htotal : finiteRun (table k n hn mask f) (k+(offset k-k))
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
      some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape (forced mask choices) k,0,false⟩,choices/2^(offset k)⟩) := by
    rw [finiteRun_add,hfirst]
    simpa using hr
  simpa only [←he] using htotal

theorem forced_low (mask : List (Option Bool)) (choices : Nat) :
    forced mask choices % 2^mask.length = value (select mask choices 0) := by
  have h := value_lt_pow (select mask choices 0)
  simp only [select_length] at h
  simp [forced,Nat.add_mod,Nat.mod_eq_of_lt h]

/-- On blank tape the verifier receives precisely the selected finite word. -/
theorem loader_blank_run (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (f : Fin n → Bool → Bool → FiniteAction n) (choices : Nat) :
    finiteRun (table k n hn mask f) (offset k)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    some (relocateConfig k (finiteInitial hn (value (select mask choices 0)) (choices/2^(offset k)))) := by
  have h := loader_run k n hn mask hm f (inputTape 0) choices
  have hf : forced mask choices % 2^k = value (select mask choices 0) := by
    rw [←hm,forced_low]
  simpa [finiteInitial,written_blank,hf] using h

/-- The complete verifier continuation is simulated after exactly the loader
cost, including its full tape, head, facing and choice suffix. -/
theorem loader_then_verifier (k n : Nat) (hn : 0 < n) (mask : List (Option Bool)) (hm : mask.length = k)
    (f : Fin n → Bool → Bool → FiniteAction n) (choices clock : Nat) :
    finiteRun (table k n hn mask f) (offset k+clock)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    (finiteRun f clock (finiteInitial hn (value (select mask choices 0))
      (choices/2^(offset k)))).map (relocateConfig k) := by
  rw [finiteRun_add,loader_blank_run k n hn mask hm f]
  simp only [Option.bind_some]
  have hs : k ≤ (relocateConfig k (finiteInitial hn (value (select mask choices 0))
      (choices/2^(offset k)))).state.val := by
    simp [relocateConfig,relocate,finiteInitial,offset]
    omega
  rw [safe_run k n hn mask f _ hs]
  exact relocated_run k n hn f _ clock

/-- Changing bits at or above the mask length cannot change the written word. -/
theorem select_eq_of_low (mask : List (Option Bool)) (a b : Nat)
    (h : ∀ i < mask.length, a.testBit i = b.testBit i) :
    select mask a 0 = select mask b 0 := by
  apply List.ext_getElem
  · simp
  · intro i ha hb
    have hi : i < mask.length := by simpa using ha
    have h1 := select_get mask a 0 i hi
    have h2 := select_get mask b 0 i hi
    simp only [Nat.zero_add] at h1 h2
    rw [h i hi] at h1
    rw [List.getElem?_eq_getElem ha] at h1
    rw [List.getElem?_eq_getElem hb] at h2
    simpa using h1.trans h2.symm

/-- Reapplying the fixed/free mask to its own output leaves the word intact. -/
theorem select_forced (mask : List (Option Bool)) (choices : Nat) :
    select mask (forced mask choices) 0 = select mask choices 0 := by
  apply List.ext_getElem
  · simp
  · intro i ha hb
    have hi : i < mask.length := by simpa using ha
    have h1 := select_get mask (forced mask choices) 0 i hi
    have h2 := select_get mask choices 0 i hi
    simp only [Nat.zero_add,forced_bit mask choices i hi] at h1 h2
    rw [List.getElem?_eq_getElem ha] at h1
    rw [List.getElem?_eq_getElem hb] at h2
    cases hm : (mask[i]?).getD none with
    | none => simp [hm] at h1 h2; exact h1.trans h2.symm
    | some b => simp [hm] at h1 h2; exact h1.trans h2.symm

/-- Any selected masked word and any later verifier choice suffix are jointly
realizable by one source branch. -/
theorem choices_for_selection (mask : List (Option Bool)) (choices tail : Nat) :
    let k := mask.length
    let branch := forced mask choices%2^k + 2^(offset k)*tail
    select mask branch 0 = select mask choices 0 ∧ branch/2^(offset k) = tail := by
  dsimp only
  let k := mask.length
  let low := forced mask choices%2^k
  let branch := low+2^(offset k)*tail
  have hl : low < 2^k := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have hs := choices_compose k low tail hl
  change branch%2^k = low ∧ branch/2^(offset k) = tail at hs
  constructor
  · have hb : ∀ i < mask.length, branch.testBit i = (forced mask choices).testBit i := by
      intro i hi
      have h1 := congrArg (fun n => n.testBit i) hs.1
      have hi' : i < k := hi
      simpa [low,Nat.testBit_mod_two_pow,hi'] using h1
    exact (select_eq_of_low mask branch (forced mask choices) hb).trans (select_forced mask choices)
  · exact hs.2

/-- The selected source frame searches exactly all masked words and all
later verifier-choice suffixes; no malformed-mask behavior is hidden. -/
theorem reference_masked_search (mask : List (Option Bool)) (n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let k := mask.length
    let g := table k n hn mask f
    let total := offset k+n
    let clock := tableWidth total g+(offset k+padding)
    let remaining := tableWidth total g+padding
    referenceLanguage (canonical (bits clock (finiteProgram total g))) = true ↔
      ∃ choices tail, finiteRun f remaining
        (finiteInitial hn (value (select mask choices 0)) tail) = none := by
  dsimp only
  let k := mask.length
  let g := table k n hn mask f
  have hsource := Shared.PNP.Record285.WitnessTruncation.referenceLanguage_finite_unbounded_choices
    (offset k+n) (by unfold offset; omega) g (offset k+padding)
  dsimp only at hsource
  have he : tableWidth (offset k+n) g+(offset k+padding) =
      offset k+(tableWidth (offset k+n) g+padding) := by omega
  rw [he] at hsource
  change referenceLanguage (canonical (bits (tableWidth (offset k+n) g+(offset k+padding))
      (finiteProgram (offset k+n) g))) = true ↔ _
  rw [he,hsource]
  constructor
  · rintro ⟨branch,haccept⟩
    change finiteRun (table k n hn mask f) _ _ = none at haccept
    rw [loader_then_verifier k n hn mask rfl f] at haccept
    refine ⟨branch,branch/2^(offset k),?_⟩
    cases hr : finiteRun f (tableWidth (offset k+n) g+padding)
        (finiteInitial hn (value (select mask branch 0)) (branch/2^(offset k))) with
    | none => rfl
    | some value => simp [hr] at haccept
  · rintro ⟨choices,tail,haccept⟩
    let branch := forced mask choices%2^k+2^(offset k)*tail
    refine ⟨branch,?_⟩
    change finiteRun (table k n hn mask f) _ _ = none
    rw [loader_then_verifier k n hn mask rfl f]
    have hs := choices_for_selection mask choices tail
    change select mask branch 0 = select mask choices 0 ∧ branch/2^(offset k) = tail at hs
    rw [hs.1,hs.2,haccept]
    rfl

/-- Canonical Boolean-list encoding writes `[true,b,false]` for each
witness bit. Only the middle cell is nondeterministic. -/
def witnessMask (count : Nat) : List (Option Bool) :=
  (List.replicate count [some true,none,some false]).flatten

def framedMask (publicBits : List Bool) (count : Nat) : List (Option Bool) :=
  publicBits.map some ++ witnessMask count

def witnessBits (choices start : Nat) : Nat → List Bool
  | 0 => []
  | count+1 => choices.testBit (start+1) :: witnessBits choices (start+3) count

@[simp] theorem witnessBits_length (choices start count : Nat) :
    (witnessBits choices start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp [witnessBits,ih]

@[simp] theorem witnessMask_length (count : Nat) : (witnessMask count).length = 3*count := by
  induction count with
  | zero => rfl
  | succ count ih => simp [witnessMask,List.replicate_succ] at *; omega

@[simp] theorem framedMask_length (publicBits : List Bool) (count : Nat) :
    (framedMask publicBits count).length = publicBits.length+3*count := by simp [framedMask]

theorem select_append (a b : List (Option Bool)) (choices pos : Nat) :
    select (a++b) choices pos = select a choices pos ++ select b choices (pos+a.length) := by
  induction a generalizing pos with
  | nil => simp [select]
  | cons x xs ih => simp [select,ih,Nat.add_comm,Nat.add_left_comm]

theorem select_public (publicBits : List Bool) (choices pos : Nat) :
    select (publicBits.map some) choices pos = publicBits := by
  induction publicBits generalizing pos with
  | nil => rfl
  | cons x xs ih => simp [select,ih]

theorem select_witnessMask (choices start count : Nat) :
    select (witnessMask count) choices start = BitstringEncoding.bitEncode (witnessBits choices start count) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [witnessMask,List.replicate_succ,List.flatten_cons,select_append,
      select,List.length_cons,List.length_nil,witnessBits,
      Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    simpa [witnessMask,Nat.add_assoc] using ih (start+3)

theorem select_framedMask (publicBits : List Bool) (count choices : Nat) :
    select (framedMask publicBits count) choices 0 =
      publicBits ++ BitstringEncoding.bitEncode (witnessBits choices publicBits.length count) := by
  simp [framedMask,select_append,select_public,select_witnessMask]

/-- Every fixed-length witness can be chosen. Its encoded trailing blanks do
not need an end-of-tape marker; the mask supplies all framing cells. -/
theorem witnessBits_complete (publicBits witness : List Bool) :
    witnessBits (value (publicBits++BitstringEncoding.bitEncode witness))
      publicBits.length witness.length = witness := by
  induction witness generalizing publicBits with
  | nil => rfl
  | cons b bs ih =>
    have hb : (value (publicBits++BitstringEncoding.bitEncode (b::bs))).testBit (publicBits.length+1) = b := by
      rw [value_bit]
      simp [Shared.ComplexityBridge.PairReverseWitness.encode_cons]
    have hr := ih (publicBits++[true,b,false])
    simp only [List.length_append,List.length_cons,List.length_nil] at hr
    rw [Shared.ComplexityBridge.PairReverseWitness.encode_cons] at hb ⊢
    simp only [witnessBits,hb,List.length_cons]
    simpa [List.append_assoc,Nat.add_assoc] using hr

/-- The actual sentinel-terminated source reference searches exactly the
canonical encodings of all fixed-length witnesses. -/
theorem reference_framed_search (publicBits : List Bool) (count n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let mask := framedMask publicBits count
    let k := mask.length
    let g := table k n hn mask f
    let total := offset k+n
    let remaining := tableWidth total g+padding
    let clock := remaining+offset k
    referenceLanguage (canonical (bits clock (finiteProgram total g))) = true ↔
      ∃ witness : List Bool, witness.length = count ∧ ∃ tail,
        finiteRun f remaining (finiteInitial hn
          (value (publicBits++BitstringEncoding.bitEncode witness)) tail) = none := by
  dsimp only
  have h := reference_masked_search (framedMask publicBits count) n hn f padding
  dsimp only at h
  have he : tableWidth (offset (framedMask publicBits count).length+n)
      (table (framedMask publicBits count).length n hn (framedMask publicBits count) f)+
        (offset (framedMask publicBits count).length+padding) =
      (tableWidth (offset (framedMask publicBits count).length+n)
        (table (framedMask publicBits count).length n hn (framedMask publicBits count) f)+padding)+
          offset (framedMask publicBits count).length := by omega
  rw [he] at h
  rw [h]
  constructor
  · rintro ⟨choices,tail,ha⟩
    refine ⟨witnessBits choices publicBits.length count,by simp,tail,?_⟩
    simpa [select_framedMask] using ha
  · rintro ⟨witness,hw,tail,ha⟩
    let choices := value (publicBits++BitstringEncoding.bitEncode witness)
    refine ⟨choices,tail,?_⟩
    rw [select_framedMask]
    have hc : witnessBits choices publicBits.length count = witness := by
      rw [←hw]
      exact witnessBits_complete publicBits witness
    rw [hc]
    exact ha

end Shared.PNP.Record285.MaskedChoiceLoader
