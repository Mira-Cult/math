import Shared.PNP.Record285.WitnessTruncation

/-! A finite nondeterministic loader writes choice bits on the actual tape,
returns to the initial head and orientation, and enters relocated verifier rows. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.ChoiceLoader
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput

def offset (k : Nat) : Nat := 2*k+2

def relocate {n : Nat} (k : Nat) (q : Fin n) : Fin (offset k+n) :=
  ⟨offset k+q.val, by have h := q.isLt; omega⟩

def relocateConfig {n : Nat} (k : Nat) (c : FiniteConfig n) : FiniteConfig (offset k+n) :=
  ⟨relocate k c.state,c.physical,c.choices⟩

def table (k n : Nat) (hn : 0 < n) (f : Fin n → Bool → Bool → FiniteAction n)
    (q : Fin (offset k+n)) (read choice : Bool) : FiniteAction (offset k+n) :=
  if h : q.val < offset k then
    ⟨if q.val < k then choice else read,
      decide (q.val = k ∨ q.val = 2*k+1),
      some ⟨q.val+1,by omega⟩⟩
  else
    let r := f ⟨q.val-offset k,by have hq := q.isLt; omega⟩ read choice
    ⟨r.write,r.turn,r.next.map (relocate k)⟩

/-- Relocation preserves every verifier transition and its complete tape. -/
theorem relocated_step (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig n) :
    finiteStep (table k n hn f) (relocateConfig k c) =
      (finiteStep f c).map (relocateConfig k) := by
  unfold finiteStep table relocateConfig relocate
  simp only
  have h : ¬ offset k+c.state.val < offset k := by omega
  simp only [h, ↓reduceDIte, Nat.add_sub_cancel_left]
  cases (f c.state (c.physical.tape c.physical.head) (c.choices.testBit 0)).next <;> simp

/-- Every finite verifier continuation is simulated with identical tape, head,
facing, remaining choice bits, and the same HALT time. -/
theorem relocated_run (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig n) (clock : Nat) :
    finiteRun (table k n hn f) clock (relocateConfig k c) =
      (finiteRun f clock c).map (relocateConfig k) := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    simp only [finiteRun,relocated_step]
    cases hs : finiteStep f c with
    | none => rfl
    | some next => exact ih next

/-- Complete tape after writing the first `count` low choice bits. Cells
outside the written interval are preserved, including arbitrary high suffixes. -/
def written (tape : Int → Bool) (choices count : Nat) : Int → Bool :=
  fun p => if 0 ≤ p ∧ p < (count : Int) then choices.testBit p.toNat else tape p

theorem written_zero (tape : Int → Bool) (choices : Nat) : written tape choices 0 = tape := by
  funext p
  simp [written]
  omega

theorem written_step (tape : Int → Bool) (choices count : Nat) :
    writeTape ⟨written tape choices count,(count : Int),false⟩ (choices.testBit count) =
      written tape choices (count+1) := by
  funext p
  simp only [writeTape,written]
  by_cases he : p = (count : Int)
  · subst p
    rw [if_pos rfl]
    have hp : 0 ≤ (count : Int) ∧ (count : Int) < ((count+1 : Nat) : Int) := by omega
    rw [if_pos hp]
    simp
  · rw [if_neg he]
    have hiff : (0 ≤ p ∧ p < (count : Int)) ↔
        (0 ≤ p ∧ p < ((count+1 : Nat) : Int)) := by omega
    by_cases hin : 0 ≤ p ∧ p < (count : Int)
    · rw [if_pos hin,if_pos (hiff.mp hin)]
    · rw [if_neg hin,if_neg (fun h => hin (hiff.mpr h))]

/-- Rewriting the scanned symbol to itself leaves the entire tape unchanged. -/
theorem write_read (c : TapeConfig) : writeTape c (c.tape c.head) = c.tape := by
  funext p
  by_cases h : p = c.head <;> simp [writeTape,h]

/-- Writing-phase configuration, including the untouched remainder of the
choice stream and every cell outside the written prefix. -/
def writingConfig (k n : Nat) (hn : 0 < n) (tape : Int → Bool)
    (choices i : Nat) (hi : i ≤ k) : FiniteConfig (offset k+n) :=
  ⟨⟨i,by unfold offset; omega⟩,⟨written tape choices i,(i : Int),false⟩,choices/2^i⟩

theorem writing_step (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n)
    (tape : Int → Bool) (choices i : Nat) (hi : i < k) :
    finiteStep (table k n hn f) (writingConfig k n hn tape choices i (by omega)) =
      some (writingConfig k n hn tape choices (i+1) (by omega)) := by
  have hidx : i < offset k := by unfold offset; omega
  have hbit : (choices/2^i).testBit 0 = choices.testBit i := by
    rw [Nat.testBit_div_two_pow]; simp
  have htail : (choices/2^i)/2 = choices/2^(i+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
  have hturn : ¬ (i = k ∨ i = 2*k+1) := by omega
  simp only [finiteStep,writingConfig,table,hidx, ↓reduceDIte,hi, ↓reduceIte,
    hturn,decide_false,Option.map_some,hbit,htail,physicalStep,Bool.false_eq_true,
    Bool.xor_self]
  rw [written_step]
  simp

/-- Any finite number of writing steps has the exact whole-tape effect and
consumes one choice bit per step. -/
theorem writing_run (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (choices i steps : Nat) (h : i+steps ≤ k) :
    finiteRun (table k n hn f) steps (writingConfig k n hn tape choices i (by omega)) =
      some (writingConfig k n hn tape choices (i+steps) (by omega)) := by
  induction steps generalizing i with
  | zero => simp [finiteRun]
  | succ steps ih =>
    have hi : i < k := by omega
    have hs := writing_step k n hn f tape choices i hi
    simp only [finiteRun,hs]
    have hh := ih (i+1) (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

/-- After the outward turn, the loader retraces the written cells while
leaving the complete tape unchanged. -/
def rewindConfig (k n : Nat) (hn : 0 < n) (tape : Int → Bool)
    (choices j : Nat) (hj : j ≤ k) : FiniteConfig (offset k+n) :=
  ⟨⟨k+1+j,by unfold offset; omega⟩,
    ⟨written tape choices k,(k : Int)-1-(j : Int),true⟩,choices/2^(k+1+j)⟩

theorem turn_outward (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices : Nat) :
    finiteStep (table k n hn f) (writingConfig k n hn tape choices k (by omega)) =
      some (rewindConfig k n hn tape choices 0 (by omega)) := by
  have hidx : k < offset k := by unfold offset; omega
  have htail : (choices/2^k)/2 = choices/2^(k+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
  simp only [finiteStep,writingConfig,rewindConfig,table,hidx, ↓reduceDIte,
    Nat.lt_irrefl,if_false,true_or,decide_true,Option.map_some,htail,physicalStep,
    Bool.false_xor,if_true,if_false]
  rw [write_read]
  simp [Int.sub_eq_add_neg]

theorem rewind_step (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (choices j : Nat) (hj : j < k) :
    finiteStep (table k n hn f) (rewindConfig k n hn tape choices j (by omega)) =
      some (rewindConfig k n hn tape choices (j+1) (by omega)) := by
  have hidx : k+1+j < offset k := by unfold offset; omega
  have hnot : ¬ k+1+j < k := by omega
  have hturn : ¬ (k+1+j = k ∨ k+1+j = 2*k+1) := by omega
  have htail : (choices/2^(k+1+j))/2 = choices/2^(k+1+(j+1)) := by
    have he : k+1+(j+1) = (k+1+j)+1 := by omega
    rw [he,Nat.pow_succ,Nat.div_div_eq_div_mul]
  simp only [finiteStep,rewindConfig,table,hidx, ↓reduceDIte,hnot,if_false,hturn,
    decide_false,Option.map_some,htail,physicalStep,Bool.true_xor,if_false]
  rw [write_read]
  simp [Int.sub_eq_add_neg,Nat.add_assoc] <;> omega

theorem rewind_run (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (choices j steps : Nat) (h : j+steps ≤ k) :
    finiteRun (table k n hn f) steps (rewindConfig k n hn tape choices j (by omega)) =
      some (rewindConfig k n hn tape choices (j+steps) (by omega)) := by
  induction steps generalizing j with
  | zero => simp [finiteRun]
  | succ steps ih =>
    have hj : j < k := by omega
    have hs := rewind_step k n hn f tape choices j hj
    simp only [finiteRun,hs]
    have hh := ih (j+1) (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem turn_inward (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices : Nat) :
    finiteStep (table k n hn f) (rewindConfig k n hn tape choices k (by omega)) =
      some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape choices k,0,false⟩,choices/2^(offset k)⟩) := by
  have hidx : k+1+k < offset k := by unfold offset; omega
  have hnot : ¬ k+1+k < k := by omega
  have hturn : k+1+k = k ∨ k+1+k = 2*k+1 := by omega
  have htail : (choices/2^(k+1+k))/2 = choices/2^(offset k) := by
    have he : offset k = (k+1+k)+1 := by unfold offset; omega
    rw [he,Nat.pow_succ,Nat.div_div_eq_div_mul]
  simp only [finiteStep,rewindConfig,relocateConfig,relocate,table,hidx, ↓reduceDIte,
    hnot,if_false,hturn,decide_true,Option.map_some,htail,physicalStep,Bool.true_xor,
    Bool.not_true,if_false]
  rw [write_read]
  simp [offset,Int.sub_eq_add_neg,Nat.add_assoc] <;> omega

/-- Split a finite execution at an exact intermediate boundary. -/
theorem finiteRun_add {n : Nat} (f : Fin n → Bool → Bool → FiniteAction n)
    (m l : Nat) (c : FiniteConfig n) :
    finiteRun f (m+l) c = (finiteRun f m c).bind (finiteRun f l) := by
  induction m generalizing c with
  | zero => simp [finiteRun]
  | succ m ih =>
    simp only [Nat.succ_add,finiteRun]
    cases hs : finiteStep f c with
    | none => rfl
    | some next => exact ih next

/-- Complete loader execution for an arbitrary initial tape, retaining the
entire frame outside the written witness window. -/
theorem loader_run (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices : Nat) :
    finiteRun (table k n hn f) (offset k)
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
    some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape choices k,0,false⟩,choices/2^(offset k)⟩) := by
  have hfirst := writing_run k n hn f tape choices 0 k (by omega)
  have hstart : writingConfig k n hn tape choices 0 (by omega) =
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ := by
    simp [writingConfig,written_zero]
  rw [hstart] at hfirst
  have hsecond := turn_outward k n hn f tape choices
  have hthird := rewind_run k n hn f tape choices 0 k (by omega)
  have hfourth := turn_inward k n hn f tape choices
  simp only [Nat.zero_add] at hfirst hthird
  have hd : offset k = k+(1+(k+1)) := by unfold offset; omega
  have htotal : finiteRun (table k n hn f) (k+(1+(k+1)))
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
      some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape choices k,0,false⟩,choices/2^(offset k)⟩) := by
    rw [finiteRun_add,hfirst]
    simp only [Option.bind_some,finiteRun,hsecond]
    change finiteRun (table k n hn f) (1+k) (rewindConfig k n hn tape choices 0 (by omega)) = _
    rw [Nat.add_comm 1 k,finiteRun_add]
    simp only [hthird,Option.bind_some,finiteRun,hfourth]
  simpa only [←hd] using htotal

/-- On a wholly blank tape, the written window is exactly the low `k` bits
of the choice stream and every other cell remains blank. -/
theorem written_blank (choices k : Nat) :
    written (inputTape 0) choices k = inputTape (choices%2^k) := by
  funext p
  by_cases hp : 0 ≤ p
  · have hpos : (p.toNat : Int) = p := Int.toNat_of_nonneg hp
    by_cases hi : p.toNat < k
    · have hj : p < (k : Int) := by omega
      simp [written,inputTape,hp,hj,hi,Nat.testBit_mod_two_pow]
    · have hj : ¬ p < (k : Int) := by omega
      simp [written,inputTape,hp,hj,hi,Nat.testBit_mod_two_pow]
  · simp [written,inputTape,hp]

theorem loader_blank_run (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (choices : Nat) :
    finiteRun (table k n hn f) (offset k)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    some (relocateConfig k (finiteInitial hn (choices%2^k) (choices/2^(offset k)))) := by
  have h := loader_run k n hn f (inputTape 0) choices
  simpa [finiteInitial,written_blank] using h

/-- Loader and verifier compose with the exact paid time and complete physical
configuration, including the verifier's unconsumed choice suffix. -/
theorem loader_then_verifier (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (choices clock : Nat) :
    finiteRun (table k n hn f) (offset k+clock)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    (finiteRun f clock (finiteInitial hn (choices%2^k) (choices/2^(offset k)))).map
      (relocateConfig k) := by
  rw [finiteRun_add,loader_blank_run]
  simp only [Option.bind_some]
  exact relocated_run k n hn f _ clock

/-- Every `k`-bit witness and every later verifier-choice stream can coexist
in one source choice integer; the turn and rewind steps consume their own bits. -/
theorem choices_compose (k witness tail : Nat) (hw : witness < 2^k) :
    (witness+2^(offset k)*tail)%2^k = witness ∧
    (witness+2^(offset k)*tail)/2^(offset k) = tail := by
  have hk : k ≤ offset k := by unfold offset; omega
  have hp : 2^k ≤ 2^(offset k) := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hw' : witness < 2^(offset k) := Nat.lt_of_lt_of_le hw hp
  have hdiv : 2^k ∣ 2^(offset k) := Nat.pow_dvd_pow 2 hk
  have hmod : 2^(offset k)%2^k = 0 := Nat.mod_eq_zero_of_dvd hdiv
  constructor
  · simp [Nat.add_mod,Nat.mul_mod,hmod,Nat.mod_eq_of_lt hw]
  · rw [Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2)),Nat.div_eq_of_lt hw']
    simp

/-- Exact reference-language search after the real blank-tape witness loader
and a relocated arbitrary verifier. The verifier receives the loaded witness
on its complete tape, and its choice stream is independent of that witness.
The verifier clock is the *actual remaining source clock*, not an assumed
shorter timeout. -/
theorem reference_loader_search (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let g := table k n hn f
    let states := offset k+n
    let clock := tableWidth states g + (offset k+padding)
    let remaining := tableWidth states g+padding
    referenceLanguage (canonical (bits clock (finiteProgram states g))) = true ↔
      ∃ witness, witness < 2^k ∧ ∃ tail,
        finiteRun f remaining (finiteInitial hn witness tail) = none := by
  dsimp only
  have hsource := Shared.PNP.Record285.WitnessTruncation.referenceLanguage_finite_unbounded_choices
    (offset k+n) (by unfold offset; omega) (table k n hn f) (offset k+padding)
  dsimp only at hsource
  have he : tableWidth (offset k+n) (table k n hn f)+(offset k+padding) =
      offset k+(tableWidth (offset k+n) (table k n hn f)+padding) := by omega
  rw [he] at hsource ⊢
  rw [hsource]
  constructor
  · rintro ⟨branch,haccept⟩
    rw [loader_then_verifier] at haccept
    have hbound : branch%2^k < 2^k := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
    refine ⟨branch%2^k,hbound,branch/2^(offset k),?_⟩
    cases hr : finiteRun f (tableWidth (offset k+n) (table k n hn f)+padding)
        (finiteInitial hn (branch%2^k) (branch/2^(offset k))) with
    | none => rfl
    | some value => simp [hr] at haccept
  · rintro ⟨witness,hw,tail,haccept⟩
    let branch := witness+2^(offset k)*tail
    refine ⟨branch,?_⟩
    rw [loader_then_verifier]
    have hsplit := choices_compose k witness tail hw
    change branch%2^k = witness ∧ branch/2^(offset k) = tail at hsplit
    rw [hsplit.1,hsplit.2,haccept]
    rfl

/-- The same verified blank-tape handoff expressed with Boolean-list
witnesses. Their length is not stored separately on the tape: trailing false
bits therefore represent the same physical tape. -/
theorem reference_loader_list_search (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let g := table k n hn f
    let states := offset k+n
    let clock := tableWidth states g + (offset k+padding)
    let remaining := tableWidth states g+padding
    referenceLanguage (canonical (bits clock (finiteProgram states g))) = true ↔
      ∃ witness : List Bool, witness.length ≤ k ∧ ∃ tail,
        finiteRun f remaining (finiteInitial hn (value witness) tail) = none := by
  dsimp only
  have h := reference_loader_search k n hn f padding
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨witness,hw,tail,haccept⟩
    refine ⟨bits k witness,by simp,tail,?_⟩
    rw [value_bits_of_lt k witness hw]
    exact haccept
  · rintro ⟨witness,hw,tail,haccept⟩
    have hp : 2^witness.length ≤ 2^k := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    refine ⟨value witness,Nat.lt_of_lt_of_le (value_lt_pow witness) hp,tail,haccept⟩

/-- The exact source frame for this loader has a quadratic state-count bound,
with both physical loader time and any verifier padding included. -/
theorem reference_loader_frame_bound (k n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let states := offset k+n
    let g := table k n hn f
    let clock := tableWidth states g + (offset k+padding)
    (canonical (bits clock (finiteProgram states g))).length ≤
      2*((4*states)*(16*states+8)+(offset k+padding))+1 := by
  exact finite_reference_frame_bound (offset k+n) (table k n hn f) (offset k+padding)

end Shared.PNP.Record285.ChoiceLoader
