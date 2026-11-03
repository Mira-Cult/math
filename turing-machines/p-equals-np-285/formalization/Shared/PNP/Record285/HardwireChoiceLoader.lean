import Shared.PNP.Record285.ChoiceLoader

/-! A source-relative finite loader for a fixed public prefix followed by
nondeterministically chosen witness bits. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Shared.PNP.Record285.HardwireChoiceLoader
open Shared.PNP.Record285.Source
open Shared.PNP.Record285.RelativeTape
open Shared.PNP.Record285.UnaryProgram
open Shared.PNP.Record285.UnaryReferenceTail
open Shared.PNP.Record285.CanonicalInput
open Shared.PNP.Record285.ChoiceLoader

/-- Replace exactly the low `width` choice bits with a fixed public prefix. -/
def forcePrefix (width publicValue choices : Nat) : Nat :=
  publicValue%2^width + 2^width*(choices/2^width)

theorem force_bit (width publicValue choices i : Nat) :
    (forcePrefix width publicValue choices).testBit i =
      if i < width then publicValue.testBit i else choices.testBit i := by
  have hp : publicValue%2^width < 2^width := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have he : forcePrefix width publicValue choices = 2^width*(choices/2^width)+publicValue%2^width := by
    simp [forcePrefix,Nat.add_comm]
  rw [he,Nat.testBit_two_pow_mul_add _ hp,Nat.testBit_mod_two_pow]
  by_cases hi : i < width
  · simp [hi]
  · simp only [hi,if_false]
    have hh : i-width+width = i := by omega
    rw [Nat.testBit_div_two_pow,hh]

theorem force_tail (width publicValue choices : Nat) :
    forcePrefix width publicValue choices / 2^width = choices/2^width := by
  simp [forcePrefix,Nat.add_mul_div_left _ _ (Nat.pow_pos (by decide : 0 < 2)),
    Nat.div_eq_of_lt (Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)))]

theorem force_tail_after (width publicValue choices i : Nat) (h : width ≤ i) :
    forcePrefix width publicValue choices / 2^i = choices/2^i := by
  have he : i = width+(i-width) := by omega
  rw [he,Nat.pow_add,← Nat.div_div_eq_div_mul,force_tail]
  rw [Nat.div_div_eq_div_mul,←Nat.pow_add,←he]

/-- The table writes the fixed public prefix in its first rows, then writes choice
bits; turning, rewind and the original verifier use unchanged rows. -/
def table (k n : Nat) (hn : 0 < n) (width publicValue : Nat)
    (f : Fin n → Bool → Bool → FiniteAction n)
    (q : Fin (offset k+n)) (read choice : Bool) : FiniteAction (offset k+n) :=
  ChoiceLoader.table k n hn f q read (if q.val < width then publicValue.testBit q.val else choice)

/-- At and after the fixed-publicValue boundary, the table is the existing
choice-loader table, including its relocated verifier. -/
theorem table_after (k n : Nat) (hn : 0 < n) (width publicValue : Nat)
    (f : Fin n → Bool → Bool → FiniteAction n) (q : Fin (offset k+n))
    (read choice : Bool) (hq : width ≤ q.val) :
    table k n hn width publicValue f q read choice = ChoiceLoader.table k n hn f q read choice := by
  simp [table,show ¬ q.val < width by omega]

/-- The tape after the fixed public prefix is identical to the corresponding
publicValue written by the normalized combined choice stream. -/
theorem written_prefix (tape : Int → Bool) (width publicValue choices : Nat) :
    written tape publicValue width = written tape (forcePrefix width publicValue choices) width := by
  funext p
  unfold written
  by_cases h : 0 ≤ p ∧ p < (width : Int)
  · rw [if_pos h,if_pos h]
    have hp : (p.toNat : Int) = p := Int.toNat_of_nonneg h.1
    have hi : p.toNat < width := by omega
    rw [force_bit]
    simp [hi]
  · simp [h]

/-- After the public-prefix-writing rows, every live loader or verifier step
stays beyond that boundary. -/
theorem base_step_stays_after (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (c next : FiniteConfig (offset k+n))
    (hc : width ≤ c.state.val) (hs : finiteStep (ChoiceLoader.table k n hn f) c = some next) :
    width ≤ next.state.val := by
  unfold finiteStep at hs
  by_cases hidx : c.state.val < offset k
  · simp only [ChoiceLoader.table,hidx, ↓reduceDIte,Option.map_some,Option.some.injEq] at hs
    cases hs
    simp only
    omega
  · simp only [ChoiceLoader.table,hidx, ↓reduceDIte] at hs
    generalize he : f ⟨c.state.val-offset k,by have hq := c.state.isLt; omega⟩
        (c.physical.tape c.physical.head) (c.choices.testBit 0) = action at hs
    cases hnext : action.next with
    | none => simp [hnext] at hs
    | some q =>
      simp only [hnext,Option.map_some,Option.some.injEq] at hs
      cases hs
      simp [relocate,offset]
      omega

theorem safe_step (k n : Nat) (hn : 0 < n) (width publicValue : Nat)
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig (offset k+n))
    (hc : width ≤ c.state.val) :
    finiteStep (table k n hn width publicValue f) c = finiteStep (ChoiceLoader.table k n hn f) c := by
  unfold finiteStep
  rw [table_after k n hn width publicValue f c.state _ _ hc]

/-- Once the public-prefix-writing rows have finished, the new table follows
exactly the previously verified loader/verifier for all remaining clocks. -/
theorem safe_run (k n : Nat) (hn : 0 < n) (width publicValue : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (c : FiniteConfig (offset k+n))
    (hc : width ≤ c.state.val) (clock : Nat) :
    finiteRun (table k n hn width publicValue f) clock c =
      finiteRun (ChoiceLoader.table k n hn f) clock c := by
  induction clock generalizing c with
  | zero => rfl
  | succ clock ih =>
    simp only [finiteRun,safe_step k n hn width publicValue f c hc]
    cases hs : finiteStep (ChoiceLoader.table k n hn f) c with
    | none => rfl
    | some next => exact ih next (base_step_stays_after k n hn width hw f c next hc hs)

/-- During the public-value phase the tape receives fixed bits, while the
original choice stream is still consumed one bit per physical transition. -/
def fixedConfig (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (tape : Int → Bool) (publicValue choices i : Nat) (hi : i ≤ width) : FiniteConfig (offset k+n) :=
  ⟨⟨i,by unfold offset; omega⟩,⟨written tape publicValue i,(i : Int),false⟩,choices/2^i⟩

theorem fixed_step (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (publicValue choices i : Nat) (hi : i < width) :
    finiteStep (table k n hn width publicValue f)
      (fixedConfig k n hn width hw tape publicValue choices i (by omega)) =
    some (fixedConfig k n hn width hw tape publicValue choices (i+1) (by omega)) := by
  have hidx : i < offset k := by unfold offset; omega
  have hik : i < k := by omega
  have hturn : ¬ (i = k ∨ i = 2*k+1) := by omega
  have htail : (choices/2^i)/2 = choices/2^(i+1) := by
    rw [Nat.div_div_eq_div_mul,Nat.pow_succ]
  simp only [finiteStep,fixedConfig,table,ChoiceLoader.table,hidx, ↓reduceDIte,
    hi, ↓reduceIte,hik,hturn,decide_false,Option.map_some,htail,physicalStep,
    Bool.false_eq_true,Bool.xor_self]
  rw [written_step]
  simp

theorem fixed_run (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (publicValue choices i steps : Nat) (h : i+steps ≤ width) :
    finiteRun (table k n hn width publicValue f) steps
      (fixedConfig k n hn width hw tape publicValue choices i (by omega)) =
    some (fixedConfig k n hn width hw tape publicValue choices (i+steps) (by omega)) := by
  induction steps generalizing i with
  | zero => simp [finiteRun]
  | succ steps ih =>
    have hi : i < width := by omega
    have hs := fixed_step k n hn width hw f tape publicValue choices i hi
    simp only [finiteRun,hs]
    have hh := ih (i+1) (by omega)
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

theorem fixed_handoff (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (tape : Int → Bool) (publicValue choices : Nat) :
    fixedConfig k n hn width hw tape publicValue choices width (by omega) =
      writingConfig k n hn tape (forcePrefix width publicValue choices) width (by omega) := by
  simp only [fixedConfig,writingConfig]
  rw [written_prefix,force_tail]

/-- The already checked choice loader finishes from any intermediate writing
boundary, with exact remaining time and the whole resulting tape. -/
theorem base_remainder (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool) (choices : Nat) :
    finiteRun (ChoiceLoader.table k n hn f) (offset k-width)
      (writingConfig k n hn tape choices width (by omega)) =
    some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape choices k,0,false⟩,choices/2^(offset k)⟩) := by
  have hfirst := writing_run k n hn f tape choices width (k-width) (by omega)
  have he : width+(k-width) = k := by omega
  have hfirst' : finiteRun (ChoiceLoader.table k n hn f) (k-width)
      (writingConfig k n hn tape choices width (by omega)) =
      some (writingConfig k n hn tape choices k (by omega)) := by
    simpa only [he] using hfirst
  have hsecond := turn_outward k n hn f tape choices
  have hthird := rewind_run k n hn f tape choices 0 k (by omega)
  simp only [Nat.zero_add] at hthird
  have hfourth := turn_inward k n hn f tape choices
  have hd : offset k-width = (k-width)+(1+(k+1)) := by unfold offset; omega
  have htotal : finiteRun (ChoiceLoader.table k n hn f) ((k-width)+(1+(k+1)))
      (writingConfig k n hn tape choices width (by omega)) =
      some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape choices k,0,false⟩,choices/2^(offset k)⟩) := by
    rw [finiteRun_add,hfirst']
    simp only [Option.bind_some,finiteRun,hsecond]
    change finiteRun (ChoiceLoader.table k n hn f) (1+k)
      (rewindConfig k n hn tape choices 0 (by omega)) = _
    rw [Nat.add_comm 1 k,finiteRun_add]
    simp only [hthird,Option.bind_some,finiteRun,hfourth]
  simpa only [←hd] using htotal

/-- Fixed public bits and nondeterministic suffix bits are written to the real
tape. The full initial tape outside the allocated window is retained. -/
theorem loader_run (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (tape : Int → Bool)
    (publicValue choices : Nat) :
    finiteRun (table k n hn width publicValue f) (offset k)
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
    some (relocateConfig k ⟨⟨0,hn⟩,
      ⟨written tape (forcePrefix width publicValue choices) k,0,false⟩,choices/2^(offset k)⟩) := by
  let forced := forcePrefix width publicValue choices
  have hfirst := fixed_run k n hn width hw f tape publicValue choices 0 width (by omega)
  have hstart : fixedConfig k n hn width hw tape publicValue choices 0 (by omega) =
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ := by
    simp [fixedConfig,written_zero]
  rw [hstart] at hfirst
  simp only [Nat.zero_add] at hfirst
  have hhandoff := fixed_handoff k n hn width hw tape publicValue choices
  change fixedConfig k n hn width hw tape publicValue choices width (by omega) =
    writingConfig k n hn tape forced width (by omega) at hhandoff
  rw [hhandoff] at hfirst
  let mid := writingConfig k n hn tape forced width (by omega)
  have hs : width ≤ mid.state.val := by simp [mid,writingConfig]
  have hsafe := safe_run k n hn width publicValue hw f mid hs (offset k-width)
  have hrest := base_remainder k n hn width hw f tape forced
  change finiteRun (ChoiceLoader.table k n hn f) (offset k-width) mid = _ at hrest
  rw [hrest] at hsafe
  have ht : forced/2^(offset k) = choices/2^(offset k) :=
    force_tail_after width publicValue choices (offset k) (by unfold offset; omega)
  rw [ht] at hsafe
  have hd : width+(offset k-width) = offset k := by unfold offset; omega
  have htotal : finiteRun (table k n hn width publicValue f) (width+(offset k-width))
      ⟨⟨0,by unfold offset; omega⟩,⟨tape,0,false⟩,choices⟩ =
      some (relocateConfig k ⟨⟨0,hn⟩,⟨written tape forced k,0,false⟩,choices/2^(offset k)⟩) := by
    rw [finiteRun_add,hfirst]
    exact hsafe
  simpa only [hd,forced] using htotal

/-- Blank tape is initialized with the fixed low public bits followed by the
remaining choice bits; head and orientation return to the original boundary. -/
theorem loader_blank_run (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (publicValue choices : Nat) :
    finiteRun (table k n hn width publicValue f) (offset k)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    some (relocateConfig k (finiteInitial hn ((forcePrefix width publicValue choices)%2^k)
      (choices/2^(offset k)))) := by
  have h := loader_run k n hn width hw f (inputTape 0) publicValue choices
  simpa [finiteInitial,written_blank] using h

/-- The entire verifier continuation is simulated, with the fixed public bits
and nondeterministic suffix actually present on the complete initial tape. -/
theorem loader_then_verifier (k n : Nat) (hn : 0 < n) (width : Nat) (hw : width ≤ k)
    (f : Fin n → Bool → Bool → FiniteAction n) (publicValue choices clock : Nat) :
    finiteRun (table k n hn width publicValue f) (offset k+clock)
      (finiteInitial (n := offset k+n) (by unfold offset; omega) 0 choices) =
    (finiteRun f clock (finiteInitial hn ((forcePrefix width publicValue choices)%2^k)
      (choices/2^(offset k)))).map (relocateConfig k) := by
  rw [finiteRun_add,loader_blank_run k n hn width hw f publicValue choices]
  simp only [Option.bind_some]
  have hs : width ≤ (relocateConfig k (finiteInitial hn
      ((forcePrefix width publicValue choices)%2^k) (choices/2^(offset k)))).state.val := by
    simp [relocateConfig,relocate,finiteInitial,offset]
    omega
  rw [safe_run k n hn width publicValue hw f _ hs]
  exact relocated_run k n hn f _ clock

/-- Numeric tape with the fixed low public field and the following witness. -/
def combined (width publicValue witness : Nat) : Nat :=
  publicValue%2^width + 2^width*witness

theorem combined_bound (width publicValue witness count : Nat) (h : witness < 2^count) :
    combined width publicValue witness < 2^(width+count) := by
  have hp : publicValue%2^width < 2^width := Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2))
  have hw : witness+1 ≤ 2^count := by omega
  have hm := Nat.mul_le_mul_left (2^width) hw
  have ha : combined width publicValue witness < 2^width*(witness+1) := by
    simp only [combined,Nat.mul_add,Nat.mul_one]
    omega
  rw [Nat.pow_add]
  exact Nat.lt_of_lt_of_le ha hm

theorem combined_low (width publicValue witness : Nat) :
    combined width publicValue witness % 2^width = publicValue%2^width := by
  simp [combined]

/-- Every forced tape window has the intended public field and a bounded
witness field; the input choices are unconstrained. -/
theorem forced_window (width count publicValue choices : Nat) :
    (forcePrefix width publicValue choices)%2^(width+count) =
      combined width publicValue ((choices/2^width)%2^count) := by
  let z := (forcePrefix width publicValue choices)%2^(width+count)
  have hd : 2^width ∣ 2^(width+count) := Nat.pow_dvd_pow 2 (by omega)
  have hlow : z%2^width = publicValue%2^width := by
    dsimp [z]
    rw [Nat.mod_mod_of_dvd _ hd]
    simp [forcePrefix]
  have hhigh : z/2^width = (choices/2^width)%2^count := by
    dsimp [z]
    rw [Nat.pow_add,Nat.mod_mul_right_div_self,force_tail]
  have hz := Nat.mod_add_div z (2^width)
  rw [hlow,hhigh] at hz
  exact hz.symm

/-- Choosing a public/witness field and a later choice tail is always possible
in the one source choice integer, and forcing the public field leaves it intact. -/
theorem choices_for_fields (width count publicValue witness tail : Nat) (hw : witness < 2^count) :
    let k := width+count
    let branch := combined width publicValue witness+2^(offset k)*tail
    (forcePrefix width publicValue branch)%2^k = combined width publicValue witness ∧
      branch/2^(offset k) = tail := by
  dsimp only
  have hbound := combined_bound width publicValue witness count hw
  have hsplit := choices_compose (width+count) (combined width publicValue witness) tail hbound
  have hmodOffset : 2^(offset (width+count))%2^width = 0 := by
    apply Nat.mod_eq_zero_of_dvd
    apply Nat.pow_dvd_pow
    unfold offset
    omega
  have hbranch : (combined width publicValue witness+2^(offset (width+count))*tail)%2^width =
      publicValue%2^width := by
    simp [Nat.add_mod,Nat.mul_mod,hmodOffset,combined]
  have hforce : forcePrefix width publicValue (combined width publicValue witness+2^(offset (width+count))*tail) =
      combined width publicValue witness+2^(offset (width+count))*tail := by
    unfold forcePrefix
    rw [←hbranch]
    exact Nat.mod_add_div _ _
  rw [hforce]
  exact hsplit

/-- The actual reference frame searches a fixed public field followed by an
arbitrary bounded witness, then runs the arbitrary verifier for the actual
remaining clock. The full head-relative tape is given by `inputTape`. -/
theorem reference_hardwired_search (width count n : Nat) (hn : 0 < n)
    (publicValue : Nat) (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let k := width+count
    let g := table k n hn width publicValue f
    let states := offset k+n
    let clock := tableWidth states g + (offset k+padding)
    let remaining := tableWidth states g+padding
    referenceLanguage (canonical (bits clock (finiteProgram states g))) = true ↔
      ∃ witness, witness < 2^count ∧ ∃ tail,
        finiteRun f remaining (finiteInitial hn (combined width publicValue witness) tail) = none := by
  dsimp only
  let k := width+count
  have hw : width ≤ k := by simp [k]
  let g := table k n hn width publicValue f
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
    change finiteRun (table k n hn width publicValue f) _ _ = none at haccept
    rw [loader_then_verifier k n hn width hw f publicValue] at haccept
    have hf := forced_window width count publicValue branch
    change (forcePrefix width publicValue branch)%2^k = _ at hf
    rw [hf] at haccept
    refine ⟨(branch/2^width)%2^count,Nat.mod_lt _ (Nat.pow_pos (by decide : 0 < 2)),
      branch/2^(offset k),?_⟩
    cases hr : finiteRun f (tableWidth (offset k+n) g+padding)
        (finiteInitial hn (combined width publicValue ((branch/2^width)%2^count))
          (branch/2^(offset k))) with
    | none => rfl
    | some value => simp [hr] at haccept
  · rintro ⟨witness,hwitness,tail,haccept⟩
    let branch := combined width publicValue witness+2^(offset k)*tail
    refine ⟨branch,?_⟩
    change finiteRun (table k n hn width publicValue f) _ _ = none
    rw [loader_then_verifier k n hn width hw f publicValue]
    have hsplit := choices_for_fields width count publicValue witness tail hwitness
    dsimp only at hsplit
    change (forcePrefix width publicValue branch)%2^k = combined width publicValue witness ∧
      branch/2^(offset k) = tail at hsplit
    rw [hsplit.1,hsplit.2,haccept]
    rfl

/-- The little-endian numeral of a concatenation records the public field in
the low cells and the witness immediately after it. -/
theorem value_append (xs ys : List Bool) :
    value (xs++ys) = value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp [value]
  | cons b xs ih =>
    simp only [List.cons_append,value,List.length_cons,ih,Nat.pow_succ,Nat.mul_add]
    have he : (2^xs.length*2)*value ys = 2*(2^xs.length*value ys) := by
      simp [Nat.mul_assoc,Nat.mul_comm]
    rw [he]
    omega

theorem combined_value (publicBits witness : List Bool) :
    combined publicBits.length (value publicBits) (value witness) = value (publicBits++witness) := by
  rw [value_append]
  simp [combined,Nat.mod_eq_of_lt (value_lt_pow publicBits)]

/-- A literal Boolean-list public input is hardwired into the actual verifier
tape; witness length is bounded, and verifier choice bits remain independent.
This is an exact finite reduction interface, not yet a polynomial builder. -/
theorem reference_hardwired_list_search (publicBits : List Bool) (count n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let width := publicBits.length
    let k := width+count
    let g := table k n hn width (value publicBits) f
    let states := offset k+n
    let clock := tableWidth states g + (offset k+padding)
    let remaining := tableWidth states g+padding
    referenceLanguage (canonical (bits clock (finiteProgram states g))) = true ↔
      ∃ witness : List Bool, witness.length ≤ count ∧ ∃ tail,
        finiteRun f remaining (finiteInitial hn (value (publicBits++witness)) tail) = none := by
  dsimp only
  have h := reference_hardwired_search publicBits.length count n hn (value publicBits) f padding
  dsimp only at h
  rw [h]
  constructor
  · rintro ⟨witness,hw,tail,haccept⟩
    refine ⟨bits count witness,by simp,tail,?_⟩
    rw [←combined_value,value_bits_of_lt count witness hw]
    exact haccept
  · rintro ⟨witness,hw,tail,haccept⟩
    have hp : 2^witness.length ≤ 2^count := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    refine ⟨value witness,Nat.lt_of_lt_of_le (value_lt_pow witness) hp,tail,?_⟩
    rw [combined_value]
    exact haccept

/-- Trailing blank bits are genuinely indistinguishable on this input tape;
a verifier that needs witness length must receive an explicit frame. -/
theorem trailing_blank_collision (publicBits : List Bool) :
    inputTape (value (publicBits++[true])) = inputTape (value (publicBits++[true,false])) := by
  rw [value_append,value_append]
  simp [value]

/-- The concrete hardwired reference frame is quadratic in the combined
public/witness/verifier state count, plus the selected padding. -/
theorem reference_hardwired_frame_bound (publicBits : List Bool) (count n : Nat) (hn : 0 < n)
    (f : Fin n → Bool → Bool → FiniteAction n) (padding : Nat) :
    let width := publicBits.length
    let k := width+count
    let g := table k n hn width (value publicBits) f
    let states := offset k+n
    let clock := tableWidth states g + (offset k+padding)
    (canonical (bits clock (finiteProgram states g))).length ≤
      2*((4*states)*(16*states+8)+(offset k+padding))+1 := by
  exact finite_reference_frame_bound (offset (publicBits.length+count)+n)
    (table (publicBits.length+count) n hn publicBits.length (value publicBits) f)
    (offset (publicBits.length+count)+padding)

end Shared.PNP.Record285.HardwireChoiceLoader
