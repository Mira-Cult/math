import Shared.ComplexityBridge.TM2BitstringBinary

/-! Identify the translated final tape exactly. The output extractor is still
to be implemented as a finite binary machine. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryOutputShape
open Turing TM2to1

/-- Related TM1 tapes are uniquely determined by the source stack contents,
even when the source control labels or internal states differ. -/
theorem related_tape_unique {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K] (a b : TM2.Cfg Γ Λ σ)
    (x y : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (ha : TrCfg a x) (hb : TrCfg b y) (hs : a.stk = b.stk) : x.Tape = y.Tape := by
  cases ha with
  | mk L hL =>
    cases hb with
    | mk L' hL' =>
      dsimp only at hs
      rw [← hs] at hL'
      have he : L = L' := by
        apply ListBlank.ext
        intro n
        funext k
        have h := congrArg (fun z => z.nth n) ((hL k).trans (hL' k).symm)
        simpa only [ListBlank.nth_map,proj,PointedMap.mk_val] using h
      rw [he]

/-- When all other stacks are cleared, the simulator tape has the canonical
list representation of the output stack, including the empty output case. -/
theorem halt_tape (tm : FinTM2) (bits : List (tm.Γ tm.k₁))
    (mid : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (hrel : TrCfg (Turing.haltList tm bits) mid) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    mid.Tape = Tape.mk₁ (trInit tm.k₁ bits) := by
  letI := tm.kDecidableEq
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  have hinit := trCfg_init (Λ := tm.Λ) (σ := tm.σ) tm.k₁ bits
  have hs : (Turing.haltList tm bits).stk = (TM2.init tm.k₁ bits : tm.Cfg).stk := by
    funext k
    by_cases hk : k = tm.k₁
    · subst k; simp [Turing.haltList,TM2.init]
    · simp [Turing.haltList,TM2.init,Function.update_of_ne hk,hk]
  have h := related_tape_unique _ _ _ _ hrel hinit hs
  exact h

/-- The finite, fixed-width serialization of the entire output-stack tape.
The marker ensures that even an empty output occupies one encoded cell. -/
def outputBits (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (bits : List (tm.Γ tm.k₁)) : List Bool :=
  Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput enc (trInit tm.k₁ bits)

theorem outputBits_length (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (bits : List (tm.Γ tm.k₁)) :
    (outputBits tm enc bits).length = width * max bits.length 1 := by
  rw [outputBits,Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput_length]
  congr 1
  dsimp only [trInit]
  simp only [List.length_cons,List.length_tail,List.length_map,List.length_reverse]
  omega

/-- Decode the selected stack column of a finite sequence of translated
symbols. Missing cells fail instead of being interpreted as data. -/
def collectColumn {K : Type} {Γ : K → Type} (k : K) :
    List (Γ' K Γ) → Option (List (Γ k))
  | [] => some []
  | a::as => do
    let b ← a.2 k
    let bs ← collectColumn k as
    some (b::bs)

/-- Decode a canonical translated stack serialization. Its first marker is
mandatory, and the empty stack has one marker-only cell. This extractor does
not validate other stack columns or later marker flags. -/
def decodeSymbols {K : Type} {Γ : K → Type} (k : K) :
    List (Γ' K Γ) → Option (List (Γ k))
  | [] => none
  | a::as =>
    if a.1 then
      match a.2 k with
      | none => if as.isEmpty then some [] else none
      | some b => (collectColumn k as).map (fun bs => (b::bs).reverse)
    else none

theorem collectColumn_rows {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (xs : List (Γ k)) :
    collectColumn k (xs.map (fun a => (false,Function.update (fun _ => none) k (some a)))) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [collectColumn,ih]

/-- Decoding is exact, including empty strings and false bits. -/
theorem decodeSymbols_trInit {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (xs : List (Γ k)) : decodeSymbols k (trInit k xs) = some xs := by
  cases h : xs.reverse with
  | nil =>
    have hx : xs = [] := by
      have hh := congrArg List.reverse h
      simpa using hh
    subst xs
    have hd : (default : Γ' K Γ).2 k = none := rfl
    simp [trInit,decodeSymbols,hd]
  | cons a as =>
    have hx : (a::as).reverse = xs := by rw [← h,List.reverse_reverse]
    simp [trInit,h,decodeSymbols,collectColumn_rows]
    simpa using hx

/-- Executable bounded parser for fixed-width words. The fuel is explicit;
short trailing words and unconsumed input fail. -/
def decodeWords {A : Type} (width : Nat) (dec : List.Vector Bool width → A) :
    Nat → List Bool → Option (List A)
  | 0, bits => if bits.isEmpty then some [] else none
  | fuel+1, bits =>
    if bits.isEmpty then some []
    else if h : (bits.take width).length = width then do
      let rest ← decodeWords width dec fuel (bits.drop width)
      some (dec ⟨bits.take width,h⟩ :: rest)
    else none

theorem decodeWords_encoded {A : Type} {width : Nat} (enc : A → List.Vector Bool width)
    (dec : List.Vector Bool width → A) (hwidth : 0 < width)
    (hdec : ∀ a, dec (enc a) = a) (xs : List A) (fuel : Nat) (hfuel : xs.length ≤ fuel) :
    decodeWords width dec fuel (xs.flatMap (fun a => (enc a).toList)) = some xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons a xs ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      have hf : xs.length ≤ fuel := by simp at hfuel; omega
      have hw : (enc a).toList.length = width := List.Vector.toList_length _
      have hn : (enc a).toList ≠ [] := by
        intro he
        rw [he] at hw
        simp at hw
        omega
      have ht : ((enc a).toList ++ xs.flatMap (fun a => (enc a).toList)).take width = (enc a).toList := by
        simp [List.take_append,hw]
      have hd : ((enc a).toList ++ xs.flatMap (fun a => (enc a).toList)).drop width =
          xs.flatMap (fun a => (enc a).toList) := by
        simp [List.drop_append,hw]
      have hv : (⟨(enc a).toList,hw⟩ : List.Vector Bool width) = enc a := by
        apply Subtype.ext
        rfl
      have hempty : ((enc a).toList ++ xs.flatMap (fun a => (enc a).toList)).isEmpty = false := by
        cases hword : (enc a).toList with
        | nil => exact False.elim (hn hword)
        | cons b bs => rfl
      simp only [List.flatMap_cons,decodeWords]
      simp only [hempty,Bool.false_eq_true,if_false]
      simp only [ht,hw,↓reduceDIte,hd,ih fuel hf,hv,hdec]
      rfl

/-- Parse a fixed-width binary serialization and then recover its selected
output stack. Fuel is bounded by the serialized input length. -/
def decodeOutputBits (tm : FinTM2) {width : Nat}
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (raw : List Bool) : Option (List (tm.Γ tm.k₁)) := do
  let rows ← decodeWords width dec raw.length raw
  decodeSymbols tm.k₁ rows

/-- The executable parser recovers every output bit, including trailing false
bits and the empty output. -/
theorem decodeOutputBits_outputBits (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (hwidth : 0 < width) (hdec : ∀ a, dec (enc a) = a)
    (bits : List (tm.Γ tm.k₁)) :
    decodeOutputBits tm dec (outputBits tm enc bits) = some bits := by
  let rows := trInit tm.k₁ bits
  have hlen : rows.length ≤ (outputBits tm enc bits).length := by
    have h := Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput_length enc rows
    change (outputBits tm enc bits).length = width * rows.length at h
    have hm := Nat.mul_le_mul_right rows.length hwidth
    omega
  have hwords := decodeWords_encoded enc dec hwidth hdec rows (outputBits tm enc bits).length hlen
  change decodeWords width dec (outputBits tm enc bits).length (outputBits tm enc bits) = some rows at hwords
  unfold decodeOutputBits
  rw [hwords]
  change decodeSymbols tm.k₁ (trInit tm.k₁ bits) = some bits
  letI := tm.kDecidableEq
  exact decodeSymbols_trInit tm.k₁ bits

/-- A left inverse for this alphabet codec already forces positive width. -/
theorem codec_decodes_output (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁)) :
    decodeOutputBits tm dec (outputBits tm enc bits) = some bits :=
  decodeOutputBits_outputBits tm enc dec
    (Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec) hdec bits


/-- The abstract related tape has a concrete binary serialization. -/
theorem halt_binary_tape (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (enc0 : enc default = List.Vector.replicate width false)
    (bits : List (tm.Γ tm.k₁))
    (mid : TM1.Cfg (Γ' tm.K tm.Γ) (Λ' tm.K tm.Γ tm.Λ tm.σ) tm.σ)
    (hrel : TrCfg (Turing.haltList tm bits) mid) :
    TM1to1.trTape enc0 mid.Tape = Tape.mk₁ (outputBits tm enc bits) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  rw [halt_tape tm bits mid hrel]
  exact Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput_tape enc enc0 (trInit tm.k₁ bits)

/-- A successful checked candidate reaches this exact finite serialized tape
in the same charged polynomial time as the full-tape simulation. -/
theorem successful_output_tape (c : Shared.Codes.TM2Candidate.Candidate)
    (p : Shared.Codes.TM2Program.Program) (hdecode : Shared.Codes.TM2Program.decodeProgram c.1.1 = some p)
    {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      (Shared.ComplexityBridge.TM2BitstringBinary.whole c p) → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      (Shared.ComplexityBridge.TM2BitstringBinary.whole c p))
    (enc0 : enc default = List.Vector.replicate width false)
    (encdec : ∀ a, dec (enc a) = a) :
    let tm := Shared.ComplexityBridge.TM2BitstringBinary.whole c p
    let alphabet := Shared.ComplexityBridge.TM2BitstringBinary.finiteAlphabet c p
    let clock := Shared.ComplexityBridge.TM2BitstringPoly.timePolynomial
      (Shared.ComplexityBridge.TM2FiniteBoundary.inputDataOfRaw c.1.2.2).stackCount c.1.2.1 p
    let cost := 2*Shared.ComplexityBridge.TM2BinaryPostCosts.timePolynomial tm alphabet enc dec clock
    ∃ program : Shared.Codes.FinitePrograms.Program, Shared.Codes.FinitePrograms.valid program = true ∧
      ∀ bits output, Shared.ComplexityBridge.TM2BitstringOutput.Evaluator.evaluate c bits = some output →
        ∃ d ≤ cost.eval bits.length, ∃ q t,
          Shared.Codes.FinitePrograms.run program
            (Shared.Codes.FinitePrograms.initial (Shared.ComplexityBridge.TM2BinaryPostCosts.inputBits tm enc bits)) d =
              some (.inr (q,t)) ∧
          Shared.ComplexityBridge.TM0FiniteProgram.tape t = Tape.mk₁ (outputBits tm enc output) ∧
          Shared.Codes.FinitePrograms.step program (q,t) = some (.inl (Tape.mk₁ (outputBits tm enc output)).head) := by
  obtain ⟨program,hvalid,hprogram⟩ :=
    Shared.ComplexityBridge.TM2BitstringBinary.successful_full_tape c p hdecode enc dec enc0 encdec
  refine ⟨program,hvalid,?_⟩
  intro bits output heval
  obtain ⟨d,hd,mid,q,t,hrel,hr,ht,hs⟩ := hprogram bits output heval
  have hshape := halt_binary_tape (Shared.ComplexityBridge.TM2BitstringBinary.whole c p) enc enc0 output mid hrel
  rw [hshape] at ht hs
  exact ⟨d,hd,q,t,hr,ht,hs⟩

end Shared.ComplexityBridge.TM2BinaryOutputShape
