import Shared.ComplexityBridge.TM2BinaryOutputShape
import Mathlib.Data.Nat.ModEq

/-! Decode output from any finite representative of the blank-quotiented tape.
A finite-table realization and its bit-operation cost are separate obligations. -/
set_option backward.isDefEq.respectTransparency false
namespace Shared.ComplexityBridge.TM2BinaryOutputPadding
open Turing TM2to1
open Shared.ComplexityBridge.TM2BinaryOutputShape

/-- Stop at the first absent output-column entry. This is an extractor for
well-formed output, not a validator of other columns. -/
def collectUntilBlank {K : Type} {Γ : K → Type} (k : K) :
    List (Γ' K Γ) → List (Γ k)
  | [] => []
  | a::as => match a.2 k with
    | none => []
    | some b => b :: collectUntilBlank k as

def decodePaddedSymbols {K : Type} {Γ : K → Type} (k : K) :
    List (Γ' K Γ) → Option (List (Γ k))
  | [] => none
  | a::as => if a.1 then some ((collectUntilBlank k (a::as)).reverse) else none

def row {K : Type} {Γ : K → Type} [DecidableEq K] (k : K) (a : Γ k) : Γ' K Γ :=
  (false,Function.update (fun _ => none) k (some a))

theorem collectUntilBlank_rows {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (xs : List (Γ k)) (n : Nat) :
    collectUntilBlank k (xs.map (row k) ++
      List.replicate n (default : Γ' K Γ)) = xs := by
  induction xs with
  | nil => cases n <;> rfl
  | cons a xs ih => simp [collectUntilBlank,row,ih]

/-- Full blank symbol cells after the translated tape do not alter the
decoded output, including when the output is empty. -/
theorem decodePaddedSymbols_trInit {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (xs : List (Γ k)) (n : Nat) :
    decodePaddedSymbols k (trInit k xs ++ List.replicate n (default : Γ' K Γ)) = some xs := by
  cases h : xs.reverse with
  | nil =>
    have hx : xs = [] := by
      have hh := congrArg List.reverse h
      simpa using hh
    subst xs
    have hd : (default : Γ' K Γ).2 k = none := rfl
    simp [trInit,decodePaddedSymbols,collectUntilBlank,hd]
  | cons a as =>
    have hx : (a::as).reverse = xs := by rw [← h,List.reverse_reverse]
    have hrows := collectUntilBlank_rows k as n
    simp [trInit,h,decodePaddedSymbols,collectUntilBlank]
    change (collectUntilBlank k (as.map (row k) ++ List.replicate n default)).reverse ++ [a] = xs
    rw [hrows]
    simpa using hx

/-- A finite fixed-width bit parser followed by blank-cell-aware extraction. -/
def decodePaddedBits (tm : FinTM2) {width : Nat}
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (raw : List Bool) : Option (List (tm.Γ tm.k₁)) := do
  let rows ← decodeWords width dec raw.length raw
  decodePaddedSymbols tm.k₁ rows

theorem flatMap_blank_cells {A : Type} [Inhabited A] {width : Nat}
    (enc : A → List.Vector Bool width)
    (enc0 : enc default = List.Vector.replicate width false) (n : Nat) :
    (List.replicate n default).flatMap (fun a => (enc a).toList) =
      List.replicate (n*width) false := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.replicate_succ,List.flatMap_cons,ih,enc0,List.Vector.replicate,
      List.Vector.toList_mk,Nat.succ_mul]
    simpa [Nat.add_comm] using (List.replicate_add width (n*width) false).symm

/-- Any number of complete all-zero cells can be appended to the serialized
output without changing its decoded value. -/
theorem decodePaddedBits_output (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁)) (n : Nat) :
    decodePaddedBits tm dec (outputBits tm enc bits ++ List.replicate (n*width) false) = some bits := by
  letI := tm.kDecidableEq
  let rows := trInit tm.k₁ bits ++ List.replicate n (default : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
  let raw := outputBits tm enc bits ++ List.replicate (n*width) false
  have hwidth := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  have hraw : rows.flatMap (fun a => (enc a).toList) = raw := by
    simp [rows,raw,outputBits,Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput,
      flatMap_blank_cells enc enc0 n]
  have hlen : rows.length ≤ raw.length := by
    have hw : (rows.flatMap (fun a => (enc a).toList)).length = width*rows.length := by
      simpa [Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput] using
        Shared.ComplexityBridge.TM1BinaryPostCosts.encodedInput_length enc rows
    rw [hraw] at hw
    have hm := Nat.mul_le_mul_right rows.length hwidth
    omega
  have hwords := decodeWords_encoded enc dec hwidth hdec rows raw.length hlen
  rw [hraw] at hwords
  change decodePaddedBits tm dec raw = _
  unfold decodePaddedBits
  rw [hwords]
  exact decodePaddedSymbols_trInit tm.k₁ bits n

/-- Append at most one cell of zeros to reach a code-cell boundary. -/
def align (width : Nat) (raw : List Bool) : List Bool :=
  raw ++ List.replicate ((width - raw.length % width) % width) false

theorem align_padding_multiple (width n : Nat) (hwidth : 0 < width) :
    width ∣ n + ((width - n % width) % width) := by
  apply Nat.dvd_of_mod_eq_zero
  have hr : n % width < width := Nat.mod_lt _ hwidth
  by_cases hz : n % width = 0
  · simp [Nat.add_mod,hz]
  · have hsub : 0 < width - n % width := by omega
    have hlt : width - n % width < width := by omega
    rw [Nat.mod_eq_of_lt hlt,Nat.add_mod,Nat.mod_eq_of_lt hlt]
    have he : n % width + (width - n % width) = width := by omega
    rw [he,Nat.mod_self]

/-- Padding to the next boundary permits any finite blank extension of the
entire serialized output, including a partial extra cell. -/
theorem aligned_decode_extension (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁)) (n : Nat) :
    decodePaddedBits tm dec (align width (outputBits tm enc bits ++ List.replicate n false)) = some bits := by
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  let m := (outputBits tm enc bits ++ List.replicate n false).length
  have hm : width ∣ m + ((width - m % width) % width) := align_padding_multiple width m hw
  have ho : width ∣ (outputBits tm enc bits).length := by
    rw [outputBits_length]
    exact dvd_mul_right _ _
  have heq : m = (outputBits tm enc bits).length + n := by simp [m]
  rw [heq] at hm
  have hp : width ∣ n + ((width - m % width) % width) := by
    apply (Nat.dvd_add_iff_left ho).mpr
    simpa [heq,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hm
  obtain ⟨q,hq⟩ := hp
  have hraw : align width (outputBits tm enc bits ++ List.replicate n false) =
      outputBits tm enc bits ++ List.replicate (q*width) false := by
    unfold align
    change (outputBits tm enc bits ++ List.replicate n false) ++
      List.replicate ((width - m % width) % width) false = _
    rw [List.append_assoc,← List.replicate_add]
    congr 2
    simpa [Nat.mul_comm] using hq
  rw [hraw]
  exact decodePaddedBits_output tm enc dec enc0 hdec bits q

/-- Every cell of a canonical translated stack is nonblank: the first has
the bottom marker and every subsequent cell contains an output symbol. -/
theorem trInit_cells_nonblank {K : Type} {Γ : K → Type} [DecidableEq K]
    (k : K) (xs : List (Γ k)) (a : Γ' K Γ) (ha : a ∈ trInit k xs) : a ≠ default := by
  cases h : xs.reverse with
  | nil =>
    simp [trInit,h] at ha
    subst a
    intro he
    have hh := congrArg (fun x : Γ' K Γ => x.1) he
    change true = false at hh
    contradiction
  | cons b bs =>
    simp only [trInit,h,List.map_cons,List.headI_cons,List.tail_cons,List.mem_cons] at ha
    rcases ha with ha | ha
    · subst a
      intro he
      have hh := congrArg (fun x : Γ' K Γ => x.1) he
      change true = false at hh
      contradiction
    · obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
      intro he
      have hh := congrArg (fun a : Γ' K Γ => a.2 k) he
      simp at hh

/-- The exact output serialization cannot end in a whole blank code cell.
This prevents losing an entire output symbol in the blank quotient. -/
theorem outputBits_no_blank_cell_suffix (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁)) :
    ¬ ∃ before, outputBits tm enc bits = before ++ List.replicate width false := by
  letI := tm.kDecidableEq
  let rows := trInit tm.k₁ bits
  have hne : rows ≠ [] := by simp [rows,trInit]
  cases hrev : rows.reverse with
  | nil =>
    have he := congrArg List.reverse hrev
    have : rows = [] := by simpa using he
    exact False.elim (hne this)
  | cons last revFront =>
    have hrows : rows = revFront.reverse ++ [last] := by
      have he := congrArg List.reverse hrev
      simpa using he
    have hmem : last ∈ trInit tm.k₁ bits := by
      change last ∈ rows
      rw [hrows]
      simp
    have hnon := trInit_cells_nonblank tm.k₁ bits last hmem
    rintro ⟨before,hout⟩
    let front := revFront.reverse.flatMap (fun a => (enc a).toList)
    have heq : front ++ (enc last).toList = before ++ List.replicate width false := by
      change rows.flatMap (fun a => (enc a).toList) = _ at hout
      rw [hrows,List.flatMap_append] at hout
      simpa [front] using hout
    have hlen : front.length = before.length := by
      have hh := congrArg List.length heq
      simp only [List.length_append,List.Vector.toList_length,List.length_replicate] at hh
      omega
    have hlast := (List.append_inj heq hlen).2
    have hv : enc last = enc default := by
      apply List.Vector.toList_injective
      rw [enc0]
      simpa [List.Vector.replicate] using hlast
    have he := congrArg dec hv
    rw [hdec last,hdec default] at he
    exact hnon he

/-- If a representative omits trailing blanks from the final cell, aligning
it restores the original serialization exactly. -/
theorem align_short_representation (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁))
    (raw : List Bool) (n : Nat) (hout : outputBits tm enc bits = raw ++ List.replicate n false) :
    align width raw = outputBits tm enc bits := by
  have hw := Shared.ComplexityBridge.TM2BinaryFiniteProgram.width_positive tm enc dec hdec
  have hn : n < width := by
    by_contra h
    have hle : width ≤ n := by omega
    have he : outputBits tm enc bits =
        (raw ++ List.replicate (n-width) false) ++ List.replicate width false := by
      rw [List.append_assoc,← List.replicate_add,Nat.sub_add_cancel hle]
      exact hout
    exact outputBits_no_blank_cell_suffix tm enc dec enc0 hdec bits ⟨_,he⟩
  let pad := (width - raw.length % width) % width
  have hpad : pad < width := Nat.mod_lt _ hw
  have hdiv : width ∣ raw.length+n := by
    have h := outputBits_length tm enc bits
    rw [hout] at h
    simp only [List.length_append,List.length_replicate] at h
    rw [h]
    exact dvd_mul_right _ _
  have hdiv' : width ∣ raw.length+pad := align_padding_multiple width raw.length hw
  have hmod : Nat.ModEq width (raw.length+n) (raw.length+pad) := by
    unfold Nat.ModEq
    rw [Nat.mod_eq_zero_of_dvd hdiv,Nat.mod_eq_zero_of_dvd hdiv']
  have heq := Nat.ModEq.add_left_cancel' raw.length hmod
  unfold Nat.ModEq at heq
  rw [Nat.mod_eq_of_lt hn,Nat.mod_eq_of_lt hpad] at heq
  unfold align
  change raw ++ List.replicate pad false = _
  rw [← heq,← hout]

/-- Alignment and padded decoding are invariant under the full blank-tape
equivalence, including representatives truncated within the last code cell. -/
theorem aligned_decode_blankRel (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁))
    (raw : List Bool) (h : BlankRel raw (outputBits tm enc bits)) :
    decodePaddedBits tm dec (align width raw) = some bits := by
  rcases h with ⟨n,hn⟩ | ⟨n,hn⟩
  · change outputBits tm enc bits = raw ++ List.replicate n false at hn
    rw [align_short_representation tm enc dec enc0 hdec bits raw n hn]
    simpa using decodePaddedBits_output tm enc dec enc0 hdec bits 0
  · change raw = outputBits tm enc bits ++ List.replicate n false at hn
    rw [hn]
    exact aligned_decode_extension tm enc dec enc0 hdec bits n

/-- Read the finite list representation already carried by a binary table's
tape. The quotient relation supplies all missing or extra trailing blanks. -/
theorem actualTape_decodes (tm : FinTM2) {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet tm)
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) (bits : List (tm.Γ tm.k₁))
    (t : Shared.Codes.FinitePrograms.Tape)
    (htape : Shared.ComplexityBridge.TM0FiniteProgram.tape t = Tape.mk₁ (outputBits tm enc bits)) :
    decodePaddedBits tm dec (align width (t.2.1::t.2.2)) = some bits := by
  have hq : ListBlank.mk (t.2.1::t.2.2) = ListBlank.mk (outputBits tm enc bits) := by
    have hleft : (Shared.ComplexityBridge.TM0FiniteProgram.tape t).right₀ =
        ListBlank.mk (t.2.1::t.2.2) := by
      simp [Shared.ComplexityBridge.TM0FiniteProgram.tape,Tape.right₀,ListBlank.cons_mk]
    have hright : (Tape.mk₁ (outputBits tm enc bits)).right₀ = ListBlank.mk (outputBits tm enc bits) := by
      simp only [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀]
    exact hleft.symm.trans ((congrArg Tape.right₀ htape).trans hright)
  have hrel : BlankRel (t.2.1::t.2.2) (outputBits tm enc bits) := Quotient.exact hq
  exact aligned_decode_blankRel tm enc dec enc0 hdec bits (t.2.1::t.2.2) hrel

/-- Every successful checked evaluation is reproduced by a single binary
table whose final represented tape is decoded by the functional extractor. -/
theorem successful_run_decodes (c : Shared.Codes.TM2Candidate.Candidate)
    (p : Shared.Codes.TM2Program.Program) (hdecode : Shared.Codes.TM2Program.decodeProgram c.1.1 = some p)
    {width : Nat}
    (enc : Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      (Shared.ComplexityBridge.TM2BitstringBinary.whole c p) → List.Vector Bool width)
    (dec : List.Vector Bool width → Shared.ComplexityBridge.TM2BinaryPostCosts.Alphabet
      (Shared.ComplexityBridge.TM2BitstringBinary.whole c p))
    (enc0 : enc default = List.Vector.replicate width false)
    (hdec : ∀ a, dec (enc a) = a) :
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
          decodePaddedBits tm dec (align width (t.2.1::t.2.2)) = some output := by
  obtain ⟨program,hvalid,hprogram⟩ := successful_output_tape c p hdecode enc dec enc0 hdec
  refine ⟨program,hvalid,?_⟩
  intro bits output heval
  obtain ⟨d,hd,q,t,hr,ht,_⟩ := hprogram bits output heval
  exact ⟨d,hd,q,t,hr,actualTape_decodes _ enc dec enc0 hdec output t ht⟩

end Shared.ComplexityBridge.TM2BinaryOutputPadding
