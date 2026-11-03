import Shared.ComplexityBridge.TM2BinaryFiniteProgram

/-! A leading-bit output tag for a fixed-width alphabet codec. The tag can
encode the Boolean value in the output stack cell at the halted TM2 boundary. -/
namespace Shared.ComplexityBridge.TM2BooleanTag
open Turing
open Shared.ComplexityBridge.TM2BinaryPostCosts

variable (tm : FinTM2) [DecidableEq (tm.Γ tm.k₁)] (yes : tm.Γ tm.k₁)
variable {n : Nat} (enc : Alphabet tm → List.Vector Bool n) (dec : List.Vector Bool n → Alphabet tm)

def tag (a : Alphabet tm) : Bool := decide (a.2 tm.k₁ = some yes)
def taggedEncode (a : Alphabet tm) : List.Vector Bool (n+1) := tag tm yes a ::ᵥ enc a
def taggedDecode (v : List.Vector Bool (n+1)) : Alphabet tm := dec v.tail

theorem tagged_roundtrip (h : ∀ a, dec (enc a) = a) (a : Alphabet tm) :
    taggedDecode tm dec (taggedEncode tm yes enc a) = a := by
  simp [taggedDecode,taggedEncode,h]

theorem tagged_blank (h : enc default = List.Vector.replicate n false) :
    taggedEncode tm yes enc default = List.Vector.replicate (n+1) false := by
  simp [taggedEncode,tag,h,List.Vector.replicate_succ]

/-- The first bit of the encoded current symbol equals its output tag. -/
theorem tagged_tape_head (h : taggedEncode tm yes enc default = List.Vector.replicate (n+1) false)
    (T : Tape (Alphabet tm)) :
    (TM1to1.trTape h T).head = tag tm yes T.head := by
  have he : T.right₀ = (T.right₀.tail).cons T.right₀.head := (ListBlank.cons_head_tail _).symm
  unfold TM1to1.trTape
  rw [he]
  simp [TM1to1.trTape',ListBlank.cons_flatMap,taggedEncode,Tape.right₀]

set_option backward.isDefEq.respectTransparency false in
/-- A translated halted configuration exposes the designated stack's
single output symbol in the bottom-marker tape cell. -/
theorem related_output_tag (last : tm.Cfg) (mid : TM1.Cfg (Alphabet tm) (Labels tm) tm.σ)
    (hrel : TM2to1.TrCfg last mid) (s : tm.Γ tm.k₁)
    (hout : last.stk tm.k₁ = [s]) :
    tag tm yes mid.Tape.head = decide (s = yes) := by
  cases hrel with
  | @mk l v S L hL =>
    change S tm.k₁ = [s] at hout
    have hcol := hL tm.k₁
    have hh := congrArg ListBlank.head hcol
    have hval : L.head tm.k₁ = some s := by
      simpa [proj,ListBlank.head_map,ListBlank.head_mk,hout] using hh
    change decide ((TM2to1.addBottom L).head.2 tm.k₁ = some yes) = decide (s = yes)
    rw [TM2to1.addBottom,ListBlank.head_cons]
    simp [hval]

/-- For Boolean machines that halt with one of two distinct symbols on the
output stack, one fixed finite candidate returns the Boolean result on the
serialized initial tape. Codec and candidate are chosen once for all inputs. -/
theorem boolean_candidate (alphabet : ∀ k, Fintype (tm.Γ k)) (no : tm.Γ tm.k₁)
    (hne : no ≠ yes) (p : Polynomial Nat) :
    ∃ (width : Nat) (encode : Alphabet tm → List.Vector Bool width)
      (decode : List.Vector Bool width → Alphabet tm),
      encode default = List.Vector.replicate width false ∧
      (∀ a, decode (encode a) = a) ∧
      ∃ candidate : Shared.Codes.FinitePrograms.Candidate,
        Shared.Codes.FinitePrograms.valid candidate.2 = true ∧
        (∃ e, Shared.Codes.FinitePrograms.decode e = some candidate) ∧
        ∀ (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg) (b : Bool),
          Shared.ComplexityBridge.TM2Symbols.runSteps tm.step n (Turing.initList tm bits) = some last →
          n ≤ p.eval bits.length → last.l = none →
          last.stk tm.k₁ = [if b then yes else no] →
          Shared.Codes.FinitePrograms.evaluate candidate (inputBits tm encode bits) = some b := by
  obtain ⟨w,baseEnc,baseDec,hblank,hinv⟩ := codec_exists tm alphabet
  let encode := taggedEncode tm yes baseEnc
  let decode := taggedDecode tm baseDec
  have he0 : encode default = List.Vector.replicate (w+1) false := tagged_blank tm yes baseEnc hblank
  have heinv : ∀ a, decode (encode a) = a := tagged_roundtrip tm yes baseEnc baseDec hinv
  obtain ⟨candidate,hvalid,hcode,hcandidate⟩ :=
    TM2BinaryFiniteProgram.fixed_exponent_candidate tm alphabet encode decode he0 heinv p
  refine ⟨w+1,encode,decode,he0,heinv,candidate,hvalid,hcode,?_⟩
  intro bits n last b hrun htime hhalt hout
  obtain ⟨mid,hrel,hresult⟩ := hcandidate bits n last hrun htime hhalt
  have htape := tagged_tape_head tm yes baseEnc he0 mid.Tape
  have htag := related_output_tag tm yes last mid hrel (if b then yes else no) hout
  change Shared.Codes.FinitePrograms.evaluate candidate (inputBits tm encode bits) =
    some ((TM1to1.trTape he0 mid.Tape).head) at hresult
  rw [htape,htag] at hresult
  cases b <;> simp [hne,Ne.symm hne] at hresult ⊢ <;> exact hresult

end Shared.ComplexityBridge.TM2BooleanTag
