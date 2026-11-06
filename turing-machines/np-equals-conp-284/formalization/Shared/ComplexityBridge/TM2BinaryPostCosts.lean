import Shared.ComplexityBridge.TM2GeneralTM0Costs
import Shared.ComplexityBridge.TM1BinaryPostCosts

/-! Polynomial TM2-to-binary-post simulation with explicit symbol codec.
The encoded initial tape and output decoding are not yet a raw-input wrapper. -/
namespace Shared.ComplexityBridge.TM2BinaryPostCosts
open Turing
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2GeneralTM1Costs
open Shared.ComplexityBridge.TM2GeneralTM0Costs

abbrev Alphabet (tm : FinTM2) := TM2to1.Γ' tm.K tm.Γ
abbrev Labels (tm : FinTM2) := TM2to1.Λ' tm.K tm.Γ tm.Λ tm.σ

variable (tm : FinTM2) (alphabet : ∀ k, Fintype (tm.Γ k))
variable {width : Nat} (enc : Alphabet tm → List.Vector Bool width)
variable (dec : List.Vector Bool width → Alphabet tm)
variable (enc0 : enc default = List.Vector.replicate width false)
variable (encdec : ∀ a, dec (enc a) = a)

include alphabet in
/-- A blank-preserving fixed-width codec exists for every finite source
alphabet. This mathematical existence is not executable reification. -/
theorem codec_exists :
    ∃ (n : Nat) (encode : Alphabet tm → List.Vector Bool n) (decode : List.Vector Bool n → Alphabet tm),
      encode default = List.Vector.replicate n false ∧ ∀ a, decode (encode a) = a := by
  letI := tm.kFin
  letI := alphabet
  exact TM1to1.exists_enc_dec

/-- Proof-side finite reachable control support for the binary post machine. -/
noncomputable def support0 : Finset (TM1to0.Λ' (TM1to1.tr enc dec (TM2to1.tr tm.m))) := by
  letI := tm.kFin
  letI := alphabet
  letI := tm.σFin
  exact TM1to0.trStmts (TM1to1.tr enc dec (TM2to1.tr tm.m))
    (TM1BinaryPostCosts.binarySupport (TM2to1.tr tm.m) (support1 tm))

theorem support0_correct :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM0.Supports (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))
      (support0 tm alphabet enc dec : Set _) := by
  letI := tm.kFin
  letI := alphabet
  letI := tm.σFin
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact TM1to0.tr_supports (TM1to1.tr enc dec (TM2to1.tr tm.m))
    (TM1BinaryPostCosts.binarySupport_correct enc dec (TM2to1.tr tm.m) (support1 tm) (support1_correct tm))

noncomputable def binaryPostLimit : Nat := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  exact TM1BinaryCosts.writeLimit (TM2to1.tr tm.m) (support1 tm) *
    TM1BinaryPostCosts.postLimit enc dec (TM2to1.tr tm.m) (support1 tm)

noncomputable def timePolynomial (p : Polynomial Nat) : Polynomial Nat :=
  simulationPolynomial tm p * Polynomial.C (binaryPostLimit tm alphabet enc dec)

/-- The initialized translated tape has an explicit finite binary input. -/
def inputBits (bits : List (tm.Γ tm.k₀)) : List Bool :=
  TM1BinaryPostCosts.encodedInput enc (TM2to1.trInit tm.k₀ bits)

set_option backward.isDefEq.respectTransparency false in
theorem inputBits_length (bits : List (tm.Γ tm.k₀)) :
    (inputBits tm enc bits).length = width * max bits.length 1 := by
  rw [inputBits,TM1BinaryPostCosts.encodedInput_length]
  congr 1
  dsimp only [TM2to1.trInit]
  simp only [List.length_cons,List.length_tail,List.length_map,List.length_reverse]
  omega

theorem initial_eq_input (bits : List (tm.Γ tm.k₀)) :
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m))
      (TM1to1.trCfg enc enc0 (translatedInitial tm bits)) = TM0.init (inputBits tm enc bits) := by
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  simp only [translatedInitial,TM1.init,TM1to1.trCfg,TM1to0.trCfg,TM0.init,inputBits]
  rw [TM1BinaryPostCosts.encodedInput_tape]
  rfl

include encdec

/-- A halted source computation reaches a binary post-Turing halt within a
polynomial number of primitive bit moves/writes, from its encoded TM1 tape. -/
theorem halt_bounded (p : Polynomial Nat) (bits : List (tm.Γ tm.k₀)) (n : Nat) (last : tm.Cfg)
    (hrun : runSteps tm.step n (Turing.initList tm bits) = some last)
    (htime : n ≤ p.eval bits.length) (hhalt : last.l = none) :
    letI := tm.kFin
    letI := alphabet
    letI : Inhabited tm.Λ := ⟨tm.main⟩
    ∃ d, n ≤ d ∧ d ≤ (timePolynomial tm alphabet enc dec p).eval bits.length ∧
      ∃ mid, TM2to1.TrCfg last mid ∧
        runSteps (TM0.step (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))) d
          (TM0.init (inputBits tm enc bits)) =
          some (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)) ∧
        TM0.step (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))
          (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)) = none := by
  letI := tm.kFin
  letI := alphabet
  letI : Inhabited tm.Λ := ⟨tm.main⟩
  obtain ⟨k,mid,hklo,hkhi,hk,hrel⟩ := TM2GeneralTM1Costs.run_from_input_polynomial tm p bits n last hrun htime
  have hs := support1_correct tm
  have hmem : (translatedInitial tm bits).l ∈ (support1 tm).insertNone := by
    change some default ∈ (support1 tm).insertNone
    exact Finset.some_mem_insertNone.2 hs.1
  obtain ⟨d,hdlo,hdhi,hd⟩ := TM1BinaryPostCosts.run_bounded enc dec enc0 encdec (TM2to1.tr tm.m)
    (support1 tm) hs k (translatedInitial tm bits) mid hmem hk
  have hmid : mid.l = none := by
    cases hrel with
    | @mk l v S L hL => cases l with | none => rfl | some q => simp at hhalt
  have hd' : runSteps (TM0.step (TM1to0.tr (TM1to1.tr enc dec (TM2to1.tr tm.m)))) d
      (TM0.init (inputBits tm enc bits)) =
      some (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr tm.m)) (TM1to1.trCfg enc enc0 mid)) := by
    rw [← initial_eq_input tm enc dec enc0 bits]
    exact hd
  refine ⟨d,by omega,?_,mid,hrel,hd',?_⟩
  · simp only [timePolynomial,Polynomial.eval_mul,Polynomial.eval_C]
    have hh := Nat.mul_le_mul_right (binaryPostLimit tm alphabet enc dec) hkhi
    have hbound : d ≤ k * binaryPostLimit tm alphabet enc dec := by
      simpa [binaryPostLimit,Nat.mul_assoc] using hdhi
    exact le_trans hbound hh
  · exact TM1BinaryPostCosts.translated_halt enc dec enc0 (TM2to1.tr tm.m) mid hmid

end Shared.ComplexityBridge.TM2BinaryPostCosts
