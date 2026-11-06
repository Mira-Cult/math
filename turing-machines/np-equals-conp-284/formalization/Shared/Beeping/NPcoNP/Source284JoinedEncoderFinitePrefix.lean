import Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2
import Shared.ComplexityBridge.TM2BinaryFinitePrefix

/-! Instantiate the quantitative continuing-prefix simulation for the actual
joined-window TM2 encoder. The resulting finite program starts on the
serialized TM2 initial tape, not the raw source tape. Its stated bound depends
on the full finite input including any suffix; a suffix-independent source
initializer and the verifier handoff are not yet established. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace Shared.Beeping.NPcoNP.Source284JoinedEncoderFinitePrefix

open Turing Shared.ComplexityBridge
open Shared.ComplexityBridge.TM2Symbols
open Shared.ComplexityBridge.TM2BinaryPostCosts
open Shared.Codes.FinitePrograms
open Shared.Beeping.NPcoNP.Source284JoinedFrames
open Shared.Beeping.NPcoNP.Source284JoinedRawEncodeTM2

def alphabet (k : machine.K) : Fintype (machine.Γ k) := by
  change Fintype Bool
  infer_instance

noncomputable def blockBound : Polynomial Nat := 2*Polynomial.X+1

/-- A single finite binary program simulates the real encoder up to its
continuing handoff. The full translated tape is retained. Its polynomial is
measured in the *whole finite input*, including the suffix. -/
theorem encoder_finite_prefix :
    letI := machine.kFin
    letI := alphabet
    letI : Inhabited machine.Λ := ⟨machine.main⟩
    ∃ (width : Nat) (enc : Alphabet machine → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet machine)
      (hblank : enc default = List.Vector.replicate width false) (program : Program) (clock : Polynomial Nat),
      (∀ a, dec (enc a) = a) ∧ valid program = true ∧
      ∀ (x w extra : List Bool),
        let bits := joinedBits x w ++ extra
        let last := cfg .done none extra [] (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
        ∃ d q tape' mid,
          2*(joinedBits x w).length+1 ≤ d ∧ d ≤ clock.eval bits.length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape tape' =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m))
              (TM1to1.trCfg enc hblank mid)).Tape ∧
          run program (initial (inputBits machine enc bits)) d = some (.inr (q,tape')) := by
  letI := machine.kFin
  letI := alphabet
  letI : Inhabited machine.Λ := ⟨machine.main⟩
  obtain ⟨width,enc,dec,hblank,hinv⟩ := TM2BinaryPostCosts.codec_exists machine alphabet
  obtain ⟨program,hvalid,hprefix⟩ := TM2BinaryFinitePrefix.finite_tm2_prefix
    machine alphabet enc dec hblank hinv blockBound
  refine ⟨width,enc,dec,hblank,program,2*timePolynomial machine alphabet enc dec blockBound,
    hinv,hvalid,?_⟩
  intro x w extra
  let bits := joinedBits x w ++ extra
  let last := cfg .done none extra [] (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
  have hr : runSteps machine.step (2*(joinedBits x w).length+1) (Turing.initList machine bits) = some last :=
    encode_joined x w extra
  have ht : 2*(joinedBits x w).length+1 ≤ blockBound.eval bits.length := by
    simp only [blockBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    dsimp [bits]
    simp only [List.length_append]
    omega
  obtain ⟨d,q,tape',mid,hdlo,hdhi,hrel,htape,hrun⟩ :=
    hprefix bits (2*(joinedBits x w).length+1) last hr ht
  exact ⟨d,q,tape',mid,hdlo,hdhi,hrel,htape,hrun⟩

/-- A translated `done` configuration has a control independent of input,
output, and unread suffix; only its translated tape varies. -/
theorem done_post_control {width : Nat} (enc : Alphabet machine → List.Vector Bool width)
    (dec : List.Vector Bool width → Alphabet machine)
    (enc0 : enc default = List.Vector.replicate width false)
    (input₁ output₁ input₂ output₂ : List Bool)
    (mid₁ mid₂ : TM1.Cfg (TM2to1.Γ' machine.K machine.Γ)
      (TM2to1.Λ' machine.K machine.Γ machine.Λ machine.σ) machine.σ)
    (h₁ : TM2to1.TrCfg (cfg .done none input₁ [] output₁) mid₁)
    (h₂ : TM2to1.TrCfg (cfg .done none input₂ [] output₂) mid₂) :
    (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m)) (TM1to1.trCfg enc enc0 mid₁)).q =
    (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m)) (TM1to1.trCfg enc enc0 mid₂)).q := by
  cases h₁ with
  | mk l₁ hl₁ =>
    cases h₂ with
    | mk l₂ hl₂ => rfl

/-- The actual encoder has one fixed finite-program handoff state for every
valid joined prefix. The program still starts on a serialized TM2 initial
tape; both its construction from raw source data and its verifier handoff
remain to be implemented. -/
theorem encoder_finite_fixed_handoff :
    letI := machine.kFin
    letI := alphabet
    letI : Inhabited machine.Λ := ⟨machine.main⟩
    ∃ (width : Nat) (enc : Alphabet machine → List.Vector Bool width)
      (dec : List.Vector Bool width → Alphabet machine)
      (hblank : enc default = List.Vector.replicate width false)
      (program : Program) (clock : Polynomial Nat) (q : Nat),
      (∀ a, dec (enc a) = a) ∧ valid program = true ∧ q < program.length ∧
      ∀ (x w extra : List Bool),
        let bits := joinedBits x w ++ extra
        let last := cfg .done none extra [] (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
        ∃ d tape' mid,
          2*(joinedBits x w).length+1 ≤ d ∧ d ≤ clock.eval bits.length ∧
          TM2to1.TrCfg last mid ∧
          TM0FiniteProgram.tape tape' =
            (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m))
              (TM1to1.trCfg enc hblank mid)).Tape ∧
          run program (initial (inputBits machine enc bits)) d = some (.inr (q,tape')) := by
  letI := machine.kFin
  letI := alphabet
  letI : Inhabited machine.Λ := ⟨machine.main⟩
  obtain ⟨width,enc,dec,hblank,hinv⟩ := TM2BinaryPostCosts.codec_exists machine alphabet
  obtain ⟨program,control,hvalid,hcontrol,hprefix⟩ := TM2BinaryFinitePrefix.finite_tm2_prefix_control
    machine alphabet enc dec hblank hinv blockBound
  let bits₀ := joinedBits [] []
  let last₀ := cfg .done none [] [] (BitstringEncoding.bitEncode (joinedBits [] [],([] : List Bool)))
  have hr₀ : runSteps machine.step (2*(joinedBits [] []).length+1) (Turing.initList machine bits₀) = some last₀ := by
    simpa [bits₀,last₀] using encode_joined [] [] []
  have ht₀ : 2*(joinedBits [] []).length+1 ≤ blockBound.eval bits₀.length := by
    simp [blockBound,bits₀]
  obtain ⟨d₀,tape₀,mid₀,_,_,hrel₀,_,_⟩ := hprefix bits₀ (2*(joinedBits [] []).length+1) last₀ hr₀ ht₀
  let q := control (TM1to0.trCfg (TM1to1.tr enc dec (TM2to1.tr machine.m)) (TM1to1.trCfg enc hblank mid₀)).q
  refine ⟨width,enc,dec,hblank,program,2*timePolynomial machine alphabet enc dec blockBound,q,
    hinv,hvalid,hcontrol _,?_⟩
  intro x w extra
  let bits := joinedBits x w ++ extra
  let last := cfg .done none extra [] (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
  have hr : runSteps machine.step (2*(joinedBits x w).length+1) (Turing.initList machine bits) = some last :=
    encode_joined x w extra
  have ht : 2*(joinedBits x w).length+1 ≤ blockBound.eval bits.length := by
    simp only [blockBound,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_X,Polynomial.eval_one]
    dsimp [bits]
    simp only [List.length_append]
    omega
  obtain ⟨d,tape',mid,hdlo,hdhi,hrel,htape,hrun⟩ :=
    hprefix bits (2*(joinedBits x w).length+1) last hr ht
  have he := done_post_control enc dec hblank extra (BitstringEncoding.bitEncode (joinedBits x w,([] : List Bool)))
    [] (BitstringEncoding.bitEncode (joinedBits [] [],([] : List Bool))) mid mid₀ hrel hrel₀
  dsimp [q]
  rw [he] at hrun
  exact ⟨d,tape',mid,hdlo,hdhi,hrel,htape,hrun⟩

end Shared.Beeping.NPcoNP.Source284JoinedEncoderFinitePrefix
