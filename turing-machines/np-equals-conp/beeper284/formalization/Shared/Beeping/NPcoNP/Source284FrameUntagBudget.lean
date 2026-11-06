import Shared.Beeping.NPcoNP.Source284ClearFrameUntagWindow
import Shared.Beeping.NPcoNP.Source284PaddingBudget

/-! A polynomial scratch budget including the paid frame-to-untagger link and
the reflected untagger. The limit remains supplied in unary by the caller. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284FrameUntagBudget

open Shared.Codes.FiniteProgramTaggedLoop (totalCost)
open Shared.Beeping.NPcoNP.Source284DecodedTaggedPipeline (Codec)
open Shared.Beeping.NPcoNP.Source284EncoderFirstSelection (code)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)
open Shared.Beeping.NPcoNP.Source284PaddingBudget (maxBody runtimeBudget)

def outputWords {width : Nat} (enc : Codec width) (remaining : List Bool) : List Bool :=
  marker enc ++ (processed remaining false).flatMap (code enc)

def clock {width : Nat} (enc : Codec width) (remaining : List Bool) : Nat :=
  totalCost (code enc false) (code enc true) remaining false (marker enc)+2+
    (Shared.Codes.FiniteProgramFrameLoop.totalCost width (items enc remaining)+2+
      (2+Shared.Codes.FiniteProgramUntag.cost (outputWords enc remaining).reverse))

def rawLength (width body : Nat) : Nat := width*(body+1)

def runtimeBound (width body : Nat) : Nat :=
  runtimeBudget width body+2+(rawLength width body*(20*rawLength width body+21)+6)

def paddedLimit (width n original outputRadius : Nat) : Nat :=
  original+outputRadius+runtimeBound width (maxBody n original)+(3*width+2)

theorem code_flatMap_length {width : Nat} (enc : Codec width) (bits : List Bool) :
    (bits.flatMap (code enc)).length = bits.length*width := by
  induction bits with
  | nil => simp
  | cons b bs ih =>
    simp [ih,Source284TaggedCyclesSource.code_length,Nat.succ_mul,Nat.add_comm]

theorem outputWords_length {width : Nat} (enc : Codec width) (remaining : List Bool) :
    (outputWords enc remaining).length = rawLength width remaining.length := by
  unfold outputWords rawLength
  rw [List.length_append,Source284EncoderMarkerSeed.marker_length,code_flatMap_length,
    Source284SerializerStripWindow.processed_length]
  simp [Nat.mul_add,Nat.mul_comm,Nat.add_comm]

theorem runtimeBound_mono (width : Nat) {a b : Nat} (h : a ≤ b) :
    runtimeBound width a ≤ runtimeBound width b := by
  unfold runtimeBound rawLength
  gcongr
  exact Source284PaddingBudget.runtimeBudget_mono width h

theorem clock_bound_exact {width : Nat} (enc : Codec width) (remaining : List Bool) :
    clock enc remaining ≤ runtimeBound width remaining.length := by
  have hs := Source284SerializerStripWindow.combined_cost_bound enc remaining
  have hu := Shared.Codes.FiniteProgramMirror.positioned_cost_bound (outputWords enc remaining)
  rw [outputWords_length] at hu
  dsimp [clock,runtimeBound,runtimeBudget] at *
  omega

theorem clock_bound {width : Nat} (enc : Codec width) (x w rest : List Bool) (original : Nat)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hw : w.length ≤ original) :
    clock enc (rest++[true]) ≤ runtimeBound width (maxBody x.length original) := by
  have hlen : (Source284JoinedPrefixScan.joinedBody x w).length = 2*x.length+2*w.length+5 := by
    have h := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body x w)
    simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at h
    omega
  have hr := congrArg List.length hbody
  simp only [List.length_reverse,List.length_cons] at hr
  have hm : (rest++[true]).length ≤ maxBody x.length original := by
    simp only [List.length_append,List.length_singleton,maxBody]
    omega
  exact le_trans (clock_bound_exact enc _) (runtimeBound_mono width hm)

theorem padding_sufficient {width : Nat} (enc : Codec width) (x w rest : List Bool)
    (original k : Nat) (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hw : w.length ≤ original) :
    k+clock enc (rest++[true])+(Source284TaggedMarkerSeed.word enc).length+1 ≤
      2*((paddedLimit width x.length original k+1)+1) := by
  have hc := clock_bound enc x w rest original hbody hw
  have hl := Source284TaggedMarkerSeed.word_length enc
  dsimp [paddedLimit] at *
  omega

/-- An explicit polynomial exists whenever the old bound and output radius
are polynomials in the input length. -/
noncomputable def paddedPolynomial (width : Nat) (original outputRadius : Polynomial Nat) : Polynomial Nat :=
  let body := 2*Polynomial.X+2*original+5
  let out := Polynomial.C width*(body+1)
  Source284PaddingBudget.paddedPolynomial width original outputRadius + 2 + (out*(20*out+21)+6)

theorem paddedPolynomial_eval (width n : Nat) (original outputRadius : Polynomial Nat) :
    (paddedPolynomial width original outputRadius).eval n =
      paddedLimit width n (original.eval n) (outputRadius.eval n) := by
  simp [paddedPolynomial,paddedLimit,runtimeBound,rawLength,maxBody,
    Source284PaddingBudget.paddedPolynomial_eval,Source284PaddingBudget.paddedLimit,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X]
  ring

end Shared.Beeping.NPcoNP.Source284FrameUntagBudget
