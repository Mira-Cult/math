import Shared.Beeping.NPcoNP.Source284CanonicalTaggedPipeline

/-! Enlarge the prepared witness limit enough to cover the serializer's
conservative tape window, while retaining the original witness cutoff in an
explicit Boolean guard. This proves arithmetic and exhaustive-search facts;
a finite source implementation of the guard and enlarged unary limit remains
an obligation. -/
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
namespace Shared.Beeping.NPcoNP.Source284PaddingBudget

open Shared.Beeping.NPcoNP.Source284DecodedTaggedPipeline
open Shared.Beeping.NPcoNP.Source284EncoderFirstSelection (code)
open Shared.Beeping.NPcoNP.Source284EncoderMarkerSeed (marker)
open Shared.Beeping.NPcoNP.Source284SerializerStrip (items)
open Shared.Beeping.NPcoNP.Source284TaggedCyclesSource (processed)

/-- A uniform count of source bits for input length `n` and original
witness bound `m`. -/
def maxBody (n m : Nat) : Nat := 2*n+2*m+5

/-- Explicit upper bound on the serializer, exit and strip steps. -/
def runtimeBudget (width body : Nat) : Nat :=
  body*(16*(width+body*(1+width))+16*width+31) + 2 +
    (body+1)*(7*width+30*((body+1)*(width+1))+26)

theorem runtimeBudget_mono (width : Nat) {a b : Nat} (h : a ≤ b) :
    runtimeBudget width a ≤ runtimeBudget width b := by
  unfold runtimeBudget
  gcongr

def paddedLimit (width n original outputRadius : Nat) : Nat :=
  original+outputRadius+runtimeBudget width (maxBody n original)+(3*width+2)

theorem original_le_padded (width n original outputRadius : Nat) :
    original ≤ paddedLimit width n original outputRadius := by simp [paddedLimit]; omega

/-- If the original cutoff and desired output radius are polynomial in the
input length, the enlarged limit is represented by this explicit polynomial. -/
noncomputable def paddedPolynomial (width : Nat) (original outputRadius : Polynomial Nat) : Polynomial Nat :=
  let body := 2*Polynomial.X+2*original+5
  original+outputRadius+
    (body*(16*(Polynomial.C width+body*(1+Polynomial.C width))+16*Polynomial.C width+31)+2+
      (body+1)*(7*Polynomial.C width+30*((body+1)*(Polynomial.C width+1))+26))+
    Polynomial.C (3*width+2)

theorem paddedPolynomial_eval (width n : Nat) (original outputRadius : Polynomial Nat) :
    (paddedPolynomial width original outputRadius).eval n =
      paddedLimit width n (original.eval n) (outputRadius.eval n) := by
  simp [paddedPolynomial,paddedLimit,runtimeBudget,maxBody,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X]

/-- Every body within the old cutoff fits the uniform runtime budget. -/
theorem clock_bound {width : Nat} (enc : Codec width) (x w rest : List Bool) (original : Nat)
    (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hw : w.length ≤ original) :
    clock enc rest ≤ runtimeBudget width (maxBody x.length original) := by
  have hlen : (Source284JoinedPrefixScan.joinedBody x w).length = 2*x.length+2*w.length+5 := by
    have h := congrArg List.length (Source284JoinedPrefixScan.joined_eq_body x w)
    simp only [List.length_append,List.length_singleton,Source284JoinedFrames.joined_length] at h
    omega
  have hr := congrArg List.length hbody
  simp only [List.length_reverse,List.length_cons] at hr
  have hm : (rest++[true]).length ≤ maxBody x.length original := by
    simp only [List.length_append,List.length_singleton,maxBody]
    omega
  have hc := Source284SerializerStripWindow.combined_cost_bound enc (rest++[true])
  have hmono := runtimeBudget_mono width hm
  change clock enc rest ≤ runtimeBudget width (rest++[true]).length at hc
  exact le_trans hc hmono

/-- The enlarged limit makes the existing decoded scratch long enough for
all witnesses within the original cutoff, regardless of high suffix. -/
theorem padding_sufficient {width : Nat} (enc : Codec width) (x w rest : List Bool)
    (original k : Nat) (hbody : (Source284JoinedPrefixScan.joinedBody x w).reverse = false::rest)
    (hw : w.length ≤ original) :
    k+clock enc rest+(Source284TaggedMarkerSeed.word enc).length+1 ≤
      2*((paddedLimit width x.length original k+1)+1) := by
  have hc := clock_bound enc x w rest original hbody hw
  have hl := Source284TaggedMarkerSeed.word_length enc
  dsimp [paddedLimit] at *
  omega

/-- The old cutoff remains part of the verifier, so enlarging the outer
certificate limit cannot introduce a witness that was previously too long. -/
def withinCutoff (original : Nat) (R : List Bool → Bool) (w : List Bool) : Bool :=
  decide (w.length ≤ original) && R w

theorem enlarged_search_iff (original enlarged bits : Nat) (R : List Bool → Bool)
    (hle : original ≤ enlarged)
    (hbits : Source284WitnessWindow.width enlarged+2 ≤ bits) :
    (∃ c, c < 2^bits ∧ Source284TaggedWitnessCodec.check enlarged (withinCutoff original R) c = true) ↔
      ∃ w, w.length ≤ original ∧ R w = true := by
  rw [Source284TaggedWitnessCodec.clock_search_iff enlarged bits (withinCutoff original R) hbits]
  constructor
  · rintro ⟨w,_,h⟩
    simp [withinCutoff] at h
    exact ⟨w,h.1,h.2⟩
  · rintro ⟨w,hw,hR⟩
    exact ⟨w,le_trans hw hle,by simp [withinCutoff,hw,hR]⟩

namespace Fixtures
/-- Enlarging the outer limit does not accept a witness above the old cutoff. -/
example : Source284TaggedWitnessCodec.check 1 (withinCutoff 0 (fun _ => true))
    (Source284TaggedWitnessCodec.encode [true]) = false := by decide +kernel
/-- A high alias of an allowed empty witness is still accepted by the guard. -/
example : Source284TaggedWitnessCodec.check 0 (withinCutoff 0 (fun _ => true)) 136 = true := by
  decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284PaddingBudget
