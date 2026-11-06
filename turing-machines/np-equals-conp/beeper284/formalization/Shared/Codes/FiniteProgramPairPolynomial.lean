import Shared.Codes.FiniteProgramPairUnified
import Shared.ComplexityBridge.ClockBounds
set_option maxHeartbeats 3000000
set_option linter.constructorNameAsVariable false

/-! Dominate the initializer's piecewise exact transition count by one
polynomial in the full canonical encoded-pair length. -/
noncomputable section
namespace Shared.Codes.FiniteProgramPairPolynomial
open Shared.Codes.FiniteProgramPairUnified

abbrev c (n : Nat) : Polynomial Nat := Polynomial.C n
abbrev X : Polynomial Nat := Polynomial.X

def decodePoly (width : Nat) (n : Polynomial Nat) : Polynomial Nat :=
  c 30*(c width+n*(c width+1))+20 +
    (n+1)*(c (7*width)+c 30*((n+1)*(c width+1))+26)

def emptyPoly (mz z o : List Bool) (width : Nat) : Polynomial Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
  let gain := 6*(1+w)
  let n := c 6*X
  let k := (n+1)*c width
  ((c 6*X+4) + c (16*mz.length+31) +
    (4+X*(6*(16*(c (1+mz.length)+X*c gain+c gain)+c (16*w+31))+4))) +
    2+decodePoly width n+2+(k*(20*k+21)+6)+2

def nonemptyPoly (mz z o : List Bool) (width : Nat) : Polynomial Nat :=
  let w := Shared.Codes.FiniteProgramTaggedLoop.maxWord z o
  let gw := 3*(1+w)
  let gx := 6*(1+w)
  let start := 1+mz.length+2*(1+w)
  let bulk := c start+X*c gw
  let n := c 6*X+c 3*X+3
  let k := (n+1)*c width
  ((c 6*X+c 3*(X+1)+2) +
    ((c (16*mz.length+31) + (2*(16*(c start)+c (16*w+31))+2)) + 2 +
      (X*(3*(16*(c start+X*c gw+c gw)+c (16*w+31))+4)+2+
        (16*bulk+c (16*w+31) + (4+X*(6*(16*(bulk+c (1+w)+X*c gx+c gx)+c (16*w+31))+4)))))) +
    2+decodePoly width n+2+(k*(20*k+21)+6)+2

def polynomial (mz z o : List Bool) (width : Nat) : Polynomial Nat :=
  emptyPoly mz z o width + nonemptyPoly mz z o width

theorem emptyPoly_eval (mz z o : List Bool) (width n : Nat) :
    (emptyPoly mz z o width).eval n = emptyBound mz z o (List.replicate n false) width := by
  simp [emptyPoly,emptyBound,decodePoly,Shared.Codes.FiniteProgramEmptyWitnessDecode.scanBound,
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeBound,Shared.Codes.FiniteProgramPairDecodeAll.decodeBound,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Nat.add_assoc]

theorem nonemptyPoly_eval (mz z o : List Bool) (width n : Nat) :
    (nonemptyPoly mz z o width).eval n =
      nonemptyBound mz z o (List.replicate n false) (List.replicate n false) width := by
  simp [nonemptyPoly,nonemptyBound,decodePoly,Shared.Codes.FiniteProgramPairDecodeAll.scanBound,
    Shared.Codes.FiniteProgramPairDecodeAll.decodeBound,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Nat.add_assoc]

/-- The empty-branch bound is monotone in the first component length. -/
theorem emptyBound_mono (mz z o x : List Bool) (width n : Nat) (hx : x.length ≤ n) :
    emptyBound mz z o x width ≤ emptyBound mz z o (List.replicate n false) width := by
  simp only [emptyBound,Shared.Codes.FiniteProgramEmptyWitnessDecode.scanBound,
    Shared.Codes.FiniteProgramEmptyWitnessDecode.decodeBound,Shared.Codes.FiniteProgramPairDecodeAll.decodeBound,
    List.length_replicate]
  gcongr

/-- The nonempty-branch bound is monotone in both component lengths. -/
theorem nonemptyBound_mono (mz z o x earlier : List Bool) (width n : Nat)
    (hx : x.length ≤ n) (hw : earlier.length ≤ n) :
    nonemptyBound mz z o x earlier width ≤
      nonemptyBound mz z o (List.replicate n false) (List.replicate n false) width := by
  simp only [nonemptyBound,Shared.Codes.FiniteProgramPairDecodeAll.scanBound,
    Shared.Codes.FiniteProgramPairDecodeAll.decodeBound,List.length_replicate]
  gcongr

/-- One explicit polynomial dominates both witness cases, including the empty
pair, in the length of the actual Google-encoded input. -/
theorem bound_polynomial (mz z o x w : List Bool) (width : Nat) :
    bound mz z o x w width ≤ (polynomial mz z o width).eval (BitstringEncoding.bitEncode (x,w)).length := by
  let n := (BitstringEncoding.bitEncode (x,w)).length
  have hx : x.length ≤ n := by
    dsimp [n]; rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]; omega
  have hw : w.length ≤ n := by
    dsimp [n]; rw [Shared.ComplexityBridge.bitstring_pair_encoded_length]; omega
  have hpoly : (polynomial mz z o width).eval n =
      emptyBound mz z o (List.replicate n false) width +
        nonemptyBound mz z o (List.replicate n false) (List.replicate n false) width := by
    simp [polynomial,Polynomial.eval_add,emptyPoly_eval,nonemptyPoly_eval]
  change bound mz z o x w width ≤ (polynomial mz z o width).eval n
  rw [hpoly]
  cases hr : w.reverse with
  | nil =>
    have h := emptyBound_mono mz z o x width n hx
    simp only [bound,hr]
    omega
  | cons b tail =>
    have ht : tail.reverse.length ≤ n := by
      have := congrArg List.length hr
      simp only [List.length_reverse,List.length_cons] at this
      simp only [List.length_reverse]
      omega
    have h := nonemptyBound_mono mz z o x tail.reverse width n hx ht
    simp only [bound,hr]
    omega

theorem runtime_polynomial (mz mo z o x w : List Bool) (width : Nat)
    (hm : mz.length = width) (hz : z.length = width) (ho : o.length = width) :
    runtime mz mo z o x w width ≤ (polynomial mz z o width).eval (BitstringEncoding.bitEncode (x,w)).length :=
  le_trans (runtime_bound mz mo z o x w width hm hz ho) (bound_polynomial mz z o x w width)

end Shared.Codes.FiniteProgramPairPolynomial
end
