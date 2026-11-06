import Shared.Beeping.NPcoNP.Source284BitWindowTM2
import Shared.Beeping.NPcoNP.Source284PackedGuardWindow
import Shared.Beeping.NPcoNP.Source284EvaluatorBitStep
import Shared.Beeping.NPcoNP.Source284RawParseTM2
import Shared.Beeping.NPcoNP.Source284FixedGuardForwardTM2

/-! Executable tagged witness extraction from a binary list and a unary
witness-limit list. The missing source-tape loader is not implemented here. -/
namespace Shared.Beeping.NPcoNP.Source284TaggedBitDecode

open ComplexityTheory Shared.ComplexityBridge
open Shared.Codes.BitNumeralCompare (value)
open Shared.Beeping.NPcoNP.Source284RawParse (payload)

/-- The two low certificate bits are the reserved zero tag. -/
def tagOK (bits : List Bool) : Bool := !(bits.headD false) && !(bits.tail.headD false)

theorem tagOK_isPolyTime : IsPolyTime tagOK := by
  let first : List Bool → Bool := fun xs => xs.headD false
  let tail : List Bool → List Bool := List.tail
  let second : List Bool → Bool := fun xs => (tail xs).headD false
  let a : List Bool → Bool := fun xs => !first xs
  let b : List Bool → Bool := fun xs => !second xs
  have hf : IsPolyTime first := Source284BitListAccessTM2.head_isPolyTime
  have ht : IsPolyTime tail := Source284BitListAccessTM2.tail_isPolyTime
  have hs : IsPolyTime second := TM2Compose.isPolyTime_comp tail first ht hf
  have ha : IsPolyTime a := TM2Compose.isPolyTime_comp first Bool.not hf TM2GateDispatch.not_isPolyTime
  have hb : IsPolyTime b := TM2Compose.isPolyTime_comp second Bool.not hs TM2GateDispatch.not_isPolyTime
  have h := TM2Compose.isPolyTime_comp (fun xs : List Bool => (a xs,b xs))
    (fun p : Bool × Bool => p.1 && p.2) (TM2GuardAllStep.pair_isPolyTime a b ha hb)
    TM2GateDispatch.and_isPolyTime
  exact h

theorem tagOK_correct (bits : List Bool) : tagOK bits = true ↔ value bits % 4 = 0 := by
  cases bits with
  | nil => simp [tagOK,value]
  | cons a rest =>
    cases rest with
    | nil => cases a <;> simp [tagOK,value]
    | cons b rest =>
      cases a <;> cases b <;> simp [tagOK,value,Nat.add_mod,Nat.mul_mod] <;> omega

/-- A finite payload parser ignores an arbitrary number of high zero bits,
including the special case of a final true marker with virtual zero payload. -/
theorem payload_false_replicate (n : Nat) : payload (List.replicate n false) = [] := by
  cases n <;> rfl

theorem payload_zero_padding (bits : List Bool) (n : Nat) :
    payload (bits ++ List.replicate n false) = payload bits := by
  induction bits using List.twoStepInduction with
  | nil => simpa [payload] using payload_false_replicate n
  | singleton b =>
    cases b <;> cases n <;> simp [payload,List.replicate_succ,payload_false_replicate]
  | cons_cons a b bs ih _ =>
    cases a <;> simp [payload,ih]

def widthTokens (tokens : List Bool) : List Bool := tokens ++ tokens ++ [true,true]

theorem widthTokens_length (tokens : List Bool) :
    (widthTokens tokens).length = Source284WitnessWindow.width tokens.length := by
  simp [widthTokens,Source284WitnessWindow.width]
  omega

theorem widthTokens_isPolyTime : IsPolyTime widthTokens := by
  have hi : IsPolyTime (id : List Bool → List Bool) :=
    ⟨Turing.idComputableInPolyTime BitstringEncoding.bitEncode⟩
  have hp := TM2GuardAllStep.pair_isPolyTime (id : List Bool → List Bool) id hi hi
  have hd := TM2Compose.isPolyTime_comp (fun xs : List Bool => (xs,xs))
    (TM2ListAppend.append (α := Bool)) hp TM2ListAppend.append_isPolyTime
  have h1 := TM2Compose.isPolyTime_comp (fun xs : List Bool => xs++xs)
    (fun xs : List Bool => xs++[true]) (by simpa [TM2ListAppend.append] using hd)
    Source284FixedGuardRowTM2.addSingleton_isPolyTime
  have h2 := TM2Compose.isPolyTime_comp (fun xs : List Bool => (xs++xs)++[true])
    (fun xs : List Bool => xs++[true]) h1 Source284FixedGuardRowTM2.addSingleton_isPolyTime
  change IsPolyTime (fun xs => xs++xs++[true,true])
  simpa [List.append_assoc] using h2

def witness (p : List Bool × List Bool) : List Bool :=
  payload (Source284BitWindowTM2.extract (widthTokens p.1,p.2.tail.tail))

theorem witness_isPolyTime : IsPolyTime witness := by
  let tokens : List Bool × List Bool → List Bool := fun p => p.1
  let cert : List Bool × List Bool → List Bool := fun p => p.2
  let width : List Bool × List Bool → List Bool := fun p => widthTokens (tokens p)
  let tail : List Bool × List Bool → List Bool := fun p => (cert p).tail
  let tail2 : List Bool × List Bool → List Bool := fun p => (tail p).tail
  have ht : IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime cert := TM2GuardAllStep.second_isPolyTime
  have hw : IsPolyTime width := TM2Compose.isPolyTime_comp tokens widthTokens ht widthTokens_isPolyTime
  have htail : IsPolyTime tail := TM2Compose.isPolyTime_comp cert List.tail hc Source284BitListAccessTM2.tail_isPolyTime
  have htail2 : IsPolyTime tail2 := TM2Compose.isPolyTime_comp tail List.tail htail Source284BitListAccessTM2.tail_isPolyTime
  have he := TM2Compose.isPolyTime_comp (fun p : List Bool × List Bool => (width p,tail2 p))
    Source284BitWindowTM2.extract (TM2GuardAllStep.pair_isPolyTime width tail2 hw htail2)
    Source284BitWindowTM2.extract_isPolyTime
  exact TM2Compose.isPolyTime_comp
    (fun p : List Bool × List Bool => Source284BitWindowTM2.extract (width p,tail2 p))
    payload he Source284RawParseTM2.payload_isPolyTime

theorem witness_correct (tokens cert : List Bool) :
    witness (tokens,cert) =
      payload (((value cert / 4) % 2^Source284WitnessWindow.width tokens.length).bits) := by
  unfold witness
  rw [Source284BitWindowTM2.extract_eq_window,widthTokens_length]
  have ht : value cert.tail.tail = value cert / 4 := by
    rw [Source284EvaluatorBitStep.value_tail,Source284EvaluatorBitStep.value_tail]
    omega
  rw [ht]
  simp [Source284CanonicalPairWindow.window,payload_zero_padding]

abbrev Input := List Bool × (List Bool × List Bool)

/-- One total comparison uses an explicit unary witness limit, rejects a bad
tag or overlong decoded witness, and otherwise evaluates the supplied relation. -/
def check (R : List Bool × List Bool → Bool) (p : Input) : Bool :=
  let w := witness (p.1,p.2.2)
  if tagOK p.2.2 && TM2BoundedWitnessGuard.guard (p.1++[true],w.length) then R (payload p.2.1,w)
  else false

theorem check_isPolyTime (R : List Bool × List Bool → Bool) (hR : IsPolyTime R) : IsPolyTime (check R) := by
  let tokens : Input → List Bool := fun p => p.1
  let tapes : Input → List Bool × List Bool := fun p => p.2
  let input : Input → List Bool := fun p => (tapes p).1
  let cert : Input → List Bool := fun p => (tapes p).2
  let w : Input → List Bool := fun p => witness (tokens p,cert p)
  let raw : Input → List Bool := fun p => payload (input p)
  let budget : Input → List Bool := fun p => tokens p ++ [true]
  let size : Input → Nat := fun p => (w p).length
  let tag : Input → Bool := fun p => tagOK (cert p)
  let fits : Input → Bool := fun p => TM2BoundedWitnessGuard.guard (budget p,size p)
  let flag : Input → Bool := fun p => tag p && fits p
  let yes : Input → Bool := fun p => R (raw p,w p)
  let no : Input → Bool := fun _ => false
  have ht : IsPolyTime tokens := TM2PairFirst.first_isPolyTime
  have htapes : IsPolyTime tapes := TM2GuardAllStep.second_isPolyTime
  have hi : IsPolyTime input := TM2Compose.isPolyTime_comp tapes _ htapes TM2PairFirst.first_isPolyTime
  have hc : IsPolyTime cert := TM2Compose.isPolyTime_comp tapes _ htapes TM2GuardAllStep.second_isPolyTime
  have hw : IsPolyTime w := TM2Compose.isPolyTime_comp (fun p : Input => (tokens p,cert p)) witness
    (TM2GuardAllStep.pair_isPolyTime tokens cert ht hc) witness_isPolyTime
  have hr : IsPolyTime raw := TM2Compose.isPolyTime_comp input payload hi Source284RawParseTM2.payload_isPolyTime
  have hb : IsPolyTime budget := TM2Compose.isPolyTime_comp tokens (fun xs => xs++[true]) ht
    Source284FixedGuardRowTM2.addSingleton_isPolyTime
  have hs : IsPolyTime size := TM2Compose.isPolyTime_comp w List.length hw TM2BinaryListLength.length_isPolyTime
  have htag : IsPolyTime tag := TM2Compose.isPolyTime_comp cert tagOK hc tagOK_isPolyTime
  have hfits : IsPolyTime fits := TM2Compose.isPolyTime_comp (fun p : Input => (budget p,size p))
    TM2BoundedWitnessGuard.guard (TM2GuardAllStep.pair_isPolyTime budget size hb hs)
    TM2BoundedWitnessGuard.guard_isPolyTime
  have hflag : IsPolyTime flag := TM2Compose.isPolyTime_comp (fun p : Input => (tag p,fits p))
    (fun p : Bool × Bool => p.1 && p.2) (TM2GuardAllStep.pair_isPolyTime tag fits htag hfits)
    TM2GateDispatch.and_isPolyTime
  have hy : IsPolyTime yes := TM2Compose.isPolyTime_comp (fun p : Input => (raw p,w p)) R
    (TM2GuardAllStep.pair_isPolyTime raw w hr hw) hR
  have hn : IsPolyTime no := TM2Constant.isPolyTime false
  exact TM2If.if_isPolyTime flag yes no hflag hy hn

theorem check_correct (R : List Bool × List Bool → Bool) (tokens input cert : List Bool) :
    check R (tokens,(input,cert)) =
      Source284TaggedWitnessCodec.check tokens.length (fun w => R (payload input,w)) (value cert) := by
  have hw := witness_correct tokens cert
  have hfits : TM2BoundedWitnessGuard.guard (tokens++[true],(witness (tokens,cert)).length) =
      decide ((witness (tokens,cert)).length ≤ tokens.length) := by
    apply Bool.eq_iff_iff.mpr
    rw [TM2BoundedWitnessGuard.guard_correct]
    simp
  by_cases ht : value cert % 4 = 0
  · have htag : tagOK cert = true := (tagOK_correct cert).2 ht
    simp only [check,htag,Bool.true_and,hfits,Source284TaggedWitnessCodec.check,
      Source284TaggedWitnessCodec.decode,ht,↓reduceIte,Source284WitnessWindow.decode]
    rw [← hw]
    split_ifs <;> simp_all <;> omega
  · have htag : tagOK cert = false := by
      cases h : tagOK cert with
      | false => rfl
      | true => exact False.elim (ht ((tagOK_correct cert).1 h))
    simp [check,htag,Source284TaggedWitnessCodec.check,Source284TaggedWitnessCodec.decode,ht]

namespace Fixtures
example : tagOK [] = true := by decide +kernel
example : tagOK [true] = false := by decide +kernel
example : tagOK [false,true] = false := by decide +kernel
example : witness ([],[false,false,true]) = [false] := by decide +kernel
example : check (fun _ => true) ([],([],[false,false,true])) = false := by decide +kernel
example : check (fun _ => true) ([true],([],[false,false,true,false,false,true])) = true := by decide +kernel
example : check (fun _ => true) ([true],([],[false,true,true,false,false,true])) = false := by decide +kernel
end Fixtures

end Shared.Beeping.NPcoNP.Source284TaggedBitDecode
