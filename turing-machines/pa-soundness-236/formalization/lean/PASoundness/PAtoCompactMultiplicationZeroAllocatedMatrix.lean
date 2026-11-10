import PASoundness.PAtoCompactMultiplicationCandidate
import PASoundness.PAtoCompactOrderIsoZero
import PASoundness.PAtoCompactTermTranslation

/-! Finite K proof for the allocated multiplication relation when its first
input and output have explicit zero graphs. This is a zero-factor case, not
general multiplication totality or a PA interpretation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactMultiplicationCandidate
open PASoundness.PAtoCompactZeroSuccessor PASoundness.PAtoCompactEmptyExtrema
open PASoundness.PAtoCompactOrderIsoZero

attribute [local irreducible] CompactProof.imp PASoundness.Cantor.pair PASoundness.Cantor.triangle

private def inputMap (b x y out : Nat) := threeMap b 0 1 2 x y out
private def F (b x y out : Nat) := mapNames (inputMap b x y out) (normalizeBottom forwardFormula)
private def R (b x y out : Nat) := mapNames (inputMap b x y out) (normalizeBottom reverseFormula)
private def L (b x y out : Nat) := mapNames (inputMap b x y out) (normalizeBottom lexFormula)
private def FT (b x y out : Nat) : Nat := match F b x y out with
  | .all _ (.imp _ body) => body.encode
  | _ => 0
private def RT (b x y out : Nat) : Nat := match R b x y out with
  | .all _ (.imp _ body) => body.encode
  | _ => 0
private def LT (b x y out : Nat) : Nat := match L b x y out with
  | .all _ (.all _ (.all _ (.all _ (.all _ (.all _ (.imp
      (.imp (.imp _ (.imp tail .bottom)) .bottom) _)))))) => tail.encode
  | _ => 0
private def LC (b x y out : Nat) : Nat := match L b x y out with
  | .all _ (.all _ (.all _ (.all _ (.all _ (.all _ (.imp _ rhs)))))) => rhs.encode
  | _ => 0

private theorem forward_shape (b x y out : Nat) : (F b x y out).encode =
    allCode (b+5) (imp (member x (b+5)) (FT b x y out)) := by rfl
private theorem reverse_shape (b x y out : Nat) : (R b x y out).encode =
    allCode (b+7) (imp (member out (b+7)) (RT b x y out)) := by rfl
private theorem lex_shape (b x y out : Nat) : (L b x y out).encode =
    allCode (b+5) (allCode (b+6) (allCode (b+7) (allCode (b+9)
      (allCode (b+10) (allCode (b+11)
        (imp (both (member x (b+5)) (LT b x y out)) (LC b x y out))))))) := by rfl

/-- An empty first factor makes the allocated order clause provable in K. -/
def zero_lex (b x y out : Nat) (hx : x < b) :
    KDerivation (imp (zeroCode x (b+3)) (L b x y out).encode) := by
  rw [lex_shape]
  apply Context.closeEmpty
  apply Context.deduction
  let Z := zeroCode x (b+3)
  let Γ := [Z]
  have hlocal : Context Γ
      (imp (both (member x (b+5)) (LT b x y out)) (LC b x y out)) := by
    apply Context.deduction
    let Δ := [both (member x (b+5)) (LT b x y out), Z]
    have ha : Context Δ (both (member x (b+5)) (LT b x y out)) := Context.head _ _
    have hm : Context Δ (member x (b+5)) := Context.conjunctionLeft ha
    have hz : Context Δ Z := .hypothesis (by simp [Δ])
    have hn : Context Δ (neg (member x (b+5))) :=
      .mp hz (.closed (zero_excludes x (b+3) (b+5) (by omega) (by omega)))
    exact Context.explode _ (.mp hm hn)
  have v (n : Nat) (hnx : n ≠ x) (hnz : n ≠ b+3) :
      ∀ h, h ∈ Γ → KDerivation (imp h (allCode n h)) := by
    intro h hh
    have he : h = Z := by simpa [Γ] using hh
    subst h
    exact zero_vacuity x (b+3) n hnx hnz
  exact Context.generalize (b+5) (v _ (by omega) (by omega))
    (Context.generalize (b+6) (v _ (by omega) (by omega))
      (Context.generalize (b+7) (v _ (by omega) (by omega))
        (Context.generalize (b+9) (v _ (by omega) (by omega))
          (Context.generalize (b+10) (v _ (by omega) (by omega))
            (Context.generalize (b+11) (v _ (by omega) (by omega)) hlocal)))))

/-- With zero graphs for the first factor and the output, the exact allocated
multiplication relation has a graph witness. Input labels may coincide. -/
def zero_product (b x y out : Nat) (hx : x < b) (_hy : y < b) (ho : out < b) :
    KDerivation (imp (zeroAt b x).encode (imp (zeroAt b out).encode (mulAt b x y out).encode)) := by
  let Z0 := zeroCode x (b+3)
  let Z2 := zeroCode out (b+3)
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [Z2,Z0]
  have hz0 : Context Γ Z0 := .hypothesis (by simp [Γ])
  have hz2 : Context Γ Z2 := Context.head _ _
  have hf : Context Γ (F b x y out).encode := by
    rw [forward_shape]
    exact .mp hz0 (.closed (zero_guard_all x (b+3) (b+5) (FT b x y out)
      (by omega) (by omega) (by omega)))
  have hr : Context Γ (R b x y out).encode := by
    rw [reverse_shape]
    exact .mp hz2 (.closed (zero_guard_all out (b+3) (b+7) (RT b x y out)
      (by omega) (by omega) (by omega)))
  have hl : Context Γ (L b x y out).encode := .mp hz0 (.closed (zero_lex b x y out hx))
  have hm : Context Γ (andF (F b x y out) (andF (R b x y out) (L b x y out))).encode := by
    have h := Context.conjunctionIntro hf (Context.conjunctionIntro hr hl)
    simpa [andF, Formula.encode, Formula.not, both, neg] using h
  have hi := existsIntroduce (b+8) (andF (F b x y out) (andF (R b x y out) (L b x y out))) (by
    change b+8 ∉ (mapNames (inputMap b x y out) (normalizeBottom productMatrix)).binders
    rw [mapNames_binders]
    intro h
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
    have hb : (normalizeBottom productMatrix).binders = {3,4,5,7,8,9,18,19,20,21,22} := by decide
    rw [hb] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [inputMap, threeMap] at he)
  have hp := Context.mp hm (.closed hi)
  change Context Γ (mulAt b x y out).encode at hp
  exact hp

theorem zero_product_certificate (b x y out : Nat)
    (hx : x < b) (hy : y < b) (ho : out < b) :
    theoremCode (certificate (zero_product b x y out hx hy ho)) =
      imp (zeroAt b x).encode (imp (zeroAt b out).encode (mulAt b x y out).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix

#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix.zero_lex
#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix.zero_product
#print axioms PASoundness.PAtoCompactMultiplicationZeroAllocatedMatrix.zero_product_certificate
