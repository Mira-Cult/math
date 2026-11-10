import PASoundness.PAtoCompactSuccCongruenceWitnessMatrix
import PASoundness.PAtoCompactSuccDoubleWitnessElim
import PASoundness.PAtoCompactSuccWitnessVacuityDynamic
import PASoundness.PAtoCompactSuccBaseMultiAlpha

/-! Witness-level K proof of quotient-successor congruence. The two
existentials are alpha-opened at fresh names and eliminated using explicit
vacuity; no semantic soundness or successor functionality is assumed. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactSuccCongruenceWitnessLift
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactSuccRelationWitnessAlpha PASoundness.PAtoCompactSuccCongruenceWitnessMatrix
open PASoundness.PAtoCompactSuccDoubleWitnessElim PASoundness.PAtoCompactSuccWitnessVacuityDynamic
open PASoundness.PAtoCompactSuccBaseMultiAlpha

/-- Quotient successors preserve equivalence, at a common base with explicit
fresh witness names. Only names are distinct; assigned objects may alias. -/
def common_congruence (b x y p q r s : Nat)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hq : q < b+2)
    (hr : r < b+2) (hs : s < b+2)
    (hrx : r ≠ x) (hry : r ≠ y) (hrp : r ≠ p) (hrq : r ≠ q)
    (hsx : s ≠ x) (hsy : s ≠ y) (hsp : s ≠ p) (hsq : s ≠ q) (hsr : s ≠ r) :
    KDerivation (imp (equivAt b x y).encode
      (imp (succAt b x p).encode (imp (succAt b y q).encode (equivAt b p q).encode))) := by
  let E := (equivAt b x y).encode
  let B := (matrix b x p r).encode
  let C := (matrix b y q s).encode
  let O := (equivAt b p q).encode
  have hfirst := (rename_witness b x p r hx hp hr hrx hrp).forward
  have hsecond := (rename_witness b y q s hy hq hs hsy hsq).forward
  have hstep : KDerivation (imp E (imp B (imp C O))) :=
    matrix_congruence b x y p q r s hx hy hp hq hr hs
  have hq := double_exists r s E B C O
    (equiv_vacuity b x y r hrx hry)
    (by simpa [C, matrix, openedBody, PASoundness.PAtoCompactAdjunction.namedSuccessor,
      Formula.encode] using opened_exists_vacuity b y q s r hry hrq)
    (equiv_vacuity b p q r hrp hrq)
    (by simpa [B, matrix, openedBody, PASoundness.PAtoCompactAdjunction.namedSuccessor,
      Formula.encode] using opened_exists_vacuity b x p r r hrx hrp)
    (equiv_vacuity b x y s hsx hsy)
    (by simpa [C, matrix, openedBody, PASoundness.PAtoCompactAdjunction.namedSuccessor,
      Formula.encode] using opened_exists_vacuity b y q s s hsy hsq)
    (by simpa [B, matrix, openedBody, PASoundness.PAtoCompactAdjunction.namedSuccessor] using
      opened_vacuity b x p r s hsx hsp hsr)
    (equiv_vacuity b p q s hsp hsq)
    (by simpa [B, matrix, openedBody, PASoundness.PAtoCompactAdjunction.namedSuccessor,
      Formula.encode] using opened_exists_vacuity b x p r s hsx hsp)
    hstep
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let A := (succAt b x p).encode
  let T := (succAt b y q).encode
  let Γ := [T,A,E]
  have he : Context Γ E := .hypothesis (by simp [Γ])
  have ha : Context Γ A := .hypothesis (by simp [Γ])
  have ht : Context Γ T := .head _ _
  exact .mp (.mp ht (.closed hsecond))
    (.mp (.mp ha (.closed hfirst)) (.mp he (.closed hq)))

/-- Same-base quotient successor congruence for arbitrary possibly aliased
operands below the allocator bound; fresh witness names are chosen internally. -/
def successor_congruence (b x y p q : Nat)
    (hx : x < b+2) (hy : y < b+2) (hp : p < b+2) (hq : q < b+2) :
    KDerivation (imp (equivAt b x y).encode
      (imp (succAt b x p).encode (imp (succAt b y q).encode (equivAt b p q).encode))) := by
  let r := max (max (max x y) p) q + 1
  let s := r + 1
  let c := max b s + 100
  have hrx : r ≠ x := by dsimp [r]; omega
  have hry : r ≠ y := by dsimp [r]; omega
  have hrp : r ≠ p := by dsimp [r]; omega
  have hrq : r ≠ q := by dsimp [r]; omega
  have hsx : s ≠ x := by dsimp [s,r]; omega
  have hsy : s ≠ y := by dsimp [s,r]; omega
  have hsp : s ≠ p := by dsimp [s,r]; omega
  have hsq : s ≠ q := by dsimp [s,r]; omega
  have hsr : s ≠ r := by dsimp [s]; omega
  have h := common_congruence c x y p q r s
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)
    hrx hry hrp hrq hsx hsy hsp hsq hsr
  have he := (equivAt_base_alpha b c x y hx hy
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)).forward
  have ha := (succAt_base_alpha b c x p hx hp
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)).forward
  have ht := (succAt_base_alpha b c y q hy hq
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega)).forward
  have ho := (equivAt_base_alpha c b p q
    (by dsimp [c,s,r]; omega) (by dsimp [c,s,r]; omega) hp hq).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let E := (equivAt b x y).encode
  let A := (succAt b x p).encode
  let T := (succAt b y q).encode
  let Γ := [T,A,E]
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hA : Context Γ A := .hypothesis (by simp [Γ])
  have hT : Context Γ T := .head _ _
  have hc : Context Γ (equivAt c p q).encode :=
    .mp (.mp hT (.closed ht)) (.mp (.mp hA (.closed ha)) (.mp (.mp hE (.closed he)) (.closed h)))
  exact .mp hc (.closed ho)

end PASoundness.PAtoCompactSuccCongruenceWitnessLift
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessLift.common_congruence
#print axioms PASoundness.PAtoCompactSuccCongruenceWitnessLift.successor_congruence
