import PASoundness.PAtoCompactSuccRelationWitnessAlpha
import PASoundness.PAtoCompactSuccOutputMatrix
import PASoundness.PAtoCompactSuccBaseMultiAlpha
import PASoundness.PAtoCompactFreeVacuity
import PASoundness.PAtoCompactGuardBaseTransport

/-! Quotient-successor output respects candidate-relative quotient equivalence.
This constructs finite K proof data; no semantic soundness is used. -/
namespace PASoundness.PAtoCompactSuccRelationOutputTransport

open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactSuccRelationWitnessAlpha PASoundness.PAtoCompactSuccOutputMatrix
open PASoundness.PAtoCompactSuccBaseMultiAlpha PASoundness.PAtoCompactEquivMultiAlpha
open PASoundness.PAtoCompactGuardBaseTransport PASoundness.PAtoCompactFreeVacuity
open PASoundness.PAtoCompactFreeNames

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Output transport at one block given a distinct, low existential witness
label. The supplied name is syntactic; represented objects may coincide. -/
def succ_output_at_fresh (b a q r w : Nat)
    (ha : a < b+2) (hq : q < b+2) (hr : r < b+2) (hw : w < b+2)
    (hwa : w ≠ a) (hwq : w ≠ q) (hwr : w ≠ r) :
    KDerivation (imp (domainAt b r).encode
      (imp (equivAt b q r).encode (imp (succAt b a q).encode (succAt b a r).encode))) := by
  let G := andF (domainAt b r) (equivAt b q r)
  have hGfree : w ∉ G.free := by
    intro h
    simp only [G, andF, Formula.not, Formula.free, Finset.union_empty, Finset.mem_union] at h
    rcases h with h | h
    · have hr' := domainAt_free b r h
      simp only [Finset.mem_singleton] at hr'
      exact hwr hr'
    · have he := equivAt_free b q r h
      simp only [Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with he | he
      · exact hwq he
      · exact hwr he
  have hv := free_vacuity w G hGfree
  let raw := Formula.all (b+10) (namedSuccessorBody a w (b+10))
  have hm : KDerivation (imp G.encode
      (imp (matrix b a q w).encode (matrix b a r w).encode)) := by
    simpa only [G, matrix, outputMatrix, raw] using
      output_matrix_guarded b a q r w raw hq hr hw
  have he := conditionalExistsCongr w hv hm
  have hs := (rename_witness b a q w ha hq hw hwa hwq).forward
  have ht := (rename_witness b a r w ha hr hw hwa hwr).backward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b r).encode
  let E := (equivAt b q r).encode
  let S := (succAt b a q).encode
  let Γ := [S,E,D]
  have hd : Context Γ D := .hypothesis (by simp [Γ])
  have heq : Context Γ E := .hypothesis (by simp [Γ])
  have hsrc : Context Γ S := Context.head _ _
  have hboth := Context.conjunctionIntro hd heq
  have hg : Context Γ G.encode := by
    simpa [G, andF, Formula.not, Formula.encode, both, neg] using hboth
  have hx : Context Γ (existsCode w (matrix b a q w).encode) := .mp hsrc (.closed hs)
  exact .mp (.mp hx (.mp hg (.closed he))) (.closed ht)

/-- Transport quotient successor along an equivalent candidate output. All
operand names are below the private block; aliases are permitted. -/
def succ_output (b a q r : Nat)
    (ha : a < b+2) (hq : q < b+2) (hr : r < b+2) :
    KDerivation (imp (domainAt b r).encode
      (imp (equivAt b q r).encode (imp (succAt b a q).encode (succAt b a r).encode))) := by
  let w := max (max a q) r + 1
  let c := max b w + 1
  have haw : a < w := by dsimp [w]; omega
  have hqw : q < w := by dsimp [w]; omega
  have hrw : r < w := by dsimp [w]; omega
  have hac : a < c+2 := by dsimp [c]; omega
  have hqc : q < c+2 := by dsimp [c]; omega
  have hrc : r < c+2 := by dsimp [c]; omega
  have hwc : w < c+2 := by dsimp [c]; omega
  have hf := succ_output_at_fresh c a q r w hac hqc hrc hwc (by omega) (by omega) (by omega)
  have hd := domainAt_transport b c r (by omega) (by omega)
  have he := (equivAt_base_alpha b c q r hq hr hqc hrc).forward
  have hs := (succAt_base_alpha b c a q ha hq hac hqc).forward
  have ht := (succAt_base_alpha c b a r hac hrc ha hr).forward
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  apply Context.deduction
  let D := (domainAt b r).encode
  let E := (equivAt b q r).encode
  let S := (succAt b a q).encode
  let Γ := [S,E,D]
  have hD : Context Γ D := .hypothesis (by simp [Γ])
  have hE : Context Γ E := .hypothesis (by simp [Γ])
  have hS : Context Γ S := Context.head _ _
  have hd' := Context.mp hD (.closed hd)
  have he' := Context.mp hE (.closed he)
  have hs' := Context.mp hS (.closed hs)
  exact .mp (.mp hs' (.mp he' (.mp hd' (.closed hf)))) (.closed ht)

#print axioms succ_output_at_fresh
#print axioms succ_output
end PASoundness.PAtoCompactSuccRelationOutputTransport
