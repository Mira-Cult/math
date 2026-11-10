import PASoundness.PAtoCompactGuardElimination
import PASoundness.PAtoCompactZeroBaseTransport

/-! A zero term graph is inhabited by an actual finite K derivation. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.PAtoCompactZeroTermTotality

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactZeroSuccessor
open PASoundness.PAtoCompactZeroExistence PASoundness.PAtoCompactEmptyDomain
open PASoundness.PAtoCompactGuardElimination PASoundness.PAtoCompactZeroBaseTransport
open PASoundness.PAtoCompactFormulaTranslation

/-- The named zero graph has the same literal code as the original K graph. -/
theorem zeroAt_encode (base x : Nat) :
    (zeroAt base x).encode = zeroCode x (base + 3) := by
  simp [zeroAt_shape, Formula.encode, zeroCode, neg, allCode]

/-- Construct one output that is both a candidate and a zero graph. -/
def zero_at_one_exists (base : Nat) :
    KDerivation (existsCode 1 (andF (domainAt base 1) (zeroAt base 1)).encode) := by
  have hf : [1, base+3, base+32, base+33, base+34, base+35,
      base+36, base+37, base+38, base+39].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      or_false, not_or, not_false_eq_true, List.nodup_nil, and_true]
    repeat' apply And.intro
    all_goals omega
  have hc := zero_candidate 1 (base+3) (base+32) (base+33) (base+34)
    (base+35) (base+36) (base+37) (base+38) (base+39) hf
  have hd : KDerivation (imp (zeroCode 1 (base+3)) (domainAt base 1).encode) := by
    simpa only [domainAt_code, PAtoCompactCandidateExact.candidateCode] using hc
  have h : KDerivation (imp (zeroCode 1 (base+3))
      (andF (domainAt base 1) (zeroAt base 1)).encode) := by
    apply Context.closeEmpty
    apply Context.deduction
    have hz := Context.head [] (zeroCode 1 (base+3))
    have hdom : Context [zeroCode 1 (base+3)] (domainAt base 1).encode := .mp hz (.closed hd)
    have hzero : Context [zeroCode 1 (base+3)] (zeroAt base 1).encode := by
      simpa only [zeroAt_encode] using hz
    have bothProof := Context.conjunctionIntro hdom hzero
    simpa [andF, Formula.encode, CompactNamed.Formula.not, both, neg] using bothProof
  exact .mp (zero_graph_exists (base+3) (by omega)) (existsCongr 1 h)

theorem zero_at_one_not_binder (base : Nat) :
    1 ∉ (andF (domainAt base 1) (zeroAt base 1)).binders := by
  have hz : 1 ∉ (zeroAt base 1).binders := by
    simp [zeroAt_shape, Formula.binders]
  simp [andF, CompactNamed.Formula.not, Formula.binders, one_not_domain_binder, hz]

theorem target_not_zero_names (base x : Nat) (hx : x < base + 2) (h1 : x ≠ 1) :
    x ∉ (andF (domainAt base 1) (zeroAt base 1)).names := by
  have hz : x ∉ (zeroAt base 1).names := by
    simp [zeroAt_shape, Formula.names, h1, show x ≠ base+3 by omega]
  simp [andF, CompactNamed.Formula.not, Formula.names, target_not_domain_names base x hx h1, hz]

theorem replace_zero_one (base x : Nat) :
    replace 1 x (zeroAt base 1) = zeroAt base x := by
  simp [zeroAt_shape, replace, rename, show base+3 ≠ 1 by omega]

theorem replace_zero_graph_one (base x : Nat) :
    replace 1 x (andF (domainAt base 1) (zeroAt base 1)) =
      andF (domainAt base x) (zeroAt base x) := by
  simp [andF, CompactNamed.Formula.not, replace, replace_domain_one, replace_zero_one]

/-- A literal zero-term graph has an output at any label below its private
block. The proof constructs a zero witness and uses capture-safe alpha. -/
def zero_term_total {α : Type} (v : α → Nat) (base out : Nat) (ho : out < base + 2) :
    KDerivation (existsCode out
      (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out base).encode) := by
  change KDerivation (existsCode out (andF (domainAt base out) (zeroAt base out)).encode)
  by_cases he : out = 1
  · subst out
    exact zero_at_one_exists base
  · have h := (existentialAlpha 1 out (andF (domainAt base 1) (zeroAt base 1))
      (Ne.symm he) (zero_at_one_not_binder base) (target_not_zero_names base out ho he)).1
    rw [replace_zero_graph_one base out] at h
    exact .mp (zero_at_one_exists base) h

theorem zero_term_total_certificate {α : Type} (v : α → Nat) (base out : Nat)
    (ho : out < base + 2) :
    theoremCode (certificate (zero_term_total v base out ho)) =
      existsCode out (termGraph v (.func .zero Fin.elim0 : Peano.language.Term α) out base).encode :=
  certificate_correct _

end PASoundness.PAtoCompactZeroTermTotality

#print axioms PASoundness.PAtoCompactZeroTermTotality.zero_term_total
#print axioms PASoundness.PAtoCompactZeroTermTotality.zero_term_total_certificate
