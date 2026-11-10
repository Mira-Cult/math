import PASoundness.PAtoCompactGuardAssembly

/-! Guard assembly for unrestricted guarded generalization. A separate
candidate guard covers the source name erased by universal binding. -/
namespace PASoundness.PAtoCompactGeneralizationGuardAssembly

open FirstOrder FirstOrder.Language
open PASoundness.CompactNamed PASoundness.CompactProof PASoundness.CompactDerivations
open PASoundness.PAtoCompactTermTranslation PASoundness.PAtoCompactGuardedBridge
open PASoundness.PAtoCompactGuardAssembly

def extraBase (φ : Peano.Formula) (x : Nat) : Nat := max x (guardBase φ) + 1

theorem allAt_name_not_free (φ : Peano.Formula) (x : Nat) :
    x ∉ (FOL.allAt x φ).freeVarFinset := by
  simp [PASoundness.SyntaxTransport.allAt_freeVars]

/-- The guard of the universal and one candidate condition for the bound
name suffice to reconstruct the source formula's guard in finite K proof
data. Input names are syntactic labels; their assigned objects may alias. -/
def guard_assemble (φ : Peano.Formula) (x : Nat) :
    KDerivation (imp (guardFormula (FOL.allAt x φ)).encode
      (imp (domainAt (extraBase φ x) x).encode (guardFormula φ).encode)) := by
  have hc : KDerivation (imp (guardFormula (FOL.allAt x φ)).encode
      (imp (guardList (extraBase φ x) [x]).encode (guardFormula φ).encode)) := by
    unfold guardFormula
    apply guardList_combine
    · intro z hz
      have hz' := (Finset.mem_sort (· ≤ ·)).mp hz
      have hle : z ≤ (FOL.allAt x φ).freeVarFinset.sup id := Finset.le_sup (f := id) hz'
      unfold guardBase
      omega
    · intro z hz
      have hz' : z = x := by simpa using hz
      subst z
      unfold extraBase
      omega
    · intro z hz
      have hz' := (Finset.mem_sort (· ≤ ·)).mp hz
      have hle : z ≤ φ.freeVarFinset.sup id := Finset.le_sup (f := id) hz'
      unfold guardBase
      omega
    · intro z hz
      have hz' := (Finset.mem_sort (· ≤ ·)).mp hz
      by_cases he : z = x
      · exact Or.inr (by simp [he])
      · apply Or.inl
        apply (Finset.mem_sort (· ≤ ·)).mpr
        simpa [PASoundness.SyntaxTransport.allAt_freeVars, he] using hz'
  apply Context.closeEmpty
  apply Context.deduction
  apply Context.deduction
  let Γ := [(domainAt (extraBase φ x) x).encode, (guardFormula (FOL.allAt x φ)).encode]
  have hg : Context Γ (guardFormula (FOL.allAt x φ)).encode := .hypothesis (by simp [Γ])
  have hx : Context Γ (domainAt (extraBase φ x) x).encode := .hypothesis (by simp [Γ])
  have hlist : Context Γ (guardList (extraBase φ x) [x]).encode := by
    have h := Context.conjunctionIntro hx (.closed .truth)
    simpa [guardList, andF, CompactNamed.Formula.encode, CompactNamed.Formula.not, both, neg] using h
  exact .mp hlist (.mp hg (.closed hc))

theorem guard_assemble_certificate (φ : Peano.Formula) (x : Nat) :
    theoremCode (certificate (guard_assemble φ x)) =
      imp (guardFormula (FOL.allAt x φ)).encode
        (imp (domainAt (extraBase φ x) x).encode (guardFormula φ).encode) :=
  certificate_correct _

end PASoundness.PAtoCompactGeneralizationGuardAssembly

#print axioms PASoundness.PAtoCompactGeneralizationGuardAssembly.allAt_name_not_free
#print axioms PASoundness.PAtoCompactGeneralizationGuardAssembly.guard_assemble
#print axioms PASoundness.PAtoCompactGeneralizationGuardAssembly.guard_assemble_certificate
