import PASoundness.PeanoUniversalClosure
import PASoundness.PeanoClosedFormulaSentence

/-! From an explicit closed-sentence PA soundness hypothesis to truth of a
particular open PA derivation, by finite syntactic universal closure. -/
namespace PASoundness.PeanoClosedToOpenSoundness
open FirstOrder FirstOrder.Language
open Peano

/-- Every named PA derivation is true at an arbitrary assignment, provided
the stated soundness hypothesis for closed PA sentences. The proof applies
that hypothesis to the sentence represented by the finite universal closure
of the supplied derivation; it does not invoke any independent PA soundness
theorem or assume semantic truth of PA axioms. -/
theorem open_of_closed_soundness
    (hPA : ∀ s : Peano.Sentence, Peano.Proves s → Nat ⊨ s)
    (φ : Peano.Formula) (h : Peano.FormulaProves φ) (v : Nat → Nat) :
    φ.Realize v := by
  let C := PeanoUniversalClosure.closure φ
  have hc : C.freeVarFinset = ∅ := PeanoUniversalClosure.closure_closed φ
  have hd : Peano.FormulaProves C := PeanoUniversalClosure.closure_proves h
  have ht : C.Realize v :=
    PeanoClosedFormulaSentence.realize_of_closed_soundness hPA C hc hd v
  exact PeanoUniversalClosure.closure_elim φ v ht

end PASoundness.PeanoClosedToOpenSoundness

#print axioms PASoundness.PeanoClosedToOpenSoundness.open_of_closed_soundness
