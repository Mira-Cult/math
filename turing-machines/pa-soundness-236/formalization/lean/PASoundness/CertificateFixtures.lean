import PASoundness.Certificates
import PASoundness.Fixtures

namespace PASoundness.CertificateFixtures

open FirstOrder FirstOrder.Language Certificates

/-- Five-node propositional identity certificate: two applications of modus
ponens combine one S and two K instances. -/
def identityProof (φ : Peano.Formula) : PAProofCode :=
  .mp
    (.mp (.logical (.s φ (φ.imp φ) φ)) (.logical (.k φ (φ.imp φ))))
    (.logical (.k φ φ))

theorem identity_checked (φ : Peano.Formula) :
    paCheck (identityProof φ) = some (φ.imp φ) := by
  simp [paCheck, identityProof, check, logicalDecode]

def successorTemplate : Peano.Formula := ((Peano.succ (.var 0)).equal Peano.zero).not

/-- A PA axiom leaf, universal generalization, and universal elimination at 0. -/
def successorAtZero : PAProofCode :=
  .mp (.logical (.allElim successorTemplate 0 Peano.zero))
    (.generalize 0 (.nonlogical (.succNeZero (.var 0))))

theorem successorAtZero_checked :
    paCheck successorAtZero = some (FOL.substAt successorTemplate 0 Peano.zero) := by
  decide

def invalidVacuous : PAProofCode :=
  .logical (.vacuous ((.var 0 : Peano.Term).equal Peano.zero) 0)

theorem invalidVacuous_rejected : paCheck invalidVacuous = none := by decide

def invalidMP : PAProofCode :=
  .mp (.logical (.eqRefl Peano.zero)) (.logical (.eqRefl Peano.zero))

theorem invalidMP_rejected : paCheck invalidMP = none := by decide

def mismatchedMP : PAProofCode :=
  .mp (.logical (.k (Peano.zero.equal Peano.zero)
    ((Peano.succ Peano.zero).equal Peano.zero)))
    (.logical (.eqRefl (Peano.succ Peano.zero)))

theorem mismatchedMP_rejected : paCheck mismatchedMP = none := by decide

def invalidParent : PAProofCode := .generalize 0 invalidMP

theorem invalidParent_rejected : paCheck invalidParent = none := by decide

theorem missingEnumerationWitness_rejected :
    enumeratedDecode (fun _ => [Peano.zero.equal Peano.zero]) (0, 1) = none := by decide

/-- The checker result supplies a real finite syntactic derivation. -/
theorem successorAtZero_derivation :
    Peano.FormulaProves (FOL.substAt successorTemplate 0 Peano.zero) :=
  paCheck_sound _ _ successorAtZero_checked

end PASoundness.CertificateFixtures
