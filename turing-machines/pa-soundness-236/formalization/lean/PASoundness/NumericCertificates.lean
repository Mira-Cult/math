import PASoundness.CertificateFixtures
import Mathlib.ModelTheory.Encoding
import Mathlib.Tactic.DeriveEncodable

/-!
Total numeric serialization for the genuine-PA proof checker, using mathlib's
existing term/formula list encodings and its checked Encodable machinery.
This is a separate reusable code format, not the compact PA238 ABI.
-/
namespace PASoundness.NumericCertificates
open FirstOrder FirstOrder.Language Certificates

def functionCode : (Σ n, Peano.language.Functions n) → Nat
  | ⟨_, .zero⟩ => 0
  | ⟨_, .succ⟩ => 1
  | ⟨_, .add⟩ => 2
  | ⟨_, .mul⟩ => 3

def functionDecode : Nat → Option (Σ n, Peano.language.Functions n)
  | 0 => some ⟨0, .zero⟩
  | 1 => some ⟨1, .succ⟩
  | 2 => some ⟨2, .add⟩
  | 3 => some ⟨2, .mul⟩
  | _ => none

theorem function_roundtrip (f : Σ n, Peano.language.Functions n) :
    functionDecode (functionCode f) = some f := by
  obtain ⟨n, f⟩ := f
  cases f <;> rfl

instance : Encodable (Σ n, Peano.language.Functions n) :=
  Encodable.ofLeftInjection functionCode functionDecode function_roundtrip

instance : Encodable (Σ n, Peano.language.Relations n) where
  encode := fun ⟨_, r⟩ => Empty.elim r
  decode := fun _ => none
  encodek := fun ⟨_, r⟩ => Empty.elim r

instance formulaSigmaEncodable (α : Type) [Encodable α] :
    Encodable (Σ n, Peano.language.BoundedFormula α n) :=
  Encodable.ofLeftInjection
    (fun φ => φ.2.listEncode)
    (fun code => (BoundedFormula.listDecode code).head?)
    (by
      intro φ
      have h := BoundedFormula.listDecode_encode_list [φ]
      simpa using congrArg List.head? h)

def selectScope {α : Type} (n : Nat)
    (φ : Σ k, Peano.language.BoundedFormula α k) :
    Option (Peano.language.BoundedFormula α n) :=
  if h : φ.1 = n then some (h ▸ φ.2) else none

instance formulaEncodable (α : Type) [Encodable α] (n : Nat) :
    Encodable (Peano.language.BoundedFormula α n) :=
  Encodable.ofLeftInjection (fun φ => (⟨n, φ⟩ : Σ k, Peano.language.BoundedFormula α k))
    (selectScope n) (by intro φ; simp [selectScope])

/-- A serialization product for the fixed finite logical-constructor tag set.
Malformed list shapes decode to none, independently of theorem validity. -/
abbrev LogicalPayload := Nat × List Peano.Formula × List Nat × List Peano.Term

def logicalPack : LogicalCode Peano.language → LogicalPayload
  | .k φ ψ => (0, [φ, ψ], [], [])
  | .s φ ψ χ => (1, [φ, ψ, χ], [], [])
  | .classical φ => (2, [φ], [], [])
  | .allElim φ x t => (3, [φ], [x], [t])
  | .allImp φ ψ x => (4, [φ, ψ], [x], [])
  | .vacuous φ x => (5, [φ], [x], [])
  | .eqRefl t => (6, [], [], [t])
  | .eqSubst φ x t u => (7, [φ], [x], [t, u])

def logicalUnpack : LogicalPayload → Option (LogicalCode Peano.language)
  | (0, [φ, ψ], [], []) => some (.k φ ψ)
  | (1, [φ, ψ, χ], [], []) => some (.s φ ψ χ)
  | (2, [φ], [], []) => some (.classical φ)
  | (3, [φ], [x], [t]) => some (.allElim φ x t)
  | (4, [φ, ψ], [x], []) => some (.allImp φ ψ x)
  | (5, [φ], [x], []) => some (.vacuous φ x)
  | (6, [], [], [t]) => some (.eqRefl t)
  | (7, [φ], [x], [t, u]) => some (.eqSubst φ x t u)
  | _ => none

theorem logical_roundtrip (c : LogicalCode Peano.language) :
    logicalUnpack (logicalPack c) = some c := by cases c <;> rfl

instance : Encodable (LogicalCode Peano.language) :=
  Encodable.ofLeftInjection logicalPack logicalUnpack logical_roundtrip

deriving instance Encodable for PACode

/-- This representation merely makes the existing generic proof tree concrete
for serialization. The inverse maps below preserve every constructor. -/
inductive Tree where
  | logical (c : LogicalCode Peano.language)
  | nonlogical (c : PACode)
  | mp (implication argument : Tree)
  | generalize (x : Nat) (premise : Tree)
  deriving Encodable

def ofProof : PAProofCode → Tree
  | .logical c => .logical c
  | .nonlogical c => .nonlogical c
  | .mp p q => .mp (ofProof p) (ofProof q)
  | .generalize x p => .generalize x (ofProof p)

def toProof : Tree → PAProofCode
  | .logical c => .logical c
  | .nonlogical c => .nonlogical c
  | .mp p q => .mp (toProof p) (toProof q)
  | .generalize x p => .generalize x (toProof p)

theorem tree_roundtrip (p : PAProofCode) : toProof (ofProof p) = p := by
  induction p <;> simp [ofProof, toProof, *]

theorem proof_roundtrip (p : Tree) : ofProof (toProof p) = p := by
  induction p <;> simp [ofProof, toProof, *]

instance : Encodable PAProofCode :=
  Encodable.ofLeftInjection ofProof (fun t => some (toProof t))
    (by intro p; simp [tree_roundtrip])

def encode (c : PAProofCode) : Nat := Encodable.encode c
def decode (code : Nat) : Option PAProofCode := Encodable.decode (α := PAProofCode) code

theorem roundtrip (c : PAProofCode) : decode (encode c) = some c :=
  Encodable.encodek c

/-- Actual total numeric proof checker. No semantic entailment or truth test. -/
def check (code : Nat) : Option Peano.Formula := (decode code).bind paCheck

theorem check_encode (c : PAProofCode) : check (encode c) = paCheck c := by
  simp [check, roundtrip]

theorem check_sound {code : Nat} {φ : Peano.Formula} (h : check code = some φ) :
    Peano.FormulaProves φ := by
  obtain ⟨c, _, hc⟩ := Option.bind_eq_some_iff.mp h
  exact paCheck_sound c φ hc

theorem check_coverage {φ : Peano.Formula} (h : Peano.FormulaProves φ) :
    ∃ code, check code = some φ := by
  obtain ⟨c, hc⟩ := paCheck_complete h
  exact ⟨encode c, (check_encode c).trans hc⟩

theorem check_exact (φ : Peano.Formula) :
    (∃ code, check code = some φ) ↔ Peano.FormulaProves φ :=
  ⟨fun ⟨_, h⟩ => check_sound h, check_coverage⟩

def successorCertificate : Nat := encode CertificateFixtures.successorAtZero

theorem successorCertificate_checked :
    check successorCertificate = paCheck CertificateFixtures.successorAtZero :=
  check_encode _

theorem malformed_parent_rejected :
    check (encode CertificateFixtures.invalidParent) = none := by
  rw [check_encode, CertificateFixtures.invalidParent_rejected]

end PASoundness.NumericCertificates
