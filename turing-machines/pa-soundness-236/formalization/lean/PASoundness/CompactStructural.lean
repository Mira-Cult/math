import PASoundness.CompactNormalization
import PASoundness.CompactAcceptance

/-!
# Structural all-rank calibration of the actual compact source

The proof interpreter, constructive proof normalization, literal prefix
recognizer, matrix evaluator, fair schedule and guarded online observer are
instantiated here. No soundness theorem for K or PA is used in the structural
equivalences. The presentation is deliberately named K: a bidirectional
finite-proof interpretation with genuine PA remains a separate obligation.
-/
namespace PASoundness.CompactStructural
open Observer CompactProof

/-- The compact source interprets every remaining free name as zero. -/
def compact : TheoryPresentation where
  Sentence := Nat
  proves := KProves
  trueInN := Integration.compactTruth

/-- The formerly open compact prenex interface now has a closed inhabitant. -/
theorem prenexCoverage : Integration.CompactPrenexCoverage :=
  ⟨CompactNormalization.coverage⟩

def normalization : NormalizationCertificate compact where
  valid := CompactMatrix.valid theoremCode
  matrix := CompactMatrix.matrixTruth theoremCode
  origin := by
    intro n p _ hv
    exact ⟨theoremCode p,theorem_origin p,Integration.normalized_prefix n p hv⟩
  coverage := by
    intro f hf
    obtain ⟨n,g,r,hn,hg,hr,ht⟩ := prenexCoverage.coverage f hf
    obtain ⟨p,hp⟩ := theorem_coverage hg
    have hv : CompactMatrix.valid theoremCode n p := by
      simp [CompactMatrix.valid,hp,hr]
    exact ⟨n,hn,p,hv,ht.trans (by simpa only [hp] using Integration.normalized_prefix n p hv)⟩

theorem emitted_relation :
    EmittedRelation normalization (Source.recordValues Integration.value) := by
  intro n p xs _ hlen
  exact CompactMatrix.record_spec theoremCode n p xs hlen

def bottomCertificates : BottomCertificates compact where
  bottom := (1 : Nat)
  falseInN := CompactSemantics.realize_one (fun _ => 0)
  valid := Integration.bottomValid
  origin := CompactMarker.marker_origin
  coverage := CompactMarker.marker_coverage

theorem zero_emitted_relation :
    ZeroEmittedRelation bottomCertificates .compactSuffix Integration.events := by
  intro p
  simp [ZeroReceipt,Integration.events,Source.emitted_exact,Admissible,
    bottomCertificates,Integration.bottomValid]

/-- Structural equivalence, including the actual completeness and validity
guards. The reverse direction uses constructed finite normalization proofs. -/
theorem source_iff_sound :
    SoundnessAcceptance .compactSuffix Integration.events ↔ compact.Sound :=
  Source.acceptance_iff_sound normalization bottomCertificates Integration.value
    emitted_relation .compactSuffix zero_emitted_relation

theorem source_formulas_iff_sound :
    FormulaAcceptance .compactSuffix Integration.events ↔ compact.Sound :=
  Source.formulaAcceptance_iff_sound normalization bottomCertificates Integration.value
    emitted_relation .compactSuffix zero_emitted_relation

theorem source_omega_iff_unsound :
    Q_omega .compactSuffix Integration.events ↔ ¬ compact.Sound :=
  observer_omega_iff_unsound normalization bottomCertificates
    (Source.recordValues Integration.value) emitted_relation .compactSuffix
    Integration.events (Source.recordsAgree Integration.value) zero_emitted_relation
    Integration.source_complete

/-- No compact conclusion is omitted: the source quantifies over all finite
K proofs, not only compact formulas already known to encode arithmetic. -/
theorem source_omega_iff_false_K_theorem :
    Q_omega .compactSuffix Integration.events ↔
      ∃ f, KProves f ∧ ¬ Integration.compactTruth f := by
  classical
  rw [source_omega_iff_unsound]
  simp only [TheoryPresentation.Sound,compact,not_forall,exists_prop]

/-- This direction exhibits the normalization/certificate coverage that was
absent from the earlier one-way failure-origin theorem. -/
theorem false_K_theorem_detected {f : Nat}
    (hp : KProves f) (hf : ¬ Integration.compactTruth f) :
    Q_omega .compactSuffix Integration.events :=
  source_omega_iff_false_K_theorem.mpr ⟨f,hp,hf⟩

/-- Raw certificates are transformed by a total finite postfix extension. -/
theorem normalized_certificate_valid (p : Nat) :
    CompactMatrix.valid theoremCode
      (CompactNormalization.rank (theoremCode p))
      (CompactNormalization.certificateFrom p) := by
  obtain ⟨r,hr⟩ := CompactNormalization.recognized (theoremCode p)
  simp [CompactMatrix.valid,CompactNormalization.certificateFrom_correct,hr]

/-- Exact pointwise equation for the existing raw record computation after
constructive certificate normalization. Tuple size is an explicit premise. -/
theorem normalized_raw_record (p : Nat) (xs : List Nat)
    (hlen : xs.length = CompactNormalization.rank (theoremCode p)) :
    RawMatrix.record (CompactNormalization.rank (theoremCode p))
        (CompactNormalization.certificateFrom p) (Marker.encode xs) = 1 ↔
      ¬ CompactMatrix.matrixTruth theoremCode
        (CompactNormalization.rank (theoremCode p))
        (CompactNormalization.certificateFrom p) xs := by
  rw [RawMatrix.record_eq_encoded,RawMatrix.boolNat_eq_one,
    CompactMatrix.record_spec theoremCode _ _ xs hlen]
  exact and_iff_right (normalized_certificate_valid p)

/-- Semantic normalization preserves the conclusion of the original raw
certificate, while the machine still checks the proof of normalized syntax. -/
theorem normalized_certificate_truth (p : Nat) :
    Integration.compactTruth (theoremCode p) ↔
      Integration.compactTruth (theoremCode (CompactNormalization.certificateFrom p)) := by
  rw [CompactNormalization.certificateFrom_correct]
  exact CompactNormalization.semantics (theoremCode p) (fun _ => 0)

theorem machine_iff_sound {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : ImplementationCertificate Integration.source M) :
    SoundnessAcceptance .compactSuffix (UniformMachine.events cert) ↔ compact.Sound :=
  UniformMachine.acceptance_iff_sound normalization bottomCertificates Integration.value
    emitted_relation .compactSuffix zero_emitted_relation cert

theorem machine_omega_iff_unsound {n : Nat} {M : Shared.Beeping.Machines.Machine n}
    (cert : ImplementationCertificate Integration.source M) :
    Q_omega .compactSuffix (UniformMachine.events cert) ↔ ¬ compact.Sound :=
  UniformMachine.omega_iff_unsound normalization bottomCertificates Integration.value
    emitted_relation .compactSuffix zero_emitted_relation cert

end PASoundness.CompactStructural
