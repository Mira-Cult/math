import PASoundness.Source

/-!
Uniform composition from an effective source relation to an ordinary binary
single-tape machine. Syntax/calculus translations and the local implementation
certificate are explicit premises. None of these theorems assumes theory
soundness, PA in particular, or a whole-machine observer correspondence.
-/
namespace PASoundness.UniformMachine
open Observer UnaryCodec Shared.Beeping.Machines

def events {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) : EventStructure :=
  decodedEvents (eventTrace (machineWordSystem M cert.labels))

theorem complete {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) :
    Complete (events cert) :=
  (implementation_complete_preserved cert).mp (Source.complete value)

theorem rawFailure_iff_source {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) (n : Nat) :
    RawFailure (events cert) n ↔ RawFailure (Source.events value) n :=
  (rawFailure_preserved
    (online_sameReceipts_word (machineWordSystem M cert.labels) cert.physicalBits) n).trans
    (rawFailure_preserved (sameOutput_sameReceipts cert.sameOutput) n).symm

theorem rawZero_iff_source {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) (view : ZeroView) :
    RawZero view (events cert) ↔ RawZero view (Source.events value) :=
  (rawZero_preserved view
    (online_sameReceipts_word (machineWordSystem M cert.labels) cert.physicalBits)).trans
    (rawZero_preserved view (sameOutput_sameReceipts cert.sameOutput)).symm

theorem level_iff_source {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) (n : Nat) :
    Q_n (events cert) n ↔ Q_n (Source.events value) n :=
  and_congr Iff.rfl (and_congr (implementation_complete_preserved cert).symm
    (rawFailure_iff_source cert n))

theorem zero_iff_source {value : Address → Bool} {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) (view : ZeroView) :
    Q_0 view (events cert) ↔ Q_0 view (Source.events value) :=
  and_congr (implementation_complete_preserved cert).symm (rawZero_iff_source cert view)

/-- The reusable machine theorem. `value` must be an actual total computation
for an effective instance; this relational theorem alone does not assert that
every arbitrary function can be implemented. The implementation certificate
supplies finite positive simulation blocks for all required computations. -/
theorem acceptance_iff_sound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (value : Address → Bool) (records : EmittedRelation N (Source.recordValues value))
    (view : ZeroView) (zeroRecords : ZeroEmittedRelation B view (Source.events value))
    {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) :
    SoundnessAcceptance view (events cert) ↔ T.Sound :=
  (implementation_observer_preserved cert view).symm.trans
    (Source.acceptance_iff_sound N B value records view zeroRecords)

theorem formulas_iff_sound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (value : Address → Bool) (records : EmittedRelation N (Source.recordValues value))
    (view : ZeroView) (zeroRecords : ZeroEmittedRelation B view (Source.events value))
    {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) :
    FormulaAcceptance view (events cert) ↔ T.Sound :=
  (formulaAcceptance_iff view (events cert)).trans
    (acceptance_iff_sound N B value records view zeroRecords cert)

theorem omega_iff_unsound {T : TheoryPresentation}
    (N : NormalizationCertificate T) (B : BottomCertificates T)
    (value : Address → Bool) (records : EmittedRelation N (Source.recordValues value))
    (view : ZeroView) (zeroRecords : ZeroEmittedRelation B view (Source.events value))
    {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) :
    Q_omega view (events cert) ↔ ¬ T.Sound := by
  classical
  have hcomp : SoundnessAcceptance view (events cert) ↔ ¬ Q_omega view (events cert) :=
    (acceptance_complement_on_complete view (events cert)).trans
      (and_iff_right (complete cert))
  exact (not_not).symm.trans ((not_congr hcomp).symm.trans
    (not_congr (acceptance_iff_sound N B value records view zeroRecords cert)))

/-- This concludes provability of the designated bottom. It is inconsistency
only for an instance whose designated sentence is actual logical falsity. -/
theorem zero_iff_bottom {T : TheoryPresentation} (B : BottomCertificates T)
    (value : Address → Bool) (view : ZeroView)
    (zeroRecords : ZeroEmittedRelation B view (Source.events value))
    {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) :
    Q_0 view (events cert) ↔ B.ProvesBottom :=
  (zero_iff_source cert view).trans
    (levelZero_exact B view (Source.events value) zeroRecords (Source.complete value))

/-- No arithmetic-hierarchy calibration is smuggled into machine refinement.
The named bridge must supply both rank-specific syntactic directions. -/
theorem positive_level_iff {T : TheoryPresentation} (N : NormalizationCertificate T)
    (value : Address → Bool) (records : EmittedRelation N (Source.recordValues value))
    (level : Nat → T.Sentence → Prop) (bridge : FiniteLevelBridge T N level)
    {states : Nat} {M : Machine states}
    (cert : ImplementationCertificate (Source.source value) M) (n : Nat) (hn : 0 < n) :
    Q_n (events cert) n ↔ LevelUnsound T level n :=
  (level_iff_source cert n).trans
    (positive_level_calibration N (Source.recordValues value) records (Source.events value)
      (Source.recordsAgree value) (Source.complete value) level bridge n hn)

end PASoundness.UniformMachine
