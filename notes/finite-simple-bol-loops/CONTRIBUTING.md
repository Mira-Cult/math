# Contributing

Contributions from nonassociative algebra, finite-group theory, representation
theory, computational algebra, and proof verification are welcome. Proofs and
structural ideas matter as much as code. AI use is welcome and should be disclosed.

## A lightweight protocol

1. Open an issue naming a question or a precise statement you want to investigate.
   State whether you seek collaborators. This is coordination, not exclusive ownership.
2. Work in a branch and open a draft pull request for substantial changes. Keep
   existing proofs and counterexamples recoverable; correct them explicitly rather
   than silently rewriting their historical status.
3. Separate the theorem statement, proof, dependencies, computations, and open
   obligations. Include a minimal example and convention notes where helpful.
4. Request review of a specific commit and statement. Reviewers should identify
   unchecked imports and whether they reproduced computational evidence.
5. Update the classification map or open problem board only to the extent the
   accepted result actually changes it. Preserve stronger unanswered questions.

## Minimum result packet

- A self-contained statement with all quantifiers and hypotheses.
- A readable proof, or a clearly identified conjecture and evidence.
- Complete publicly accessible dependency closure for new arguments. A private
  repository link is not an adequate proof dependency.
- Primary-source locators for imported theorems, including convention changes.
- Source code, exact input parameters, seeds, software versions, and reproduction
  commands for computational claims. Preserve negative controls and failures.
- Isomorphism/isotopy conventions and any unresolved redundancy of parameters.
- Attribution for ideas, proofs, code, and review; disclose AI assistance.

## Review report

Specify the exact commit, statements checked, reasoning checked, commands run,
results, and remaining limitations. "No error found" is scoped evidence, not a
blanket endorsement of the project. A model review must be labeled as a model
review, even when performed independently of the authoring model.

Corrections, counterexamples, and prior-art identifications are first-class
contributions. Preserve credit when a conjecture is refuted or a proof repaired.
No new software or document license is asserted by this protocol; preserve the
applicable source attribution and license terms.
