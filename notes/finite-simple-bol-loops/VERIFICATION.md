# Evidence and publication policy

The public workspace distinguishes:

- **Classical imported theorem:** an existing published result, with exact locator.
- **Proof draft:** a proposed new argument available for inspection.
- **Scoped model review:** a separate model examined named statements at a named revision.
- **Reproduced finite check:** a stated command and input were rerun; this does not certify a universal theorem.
- **Human expert review:** only claimed when a named, consenting expert actually supplied it.
- **Formal verification:** only claimed for an identified theorem checked by a specified kernel and imports.

These labels are not a single confidence ladder. A computation cannot repair a
missing universal argument; a proof review does not establish novelty; a source
statement can change after the reviewed revision.

## Release gate for each result

Before a construction enters the public catalogue, include its complete proof
dependencies or immutable accessible public references. Record the source commit,
exported file hashes, transformations made during export, exact reviewed source
revisions, and this release's audit limits. Do not publish an inaccessible private
link as a substitute for an argument.

Read every exported file for unrelated private content and credentials. Do not
export raw conversations, private collaborator information, or speculative
projects merely because they share a source workspace. Preserve mathematical
counterexamples and limitations relevant to the published claims.

The source research remains active. A public snapshot is not a claim that every
later branch update is covered by its review. Corrections should name the affected
statement and revisions and explain whether downstream results change.
