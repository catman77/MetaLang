# MetaLang

MetaLang is a Lean 4 and Mathlib formalization of a theory of **admissible
semantic continuations**. It accompanies the WORLD-META research corpus
(v0.3–v0.38) and the paper
[Admissible Semantic Continuations: A Metalanguage of Continuation Structure,
Its Meaning Algebra, and the Limits of Observational Reconstruction](paper/main.pdf).

Author: **Sergey Kotikov**.

## The theory

The starting point is the set of continuations admissible after a history:

$$C(h) = \{x \mid hx \text{ is admissible}\}.$$

Meaning is an effect on continuation structure, a law is a filter on
continuations, and an object is a stable continuation pattern. The formal
development studies the semantic quotients, geometry, algebra, and observer
systems that arise from these definitions.

Two distinctions guide the development: a source is distinct from its
observers, and semantic structure alone does not imply utility or a causal
channel. An observer quotient is legitimate only when it preserves the
required continuation structure.

The observational endpoint is the operational object
$S_{\mathrm{op}} = S / \ker\eta_S$, where $\eta_S$ combines the declared
observers. A complete observer diagram need not determine a unique source.
The quaternion and dihedral groups of order eight provide an explicit finite
witness: their strict-quotient diagrams are isomorphic, although the groups
are not, and their common operational object is the Klein four-group.

## Formal development

| Area | Main contents | Representative modules |
|---|---|---|
| Continuation semantics | Admissible histories, future cones, filters, semantic congruence, internal language, quotient legitimacy | `Continuation`, `Grammar`, `Congruence`, `InternalLanguage`, `Observer` |
| ASC geometry and descent | Distinguishing depth, ultrametrics, refinement, local presentations, reconstruction, and gluing obstructions | `ASCTopology`, `CollapseBridge`, `Descent`, `Gluing` |
| Meaning algebra: reconstruction | Three operation symbols, filtration compatibility, algebraic descent, and transport of equations | `MeaningAlgebra`, `AlgebraicDescent`, `MeaningWitnesses`, `AtlasCocycle` |
| Meaning algebra: reflection and constraints | Reflectors, joint reflection, Moore conditions, implication antichains, and non-distributive condition logics | `Reflection`, `JointReflection`, `ConstraintLogic`, `ConditionLogic`, `FilterLogic`, `SourceFilterLogic` |
| Meaning algebra: observation | Projection descent, joint observer reconstruction, shadow laws, and the equational theory of the operational object | `Projection`, `MultiObserver`, `OperationalAlgebra` |
| Self-reference and boundaries | Partial fixed points, theory presentations, the syntactic diagonal lemma, the Tarski barrier, and obstruction diagnostics | `SelfReference`, `TheorySpace`, `TheoryPresentation`, `BoundaryObject` |
| Operational equivalence | Observer diagrams, the finite group witness, and non-identifiability of the source | `ObservationDiagram`, `Q8D8`, `OperationalEquiv` |
| Language growth and solver extension | Grammar refinement, admissibility versus utility, separation as pair covering, and conditional solver guarantees | `LanguageGrowth`, `GrammarGrowth`, `SeparationCover` |

The meaning algebra therefore has **three checkpoints**: reconstruction
(v0.22–v0.24), reflection and constraint logic (v0.25–v0.27), and
projection and observation (v0.32–v0.38).

The [corpus certificate](formal/final_certificate.json) indexes **336 claims**:
244 proved claims and 92 refuted claims supported by explicit countermodels.
The later solver extension is documented separately in
[PRD_SOLVER.md](formal/PRD_SOLVER.md).

The proof discipline forbids `sorry`, new axioms, and `native_decide`.
Headline theorems depend only on `propext`, `Classical.choice`, and
`Quot.sound`, or a subset of these. Substantive claims have corresponding
failure predicates and proofs excluding those failures. Differences between
the formal statements and the corpus prose are recorded in
[ProofAudit.md](formal/ProofAudit.md).

These results concern the declared mathematical models. They do not establish
that the physical world is a projection of a richer semantic source, that
semantic structure determines utility, or that correspondence supplies a
causal channel. **Gödel incompleteness is neither formalized nor derived**;
the self-reference layer proves a syntactic diagonal lemma and a Tarski
barrier under its stated assumptions.

## Repository layout

| Path | Purpose |
|---|---|
| [`formal/MetaLang.lean`](formal/MetaLang.lean) | Entry point importing the formal library |
| [`formal/MetaLang/`](formal/MetaLang/) | Lean definitions, theorems, countermodels, and audits |
| [`formal/README.md`](formal/README.md) | Detailed module map and local build notes, in Russian |
| [`formal/PRD_BACKLOG.md`](formal/PRD_BACKLOG.md) | Corpus coverage decisions and milestones M10–M17 |
| [`formal/final_certificate.json`](formal/final_certificate.json) | Claim statuses and corpus attributions |
| [`formal/ProofAudit.md`](formal/ProofAudit.md) | Proof audit and explicitly recorded weakenings |
| [`docs/`](docs/) and root-level experiment ZIP files | Immutable published experiments and the research narrative |
| [`paper/`](paper/) | English LaTeX paper, bibliography, compiled PDF, and checks |

The experiment archives are sealed results with pre-outcome hash manifests.
Extract them into a temporary directory for inspection or replay; preserve
the archives and their frozen contents unchanged. The theorem, experiment,
and philosophical interpretation layers remain separate.

## Build the Lean library

Install Lean's [elan toolchain manager](https://github.com/leanprover/elan)
and ensure `elan` and `lake` are on your `PATH`. Dependency downloads require
network access; the optional coverage audit also requires Python 3 and
`unzip`.

The project pins:

- Lean: `leanprover/lean4:v4.29.0-rc8` in [`formal/lean-toolchain`](formal/lean-toolchain).
- Mathlib: `698d2b68b870f1712040ab0c233d34372d4b56df` in [`formal/lake-manifest.json`](formal/lake-manifest.json).

### Fresh clone on another machine

```bash
git clone https://github.com/catman77/MetaLang.git
cd MetaLang/formal
lake update
lake exe cache get
lake build
```

The cache command downloads precompiled Mathlib artifacts, avoiding a full
Mathlib compilation. Allow roughly 1.3 GB for the dependency cache. `lake
build` checks the library imported by `MetaLang.lean`.

### Reuse an existing Mathlib build

On the original development machine, run `setup.sh` **before** the first
build in a fresh checkout:

```bash
cd formal
./setup.sh
lake build
```

By default, the script links packages from
`/home/catman/CatmanCode/SymStructures-RH/.lake/packages`. To reuse a build
elsewhere, pass the directory explicitly:

```bash
./setup.sh /absolute/path/to/existing/project/.lake/packages
lake build
```

The reused build must match the pinned Lean toolchain and dependency
revisions. The links are machine-specific and must be recreated on a fresh
checkout. **Do not run `lake update` after setting up dependency reuse**: it
discards that setup and can trigger a full Mathlib rebuild.

## Check proof dependencies

After building, run the following from `formal/` to inspect the four principal
audit theorems:

```bash
METALANG_CHECK_DIR="$(mktemp -d)"
cat > "$METALANG_CHECK_DIR/axioms.lean" <<'LEAN'
import MetaLang
#print axioms MetaLang.Audit.final_audit_passes
#print axioms MetaLang.AuditM7.ladder_audit_passes
#print axioms MetaLang.AuditM8.algebra_audit_passes
#print axioms MetaLang.AuditM9.projection_audit_passes
LEAN
lake env lean "$METALANG_CHECK_DIR/axioms.lean"
```

Apply the same `#print axioms` command to any theorem of interest.

## Audit corpus coverage

From the repository root, extract each archive into its own temporary
subdirectory and run the attribution sweep:

```bash
METALANG_SCRATCH="$(mktemp -d)"
for archive in docs/*.zip ./*.zip; do
  [ -f "$archive" ] || continue
  unzip -q "$archive" -d "$METALANG_SCRATCH/$(basename "$archive" .zip)"
done
python3 formal/tools/gate_sweep.py "$METALANG_SCRATCH" --list
```

The sweep verified on 4 October 2026 reports 714 scientific gates: 577 with
explicit attributions, zero remaining `FORMALIZE` candidates, and 137
unattributed entries classified as numeric thresholds (41), scope
declarations (22), instrument checks (32), or unlabeled early gates (42).
The classification is heuristic, and unlabeled gates require manual
interpretation. Attribution is a provenance check; it does not make every
experimental gate a Lean theorem.

## Build the paper

With a LaTeX installation providing `pdflatex`, BibTeX, and the packages used
in `paper/main.tex`, run:

```bash
cd paper
bash check.sh
```

This rebuilds `main.pdf` and checks references, citations, and the paper's
writing conventions. Install Poppler's `pdftotext` to enable the additional
check for unresolved marks in the PDF.

## License

MIT License. Copyright (c) 2026 Sergey Kotikov. See [LICENSE](LICENSE).
