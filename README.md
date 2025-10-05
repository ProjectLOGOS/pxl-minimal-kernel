<!-- SPDX-License-Identifier: CC-BY-4.0 -->
# PXL Final Proofs

This repository contains the final proofs for the Protopraxic Logic (PXL) system, a modal logic framework.

## Core Phases

- **Phase 1**: Inductive syntax and Prov relation (`PXLv3.v`)
- **Phase 2**: Meta-theorems (`PXLv3_Meta.v`)
- **Phase 3**: S5 Kripke semantics (`S5_Kripke.v`)
- **Phase 5**: Decidability (`PXL_Decidability.v`)
- **Phase 6**: Expressiveness (NNF, Filtration, Intertranslation)

## Phase-6 Expressiveness

Phase-6 kernel is IL-complete with zero admits; classical results live in `PXL_Expressiveness_ClassicalOverlay.v`.

### Guarantees
- **Kernel**: IL theorems, NNF witness with nnf_dirR and nnf_dirL: nnf_out â†’ Â¬Â¬Ï†, filtration â†’ FMP (satisfiability form), conserv_PXL_to_S5 (soundness).
- **Overlay**: DN left, full De Morgan, modal dual reverse, equivalence wrappers, classical macro round-trip.

### Building
```bash
make kernel  # Kernel-only: IL-complete, zero admits
make overlay # Classical extensions
make all     # Both
make hygiene # Fail CI on any Axiom|Admitted outside overlay
```

### Files
- Kernel: `PXL_Expressiveness_Boolean.v`, `PXL_Expressiveness_NormalForms.v`, `PXL_Expressiveness_ModalDuals.v`, `PXL_Expressiveness_Filtration.v`, `PXL_Expressiveness_Intertranslation.v`
- Overlay: `PXL_Expressiveness_ClassicalOverlay.v`

### Hygiene
Zero `Axiom`/`Admitted` in kernel; overlay houses classical strength when needed.

## Triune Overlay

The triune overlay provides theology-neutral proofs of triune grounding formulas using PXL semantics.

### Goals
- Prove necessary co-existence, unity, distinction, and grounded laws of thought.
- Maintain absolute neutrality: no theological axioms in the core.
- Non-intrusion guarantee: overlay can be removed without affecting core proofs.

### Building
```bash
make  # Builds core
coqchk -quiet -R coq PXLs  # Verifies core
```

### Enabling Overlay
To include the triune overlay:
```bash
# The overlay is included in the main build
make
coqchk -quiet -R coq PXLs
```

### Files
- `PXL_TriuneTheory.v`: Definitions and theorem statements.
- `PXL_Completeness_Interface.v`: Thin interface for proofs.
- `PXL_Completeness_Instance.v`: Concrete completeness instance.

### Hygiene
Zero `Axiom`/`Admitted`/`Parameter` in core; overlay has placeholders for proofs.

### Disabling Overlay
Remove `PXL_TriuneTheory.v`, `PXL_Completeness_Interface.v`, `PXL_Completeness_Instance.v` from `_CoqProject` and rebuild.
# PXL Total Packet

- Core phases (15): constructive, self-contained, kernel-verified.
- Phase 4: completeness via localized canonical lemmas (scoped to Phase-4; core hygiene intact).
- Overlays (Triune Theory / Metaphysical Necessity): separate, removable, with admits where they encode extra-logical theses.
- Build: Coq 8.20.1, OCaml 4.14.2.

## Build & Verify
1. Clone: `git clone https://github.com/ProjectLOGOS/pxl-minimal-kernel.git`
2. Open PowerShell in this folder.
3. Run: .\verify.ps1
   - Compiles with coqc (Prelude via -R "C:\Coq-Platform~8.20~2025.01\lib\coq\theories" Coq and logical path -Q coq PXLs)
   - Runs coqchk
   - Runs hygiene scan (Axiom|Admitted|Parameter) and saves hygiene.txt

## Hygiene Policy
- Core files: no Axiom/Parameter; admits only where documented (e.g., decidability/completeness internals if present in your snapshot).
- Overlays: admits may remain for metaphysical statements; they are removable without affecting core.


### Toolchain install (Coq Platform)
Install Coq Platform 2024.09 (Coq 8.20.1). On Ubuntu CI we use `coqorg/coq:8.20.1`.

## License

- Code: Apache-2.0 (see \LICENSE\, SPDX headers in source)
- Documentation: CC BY 4.0 (see \docs/LICENSE\, SPDX headers in docs)
- NOTICE file included for Apache-2.0 attribution.

