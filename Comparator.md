# Comparator Setup

This repository has one comparator target:

- `Comparator/config.json`

The challenge module is `Showcase`, which imports the mathematical library
but not the final `Solution` module. One imported module already contains an
internal proof of the showcased sixth-order reduction; the comparator's role
is to check that `Solution` exposes the exact requested statement surface and
uses only the permitted axioms. `Showcase` defines the iterated difference
operator and states four checked results with intentional `sorry` bodies: the
inequality, equality characterization, unique attainment, and the sixth-order
operator-to-polynomial reduction. The solution module repeats the same public
surface and bridges it to the sorry-free mathematical library.

Run the check with:

```bash
./scripts/run_local_comparator.sh
```

If the tools are not installed locally, use:

```bash
./scripts/setup_local_comparator_linux.sh
```

The setup script installs local copies under `.proof-audit-tools/`, pinned to
versions compatible with Lean `v4.32.0`:

- comparator: `07bc4ea40f2266dcb861820a2ec1fa3244ed307f`;
- lean4export: `4e7915201d3f9f04470d9eae002fa695f7cdc589`;
- landrun: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`.

The comparator invocation uses the real landrun sandbox. When checking
genuinely adversarial source, also follow comparator's current outer
`systemd-run` hardening guidance.
