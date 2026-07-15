# Comparator Setup

This repository has one comparator target:

- `Comparator/config.json`

The challenge module is `Showcase`, which imports the mathematical
prerequisites but not the final proof module and states the two parts of
Theorem 1.4 with intentional `sorry` bodies. The solution module is
`Solution`, which repeats the same public surface and bridges it to
`JoseSmoothest.Challenge`.

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
