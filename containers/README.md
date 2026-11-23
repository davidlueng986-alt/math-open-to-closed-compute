# Prebuilt math toolboxes

Build math toolboxes builds and smoke-tests three images and publishes them to GHCR.
It runs when container files change on main and can also be started manually.

- math-compute-sat: pinned SMS/Glasgow, PySMS, PySAT, Z3, MiniSat, nauty, C++, GMP, NumPy and NetworkX.
- math-compute-sage: SageMath 10.6, GAP, PARI/GP and Singular, plus nauty, Z3 and MiniSat.
- math-compute-lean: Lean 4.36.0 and mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842 with compiled cache in /opt/mathlib4.

Use Actions > sharded-toolbox-run and select a toolbox plus job and shard options.
The original sharded-run is still available. Jobs still run their own setup.sh.
Direct SAT setup skips its build when the pinned SMS toolbox is available.

For compatible Lean proofs use cd /opt/mathlib4 and lake env lean /path/to/file.lean.
Other toolchain or mathlib versions require their matching dependencies and cache.

Each image has latest and sha-<commit> tags. Use the SHA tag for reproducibility.
GHCR package visibility and permissions are managed through GitHub Packages.
Images need an initial successful publish before use. Large images can take time to pull.
