# Phase-compatible short lifts: standalone Lean package

This package proves a lift-selection lemma for every permutation on `Fin n`, `n > 0`. It minimizes the integer quadratic energy over **all balanced, phase-compatible lifts**, obtains all subset bounds, and derives strict shortness. It does not minimize the affine inversion number C, construct an L/R/X route, pay cursor motion, or prove an upper bound or a diameter equality.

Source and author build log are preserved byte-for-byte. The successful original compilation used the existing authorized research node, Lean 4.34.0 and Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`. The lock file was copied exactly from that build environment and all nine installed dependency commits were read back and matched to it. No remote credentials, service configuration, private messages or other participants' source packages are included.

The portable Lake target name is new packaging metadata; it does not alter the checked `.lean` source or dependency lock. Packaging verified hashes and structure, without claiming a second independent compilation. Independent reviewer A is pending.

## Reproduce

With Python 3 and an installed Lean/Elan toolchain manager, from this directory:

```sh
python3 verify.py
lake exe cache get
python3 verify.py --lean
```

`lake exe cache get` retrieves pinned public dependencies and cached dependency objects; it requires network access. Do not run `lake update`, which would re-resolve the recorded lock. `verify.py --lean` requires those dependencies, runs `lake env lean UpperLiftSelection.lean`, and verifies the four expected axiom reports. The Lean compiler checks the whole file. Its axiom dependency report is explicitly printed for `initial_lift`, `exists_energy_minimizer`, `shift_energy`, and `exists_majorized_short_lift`, each containing only `propext`, `Classical.choice`, `Quot.sound`.

The default hash check does **not** execute Lean and is not mathematical verification. There is no claim of an independent Mathlib rebuild or a new independent review. See the adjacent result record for exact theorem, proof outline, attribution and integration obligations.

## Export inventory

Namespace `LRX.UpperLiftSelection`; definitions `Balanced`, `Compatible`, `Energy`, `Shift`; theorems `energy_nonneg`, `initial_lift`, `exists_energy_minimizer`, `sum_indicator`, `shift_balanced`, `shift_compatible`, `shift_energy`, `minimizer_subset_bound`, `subset_bounds_short`, `exists_majorized_short_lift`.

The two conditional helper bounds assume an energy minimizer or subset bounds respectively. The final existence theorem discharges those assumptions internally; it assumes only the permutation and `0 < n`. `Compatible` uses an integer phase; normalization and its interpretation in a paid LRX route are outside this file.
