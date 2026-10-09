# AME(6,2) in Lean

A Lean 4 proof that an absolutely maximally entangled state of six qubits exists. It proves `ame_6_2_exists` from Open Quantum Problem 35 in Google DeepMind's [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) against their own definitions.

## The result

An AME(6,2) state is a state of six qubits where any three of them on their own look completely random. The witness here is the prism graph state. The prism has two triangles, 0 2 4 and 1 3 5, joined by the rungs 0 3, 1 4 and 2 5. Its amplitudes are ±1/8, with the sign (-1)^(number of edges with both ends 1).

This is a known result (A. J. Scott, Phys. Rev. A 69, 052330, 2004). Six is the largest number of qubits for which an AME state exists (F. Huber, O. Gühne and J. Siewert, Phys. Rev. Lett. 118, 200502, 2017). The prism state is Scott's hexacode state up to local operations on individual qubits. `checks/hexacode_equivalence.py` checks that numerically from Scott's own generator matrix. It's a side check, not part of the Lean proof. AME graph states are studied in W. Helwig, Absolutely Maximally Entangled Qudit Graph States (arXiv:1306.2879, 2013). I found no earlier formal proof. The Lean proof is new. The mathematics isn't.

## The proof

Formal Conjectures' definition asks for a maximally mixed reduction after every one of the 720 permutations of the parties. The proof doesn't check them one by one.

- `AME62/Reduction.lean` proves two general facts, for any number of parties, local dimension and block size. Whether a reduction is maximally mixed depends only on which parties are kept, not their order. And a permutation that leaves the state unchanged can be composed in freely. That takes 720 permutations down to 20 sets of three kept parties.
- `AME62/Sign.lean` shows rotating the parties maps the prism to itself. It then holds the one finite fact, for four permutations keeping 0 1 2, 0 1 3, 0 1 4 and 0 2 4: the traced sum of sign products is 8 on the diagonal and 0 off it. The Lean kernel checks these with `decide +kernel`.
- `AME62/Cover.lean` shows every set of three parties is a rotation of one of those four. So the 20 sets come down to 4.
- `AME62/State.lean` defines the state and proves it's normalised and unchanged by rotation.
- `AME62/Existence.lean` proves every three party reduction is I/8.
- `AME62/FormalTarget.lean` puts it together as `AME62.ame_6_2_exists : ExistsAME 6 2`.
- `AME62/Control.lean` drops the rung 0 3 and proves the resulting state is not AME. So the check isn't passing for a trivial reason. `AME62.lean` imports it so the checks below cover it. The main result doesn't depend on it.

The statement is the same term as Formal Conjectures' `OpenQuantumProblem35.ame_6_2_exists`. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.

## Building

It needs Lean v4.33.1 and depends on Formal Conjectures at commit `40a8592c`.

```
lake exe cache get
lake build
```

A fresh build first compiles Formal Conjectures' support library, which took about ten minutes here. Building this project after that took about nine minutes, nearly all of it loading Mathlib. The kernel checks themselves take seconds. On a machine with limited memory set `LEAN_NUM_THREADS` to a small number first.

To rerun the checks, one at a time:

```
lake env lean audit/Audit.lean
lake env lean audit/Vacuity.lean
python audit/lexical.py
lake exe runLinter AME62
lake exe lint-style AME62
python checks/hexacode_equivalence.py
```

The last one needs numpy.

## How it was made

I used Claude Code to draft the Lean. I've checked every line myself and can explain all of it. I checked the witness numerically before writing any Lean.

## About

I'm Zayn Blore. My main project is [csd-lean4](https://github.com/zblore/csd-lean4), the Lean library behind my work on Constraint-Surface Dynamics.
