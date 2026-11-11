# Shannon's circle construction is a growing hexagon (OEIS A374338, A374337, A400701)

This repository contains proofs, machine-checked in Lean 4, of the formulas conjectured in OEIS [A374338](https://oeis.org/A374338) and [A374337](https://oeis.org/A374337) (S. R. Shannon, 2024), and in [A400701](https://oeis.org/A400701) (A. Markey, 2026).

**The construction.** Start with two points at distance 1 and draw the unit circles around them. At each iteration, draw a unit circle around every new intersection point. After n iterations, count the vertices V(n) (A374338), the arcs E(n) (A374339) and the bounded regions R(n) (A374337).

## Results

With c_n = 0, 4, 2 for n ≡ 0, 1, 2 (mod 3), for all n ≥ 1:

- **V(n) = (3n² + 5n + c_n)/3** (Shannon's conjecture);
- **R(n) = (15n² − 17n − 3)/3, |15n² − 17n − 7|/3, (15n² − 17n + 7)/3** for n ≡ 0, 1, 2 (mod 3) (Shannon's conjecture);
- E(1) = 6 and, for n ≥ 2, **E(n) = 6n² − 4n + 2** if n ≡ 2 (mod 3), **6n² − 4n − 2** otherwise;
- **A400701(n) = (3n² + 17n + 21 + c_n)/3 = A374338(n) + 4n + 7** for n ≥ 2 (Markey's conjecture and the closed formula of the entry).

**Key idea.** Unit circles centred at points of the triangular lattice meet only at lattice points, so the construction is two-neighbour growth on that lattice. After n ≥ 1 iterations, the vertex set is exactly the set of lattice points of the hexagon

  |u| ≤ n,  |u| + 3|y| ≤ 2n + 1   (u + y odd),

in suitable coordinates. Counting its points, its arcs and its regions (by Euler's formula) gives the formulas.

## Contents

| File | Description |
|---|---|
| `A374338_paper.pdf` | The paper (English): proofs, prior work, credits |
| `A374338_paper.tex` | LaTeX source of the paper |
| `A374338.lean` | Lean 4 formalization (925 lines) |
| `checks/simulation_cercles.py` | Independent floating-point simulation of the actual circles (no lattice assumption) |
| `checks/references_oeis.csv` | Published OEIS terms used by the simulation |

## What is formalized

The Lean file defines the construction **geometrically in ℂ** (a point is added when it is at distance 1 from two distinct existing vertices) and proves:

```lean
theorem shannon_geometric_vertices (n : ℕ) (hn : 1 ≤ n) :
    (((circleStep^[n]) (toPlane '' (seedShannon : Set Site))).ncard : ℤ) =
      (3*(n : ℤ)^2 + 5*(n : ℤ) + correction n)/3
```

It also proves:
- the lattice lemma for circle intersections;
- the exact hexagonal shape for both seeds;
- the formula for the edges (defined as the sum of circle–vertex incidences);
- the formula for the regions (defined as E − V + 1);
- Markey's relation.

**Not formalized:** the identification of the arcs of the drawing with these incidences, and Euler's formula. Both are proved on paper.

## How to check

Requirements: Lean `4.36.0-rc2` and Mathlib commit `9d581dfff2e41de989072ea63abf3daf69311520`.

```bash
lake env lean A374338.lean
```

Expected result: no errors and no `sorry`, and `#print axioms` reports only `[propext, Classical.choice, Quot.sound]` for the main theorems.

SHA-256 of `A374338.lean`:
`3f07ccdda3e15e6d76270ec9deb8134314c1c8ac8f7192e5aaf6b94c071e0b4a`

Independent simulation (Python 3):

```bash
cd checks && python3 simulation_cercles.py --references references_oeis.csv
```

## Prior work and credits

- The sequences and conjectures are due to **S. R. Shannon** (A374337–A374339) and **A. Markey** (A400701). The closed formula of A400701 is due to **S. A. Irvine**.
- The related entry [A264788](https://oeis.org/A264788) (K. Ngaokrajang, 2015; formulas by C. Barker) counts circles added in a similar construction. We do not claim a proof for that entry.
- The asymptotic shapes of threshold growth models were studied by J. Gravner and D. Griffeath. We found no previous proof of the exact shape or of these formulas.

This work was produced under the pseudonym A-guy-with-AI, in collaboration with AI systems:
- **Claude (Anthropic):** the lattice reduction, the hexagonal shape, the counting and the paper.
- **ChatGPT (OpenAI):** review, the independent geometric simulation, the Lean formalization and the literature search.

## License

MIT, see `LICENSE`.
