# Formalization — Markets as Rewriting Systems

Lean 4 mechanization accompanying the paper "Markets as Rewriting Systems: Confluence,
Termination, and the Order-Independence of Decentralized Allocation" (L. R. de Andrade,
working paper, 2026).

## What is verified

`SwapConfluence.lean` has two parts (axiom usage per theorem below, checked via
`#print axioms`; Newman's Lemma and the example are fully axiom-free):

**Part I — `namespace ARS`: abstract rewriting + Newman's Lemma.**
- `ARS.newman : Terminating R → LocallyConfluent R → Confluent R` — **Newman's Lemma**
  (terminating + locally confluent ⟹ confluent), the engine behind the paper's local test for swap dynamics. Proved
  by well-founded induction, with supporting `Star` lemmas (transitivity, head decomposition).

**Part II — `namespace SwapConfluence`: the non-confluence example (Section 4.2).**
- `swap_dynamics_not_confluent : ¬ Confluent Step` — housing-market bilateral-swap dynamics
  is **not** confluent;
- `nonconfluence_witness` — explicit witness: from one initial allocation, two improving-swap
  sequences reach two distinct swap-stable (normal-form) allocations;
- `terminating_Step : Terminating Step` — the dynamics terminates (each improving swap
  strictly raises total utility, which is bounded);
- `swap_step_not_locallyConfluent : ¬ LocallyConfluent Step` — **the capstone**: combining
  termination with Newman's Lemma, the failure of confluence is *necessarily local* — there
  is a non-joinable critical pair (exactly the §4.2 analysis). This is the mechanized form of
  the Proposition 4.4 narrative for the concrete instance.

The example is stated with the *same* `Confluent`/`LocallyConfluent` that Newman relates, so
the artifact is internally coherent: Newman is the general engine; the example is a concrete
terminating system whose non-confluence Newman localizes to a critical pair.

## Axioms (honesty)

Checked with `#print axioms`:
- `ARS.newman`, `swap_dynamics_not_confluent`, `nonconfluence_witness` — depend on **no
  axioms** (fully constructive; atomic facts by `decide`).
- `terminating_Step`, `swap_step_not_locallyConfluent` — depend on `propext` and `Quot.sound`
  (two of Lean's three standard foundational axioms, pulled in by the well-founded-recursion
  library). They use **no `sorry`** and **no `Classical.choice`**.

## Scope

Mechanized: Newman's Lemma (abstract), the concrete non-confluence example, its termination,
and the locality corollary. **Not** (yet) mechanized: the general, `n`-agent critical-pair
reduction of Proposition 4.4 (in particular a "disjoint swaps commute" lemma over an
arbitrary agent set), which would need a general housing-market model rather than the
concrete 3-agent instance.

## Build

Requires `elan` (Lean toolchain manager); the toolchain is pinned in `lean-toolchain`
(Lean 4.30.0).

```
lake build
```

Or typecheck the single file directly (no dependencies):

```
lean SwapConfluence.lean
```
