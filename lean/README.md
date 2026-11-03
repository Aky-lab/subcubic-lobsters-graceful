# Checking the subcubic lobster certificate with Lean

With elan installed, run the following from this directory:

    lake build

The toolchain is pinned to Lean 4.33.0. There are no external Lean packages. On a fresh build the Certificate target parses the bundled JSON, checks all rows, discovers a set of windows, and checks every outgoing edge of that set. Lake caches successful builds. To force a fresh check use lake clean followed by lake build.

## What the theorem says

Lobster.certificate_universal states that every nonempty word in normal reading order has a parse ending at port zero or at the finished marker. Every block of this parse is witnessed by a row of this specific JSON file that satisfies validRow. Parsed stores the consumed prefix newest letter first, which explains word.reverse in the theorem. There are no hypotheses about the concrete table or its coverage left for the caller to prove.

Coverage.lean proves that the five-letter suffix and six history slots describe all possible last blocks, that finished parses cannot continue, and that an accepting closed set suffices. This abstract proof uses ordinary kernel-checked terms.

Certificate.lean embeds the actual JSON at build time. The computed fact rows_checked requires exactly 6,104 decoded rows, all passing the local equations. The checker rebuilds the block edges, checks the permutation of ordinary labels or the separate class permutations, checks all edge differences or sums, and verifies the specified entry and exit ranks.

The second computed fact, concrete_check, requires exactly 278,215 distinct windows, inclusion of the start window, and acceptance and closure of all four outgoing transitions at every window (1,112,860 transitions). The 47 discovery rounds only propose a set. An inadequate set fails the separate closure check. The proofs ends_exact, child_view and root_view connect the executable states to the abstract proof. The lookup_from_rows and lookup_checked lemmas connect the lookup table to actual validated rows.

## Trust and scope

The two large closed calculations use native_decide, which relies on Lean's compiled evaluation. The file prints the axioms of rows_checked and certificate_universal so this trust choice is visible. The concrete result is not a kernel-only replay of those two calculations. There are no admitted proof placeholders. Neither the Python nor JavaScript verifier is invoked.

The JSON file is byte-identical to subcubic_lobster_rules.json in the Zenodo v1 supplement, with SHA-256 f1e26f8a0944ee8de9fd40fdce9310c2360d3ff7d31236737d1a10dc4403e1d7. The pinned original is 250177 bytes. The publication predates this Lean development.

This theorem certifies the actual rules and the language argument. A formal proof that the local conditions yield a graceful labeling under every join, together with the reduction from an arbitrary subcubic lobster as a graph to its word, would be needed for an end-to-end Lean proof of the graph theorem.
