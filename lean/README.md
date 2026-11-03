# An end-to-end Lean proof for subcubic lobsters

The main theorem is Lobster.every_subcubic_lobster_is_graceful in GraphTheorem.lean. It applies to a finite undirected simple graph G that is a tree, has maximum degree at most three, and has a simple path within graph distance two of every vertex. The path may consist of one vertex. The proof does not require a matching, an input word, a diameter supplied by the caller, or a bound on the tree order.

For a tree with n vertices, IsGraceful asks for two bijections. The first sends the vertices to Fin n. The second sends the actual unordered edges of G to Fin (n-1). On each edge its second index plus one must equal the absolute difference of its two vertex labels. Adding one expresses the positive edge interval using Lean's zero-based Fin type.

## Reproduce

Install elan and Git. From this directory use the pinned Lean 4.33.0 toolchain. The first command fetches prebuilt mathlib dependencies for the graph modules used here. The second builds the local source, including the finite certificate checks.

    lake exe cache get Mathlib.Combinatorics.SimpleGraph.Acyclic Mathlib.Combinatorics.SimpleGraph.Metric
    lake build

Mathlib is pinned to v4.33.0 and the lockfile pins its dependencies. The first build requires internet access for these dependencies. To repeat all local checks after a successful build, run lake clean lobster_certificate followed by lake build. The final build target prints the axioms of the main theorem.

## Proof map

| File | Result |
| --- | --- |
| GraphTheorem.lean | Formal statement in terms of mathlib SimpleGraph, graph distance, and bijections. Uses the tree edge-count theorem to pass from witnesses for every difference to a bijection on all edges. |
| PathReduction.lean, Fibres.lean, NamedSpine.lean | Choose a maximal witnessing path. Its endpoints admit no off-path neighbors. Each interior vertex has at most one available neighbor, and each off-path head has room for at most two children. A choice of parents partitions the original vertices into spine cells. Every edge of the resulting spanning construction is an original graph edge. |
| Transport.lean, Strips.lean | Give the cells explicit vertices and edges. Align a certificate-labeled sequence of cells with the named cells of the graph, then use uniqueness of vertex names to transfer all labels. |
| Joining.lean | Prove the interval joining lemma and the complement operation uniformly in the order of the old tree. |
| Assembly.lean | Decode the actual JSON rows as cells. Check the geometric conditions on those decoded cells and prove by induction on a parse that it yields a globally graceful segment. Handle the explicit cap and the zero-port terminal cases. |
| Certificate.lean | Decode the exact table. Validate the 6,104 rows and check closure and acceptance of 278,215 distinct windows under all four letters. Connect each transition to a validated row in the table. |
| Coverage.lean | Prove that the finite window represents all allowable last blocks and that acceptance of all outgoing transitions in a closed set implies a terminal parse for every nonempty word. |

The graph proof uses a maximal witnessing path; it does not need to verify the Python constructor's choice of a diameter. On the graph side it suffices to exhibit every difference on an original edge. A tree has exactly n-1 edges, which makes these witnesses exhaustive and unique. The formal theorem establishes existence of a labeling. The supplemental Python implementation is separately tested.

## Computational trust and provenance

Three finite calculations use Lean's native_decide. They verify the row equations, language closure and acceptance, and the interpretation of the row labels on the decoded cells. Each native evaluation introduces a compiler-trusted axiom, listed by the main theorem's axiom report. The remaining proof is checked by the Lean kernel with the standard propext, Classical.choice, and Quot.sound axioms. There are no admitted proof placeholders. Neither Python nor JavaScript is invoked by the Lean build.

The 250177-byte JSON input has SHA-256 f1e26f8a0944ee8de9fd40fdce9310c2360d3ff7d31236737d1a10dc4403e1d7. It is byte-identical to the rule table in the Zenodo v1 supplement. This formalization was developed after the v1 deposit. It is separate from independent human peer review and from the question of priority.
