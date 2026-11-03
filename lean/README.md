# Lean verification of the Section 3 recurrence

From this directory, with elan installed, run:

    lean -DwarningAsError=true Coverage.lean

Lean 4.33.0 with its standard library suffices. The last line reports that Lobster.coverage depends on propext and Quot.sound. No native decision procedure, external solver, or admitted lemma is used.

A Parsed derivation builds a legal sequence of rules starting at start. Its word index is stored newest first, while the rule relation and the public coverage theorem take words in normal reading order. Each rule consumes one to six letters. A finished block cannot be extended, start cannot be a rule destination, and only finish or port zero is terminal.

Represents gives the meaning of all six history slots, including inactive slots near the beginning of a word. output_exact proves both soundness and completeness of one window transition against Parsed. advance_correct proves that updating the five letters and six history slots preserves their meanings. coverage then derives an accepting parse for every nonempty word from three hypotheses about a proposed set of windows: it contains the initial window, is closed under all four letters, and every outgoing letter yields a terminal destination.

Scope: this file proves the implication for any rule relation. It does not import the concrete JSON table or discharge the closure and acceptance hypotheses for that table. The executable Python and JavaScript checks separately evaluate the concrete certificate. Its local label equations, the joining lemma in its entirety, and the graph-to-word reduction are outside this Lean theorem. This is a follow-up to Zenodo v1, separate from its deposited files.
