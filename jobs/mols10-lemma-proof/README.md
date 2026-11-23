# E074 odd-order four-layer rigidity obstruction

Let four OA(25,5,5,2) layers be coarsened rows and assign a bit to each symbol occurrence. A coarse pair bucket has one row per layer. Fine orthogonality means the two bits run over all four binary pairs, so each direction induces one of three nonzero partition colors in F2^2, namely (b0+b1,b0+b2). The two colors are unequal.

If three directions are fully rigid (the color for each coarse fibre is independent of the other direction and its symbol), their nonempty color sets are pairwise disjoint. There are only three colors, so each has one constant color and all three are different. Label them (1,0),(0,1),(1,1).

Choose any fibre of a fourth direction. Each of the three rigid directions gives five buckets, reindexing the same five rows in every layer. Hence the vector sum of the five colors is independent of which direction is used. Avoiding (1,0) makes the second component of every color 1. Avoiding (0,1) makes the first component 1. Since five is odd, the common vector sum is (1,1). But avoiding (1,1) forces the component sum of each color to be 1, and hence that of the common sum to be 1, contradiction.

The Lean source formalizes the bit-level orthogonality implication, odd-five parity contradiction, permutation invariance and the resulting forbidden three-color fibre condition. It does not formalize the complete reduction from arbitrary OA10 to four layers; no such reduction is known. The original problem remains OPEN. No novelty claim until literature review.