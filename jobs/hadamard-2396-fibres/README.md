# A width-12 Hadamard core at order 2396

This job tests the trivial Walsh component in the three-mixed-fibre construction on the Klein four-group times the additive group of the field with 149 elements. It follows §5.6 of the [order-668 construction](https://hexagonmath.org/2611.00637v1). Three sequences have a spike of magnitude 1 at zero. The fourth has a spike of magnitude 2 there. Outside zero their values are 0 or ±2. The combined periodic autocorrelation must be 599 at zero and zero at every nonzero shift. A solution to this projection would still need three other compatible Walsh components and a border.

The base supports comprise four cells of a four-by-four array of block indices and quartic multiplicative cosets. Signs are free at every point. The second census moves one occupied position to any vacant nonzero position, including across blocks. The pure fibre in the fourth block stays at zero. There are 1,820 base patterns and 119,595,840 distinct labelled one-exchange patterns. Distinct bases differ in at least 74 membership bits, so their one-exchange neighborhoods do not intersect.

The three mixed blocks may be permuted. An individual row may be reversed, and all rows may be scaled together by any nonzero field element. These operations preserve their summed autocorrelations. Using them gives 46 base representatives. After choosing a removed coset in a base, quartic scaling acts freely and transitively on its 37 points, so it suffices to remove one designated point and try all 444 additions. Each base representative has 1,776 move representatives.

For a shift s, let C be the sum of support overlaps of the four pure parts, including the fourth origin. Let L be the number of occupied spike neighbors at s and −s in the first three rows. Let B count the negative signs at these neighbors and let A be the sum of negative-bit incidences weighted by the two shifted supports. Expanding the autocorrelation modulo 16 gives

```
L even,    B + 2 A = C + L/2 (mod 4).
```

The parity equation is always linear over the binary field. If L = 2, the two negative bits agree when B is even, and then B/2 equals either bit. If B is odd, B = 1. This supplies a second linear equation. For L above 2 only the parity equation is used. Gaussian elimination gives affine expressions for individual signs. We test the exact norm 599 against bounds on individual row sums and sums and differences of pairs of rows. The bounds allow a separate sign for each distinct linear expression, so a rejection is sound even when the expressions are dependent. For at most 16 free bits the code checks the entire affine space and tests the autocorrelations exactly. Larger unexcluded spaces are explicitly counted as unresolved. The collector directly rechecks every reported projection by integer scalar products.

```bash
bash jobs/hadamard-2396-fibres/run.sh 0 1 /tmp/hadamard-census/shard-0
python3 jobs/hadamard-2396-fibres/merge.py /tmp/hadamard-census /tmp/hadamard-summary
```

Requires only Python 3. Use the repository's sharded-run workflow to split the 46 base classes. The published result includes the counts for every disposition and representatives of any unresolved or exact projection.
