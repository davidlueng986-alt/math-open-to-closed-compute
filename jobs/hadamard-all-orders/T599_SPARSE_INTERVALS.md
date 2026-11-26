# Exact sparse comparators with two intervals at length 599

Let \(p=2m+1\) be an odd prime. Take the Goethals–Seidel source sequences \((s,s\tau,sq,sq\tau)\), where \(\tau\) takes a constant sign on each of two circular intervals of lengths \(a\ge m+1\) and \(b=p-a\ge1\). In each interval we can independently negate \(q\) because the source Gram depends only on equality of \(q\) signs within that interval. The four classes defined by \((\tau,q)\) are a signed partition of the coordinates.

For \(p=599\), exact orthogonality with at most six minority positions of \(q\) is impossible when the intervals have lengths 300 and 299. With arbitrary interval lengths, the parity and row-sum conditions leave only 704 normalized partitions in this sparsity range. A partition specifies the comparator, with the longer interval beginning at position zero. The underlying \(s\) signs still have to be found.

## The reflection-disagreement path

For \(1\le d\le m\), one quarter of the combined source correlation is the signed sum over the pairs at cyclic lag \(d\) in the same class. The eligible pair count must be even for exact orthogonality or for the modular source considered in [T599_COMPARATORS.md](T599_COMPARATORS.md).

Before imposing \(q\), the pair count within the two intervals is \(p-2d\) for \(d\le b\) and \(2a-p\) for \(d>b\). In both cases it is odd. Removing edges whose endpoints disagree in \(q\) changes its parity by the sum of the distance-\(d\) degrees at the minority positions. At a position with endpoint distances \(r,r'\), each endpoint distance \(r\) contributes \([d\le r]+[p-d\le r]\). Modulo two this is \([d\le \min(r,p-1-r)]\) for \(1\le d\le m\). Indeed when \(r>m\), the count is odd exactly for \(d<p-r\). The two endpoint distance contributions of a position are exchanged by interval reflection. Only the disagreement bits on reflection pairs matter.

Label the local positions \(j\) in the longer interval by \(j\), and those in the shorter interval by \(p-1-j\). Their folded distance is the pair of labels under \(S(x)=-1-x\pmod p\), indexed by \(0,\dots,m\). Reflection in either interval is \(R(x)=a-1-x\pmod p\). Each nonfixed pair of \(R\) gives an edge between its two folded vertices. The graph is connected because \(S R\) is translation by \(-a\), which has one orbit for prime \(p\). There are \(m\) reflection pairs and \(m+1\) folded vertices. Each vertex has degree at most two, so the graph is a path. Its endpoints are the fold of the fixed position of \(S\) and the fold of the fixed position of \(R\).

Select the edges on which \(q\) disagrees. The degree sum at the minority positions must be odd at every lag \(1,\ldots,m\). Subtracting successive lag conditions says that the selected edges have odd degree exactly at the folded vertices \(0,m\). This is the unique subpath joining them. Therefore every \(q\) has at least as many minority positions as edges on that subpath. Following the path from \(m\), a representative of its \(k\)-th vertex is \(m-ka\pmod p\) by alternating \(R,S\). Thus the required subpath has length
\[
 L=\min\{r,p-r\},\qquad r=ma^{-1}\bmod p .
\]
If a reflection pair is selected, choose exactly one of its endpoints for the minority set. At each unselected pair, choose either neither or both. A fixed position of \(R\) may be chosen independently. This describes all comparators that pass the eligible-pair parity condition.

## The exact square sum and the balanced split

Exact source orthogonality also requires that the four signed class sums have squared sum \(p\). This follows by summing the combined cyclic correlation over all lags and dividing by four. At \(p=599\equiv7\pmod8\), three class sums must be odd and the sole even class sum must be \(2\pmod4\), by the possible residues of squares. In particular all classes are nonempty. If the two minority class sizes add to at most six, the square sum only allows sizes two and three. Their absolute signed sums are two and three, and the other two sums have absolute values 15 and 19. One can check this by trying the minority magnitudes \(u\le a_0,v\le b_0\) with the parities of the sizes \(a_0,b_0\), and looking for \(599-u^2-v^2\) among the sums of two integer squares. The verifier does this exact check.

When \((a,b)=(300,299)\), the disagreement subpath contains just the reflection edge between the two endpoints of the longer interval. Its minority size is odd and must be three. These three positions consist of one endpoint and a reflected pair. The size-two class of the shorter interval is a reflected pair. All signs in each minority class agree, by their signed-sum magnitudes.

Every within-class separation then has ordinary distance at most 299, so exact vanishing of the cyclic correlations is exact vanishing of their combined ordinary correlations. Evaluate their Laurent polynomial at \(-1\). The same squared sum of 599 now holds for the four *alternating* signed class sums. The reflected pair in the longer interval has opposite parities, so that minority class has alternating magnitude one. The reflected pair in the shorter interval has equal parities, giving magnitude two. The remaining two alternating sums would have squares adding to \(599-1-4=594\), which cannot be a sum of two squares. For example, 11 divides 594 exactly once and is \(3\pmod4\). This excludes the whole balanced two-interval sparse exact branch, including the three-negative modular branch.

## The other interval lengths

The required minority sizes sum to five, so \(L\le5\). Counting placements by choosing the selected endpoints, optional midpoint and full unselected reflection pairs gives the following table. Cyclic shifts are normalized by fixing the start of the longer interval. Reflections are included in the counts.

| Interval lengths | Path length | Disagreements in the two intervals | Candidate partitions |
|---|---:|---:|---:|
| \(300,299\) | 1 | \(1,0\) | 0 by the alternating square sum |
| \(449,150\) | 2 | \(1,1\) | 296 |
| \(499,100\) | 3 | \(2,1\) | 392 |
| \(524,75\) | 4 | \(3,1\) | 16 |
| \(539,60\) | 5 | \(4,1\) | 0 by the minority sizes |

The [verifier](defect12_t599_sparse.py) checks the arithmetic and the counts. These 704 partitions describe the remaining possibilities under these conditions when the two minorities have total size at most six. Exact constructions with larger minorities, with more than two intervals in \(\tau\), or without the \((s,s\tau,sq,sq\tau)\) pattern are outside this exclusion.
