# Original correlations on the two abelian groups of order 1197

An abelian Legendre pair consists of two sign functions of sum 1 with combined periodic autocorrelation −2 at every nonidentity group element. Both abelian groups of order $1197=3^2\cdot7\cdot19$ are tested here. The cyclic group is $C_{1197}$. The second group is $C_3^2\times C_7\times C_{19}$. There are 598 independent equations in each case.

Let $A,B$ be the group-developed sign matrices. Their row and column sums are 1 and they commute. With $e$ the column of 1197 ones, an exact pair would give the following matrix of order 2396.

$$
\begin{pmatrix}
1&1&e^T&e^T\\
1&-1&e^T&-e^T\\
e&e&-A&-B\\
e&-e&-B^T&A^T
\end{pmatrix}
$$

Its last two block rows have diagonal Gram blocks $2J+AA^T+BB^T$ and vanishing cross block $AB-BA$. The first two rows are orthogonal to each other and to every remaining row. Consequently zero full error certifies the required Hadamard matrix.

Positions in the elementary-3 case have coordinates $((i\bmod9)\mathbin{\mathrm{div}}3,i\bmod3,i\bmod133)$. The optimizer implements their addition using a carry correction. The checker reconstructs that law from Cartesian coordinates and independently computes its correlations by conditional bit rotations. It checks every winning sign mask, group, raw score and quotient score. [Integer checker and group census](audit_group.py)

For a nonzero shift $s$ and negative supports $S,T$ of size 598, the defect divided by four is $|S\cap(S+s)|+|T\cap(T+s)|-597$. The solver precomputes the integer second derivatives with respect to orbit membership. Exchanges preserve both cardinalities. Annealing permits one orbit of size three or nine to exchange with three smaller ones. Polishing tests paired exchanges across the two words with their exact interaction. The score counts each original shift pair once, including its multiplicity inside a multiplier orbit. [Search](orbits.cpp)

The 18-shard job covers every candidate subgroup of order nine, every candidate of order three, and a search with the trivial multiplier on both groups. These subgroups are representatives after a basis change in the elementary-3 factor. Every shard tries 22 schedules on each group law. Results include the full original sign masks and all 598 correlations can be recomputed. The sampled sign assignments occupy a small part of each search space. [Search schedules](scan_groups.py) · [Scalar recheck at collection](merge.py)

~~~sh
bash jobs/hadamard-2396-abelian/run.sh 0 18 /tmp/hadamard-abelian/shard-0
mkdir -p /tmp/hadamard-abelian-result
python3 jobs/hadamard-2396-abelian/merge.py /tmp/hadamard-abelian /tmp/hadamard-abelian-result
~~~
