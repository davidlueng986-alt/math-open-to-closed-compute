# Nonzero lower correlations in the Paley completion

Let $t$ be odd, $m=2t-2$, and $H$ be the lower Hadamard matrix
used in the [Paley outside construction](R_PALEY_PROJECTIVE_LIFT.md).
Normalize its unused column $\gamma$ to all $+1$. Write $W$ for
the $t$ selected columns and $V$ for the $t-3$ other columns.
An extra inner column is $(u,-u,z,+1,+1)$, where $u,z$ are sign
vectors of lengths $t,m$, respectively, and

$$
W^{\mathsf T}z=-2u,\qquad \gamma^{\mathsf T}z=-2.
$$

Two such columns are orthogonal when
$2u_i^{\mathsf T}u_j+z_i^{\mathsf T}z_j+2=0$.

## A compatible pair with a shared source

Suppose $t\ge5$. Take a normalized column $g\ne\gamma$ and two
different rows $r,s$ where $g$ is positive. The row disagreement
set $D$ has $t-1$ columns and excludes $\gamma,g$. Choose $W$
to consist of $D$ and one column where the rows agree other than
$\gamma,g$. This leaves $g$ unused. Let $z_r,z_s$ be the results
of flipping $g$ at $r,s$, respectively. The two upper vectors
are the corresponding rows of $W$, since $W^{\mathsf T}g=0$
and the flipped entries of $g$ are positive. Both lower sums are
$-2$. Their upper dot product is $2-t$, while their lower dot
product is $m-4=2t-6$. The full dot product is zero.

With the existing outside and two fixed columns this gives width
$2t+4$. Its lower pair is highly correlated. In a family with all
lower pairs orthogonal, the upper Gram on $k$ extra columns is
$(t+1)I_k-J_k$. Its positive semidefiniteness implies $k\le t+1$,
which restricts that construction to width $3t+3$.

## Width 1213 at order 2396

A separate witness enlarges the [mixed width-1212 construction](R_PALEY_ANCHORED_TRIPLES.md)
using a new selection of $W$. It keeps that witness's eleven
single flips and one triple flip. The additional candidate is the
single flip at lower row 728 of lower source column 794, with
zero-based indices. In its twelve new lower pairs, nine products
are $-4$ and three are $+4$. The corresponding upper products are
$1$ and $-3$, respectively, so the upper block compensates for
each lower product.

The selection used signs of the upper candidates at each eligible
column of $H$, divided by the first upper candidate's sign.
Fixing the number selected in each of the resulting nine-bit
profile classes preserves all margins and pair intersections of
those nine bits. The remaining class cardinalities, margins,
and pair intersections form an exact integer selection problem.
The witness replaces 91 selected indices and is recorded as a
bit mask. Its replay checks all 735078 column dot products and
the SHA-256 of the packed $2396\times1213$ rectangle.

## Distance required in a full completion

Fix one unused normalized source $g$ in $V$. Suppose three
distinct compatible inner columns have lower words $z_1,z_2,z_3$
at distances at most $\rho$ from the line $\{g,-g\}$.
Write $z_i$ as $\varepsilon_i g$ flipped on $S_i$, where
$\varepsilon_i\in\{+1,-1\}$ and $|S_i|\le\rho$.
For $d_{ij}=|S_i\triangle S_j|$,

$$
z_i^{\mathsf T}z_j=\varepsilon_i\varepsilon_j(m-2d_{ij}),\qquad
(\varepsilon_i u_i)^{\mathsf T}(\varepsilon_j u_j)
=-(t-1)+d_{ij}-\varepsilon_i\varepsilon_j.
$$

In each position the sum of three signs is odd, so
$\|\sum_i\varepsilon_i u_i\|^2\ge t$.
At most two of the three pairs have opposite orientations,
and $\sum_{i<j}d_{ij}\le 2\sum_i |S_i|\le6\rho$.
Consequently,

$$
t\le\left\|\sum_i\varepsilon_i u_i\right\|^2
\le -3t+12\rho+8.
$$

If $\rho<(t-2)/3$, a set of mutually orthogonal inner columns
therefore contributes at most two words per unused source line.
The total within that radius of any of the $t-3$ lines in $V$
is at most $2t-6$.

The absolute inner products of a candidate $z$ with each column
of $W$ and with $\gamma$ are exactly 2, so the distance from
each of those source lines is $t-2$.
For $t=599$, use $\rho=198$. A full completion requires
$m=1196$ extra columns, while the union of radius-198 balls around
all signed sources can contain at most 1192 compatible lower
words. At least four lower words therefore have Hamming distance
at least **199** from every signed source column of $H$.
This applies to any selection of $W,\gamma$ in the Paley outside
construction.

Run `python jobs/hadamard-all-orders/r_paley_nonzero_lower.py` to
verify the exact width-1202 and width-1213 witnesses and the
distance arithmetic.
