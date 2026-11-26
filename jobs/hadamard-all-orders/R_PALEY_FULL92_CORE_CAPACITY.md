# A capacity bound for the twelve fixed full92 inner columns

Fix the full92 order-1196 source and the twelve inner columns from the width-1212 contrast construction. The selected exterior may be any 600 physical source indices. We prove that an all-one-flip continuation preserving these twelve inner columns has width at most 1579.

## Repeated reserves

Write $z_i$ for the source column at reserve $g_i$ flipped at raw row $r_i$, and $p_i(g)=\langle z_i,H_g\rangle/2$. From the assembly formula, two added columns are orthogonal exactly when

$$
2\sum_{g\in X}p_i(g)p_j(g)+\langle z_i,z_j\rangle=0.
$$

The reserve is outside $X$ since $|p_i(g_i)|=597$. Two compatible one-flips have different raw rows. If the row and reserve both agree, their columns coincide. With the same row and different reserves, the raw dot is zero but the 600 selected projection products have a common sign.

If two one-flips at distinct raw rows $r,s$ share a reserve $g$, the raw dot is 1192. On the 600 selected indices the exterior row dot, after each of the two rows is normalized at $g$, must be $-596$. On the full physical source the two normalized rows disagree on exactly 598 indices. Thus $X$ contains the entire 598-index sector having relative disagreement at $g$, plus two indices from the other sector.

For two new raw rows, their common reserve must have each row's unique prescribed old-twelve signed profile from the parity formula in the width-1217 proof. We check all raw pairs sharing such a profile and every physical non-old reserve in it. We separately check a new raw row sharing any old reserve with its fixed old root. Each required sector either contains an old reserve or has normalized old-old exterior Gram magnitude greater than two for some pair. Two added indices can change any given old-old dot by at most two. Since the old twelve frame is skew, every such Gram entry must be zero. Therefore repeated reserves are impossible in this continuation.

The integer replay checks 9510 new/new and 14208 old/new triples. Of these, 4972 and 14199 require a forbidden old reserve, respectively. In the remaining 4538 and 9 cases, an old Gram entry exceeds the magnitude bound.

## Exact bound including the old Gram

For each signed old-twelve profile $a$, let $C_a$ be its physical capacity after deleting the old reserves. Let $d_a$ count all new raw rows prescribing it, and $x_a$ be its selected exterior count. Since reserves are distinct, at most $\min(d_a,C_a-x_a)$ extra inners use the profile. The old Gram gives $Ax=(600,0,\ldots,0)$, with one total-count row and the 66 pair-product rows.

Use the integer weights $w$ in the checker and scale $D=100000$. Put $s_a=w^\mathsf{T} A_a$. Over an allowed exterior, $w^\mathsf{T}Ax=600w_0$. Consequently

$$
D\sum_a\min(d_a,C_a-x_a)
\le
600w_0+\sum_a\max_{0\le z\le C_a}
\bigl(D\min(d_a,C_a-z)-s_a z\bigr).
$$

Each maximum occurs at an endpoint or the single breakpoint. The right-hand side evaluates to 36701330. The number of further inners is an integer, so it is at most 367. Adding the 1200 exterior and border columns and twelve fixed inners gives 1579. For the specific old-twelve exterior histogram of the width-1217 branch, the capacity sum directly gives 236 further inners and width at most 1448.

The bound applies to this source and the twelve immutable inner columns. Altered anchor lines or other lower-word types remain available.
