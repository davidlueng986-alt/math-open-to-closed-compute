# Seventeen inner columns on the full92 source

The $2396\times1212$ contrast rectangle has twelve inner columns from the full 92-row skew frame. Three successive exterior reselections preserve all existing inner columns and add one unrestricted one-flip inner each. The new roots lie outside the 92-row frame. Two joint reselections then add a fourth and fifth unrestricted root, giving $2396\times1216$ and $2396\times1217$ rectangles. Each retains the original twelve inner columns and their full signed profile histogram.

| Width | Physical root | Reserve column | Reselected exterior indices | Zero column products | Reserve rank over $\mathbb F_{599}$ |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1213 | 972 | 1027 | 235 | 735078 | 13 |
| 1214 | 1013 | 907 | 56 | 736291 | 14 |
| 1215 | 1066 | 1167 | 36 | 737505 | 15 |

Fix the previously used roots $r_i$ and reserve columns $g_i$. Normalize every source column on those roots by its sign at $r_0$. A group $L$ consists of columns with the same normalized signed vector $L_i$. The counts $m_L$ of selected columns in each group determine every old off-diagonal exterior row product, since each product is $\sum_L m_L L_iL_j$. Each successive step preserves the entire vector $(m_L)_L$ defined by all earlier roots.

For a proposed new root $r$, the sign of a normalized source column at $r$ splits each group into lists with capacities $p_L$ and $q_L$. These capacities omit all previously used reserves and the new candidate reserve $g$. Let $n_L$ be the number selected from the positive list. The exact old-new exterior products are

$$
\sum_L (2n_L-m_L)L_i,\qquad
\max(0,m_L-q_L)\le n_L\le\min(m_L,p_L).
$$

The target for the $i$-th product is

$$
H_{r_i,g_i}H_{r,g_i}+H_{r,g}H_{r_i,g}.
$$

These are linear equations in bounded integers. Each feasible count vector gives distinct physical indices by taking the indicated numbers from the two lists. The target accounts for both reserve contacts, including when the new root is outside the skew frame.

## Joint reselection for widths 1216 and 1217

The additional roots are $972,1013,1066,1051$, with reserves $935,852,523,1106$ in that order. The reserves of the first three additional roots change from $1027,907,1167$. The first twelve inner columns stay fixed. The 600 exterior indices change in 122 places compared with width 1215.

Width 1217 keeps all sixteen physical roots and adds raw row 16. The five unrestricted roots have reserves 1050, 622, 112, 439, and 94 in the order 972, 1013, 1066, 1051, and 16. All four prior unrestricted reserves change. The original twelve inner columns and their signed profile histogram stay fixed. The exterior reselection replaces 216 of the 600 indices from width 1216.

Encode the binary signs of a source column $c$ by $b_c(i)$ after normalizing at the first old root $r_0$. Set $\epsilon_c(i,j)=b_c(i)+b_c(j)$ and $\beta_i=\sum_{c\in X} b_c(i)$ in $\mathbb F_2$. For a pair of roots, the required exterior Hamming distance is $299+\epsilon_{g_i}(i,j)+\epsilon_{g_j}(i,j)$, using the binary representatives of the two $\epsilon$ values. Its parity is $\beta_i+\beta_j$. All twelve old roots have $\beta_j=0$, since their pair distances against $r_0$ equal 300. Comparing the contact at an old root $r_j$ with the contact at $r_0$ gives

$$
b_{g_i}(j)=\epsilon_{g_j}(i,j)+\epsilon_{g_0}(i,0)
\qquad\text{for each old }j.
$$

This specifies the unique old signed profile that can hold a reserve for candidate root $r_i$. For two new roots the remaining parity condition is

$$
b_{g_i}(j)+b_{g_j}(i)=1+\epsilon_{g_0}(i,0)+\epsilon_{g_0}(j,0).
$$

After selecting reserves that meet these conditions and have spare physical capacity, pairs of exterior exchanges keep the old twelve profile counts and the required row parities. The final witness satisfies every exact exterior moment equation.

Replay with Python's standard library from this job directory.

~~~sh
python r_paley_full92_unrestricted.py
~~~

The replay checks the successive and joint profile histograms, physical index capacities, every mixed row product, and every rectangle column product. The largest rectangle has 739936 zero products and reserve rank 17 over $\mathbb F_{599}$. Its SHA256 is `77f87219f5ffeaa473fa1c80505c3c4a74febf5c89dac226a6e68a69a36d9bae`. The construction leaves 1179 columns to reach the square of order 2396.
