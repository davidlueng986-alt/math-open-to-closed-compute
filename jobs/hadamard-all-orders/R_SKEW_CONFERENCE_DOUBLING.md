# 斜 conference 倍增與合成乘數的外層設計

若 $q\equiv3\pmod4$ 是素數冪，$a\ge1$，令 $t=2^a(q+1)-1$。存在階數 $t+1$ 的斜 conference matrix。因此只要有較小的 $H(2t-2)$，便能構造精確外層設計 $R(t)$ 和至少五條共同相容的 incidence 內欄。這項較小階假設在最小反例中自動成立。下面給出兩個以前三項全矩陣構造未覆蓋的無限合成乘數族，其中一族落在 $t\equiv599\pmod{100590}$。[外層組裝](R_PALEY_PROJECTIVE_LIFT.md) · [通用內欄下界](R_PALEY_UNIFORM_GROWTH.md) · [整數重播](r_skew_conference_doubling.py)

## 斜 conference 的倍增

設 $C$ 為階數 $v$ 的斜 conference matrix。令

\[
H_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
T=C\otimes H_2+I_v\otimes J_2.
\]

$T$ 反對稱，對角為零，其餘均為符號。由 $H_2J_2^{\mathsf T}=J_2H_2^{\mathsf T}$，且 $C+C^{\mathsf T}=0$，兩個交叉項相消。因此

\[
TT^{\mathsf T}=2(v-1)I_{2v}+I_{2v}=(2v-1)I_{2v}.
\]

Paley 的斜 conference $C(q+1)$ 迭代 $a$ 次得到所需階數。對角共軛使首行除對角外全正，刪去首行首欄就取得行欄和皆零、欄 Gram 為 $tI-J$ 的核心。將它與 $H(2t-2)$ 放入既有外層公式，通用內欄構造給出兩條既有附加欄（含全正欄）及四條一位換號欄。[外層與換號公式](R_PALEY_UNIFORM_GROWTH.md)

## 兩個無限剩餘族

取 $a=1$，所以 $t=2q+1$。下列週期使底數的冪在各列出的模數中保持與底數同餘，驗算器以模冪逐項驗證。

| $q$ | $t$ 的兩個不同素因子 | $4t-1$ 的兩個不同素因子 | $2t-1$ 的兩個不同素因子 | $16t+1$ 的非平方同餘 |
| --- | --- | --- | --- | --- |
| $227^{63600c+1}$ | $5,7$ | $17,107$ | $3,101$ | $10\bmod11$ |
| $805019^{63540540c+1}$ | $109,14771$ | $5,479$ | $3,7$ | $7\bmod13$ |

這裡 $c\ge0$。兩個底數都是 $3\bmod4$ 的素數，故其冪提供 Paley 斜 conference。表中的兩個直接 Paley 參數均有相異素因子。又因 $16t+1$ 不是平方，無法有 $4t=s(s+1)$ 的 Scarpis 輸入。第二列有 $q\equiv299\pmod{201180}$，因而 $t\equiv599\pmod{100590}$。這些是外層及相容前綴的條件構造，兩族的全階矩陣仍待完成。[剩餘集合](README.md#dependency-table) · [模冪驗算](r_skew_conference_doubling.py)

## $t=455$ 的整數見證

第一族的首項是 $455=5\cdot7\cdot13$。用素數 $907$ 的 Paley 矩陣作 $H(908)$，因此這一項可無條件構造。重播核查 1,818 個互異且不互補的區塊、910 個點與 413,595 個點對，得到精確 $2\text{-}(910,455,454)$ 設計。同一構造給出 $1820\times916$ 部分矩陣，419,070 個欄內積全為零。[整數見證](r_skew_conference_doubling.py)

```sh
python3 -B jobs/hadamard-all-orders/r_skew_conference_doubling.py
```
