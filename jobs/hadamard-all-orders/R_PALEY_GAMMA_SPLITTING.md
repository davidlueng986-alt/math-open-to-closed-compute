# 一位換號強制的預留格單位軸

在 Paley 外層中，每個互異的一位換號來源欄，強制一條預留格 $\Gamma$ 的單位軸。相容新欄在這條軸上的座標，恰是已知實體行的符號乘上一個固定符號。在 2396 階的 1,215 欄見證，任何延伸舊預留碼的自對偶碼都使 $\Gamma\simeq\mathbb Z^{15}\perp\Gamma'$，其中 $\Gamma'$ 的秩為 581。[提升格](R_PALEY_LATTICE_LIFT.md) · [1,215 欄見證](R_PALEY_BUCKET_EXTENSION.md) · [整數重播](r_paley_gamma_splitting.py)

## 從一位換號得到單位軸

令 $t\equiv3\pmod4$、$t\ge7$、$m=2t-2=4d$，預留欄數為 $v=t-3$。已知內欄的原始下部字及半投影記為 $z_i,b_i,w_i$。若第 $i$ 條從未選來源欄 $H_{g_i}$ 的第 $\rho_i$ 行換號，可選帶號直線的代表為 $z_i=H_{g_i}-2\sigma_i e_{\rho_i}$，其中 $\sigma_i=H_{\rho_i,g_i}$。於是 $w_i(g_i)=t-2$，其餘預留座標絕對值均為一。令

\[
q_i=t e_{g_i}-w_i.
\]

$q_i$ 在來源欄對應的預留座標是二，其餘為符號，故 $\|q_i\|^2=t$。又 $q_i\equiv-w_i\pmod t$，所以 $q_i/\sqrt t$ 是每個延伸舊碼的 $\Gamma$ 中一條單位向量。不同來源欄的大小二位置不同，故其點積絕對值嚴格小於 $t$。等向性使點積為 $t$ 的倍數，於是恰為零。共享同一位置的兩個候選則有奇數點積，只能給出同一條單位軸。

每條單位軸都直接分裂出 $\mathbb Z$。當 $k$ 條已知欄使用互異預留來源時，$\Gamma\simeq\mathbb Z^k\perp\Gamma'$。其餘部分的秩為 $v-k$，且仍為整幺模格。若知道全部單位軸，餘下秩小於 12 時只可能是零或八，非零者是 $E_8$。這來自 Conway–Sloane 的低維無單位向量分類。[Conway–Sloane 分類](https://neilsloane.com/doc/Me102.pdf)

## 座標就是實體符號

令一條新欄的原始半投影為 $b,w$。與舊欄 $i$ 精確相容時，$w_i^{\mathsf T}w=-t b_i^{\mathsf T}b$；也有 $z_i^{\mathsf T}z/2=w(g_i)-\sigma_i z_{\rho_i}=-b_i^{\mathsf T}b$。合起來得到

\[
\frac{q_i^{\mathsf T}w}{t}=\sigma_i z_{\rho_i}.
\]

因此任意相容下部字在已知單位軸上的座標全為符號。對舊欄本身，座標為一而 $\sigma_i z_{i,\rho_i}=-1$。重播在完整 28 階對照中，也由四條單位軸核對四條真正多位換號欄的物理符號。[相容內積公式](R_PALEY_ISOTROPIC_CODE.md) · [符號重播](r_paley_gamma_splitting.py)

此外，$Vq_i$ 作為實體行字滿足

\[
Vq_i=H_{g_i}+m\sigma_i e_{\rho_i}+Xb_i.
\]

這是因 $Xb_i+Vw_i=2d z_i$ 及 $t=2d+1$。所以在短根的模 $d$ 方程中，$Vq_i$ 可換成那條舊來源欄加一個明列的 $X$ 線性組合。[短根方程](R_PALEY_ROOT_EXTENSION.md)

## 2396 階短根的餘量

以第一條舊下部字為樞紐，令 $s=(z_1-z)/2$ 是實體換號字。短根的選定係數為 $a=(b_1-b)/2$，預留係數為 $r=(w_1-w)/2$。在十五條已知單位軸上的係數為

\[
p_i=q_i^{\mathsf T}r/t=\mathbf1_{i=1}+\sigma_i s_{\rho_i}.
\]

每個 $p_i$ 都是零或舊樞紐欄在該軸的符號。設 $r_\perp=r-\sum_i p_iq_i$，餘量平方範數 $N=\|r_\perp\|^2/t$。令 $h$ 是實體換號數，$h_0$ 是其中十五個已知行的換號數，$\delta$ 表示樞紐行是否換號。短根等式與上式給出

\[
\|a\|^2+\|p\|^2+N=598,\qquad
h=2(1+\|p\|^2+N),\qquad
N=h/2-h_0-2+2\delta.
\]

整條新字反向會在全部 600 個 $a$ 和 15 個 $p$ 的可用位置取補集。因此可定向使 $\|a\|^2+\|p\|^2\ge308$，從而 $N\le290$。

這份見證的舊 $b_i$ 兩兩正交。記舊欄的軸座標矩陣為 $P=(q_i^{\mathsf T}w_j/t)_{i,j}$。整數重播驗證 $P=I+K$，其中 $K$ 反對稱。各舊預留字投影到 $\Gamma'$ 後，所得 Gram 為

\[
G=(v-1)I+K^2.
\]

對任何新增短根，令 $y_i=(t-1)\mathbf1_{i=1}-a^{\mathsf T}b_i-(P^{\mathsf T}p)_i$。這個量也是餘量的實體預留座標 $r_\perp(g_i)$。確實，舊欄的預留餘量向量是 $t e_{g_i}$ 在 $q_j$ 實線性空間的正交餘量。由 $K$ 的行欄絕對值和至多十四及反對稱性，$G$ 的特徵值介於 $595-14^2$ 與 $595$。因此 $y$ 必須滿足 $y^{\mathsf T}G^{-1}y\le N$，特別有 $\|y\|^2\le595N$。這是對相容短根的必要限制，尚未在固定 1,215 欄配置上得到新欄。[秩 581 餘量驗算](r_paley_gamma_splitting.py)

固定 1,215 欄配置的新增短根，也已排除落在這十五條軸加上十四條額外明列軸的實線性空間。[二十九軸二次秩排除與重播](R_PALEY_GAMMA_QUADRATIC.md)

## 完整多位換號對照

當 $\Gamma\simeq\mathbb Z^v$，可把預留半投影寫作 $w=Qc$，其中 $Q^{\mathsf T}Q=tI$。每個合格下部字的 $c$ 都是符號。要有一位換號候選，某個 $Q$ 行必能輸出 $t-2$。由 $\sum_j(|Q_{ij}|-1)^2=t+v-2\|Q_{i,:}\|_1\le1$，該行恰有一個大小二座標，其餘全為符號。若該行的大小二座標在第 $j$ 欄，則模二正交迫使其他行在第 $j$ 欄皆為奇數。該欄的平方範數再迫使其他格全為符號。

在 44 階，用 Williamson 與 Tonchev IV 的 20 階來源，各有一件預留碼，其 $Q$ 每行的絕對值和恰為七，所以無一位換號候選。兩個碼各給出完整 $H(44)$，二十條下部字分別有十二條距最近帶號來源三位、八條五位。全矩陣的 946 個欄內積均為零。[三類來源](R_PALEY_ORDER44_MULTICLASS.md) · [多位換號見證](r_paley_gamma_splitting_data.json) · [重播](r_paley_gamma_splitting.py)

```sh
python3 -B jobs/hadamard-all-orders/r_paley_gamma_splitting.py
```
