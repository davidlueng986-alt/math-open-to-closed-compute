# 反轉核心的分母可集中到任一指定奇質數

令 $r\ge7$ 為奇數，$n=2r+1$，$G=nI-2J$。假設有有理矩陣 $D_0$ 滿足
\[
D_0^{\mathsf T}D_0=G,\qquad D_0\mathbf1=-\mathbf1,
\]
且對每個質數 $\ell$ 都有解同式的 $D_\ell\in M_r(\mathbb Z_\ell)$，其中 $D_2\equiv I\pmod2$。那麼對任意指定的奇質數 $P$，存在
\[
 D\in M_r(\mathbb Z[1/P]),\qquad D\equiv I\pmod2,\qquad
 D^{\mathsf T}D=G,\qquad D\mathbf1=-\mathbf1.
\]
此處模 $2$ 是環映射 $\mathbb Z[1/P]\to\mathbb F_2$。這把整數化問題縮到一個可任意選擇的質數。消除最後一個質數的分母仍需額外構造。[有理與局部整數因子](YAMADA_LOCAL_INTEGRAL.md) · [反轉核心與實符號格形](YAMADA_CIRCULANT_REVERSE.md)

## 調整行列式與旋量範數

令 $V=\mathbf1^\perp\subset\mathbb Q^r$，二次型取 $Q(v)=v^{\mathsf T}v$，並把 $V$ 上的正交算子延伸成固定 $\mathbf1$ 的算子。由 $D_\ell^{\mathsf T}D_\ell=D_0^{\mathsf T}D_0$ 知 $D_\ell D_0^{-1}$ 正交，且它固定 $\mathbf1$。兩因子的行列式皆為 $\pm n^{(r-1)/2}$。若有需要，先對 $D_0$ 左乘單一對換的置換矩陣，使其行列式與 $D_2$ 相同。此步保留兩個有理等式。對每個奇 $\ell\ne P$，同樣可左乘置換來對齊 $D_\ell$ 的行列式。故每項要求都可寫成 $U_\ell D_0$，其中 $U_\ell\in\mathrm{SO}(V)(\mathbb Q_\ell)$。

旋量範數用 $\theta_\ell:\mathrm{SO}(V)(\mathbb Q_\ell)\to\mathbb Q_\ell^\times/\mathbb Q_\ell^{\times2}$，兩個反射 $s_v s_w$ 的範數類是 $Q(v)Q(w)$。在保持局部矩陣要求的前提下，可任意更改 $\theta_\ell(U_\ell)$ 的**單位**平方類。

- 奇 $\ell$ 取 $v=e_1-e_2$，並在 $v,e_3-e_4$ 所張成的平面上取 $w$。平面在 $\mathbb F_\ell$ 的型為 $2x^2+2y^2$，可表示每個非零值。確切地說，兩個分別由 $2x^2$ 與 $a-2y^2$ 取得的集合各有 $(\ell+1)/2$ 個元素，必相交。取整數代表使 $Q(w)$ 為指定單位平方類。兩反射因平方長度為單位，可作用於整個 $\mathbb Z_\ell^r$ 並保留全一向量。取 $Q(w)$ 與 $2$ 的乘積為所需單位類，左乘 $s_v s_w$ 即可。
- $\ell=2$ 取 $v=(1,-1,0,\ldots)$。依次取 $w=(1,1,-2,0,\ldots)$、$(1,-1,2,-2,0,\ldots)$、$(1,1,-2,2,-2,0,\ldots)$。這些向量的和皆為零，$Q(w)/2$ 各為 $3,5,7$。$v,w$ 模二相等，且 $Q(v)/2,Q(w)/2$ 都是奇單位，所以 $s_v,s_w$ 都保持 $\mathbb Z_2^r$，模二為同一個反射的約化。乘積模二為 $I$，旋量範數依次是平方類 $3,5,7$。以恆等矩陣補入類 $1$，剛好涵蓋所有二進單位平方類。

取有限質數集 $B$，包含 $2$、$rn$ 的質因數和 $D_0$ 的所有分母質數。對 $\ell\in B\setminus\{P\}$，令 $\varepsilon_\ell\in\{0,1\}$ 是 $\theta_\ell(U_\ell)$ 的賦值奇偶。設 $s=\prod_{\ell\in B\setminus\{P\}}\ell^{\varepsilon_\ell}>0$。由上述單位調整，可使每個 $\theta_\ell(U_\ell)$ 等於 $s$ 的平方類。

全域亦有 $h\in\mathrm{SO}(V)(\mathbb Q)$ 使 $\theta(h)$ 為 $s$。因 $\dim V=r-1\ge6$，$Q$ 表示每個正有理數 $a$。理由是 $Q\perp\langle-a\rangle$ 在實數域不定，且在每個 $\mathbb Q_\ell$ 的維度至少五，故處處等向。Hasse–Minkowski 定理給出有理等向向量，$Q$ 的正定性迫使最後一個座標非零，從而得到 $Q(u)=a$。分別令 $Q(v)=1$、$Q(w)=s$，便可取 $h=s_v s_w$。當 $r\ge9$ 時，也可用四組互不相交的差分向量和有理四平方定理直接證明表示性。[局部等向性、Hasse–Minkowski 與旋量範數](https://link.springer.com/book/10.1007/978-3-540-45629-1)

## 自旋群的強逼近

對 $\ell\in B\setminus\{P\}$，由 $\theta_\ell(U_\ell h^{-1})=1$，可把 $U_\ell h^{-1}$ 提升成某個 $g_\ell\in\mathrm{Spin}(V)(\mathbb Q_\ell)$。對 $\ell\notin B\cup\{P\}$，$D_0$ 已整數。若延伸至全空間的 $h$ 在 $\ell$ 也整數，可令 $U_\ell=h$、$g_\ell=1$。只剩有限個 $h$ 有分母的質數，且 $s$ 於這些質數皆為單位。可取上述奇質數的整數反射乘積作 $U_\ell$，旋量範數為 $s$，再提升 $U_\ell h^{-1}$。因此所有 $\ell\ne P$ 都有局部 $g_\ell$，使 $\pi(g_\ell)hD_0$ 具所需整數性及二進餘數，其中 $\pi:\mathrm{Spin}(V)\to\mathrm{SO}(V)$。

在有限個指定 $\ell$，取 $g_\ell$ 的開鄰域，使所有元素仍保留矩陣的整數性及模二餘數。其餘質數不除 $2r$，零和格為非退化整數格，且標準整數格分解為零和格與全一方向的正交直和。取該零和格的整數自旋群作開緊子群，其像保留標準整數格。這些局部條件給出避開 $\{\infty,P\}$ 的限制直積中的非空開集合。

$\mathrm{Spin}(V)$ 在 $\dim V\ge6$ 時為單連通、絕對幾乎單群。$V$ 在 $\mathbb Q_P$ 因維度至少五而等向，故 $\mathrm{Spin}(V)(\mathbb Q_P)$ 非緊。強逼近定理因此給出有理自旋元素 $g$ 落入上述開集合。令 $D=\pi(g)hD_0$，便在每個 $\ell\ne P$ 整數，且模二為 $I$。有理數在所有其他質數整數的條件恰為屬於 $\mathbb Z[1/P]$，故得結論。[Rapinchuk，Theorem 2.3](https://arxiv.org/abs/1207.4425)

## 已證質數候選與小階對照

對 $r=307076037508906904285239$，已有有理因子與各質數的局部整數因子，且在 $2$ 可取恆等餘數。故例如可以同時滿足全部 Gram 與二進條件，只容許分母含 $5$。同一結論也各自適用於選擇 $3$、$7$ 或任意奇質數。這些存在敘述可對不同質數給出不同矩陣。[大質數候選與精確有理因子](YAMADA_NONCIRCULANT_RATIONAL.md)

重播取 Paley 的 $23$ 點反轉核心以得 $r=11$ 的整數 $D$，再左乘對照用的 $s_v s_w$，其中 $Q(v)=2$、$Q(w)=10$。逐項核查變換後的全體行和與 Gram、恆等二進餘數及實際分母 $5$，另核查上面四種二進單位類。程式重播小階算術，強逼近給出大階存在性。

```sh
python3 -B jobs/hadamard-all-orders/yamada_single_prime_denominator.py
```
