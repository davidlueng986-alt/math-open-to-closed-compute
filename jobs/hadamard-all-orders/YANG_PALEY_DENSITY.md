# T–Paley 長度集合的密度限制

令 \(R\subset\mathbb N\) 為可用的 T 字長度。只考慮
\[
 \mathcal H_R=\{t\ge1:\ t=r(q+1)/4,\ r\in R,\ q\equiv3\pmod4,\ q\text{ 為質數冪}\}.
\]
若 \(\sum_{r\in R}1/r<\infty\)，則 \(\mathcal H_R\) 在正整數中自然密度為零，並且在任何固定等差級數中相對密度也是零。

固定 \(K\)。每個 \(r\le K\) 對應 \(q\le4X/r\)。質數及質數冪的計數為 \(o(X)\)，故這些有限個長度共產生 \(o(X)\) 個 \(t\le X\)。對 \(r>K\)，因 \(q\equiv3\pmod4\)，所有產生的 \(t\) 都是 \(r\) 的正倍數，並且至多有 \(\lfloor X/r\rfloor\) 個。合併即得
\[
 \limsup_{X\to\infty}\frac{|\mathcal H_R\cap[1,X]|}{X}
 \le \sum_{\substack{r\in R\\r>K}}\frac1r.
\]
令 \(K\) 增至無窮，右端為零。任一固定等差級數自身約有 \(X/M\) 項，故相對密度結論隨即成立。

更一般地，若某個 \(0<s<1\) 有 \(\sum_{r\in R}r^{-s}<\infty\)，則 \(|\mathcal H_R\cap[1,X]|=O_R(X/\log X)\)。對 \(r\le\sqrt X\)，質數冪估計 \(O(Y/\log Y)\) 給出每個 \(r\) 至多 \(O(X/(r\log X))\) 個。這個估計可由 Chebyshev 的質數上界加上至多 \(\sqrt Y\log_2Y\) 個非質數的質數冪得到。對 \(r>\sqrt X\)，相同倍數計數給出
\[
 X\sum_{r>\sqrt X}r^{-1}\le X^{(1+s)/2}\sum_{r\in R}r^{-s}.
\]

這適用於本階段的 Yang 可變長度 \(r=w(2g+1)\)：\(w\) 取有限多個已驗基底寬，\(g\) 的質因數全落在 \(\{2,5,13\}\)（包含用長度 2、10、26 相乘，以及乘上 \(2^{Pj}\) 的擴張）。對任一 \(s>0\)，
\[
 \sum_{w,g}\frac1{(w(2g+1))^s}
 \le \left(\sum_w(2w)^{-s}\right)
     \prod_{p\in\{2,5,13\}}(1-p^{-s})^{-1}<\infty.
\]
同樣包含本階段有限多個固定長度，也適用於任何改用有限多個 Golay 種子的同類方法。把 \(w=1\) 納入有限的基底寬，即同時涵蓋直接 Golay 的 \(t=2g+1\)（令 \(q=3\)），以及 \(r=2g+1,\ q=3^e\) 的 Golay–Paley。

因此，即使在很多模數中每個指定類都能找到無限多個完整矩陣，上述 Yang–Paley 家族在主剩餘數列中仍只佔零相對密度。其補集含該數列中幾乎所有乘數。固定 [13 模數證明](YANG_THIRTEEN_RESIDUES.md) 中的任一合格長度及其主質數進程，等差級數的質數定理還給出 \(\Omega(X/\log X)\) 個乘數，故這類構造合計的計數量級在主數列內恰是 \(X/\log X\)。若只靠同型 T–Paley 公式覆蓋整條主數列，可用 T 長度的倒數和發散是必要條件。[半質數乘數中的具體限制](SEMIPRIME_T_PALEY_SLICE.md)
