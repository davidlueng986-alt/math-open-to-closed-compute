# 同一剩餘數列的無限 Williamson 乘積及 Golay–Yang 交集界

令 \(p_0=5{,}963{,}361{,}072{,}439\)、\(h=10{,}698{,}720{,}412{,}380\)。取任一質數 \(q\equiv2p_0-1\pmod{2h}\)，置 \(n=(q+1)/2\) 及 \(t=11n\)。這裡 \(n\) 可以是合數；\(n\) 和前述細分進程的質數乘數有相同餘數。由於 \(\gcd(2p_0-1,2h)=1\)、\(q\equiv1\pmod4\)，有無限多個合用 \(q\)。每一個都能用 \(T(11)\) 及 Turyn 的長度 \(n\) Williamson 四元組構造完整 \(H(4t)\)。[有限域及區塊公式](SEMIPRIME_WILLIAMSON.md)

當 \(n\) 為合數時，在 \(\mathbb F_{q^2}^\times\) 中取範數一子群的生成元 \(\delta\)，其階是 \(q+1=2n\)。則 \(\gamma=\delta^2\) 的階恰為 \(n\)，和 \(\mathbb F_q^\times\) 的交仍僅為 1，因為 \(n\) 奇數。\(\gamma^i\) 與 \(\sqrt d\,\gamma^i\) 給出兩個互不相交的射影軌道，證明照原區塊公式成立。有限重播額外在 \(q=29,n=15\) 組出完整 \(H(660)\)，核查 217,470 個欄對。[整數重播](semiprime_williamson.py)

## 合計比較各種郭萊長度

令 \(\mathcal W\) 為本節由 \(q\) 得到的全部乘數。按等差級數的質數定理，
\[
|\mathcal W\cap[1,X]|\sim\frac{2}{11\varphi(2h)}\frac{X}{\log X}.
\]
令 \(R\) 為任一固定的 T 長度集合，並假設對某個 \(0<s<1\)，\(\sum_{r\in R}r^{-s}<\infty\)。令 \(\mathcal H_R\) 為可由 \(t=r(q'+1)/4\)、\(q'\equiv3\pmod4\) 為質數冪的 T–Paley 公式生成的乘數。則
\[
|\mathcal W\cap\mathcal H_R\cap[1,X]|=o_R(X/\log X).
\]
因此本節的 Williamson 乘積在 \(\mathcal W\) 中有相對比例趨於一的參數，避開任何一個這類固定 T 長度集合。例如，可同時避開所有從固定有限 Golay 種子及基底寬度生成的 Yang–Paley 長度，以及此前明列的固定長度。直接 Golay 也可納入，因為取 \(q'=3\) 即得 \(t=r\)。[長度倒數和估計](YANG_PALEY_DENSITY.md)

固定 \(r\)。因 \(t\) 為奇數，只需考慮奇數 \(r\)。令 \(L_r=\operatorname{lcm}(11,r)\)，則任何交集乘數都可寫成 \(t=L_r u\)。其兩個參數是
\[
q=au-1,\quad q'=bu-1,\qquad a=2L_r/11,\quad b=4L_r/r.
\]
其中 \(a\ne b\)，因為相等要求 \(r=22\)。若 \(q'\) 是指數至少二的質數冪，給定 \(r\) 時至多出現 \(O_r(\sqrt X\log X)\) 個。剩下兩個參數皆質數。選任意有限組奇質數 \(\ell\nmid ab(a-b)\)。對每個 \(\ell\)，在 \(q\) 的 \(\ell-1\) 個可逆餘數中，恰有一個使 \(q'\equiv0\pmod\ell\)，因 \(q'=(b/a)(q+1)-1\) 且 \(a\not\equiv b\pmod\ell\)。除去有限個 \(q'=\ell\) 的情況，質數 \(q\) 須避開所有這些餘數。由中國剩餘定理及等差級數的質數定理，其上界相對於原本 \(q\equiv-1\pmod a\) 的質數個數，漸近比例為
\[
\prod_{\ell}\left(1-\frac1{\ell-1}\right).
\]
這個比例可任意小，因質數的倒數和發散且只略過有限個質數。故固定 \(r\) 的交集是 \(o_r(X/\log X)\)。

最後先固定 \(K\)，把 \(r\le K\) 併入有限項。對 \(K<r\le\sqrt X\)，以質數冪計數上界，併入至多 \(O(X/\log X)\sum_{r>K}1/r\) 個乘數。對 \(r>\sqrt X\)，由倍數計數併入至多 \(X^{(1+s)/2}\sum_r r^{-s}=o_R(X/\log X)\) 個。先令 \(X\) 增大，再令 \(K\) 增大即得所述交集界。

這是一條無條件的無限構造，\(n\) 無須是質數。若要求 \(n\) 為質數，則需要兩個線性式同時取質數，前述三份實例已取得證書，而整個半質數乘數族仍待處理。[已證質數對與半質數缺口](SEMIPRIME_WILLIAMSON.md)
