# T–Paley 構造涵蓋會議矩陣障礙數列的全部 247 個指定餘數對

令 \(L=24{,}342{,}780\)、\(t_0=20{,}018{,}009\)。對任意 \(a\bmod13\)、\(b\bmod19\)，有無限多個乘數 \(t\) 同時滿足
\[
t\equiv t_0\pmod L,\qquad
t\equiv a\pmod{13},\qquad
t\equiv b\pmod{19},\qquad
t\equiv2\pmod{23}
\]
且可構造完整的 \(4t\) 階 Hadamard 矩陣。構造只需挑選長度 \(43,67,73\) 之一的 T 字，搭配明列素數冪參數的 Paley 區塊。[精確整數重播](t43_conference_free.py)

## 三個長度涵蓋 247 個餘數對

固定長度 \(r\in\{43,67,73\}\)。對質數 \(q\equiv3\pmod8\)，T 字與 Paley 區塊的乘積給出 \(t=r(q+1)/4\) 的完整 \(H(4t)\)。各 \(r\) 與 \(4L\) 互質，主數列條件等價於
\[
q\equiv 4t_0\,r^{-1}-1\pmod{4L}.
\]
三個對應餘數皆與 \(4L\) 互質且等於 \(3\bmod8\)。[區塊乘積定理](PALEY_PROGRESSION.md#區塊乘積)

另取 \(\ell\in\{13,19,23\}\)。要 \(t\equiv u\pmod\ell\)，則 \(q\equiv 4u\,r^{-1}-1\pmod\ell\)。此質數等差進程的條件是右式非零，等價於 \(u\ne r/4\bmod\ell\)。三個長度的唯一禁用餘數如下。

| T 字長度 \(r\) | \(q\bmod4L\) | \(t\bmod13\) 禁用值 | \(t\bmod19\) 禁用值 | \(t\bmod23\) 禁用值 |
|---|---:|---:|---:|---:|
| 43 | 56,208,811 | 1 | 6 | 5 |
| 67 | 15,728,107 | 7 | 12 | 11 |
| 73 | 7,766,131 | 2 | 4 | 1 |

對任意指定的 \(a\) 與 \(b\)，各自至多排除一個 \(r\)。模 23 的指定值 2 對三個 \(r\) 都可用。故總可選一個 \(r\)，再用中國剩餘定理把四個同餘條件合為模 \(4L\cdot13\cdot19\cdot23\) 的單一餘數。此餘數與模數互質，可另由 Dirichlet 等差數列質數定理得到無限多個質數 \(q\)，進而得到無限多個不同的 \(t\)。整數重播逐一驗證 247 個 CRT 合併及互質條件。[逐對同餘核查](t43_conference_free.py)

整個主數列滿足 \(t\equiv599\pmod{100590}\)、\(t\equiv1\pmod4\) 且 \(t\equiv11\pmod{121}\)。質因數 11 的奇數賦值排除 \(t+1\) 階實會議矩陣，並使 \(R(t)\) 的任一配對最多有 \(2t-5\) 個橫截區塊。直接 Paley 的兩個參數 \(4t-1,2t-1\) 分別同時含質因數 \(5,479\) 與 \(3,7\)。所取 \(t\equiv2\pmod{23}\) 使 \(16t+1\equiv10\pmod{23}\) 為非平方，排除原始 Scarpis–Đoković 階數形式 \(4t=q'(q'+1)\)。[橫截區塊與會議矩陣條件](R_PAIRED_TRANSVERSAL_GAP.md) · [直接 Paley 參數](GOLAY_CONFERENCE_FREE.md)

## 247 條明列的素數冪子族

參數表按索引 \(19a+b\) 給出每個餘數對的一個 \((r,q)\)，其中 \(q\) 為質數且 \(q\equiv3\pmod8\)。取 \(P=473220\)，則該餘數對的具體無限子族為
\[
t_k=r\bigl(q^{1+Pk}+1\bigr)/4,\qquad k\ge0.
\]
重播核查每一個底質數及 \(q^P\equiv1\pmod{4L\cdot13\cdot19\cdot23}\)，所以 \(t_k\) 均維持指定餘數。這 247 條子族由 \((t\bmod13,t\bmod19)\) 區分，兩兩不交。明列子族的證明只需素數冪 Paley 區塊定理與精確整數核查。[底質數與證書](t43_prime_parameters.json) · [整數驗證](t43_conference_free.py)

核查底質數使用 Lucas 判準。對每個欲認證的 \(p>2\)，表列已認證的質數因子 \(q_i\)，含重數且乘積為 \(p-1\)，以及底數 \(h\)。核查 \(h^{p-1}\equiv1\pmod p\)，並對每個相異 \(q_i\) 驗證 \(\gcd(h^{(p-1)/q_i}-1,p)=1\)。對任一質因數 \(d\) 整除 \(p\)，\(h\bmod d\) 的階必為 \(p-1\)，否則會整除至少一個 \((p-1)/q_i\)。由 \(p-1\mid d-1\) 得 \(d\ge p\)，所以 \(p\) 為質數。從 2 開始，程式按遞增順序重播 933 個質數證書。

## 明列的長度 43 素數冪子族

令 \(p=445{,}693{,}291\)。對每個整數 \(k\ge0\)，取
\[
q=p^{1+31548k},\qquad t=43(q+1)/4.
\]
首個乘數是 \(4{,}791{,}202{,}889\)，對應階數 \(19{,}164{,}811{,}556\)。試除核查 \(p\) 為質數，且 \(p^{31548}\equiv1\pmod{4L\cdot13\cdot19}\)。因此 \(t\equiv t_0\pmod L\)、\(t\equiv5\pmod{13}\)、\(t\equiv2\pmod{19}\) 對所有 \(k\) 成立。此子族用模 19 的非平方 14 排除 Scarpis 形式。

模 13 的非零及模 19 的餘數 2 排除原先四個明列的子族。由直接 Golay 參數分類，形如 \(g=2^a10^b26^c,\ t=2g+1\) 的本數列直接構造也無法給出餘數 \(2\bmod19\)。[舊子族的同餘](GOLAY_PROGRESSION.md) · [直接 Golay 參數分類](GOLAY_CONFERENCE_FREE.md)

## 種子與整階對照

以 \(\pm i\) 表示位置上第 \(i\) 條 T 字取相應符號，其餘三字取零。重播使用 HadamardR 公開資料中長度 \(43,67,73\) 的 T 字，逐一核查每個位置與全部非零位移的合併非週期自相關。資料取自 HadamardR 手冊歸功於 London 2013 年的 T 序列資料。長度 43 另有獨立的 \(BS(22,21)\) 存在來源，同樣能以標準二分支撐法推出 T(43) 存在。[HadamardR 資料與出處](https://cran.r-project.org/web/packages/HadamardR/HadamardR.pdf) · [公開資料檔](https://github.com/cran/HadamardR/blob/master/R/sysdata.rda) · [Đoković 基底序列分類](https://doi.org/10.1155/2010/851857)

小階對照固定 \(q=19\)。從上述三個種子分別重建完整 \(H(860)\)、\(H(1340)\)、\(H(1460)\)，逐一核對 369,370、897,130、1,065,070 個欄內積。

    python3 -B jobs/hadamard-all-orders/t43_conference_free.py
