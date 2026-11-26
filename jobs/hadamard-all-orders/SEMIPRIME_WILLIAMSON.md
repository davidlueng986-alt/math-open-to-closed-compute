# 用 Williamson 乘積構造三個半質數階數

取下表中任一質數 \(p\)，令 \(q=2p-1\)。表中三個 \(q\) 也都是質數。長度 11 的 T 字與 Turyn 的 \(p\) 階 Williamson 四元組作 Cooper–Wallis 乘積，給出完整的 \(H(44p)\)。[Turyn 構造](https://doi.org/10.1016/0097-3165(72)90095-7) · [Cooper–Wallis 乘積](https://doi.org/10.1017/S0004972700045019) · [精確重播](semiprime_williamson.py)

| \(p\) | \(q=2p-1\) | Hadamard 階數 \(44p\) |
|---:|---:|---:|
| 498,104,500,041,919 | 996,209,000,083,837 | 21,916,598,001,844,436 |
| 958,149,477,774,259 | 1,916,298,955,548,517 | 42,158,577,022,067,396 |
| 2,627,149,862,105,539 | 5,254,299,724,211,077 | 115,594,593,932,643,716 |

每個 \(p\) 都在加強後的半質數進程
\[
p\equiv5{,}963{,}361{,}072{,}439\pmod{10{,}698{,}720{,}412{,}380}.
\]
因此 \(t=11p\equiv20{,}018{,}009\pmod{24{,}342{,}780}\)，且 \((t\bmod13,t\bmod19,t\bmod37)=(5,2,1)\)。另有 \(p\equiv435\pmod{529}\)，故 \(23\) 恰整除 \((t-1)/2\) 一次。這三個階數正處於有限基底 Golay–Yang 排除所描述的半質數族。此處的乘積使用增長的 Williamson 四元組和固定的 \(T(11)\)。[半質數參數與既有分支](SEMIPRIME_T_PALEY_SLICE.md)

## 由有限域得到對稱循環 Williamson 四元組

以下把 Turyn 構造在 \(q=2p-1\) 為質數時直接驗明。設 \(d\) 是 \(\mathbb F_q\) 中的非平方，令 \(\alpha^2=d\)，以 \(1,\alpha\) 作 \(\mathbb F_{q^2}\) 的基底。取
\[
\delta=\frac{1+\alpha}{1-\alpha},\qquad \gamma=\delta^2.
\]
因 \(\alpha^q=-\alpha\)，\(\delta\) 的域範數為 1，故 \(\gamma^p=1\)。又 \(\delta\ne\pm1\)，且 \(p\) 是質數，因此 \(\gamma\) 的階為 \(p\)。射影直線的 \(q+1=2p\) 個點可用 \(\gamma^i,\alpha\gamma^i\) 表示，其中 \(0\le i<p\)。前一組互異，因 \(\langle\gamma\rangle\) 與 \(\mathbb F_q^\times\) 的交只有 1。後一組也互異，且 \(\alpha\) 的範數 \(-d\) 是非平方，與前一組的範數平方類相異。

對上述代表 \(u,v\)，令會議矩陣的格為 \(\chi(\det(u,v))\)，其中 \(\chi\) 是二次特徵，並取 \(\chi(0)=0\)。對不同的 \(u,v\)，在它們所張成的基底中寫 \(w=a u+b v\)。兩行在 \(w\) 的格乘積為 \(\chi(-ab)\)，與代表的非零伸縮無關。將 \(w\) 遍歷全部射影點，得 \(\sum_{b\in\mathbb F_q}\chi(-b)=0\)，另有 \(a=0\) 的點貢獻零。每行平方和為 \(q\)，故會議矩陣平方是 \(qI\)。

乘 \(\gamma\) 的行列式等於 1，因此依兩組射影點排序後，各塊皆為循環矩陣。乘 \(\alpha\) 的行列式為 \(-d\)，故兩個對角塊符號相反。因 \(q\equiv1\pmod4\)，全矩陣對稱。對交叉塊，域共軛將 \(\alpha\gamma^i\) 送至 \(-\alpha\gamma^{-i}\)，且 \(\chi(-1)=1\)，因此交叉塊本身對稱。會議矩陣遂為
\[
\begin{pmatrix}R&S\\ S&-R\end{pmatrix},
\qquad R^2+S^2=qI .
\]
取 \(A=B=S,\ C=R+I,\ D=R-I\)。這四個對稱循環符號矩陣互相交換，且
\[
AA^{\mathsf T}+BB^{\mathsf T}+CC^{\mathsf T}+DD^{\mathsf T}
=2(q+1)I=4pI .
\]
因此它們滿足 Williamson 條件。[Turyn 定理及會議塊說明](https://doi.org/10.1016/0097-3165(73)90010-1) · [對稱循環塊公式](https://doi.org/10.1017/S1446788700020255)

## 完整矩陣與重播

由 HadamardR 的 \(BS(6,5)\) 取兩對序列的半和、半差，再放於不交的長 6、5 區間，得到 \(T(11)\) 的四條選擇字。令 \(T_i\) 為其循環矩陣，則逐格恰有一個 \(T_i\) 活動，且 \(\sum_iT_iT_i^{\mathsf T}=11I\)。以 \(A,B,C,D\) 填入標準 Williamson 四階區塊陣 \(V\)，使 \(VV^{\mathsf T}=4pI\)。取 \(W_j=\sum_iT_i\otimes V_{ij}\)。每個 \(W_j\) 為 \(\pm1\) 矩陣，且
\[
\sum_j W_jW_j^{\mathsf T}
=\sum_{i,i'}T_iT_{i'}^{\mathsf T}\otimes\sum_j V_{ij}V_{i'j}^{\mathsf T}
=44pI.
\]
這些 \(W_j\) 為 \(C_{11}\times C_p\) 上的循環矩陣，反轉可同時將它們轉置，故 Goethals–Seidel 陣給出完整 \(H(44p)\)。程式在 \(q=13,p=7\) 重建這一整條構造，核查 \(H(308)\) 全部 47,278 個欄內積。[公開基底序列](https://github.com/cran/HadamardR/blob/master/R/sysdata.rda) · [乘積驗算](semiprime_williamson.py)

表中的 \(p,q\) 透過 Lucas 證書逐個驗證。對待證質數 \(n\)，逐一核查 \(n-1\) 的已證質數分解、\(h^{n-1}\equiv1\pmod n\)，及每個質因數 \(f\mid n-1\) 的 \(\gcd(h^{(n-1)/f}-1,n)=1\)。因此任一質因數 \(d\mid n\) 下 \(h\) 的階都是 \(n-1\)，迫使 \(d\ge n\)。重播從質數 2 開始，用純整數算術完成。[質性證書](semiprime_williamson.py)

這個構造適用於半質數進程中每個符合 \(2p-1\) 為質數的 \(p\)。在此進程，\(p\equiv3\pmod4\)，所以 \(2p-1\equiv5\pmod8\)。若 \(2p-1=a^e\) 是素數冪，偶數 \(e\) 會給出 \(1\bmod8\)。若 \(e>1\) 為奇數，則 \((a^e+1)/2\) 被 \((a+1)/2\) 真整除，與 \(p\) 為質數矛盾。因此允許素數冪仍等價於這個質數對條件。

## 仍未覆蓋的無限子族

再選 \(p\equiv16\pmod{31^2}\)、\(p\equiv21\pmod{41}\)。與上述進程相合得到
\[
p\equiv261{,}129{,}632{,}466{,}031{,}099
\pmod{421{,}540{,}282{,}968{,}184{,}380}.
\]
代表與模數互質，故仍有無限多個質數。對每一個，\(31\) 恰整除 \(2p-1\) 一次，且 \(41\mid 2p-1\)。由於 \(31\equiv3\pmod4\) 且 \(2p\equiv2\pmod4\)，局部 Smith 指數的等向空間論證排除任何 \(2p\) 階實會議矩陣。[一般會議矩陣障礙](R_PAIRED_TRANSVERSAL.md)

這也排除任何有兩條字相同至多差整體正負號的對稱循環 Williamson 四元組。為證明這一點，將四字在 \(\mathbb Z[C_p]\) 寫成 \(X_i=J-2P_i\)，其中 \(J\) 為全一字，\(P_i\) 指示負號位置。由對稱性 \(\sum_i X_i^2=4p\)。展開後除以四得
\[
\sum_i P_i^2=p\cdot1+(\textstyle\sum_i|P_i|-p)J .
\]
模二時平方把位置 \(j\) 送到 \(2j\)，倍增在 \(C_p\) 可逆。故四個符號的逐位乘積在全部非零位相同，且與零位的乘積相反。把兩條重複字定向為 \(A=B=S\)，再定向 \(C,D\) 使零位分別為 \(+1,-1\)。則兩字在每個非零位相同，因而 \(C=R+1,D=R-1\)，其中 \(R\) 只有零位為零。Williamson 恆等式給出 \(R^2+S^2=(2p-1)I\)，故用上述兩區塊組成 \(2p\) 階實會議矩陣，矛盾。其他對稱循環 Williamson 構造仍可在此子族上嘗試。從更大的有限域壓縮本節的 Turyn 四元組，也有獨立的障礙。[商群壓縮限制](WILLIAMSON_FOLDING.md)

    python3 -B jobs/hadamard-all-orders/semiprime_williamson.py
