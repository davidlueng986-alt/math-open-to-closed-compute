# 長度 187 的 Golay–Yang–Paley 無限構造

令 \(L=24{,}342{,}780,\ t_0=20{,}018{,}009\)。取底質數 \(p=166{,}531{,}867\)、週期 \(P=6{,}625{,}080\)。對每個整數 \(k\ge0\)，令
\[
q=p^{1+Pk},\qquad t=187(q+1)/4 .
\]
每個 \(t\equiv t_0\pmod L\) 都有完整 \(H(4t)\)。首個乘數為 \(7{,}785{,}364{,}829\)。構造以長度 8 的 Golay 對與一組 \(BS(6,5)\) 組成長度 187 的 T 字，再與 \(q\) 的 Paley 區塊相乘。[整數重播](t187_yang.py) · [Paley 區塊乘積](PALEY_PROGRESSION.md#區塊乘積)

## 從 Golay 對和基底序列直接組成 T 字

令 \(A,B,C,D\) 是 \(BS(m,n)\) 的四條符號字，前兩字長 \(m\)，後兩字長 \(n\)。令 \(F,G\) 是長 \(s\) 的二元 Golay 對。Yang 的乘法提供長度 \((2s+1)(m+n)\) 的 T 字。以下將這一情形的區塊公式寫成多項式並核對其恆等式。[Yang 乘法定理](https://combinatorialpress.com/article/jcmcc/Volume%20027/vol-27-paper%201.pdf)

寫 \(U^*(z)=U(z^{-1})\)，並令 \(U^\#(z)=z^{\ell-1}U^*(z)\) 表示長 \(\ell\) 字的反序。取 \(y=z^{m+n}\)、\(u=z^m\)、\(E=F(y^2)\)、\(J=G(y^2)\)、\(E'=F^\#(y^2)\)、\(J'=G^\#(y^2)\)。四條區塊字為
\[
\begin{aligned}
Q&=AE'+uCJ-y^{2s}B^\#,\\
R&=BE'+uDJ'+y^{2s}A^\#,\\
S&=yAJ'-yuCE-y^{2s}uD^\#,\\
T&=yBJ-yuDE+y^{2s}uC^\#.
\end{aligned}
\]
在最初 \(2s\) 個長 \(m+n\) 的區塊，\(Q,R\) 恰佔偶索引區塊，\(S,T\) 恰佔奇索引區塊。末區塊的前 \(m\) 位屬於 \(Q,R\)，後 \(n\) 位屬於 \(S,T\)。每一對活躍字皆有兩個符號。因此每一位置在
\[
(Q+R)/2,\quad(Q-R)/2,\quad(S+T)/2,\quad(S-T)/2
\]
恰有一個非零符號。

將每個式子的三項按列出順序編號。計算 \(QQ^*+RR^*+SS^*+TT^*\) 時，各字的對角項合計為
\[
(EE^*+JJ^*+1)(AA^*+BB^*+CC^*+DD^*)=(2s+1)\,2(m+n).
\]
交叉項按下列方式成對相消，表中的 \(Q_{ij}\) 表示 \(Q\) 的第 \(i\) 項乘第 \(j\) 項的星號。

| 相消的交叉項 | 使用的等式 |
|---|---|
| \(Q_{13}+R_{13}\)，\(S_{23}+T_{23}\) | 多項式乘法可交換 |
| \(Q_{12}+S_{12}\)，\(R_{12}+T_{12}\) | \(E'=y^{2s-2}E^*\)，\(J'=y^{2s-2}J^*\) |
| \(Q_{23}+T_{13}\)，\(R_{23}+S_{13}\) | \(uz^{1-m}=yu^{-1}z^{1-n}\) |

其餘各項是表中各項的星號，同樣相消。取兩組半和、半差後，合併非週期自相關是上式的一半，即 \((2s+1)(m+n)\) 乘零位指示函數。這證明所需的 T 字條件。[明列區塊公式，定理 5.4](https://dokumen.pub/hadamard-matrices-constructions-using-number-theory-and-algebra-9781119520245-9781119520276-9781119520139.html)

此處 \(s=8,m=6,n=5\)。Golay 對由長度 1 的對連續三次串接加倍，基底序列取自 HadamardR 的 BaseOrder 5。重播逐格構造四條 T 字，核對全部 186 個非零位移，並取 \(q=19\) 組出完整 \(H(3740)\)，查驗全部 6,991,930 個欄內積。[公開基底序列資料](https://github.com/cran/HadamardR/blob/master/R/sysdata.rda) · [整數重播](t187_yang.py)

## 數列及和既有構造的區分

因 \(187=11\cdot17\)，條件 \(t\equiv t_0\pmod L\) 經約去 11 等價於
\[
17(q+1)\equiv4(t_0/11)\pmod{4L/11}.
\]
這給出 \(q\equiv7{,}197{,}307\pmod{8{,}851{,}920}\)。上述底質數 \(p\equiv3\pmod8\)，滿足此同餘，且 \(p^P\equiv1\pmod{(4L/11)\cdot13\cdot19\cdot23\cdot43\cdot67\cdot73}\)。因此對所有 \(k\)，\(t\equiv t_0\pmod L\)，且 \((t\bmod13,t\bmod19,t\bmod23)=(8,12,0)\)。

全族的 \(t\) 均不被 13、19、43、67、73 整除，所以與任何以這五個固定 T 字長度搭配 Paley 區塊的構造子族不交。模 19 的 12 也排除同一數列內形如 \(t=2g+1,\ g=2^a10^b26^c\) 的直接 Golay 構造，以及兩個已明列的 Golay–Paley 素數冪子族。原始 Scarpis 階數形式所需的平方 \(16t+1\equiv3\pmod{19}\) 為非平方。主數列的會議矩陣障礙依舊成立。[直接 Golay 分類](GOLAY_CONFERENCE_FREE.md) · [Golay–Paley 子族](CONFERENCE_FREE_GOLAY_PALEY.md) · [會議矩陣障礙](R_PAIRED_TRANSVERSAL.md)

    python3 -B jobs/hadamard-all-orders/t187_yang.py
