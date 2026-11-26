# 反轉斜核心的 Yamada 乘積與質數障礙

令 \(r\) 為奇數，\(n=2r+1\)、\(p=4r+3\)、\(q=p-2\)。若 \(q\equiv5\pmod8\) 為質數冪，且有一個反轉對合 \(R\) 把 \(n\) 階歸一化斜核心 \(S\) 送到 \(-S\)，則可用 Yamada 的兩個循環矩陣和長度 11 的 T 字構造完整的 \(H(44p)\)。在 \(r\) 為質數時，本文給出產生這種核心的精確循環條件，並排除目前最細剩餘數列中的這個入口。對不依循環的核心，得到較弱的局部必要條件，另有已證質數的候選通過該條件。[Yamada 有限域構造](https://www.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/some-new-series-of-hadamard-matrices/2CF4B3D949273D45717E6F5FED183827) · [Seberry–Yamada，Lemma 26](https://documents.uow.edu.au/~jennie/WEBPDF/139_1990.pdf)

## 反轉核心與實係數矩陣

歸一化斜核心滿足 \(S^{\mathsf T}=-S,\ S\mathbf1=0,\ SS^{\mathsf T}=nI-J\)，且非對角格全為符號。設反轉置換是對合。兩個固定點間的符號將被迫等於自身的負值，故恰有一個固定點，其餘為 \(r\) 對。排列每對兩端，使固定點一行在前 \(r\) 個端點為正、後 \(r\) 個端點為負。此時
\[
S=\begin{pmatrix}
0&\mathbf1^{\mathsf T}&-\mathbf1^{\mathsf T}\\
-\mathbf1&A&B\\
\mathbf1&-B&-A
\end{pmatrix},
\quad A^{\mathsf T}=-A,\quad B^{\mathsf T}=B.
\]
令 \(D=A-B\)。它的對角為 \(\pm1\)，每個非對角有序對 \((D_{ij},D_{ji})\) 恰有一個活動格，值為 \(\pm2\)。在配對上作二階 Walsh 變換後，核心的非零區塊為 \(M\) 及 \(-M^{\mathsf T}\)，其中 \(M\) 把 \(\sqrt2\,\mathbf1^{\mathsf T}\) 疊在 \(D\) 之上。故 \(M^{\mathsf T}M=nI\)，並有
\[
D^{\mathsf T}D=nI-2J,\qquad
D\mathbf1=D^{\mathsf T}\mathbf1=-\mathbf1 .
\]
其中 \(D^{\mathsf T}\mathbf1=-\mathbf1\) 來自 \(S\mathbf1=0\)。由這個等式及 \(D^{\mathsf T}D\,\mathbf1=\mathbf1\) 得另一個行和等式。反之，有上述格形和 Gram 的 \(D\) 給出 \(A=(D-D^{\mathsf T})/2\)、\(B=-(D+D^{\mathsf T})/2\)。此時 \(M\) 的列空間正是 \((1,\sqrt2\,\mathbf1)^\perp\)，所以由同一 Walsh 變換得到所需 \(SS^{\mathsf T}=nI-J\) 及反轉對合。

把 \(S\) 重標，使反轉對合 \(R\) 成為 \(n\) 個循環座標的反射。則 \(SR\) 為對稱矩陣。設 \(M_0,N_0\) 為 Yamada 的兩個 \(n\) 階對稱循環矩陣，滿足 \(M_0^2+N_0^2=qI\)，其中 \(M_0\) 的對角全零，餘格及 \(N_0\) 均為符號。取兩組係數
\[
U=(I,0,SR,SR),\qquad V=(M_0,N_0,R,R).
\]
四個 \(p\) 階矩陣的核心分別取 \(U_i\otimes J_2+V_i\otimes\left[\begin{smallmatrix}1&-1\\-1&1\end{smallmatrix}\right]\)，角落符號依次為 \((1,-1,1,1)\)，邊界符號為 \((-1,-1,1,1)\)。逐格恰有一個來源，故皆為符號。配對的反對稱子空間上，四矩陣為 \(2M_0,2N_0,2R,2R\)。配對常數中正交於全一字的子空間上為 \(2I,0,2SR,2SR\)。兩處各自對稱交換，平方和為 \(4pI\)。邊界與均勻常數的二維子空間上，四矩陣為 \(K,K-2I,2I-K,2I-K\)，其中 \(K=\left[\begin{smallmatrix}1&-\sqrt{2n}\\-\sqrt{2n}&2\end{smallmatrix}\right]\)，同樣交換且平方和為 \(4pI\)。故這四個矩陣可直接代入長度 11 的 T 字係數陣。[T 字代入及 Gram 證明](UNREAL_BUTSON_PRODUCT.md)

## 循環情形的精確整數提升

設 \(r\) 為奇質數，\(\zeta=\zeta_r\)，\(\mathcal O=\mathbb Z[\zeta]\)。上述 \(D\) 可取循環矩陣，恰當且僅當存在
\[
\beta\in\mathcal O,\qquad
\beta\overline\beta=2r+1,\qquad
\beta\equiv1\pmod{2\mathcal O}.
\]
由 \(D\) 取 \(\beta=\sum_i D_{0i}\zeta^i\)，恆等式立得。反向時，\(\beta\) 在模 \(1-\zeta\) 的餘數為 \(\pm1\)，由範數等式和 \(\mathcal O/(1-\zeta)\cong\mathbb F_r\) 可見。可先整體變號使餘數為 \(-1\)，再取整數向量 \(d\) 使 \(\beta=\sum_i d_i\zeta^i\) 且 \(\sum_i d_i=-1\)。這個提升唯一，因任何另一個表示只差同一個整數加到全部係數，係數和因此改變 \(r\) 的倍數。

由 \(\beta\equiv1\pmod2\) 與係數和知 \(d_0\) 為奇，其餘皆為偶數。寫 \(\beta=1+2u\)，範數模四為三，故 \(u+\bar u\equiv1\pmod2\)，也就是 \(\beta+\bar\beta\equiv0\pmod4\)。因此 \(d_i+d_{-i}\equiv2\pmod4\)，因該和的多項式表示在模四下所有係數相同，而常數項為 \(2d_0\)。Parseval 恆等式給出
\[
\sum_i d_i^2=\frac{1+(r-1)(2r+1)}r=2r-1.
\]
奇係數 \(d_0\) 至少貢獻 1，每對其他偶係數因上述同餘至少貢獻 4，總下界恰為 \(2r-1\)。因此達到下界，\(d_0=\pm1\)，且每對恰一個為 \(\pm2\)，另一個為零。把 \(d\) 作為循環矩陣的首行，其 Fourier Gram 在零頻為 1，其餘頻率均為 \(2r+1\)，故是所需的 \(D\)。

小階對照取 \(r=3,\ \beta=1-2\zeta_3\)，提升為 \((1,-2,0)\)，由 \(\mathbb F_{13^2}\) 重建 \(M_0,N_0\)，組得 \(H(660)\)，核查全部 217,470 個行內積。[完整整數重播](yamada_circulant_reverse.py)

## 最細數列排除循環的斜半塊

更一般地，令 \(r>1\) 為奇數。若有質數 \(\ell\mid2r+1\)，使 \(-1\) 是 \(\ell\) 在模 \(r\) 下的某個冪，則上述循環 \(D\) 無解。把其首行多項式 \(d(z)\) 取模 \(\ell\)。在特徵 \(\ell\) 的代數閉包中，對每個非恆等 \(r\) 次根 \(z\)，Gram 給出 \(d(z)d(z^{-1})=0\)。此處 \(z^{-1}=z^{\ell^k}\)，故 \(d(z^{-1})=d(z)^{\ell^k}\)，迫使 \(d(z)=0\)。因 \(\ell\nmid r\)，這些根互異，故 \(d(z)\) 模 \(\ell\) 是 \(1+z+\cdots+z^{r-1}\) 的倍數。其係數本有一個 \(\pm1\) 和某個零，矛盾。此證明容許 \(\ell\mid 2r+1\) 的任意正賦值。

在目前最細的剩餘數列 \(p\equiv261129632466031099\pmod{421540282968184380}\)，有 \(r\equiv1\pmod3\) 及 \(r\equiv3\pmod7\)。若 \(r\equiv3\pmod4\) 為質數，則 \(3\mid2r+1\)，且二次互反律給 \((3/r)=-1\)。若 \(r\equiv1\pmod4\) 為質數，則 \(7\mid2r+1\)，且 \((7/r)=-1\)。兩種情形都得到 \(\ell^{(r-1)/2}\equiv-1\pmod r\)，所以整個質數 \(r\) 分支通過上述排除。[最細剩餘數列](SEMIPRIME_WILLIAMSON.md)

這個排除其實只須斜半塊 \(A\) 為循環，容許 \(B\) 任意。首先 \(DD^{\mathsf T}=D^{\mathsf T}D=nI-2J\)，故 \(AB=BA\)。在 \(\mathbf1^\perp\) 上，\(B^2=nI+A^2\)。循環斜塊 \(A\) 在非零頻率有特徵值 \(\lambda\in\mathbb Q(\zeta)\)，且 \(\bar\lambda=-\lambda\ne0\)。其 Galois 穩定子不含取共軛的元素，因 Galois 群為循環，穩定子階 \(h\) 必為奇數。所有非零頻率的特徵值正是 \(\lambda\) 的共軛，因此 \(\mathbf1^\perp\) 是 \(\mathbb Q(\lambda)\) 上的 \(h\) 維空間，且 \(B\) 為線性算子。若 \(n+\lambda^2\) 在此域無平方根，恆等式 \(B^2=n+\lambda^2\) 會使此空間成為二次擴域上的線性空間，與 \(h\) 奇數矛盾。因此 \(A,B\) 有共同特徵值 \(\lambda,b\)，其中 \(b\in\mathbb Q(\lambda)\) 且 \(b^2=n+\lambda^2\)。因 \(B\) 實對稱，\(b\) 為實數。於是 \(D\) 的特徵值 \(\beta=\lambda-b\) 有範數 \(n\)。且 \((D-I)/2\) 為整數矩陣，故 \((\beta-1)/2\) 為代數整數，回到已排除的循環提升條件。

## 雙正則斜半塊與有限頂點修改的障礙

設 $r\equiv3\pmod4$，且 $r+1$ 不是平方。取標準雙正則斜半塊 $A_0$，即 $A_0\mathbf1=0$、$A_0^2=-rI+J$。若所需的 $A$ 本身為雙正則，則在零和的有理空間上，$A$ 使該空間成為 $\mathbb Q(\sqrt{-r})$ 的奇數維線性空間，而 $B$ 與 $A$ 交換並有 $B^2=(r+1)I$。由於此虛二次域不含 $\sqrt{r+1}$，$B$ 將使空間維數為偶數，得到矛盾。特別是質數 $r>3$ 且 $r\equiv3\pmod4$ 時，$r+1$ 為平方會分解 $r=(\sqrt{r+1}-1)(\sqrt{r+1}+1)$，亦不可能。

這個障礙也涵蓋由 $A_0$ 出發，僅更改同一頂點集 $J_0$ 內所有可能方向的情形，只要 $|J_0|-1<\sqrt r$，並保持整體正則。令 $E=A-A_0$、$U=\operatorname{im}E$。$U$ 在零和空間內且支撐於 $J_0$。主塊 $A_0[J_0,J_0]$ 的算子範數至多 $|J_0|-1$，而 $A_0$ 在零和空間把長度乘 $\sqrt r$，故 $U\cap A_0U=0$。$U\oplus A_0U$ 對 $A$ 不變，其正交補上 $A=A_0$。

在 $U\oplus A_0U$ 中以 $u+A_0v$ 為座標。若有 $\lambda=\pm i\sqrt r$ 的特徵向量，第二分量給 $u=\lambda v$，第一分量便給 $E(\lambda v+A_0v)=0$。由 $E$ 斜對稱，其核是 $U^\perp$，所以 $(\lambda I+P_UA_0|_U)v=0$。但此壓縮的範數亦至多 $|J_0|-1$，故無此特徵向量。因此 $A^2=-rI$ 的有理特徵空間恰為上述正交補，在 $\mathbb Q(\sqrt{-r})$ 上的維數為 $(r-1)/2-\operatorname{rank}E$，仍是奇數，因斜矩陣的秩為偶數。$B$ 保留此空間，故同樣的平方根矛盾成立。這排除局部頂點修改，仍容許更廣泛的不循環斜半塊。

## 不依循環的局部條件

固定任一反轉核心，不要求 \(A,B\) 循環。於質數 \(\ell\mid n\) 的局部整數環，\(D\) 保持零和格 \(V\)，其秩 \(r-1=2k\)，在基底 \(e_i-e_r\) 中的 Gram 行列式為 \(r\)，故模 \(\ell\) 非退化。\(D\) 在 \(V\) 是倍率 \(n\) 的相似變換。若 \(e=v_\ell(n)\) 為奇數，取 \(D\) 的 Smith 指數 \(a_1\le\cdots\le a_{2k}\)。其伴隨算子有同一指數列，且與 \(D\) 的乘積為 \(nI\)，故 \(a_i+a_{2k+1-i}=e\)。用 Smith 左右基底寫成 \(Du_i=\ell^{a_i}v_i\)，前 \(k\) 個 \(a_i\) 不超過 \((e-1)/2\)。由
\[
\langle v_i,v_j\rangle=\ell^{-a_i-a_j}n\langle u_i,u_j\rangle
\]
知前 \(k\) 個 \(v_i\) 模 \(\ell\) 張成一個全等向空間。延伸成基底後，Gram 的雙邊方塊形狀給出行列式 \((-1)^k\) 乘一平方。因此 \((-1)^k r\) 必為模 \(\ell\) 的平方。特別是 \(r\equiv3\pmod4\) 時，對 \((2/\ell)=-1\) 的質數，\(v_\ell(n)\) 必為偶數。

先前三個質數組的偏移 \(839,1303,2235\)，在 3、11 的賦值分別為 \((1,1),(2,1),(1,2)\)，故也排除不依循環的反轉核心。另有已取得 Lucas 證書的四個質數
\[
\begin{aligned}
p&=1{,}228{,}304{,}150{,}035{,}627{,}617{,}140{,}959,\\
q&=p-2,\qquad r=307{,}076{,}037{,}508{,}906{,}904{,}285{,}239,\\
h&=80{,}565{,}666{,}406{,}639{,}618{,}073 .
\end{aligned}
\]
該 \(p\) 的偏移為 \(2{,}913{,}847\)，且 \(2r+1=3^2\cdot7\cdot11^2h\)，\(h\equiv1\pmod8\)，所以所有奇賦值質數都通過這項局部條件。得到 \(H(44p)\) 仍取決於找到不依循環的反轉核心。[質性與算術重播](yamada_circulant_reverse.py)

    python3 -B jobs/hadamard-all-orders/yamada_circulant_reverse.py
