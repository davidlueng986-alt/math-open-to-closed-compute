# 無實會議矩陣子族中的 Golay–Paley 構造

令 $M=24{,}342{,}780$、$T=20{,}018{,}009$。對每個 $k\ge0$，令

$$
g=2^6\,26^{19},\qquad r=2g+1,qquad q_k=3^{2821+43020k},\qquad t_k=r(q_k+1)/4.
$$

每一個 $H(4t_k)$ 均有明確構造。所有 $t_k\equiv T\pmod M$ 且 $t_k\equiv1\pmod{13}$、$t_k\equiv15\pmod{19}$。它們與先前四個明列子族及此級數中的直接 Golay 構造不相交。這個級數是[原剩餘數列](PALEY_PROGRESSION.md)的一部分，其每個乘數都排除 $t_k+1$ 階實會議矩陣。對所得 Hadamard 矩陣抽出外層設計，則每個配對至多有 $2t_k-5$ 個橫截區塊。[外層界](R_PAIRED_TRANSVERSAL_GAP.md) · [直接 Golay 子族](GOLAY_CONFERENCE_FREE.md)

## 構造及整數核查

由長度 2、26 的 Golay 對及 Turyn 乘積，長度 $g$ 有二元 Golay 對。把其兩字和中間一個單點排列成長度 $r$ 的四條互補單支撐字，得到已核查的 $T(r)$ 充分條件。$q_k$ 是素數冪且 $q_k\equiv3\pmod8$，可用 $T(r)$ 與 $q_k+1$ 階 Paley 區塊的直積構造 $H(r(q_k+1))$。直積在 $C_r\times C_{(q_k+1)/4}$ 上，毋須兩邊長度互質。重播使用同一個 Golay 種子 $g=26$ 和小 Paley 參數 $q=19$，重建完整 $H(1060)$，逐一核查所有 561,270 個欄對。[Golay 生成](GOLAY_PROGRESSION.md) · [區塊乘積](PALEY_PROGRESSION.md#區塊乘積) · [算術與小階重播](conference_free_golay_paley.py)

取 $D=(4M/11)\cdot13\cdot19=2{,}186{,}424{,}240$。因 $3^{43020}\equiv1\pmod{D/3}$ 且 $q_k\equiv0\pmod3$，得

$$
q_k\equiv 2{,}149{,}427{,}283\pmod D.
$$

代入 $t_k$ 即得上述同餘，因 $rD/4$ 被 $13$、$19$ 及 $M$ 整除。就已記載的直接形式而言，$4t_k-1$ 被相異質數 $5,479$ 整除，$2t_k-1$ 被 $3,7$ 整除。又 $16t_k+1\equiv13\pmod{19}$ 為非平方，排除 $4t_k=a(a+1)$。長度 13 及 19 的兩個舊區塊子族分別要求 $13\mid t$ 或 $19\mid t$，另外兩個舊 Golay 子族在模 19 為 $16,13$。由 $3^{43020}\equiv1\pmod{1621}$ 及 $r(3^{2821}+1)/4\equiv1\pmod{1621}$，本族各乘數的 $t_k-1$ 都被 1621 整除。此級數中的直接 Golay 公式則使 $t-1$ 的質因數僅為 2、13，與 1621 互質。因此本族與整個上述直接 Golay 參數範圍不相交。[Lean 同餘核查](ConferenceFreeGolayPaley.lean)

另取 $g'=2^{102}\,26$、$r'=2g'+1$、$q'_k=3^{28465+43020k}$，令 $t'_k=r'(q'_k+1)/4$。同一構造逐階成立，這次 $q'_k\equiv937{,}023{,}363\pmod D$，得到 $t'_k\equiv T\pmod M$、$t'_k\equiv1\pmod{13}$、$t'_k\equiv7\pmod{19}$，且 $16t'_k+1\equiv18\pmod{19}$ 為非平方。模 19 的 7 排除上述四個舊子族、第一個 Golay–Paley 子族，以及本級數全部直接 Golay 參數。[兩個新子族的精確模運算](conference_free_golay_paley.py)

## 同一構造的完整指數判準

考慮全部 $g=2^a10^b26^c$，其中 $a,b,c\ge0$。欲以 $r=2g+1$ 和 $q\equiv3\pmod8$ 的奇質數冪構造 $t=r(q+1)/4\equiv T\pmod M$。由 $3\nmid g$ 且 $3\nmid t$，必有 $r\equiv2\pmod3$。因此 $3\mid q$，即 $q=3^e$，$e\ge1$。若 $b>0$，則 $r\equiv1\pmod5$，$4T\equiv1\pmod5$ 又強制 $q\equiv0\pmod5$，矛盾。$g=1$ 會令 $r$ 被 3 整除，其餘允許的 $g$ 均為偶數，故 $r\equiv1\pmod4$。由 $T\equiv1\pmod4$ 得 $e\equiv1\pmod4$。

寫 $s=(3^e+1)/4$。$M$ 唯一整除 $T$ 的質因數是 11，且 $3$ 在模 11 的階為奇數 5，所以 $11\nmid s$。因此可行 $s$ 必與 $M$ 互質，而 $r\equiv Ts^{-1}\pmod M$。指數 $e$ 按 $14340$ 取餘，即可確定 $s\bmod M$，因 3 在模 $4M/3$ 的階為 $14340$。另設 $B=M/4=6{,}085{,}695$。所需長度在模 $B$ 的值是

$$
G_e=\frac{(Ts^{-1}\bmod M)-1}{2}\pmod B.
$$

其餘條件由 $g$ 為偶數及 $G_e$ 確定。模 $B$ 下 2 的階是 $157740$，$26$ 不在所生成子群，但 $26^2\equiv2^{29024}\pmod B$。故只須在 $\langle2\rangle$ 和 $26\langle2\rangle$ 中搜尋 $G_e$。精確整數重播遍歷全部指數餘類。共有 2,390 個符合上述指數奇偶與 $s$ 可逆條件，其中 **595 個**的 $G_e$ 落在這兩個陪集，全部落在後者。

對每個通過的餘類，以 $A_e\in[0,157740)$ 定義 $G_e\equiv26\,2^{A_e}\pmod B$。在這條 Golay–Paley 構造內，與原子族相容的參數，恰為 $b=0$、$c=2m+1$ 和

$$
a+29024m\equiv A_e\pmod{157740}.
$$

每個餘類均可取非負指數實現。這是構造參數的分類，餘類數量並非已解決的乘數比例。$e=1$ 給出 $A_e=83022$，即直接 Golay 條件。$e=2821$ 給出 $A_e=103482$，可取 $a=6,m=9$，亦即上列新子族。[完整模運算重播](conference_free_golay_paley.py)

~~~sh
python3 -B jobs/hadamard-all-orders/conference_free_golay_paley.py
~~~
