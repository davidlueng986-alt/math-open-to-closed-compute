# 多維奇質數鄰格的整數分母下降

令 $P$ 為奇質數，$D\in M_r(\mathbb Z[1/P])$ 滿足反轉核心的 Gram 等式、$D\mathbf1=-\mathbf1$ 與 $D\equiv I\pmod2$。取最小正分母指數 $k$，令 $E=P^kD$、$W=\operatorname{im}(E\bmod P)$。$E^\mathsf TE$ 被 $P^2$ 整除，故 $W$ 全等向。以下刻畫一批以分母 $P$ 作正交變換的同時下降量。[原單向量下降](PARITY_DENOMINATOR_DESCENT.md)

## 批次下降量

設 $U=M/P$ 是有理正交矩陣、$M$ 為整數矩陣，且 $U\mathbf1=\mathbf1$、$U\equiv I\pmod2$。設 $A=\operatorname{im}(M^\mathsf T\bmod P)$ 且 $A\subseteq W$。由 $W$ 全等向，$ME$ 因 $P$ 整除，故 $UE$ 整數。新的殘餘秩精確為
\[
 \operatorname{rank}(UE\bmod P)=\dim W-\dim\ker B ,
\]
其中 $B$ 是以下定義在 $A$ 上的交錯形式。對 $a,b\in A$ 各取與 $a$ 同餘的整數提升 $e_a\in E\mathbb Z^r$ 和 $l_a\in M^\mathsf T\mathbb Z^r$，設
\[
 B(a,b)=b^\mathsf T(e_a-l_a)/P\pmod P.
\]

若 $e_a$ 的兩種提升相差 $Pz$，將 $Pz$ 與 $b$ 的 $E$ 提升作內積，因被 $P^2$ 整除而有 $b^\mathsf Tz=0$ 模 $P$。若 $l_a$ 的兩種提升相差 $Pz$，用 $b$ 的 $M^\mathsf T$ 提升與之作內積，由 $MM^\mathsf T=P^2I$ 得同樣結論。因此 $B$ 良定且雙線性。比較 $e_a^\mathsf Te_b$ 和 $l_a^\mathsf Tl_b$ 模 $P^2$，即得 $B(a,b)+B(b,a)=0$，所以 $B$ 交錯。

若 $Ec=Pz$，則由 $A\subseteq W$ 及 $E^\mathsf TE$ 被 $P^2$ 整除知 $\bar z\perp A$，故 $UEc=Mz$ 模 $P$ 為零。因此新的模像是同一個 $W$ 上的線性映射之像。若 $Ue=0$ 模 $P$，則 $e=M^\mathsf T z$ 對某個整數 $z$ 成立，故 $\bar e\in A$。對 $a\in A$，寫 $e_a=l_a+Pz$。由 $Ul_a=0$ 模 $P$ 可知 $Ue_a=Mz$ 模 $P$，其為零恰當 $\bar z\perp A$，即 $B(a,\cdot)=0$。這證明下降量。若 $A$ 一維，其上交錯形式必為零，故精確降一維。若 $A$ 二維，可能一次降兩維，也可能完全無下降。

## 直接從分子定義的鄰格

對任意 $A\subseteq W$，取一組基 $a_i$ 以及其 $E$ 提升 $e_i$。令
\[
 L_A=\{z\in\mathbb Z^r:\bar z\perp A\},
 \qquad L'_E=L_A+\sum_i\mathbb Z(e_i/P).
\]
這個正定格整數且單模。確實，$[\,\mathbb Z^r:L_A\,]=P^{\dim A}$，$e_i/P$ 模 $L_A$ 的類亦獨立且各級數為 $P$。交叉內積由 $L_A$ 的定義整數化，而 $(e_i/P)^\mathsf T(e_j/P)$ 由 Gram 整除保證整數。這份鄰格的定義不依賴提升的選擇，上節對兩份 $E$ 提升之差的證明顯示除以 $P$ 後相差 $L_A$。

若 $L'_E$ 在每個標準座標的模二類各有一條平方長度一的向量線，可取這些向量為正交基。因 $P$ 為奇數，可在 $\mathbb Z_2^r$ 確認這些模二類。內積為整數，不同的單位向量線彼此正交。每條軸與全一向量內積為奇整數，各平方加起來等於 $r$，所以可定向使這些內積都為一。取這些軸為 $U$ 的列，$U$ 固定全一方向且模二為恆等，分母至多 $P$。此時 $M^\mathsf T\mathbb Z^r=P L'_E$，因此每個 $e_i$ 都在其中，上一節的 $B$ 恒為零，殘餘秩精確降 $\dim A$。反向，若帶同樣 $A$ 的 $U$ 恰降 $\dim A$，則 $B=0$，其鄰格 $U^{-1}\mathbb Z^r$ 包含全部 $e_i/P$ 及 $L_A$，由單模性與 $L'_E$ 相等。所以整批降秩等價於這一份鄰格具有指定模二框架。

## 質數三的所有分母一次正交變換

當 $P=3$，每個 $M$ 的列平方長度為九、總和為三、只有其對角格為奇數。整數平方分解只有兩種符合者。若對角為 $3$，其餘為零。否則對角為 $-1$，其餘恰兩格為 $2$。兩條列的內積模四為零，迫使第二種列的非對角支撐互惠。互惠的兩列在兩個對角位置合貢獻 $-4$，須在其餘處恰共用一個 $2$。因此非平凡列只能分為互斥三元組，每個區塊為 $-I_3+2J_3/3$。

當所有選用的三元組指示字皆在 $W$ 時，可對每一批用上述交錯形式精確算其下降量。小階重播從 23 點反轉核心的 $11$ 階 Gram 因子開始，經五個三元組變換得到最小分母九、殘餘秩二。兩個互斥三元組各自可降一維，但合併後的交錯形式秩為二，兩個同時作用保留殘餘秩二。另一個小階重播取 $P=5$，檢查五個座標的常數方向能把一次分母完整消去。這些對照證明只檢查各方向各自可降，仍不足以判定它們的同時下降量。

    python3 -B jobs/hadamard-all-orders/parity_neighbor_rank_descent.py
