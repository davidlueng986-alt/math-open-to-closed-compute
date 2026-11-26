# 殘餘碼外方向的奇質數分母下降

沿用批次鄰格的 $E=P^kD$、$W=\operatorname{im}(E\bmod P)$、$U=M/P$，令 $A=\operatorname{im}(M^\mathsf T\bmod P)$。$UE$ 為整數恰當 $A\subseteq W^\perp$。以下允許 $A$ 部分落在 $W$ 外。[批次鄰格](PARITY_NEIGHBOR_RANK_DESCENT.md)

令
\[
 Z=\{\bar z\in\mathbb F_P^r:Pz\in E\mathbb Z^r\text{，其中 }z\in\mathbb Z^r\},\qquad K=W\cap A .
\]
由 Gram 整除，$W\subseteq Z\subseteq W^\perp$。以 $\rho(z)=(b\mapsto b^\mathsf Tz)$ 記 $Z$ 映至 $A^*$ 的線性映射，且令 $T=\rho(Z)$。對 $a\in K$，取各自在 $E\mathbb Z^r$ 與 $M^\mathsf T\mathbb Z^r$ 的同餘提升 $e_a,l_a$，並令
\[
 \psi(a)=\bigl[b\mapsto b^\mathsf T(e_a-l_a)/P\bigr]\in A^*/T.
\]
改變 $E$ 提升只改變 $T$ 中的元素。改變 $M^\mathsf T$ 提升時，其差與該格的其他向量內積被 $P^2$ 整除，故不改變配對。於是 $\psi$ 是良定線性映射。

精確的秩關係為
\[
 \operatorname{rank}(UE\bmod P)=\dim W+\dim T-\dim\ker\psi .
\]
確實，$E$ 的模 $P$ 零字在應用 $U$ 後的像是 $\bar M Z$，同構於 $T$。將新像再模掉這一子空間，便得到從 $W$ 誘導的線性映射。若 $Ue$ 與 $Mz$ 模 $P$ 同餘，其中 $Pz\in E\mathbb Z^r$，則 $U(e-Pz)\in P\mathbb Z^r$，所以 $e-Pz\in M^\mathsf T\mathbb Z^r$，故原餘數屬於 $K$。對 $a\in K$，$Ue_a$ 在該商空間的像恰由 $\psi(a)$ 給出。這證明公式。當 $A\subseteq W$ 時，因 $Z\subseteq W^\perp$，$T=0$，而 $\psi$ 就是原交錯配對。

## 一次分母且 Gram 整數可逆

若 $k=1$ 且 $P$ 不整除 $\det(D^\mathsf TD)$，$Z=W^\perp$。事實上，令 $G=D^\mathsf TD$。$G$ 在 $\mathbb Z_P$ 可逆，且 $E^\mathsf TE=P^2G$，故 $P^2E^{-1}=G^{-1}E^\mathsf T$。Smith 指數 $\lambda_i(E)$ 成對加至二，並全在 $0,1,2$。$W$ 的維度是指數零的數目。$Z$ 的維度是指數不超過一的數目，也就是 $r-\dim W$，所以等於 $W^\perp$。

此時 $T$ 是 $A^*$ 中在 $K$ 上消失的子空間，$A^*/T$ 自然等於 $K^*$。$\psi$ 就是把原交錯配對的雙變元都取在 $K$ 上，記作 $B_K$。寫 $a=\dim A$、$t=\dim K$，得到
\[
 \operatorname{rank}(UE\bmod P)=\dim W+a-2t+\operatorname{rank}B_K .
\]
在這個範圍，一次變換將整個分母消去恰當 $A=W$ 且交錯形式為零。若 $A$ 有一部分落在 $W$ 外，精確計算這類方向代價，仍容許在 $t$ 夠大時下降。

若應用到已取得的巨型 Pell 因子，$r$、$2r+1$ 都與 $P=146850491611181$ 互質，且修正後的 $W$ 在 $\mathbf1^\perp$ 仍是最大全等向子空間。任何保持全一方向、在其他質數處已整數的正交修復，若能直接把一次分母因子整數化，則在 $P$ 的分母最多一次，且 $A=W$。因此這種一步修復恰須檢查由全部 $W$ 定義的鄰格是否有指定的模二單位框架。[明式 Pell 因子](YAMADA_EXPLICIT_PELL_FACTOR.md) · [原循環碼的秩](YAMADA_CYCLIC_PELL_DESCENT_LIMIT.md)

## 兩類實體對照

取 23 點核心的 $11$ 階 Gram 因子與質數 $3$。對原整數因子先施一個三座標區塊變換，分母升為三，秩為一。若再對不相交的三座標區塊作用，新 $A$ 與舊 $W$ 交集為零，殘餘秩升為二。

另一個確切因子由六次三座標操作取得，最小分母為 $3^5$，殘餘碼只由一個重量六的字生成。這個字在兩個不交三座標組上分別為全一和全負一。兩組指示字各自在 $W^\perp$，各自作用都保留殘餘秩一。合併時 $A$ 有二維，$K=W$ 有一維，$Z$ 對兩組皆正交，故 $T=0$ 且一維交錯形式為零。實際重播的殘餘秩由一降為零，最小分母由 $3^5$ 降為 $3^4$。因此即使原碼已沒有重量三的字，批次變換仍可下降。

    python3 -B jobs/hadamard-all-orders/parity_neighbor_rank_descent.py
