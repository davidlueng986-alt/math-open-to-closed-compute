# A proof map for the full Hadamard conjecture

Let $H(n)$ mean that $n$ mutually orthogonal sign columns of length $n$ exist, and let $P(n,k)$ mean that $k$ such columns exist. The target is $H(4t)$ for **every** positive integer $t$. This file gives two exact sets of proof obligations. The shorter one has **two open families**. Construct a residual design, then prove an integral extension step for compatible prefixes of that design. Both families are necessary and together they are sufficient, given the published completion theorem. The fractional extension problem already has an explicit solution at every step.

**全題仲未攻克。** 以下每條未證引理都寫明要覆蓋邊啲 $t$、可以更換邊啲已選嘅集合，以及點樣接返去全猜想。單獨做好幾多個階數，量度唔到距離通證仲有幾遠。

## 全題進度

原題要求每個正整數 $t$ 的 $H(4t)$；一個被證明無解的階數足以反證。已知族先逐階覆蓋適用參數，未覆蓋的奇數乘數須有能涵蓋全部的證明。下列正面路線可互補。對同一階，各項以「且」相接的條件必須由相容的構造共同提供。

| 路線 | 已得到甚麼 | 仍缺甚麼 |
| --- | --- | --- |
| 已知構造的覆蓋 | 直接 Paley、Scarpis–Đoković、長度 3 區塊乘積，以及原有剩餘等差數列中長度 13、19 區塊乘積的兩個不相交無限子族 | 覆蓋餘下全部奇數乘數的定理。[明確子族](PALEY_PROGRESSION.md) · [群標籤直接乘積的奇偶障礙](T_PRODUCT_PARITY.md) |
| 外層設計與精確內欄 | 全寬同餘解及有理延伸。2396 的三交集模型只餘兩組，兩組皆須非交換。規範化的兩方陣疊接至少須加五欄。固定 988 組可模十六配對的上部，精確解的六行下部省略投影在行重排下只餘八種 | 同一組五欄仍須讓所有新舊內積精確為零。全階仍須統一構造外層設計，並在共同證書上滿足整數內欄條件。[交集限制](R_SYMMETRY.md) · [精確省略欄 Gram](EXTERIOR_STACKS.md) · [模十六提升與排除](EXTERIOR_MOD16_INVARIANT.md) · [八種省略投影](EXTERIOR_EXACT_FACTORS.md) |
| 直接構造近滿矩陣 | 所有奇數乘數的混合奇偶缺 8 欄可完成；缺 9 至 11 欄可完成或到達缺 8 欄。2396 的缺 12 欄由至多兩個整幺模超格精確判定。完整補欄等價於某個仿射格的最短向量達到門檻。缺 12 欄的 $D_{12}^{+}$ 在 28、44、60 階有精確阻塞例；$t=4r+3$ 的模型通過兩個 Gram 等式模十六，$t=16k+3$ 的另一構造達模三十二 | 統一取得近滿矩陣，且解決無法直接完成的格型。2396 的單位移近來源須翻轉逾四分之一符號才能精確正交，精確構造需要其他來源或整體重建。[整幺模判準](OVERLATTICES.md) · [統一模十六構造](MOD16_DEFECT12_FAMILY.md) · [模三十二構造](MOD32_DEFECT12_CONSTRUCTION.md) · [精確修復下界](NEAR64_EXACT_REPAIR.md) |
| 2396 階的專用構造 | 原始循環證書、邊框證書，以及長度 599 T 序列的支撐、模四符號與奇係數逐位提升。300／299 分段下，兩區間共至多六個少數比較符號的精確構造已排除 | 任一條路線取得完整二元矩陣；單階成果的構造若可推廣再接回全題。[T 序列](T599.md) · [稀疏比較序列](T599_SPARSE_INTERVALS.md) |

## What is known about the distance

Write $r(n)=\max\{k:P(n,k)\}$. Unconditionally, for every $\epsilon>0$ and all sufficiently large multiples of four, $r(n)\ge n/2-O_\epsilon(n^{113/132+\epsilon})$. In particular the literature guarantees $(1/2-o(1))n$ orthogonal columns. Verheiden proved that **any** $n-7$ real orthogonal sign columns of length $n$ can be completed to $n$ for the orders used here. The conjecture follows if that threshold can be reached for every required $n$. The lower bound gives neither a rate of proof progress nor an effective finite search for the rest. [Graham–Shparlinski, §3](https://arxiv.org/abs/0709.2704) · [de Launey–Levin, Theorem A](https://arxiv.org/abs/1003.4003) · [Verheiden, thesis §4](https://thesis.caltech.edu/2899/) · [Verheiden, journal article](https://doi.org/10.1016/0097-3165(80)90028-X)

At $n=2396$, matching absolute projection multisets constructs **1,197 orthogonal columns** and checks all **715,806** pairwise inner products exactly. The seven-column completion theorem would apply at **2,389**. Extension may require changing the alignment or previously chosen columns. In the separate cyclic construction, 310 of 598 shift pairs vanish on one witness and 49 further original equations suffice under its documented constraints. That shift count does not measure $r(2396)$. This order remains the smallest gap in the cited frontier. [Explicit construction and next-column constraints](STACK_1197.md) · [Cyclic certificates](../hadamard-2396-coverage/README.md) · [Frontier snapshot](https://github.com/vatskishan03/Hadamard/blob/d885022144ba6bf4efa8315e14871a3736947527/FRONTIER.md)

**第 1,198 欄。** 雙通道重排保有前 1,197 欄的精確正交。最佳整數零計數的配置將最後一欄的非零內積減至 88 個。固定這組新增符號與兩部來源後，保留模八的重配有精確最小上界 16。另一組符號可讓最後一欄的全部內積只取 \(-8,0,8\)。要完成下一欄，全部誤差須在同一組配置歸零。[整數運輸證書](STACK_1198_TRANSPORT.md) · [聯合符號證書](STACK_1198_JOINT.md) · [有界排除與雙通道條件](STACK_1198.md)

固定 1,196 個舊欄及已知首條新增欄後，第二條新增欄等價於四個明列矩陣之一的模 1200 核中存在非常數二元向量。該向量會自動具有重量 600。完整延伸等價於對應的輔助 1200 階矩陣能同時滿足奇數模數碼匹配及模 32 仿射條件。[精確輔助矩陣與同餘](STACK_1198_AUXILIARY.md)

在折疊 Paley 下部、精確省略投影且舊欄殘差皆為四的倍數時，只要誤差平方和小於 4,800 且滿足模 75 輔助條件，全部殘差必為零。新重配證書達到平方和 4,032，保持前 1,197 欄精確正交及省略投影，仍欠模 75。[平方殘差與模 75 間隙](STACK_1198_ENERGY.md)

新的折疊配置已讓反對稱通道全部 599 個保留欄位精確正交，只餘對稱通道的平方誤差 2,112。對稱通道小於 2,400 時，模 25 即足以推出完全相消；此配置仍欠模 25。[單通道構造和精確門檻](STACK_1198_CHANNELS.md)

對稱通道的模 25 檢查只需 300 個連續有限行，或無窮行加 299 個連續有限行。保留指定的 896 個精確舊欄位置後，剩餘條件可化為模 5 的獨立欄檢查。若殘差絕對值小於 20，通過該檢查就能精確完成下一欄。另在現有三組支撐、固定參考欄的總置換距離三以內，任意重新配對或變號都無法完成下一欄。[模 5 資訊集](STACK_1198_MOD5.md) · [三次置換的完整排除](STACK_1198_REPLACEMENTS.md)

任意奇數 \(t>1\) 的同類疊接有精確輔助矩陣判準。來源的階數是 \(2(t-1)\) 與 \(2(t+1)\)，都比 \(4t\) 小。固定相容邊界、舊配對及一條成功欄後，完整延伸等價於二元核恰有 \(4(t+1)\) 個解。奇數模數另可化成兩個碼的相等。要由此證明全題，仍須為每個餘下奇數 \(t\) 提供能完成的來源與配對。[奇數乘數的必要且充分條件](STACK_ODD_T_AUXILIARY.md)

若下部選用 Sylvester 因子張量 \(4d\) 階來源，\(d\) 為下部階數的奇數部分且至少為三，則每個通道的平方內積殘差低於 \(32d\) 時，奇數模 \(d\) 相消足以推出整數相消。2396 階另有一個四通道的 1200 階來源，每通道門檻為 2,400。新來源仍須配合可延伸的符號欄。[統一殘差間隙與四通道來源](STACK_ODD_T_RESIDUAL.md)

四通道來源現已得到另一份 1,197 欄精確疊接。在同一來源上的第二欄候選已達殘差平方和 1,984，另一份候選只餘 130 個絕對值 4 的內積。每個低能量通道只須測試 150 條模 25 同餘。固定 596 個指定的精確配對後還可改用模 5。另一個雙通道見證令全部 597 個對稱保留欄精確相消，只餘反對稱平方誤差 1,888。各組候選仍欠各自的奇數同餘。[四通道構造、殘差與圖碼](STACK_1197_FOUR_CHANNELS.md) · [精確對稱通道](STACK_1198_RECIPROCAL.md)

四通道的新候選達到平方誤差 1,920，所有 120 個非零內積絕對值皆為 4。保留指定的 596 個精確位置，同一組基底允許各通道用模 3 或模 5，對應殘差絕對值門檻分別是 12 和 20。固定參考欄及翻號數時，任意重配仍無法在三次支撐置換內得到精確欄。雙通道的 1,888 見證則驗出 896 個模 5 的指定精確位置。一般情況若可達逐內積模 20、並讓平方誤差低於 1,600，兩個投影矩條件即足以用重配完成精確欄。[四通道共同基底及置換排除](STACK_1197_FOUR_CHANNELS.md) · [雙通道模 5 和重配定理](STACK_1198_RECIPROCAL_MOD5.md)

雙通道另有同一份來源和新增符號的兩個精確邊際。使用射影帶號排列後，各自都能匹配成 1,197 欄，且兩條新欄互相正交。在保持共同配對的問題中，重數計算得到精確內積上限 1,103，仍欠 94 個內積。[精確邊際與共同配對上限](STACK_1198_MARGINALS.md)

固定兩個公開首欄配對時，模十六的整數可提升子空間有 301 個自由位元，下一欄的帶方向省略半內積從 46 個縮至 30 個。對六種明列固定配對，交叉內積的模 3 碼亦排除了張量積輔助矩陣，完整補欄須改配或另造輔助來源。[模十六核心](STACK_1198_TWO_ADIC.md) · [交叉內積碼](STACK_ODD_T_CODE_COMPONENTS.md)

**從相鄰序列長度轉進 2396。** 已重建精確非週期 \(T(598)\)。平方和條件排除從 600 的任意互補四元組各刪一位，以及 23 與 Golay 26 乘積族的差一位插入。299 與 Golay 2 的兩種座標排序同樣已排除所有一次插入，包括兩個互為反轉的中央切點。[平方和障礙](LENGTH_CHANGE_599.md) · [Golay 2 插入排除](T599_GOLAY2_CENTRAL.md)

**四行四欄邊框。** 長度 598 的四字若在每個非零位移的合併相關均為 \(-4\)，即可直接構造完整 2396 階矩陣。它亦等價於一類指定循環軌道的外層設計。共同階 11 乘子已排除。同一組符號在原長全數達模八，並同時精確滿足 26 階及 46 階商群。保持雙商群後，每個符號半部有 131 個原長誤差座標須共同歸零。另一個精確 Paley 正半部要求長度 299 的重複自相關四元組，兩種標準四元數乘積皆無法提供。[四邊框與軌道條件](BORDER4_2396.md) · [兩個精確商群](BORDER4_2396_BOTH.md) · [Paley 分解](BORDER4_2396_PALEY_SPLIT.md)

互補支撐證書把負半部做到原長完全精確，並同時保有正半部 13 階精確商群及模四條件。原長精確非零位移已增至 181 個。另一組保留相同精確負半部，在原長全部非零位移達模十六，其中 121 個精確。保留負半部、互補支撐及正半部商群，仍須正半部的 142 個原長誤差座標歸零。精確整數譜界證明這組配置必須連同正半部的前兩條字至少改動一條。純張量重複字及四條各自完美的負半部字另有精確排除。[原長精確負半部](BORDER4_2396_EXACT_NEGATIVE.md) · [張量與稱重字限制](BORDER4_2396_TENSOR_WEIGHING.md)

另一個精確負半部支撐容許原長全部模十六，而 13 階商群只餘兩對反向位移有 \(\pm8\) 的誤差。這是該支線最小的非零商群平方誤差，仍須讓兩對同時歸零。[巢狀支撐與近精確商群](BORDER4_2396_NESTED.md)

一個經驗算的換號操作在保持原長模十六時，可在 13 階商群的 \(\pm3\) 各加八、\(\pm4\) 各減八。其支撐分組與平方和 256 的候選不同。若固定該候選的前兩條正半部，兩個二元秩條件迫使所有保留原長模十六的後兩條，以及符合必需序列和的符號選擇，維持原商群殘差。[固定前兩條的障礙](BORDER4_2396_FIXED_FIRST.md) · [換號證書](BORDER4_2396_TRANSFER.md)

對同一個平方和 256 候選，前兩條正半部合計至多三次平衡換號，且後兩條可在固定互補支撐上任意改號，仍無法同時得到原長模十六和精確 13 階商群。[完整三次換號枚舉](BORDER4_2396_SMALL_FIRST.md)

放開首兩條，其中第二條改變兩個完整纖維，可另構造保持原長模十六的平方和 256 候選。其 13 階商群在 \(\pm2\) 各差 \(+8\)、在 \(\pm3\) 各差 \(-8\)，原長有 141 個非零位移精確。[完整符號與換號驗算](BORDER4_2396_TWO_FIBERS.md)

兩個反對稱相位的乘積可精確轉移上述商群殘差。一個原長模十六見證驗證換號前後的模十六；另一個見證保留兩條前字的整數商群邊際並取得精確商群。兩條條件仍須在同一來源上合成。[反射相位的乘積恆等式與實例](BORDER4_2396_PRIMITIVE_LIFTS.md)

**五欄省略投影。** 改變 148 個行對異或的新折疊保有逐索引模八、行欄重量及全部精確 Gram，得到 39 組精確五維配對。它的索引 313 在任何重配下都無法精確相消，故 136 和 148 兩個固定折疊都需更換。保持參考配置的逐索引模八值時，要從第八個因數切換到其他因數並完成精確相消，必須改動全部五個折疊座標。[Hall 排除與 34 組見證](EXTERIOR_FOLD_HALL.md) · [新折疊及因數切換限制](EXTERIOR_FOLD_COORDINATES.md)

第二條折疊的週期碼支援另有精確容量界，已排除列出的階 13 與階 23 射影週期族。對任意可行的非零第二折疊改變，指定的 280 個座標中至少改兩個，且至多改 32 個。[週期族與縮短碼驗算](EXTERIOR_SECOND_FOLD.md)

容許重新配對並重新指派模八索引，可在同一個實體折疊保留全部 1,193 個聯合模八相消、行欄重量及省略 Gram，同時讓多對指定的 Sylvester 投影整數相消。[指定投影對見證](EXTERIOR_REINDEXED_ANCHORS.md)

保留九對見證的第二折疊以及索引 18 的原標籤，該索引的第二座標容量至多為 \(-40\)，而同標籤上部最小值為 \(-32\)。新見證重配索引 18 與 618，保留第二折疊的全部 600 位元、三對原有的完整精確配對、1,193 組模八相消及精確 Gram。新見證仍須增加精確配對才能完成五欄拼接。[整數容量界與新見證](EXTERIOR_REINDEXED_PIVOT.md)

索引 18 的重配配置已擴到十對指定精確投影。它同時保留全部模八相消、精確省略投影及兩個 Gram。固定這份第二條實體符號欄時，即使放開其他四欄與配對，第二座標的多重集也限制全配置至多有 1,121 組精確五維相消。完成此路線須改動第二條的符號方向，可繼續測試原有折疊。[十對見證與標量上界](EXTERIOR_REINDEXED_PIVOT.md)

固定第二折疊、兩半重量、七個省略投影及原有二十個指定投影的第二座標時，完整枚舉得到第二座標模十六至多 1,189 組相消。釋放其中一對指定投影後，新見證達到全部 1,193 組第二座標模十六，同時保留精確 Gram 和全部聯合模八。保持這條第二實體欄的另一個見證有十對完全精確的指定投影。[完整方向枚舉、釋放一對及同欄延伸](EXTERIOR_ORIENTATION.md)

**近正交 conference 種子。** 當 \(4t-3\) 是素數冪，可從階數 \(4t-2\) 的對稱 conference 填符號對角，再嘗試加兩行兩欄。任何完整構造的左上改動秩至少 \(t-2\)。2396 階至少要改動 2,296 條原行和原欄。[統一修復下界](CONFERENCE_PLUS_TWO.md)

## Dependency table

| ID | Statement to establish | Status |
| --- | --- | --- |
| 1 | $H(n)\Rightarrow H(2n)$. Strip powers of two from $t$. | Lean |
| 2 | Paley handles odd $t$ when $4t-1$ or $2t-1$ is a prime power, including $t=1,3$. Scarpis–Đoković handles $4t=q(q+1)$ for prime powers $q\equiv3\bmod4$. | Published |
| 3 | Normalize a square witness and extract the two incidence families below. | Proved below |
| 4 | For every remaining $t$, choose $4t-2$ blocks of size $t$ on $2t$ points so every point pair occurs $t-1$ times. This is obligation **R**. | **Open in this route** |
| 5 | Pair counts in R force all point degrees and the total number of blocks. The symmetric fractional block selection satisfies every equation. | Proved below |
| 6 | In any such design, each equal partition of the points has squared row imbalances summing to $2t^2$. For odd $t\ge3$ at most one block can be an entire half. | Lean |
| 7 | Start with the empty inner family. Its row capacities hold. | Lean |
| 8 | At every admissible prefix, the remaining row capacities give an explicit fractional next column satisfying **all** old intersections. | Lean |
| 9 | A fractional next column exists with at most $2t+j$ fractional positions after $j$ inner columns. | Linear algebra below |
| 10 | For each required $t$ and $0\le j<2t-8$, existence of an admissible prefix of width $j$ implies existence at $j+1$. This is integral obligation **B**. | **Open in this route** |
| 11 | For any candidate of the right size, the last of its $2t$ outside-point equations follows from the preceding $2t-1$. | Lean |
| 12 | The bordered incidence matrix has $1+2t+j$ mutually orthogonal sign columns. | Lean |
| 13 | Set $j=2t-8$ and apply seven-column completion. Alternatively $j=2t-1$ gives a full matrix directly. | Lean for the assembly, published for completion |
| 14 | Induction on $j$, then doubling, deduces the full conjecture from R and B. | Lean, conditional on the two open families and the cited results |

Let $D$ contain all odd $t\ge5$ missed by the three substitutions in row 2. Obligations R and B run over **every** $t\in D$. Other proved constructions may be added to the covered cases. The remaining set is infinite. For $t=599+100590k$, $k\ge0$, the integer $4t-1$ is divisible by both 5 and 479, and $2t-1$ by both 3 and 7. Only $O(\sqrt T)$ integers $t\le T$ can have $4t=q(q+1)$, while this progression has positive density. At $t=599$ the factorizations are $2395=5\cdot479$ and $1197=3^2\cdot7\cdot19$, and $16t+1=9585$ lies strictly between $97^2$ and $98^2$. [Paley (1933)](https://doi.org/10.1002/sapm1933121311) · [Đoković, Theorem 1](https://arxiv.org/abs/1601.00635)

**One infinite branch already closes.** Set $q=43^{60k+1}$ and $t=q(q+1)/4$ for $k\ge0$. Then $q\equiv43\pmod{226920}$ with $226920=8\cdot3\cdot5\cdot31\cdot61$. Thus $t$ is odd, $4t-1$ is divisible by 31 and 61, and $2t-1$ is divisible by 3 and 5. Both direct Paley tests miss every member. Applying Paley to $q+1$ and then Scarpis–Đoković gives a full $H(q(q+1))$ for **every** $k$. The modular identity is checked in Lean. Python reconstructs the first member, $H(1892)$, and checks all 1,788,886 pairwise products. This branch is an application of published constructions. [Lean congruence](Constructions.lean) · [Matrix reconstruction](verify.py) · [Đoković’s construction](https://arxiv.org/abs/1601.00635)

### 長度 3 乘積覆蓋另一個無限族

對每個 $q=107^{528k+1}$，$k\ge0$，設 $s=(q+1)/4$。有 $q\equiv107\pmod{2080120}$，所以 $s$ 為奇數。階數 $n=3(q+1)=4(3s)$ 的兩個直接 Paley 參數 $n-1$ 和 $n/2-1$ 分別有不同素因子 $17,19$ 及 $7,23$，而 $4n+1\equiv2\pmod5$，排除 $n=a(a+1)$ 的 Scarpis 輸入。Lean 核查冪次同餘以及這三個排除。

構造 $H(n)$ 用四個循環區塊的 Paley 方陣及長度 3 的 T 矩陣。取 $\mathbb F_{q^2}^\times$ 中階 $s$ 的元素 $\zeta$。它的範數為 1，且 $\gcd(s,q-1)=1$，故在射影直線上有四個長 $s$ 的軌道；每個軌道選向量代表 $v,\zeta v,\ldots,\zeta^{s-1}v$。令 Paley 矩陣的非對角項為 $\chi(\det(v_i,v_j))$，對角項為 1。標準 Paley 論證給出 $NN^{\mathsf T}=4sI$。其中任兩不同射影點的非對角字符列內積是直線上斜率的二次字符和，為零；每列的平方和是 $q$，且非對角矩陣反對稱。因乘 $\zeta$ 保持二維行列式，每個 $s\times s$ 區塊都循環。

令 $A_j(a,x)$ 為 $N$ 第 $a$ 個區塊行、第 $j$ 個區塊列的循環生成字在 $x$ 的值，取 $a\in\mathbb Z/3$ 對應前三個區塊行，$x\in\mathbb Z/s$。固定移位 $(d,e)$ 後，對 $j,x$ 求和的自相關是 $N$ 的第 $(a,0)$ 行與第 $(a+d,-e)$ 行的內積。再對 $a$ 求和，非零移位得零，零移位得 $12s$。在 $\mathbb Z/3\times\mathbb Z/s$ 上用 Goethals–Seidel 組裝即得 $H(12s)$。這是已發表的 T 矩陣乘積在長度 3 的應用。首個 $H(324)$ 已重建並逐一核查全部 52,326 個行內積。$t=599+100590k$ 恆為 $2\bmod3$，故此族仍留下該無限剩餘類。[Lean 算術](TripleProduct.lean) · [首例驗算](triple_product.py) · [乘積構造來源](https://arxiv.org/html/2610.27175v2#S4)

## The construction and its converse

Put $n=4t$, $m=4t-2$, $b=2t-1$ and $h=2t-8$. The common ground set for **columns** of the incidence matrices below has $m$ row labels. In the equivalent block-design description a row of $Y$ is a block on $2t$ points.

| Conditions on the same row labels | Exact targets |
| --- | --- |
| Outside matrix $Y$ with $2t$ columns | Each row has $t$ ones. Each column has $2t-1$ ones. Each pair of columns meets in $t-1$ rows. |
| Inside matrix $X$ with $j$ columns | Each column has $2t-2$ ones. Each pair meets in $t-2$ rows. |
| Between $Y$ and $X$ | Every outside column meets every inside column in $t-1$ rows. |

**Extraction.** Given a full square Hadamard matrix, flip column and row signs to make the first row and column positive. All other rows and columns are balanced. Separate the nonconstant columns by the second row. Exactly $2t$ have a minus, and $b$ have a plus. Delete the first two rows and encode plus as one. Call the resulting groups $Y$ and $X$. Two balanced orthogonal sign columns have exactly $t$ common positive entries. Subtract the contribution of the top two positions to get the table. For each lower row, its scalar products with the first and second rows both vanish. Subtracting the equations gives zero sign sum across its $2t$ outside positions, hence exactly $t$ ones there. The other $b$ positions then contain $t-1$ ones. This last fact supplies the capacities used below.

**Assembly.** Conversely, append two signs at the top of each incidence column. Append $(+,-)$ to $Y$ and $(+,+)$ to $X$, and add one constant positive column. Each nonconstant column has $2t$ plus signs and each pair has $t$ simultaneous plus signs. For positive supports $U,V$, the inner product is $n-2(|U|+|V|)+4|U\cap V|$, hence every off-diagonal inner product vanishes. This proves $P(4t,1+2t+j)$, with $1+2t+h=4t-7$. Conversely any full witness supplies every prefix by taking any $j$ of its $b$ inside columns. No cyclic, circulant, or multiplier symmetry is required. [Lean assembly](Assembly.lean)

## R — choose the outside blocks

There is a finite, explicit system for each $t$. For every $t$-subset $S$ of the $2t$ points introduce a variable $w_S$. For each unordered pair $\{u,v\}$ require $\sum_{S\supseteq\{u,v\}}w_S=t-1$. A nonnegative integral solution gives R. Summing over $v\ne u$ gives degree $2t-1$ at $u$. Summing those degrees gives $4t-2$ blocks. The constant rational choice $w_S=(t-1)/\binom{2t-2}{t-2}$ meets every pair equation. For odd $t\ge3$ any integral solution also satisfies $w_S+w_{S^c}\le1$, as follows from the identity below. Thus one may use binary selection variables from the outset. A way to subdivide R is to enumerate the point pairs and prove feasibility after imposing each extra equality while retaining all earlier ones.

**An obstruction for odd multipliers.** Bisect the $2t$ points in any way. In row $r$ let $a_r,b_r$ count its points on the two sides. Each of the $t^2$ cross pairs occurs $t-1$ times, so $\sum_r a_rb_r=t^2(t-1)$. Using $a_r+b_r=t$ and $m=4t-2$ gives

$$\sum_{r=1}^{4t-2}(a_r-b_r)^2=2t^2.$$

For odd $t$, every summand is positive. A row equal to either entire half contributes $t^2$. Two such rows would exhaust the sum and leave other positive terms. In particular no two rows of $Y$ are equal or complementary. At a prime $t=p\ge5$, this rules out invariance under a point permutation consisting of two $p$-cycles. Only the cycles themselves could be fixed blocks, so there is at most one. All other block orbits have size $p$, whereas the number of fixed blocks must be $4p-2\equiv p-2\pmod p$. This eliminates that proposed symmetry also at $p=599$. [Lean energy and pure-block bound](OuterEnergy.lean)

**區塊交集限制。** 固定一個區塊 $B$，取 $B,B^c$ 為等分。扣掉 $B$ 自己的 $t^2$ 和每個其他區塊至少貢獻的 $1$，得到

$$\sum_{C\ne B}\big((2|B\cap C|-t)^2-1\big)=(t-1)(t-3).$$

若某個 $C$ 的交集大小是 $1$ 或 $t-1$，該項已用完整個右端，故其餘交集只可能為 $(t\pm1)/2$。對奇數 $t\ge5$，每個區塊至多有一個這樣的鄰居。更一般地，若有 $k$ 個其他區塊的平方失衡至少為 $M$，則 $(M-1)k\le(t-1)(t-3)$。兩個限制都經 Lean 核查。[Lean 區塊交集與數量上限](OuterEnergy.lean)

**奇數 $t\ge5$ 時至少需要三種區塊交集大小。** 若只有兩種 $a<b$，設 $d=b-a$，以 $F$ 表示交集為 $b$ 的鄰接矩陣。區塊 Gram 矩陣是 $(t-a)I+aJ+dF$。另一方面 $Y^{\mathsf T}Y=tI+(t-1)J$，故在全一向量的垂直空間，$YY^{\mathsf T}$ 有兩個特徵值 $t,0$。這使整數矩陣 $F$ 的兩個特徵值為 $a/d,(a-t)/d$；有理代數整數必為整數，所以 $d$ 整除 $a,t$。令 $t=du$，$u$ 為奇數。每個區塊和其他區塊的平均交集除以 $d$ 等於 $u/2-u/(2(4t-3))$，嚴格在 $(u-1)/2$ 和 $(u+1)/2$ 之間。因 $a/d,b/d$ 相鄰，$a+b=t$ 且 $ab=(t^2-d^2)/4$。由 Gram 平方，各行的非對角交集平方和為 $t^2(t-1)$。用 $x^2=tx-ab$ 代入兩種交集值，得 $(4t-3)d^2=t^2$，即 $u(4d-u)=3$。正整數解只給 $t=1,3$。若只有一種交集大小，Gram 在全一向量的垂直空間只能有一個特徵值，也不可能。這排除了以兩種交集構成強正則圖的整條外層設計路線。

在 $t=599$，若限制為**恰三種**交集 $a<b<c$，用相同特徵值論證可知 $\gcd(b-a,c-a)$ 整除 599，故等於 1。每行的三種次數由零次、一次及二次矩 $(2393,716404,214562998)$ 唯一決定，逐一檢查得到六種正整數分布。再以交集為 $a$ 的子圖為例，模 $c-b$ 有 $P=YY^{\mathsf T}\equiv (t-b)I+bJ+(a-b)F$。在 $P^2=tP+t^2(t-1)J$ 中代入上式，便能限制 $F^2$ 的共同鄰居數。每行非對角共同鄰居之和必等於 $\deg(F)(\deg(F)-1)$。驗算器對三個例外值各做此測試，排除 $(259,295,306)$ 及 $(270,299,322)$。[完整整數枚舉](r_intersections.py)

交集組合 $(299,300,598)$ 亦不可能。令 $k=299$，$F$ 是交集 $k+1$ 的圖，$M$ 是交集 $2k$ 所給的完美配對。從 $P=(k+1)I+kJ+F+kM$ 的特徵值，得 $F^2+F=k(I+J-FM-MF-M)$。非對角各項非負，迫使兩個配對之間至多一條 $F$ 邊。配對的總度數恰為其他配對的數目，故恰有一條。在每個配對標記兩個端點為 $\pm1$，令 $T_{ij}$ 記錄從配對 $i$ 到 $j$ 的唯一邊在 $i$ 的端點符號，對角線為零。上式再給兩對端點之間的四個共同鄰居數 $k-1,0,0,k$，其中 $k-1$ 在有邊的位置。因此 $T^{\mathsf T}T=(4k+1)I-J$。由 $TT^{\mathsf T}$ 的對角線全為 $4k$，其一維零空間可取符號向量。以該向量和全一向量作邊框，得整數 $C$ 滿足 $CC^{\mathsf T}=1197I_{1198}$。

模 7 時，$\ker C=\operatorname{im}C^{\mathsf T}$。若 $Cx\equiv0$，取整數代表並令 $y=Cx/7$，便有 $C^{\mathsf T}y=171x$，而 $171$ 在模 7 可逆。反向由 $CC^{\mathsf T}\equiv0$ 得出。於是標準點積有 $599$ 維全等向子空間。取其基底及點積對偶向量作一組基，Gram 行列式成為 $(-1)^{599}$，在 $\mathbb F_7$ 不是平方。但標準點積的 Gram 行列式經換基必保持平方類，矛盾。矩方程及上述限制留下 $(1,299,300)$、$(286,299,303)$、$(286,299,309)$。再按唯一伙伴分解成 Euler 多重圖，循環與整數 Gram 條件排除 $(1,299,300)$ 的全部分支。因此恰三種交集只餘 $(286,299,303)$ 和 $(286,299,309)$，兩者的可實現性仍待證。兩組都排除了固定零點或兩點的點對合。 兩組亦排除帶單一固定點的 1197 點交換群正則構造；後一組排除同型的任意群構造。若任一譜可由完整 Hadamard 提取，固定同一標記行對而更換任何正規化欄後，每個區塊都須有六種交集。一般設計也可能有四種以上交集。[矩方程及數值核查](r_intersections.py) · [近互補譜的完整排除](NEAR_COMPLEMENT.md) · [對合與四區塊限制](R_SYMMETRY.md)

**素數乘數的交集圖不能全交換。** 若交集為 $w$ 的整數鄰接矩陣 $A_w$ 與 $P=YY^{\mathsf T}$ 交換，它便保持 $P$ 唯一的常數特徵空間，故有常數度數 $d_w$。在特徵值 $t$ 的空間，其跡是有理數和代數整數，必為整數。用該空間的投影 $E=(P-(t/2)J)/t$ 計算，
$$\operatorname{tr}(A_w E)=\frac{(2t-1)d_w(2w-t)}t.$$
對素數 $t\ge5$，所有允許的 $w$ 介乎 $1$ 與 $t-1$，所以 $t\mid d_w$。若所有交集圖都交換，其度數相加卻為 $4t-3$，矛盾。這排除素數乘數的交換交集模型。2396 階餘下兩組分布中的每個度數均非 599 的倍數，所以每個交集圖都不與 $P$ 交換。[度數與精確核查](r_intersections.py)

**2396 餘譜的線性規劃與嵌入。** 一旦基本 Gram 條件成立，常重量 Johnson 核與球面兩點核的所有階都自動半正定。對 $(286,299,309)$，若外層可嵌入完整 Hadamard，整數方差已達下界，外欄的每個低交集跨組鄰居數只能為 137 或 147。結合點對 Gram 與握手定理，至少有 570 個點的切分不均勻。兩組譜的可實現性仍開放。[兩點核](R_TWO_POINT.md) · [方差與逐欄限制](R_EMBEDDING.md)

**素數階對稱。** 若 $t=p\ge5$ 是素數，一個階為 $p$ 的點置換也可能只含一個 $p$-循環，其餘 $p$ 點固定。此時不動區塊仍只能是循環的支集及其補集。相同的區塊軌道計數排除這種置換，因此外層設計的自同構群沒有階為 $p$ 的元素。對任意奇數 $t\ge5$，若素數 $p>t$，階為 $p$ 的點置換只能有一個 $p$-循環且少於 $t$ 個不動點。它沒有任何不動區塊，故 $p\mid 4t-2$，只能是 $p=2t-1$。在 $t=599$，$2t-1=1197$ 合成，故任何素數 $p\ge599$ 都不可能是外層設計的自同構階。

完整矩陣亦有一個限制。若 $H(4p)$ 有階為 $p\ge5$ 的帶符號行列自同構，可以在各 $p$-循環內重選符號，使它成為普通行列置換。因 $H$ 可逆，兩個置換矩陣相似，同有 $k$ 個 $p$-循環。取同一行循環中的三行。它們在所有不動列上相同，任兩行卻必在恰 $2p$ 個位置相異。若 $k=1$，可變位置不足。若 $k=2$，三行在可變位置上須兩兩全反，亦不可能。若 $k=3$，有 $p$ 個不動行及 $p$ 個不動列。以一個不動行和一個不動列規範化；這些行列變號在各循環內相同，故保留置換。規範化後，各其他不動行有 $2p$ 個負號，不動列上的負號數介乎 $0$ 至 $p-1$，而每個移動列循環的貢獻是 $0$ 或 $p$。於是每個其他不動行只能在三個移動循環中的兩個取負號，其餘全正。連同首行只有四種不同的行，與 $p\ge5$ 矛盾。故 $k=4$，即行列上的作用均無不動點。這也適用於 $p=599$。此段的置換結論是上述書面推導。

## B — round the next column

Suppose $Y$ and $j$ inside columns satisfy the table. For a lower row $r$, write $d_r$ for its current number of inside ones, $u_r=t-1-d_r$ for how many ones it still needs, and $s=b-j$ for remaining inside slots. Call the prefix **admissible** if $0\le u_r\le s$ for every row. All prefixes of a full matrix are admissible. At $j=0$ every $Y$ supplies an admissible prefix.

The next binary column $z$ has to pick $2t-2$ rows. It must pick $t-1$ rows in each $Y_i$ and $t-2$ rows in each previous $X_i$. Where $u_r=0$ it must pick zero, and where $u_r=s$ it must pick one. Those boundary conditions suffice to preserve capacity after an integral step. **For any admissible prefix with $s>0$, $z_r=u_r/s$ solves every one of these equations over the rationals.** The three counts, before division, are

$$\sum_r u_r=s(2t-2),\qquad \sum_{r\in Y_i}u_r=s(t-1),\qquad \sum_{r\in X_i}u_r=s(t-2).$$

For the last identity, the previous columns contribute $(2t-2)+(j-1)(t-2)$ to $\sum_{r\in X_i}d_r$. For the middle identity they contribute $j(t-1)$. For the total they contribute $j(2t-2)$. This proves all three. Also $\sum_i |z\cap Y_i|=t|z|$ for a binary column, so one outside equation is redundant. [Lean fractional extension](Rounding.lean) · [Lean redundant equation](Constructions.lean)

**How far fractional rounding goes.** The equality matrix has at most $2t+j$ independent rows because the outside incidence rows sum to $t$ times the size equation. If more than $2t+j$ coordinates are strictly fractional, there is a nonzero rational null vector supported there. Move in that direction to the first box boundary. This keeps all equations and all previously integral positions. Repeating gives the bound in row 9 of the table. The last fractional entries can be genuinely coupled. For a Paley order-20 example the first-step polytope has a vertex with eight fractional entries. Eight independent count equations on these eight positions have minor determinant 12. The other ten entries are fixed at their bounds, so this point is a vertex. The same $Y$ has an integral solution. Thus choosing an arbitrary LP vertex does not settle B. [Exact vertex and determinant](verify.py)

**The remaining quantifier.** For every $t\in D$ and $0\le j<h$, prove that *if some admissible prefix of width $j$ exists, some admissible prefix of width $j+1$ exists*. One may replace both $Y$ and the earlier $X$ columns between steps. Proving integral rounding for every presented prefix would suffice too, but existence needs only a suitable choice. The first open rounding target is particularly concrete. Choose $2t-2$ blocks of a suitable $Y$ so every point occurs in exactly $t-1$ chosen blocks. At $t=599$ this asks for 1,196 of 2,394 blocks covering each of 1,198 points 598 times. Later columns must additionally meet every earlier selection in exactly 597 blocks. A construction for this first step on an explicitly described infinite subfamily of $D$ would advance the all-order route. [Lean implication from R and B](Rounding.lean)

### 固定前綴與固定外層設計的障礙

設 $t,j$ 皆為奇數。如果 $j$ 條內列在每一行的負載 $d_r$ 皆為偶數，則任何二元新列 $z$ 都不能保留全部內部交集。因為 $\sum_r z_r d_r$ 必為偶數，但若新列與每條舊列相交於 $t-2$ 行，這個總數便等於奇數 $j(t-2)$。由 $\sum_r d_r=j(2t-2)$ 和 $\sum_r d_r^2=j(j(t-2)+t)$，再用偶數的 $d_r^2-2d_r\equiv0\pmod8$，可得這類障礙只會出現在 $j\equiv2t-1\pmod8$。相應的兩條一般引理已用 Lean 核查。[Lean 奇偶性引理](Parity.lean)

忽略容量強制的座標時，這也是全部交集奇偶條件唯一可能的障礙。在 $\mathbb F_2$ 上，外列滿足 $Y^{\mathsf T}Y=I$，且每行的 $t$ 個一使全一向量在 $Y$ 的列空間內。令 $q=\sum_{i<j}X_i$。若 $j$ 為偶數，取 $z=q$，則 $Y^{\mathsf T}z=0$ 且 $X_i^{\mathsf T}z=1$。若 $j$ 為奇數且 $q\ne0$，選滿足 $q_r=1$ 的行 $r$，取 $w=(I+YY^{\mathsf T})e_r$。此時 $X_i^{\mathsf T}w=X_i(r)$，而 $\delta_i=1+X_i(r)$ 的總和為零。令 $z=w+\sum_i\delta_iX_i$，便有 $X_i^{\mathsf T}z=1$，因為舊內列的 Gram 矩陣是 $I+J$。$Y^{\mathsf T}z=0$ 亦保證 $z$ 的重量為偶數。這給出模二的精確可行性判準，整數交集及容量仍需另行滿足。

**可一開始就選出全寬的同餘解。** 給定任意奇數 $t\ge3$ 的 $Y$，設 $d=2t-2$ 及 $K=\ker(Y^{\mathsf T})$（在 $\mathbb F_2$ 上）。因 $Y^{\mathsf T}Y=I$，環境空間正交分解為 $K$ 與 $Y$ 的列空間。$K$ 中各向量重量為偶數，$q_K(v)=\operatorname{wt}(v)/2\bmod2$ 的極化是普通點積，因而非退化。在這個正交分解上，重量模四可相加。取虛數單位 $\mathrm i$，整個空間的權重和為 $(1+\mathrm i)^{4t-2}$；$Y$ 的正交基每項重量 $2t-1\equiv1\bmod4$，其列空間的權重和為 $(1+\mathrm i)^{2t}$。相除得

$$\sum_{v\in K}(-1)^{q_K(v)}=(1+\mathrm i)^d.$$

在 $\mathbb F_2^d$ 上，$q_0(a)=\binom{\operatorname{wt}(a)}2\bmod2$ 的極化矩陣是 $I+J$，同樣非退化。其權重和為 $(1+\mathrm i)^d$ 的實部與虛部之和，等於同一個實數，因 $4\mid d$。兩個二次型因此等距。此分類可用二維分解看出。非退化二次型若有非零等向量 $e$，可選與 $e$ 的極化值等於一的 $f$，再以 $f+e$ 調整至 $q(f)=0$，分離一個雙曲平面。維數至少四時，若兩個正交的非退化平面都沒有非零等向量，取各一個非零向量相加便得到一個。故反覆分離後至多剩一個各非零向量之 $q$ 值皆為一的平面。兩類平面的權重和分別為 $2$ 和 $-2$，因此同維數與同符號決定同一類。

取 $q_0$ 標準基及其總和並映到 $K$，得到 $d+1=2t-1$ 條內列。它們的重量皆為 $0\bmod4$、任兩列的交集皆為奇數、與外列的交集皆為偶數。這符合全部內列重量的模四目標及兩組交集的模二目標。這一步適用於任意 $Y$，而後仍要把同餘提升為指定的整數計數及行容量。這是書面推導。

在 $t=7$，一個明列的 $2$-$(14,7,6)$ 外層設計有五條相容內列，負載為一個 $0$、二十個 $2$ 和五個 $4$。因此 $j=5$ 的可行前綴具有有理下一列 $(6-d_r)/8$，但不能保留這五條內列而加第六條。Lean 直接檢查外層設計、內列、所有交集和容量，再由奇偶性證明無法延伸。另以整數枚舉 $\ker(Y^{\mathsf T}\bmod 2)$ 的 4,096 個向量，證實固定這個 $Y$ 時，能通過外層交集及重量測試的內列恰有這五條。即使重選內列，固定這個 $Y$ 也無法達到 $28-7=21$ 列的門檻。此階已有 Paley 構造，例子排除的是對任意固定 $Y$ 或前綴的延伸定理。文獻先前已記載不可嵌入完整設計的同參數例子。[Lean 28 階證書](BlockedPrefix.lean) · [完整枚舉](verify.py) · [Mackenzie–Fleming，§1](https://www.combinatorics.org/ojs/index.php/eljc/article/download/v6i1r24/pdf/)

這個例子亦有一個可精確驗算的 $E_8$ 缺陷。組裝後的 $28\times20$ 矩陣為 $A$。驗算器檢查 $Q=(28I-AA^{\mathsf T})/4$ 為對角線全為 $2$ 的整數矩陣，且第 $11,2,3,4,5,6,8,9$ 行列（從零起數）的主子式等於 $1$。由 $A^{\mathsf T}A=28I$，$Q$ 半正定且秩為 $8$，故這八個 Gram 向量生成正定偶幺模格。其餘 Gram 向量與這八個基向量均有整數內積，所以已在同一格內。秩八的正定偶幺模格唯一，因而這個格是 $E_8$。[整數 Gram 證書](verify.py) · [Elkies 的唯一性證明](https://people.math.harvard.edu/~elkies/Misc/E8.pdf)

**這個前綴最少要換掉三列。** 對 $A$ 的全部 $\binom{20}{2}=190$ 對刪除選擇，把候選符號列分成兩半，各列的 Hamming 距離相加必須是 $14$。先把候選首項固定為 $+1$，再以兩半的距離向量作精確配對。每次只有原本刪去的兩列符合，故保留任意十八列時，無法加入第三列。刪去索引 $9,12,19$（從零起數），則可加入十一列，得到完整的 $28\times28$ 矩陣。這十一列的前四列已達到二十一列的完成門檻。Lean 核查修復後完整矩陣的 378 個列對。[刪除配對及矩陣](verify.py) · [修復證書](BlockedPrefix.lean)

## Finer proof obligations with separate marginals

This equivalent variant lets one work on inside intersections before proving all the mixed counts. Put $a=\min(t,h)$.

1. Given $Y$, fix one row and choose $a$ outside columns incident with it. Clear that row in the selected columns. Every selected size and every pair intersection drop by one. These columns satisfy the inside marginal up to width $a$. [Lean seed](Reductions.lean)
2. For $a\le j<h$, prove that existence of an inside marginal of width $j$ implies existence at $j+1$. Replacing an earlier marginal is allowed. At $t=599$ this gives 591 separate growth steps.
3. Retain a **full width-$h$** inside marginal and a full $Y$. Let a stage $(j,\ell)$ mean that all mixed counts of the first $j$ inside columns hold, and the next inside column agrees with the first $\ell$ outside columns. Prove existence at $(j,\ell+1)$ from existence at $(j,\ell)$ for $\ell<2t-1$. Each step adds one equality and preserves the entire earlier set of equalities on a common witness. The final outside equality follows from row sizes. At $t=599$ this gives $1190\cdot1197=1{,}424{,}430$ single-equality steps, indexed by the same two variables for all $t$. [Lean stage theorem and three-family implication](Constructions.lean)

The compatibility condition has mathematical content. At order 20, swapping just two lower row labels in $X$ preserves both marginals and breaks eight mixed counts. Greedy extension can also fail for general partial matrices at arbitrarily large orders. Repeat every row of $H(4)$ exactly $t$ times to give four orthogonal columns of length $4t$. If a fifth column were orthogonal to these four, the four sums on the repeated row groups would form a vector in the kernel of $H(4)^{\mathsf T}$. All four sums would have to vanish, which is impossible when $t$ is odd. [Marginal permutation check](verify.py)

## Reproduction and proof boundary

Run `python3 jobs/hadamard-all-orders/verify.py` from the repository root. Python uses only the standard library. Orders 20, 44 and 60 exercise extraction, reconstruction, capacities and the fractional certificate through **every** prefix of the known solutions. For order 20 the checker also goes through all 252 choices of the first half of an equal cut of the outside points.

For the $2396\times1196$ witness, the upper block is a full matrix of order $1196=4\cdot13\cdot23$. A length-13 ternary quadruple and a symmetric length-23 Williamson quadruple give four length-299 sign words. Their summed periodic autocorrelation vanishes at every nonzero shift, as the checker verifies before building the Goethals–Seidel array. The lower block consists of 1,196 columns of the order-1,200 Sylvester double of Paley $H(600)$. Stacking corresponding columns preserves zero inner products. Both source squares and **every** pair of stacked columns are independently checked. The construction uses known ingredients and supplies a reproducible lower bound at this order. [Williamson data, pinned SageMath table](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/combinat/matrices/hadamard_matrix.py#L636) · [Goethals–Seidel array](https://github.com/sagemath/sage/blob/8de8dad7bcb38e1baa43508cbe944bf04a2d0401/src/sage/combinat/matrices/hadamard_matrix.py#L1020) · [Checker](verify.py)

**新增第 1,197 欄。** 換用四條省略下部欄，並按新欄對兩個來源的絕對內積多重集重排及變號下部欄。精確重建驗清全部新舊和舊舊欄對。保留此來源與新欄，下一欄的四維省略投影在變號下只餘 23 個方向。若完整延伸，兩種奇偶類各需四個方向，且合法方向框架只餘四對。[明確符號證書與整數限制](STACK_1197.md)

**2396 階疊接證書與外層設計的差距。** 在已公布的疊接次序下，所有行對的絕對內積最大為 $168$。上部行對內積為零，下部不同行的內積由刪去的四列所決定，絕對值至多為四。跨區行對則逐一用整數驗算。因此任意兩行最多只在 $(1196+168)/2=682$ 條原列相異。外層設計組裝的 1,199 條列要求兩條指定行相異於其中 1,198 列。這個組裝最多沿用 $682+1=683$ 條原列，至少有 513 條原列不能保留。

即使任意重排及變號後才疊接相同的上下來源，也無法保留全數 1,196 列而只加三列來得到外層設計。指定的兩行必須分處上、下兩部，因為同一部內的行對在原列上遠少於 1,195 個相異位置。令 $b$ 是指定的下部行。在每種相差整行變號視為相同的符號型態中，驗算證實四條省略列加任一原列所成的五符號型態至少出現 52 次。若兩條指定行在所有原列相反，選另一個在四條省略列上與 $b$ 相同至整行變號的下部行 $b'$。完整下部方陣的行正交性使截短後的 $b\cdot b'$ 等於 $\pm4$。兩條指定行的差與 $b'$ 的原列內積絕對值為 $8$，兩條相異的新列至多抵銷 $4$。若兩條指定行只在一條原列相同，選在該列和四條省略列上與 $b$ 同型的 $b'$。絕對值增至 $10$，三條相異的新列至多抵銷 $6$。這兩個情形都與外層設計逐行平衡所要求的零內積矛盾。這是對特定下部來源及四條省略列的排除。[精確行對及符號型態檢查](verify.py)

另一個明列的對齊提供外層設計的**六欄精確補足問題**。先取 1,192 條正交欄，疊接時特意使指定兩行符號相反。再按每行所缺正號數循環填入六欄，所得 $2396\times1198$ 符號陣的每欄均平衡，其餘 2,394 行亦均平衡。驗算確認舊欄間的 709,836 個內積全為零，這個六欄填法只滿足 7,152 個新舊欄內積中的 288 個。下一個精確接點是同時滿足全部新舊欄及六條新欄互相之間的內積，或證明此對齊無法實現。這與上文直接近滿方陣的路線有不同的欄數及閉合條件。[外層平衡重現](verify.py)

後續在同一下部來源找到 1,193 條舊欄和五條新欄，重現全部行欄平衡及十個新欄間內積。固定其上半部五符號行多重集時，所有上下欄配對均因 Gram 矩陣慣性而排除。另一個給出正定目標 Gram 的上半部型態，也因模 13 的整數實現條件而排除。換用另一個 $H(1200)$ 來源甚至有 1,195 條舊欄加三欄暫填的平衡候選。然而 Parseval 界證明，對奇數 $t\ge65$ 的規範化 $H(2t-2)/H(2t+2)$ 疊接，至多四欄的任何正交補法都不可能。明列的五欄和六欄候選還要求保留部分的消去矩陣滿欄秩。[疊接下界與滿秩證明](EXTERIOR_STACKS.md)

改選行型態及舊欄配對後，已有一組證書同時做到全部行欄平衡、新舊內積模八為零、新欄間內積模八為零，其中三個新欄間內積精確為零。Parseval 界也證明這個證書需要更換上部符號，才有機會讓全部內積精確為零。若沿用這組省略欄，任何精確五欄補法至少有四條下部新欄須距每條帶符號省略欄至少 25 格。 改排另一組實際符號行後，已在同一組欄上實現精確行欄平衡、十個新欄間內積為零、完整省略欄 Gram 及 5,965 個新舊內積模八為零。跨省略型態交換與配對調整使模十六的完整向量配對由 887 條增至 994 條，保有精確 Gram 與全部模八正交。混合位元不變量排除固定有 994 組配對的上部，容許任意下部與配對。另有 988 組配對的配置通過此必要條件，全部新舊內積仍須精確相消。任意來源的 2396 階精確五欄補法都不能有兩對互不重疊的新欄，其上部距離均至少 955。[聯合同餘證書](EXTERIOR_MOD8.md) · [模十六提升](EXTERIOR_LIFT.md) · [固定上部的排除](EXTERIOR_MOD16_INVARIANT.md) · [省略欄 Gram 與下部距離](EXTERIOR_STACKS.md) · [上部欄對距離](EXTERIOR_CONTRASTS.md)

The GitHub workflow builds the Lean files with version 4.36.0 and treats warnings as errors. The two global implication theorems expose Paley-covered cases and Verheiden completion as inputs. R, B and their alternative marginal growth assumptions remain explicit hypotheses. The fractional identities, conditional induction, row-energy and parity obstructions, order-28 blocked prefix, doubling, and assembly have kernel-checked proofs. The complete fixed-design census and Gram determinant use exact Python arithmetic. The Python replays also cover the order-324 product, the intersection classification and figure-eight determinant sieve at order 2396, the five-column Gram certificates and joint modular lift, the exact order-28 defect and the order-2396 defect-12 Gram model modulo sixteen, and the length-599 phase congruences. The geometric lattice and group-algebra arguments are written proofs with separately checked arithmetic. [GitHub Actions](../../.github/workflows/hadamard-all-orders.yml)
