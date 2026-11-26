# Paley 倍增斜會議矩陣沒有反轉對合

令 $r\equiv3\pmod4$ 為至少 $19$ 的質數冪。取 $r+1$ 階 Paley 斜會議矩陣 $C$，令
\[
H_2=\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad
J_2=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\qquad
T=C\otimes H_2+I\otimes J_2 .
\]
$T$ 是 $2(r+1)$ 階斜會議矩陣，且不存在任何帶符號置換矩陣 $Q$ 使 $QTQ^{\mathsf T}=-T$。因此無論選哪個頂點歸一化、是否先重標或作符號切換，$T$ 都不能供給反轉 Yamada 構造的 $2r+1$ 點核心。此結果只針對這份倍增來源。[倍增公式](R_SKEW_CONFERENCE_DOUBLING.md) · [反轉 Yamada 構造](YAMADA_CIRCULANT_REVERSE.md)

## 由四行乘積辨認倍增配對

將 $T$ 的座標寫成 $(a,i)$，其中 $a$ 為 $C$ 的座標，$i\in\{0,1\}$。稱四個互異座標組成的集合 $F$ 為閉合，若把 $T$ 在這四行的格逐欄相乘，所得符號在所有 $F$ 外的欄恒定。帶符號置換共軛及整體變號均保留此性質：四行的符號因子給出與欄無關的常數，每欄自身的符號因子出現四次。

四行若正好由兩組完整配對組成，則對每個外部欄，$C$ 的格皆出現偶數次，$H_2$ 的兩行乘積也出現兩次，故四行乘積恒為 $1$。反向時，對 $a$ 避開四行所在的原始座標，欄 $(a,0),(a,1)$ 的乘積之比為 $(-1)^{\sum_{(b,i)\in F}i}$，所以閉合必迫使此指數為偶數。其餘因子便是 $C$ 中出現奇數次的原始行所給的乘積。

- 若四行的原始重數為 $(2,1,1)$，則兩條單行在除三個原始座標外的 $r-2$ 處有相同逐位乘積。這兩原始行在自己的兩處乘積為零，在重複座標處只有一個符號可補償，與行正交矛盾。
- 若四個原始座標皆不同，視 $C$ 為 $\mathbb F_r\cup\{\infty\}$ 上的 Paley 矩陣。若四個原始座標中有 $\infty$，則在有限欄上的乘積為平方自由三次多項式的二次特徵，閉合將給絕對值 $r-3$ 的全域特徵和，超出 Weil 界 $2\sqrt r$。若沒有 $\infty$，同理為四次、絕對值 $r-4$，超出 Weil 界 $3\sqrt r$。兩個嚴格不等式都在 $r\ge19$ 成立。[有限域二次特徵和的 Weil 界，Lidl–Niederreiter Theorem 5.41](https://doi.org/10.1017/CBO9780511525926)

故閉合四集合恰為兩個完整配對的聯集。同一配對的兩個座標同時出現在 $r$ 個閉合集，不同配對的兩個座標只同時出現在一個閉合集。因此任何可能的反轉共軛都必把倍增配對送到倍增配對。

## 二階區塊排除反轉

若有上述 $Q$，以 $Q_a$ 表示它把原始配對 $a$ 送到某一配對時所用的二階帶符號置換矩陣。每個對角區塊都要求
\[
Q_aJ_2Q_a^{\mathsf T}=-J_2,
\]
所以 $\det Q_a=-1$。任意相異的 $a,b$ 的交叉區塊則有 $Q_a H_2 Q_b^{\mathsf T}=\pm H_2$，即 $Q_b=\pm H_2 Q_a H_2/2$。取三組相異配對，後兩組的二階矩陣必相等至多差整體符號，再比較兩者的交叉區塊，得到其中一個必滿足 $Q_b=\pm H_2 Q_b H_2/2$。然而行列式 $-1$ 的二階帶符號置換矩陣只有正負的 $\operatorname{diag}(1,-1)$ 及正負的對換矩陣。$H_2$ 共軛把這兩種類互換，故矛盾。

任何反轉核心置換 $R$ 都會在對應的歸一化斜會議矩陣上給出 $\operatorname{diag}(-1,R)$ 的反轉共軛。於是本證明涵蓋歸一化頂點及切換的任意選擇。小階重播取 $r=19$，從 40 階矩陣的全數 91,390 個四集合中得到 190 個閉合集，恰為所有倍增配對的兩兩聯集。

## 巨型質數候選的精確範圍

已證 $r=307076037508906904285239$ 為質數且 $r\equiv3\pmod4$，故此 Paley 倍增在該候選確實存在。通常的 Yamada–Kiyasu 構造只需斜會議矩陣，故以 $p=4r+3$、已證質數 $q=p-2\equiv5\pmod8$ 可得到 $H(4p)$。此處目標 $H(44p)$ 的反轉乘積要求更強的性質，不能以這份倍增矩陣代入。其他非循環斜來源和全域整數 Gram 路線仍可嘗試。[Yamada Theorem 4](https://www.cambridge.org/core/journals/journal-of-the-australian-mathematical-society/article/some-new-series-of-hadamard-matrices/2CF4B3D949273D45717E6F5FED183827) · [候選質性重播](yamada_circulant_reverse.py)

```sh
python3 -B jobs/hadamard-all-orders/yamada_paley_doubling_reverse_limit.py
```
