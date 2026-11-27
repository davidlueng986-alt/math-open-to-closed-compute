# Hadamard 全猜想的結案 DAG

**OPEN · 2026-11-27 · JSP-000013**　原題要求對每個正整數 $t$，構造或證明存在一個 $4t$ 階、元素為 $\pm1$、各欄互相正交的方陣。一個覆蓋全部 $t$ 的證明可以結案。一個具體 $t$ 連同排除該階**所有**此類方陣的證明，亦可以結案。[原題](https://github.com/TheJustinSunPrize/awards/blob/10e0ab6e7503b6db769029d7d68cc4ca42c011d7/problems/catalog-0001-0100.md#JSP-000013)

| 要查什麼 | 入口 |
| --- | --- |
| 每個命題、量詞、AND/OR 依賴、證據及結案規則 | [完整 DAG](GRAPH.md) · [機讀版本](dag.json) |
| 可以交給其他 agent 的工作、交付物、驗收、失敗時保留什麼 | [24 張任務卡](TASKS.md) |
| 為什麼這些節點可以接回原題 | [數學推導](lemmas.md) · [前一輪全階歸約](../README.md) |
| Lean 證到哪裡、驗證如何重跑 | [審核和重現紀錄](../VERIFICATION.md) · [GitHub Actions](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/workflows/hadamard-all-orders.yml) |

## 全題還缺甚麼

先用倍增處理偶數乘子，用 Paley 和 Scarpis–Đoković 處理已知類別。記 $D$ 為這些測試餘下的奇數 $t\ge5$。$D$ 可以包含已有其他構造的階數，例如 $t=23$ 可用已知 $H(92)$ 做對照。對每個 $t\in D$，目前最直接的兩個缺口是構造一個外部區塊設計，以及在同一組行標籤上找到足夠多條互相相容的內欄。每一步可改選較早的資料，但輸出的所有交數必須在同一份見證上成立。[全階範圍和已知類別](../README.md#dependency-table) · [Lean 條件式推論](../Rounding.lean)

現有一族可以從原本的 $D$ 劃去。對每個 $j\ge0$，Mathon 的 45 點圖配合 Turyn 的冪次定理給出 $4t=2(45^{12j+1}+1)$ 的完整方陣，首項是 92 階。在任一外部設計中，兩個只差一點的區組會給出一條與其他合法內欄自動相容的內欄。若同一點可分別與 $2t-8$ 個不同的點作這類交換，就可以補成方陣。2396 階須要至少 1190 個交換，此路線只剩 1190 至 1195 這六種度數待判定。[構造、證明及 2396 階限制](../first-match/README.md)

以下箭嘴由前提指向結論。完整圖把共同依賴、可替代的充分路線和只供實驗的紀錄逐一列明。[完整節點及依賴](GRAPH.md)

~~~mermaid
flowchart BT
    pair["外部設計 R"] --> bands["AND · R 加四段整數延伸"]
    first["第一欄"] --> bands
    early["容量自動成立的欄段"] --> bands
    mid["容量會綁住的欄段"] --> bands
    endg["只欠八欄時找到可延伸前綴"] --> bands
    bands --> rem["OR · 覆蓋所有 t ∈ D"]
    clique["同一個規則矩陣對上構造 h-clique"] --> rem
    cert["45 冪次族 AND 餘下各階有 h 個相容證書"] --> rem
    design["全參數的完整區塊分解"] --> rem
    tail["同一個 T 的尾端定理 AND 全部有限餘例"] --> rem
    rem --> yes["AND · 每個正整數 t 都有 H(4t)"]
    known["已知奇數階 AND 倍增"] --> yes
    excl["在指定 t 排除全部完整區塊分解"] --> no["OR · 一個經核實的反例"]
    allpairs["在指定 t 排除所有矩陣對上的 h-clique"] --> no
    yes --> root["OR · 原題結案"]
    no --> root
~~~

兩條正面主線共用一個表示法。在外部設計固定一個點，就得到兩個 $b\times b$ 的 0/1 規則矩陣 $A,B$，其中 $b=2t-1$。每行每欄皆有 $k=t-1$ 個 1，並且 $A^{\mathsf T}A+B^{\mathsf T}B=tI+(t-2)J$，$J$ 是全 1 矩陣。下一條內欄的第一個整數問題，是在兩側各揀 $k$ 行，令整個欄計數向量相同。將每一對選法當作頂點，兩個選法合共重疊 $t-2$ 行時連邊。在**同一**個 $A,B$ 上取得 $h=2t-8$ 個兩兩相鄰的頂點，已足夠構造 $4t-7$ 條正交欄，再由 Verheiden 補成方陣。反過來，任何完整方陣都會給出這樣的圖和頂點。[雙向證明](lemmas.md#pivot) · [圖的定義](lemmas.md#signature) · [補全定理](https://doi.org/10.1016/0097-3165(80)90028-X)

逐欄路線把關鍵歸納拆為四段。令 $j$ 為已有內欄數，$a=\min(t-1,h-1)$。下表四段無重疊，也沒有漏步。

| 節點 | 精確範圍 | 工作者要證的事 |
| --- | --- | --- |
| FIRST | $j=0$ | 若外部設計存在，證明某對 $A,B$ 有一對整數選法具有相同計數向量。 |
| EARLY | $1\le j<a$ | 證明可達寬度 $j+1$。此時行容量自動成立，計數向量還要記下與舊欄的重疊。 |
| MIDDLE | $a\le j<h-1$ | 容量為零或已滿的行會強制新位元。要同時滿足這些強制條件和全部交數。 |
| LAST-EIGHT | $j=h-1$ | 若有此前綴，證明至少有一個可成功加欄的前綴。它給出 $4t-7$ 欄，可補齊。 |

尾段已經有一個規模與階數無關的檢查。對一份固定的 $n\times(n-8)$ 前綴，其正交補空間只有八維。固定整體正負號，最多試 **128** 個符號向量。不同階數的檢查還可共用一個有限的八維行類型集合。因此可把「這份前綴能否延伸」交給精確程式，把「每個所需階數總能找到至少一份成功前綴」交給研究幾何結構的 agent。12 階的對照例說明為甚麼要容許改選舊欄。原來四欄完全無法加欄；刪去指定一欄後，精確枚舉找到 1,296 對可以補入的正交欄。[有限行類型和秩界](lemmas.md#finite-row-types-at-defect-eight) · [正反對照](verify_endgame.py)

## 第一批任務進度

| Agent 任務卡 | 可以獨立交付的第一份成果 |
| --- | --- |
| [T-SIGNATURE-ATLAS](TASKS.md#t-signature-atlas) | 已完成。兩側各 352,716 個選法，正好 21 個共有向量，每個重數均為一。[完整圖冊](../first-match/atlas.json) |
| [T-FIRST-MATCH](TASKS.md#t-first-match) | 已認領。兩個只差一點的外部區組足以構造內欄，45 冪次族已有全解。餘下階數的存在性仍待證。 |
| [T-CERTIFICATE-SUPPLY](TASKS.md#t-certificate-supply) | 可認領。在 2396 階判定近滿星形的六種度數，或構造更多整數係數證書。[剩餘行的秩界及交數](../first-match/README.md#the-unpaired-rows-when-the-star-misses-at-most-seven-points) |
| [T-LOW-TRADES](TASKS.md#t-low-trades) | 最小正誤差只能是一個交替四邊形。證明哪類保持誤差的局部交換，可以製造出一次交換就修復它的兩行。 |
| [T-TYPE-ATLAS](TASKS.md#t-type-atlas) | 先固定八維 Gram 矩陣 $G=8I$，列全行類型及各自排除的 128 位候選遮罩，並獨立核對計數。 |

任務卡的 **needs** 指開工所需的已證資料，**uses** 是可用的相關結果。研究任務可在清楚列明的數學假設下開始，完成一個階數、有限圖冊或對輔助引理的反例，各自有獨立交付價值。把上層命題標成已證時，要逐一核對適用範圍、見證及結合規則。需要切換 agent 時，交出 task ID、輸入及標籤、證明或可重跑證書、精確涵蓋範圍，並指出仍欠哪一條命題。[全部任務及驗收](TASKS.md)

可把下段連同任務卡連結直接交給一位 agent。

> 認領這張卡，在工作分支把該卡的 claim 填上 owner 和 branch。先讀卡內列出的前提及所連的數學引理，完成第一份可驗收的結果。提交時附上精確量詞、證明或證書、重跑方法，並指明它能解鎖哪個節點。預計本機超過半小時的計算，放到公開 compute repo 的 GitHub Actions。改動機讀資料後重新產生圖和清單。

## 如何讀進度

目前有 18 張卡可直接領取，1 張已認領，1 張已完成，另有 4 張要等上游成果，包括使用同一個已證截止值的有限覆核，以及最終結案審核。逐欄路線仍須補上上述兩個全稱缺口。以 2396 階為例，另一研究分支的 1,218 條正交欄已重跑，全部 741,153 個內積為零。七欄補全門檻是 2,389 條，兩者相差 1,171 條。[1,218 欄見證](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/78f36d65c9df0beb8659394e0a43b0f95d331fe9/jobs/hadamard-all-orders/R_PALEY_FULL92_EIGHTEEN.md) 此階的循環方程、任一固定前綴的失敗，以及一個真的 2396 階完整方陣，在全圖各有不同的結論。[單階證據](../README.md#what-is-known-about-the-distance) · [循環證書](../../hadamard-2396-coverage/README.md)

從 repo 根目錄可執行下列指令，檢查結案邏輯、任務依賴及目前可認領清單。

~~~sh
python3 jobs/hadamard-all-orders/closure-dag/check_dag.py --check-tasks
python3 -B jobs/hadamard-all-orders/closure-dag/render.py --check
~~~
