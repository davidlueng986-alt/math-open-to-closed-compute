# CAP062：cap 專用 sumset 的 Lean 形式化

本交付包含 **25 個具名 Lean 定理**，包括主定理、輔助引理及具體非空例子。全部已在公開 GitHub Actions 中以 `-DwarningAsError=true` 成功編譯；25 項公理稽核只出現標準的 `propext`、`Classical.choice`、`Quot.sound`，沒有 `sorryAx`、新增公理或 `native_decide`。

**形式化範圍是 cap 上界論證中的集合計數與切層引理。這不是整個七維數值上界 $r_3(7)\le281$ 的 Lean 證明，也沒有形式化 Hill cap 分類、全部格子證書或精確最大值。** 25 個宣告數量不代表25項新的研究結果。

## 成功版本與證據

| 項目 | 固定值 |
|---|---|
| Git commit | `9b77624cf060f7a874232f464e72ac5fe5cc5b59` |
| Actions run / job | `45285247933` / `138079773528` |
| Lean source SHA256 | `95dcee638e9b142ae0a88c679218280ac4418f5b3388848b5b3dcc034ef04516` |
| Lean | `v4.36.0` |
| mathlib commit | `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` |
| Container digest | `sha256:8ba27c4e6be1aff22d80e6444f3ef7a4d0fc0438bcadf55ef39d2c17c74ae116` |

- [成功 Actions run](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45285247933)
- [固定 commit 的 Lean 原始碼](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/9b77624cf060f7a874232f464e72ac5fe5cc5b59/jobs/capset-lean/CapSumset.lean)

`CI_RESULT_25.json` 與 `lean_axioms_25.log` 保存實際成功 run 的公理輸出；`VERIFICATION_25.json` 記錄 commit、run、job 與原始碼 SHA。`DECLARATION_AUDIT.json` 核對所有25個具名定理均有相應的 `#print axioms`。本目錄不含失敗候選、草稿或另行下載的 mathlib 原始碼。

## 一、刪點表示數與真正 cap 切層

令 $R_{A,B}(t)=\#\{(a,b)\in A\times B:a+b=t\}$。如果保留集合 $A_0,B_0$ 與第三層 $C$ 沒有混合零和三點，則每個 $c\in C$ 都滿足

$$
R_{A,B}(-c)\le |A\setminus A_0|+|B\setminus B_0|.
$$

`representation_card_le_deleted` 將固定和的每個表示歸入已刪第一端點，或由已刪第二端點唯一決定的第一端點。表示數界由此推出，並未放在前提中。此定理甚至不需要 $A_0\subseteq A$ 或 $B_0\subseteq B$。

`cap_slices_mixed` 從真正的 `IsCap K`（$K\subseteq G\times\mathbb Z/3\mathbb Z$）推出三個切層的混合零和禁制；`cap_slice_representation_bound` 因而直接將上述表示數界用到 cap。這是上界 Fourier 論證中 $r(-c)\le d$ 的組合步驟。

## 二、restricted sumset 的基數界

令 $A\widehat+ A=\{a+b:a,b\in A,\ a\ne b\}$。對 cap $A$，`negative_disjoint_restrictedSumset` 證明 $-A$ 與 $A\widehat+ A$ 不交，繼而在有限群中得到

$$
|A|+|A\widehat+ A|\le |G|.
$$

`two_point_cap`、`two_point_packing_sharp` 及 `deletion_bound_sharp` 給出非空、達等號的 kernel 核查例子。

## 三、兩側各刪兩點的雙平移覆蓋

若刪去 $\{a_1,a_2\}$ 與 $\{b_1,b_2\}$ 後，和 $t$ 完全沒有表示，定義

$$
X=(a_1+B)\cap(a_2+B),\qquad
Y=(b_1+A)\cap(b_2+A).
$$

程式證明以下兩個不同強度的結論，並將集合覆蓋轉成有限基數界：

- 若 $R_{A,B}(t)\ge3$，則 $t\in X\cup Y$。
- 若 $R_{A,B}(t)\ge4$，則 $t\in X\cap Y$。

證明先計算每側實際參與該和的已刪端點數。若不在某個雙平移交集中，該側最多提供一個已刪端點，因此得到所需矛盾。覆蓋本身不需要具名刪點相異或屬於原集合；要再代入某種特殊 cap 的非零平移交集界時，則須另外證明相異性與該交集界。

`cap_slice_deletion_holes` 與 `cap_two_deletion_high_holes_card_le` 從真實 cap 切層取得洞的前提。`two_deletion_cap_nonvacuous` 形式化一個五點 cap：原始兩層都是四點 cap，各刪兩點後，某個原有四個表示的和完全消失。因此 cap、刪點、洞及高表示數條件可以同時成立。

## 四、表示數保護完整 sumset

`sumset_eq_after_few_deletions` 證明：如果每個原始可達和都有至少 $k$ 個表示，而且兩側刪點總數少於 $k$，則

$$
(A\setminus D_1)+(B\setminus D_2)=A+B.
$$

表示數下界涵蓋**所有可達的和，包括和為零**；它不只是對 $t\ne0$ 的要求。完整 sumset 相等是結論，不是前提。`cap_slice_avoids_completed_sumset` 進一步證明：若保留點在真實 cap 的前兩層中，則第三層的負點避開完成後的整個 sumset。

這可用於反射45點 cap 的應用，但最小正表示數9仍須由另一項數學或有限證書驗證提供；本模組沒有把該數值或分類結果當作新公理。Lean 中另有 $\mathbb Z/3\mathbb Z$ 的具體 sumset 穩定性例子。

## 定義與非空性稽核

`IsCap S` 的定義是：集合中每個零和三元組都必須三點相同。在 $\mathbb F_3^n$ 這等價於沒有三個相異共線點。集合計數定理在任意交換加法群成立；cap 三層連結明確使用 `ZMod 3` 作層座標。

`MATHEMATICAL_AUDIT.md` 解釋假設的用途及非空性。兩份獨立小例子資料也可用純 Python 標準庫重算：

```bash
python verify_nonvacuity.py
```

此檢查重算五點 cap 的四表示洞，及另一個18點 cap：兩側實際各刪一點，最小正表示數3，sumset 仍有25點，第三層仍非空。後者是獨立有限枚舉的數學稽核，**不冒充已在 Lean 中形式化的18點例子**，也不代替 Lean 編譯或公理檢查。

## 重現 Lean 編譯

在存有 `CapSumset.lean` 的目錄執行：

```bash
docker run --rm -v "$PWD":/work \
  ghcr.io/davidlueng986-alt/math-compute-lean@sha256:8ba27c4e6be1aff22d80e6444f3ef7a4d0fc0438bcadf55ef39d2c17c74ae116 \
  bash -lc 'cd /opt/mathlib4 && lake env lean -DwarningAsError=true /work/CapSumset.lean'
```

公開 Actions 使用相同固定映像，在 `/opt/mathlib4` 執行：

```bash
lake env lean -DwarningAsError=true "$GITHUB_WORKSPACE/jobs/capset-lean/CapSumset.lean"
```

原始碼末尾會列印所有25個定理的公理依賴。重現時應要求編譯零錯誤、零警告，且所有公理依賴均在上述標準三種以內；不得接受 `sorryAx`、`admit`、新增公理或 `native_decide`。`MANIFEST.json` 記錄本交付各檔案的 SHA256。
