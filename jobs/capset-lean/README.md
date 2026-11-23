# Cap 專用和集引理：已通過 Lean 核心驗證

25 項具名定理、輔助引理與非空例子已在公開 GitHub Actions 通過編譯及逐項公理稽核。固定來源版本使用 Lean 4.36.0、mathlib commit `fc4f59e577feb1a4956671bc04ac18aaaf8cd842` 及固定容器 digest。

- [成功執行與完整步驟](https://github.com/davidlueng986-alt/math-open-to-closed-compute/actions/runs/45285247933)
- [已驗證的固定原始碼](https://github.com/davidlueng986-alt/math-open-to-closed-compute/blob/9b77624cf060f7a874232f464e72ac5fe5cc5b59/jobs/capset-lean/CapSumset.lean)
- [數學內容、定義與重現方法](release/README.md)
- [實際 CI 稽核結果](release/CI_RESULT_25.json)
- [固定依賴](release/DEPENDENCIES.json)；[交付雜湊清單](release/MANIFEST.json)

原始碼 SHA256：`95dcee638e9b142ae0a88c679218280ac4418f5b3388848b5b3dcc034ef04516`。

內容包括真正 cap 的三層混合禁制、刪點後的表示數上界、restricted sumset 基數界、兩側各刪兩點的高表示數洞覆蓋，以及正表示數足夠時的完整和集穩定性。所有25項宣告均有實際 `#print axioms` 記錄；依賴限於 `propext`、`Classical.choice`、`Quot.sound`，沒有未證明洞或新增公理。

此形式化驗證集合計數與 cap 切層引理。整個七維數值上界的分類輸入、格子證書與精確最大值尚未端到端形式化。數學範圍與非空性稽核詳見 release 文件。
