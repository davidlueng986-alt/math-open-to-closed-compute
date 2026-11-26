# Cooper–Wallis 來源的兩條精確遠內欄

用長度 13 的互補選擇字與長度 23 的 Williamson 字組成一個 \(H(1196)\)。此來源有一個 23 階的行欄聯合循環自同構。同一來源上可選兩個原始下部字，各自與最近的帶號來源欄相距 503 位。兩字在 702 條來源欄上同時有絕對值為 2 的投影，足以選出共同的 600 條欄並組裝 \(2396\times1202\) 的精確部分矩陣。[整數重播](r_paley_cooper_wallis.py) · [Paley 共同選欄判準](R_PALEY_ISOTROPIC_CODE.md)

## 來源與循環相位

把既有長度 13 的選擇字拆成四個互不相交的帶號支撐 \(T_0,T_1,T_2,T_3\)。以 \(G\) 表示線性的 Goethals–Seidel 四塊陣列，再取以下四個 52 階矩陣。[選擇字](r_paley_far_alternative.py)
\[
\begin{aligned}
 E_0&=G(T_0,T_1,T_2,T_3), &
 E_1&=G(T_1,-T_0,T_3,-T_2),\\
 E_2&=G(T_2,-T_3,-T_0,T_1), &
 E_3&=G(T_3,T_2,-T_1,-T_0).
\end{aligned}
\]
令 \(W_i\) 為四個對稱的 23 階 Williamson 循環矩陣，取 Cooper–Wallis 張量和
\[
 H=\sum_{i=0}^3 E_i\otimes W_i.
\]
每個短行欄位置恰有一個 \(E_i\) 非零，故 \(H\) 每格皆是符號。重播驗證 \(E_iE_i^{\mathsf T}=13I\) 及 \(E_iE_j^{\mathsf T}+E_jE_i^{\mathsf T}=0\)。由於 \(W_i\) 對稱循環而彼此交換，交叉項逐對消去，剩下 \(13I\otimes\sum_i W_iW_i^{\mathsf T}=1196I\)。程式另逐一核對來源的 714,610 個欄內積。[Cooper–Wallis 構造](https://doc.sagemath.org/html/en/reference/combinat/sage/combinat/matrices/hadamard_matrix.html#sage.combinat.matrices.hadamard_matrix.hadamard_matrix_cooper_wallis_construction)

實體行欄索引均為 \((b,x,y)\)，其中 \(b\in\{0,1,2,3\}\)、\(x\in\mathbb Z_{13}\)、\(y\in\mathbb Z_{23}\)。每個 23 階循環塊只依賴行欄的 \(y\) 差。故同時令每行及每欄的 \(y\) 加一即保持來源，且此置換具有 23 階。重播直接按實體索引核對。[來源與自同構驗算](r_paley_cooper_wallis.py)

## 共同投影與精確內欄

兩個原始字都只依賴 \((b,y)\)，把各自的 92 個符號按上述索引順序編成位元整數，可寫為 `22fd107294e64c0c93ba5dc` 和 `3f36b7a5dc76fd10456b1b1`。把每個字沿 \(x\) 重複 13 次，得到長度 1,196 的 \(z,z'\)。兩者原始內積為零。兩字投影皆為 \(\pm2\) 的來源欄中，同號、異號各有 351 條。各取 300 條後，在半投影字上得到 \(b(z)^{\mathsf T}b(z')=0\)，故兩條完整內欄互相正交。

按重播欄順序打包，部分矩陣的 SHA-256 是 `3feea024e76c23bf87530d5788716ac38472f36e9ff5c3dfa37738aaeeb481ea`。全部 **721,801** 個欄內積均為零。此見證採用這份新來源，2396 階完整構造仍待完成。[完整欄重播](r_paley_cooper_wallis.py)

    python3 -B jobs/hadamard-all-orders/r_paley_cooper_wallis.py
