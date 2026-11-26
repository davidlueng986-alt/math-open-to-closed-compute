# 非交換的六次根乘積與區塊變換的精確條件

令 \(p\) 為正整數。若存在 \(p\times p\) 符號矩陣 \(A,B\) 滿足
\[
AB^{\mathsf T}=BA^{\mathsf T},\qquad
AA^{\mathsf T}+3BB^{\mathsf T}=4pI_p ,
\]
則長度 11 的 T 字給出完整 \(H(44p)\)。此構造允許 \(AB\ne BA\)，也不要求 \(A,B\) 循環。以上條件等價於有一個取值於四個非實六次單位根的 \(BH(p,6)\)。[非實六次根構造](https://doi.org/10.1007/s10623-015-0045-y) · [T 字代入公式，§3](https://hexagonmath.org/pdf/2611.01070v1)

所需的複數矩陣正是 \(W=(A+i\sqrt3 B)/2\)。四種符號配對使各格位於四個非實六次根，且
\[
WW^*=\tfrac14(AA^{\mathsf T}+3BB^{\mathsf T})
+\tfrac{i\sqrt3}{4}(BA^{\mathsf T}-AB^{\mathsf T}).
\]
已細分的質數 \(p\) 數列滿足 \(p\equiv1\pmod3\)，所以非實 Butson 構造所受的 Eisenstein 範數障礙在此不排除 \(p\)。此數列尚欠符合四根條件的矩陣來源。[質數分支及會議矩陣障礙](SEMIPRIME_WILLIAMSON.md)

## 由長度 11 直接構造

設 \(\boldsymbol t\) 是長度 11、逐點恰有一個活動符號的四條 T 字。對四個實變數 \(u_i\)，用標準四元數乘法矩陣 \(M(u)\) 作用於每點的 \(\boldsymbol t\)。因 \(M(u)^{\mathsf T} M(u)=(\sum_i u_i^2)I_4\)，所得四條字的合併週期自相關是 \(11(\sum_i u_i^2)\delta_0\)。其 Goethals–Seidel 陣可寫為 \(\sum_i u_i X_i\)，其中 \(X_i\) 為 44 階三元矩陣。每個格恰有一個 \(X_i\) 活動，因每個輸入點是帶符號的座標向量，而 \(M(u)\) 的每格恰有一個帶號變數。Gram 恆等式給出
\[
X_iX_i^{\mathsf T}=11I,\qquad
X_iX_j^{\mathsf T}+X_jX_i^{\mathsf T}=0\quad(i\ne j).
\]
取 \(C_0=A\)、\(C_1=C_2=C_3=B\)。則 \(\sum_i X_i\otimes C_i\) 逐格是符號，交叉 Gram 項因 \(C_i C_j^{\mathsf T}=C_j C_i^{\mathsf T}\) 成對抵消，對角項總和是 \(44pI\)。[長度 11 的來源](SEMIPRIME_WILLIAMSON.md#完整矩陣與重播) · [四係數代入證明](https://hexagonmath.org/pdf/2611.01070v1)

用已發表的 13 階非實源作對照，程式核查 \((AB)_{1,2}=1\)、\((BA)_{1,2}=-7\)（索引從零起），同時核查全部轉置乘積條件。再組出 \(H(572)\)，逐一核查 **163,306** 個行內積。[13 階源，表 1](https://hexagonmath.org/pdf/2611.01070v1) · [精確重播](unreal_butson_product.py)

## 奇數倍四階區塊的任意正交變換

令 \(d=4s\)，其中 \(s\) 為奇數。固定實正交矩陣 \(R\) 滿足 \(R^2-R+I=0\)，把六次根指數 \(k\) 送到 \(R^k\)。對來源指數陣 \((k_{ij})\)，容許任意實正交 \(U_i,V_j\)，嘗試令每格的 \(U_iR^{k_{ij}}V_j\) 都是除以 \(\sqrt d\) 的實 Hadamard 區塊。若此嘗試成功，則必有列、欄相位可將來源改成四個非實六次根。這個必要條件不需要來源本身已有正交性。

設 \(\mathcal O=\mathbb Z_{(2)}\) 為奇分母有理數環，\(L=\mathcal O^d\)，並取
\[
D=\{x\in L : \textstyle\sum_i x_i\in2\mathcal O\}.
\]
對任一 \(d\) 階實 Hadamard 區塊 \(H\)，令 \(F=H/2\)。任意兩欄的 Hamming 距離為 \(d/2=2s\)，故欄內負號數同奇偶，欄和模四相同。若 \(x\in D\)，則 \(Hx/2\) 各座標在 \(\mathcal O\) 中，其總和模二是同一個欄和除以二的餘數乘 \(\sum_i x_i\)，故 \(F D\subset D\)。同理 \((H^{\mathsf T}/2)D\subset D\)。因 \(F^{-1}=H^{\mathsf T}/(2s)\) 且 \(s\) 在 \(\mathcal O\) 可逆，遂有 \(F D=D\)。

對偶格 \(D^*=\{y:y\cdot D\subset\mathcal O\}\) 等於 \(L+\mathcal O(\mathbf1/2)\)。由 \(2e_i\) 及 \(e_i-e_j\) 在 \(D\) 可見，每個 \(D^*\) 座標的分母至多含一個 2，且所有座標模 \(\mathcal O\) 同餘。商群 \(D^*/D\) 是二維 \(\mathbb F_2\) 空間，因 \(L/D\) 及 \(D^*/L\) 各有兩元素，\(2D^*\subset D\)。其三個非零向量對應 \(D\) 的三個二重超格，其中一個是 \(L\)。由 \(F^{\mathsf T}F=sI\) 及 \(FD=D\)，也有 \(FD^*=D^*\)。由於 \(F e_j\) 各座標皆為半奇整數，故 \(F\) 送 \(L\) 到另一個超格。

可先對來源指數作列、欄相位變換，使首列與首欄全為零，並將其逆變換吸收入 \(U_i,V_j\)。由區塊假設，
\[
F_{ij}=\sqrt{s}\,U_iR^{k_{ij}}V_j,\qquad
F_{ij}=F_{i0}F_{00}^{-1}\widetilde R^{k_{ij}}F_{0j},\qquad
\widetilde R=U_0RU_0^{-1}.
\]
若每個指數皆為 \(0\bmod3\)，整體乘一個非實六次根便已符合四根條件。否則選某個 \(k_{ij}\not\equiv0\bmod3\)。上式表示 \(\widetilde R^{k_{ij}}\) 為維持 \(D,D^*\) 的有理矩陣。因 \(\widetilde R^3=-I\) 且該指數與 3 互質，其適當冪與整體符號給出 \(\widetilde R\)。因此 \(\widetilde R\) 也維持 \(D,D^*\)。

在商群 \(D^*/D\) 上，\(\widetilde R^2+\widetilde R+I=0\) 排除任何非零固定向量，故 \(\widetilde R\) 循環置換這三個超格。按這個循環把超格標成 \(\mathbb Z/3\mathbb Z\)，設 \(r_i\) 是 \((F_{i0}F_{00}^{-1})^{-1}L\) 的標號，\(c_j\) 是 \(F_{0j}L\) 的標號。每個 \(F_{ij}L\ne L\)，所以
\[
k_{ij}+c_j-r_i\not\equiv0\pmod3 .
\]
這正是把來源矩陣逐列、逐欄乘六次根，使所有格都避開實相位的條件。

對本構造的 \(d=44\)，此條件也充分。取 \(P=X_0+X_1+X_2+X_3\) 與 \(Q=X_0-X_1+X_2+X_3\)。兩者是實 Hadamard，且 \(QP^{\mathsf T}+PQ^{\mathsf T}=44I\)。所以 \(QP^{\mathsf T}/44\) 滿足所需二次式，將 \(P\) 送到 \(Q\)。已改相位的四個根再乘一個共同六次根可落在 \(\{\pm1,\pm\zeta_6\}\)，相應區塊為 \(\{\pm P,\pm Q\}\)。如果來源為 \(BH(p,6)\)，其 Gram 恆等式經此實表示及替換完整保留。任何同階實正交 \(R\) 滿足該二次式時，都與這個表示正交共軛，因 \((2R-I)/\sqrt3\) 是一個正交複結構。程式直接在 \(D^*/D\) 上核查這對 T11 區塊比值的三循環。[44 階區塊及商群重播](unreal_butson_product.py)

## 六次根矩陣未必可用

Szöllősi 的 \(BH(19,6)\) 取首三行。逐欄以第一行的指數為基準，得到兩個模三差值的有序對，共覆蓋九種中的八種，唯獨缺 \((2,2)\)。任意首三行相位平移只會平移這八對，仍包含 \((1,2)\) 或 \((2,1)\)。相應欄在三行中具有三個相異的模三相位，故任意欄相位都留下一個實根。這份資料無法沿用上述任何 \(d=4s\)、\(s\) 奇數的正交區塊變換。[19 階原矩陣](https://arxiv.org/abs/1204.5166) · [六次根 Gram 及模三差值重播](unreal_butson_product.py)

    python3 -B jobs/hadamard-all-orders/unreal_butson_product.py
