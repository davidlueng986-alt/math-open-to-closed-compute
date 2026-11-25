# 對稱 conference 加兩行兩欄的統一修復下界

令 \(n=4t\)、\(m=n-2\)、\(q=m-1\)。若 \(q=4t-3\) 是素數冪，Paley 給出階數 \(m\) 的對稱 conference 矩陣 \(C\)。它的對角為零，其餘為符號，且 \(CC^{\mathsf T}=qI_m\)。選任意符號對角 \(D\)。種子 \(X=C+D\) 的兩條不同行，內積都是 \((d_i+d_j)C_{ij}\)，故絕對值至多 2。

若以 \(X\) 為左上種子來構造 \(H(n)\)，可完整保留的舊行及舊欄各至多 \(2(1+\lfloor\sqrt q\rfloor)\)。左上塊的改動矩陣秩至少 \(t-2\)。2396 階的 \(q=2393\) 為素數，這要求至少 2,296 條原行與 2,296 條原欄受到改動，且左上改動矩陣秩至少 597。這個界也容許任意選擇新加的兩行兩欄。[精確 Paley 種子與整數界重跑](conference_plus_two.py)

## 完全保留的行與欄

若一組舊行 \(I\) 在左上塊完全沒改動，並有同一個對角符號 \(d\)，其新增兩格 \(u_i\in\{\pm1\}^2\) 必須滿足
\[
 u_i\cdot u_j=-2dC_{ij}\quad(i\ne j).
\]
由右側的絕對值為 2，所有 \(u_i\) 皆平行。寫 \(u_i=\varepsilon_i u_0\) 得
\(C_I=d(I-\varepsilon\varepsilon^{\mathsf T})\)。其最大特徵值絕對值至少 \(|I|-1\)，而對稱主子矩陣的譜範數至多 \(\|C\|=\sqrt q\)。兩種對角符號各給一個大小上界，合計得所述可保留行數。對轉置使用同樣論證給出欄數界。

## 允許任意分布的改動

若左上塊改成 \(X+E\)，右上兩欄為 \(U\)，頂部 Gram 給出
\[
 R:=2I-CD-DC=XE^{\mathsf T}+E(X+E)^{\mathsf T}+UU^{\mathsf T},
 \qquad \operatorname{rank}(R)\le 2\operatorname{rank}(E)+2.
\]
按對角符號分塊後，\(R/2\) 的塊為 \(I-dC_I\)。一塊若大小為 \(s\)、秩為 \(r\)，則 \(C_I\) 至少有 \(s-r\) 個特徵值等於 \(d\)。餘下 \(r\) 個特徵值的絕對值至多 \(\sqrt q\)。又因 \(C_I\) 的平方跡是 \(s(s-1)\)，所以
\[
 s(s-1)\le(s-r)+qr,\qquad r\ge\frac{s(s-2)}{q-1}.
\]
兩塊合計並用 \(s_+^2+s_-^2\ge m^2/2\)，得
\[
 \operatorname{rank}(R)\ge\frac{m^2/2-2m}{m-2}
  =\frac m2-1-\frac{1}{m/2-1}.
\]
因秩為整數，且在此 \(m\ge6\)，故 \(\operatorname{rank}(R)\ge m/2-1=2t-2\)，進而 \(\operatorname{rank}(E)\ge t-2\)。此結論說明上述近正交種子的修復範圍，仍容許對所有受影響行欄共同改動。
