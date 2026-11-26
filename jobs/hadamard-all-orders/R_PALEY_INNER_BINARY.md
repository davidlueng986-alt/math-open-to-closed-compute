# Paley 內欄的聯合模八條件

對固定 Paley 外層，以 \(m=2t-2\) 記下方行數，\(W\) 為其 \(m\times t\) 歸一化符號矩陣。已與外欄、全正欄及第一條固定內欄精確正交的欄可寫成 \(c_i=(u_i,-u_i,z_i,1,1)\)，其中 \(W^{\mathsf T}z_i=-2u_i\) 及 \(\sum_r z_{i,r}=-2\)。令 \(x_i=(z_i+\mathbf1)/2\) 是下方正號支撐，並定義
\[
d_r=\#\{j:W_{r,j}=-1\}\pmod2,\qquad q_i=x_i+d\quad\text{於 }\mathbb F_2^m.
\]
每個 \(x_i\) 重 \(t-2\)，而 \(d\) 的重量是偶數，故 \(q_i\) 的重量為奇數。[內欄方程](R_PALEY_PROJECTIVE_LIFT.md)

對任何兩條各自符合上述整數條件的候選，有
\[
c_i^{\mathsf T}c_j\equiv4q_i^{\mathsf T}q_j\pmod8.
\tag{1}
\]
因此要使新欄彼此聯合通過模八，應在既有二元正交欄的正交補中選擇下一個 \(q\)，並將它平移回 \(x=q+d\)。若從一條底層 Hadamard 來源欄開始作多位換號，這一步把可用換號遮罩限制在一個仿射二元碼內。

## 等式的推導

寫 \(n_i\) 為 \(u_i\) 的負號數，\(D_r\) 為 \(W\) 第 \(r\) 行的整數負號數。將 \(W^{\mathsf T}z_i=-2u_i\) 對上部索引加總，再用 \(\sum z_i=-2\)，得
\[
\sum_r D_r z_{i,r}=-2n_i.
\]
又 \(\sum_r D_r=t(t-1)\)，所以 \(n_i\equiv t(t-1)/2+d^{\mathsf T}x_i\pmod2\)。兩個下方字的內積等於
\[
z_i^{\mathsf T}z_j=m-4(t-2)+4x_i^{\mathsf T}x_j=-2t+6+4x_i^{\mathsf T}x_j.
\]
而 \(u_i^{\mathsf T}u_j\equiv t-2(n_i+n_j)\pmod4\)。代回完整欄內積 \(2+2u_i^{\mathsf T}u_j+z_i^{\mathsf T}z_j\)，用 \(d^{\mathsf T}d=0\) 得 (1)。

## 兩份精確部分矩陣的二元完整延伸

一組二元標準正交欄 \(q_1,\dots,q_k\) 生成非退化子空間。其正交補的特徵向量是
\[
a=\mathbf1+\sum_{i=1}^k q_i.
\]
任意補空間的 \(v\) 滿足 \(v^{\mathsf T}v=a^{\mathsf T}v\)，因二元標準點積下 \(v^{\mathsf T}v=\mathbf1^{\mathsf T}v\)。若 \(k<m\) 且 \(a=0\)，則所有剩餘向量重量皆偶，模八內欄無法再添。

反過來，若 \(a\ne0\)，可選一個奇重量向量 \(v\) 追加。當補空間維度大於一，奇重量向量至少有兩個，選 \(v\ne a\) 使下一步特徵向量 \(a+v\ne0\)。重複即可完成二元標準正交基。

驗算分別從 1,211 與 1,212 欄證書的十一與十二條非固定內欄抽出 \(q_i\)，並在各自的外層上構造完整 1,196 欄二元正交基。另用十六條各自符合原始方程的內欄檢查 (1) 的真、假兩種情形。要提升二元基，仍須同時取得每個下方字的指定整數重量、全部投影幅度及精確整數正交。[1,211 欄整數來源](R_PALEY_SKEW_INNER.md) · [1,212 欄整數來源](R_PALEY_ANCHORED_TRIPLES.md) · [二元重播](r_paley_inner_binary.py)
