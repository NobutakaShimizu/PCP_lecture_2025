# Dinur(2007)のPCP定理の証明

## 1. はじめに

> **PCP定理**は計算複雑性理論における最も重要な結果の一つであり、近似アルゴリズムの限界を示す基礎となっています。

### 1.1 PCPとは何か

**確率的検査可能証明**（Probabilistically Checkable Proof, PCP）は、NP問題の証明を「ランダムに少数のビットだけ読んで検証できる形式」に変換できることを示す概念です。

> 💡 **定義：$\mathrm{PCP}(r, q)$クラス**
> 
> $\mathrm{PCP}(r, q)$は、次の条件を満たす言語$L$の集合です：
> - $O(r)$個のランダムビットを使用し
> - 証明から$O(q)$ビットだけ読み取り
> - 次の性質を保証する検証器$V$が存在する
>   * $x \in L$の場合、$\Pr[V^{\pi}(x)$が受理$] = 1$となる証明$\pi$が存在する
>   * $x \not\in L$の場合、任意の証明$\pi$に対して、$\Pr[V^{\pi}(x)$が受理$] \leq \frac{1}{2}$

### 1.2 PCP定理

> 🔍 **定理1.1（PCP定理）[Arora and Safra 1998; Arora et al. 1998]**
> 
> $\mathrm{NP} \subseteq \mathrm{PCP}(\log n, 1)$

この定理は、どんなNP問題も、証明からわずか**定数個のビット**だけを読むことで確率的に検証できることを示しています。これは古典的な証明の概念を完全に変革するものです。

### 1.3 PCPと近似困難性

PCPの最も重要な応用は、**近似アルゴリズムの限界**を示すことです。

> 💡 **定義1.2：制約**
> 
> 変数の集合$V = \{v_1, \ldots, v_n\}$とアルファベット$\Sigma$に対して、$q$項制約$(C, i_1, \ldots, i_q)$は：
> - インデックスの$q$組 $i_1, \ldots, i_q \in [n]$
> - 「受理可能な」値の部分集合 $C \subseteq \Sigma^q$
> から構成されます。
> 
> 割り当て $a: V \rightarrow \Sigma$ が $(a(v_{i_1}), a(v_{i_2}), \ldots, a(v_{i_q})) \in C$ を満たすとき、その制約は満たされます。

**制約充足問題**（CSP）は、変数の集合$V$に対する制約の集合$C = \{c_1, \ldots, c_n\}$が与えられたとき、すべての制約を満たす割り当てが存在するかどうかを決定する問題です。

PCPの近似困難性バージョンは次のように表現できます：

> 🔍 **定理1.3（PCP定理の近似困難性バージョン）**
> 
> ある整数$q > 1$とアルファベットサイズ$|\Sigma| > 1$が存在し、$\Sigma$上の$q$項制約の集合$C$が与えられたとき、$\mathrm{UNSAT}(C) = 0$か$\mathrm{UNSAT}(C) \geq \frac{1}{2}$かを決定することはNP困難である。

ここで、$\mathrm{UNSAT}(C)$は、すべての可能な割り当てにおいて満たされない制約の最小の割合を表します。

> 💡 **補題1.4**
> 
> 定理1.1と定理1.3は同値です。

## 2. Dinurのアプローチ：ギャップ増幅

Dinurの証明の核心は、**ギャップ増幅**という新しい手法です。これは制約グラフの「不満足値」（UNSAT値）を段階的に増幅していくアプローチです。

### 2.1 制約グラフ

> 💡 **定義1.5：制約グラフ**
> 
> $G = \langle(V, E), \Sigma, C\rangle$は次の条件を満たすとき、制約グラフと呼ばれます：
> 1. $(V, E)$は無向グラフで、$G$の基礎となるグラフです
> 2. 集合$V$は、アルファベット$\Sigma$上の値を取る変数の集合としても見なされます
> 3. 各辺$e \in E$には制約$c(e) \subseteq \Sigma \times \Sigma$が付随し、$C = \{c(e)\}_{e\in E}$ です

割り当て$\sigma: V \rightarrow \Sigma$に対して、$\mathrm{UNSAT}_{\sigma}(G)$は割り当て$\sigma$によって満たされない辺の割合を表します：

$\mathrm{UNSAT}_{\sigma}(G) = \Pr_{(u,v)\in E}[(\sigma(u), \sigma(v)) \not\in c(e)]$

そして、$\mathrm{UNSAT}(G) = \min_{\sigma} \mathrm{UNSAT}_{\sigma}(G)$は$G$の**不満足値**と呼ばれます。

### 2.2 メイン定理：ギャップ増幅ステップ

Dinurの証明の中心となるのは、制約グラフの不満足値を倍増させる変換です：

> 🔍 **定理1.7（メイン）**
> 
> ある$\alpha_0$が存在し、任意の有限アルファベット$\Sigma$に対して、定数$C > 0$と$0 < \alpha < 1$が存在して、制約グラフ$G = \langle(V, E), \Sigma, C\rangle$が与えられたとき、多項式時間で制約グラフ$G' = \langle(V', E'), \Sigma_0, C'\rangle$を構築でき、次の性質を満たします：
> 
> - $\mathrm{size}(G') \leq C \cdot \mathrm{size}(G)$
> - （完全性）$\mathrm{UNSAT}(G) = 0$ならば$\mathrm{UNSAT}(G') = 0$
> - （健全性）$\mathrm{UNSAT}(G') \geq \min(2 \cdot \mathrm{UNSAT}(G), \alpha)$

このステップを対数回繰り返すことで、最終的に定数のギャップを持つ制約グラフが得られ、PCP定理が証明されます。

## 3. ギャップ増幅の3つの操作

Dinurのギャップ増幅は、制約グラフに対する3つの操作から構成されています：

### 3.1 グラフべき乗（Graph Powering）

グラフべき乗は、制約グラフの不満足値を増幅する新しい操作です。

> 💡 **グラフべき乗の定義**
> 
> $d$正則制約グラフ$G = \langle(V, E), \Sigma, C\rangle$と$t \in \mathbb{N}$に対して、$G^t = \langle(V, E'), \Sigma^{d^{\lceil t/2 \rceil}}, C^t\rangle$を次のように定義します：
> - $G^t$の頂点は$G$と同じ
> - 辺：$u$と$v$の間に$k$本の平行辺があるのは、$G$において$u$から$v$への$t$歩の経路がちょうど$k$本あるとき
> - アルファベット：$G^t$のアルファベットは$\Sigma^{d^{\lceil t/2 \rceil}}$で、各値は頂点の「近傍への意見」を表す

この操作の重要な性質は、次の補題で表されます：

> 🔍 **補題1.8（増幅補題）**
> 
> $0 < \lambda < d$と$|\Sigma|$が定数のとき、定数$\beta_2 = \beta_2(\lambda, d, |\Sigma|) > 0$が存在し、任意の$t \in \mathbb{N}$と各頂点に自己ループを持つ$d$正則制約グラフ$G = \langle(V, E), \Sigma, C\rangle$で$\lambda(G) \leq \lambda$を満たすものに対して、
> 
> $\mathrm{UNSAT}(G^t) \geq \beta_2\sqrt{t} \cdot \min\left(\mathrm{UNSAT}(G), \frac{1}{t}\right)$
> 
> が成り立ちます。

グラフべき乗の利点は、UNSAT値を$\sqrt{t}$倍に増幅しながら、グラフのサイズを線形にしか増加させないことです。

### 3.2 前処理（Preprocessing）

任意の制約グラフを「良い構造」を持つものに変換するステップです：

> 🔍 **補題1.9（前処理補題）**
> 
> 定数$0 < \lambda < d$と$\beta_1 > 0$が存在し、任意の制約グラフ$G$は制約グラフ$G' = \mathrm{prep}(G)$に変換でき、次の性質を満たします：
> 
> - $G'$は自己ループを持つ$d$正則グラフで、$\lambda(G') \leq \lambda < d$
> - $G'$は$G$と同じアルファベットを持ち、$\mathrm{size}(G') = O(\mathrm{size}(G))$
> - $\beta_1 \cdot \mathrm{UNSAT}(G) \leq \mathrm{UNSAT}(G') \leq \mathrm{UNSAT}(G)$

### 3.3 アルファベット削減（Alphabet Reduction by Composition）

グラフべき乗によって増加したアルファベットサイズを削減するための操作です。この操作は、PCPの構築において重要な役割を果たし、多くの研究がなされてきました。

> 🔍 **補題1.10（合成補題）**
> 
> 定数の拒否確率$\varepsilon > 0$とアルファベット$\Sigma_0$（$|\Sigma_0| = O(1)$）を持つ割り当てテスター$P$が存在すると仮定します。$P$にのみ依存する定数$\beta_3 > 0$が存在し、任意の制約グラフ$G = \langle(V, E), \Sigma, C\rangle$に対して、線形時間で制約グラフ$G' = G \circ P$を計算でき、$\mathrm{size}(G') = c(P, |\Sigma|) \cdot \mathrm{size}(G)$かつ
> 
> $\beta_3 \cdot \mathrm{UNSAT}(G) \leq \mathrm{UNSAT}(G') \leq \mathrm{UNSAT}(G)$
> 
> を満たします。

#### 3.3.1 アルファベット削減に関する主要文献

アルファベット削減は、PCP理論において長年研究されてきた重要なテーマです。以下に、この分野の主要な文献をいくつか紹介します：

1. **Arora and Safra (1998)** [1] - PCPの最初の定式化において、アルファベットサイズを削減するための「並列化」と「低次テスト」の技術を導入しました。
   [詳細は論文リストを参照](PCP_papers.md#-probabilistic-checking-of-proofs-a-new-characterization-of-np-1998)

2. **Guruswami, Håstad, Sudan, and Zuckerman (2020)** [2] - 「Alphabet Reduction for Low-Error PCPs with Constant Soundness」では、低エラーPCPのためのアルファベット削減技術を提案し、ランダム射影（random projection）を用いて健全性をほぼ保ったままアルファベットサイズを定数に削減する方法を示しました。
   [詳細は論文リストを参照](PCP_papers.md#-alphabet-reduction-for-low-error-pcps-with-constant-soundness-2020)

3. **Dinur and Harsha (2013)** [3] - 「Composition of Low-Error 2-Query PCPs using Decodable PCPs」では、復号可能なPCP（Decodable PCPs）を用いて、2クエリPCPの合成におけるエラー増幅問題を解決し、アルファベットサイズを効率的に削減する方法を提案しました。
   [詳細は論文リストを参照](PCP_papers.md#-composition-of-low-error-2-query-pcps-using-decodable-pcps-2013)

4. **Ben-Sasson, Goldreich, Harsha, Sudan, and Vadhan (2006)** [4] - 「Robust PCPs of Proximity, Shorter PCPs, and Applications to Coding」では、PCPs of Proximityの概念を導入し、効率的なアルファベット削減のための新しい合成手法を開発しました。
   [詳細は論文リストを参照](PCP_papers.md#-robust-pcps-of-proximity-shorter-pcps-and-applications-to-coding-2006)

5. **Moshkovitz and Raz (2010)** [5] - 「Two-Query PCP with Subconstant Error」では、サブ定数のエラー確率を持つ2クエリPCPの構築において、効率的なアルファベット削減技術を提案しました。
   [論文の詳細](https://dl.acm.org/doi/10.1145/1857914.1857917)

これらの研究は、アルファベット削減の理論的基盤を提供し、Dinurのギャップ増幅手法の重要な構成要素となっています。

> 💡 **アルファベット削減の重要性**
> 
> アルファベット削減は、PCPの構築において次の理由から重要です：
> 
> 1. **反復可能性** - ギャップ増幅ステップを繰り返し適用するためには、各ステップ後にアルファベットサイズを制御する必要があります。
> 2. **近似困難性** - 小さいアルファベットサイズのPCPは、より強力な近似困難性結果をもたらします。
> 3. **実用性** - 小さいアルファベットサイズは、PCPに基づく暗号プロトコルなどの実用的な応用において重要です。

## 4. 組み合わせ増幅ステップ

これら3つの操作を組み合わせることで、ギャップ増幅ステップが完成します：

1. 制約グラフ$G_i$を前処理する
2. 結果を$t$乗する
3. 結果を割り当てテスター$P$と合成する

つまり、$G_{i+1} = (\mathrm{prep}(G_i))^t \circ P$ となります。

このステップを$\log |G|$回繰り返すことで、PCP定理が証明されます。

## 5. 結論と応用

Dinurの証明は、PCP定理に対する新しい組合せ論的アプローチを提供しました。この手法は：

1. **短いPCPと局所的にテスト可能な符号**（Locally Testable Codes, LTCs）の構築
2. **割り当てテスター**（Assignment Testers）への拡張

など、多くの応用を持っています。

特に、この手法により、長さが$n \cdot \mathrm{poly} \log n$で、定数個のクエリで確率的に検証できるPCPとLTCの構築が可能になりました。

> 🔍 **結果**
> 
> $\mathrm{SAT} \in \mathrm{PCP}_{1/2,1}(\log^2(n \cdot \mathrm{poly} \log n), O(1))$

Dinurの証明は、その組合せ論的な性質と直感的な理解のしやすさから、PCP理論の教育と研究に大きな影響を与えました。

## 参考文献

[1] S. Arora and S. Safra, "Probabilistic Checking of Proofs: A New Characterization of NP," Journal of the ACM, vol. 45, no. 1, pp. 70-122, 1998.

[2] V. Guruswami, J. Håstad, M. Sudan, and D. Zuckerman, "Alphabet Reduction for Low-Error PCPs with Constant Soundness," SIAM Journal on Computing, vol. 49, no. 5, pp. 1021-1061, 2020.

[3] I. Dinur and P. Harsha, "Composition of Low-Error 2-Query PCPs using Decodable PCPs," SIAM Journal on Computing, vol. 42, no. 6, pp. 2452-2486, 2013.

[4] E. Ben-Sasson, O. Goldreich, P. Harsha, M. Sudan, and S. Vadhan, "Robust PCPs of Proximity, Shorter PCPs, and Applications to Coding," SIAM Journal on Computing, vol. 36, no. 4, pp. 889-974, 2006.

[5] D. Moshkovitz and R. Raz, "Two-Query PCP with Subconstant Error," Journal of the ACM, vol. 57, no. 5, pp. 1-29, 2010. 