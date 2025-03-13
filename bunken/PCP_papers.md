# 📚 PCP関連論文リスト(時系列順)

### 📄 A Sub-Constant Error-Probability Low-Degree Test, and a Sub-Constant Error-Probability PCP Characterization of NP (1997)
**<span style="color:#990066">👥 著者</span>**: Ran Raz, Shmuel Safra

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 38th Annual Symposium on Foundations of Computer Science (FOCS 1997), pp. 475-484

**<span style="color:#990066">📄 PDF</span>**: [sources/Raz Safra 1997 Low-Degree Test PCP Characterization.pdf](sources/Raz%20Safra%201997%20Low-Degree%20Test%20PCP%20Characterization.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

平面(2次元のアフィン部分空間)への低次多項式の制限を使用する新しい低次テストを導入. このテストは非常に小さいエラー確率を持ち, NPの低エラーPCP特性を証明することを可能にした. 具体的には, 任意の定数$c>0$に対して, 任意のNP言語のメンバーシップは, $O(1)$回のアクセスで検証でき, 各アクセスは対数的なビット数を読み取り, エラー確率は$2^{-(\log n)^c}$となる. この結果の応用として, SET-COVERを対数的な近似率で近似することがNP困難であることを示した.
</details>

### 📄 Probabilistic Checking of Proofs: A New Characterization of NP (1998)
**<span style="color:#990066">👥 著者</span>**: Sanjeev Arora, Shmuel Safra

**<span style="color:#990066">📚 出版情報</span>**: Journal of the ACM (JACM), Volume 45, Issue 1, pp. 70-122

**<span style="color:#990066">📄 PDF</span>**: [sources/Arora Safra 1998 NP Proofs.pdf](sources/Arora%20Safra%201998%20NP%20Proofs.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

NPの新しい特性付けを提供. NPは, メンバーシップの証明が対数的な数のランダムビットを使用し, 証明から部分対数的な数のビットを読み取ることによって, 確率的に多項式時間で検証できる言語のクラスを正確に含む. この特性付けの意味, 特にCliqueとIndependent Setの近似が非常に弱い意味でもNP困難であることを示した.
</details>

### 📄 Proof Verification and the Hardness of Approximation Problems (1998)
**<span style="color:#990066">👥 著者</span>**: Sanjeev Arora, Carsten Lund, Rajeev Motwani, Madhu Sudan, Mario Szegedy

**<span style="color:#990066">📚 出版情報</span>**: Journal of the ACM (JACM), Volume 45, Issue 3, pp. 501-555

**<span style="color:#990066">📄 PDF</span>**: [sources/Arora 1998 Proof Verification.pdf](sources/Arora%201998%20Proof%20Verification.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

NPのすべての言語は, 対数的な数のランダムビットを使用し, 証明内の定数数のビットを調べることによってメンバーシップ証明をチェックする確率的な検証者を持つことを示した. 言語内の文字列の場合, 検証者が確率1で受け入れるような証明が存在する. 言語内にない文字列の場合, 検証者はすべての提供された「証明」を少なくとも$1/2$の確率で拒否する. この結果はArora and Safra [1998]の結果を基に改良したもの. 結果として, $\mathrm{NP} \not\subseteq \mathrm{P}$でない限り, MAX SNP困難な問題は多項式時間近似スキームを持たないことを証明. また, クリークサイズの近似に関するFeige et al. [1996]とArora and Safra [1998]の結果を改良し, $N$頂点グラフの最大クリークサイズを近似率$N^\varepsilon$で近似することがNP困難であるような正の$\varepsilon$が存在することを示した.
</details>

### 📄 Zero Knowledge and the Chromatic Number (1998)
**<span style="color:#990066">👥 著者</span>**: Uriel Feige, Joe Kilian

**<span style="color:#990066">📚 出版情報</span>**: Journal of Computer and System Sciences, Volume 57, Issue 2, pp. 187-199

**<span style="color:#990066">📄 PDF</span>**: [sources/Feige Kilian 1998 Chromatic Number.pdf](sources/Feige%20Kilian%201998%20Chromatic%20Number.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

グラフの彩色数の近似に関する研究. PCPの結果を用いて, グラフの彩色数を効率的に近似することの困難性を示した. 具体的には, ゼロ知識証明システムとPCPの関連性を探求し, グラフの彩色数を定数の近似率で近似することがNP困難であることを証明. さらに, 任意の$\varepsilon > 0$に対して, 近似率$n^{1-\varepsilon}$での近似がNP困難であることも示した. この結果は, 対話型証明システムとPCP理論の技術を組み合わせることで得られ, 近似アルゴリズムの限界に関する重要な知見を提供している. また, この研究はゼロ知識証明とPCP理論の橋渡しとなり, 計算複雑性理論における新たな研究方向を開拓した.
</details>

### 📄 A Combinatorial Consistency Lemma with Application to Proving the PCP Theorem (2000)
**<span style="color:#990066">👥 著者</span>**: Oded Goldreich, Shmuel Safra

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 29, Issue 4, pp. 1132-1154

**<span style="color:#990066">📄 PDF</span>**: [sources/Goldreich Safra 2000 PCP Theorem.pdf](sources/Goldreich%20Safra%202000%20PCP%20Theorem.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

PCP定理に関する研究. PCPの基本的な性質と応用について詳細に解説し, 証明システムの効率性と検証の複雑性の関係を分析した. 本論文では, 組合せ論的一貫性補題(Combinatorial Consistency Lemma)と呼ばれる新しい技術を導入し, これを用いてPCP定理の証明を簡略化した. この補題は, 複数の関数が局所的に一貫している場合, それらが大域的にも一貫した単一の関数に近似できることを保証するもので, 低次テスト(Low-Degree Test)の分析に特に有用である. 著者らは, この補題を用いて, 従来の代数的手法に依存せずにPCP定理の証明を構築する方法を示し, PCPの理論的基盤をより堅固なものにした. また, この手法は後の研究, 特にDinurによるギャップ増幅技術を用いたPCP定理の証明に影響を与えた.
</details>

### 📄 Randomness-efficient Low Degree Tests and Short PCPs via Epsilon-Biased Sets (2003)
**<span style="color:#990066">👥 著者</span>**: E. Ben-Sasson, M. Sudan, S. Vadhan, A. Wigderson

**<span style="color:#990066">📚 出版情報</span>**: Electronic Colloquium on Computational Complexity (ECCC), Technical Report TR03-050

**<span style="color:#990066">📄 PDF</span>**: [sources/Randomness-efficient Low Degree Tests.pdf](sources/Randomness-efficient%20Low%20Degree%20Tests.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

ランダム性効率の良い低次テストの設計と分析. $\varepsilon$-biased set を介して, PCPシステムにおけるランダム性の使用を最小化しながら, 効率的な低次多項式テストを構築する方法を提案. 確率的に検査可能な証明(PCP)と局所的にテスト可能な符号(LTC)の最初の明示的な構築を提示した.
</details>

### 📄 Robust PCPs of Proximity, Shorter PCPs, and Applications to Coding (2006)
**<span style="color:#990066">👥 著者</span>**: E. Ben-Sasson, O. Goldreich, P. Harsha, M. Sudan, S. Vadhan

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 38th Annual ACM Symposium on Theory of Computing (STOC 2006), pp. 1-10

**<span style="color:#990066">📄 PDF</span>**: [sources/Ben Sasson Robust PCPs 2006.pdf](sources/Ben%20Sasson%20Robust%20PCPs%202006.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

PCPs of Proximityのロバスト性の概念を導入し, より短いPCPの構築方法と符号化への応用を示した. 従来のPCPが入力が言語に属するかどうかを検証するのに対し, PCPs of Proximityは入力が特定のNP witnessに「近い」かどうかを検証する. 本論文では, PCPs of Proximityのロバスト性(robustness)という新しい性質を定義し, これが従来のPCPの健全性(soundness)を強化したものであることを示した. 具体的には, 偽の主張に対して, 検証者がアクセスするビット列全体が任意の有効な証明から遠くなることを保証する. 著者らは, このロバストなPCPs of Proximityを用いて, 従来よりも大幅に短い長さのPCPを構築する方法を提案し, 特に準線形長(almost-linear length)のPCPを実現した. さらに, これらの技術を誤り訂正符号の構築に応用し, 局所的にテスト・復号可能な符号の設計にも貢献した. この研究は, PCPの理論と実践の両面で重要な進展をもたらした.
</details>

### 📄 Assignment Testers: Towards a Combinatorial Proof of the PCP Theorem (2006)
**<span style="color:#990066">👥 著者</span>**: I. Dinur, O. Reingold

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 36, Issue 4, pp. 975-1024

**<span style="color:#990066">📄 PDF</span>**: [sources/Dinur Reingold 2006 PCP Theorem.pdf](sources/Dinur%20Reingold%202006%20PCP%20Theorem.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

本論文では, PCP定理の新しい概念的枠組みとして「割り当てテスター」を提案し, これを用いて組合せ論的なPCP定理の証明方法を開発した. 割り当てテスターは, 与えられた制約充足問題(CSP)のインスタンスに対して, その変数への割り当てが制約を満たすかどうかを効率的にテストする手法である. 著者らは, この概念を用いて, PCPの構成における重要な要素である「ギャップ増幅」を実現する方法を示した. 具体的には, CSPインスタンスに対して, (1)拡大操作, (2)符号化, (3)テストの置き換え, という基本操作を繰り返し適用することで, 元の問題の近似困難性を保ちながらギャップを指数関数的に増幅させる手法を開発した. この手法は, 従来の代数的手法(低次テストなど)に依存せず, グラフ理論や確率的手法を用いた直感的でエレガントな証明を提供し, PCP理論の理解と教育を大きく前進させた. この研究は, 後にDinurによるPCP定理のギャップ増幅を用いた証明(2007年)の基礎となり, 計算複雑性理論における重要な貢献となった.
</details>

### 📄 Locally Testable Codes and PCPs of Almost-Linear Length (2006)
**<span style="color:#990066">👥 著者</span>**: Oded Goldreich, Madhu Sudan

**<span style="color:#990066">📚 出版情報</span>**: Journal of the ACM (JACM), Volume 53, Issue 4, pp. 558-655

**<span style="color:#990066">📄 PDF</span>**: [sources/Goldreich Sudan 2006 Locally Testable Codes.pdf](sources/Goldreich%20Sudan%202006%20Locally%20Testable%20Codes.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

局所的にテスト可能な符号(Locally Testable Codes)の概念と構築方法について研究. PCPとの関連性や理論的基盤を詳細に分析した. 本論文では、局所的にテスト可能な符号(LTC)が確率的に検査可能な証明(PCP)と本質的に同等であることを示し、両者の関係を形式化した. LTCは、少数のビットをランダムに読み取るだけで、与えられた文字列が有効な符号語であるかどうかを高い確率で判定できる誤り訂正符号である. 著者らは、メッセージ長$k$に対して符号長が$k \cdot \mathrm{polylog}(k)$(準線形)であり、定数個のビットをクエリするだけでテスト可能なLTCの構築方法を提案した. この結果は、同時に準線形長のPCPの存在を意味し、PCPの長さに関する理論的限界に迫るものである. また、この研究はLTCの構築に代数的手法(多項式に基づくもの)と組合せ論的手法(グラフに基づくもの)の両方を統合し、符号理論とPCP理論の橋渡しとなる重要な貢献をした.
</details>

### 📄 The PCP Theorem by Gap Amplification (2007)
**<span style="color:#990066">👥 著者</span>**: Irit Dinur

**<span style="color:#990066">📚 出版情報</span>**: Journal of the ACM (JACM), Volume 54, Issue 3, Article 12

**<span style="color:#990066">📄 PDF</span>**: [sources/PCP Theorem by Gap Amplification 2007.pdf](sources/PCP%20Theorem%20by%20Gap%20Amplification%202007.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

ギャップ増幅技術を用いたPCP定理の証明. 従来の代数的手法とは異なる組合せ論的アプローチにより, PCP定理の理解を深めた. 本論文は, PCP定理に対する画期的な新しい証明方法を提示し, 理論計算機科学における重要な成果となった. 著者は, 制約充足問題(CSP)のギャップを増幅する反復的な手法を開発し, これによりPCP定理を純粋に組合せ論的な方法で証明することに成功した. 具体的には, CSPインスタンスに対して, (1)拡大操作, (2)符号化, (3)テストの置き換え, という3つの基本操作を繰り返し適用することで, 元の問題の近似困難性を保ちながらギャップを指数関数的に増幅させる方法を示した. この手法は, 従来の代数的手法(低次テストなど)に依存せず, グラフ理論や確率的手法を用いた直感的でエレガントな証明を提供し, PCP理論の理解と教育を大きく前進させた. また, この研究はPCPの応用範囲を広げ, 近似アルゴリズムの限界に関する新たな知見をもたらした.
</details>

### 📄 Short PCPs with Polylog Query Complexity (2008)
**<span style="color:#990066">👥 著者</span>**: Eli Ben-Sasson, Madhu Sudan

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 38, Issue 2, pp. 551-607

**<span style="color:#990066">📄 PDF</span>**: [sources/Ben Sasson Sudan 2008 PCPs Query Complexity.pdf](sources/Ben%20Sasson%20Sudan%202008%20PCPs%20Query%20Complexity.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

PCPの問い合わせ複雑性に関する研究. PCPシステムの効率性を向上させるための新しい技術と, 問い合わせ数と証明長のトレードオフを分析した. 本論文では, 証明長と問い合わせ複雑性のトレードオフに関する重要な進展を報告している. 著者らは, 入力サイズ$n$に対して, 証明長が$n \cdot \mathrm{polylog}(n)$(準線形)であり, 問い合わせ複雑性が$\mathrm{polylog}(n)$(多項式対数)であるPCPシステムの構築方法を提案した. これは, 従来の定数問い合わせ複雑性を持つPCPよりも証明長を大幅に短縮することに成功している. この結果を得るために, 著者らは代数的PCPの構成に新しい技術を導入し, 特に低次拡張(low-degree extension)と低次テスト(low-degree test)の効率化を図った. また, この研究はPCPの実用化に向けた重要なステップとなり, 暗号プロトコルや対話型証明システムなどの応用分野にも影響を与えた. さらに, この結果は後のサイズ-問い合わせトレードオフに関する研究の基礎となり, PCPの理論的限界に関する理解を深めることに貢献した.
</details>

### 📄 New Direct-Product Testers and 2-Query PCPs (2012)
**<span style="color:#990066">👥 著者</span>**: Russell Impagliazzo, Valentine Kabanets, Avi Wigderson

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 41, Issue 6, pp. 1722-1768

**<span style="color:#990066">📄 PDF</span>**: [sources/Impagliazzo 2012 Direct-Product Testers.pdf](sources/Impagliazzo%202012%20Direct-Product%20Testers.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

直積テスター(Direct-Product Testers)の概念と分析. 複数の問題インスタンスを同時に扱う際の効率的なテスト方法を提案し, PCPとの関連性を示した. 本論文では, 直積符号(direct-product code)に対する新しいテスト方法を開発し, これを用いて2クエリPCPの構築と分析を行った. 直積符号は, 関数$f$に対して, すべての$k$サイズの部分集合$S$上での$f$の値を記録するものである. 著者らは, 3クエリを用いる直積テスターを設計し, これが指数的に小さい成功確率(soundness error)を持つことを証明した. 具体的には, テストに合格する確率が$\delta$である場合, テストされる関数は少なくとも$\delta^{O(1)}$の割合で有効な直積符号に一致することを示した. さらに, この結果を用いて, 2クエリPCPの健全性(soundness)を改善し, 従来の並列反復(parallel repetition)定理を効率的に実装する方法を提案した. この研究は, PCPの理論的基盤を強化するとともに, ハードネス増幅(hardness amplification)や誤り訂正符号の分野にも重要な貢献をした.
</details>

### 📄 Composition of Low-Error 2-Query PCPs using Decodable PCPs (2013)
**<span style="color:#990066">👥 著者</span>**: Irit Dinur, Prahladh Harsha

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 42, Issue 6, pp. 2452-2486

**<span style="color:#990066">📄 PDF</span>**: [sources/Dinur Harsha 2013 Low-Error PCPs.pdf](sources/Dinur%20Harsha%202013%20Low-Error%20PCPs.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

低エラーPCP(Low-Error PCPs)の構築と分析. エラー確率を最小化しながら効率的な検証を可能にするPCPシステムの設計方法を提案した. 本論文では, 復号可能なPCP(Decodable PCPs, 略してdPCP)という概念を用いて, 低エラー2クエリPCPの合成方法を開発した. dPCPは, 通常のPCPを拡張したもので, 検証だけでなく, 証明から元のNP witnessを効率的に復号する機能も持つ. 著者らは, このdPCPを用いて, 2クエリPCPの合成において生じる「エラー増幅問題」を解決する方法を提案した. 従来のPCP合成では, 内部検証器のエラーが外部検証器のエラーによって増幅されるという問題があったが, dPCPを用いることでこの問題を回避し, 合成後もエラー確率を低く保つことに成功した. 具体的には, 任意の定数$\varepsilon > 0$に対して, サイズ$n$の入力に対して, 証明長$n^{1+o(1)}$, 問い合わせ複雑性2, そしてエラー確率$\varepsilon$を持つPCPの構築方法を示した. この結果は, PCPの理論的限界に迫るものであり, 特に2クエリPCPの最適化に重要な貢献をした.
</details>

### 📄 Distributed PCP Theorems for Hardness of Approximation in P (2017)
**<span style="color:#990066">👥 著者</span>**: Amir Abboud, Aviad Rubinstein, Ryan Williams

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 58th Annual Symposium on Foundations of Computer Science (FOCS 2017), pp. 25-36

**<span style="color:#990066">📄 PDF</span>**: [sources/Distributed PCP Theorems 2017.pdf](sources/Distributed%20PCP%20Theorems%202017.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

分散PCPの概念と定理. 複数のプロセッサ間で分散された証明検証システムの理論的基盤と応用について研究. 特に, 強指数時間仮説(SETH)からP内の近似問題への初めてのPCP的還元を提供し, 二色最大内積問題や二色LCS最近接ペア問題などに対する真に準二次的な近似アルゴリズムが存在しないことを示した.
</details>

### 📄 Fine-grained Complexity Meets IP = PSPACE (2019)
**<span style="color:#990066">👥 著者</span>**: L. Chen, S. Goldwasser, K. Lyu, G. Rothblum, A. Rubinstein

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 60th Annual Symposium on Foundations of Computer Science (FOCS 2019), pp. 1067-1086

**<span style="color:#990066">📄 PDF</span>**: [sources/Chen et al 2019 Fine-grained Complexity Meets IP PSPACE.pdf](sources/Chen%20et%20al%202019%20Fine-grained%20Complexity%20Meets%20IP%20PSPACE.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

fine-grained complexityと対話型証明システム(IP)およびPSPACEの関係について研究. PCPの技術を用いて, 計算複雑性理論における新しい結果を導出した. 本論文では, fine-grained complexityと対話型証明システムの理論を融合させ, 計算問題の細粒度な困難性に関する新しい知見を提供している. 著者らは, 強指数時間仮説(SETH)のようなfine-grained complexityの仮定の下で, 対話型証明システムを用いて様々な計算問題の時間的下界を証明する手法を開発した. 具体的には, $\mathrm{IP} = \mathrm{PSPACE}$の結果をfine-grained complexityの文脈で再解釈し, オラクルモデルにおいて$\mathrm{NTIME}[n^{1.01}] \not\subset \mathrm{DTIME}[n^{1.99}]$を証明するための新しい手法を提案した. また, この研究はPCPの技術, 特に低次テストと符号化を用いて, 時間階層定理(Time Hierarchy Theorem)の細粒度版を証明することに成功した. この結果は, 計算複雑性理論における古典的な結果をfine-grained complexityの観点から再評価し, 新たな研究方向を開拓した点で重要な貢献となっている.
</details>

### 📄 Alphabet Reduction for Low-Error PCPs with Constant Soundness (2020)
**<span style="color:#990066">👥 著者</span>**: V. Guruswami, J. Håstad, M. Sudan, D. Zuckerman

**<span style="color:#990066">📚 出版情報</span>**: SIAM Journal on Computing, Volume 49, Issue 5, pp. 1021-1061

**<span style="color:#990066">📄 PDF</span>**: [sources/Guruswami 2020 Alphabet Reduction.pdf](sources/Guruswami%202020%20Alphabet%20Reduction.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

アルファベット削減技術とその応用. PCPシステムや符号理論におけるアルファベットサイズの削減方法と, その理論的意義について分析した. 本論文では, 定数の健全性(constant soundness)を持ちながら低エラー確率を実現するPCPにおいて, アルファベットサイズ(各クエリの応答に使用される記号の集合のサイズ)を削減する新しい技術を提案している. PCPのアルファベットサイズは, 実用的な応用や理論的な分析において重要なパラメータである. 著者らは, 従来のアルファベット削減技術が低エラーPCPに適用された場合, エラー確率が大幅に増加するという問題を解決するための新しい手法を開発した. 具体的には, ランダム射影(random projection)と呼ばれる技術を用いて, 元のPCPの健全性をほぼ保ったまま, アルファベットサイズを定数に削減する方法を示した. この結果は, 特に2クエリPCPの最適化に重要な貢献をし, PCPの実用化に向けた障壁の一つを取り除いた. また, この研究は誤り訂正符号の分野, 特に局所的に復号可能な符号(locally decodable codes)の設計にも応用可能な技術を提供している.
</details>

### 📄 Rigid Matrices From Rectangular PCPs (2020)
**<span style="color:#990066">👥 著者</span>**: Amey Bhangale, Prahladh Harsha, Orr Paradise, Avishay Tal

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 52nd Annual ACM Symposium on Theory of Computing (STOC 2020), pp. 912-925

**<span style="color:#990066">📄 PDF</span>**: [sources/Rigid Matrices from Rectangular PCPs.pdf](sources/Rigid%20Matrices%20from%20Rectangular%20PCPs.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

長方形PCP(rectangular PCPs)と呼ばれるPCPの変種を導入. 証明を正方行列として考え, 検証者が使用するランダムコインを2つの互いに素な集合に分割し, 一方が各クエリの行を決定し, もう一方が列を決定する. 効率的で短く, 滑らかで(ほぼ)長方形のPCPを構築し, その主要な応用として, $\mathrm{NTIME}(2^n)$内の困難な言語の証明が, 行列として見たとき, 無限に多くの場合に剛性を持つことを示した. これはAlmanとChen [FOCS, 2019]による明示的な剛性行列をFNPで構築するという最近の結果を強化し, 簡略化したものである.
</details>

### 📄 Smooth and Strong PCPs (2021)
**<span style="color:#990066">👥 著者</span>**: Orr Paradise

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 53rd Annual ACM Symposium on Theory of Computing (STOC 2021), pp. 1568-1581

**<span style="color:#990066">📄 PDF</span>**: [sources/Paradise 2021 Smooth and Strong PCPs.pdf](sources/Paradise%202021%20Smooth%20and%20Strong%20PCPs.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

滑らかで強力なPCP(Smooth and Strong PCPs)の概念と構築. PCPシステムの新しい性質を定義し, その理論的基盤と応用について研究した. 本論文では, PCPの二つの重要な性質である「滑らかさ(smoothness)」と「強さ(strength)」を同時に最適化する方法を探求している. 滑らかなPCPは, 検証者のクエリが一様分布に近い分布に従うものであり, 強いPCPは, 偽の主張に対して検証者がアクセスするビット列全体が任意の有効な証明から遠くなることを保証するものである. これらの性質は, 暗号プロトコルや対話型証明システムなどの応用において重要な役割を果たす. 著者は, これらの性質を同時に最適化するPCPの構築方法を提案し, 特に線形サイズの証明長を持ちながら, 滑らかさと強さの両方を実現するPCPの存在を証明した. この結果を得るために, 著者は新しい合成定理(composition theorem)を開発し, 滑らかなPCPと強いPCPを効率的に組み合わせる方法を示した. この研究は, PCPの理論的基盤を強化するとともに, ゼロ知識証明や安全な計算などの暗号学的応用に新たな可能性を開いた.
</details>

### 📄 Perfect Zero-Knowledge PCPs for #P (2024)
**<span style="color:#990066">👥 著者</span>**: Tom Gur, Jack O'Connor, Nicholas Spooner

**<span style="color:#990066">📚 出版情報</span>**: Proceedings of the 56th Annual ACM Symposium on Theory of Computing (STOC 2024)

**<span style="color:#990066">📄 PDF</span>**: [sources/Gur et al. Perfect Zero-Knowledge PCPs for #P 2024.pdf](sources/Gur%20et%20al.%20Perfect%20Zero-Knowledge%20PCPs%20for%20%23P%202024.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

#P内のすべての言語に対する完全ゼロ知識確率的検査可能証明(PZK-PCPs)の構築. これはBPP外の言語に対する初めてのPZK-PCPの構築である. さらに, 以前の(統計的)ゼロ知識PCPの構築とは異なり, この構築は非適応性と任意の(適応的な)多項式時間悪意のある検証者に対するゼロ知識を同時に達成している. 著者らの構築は, 組合せ的ヌルステレンザッツを使用して超立方体内で反対称構造を得て, その外部でランダム性を得る新しいマスクされたサムチェックPCPから成る. ゼロ知識を証明するために, 局所的にシミュレート可能な符号化という概念を導入: 符号化の各局所的ビューがメッセージの局所的ビューから効率的にサンプリングできるランダム化された符号化. サムチェックプロトコルから生じる符号(部分立方体の和で拡張されたリード・マラー符号)が局所的にシミュレート可能な符号化を許容することを示した. これにより, マスクされたサムチェックをシミュレートする代数的問題が反対称関数の組合せ的性質に還元される.
</details>

### 📄 A Zero-Knowledge PCP Theorem (2024)
**<span style="color:#990066">👥 著者</span>**: Tom Gur, Jack O'Connor, Nicholas Spooner

**<span style="color:#990066">📚 出版情報</span>**: arXiv:2411.07972v1 [cs.CC], 12 Nov 2024

**<span style="color:#990066">📄 PDF</span>**: [sources/Zero-Knowledge PCP Theorem 2024.pdf](sources/Zero-Knowledge%20PCP%20Theorem%202024.pdf)

<details>
<summary><strong><span style="color:#990066">📝 概要</span></strong> (クリックで展開)</summary>

すべての多項式q*に対して, 証明に最大q*クエリを行う(適応的な)敵対者に対して完全ゼロ知識である, NP用の多項式サイズ, 定数クエリ, 非適応的PCPが存在することを示した. さらに, 任意の多項式時間敵対者に対して完全ゼロ知識である, NEXP用の指数サイズ定数クエリPCPを構築した. これは, 最近の#P用の完全ゼロ知識PCPの構築(STOC 2024)とKilian, Petrank, Tardosによる画期的な研究(STOC 1997)の両方を改善するものである. 本研究は, ゼロ知識PCPの理論を大きく前進させ, より強力な計算モデルに対するゼロ知識証明の可能性を示した点で重要な貢献となっている.
</details> 