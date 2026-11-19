# #700(a) の追加結果　素数を動かしたときの等号

2026年11月19日。ここで $f(n)$ は $2\le k\le\lfloor n/2\rfloor$ における $\gcd(n,\binom nk)$ の最小値である。本稿は11月18日付の原稿の定理1を出発点とする。主な追加結果は、固定した任意の余因子に対する素数の密度と、余因子 $8$ における例外の完全な分類である。 [元の研究ノート](erdos-700-general-criterion.pdf)

## 固定した余因子に対する素数の密度

**定理.** 整数 $m\ge2$ を固定し、$E_m(X)$ を $m<p\le X$ かつ $f(mp)<m$ となる素数 $p$ の個数とする。$m$ のみに依存する $\delta_m,C_m>0$ があって、すべての整数 $X\ge1$ で

$$
E_m(X)\le C_m X^{1-\delta_m}.
$$

とくに $\pi(X)$ を $X$ 以下の素数の個数とすると $E_m(X)/\pi(X)\to0$ であり、$f(mp)=m$ となる素数の相対密度は $1$ である。$p>m$ では $mp$ の最大素因数も最大の素数べき約数も $p$ なので、両版の #700(a) で同じ等号を数えている。元の原稿の定理2では素数 $q$ を固定し、$n=mq^e$ の指数 $e$ の分布を数えている。 [有限の個数評価](Erdos700/Sparse.lean) · [べき乗による評価と密度](Erdos700/Density.lean)

### 候補列と繰り上がり

$n=mp$ とする。$n\mid k\binom nk$ から $n\mid k\gcd(n,\binom nk)$ が従う。$p\nmid k$ なら列の最大公約数は素数 $p$ の正の倍数なので $m$ より大きい。$k=tp$ ならLucasの定理により $\binom{mp}{tp}\equiv\binom mt\pmod p$ であり、$m<p$ なので右辺は $p$ で割れない。したがってこの列の最大公約数は $\gcd(m,\binom{mp}{tp})$ である。列 $k=p$ はちょうど $m$ を与える。以上から

$$
f(mp)=m \quad\Longleftrightarrow\quad
m\mid\binom{mp}{tp}\quad(1\le t\le\lfloor m/2\rfloor)
$$

を得る。 [候補列の必要十分条件](Erdos700/LargePrime.lean)

$\ell^a\parallel m$ ごとに、$H$ を $m\le\ell^H$ となる最小の整数とし、$L=H+a-1$ とおく。$p$ の $\ell$ 進表示で、下から位置 $d$（一の位が $0$）から数字 $\ell-1$ が $L$ 個連続しているとする。$v=\ell^d-(p\bmod\ell^d)$ とおけば $1\le v\le\ell^d$。$H\le j\le H+a-1$ と $M=\ell^{d+j}$ に対して $p\equiv-v\pmod M$ かつ $mv\le M$ である。$0<t<m$ のとき、$tp$ と $(m-t)p$ の法 $M$ での剰余はそれぞれ $M-tv$ と $M-(m-t)v$ で、和は $2M-mv\ge M$。相異なる $a$ 個の位置で繰り上がるため、Kummerの定理により $\ell^a\mid\binom{mp}{tp}$ がすべての $t$ で同時に成立する。これが各 $\ell\mid m$ で成立すれば $f(mp)=m$ となる。 [桁条件の形式証明](Erdos700/LargePrime.lean)

### 例外を数える

$B_\ell=\ell^{L}$ とおく。$\ell$ 進の桁を下から $L$ 桁ずつまとめると、$B_\ell$ 進表示の数字 $B_\ell-1$ は、上で使った連続する $L$ 個の桁に対応する。したがって例外の素数では、少なくとも一つの $\ell\mid m$ についてこの数字が一度も現れない。$B=B_\ell$ とし、$0\le x\le X$ の表示を、先頭の $0$ を許して $r=1+\lfloor\log_B X\rfloor$ 桁にそろえる。各桁には高々 $B-1$ 通りの選び方があるので、

$$
E_m(X)\le\sum_{\ell\mid m,\ \ell\ \mathrm{prime}}
(B_\ell-1)^{\,1+\lfloor\log_{B_\ell}X\rfloor}.
$$

$\theta_\ell=\log(B_\ell-1)/\log B_\ell<1$ とすれば、各項は $(B_\ell-1)X^{\theta_\ell}$ 以下である。$\delta_m=1-\max_{\ell\mid m}\theta_\ell$、$C_m=\sum_{\ell\mid m}(B_\ell-1)$ と取れる（最大・和はいずれも素数にわたる）。Leanでの密度の証明は、MathlibのChebyshev関数の評価から $X\le8\pi(X)\log X$（$X\ge32$）を導き、$\log X/X^{\delta_m}\to0$ を使う。 [有限個の桁列の数え上げ](Erdos700/Sparse.lean) · [極限の形式証明](Erdos700/Density.lean)

## $n=8p$ の例外の完全分類

**定理.** $p>8$ を素数とする。$p-1$ または $3p-1$ が $2$ のべきなら $f(8p)=4$ であり、それ以外は $f(8p)=8$ である。たとえば $3\cdot11-1=32$ なので $f(88)=4$ であり、$p=13$ では $f(104)=8$ である。 [分類の形式証明](Erdos700/EightPrime.lean)

$w(x)$ を $x$ の二進表示にある $1$ の数とする。調べる列は $k=p,2p,3p,4p$ だけでよい。$k=p,3p$ は $8$ と互いに素なので、$8\mid k\gcd(8p,\binom{8p}k)$ と前節の列の評価から、どちらの最大公約数も $8$ である。$k=2p,4p$ ではKummerの桁和公式から、二項係数の $2$ 進付値は順に $w(3p)$ と $w(p)$ となる。よって

$$
f(8p)=2^{\min(3,w(p),w(3p))}.
$$

奇数 $x>1$ の二進表示は末尾が $1$ なので $w(x)\ge2$。$w(x)=2$ は $x=2^j+1$ と同値である。これで分類が従う。各指数 $j$ に対して二つの方程式がそれぞれ高々一つの $p$ を与えるため、$8<p\le X$ の例外は $O(\log X)$ 個である。

この二つの形には数論での名前がある。$2^j+1$ が素数なら、$j$ は $2$ のべきである。実際、$j$ が奇因子 $s>1$ をもてば $2^{j/s}+1$ が真の約数になる。また $3p=2^j+1$ なら $j$ は奇数である。$j=bc$、$b,c>1$ が奇数なら、$(2^b+1)/3$ が $p$ の $1$ より大きい真の約数になるから、$p>8$ では $j$ は奇素数である。したがって $8p$ の例外素数は、$8$ より大きいFermat素数とWagstaff素数の和集合に一致する。 [Fermat素数](https://oeis.org/A019434) · [Wagstaff素数](https://oeis.org/A000979)

$8<p\le100000$ の全9,588素数を余因子公式で照合した。例外は $11,17,43,257,683,2731,43691,65537$ の8個だった。$p\le500$ の該当する91素数については、二項係数を整数で求め、元の定義の全列の最小値とも照合した。さらに $2\le m\le36$、$m<p\le1000$ の5,633組で余因子公式と桁による判定が一致し、連続する桁が与えた701組の十分条件もすべて成立した。 [再現用コード](verify_large_prime.py)

## $n=9\cdot2^e$ と問題 #406

$e\ge4$ のとき、$2^{e-1}$ の三進表示に数字 $2$ が現れれば $f(9\cdot2^e)=9$、現れなければ $4$ である。原稿の主張をすべての $e$ について形式化した。$9$ を下回れるのは中央の列だけで、その列の二項係数の $2$ 進付値はちょうど $2$ である。残る $3$ の整除性は中央の二項係数に対する桁条件で決まる。例外指数の集合の有限性と、「三進表示に $2$ を含まない $2$ のべきが有限個か」という #406 の有限性命題の同値もLeanで証明した。たとえば $e=9$ では $2^8=(100111)_3$ なので $f(4608)=4$ となる。 [指数族の形式証明](Erdos700/Families.lean) · [問題 #406](https://www.erdosproblems.com/406)

Sayeは指数 $t\le2\cdot3^{45}$ まで、三進表示に $2$ を含まない $2^t$ が $1,4,256$ に限られることを計算で検証した。この結果を移せば $4\le e\le2\cdot3^{45}+1$ の例外は $e=9$ のみである。無限範囲での有限性は引き続き別の問題である。Holdum・Klausen・Rasmussenには、素数進表示と中央二項係数の整除性に関する先行の密度定理がある。 [Saye (2022)](https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.html) · [Holdum・Klausen・Rasmussen (2015)](https://math.colgate.edu/~integers/p43/p43.pdf)

## 問題文と証明の範囲

1978年の原論文で分母に現れるのは最大の素数べき約数（本稿の $Q$）、現在の問題集で分母に現れるのは最大素因数 $P$ である。たとえば $n=12$ では $f(12)=3=12/Q$、$12/P=4$ となる。一般定理は二つの等号集合を、$n$ の素因数分解と有限回の分割で得られる部分和だけで指定する。LeanではFormal Conjecturesが採用する集合の下限による $f$ の定義でも、該当する合成数の集合と明示した解集合が一致する。したがって各合成数について、二項係数を計算せずに判定できる。 [集合等式の形式証明](Erdos700/AnswerSets.lean) · [Erdős–Szekeres原論文 pp. 98–99](https://static.renyi.hu/~p_erdos/1978-46.pdf) · [照合したFormal Conjecturesの版](https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/FormalConjectures/ErdosProblems/700.lean)

#700(b) は $f(n)>\sqrt n$ を満たす合成数の無限性、(c) はすべての合成数にわたる対数上界を問う。本研究の全合成数に対する解集合は (a) のものである。公開討論には、特定の合成数族を桁で調べる先行の観察もある。一般判定および追加結果の文献上の優先性と、(a) の特徴づけとしての外部評価は未確認である。 [問題 #700 の公開討論](https://www.erdosproblems.com/forum/thread/700?order=oldest)
