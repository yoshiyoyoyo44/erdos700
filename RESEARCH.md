# #700(a) の追加結果　固定余因子の密度と等号を満たす指数

2026年11月19日。ここで $f(n)$ は $2\le k\le\lfloor n/2\rfloor$ における $\gcd(n,\binom nk)$ の最小値である。本稿は11月18日付の原稿の定理1を出発点とする。主な追加結果は、固定した任意の余因子に対する素数の密度、余因子 $8$ における例外素数の分類、および余因子 $4,6$ の二つの族における全指数の分類である。 [元の研究ノート](erdos-700-general-criterion.pdf)

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

## 素数を固定して指数を動かす場合（原稿の定理2）

**定理.** $m\ge2$ ごとに一つの $\delta_m>0$ が存在する。任意の素数 $q\nmid m$ に対し定数 $C_{m,q}>0$ を取ることができ、すべての整数 $E\ge1$ で

$$
\#\{1\le e\le E:f(mq^e)<m\}\le C_{m,q} E^{1-\delta_m}
$$

が成り立つ。$f(mq^e)=m$ となる指数の割合が $1$ に収束することもLeanで証明した。$e$ が十分大きければ $q^e$ は $mq^e$ を割る最大の素数べきなので、これは原論文版の等号の分布を与える。 [定理2と密度の形式証明](Erdos700/ExponentDensity.lean)

**候補の縮約.** $h=\min(e,\lfloor\log_q(m-1)\rfloor)$、$z=q^{e-h}$、$A=mq^h$ とおく。値 $m$ は列 $k=q^e$ で達成される。$m$ を下回る候補は $k=tz$、$1\le t\le\lfloor A/2\rfloor$ に限られ、$A\le m(m-1)$。この列における最大公約数は次のとおりである。

$$
q^{\min(e,v_q(\binom At))}
\prod_{\ell^a\parallel m}\ell^{\min(a,v_\ell(\binom{Az}{tz}))}.
$$

積は $m$ の各素因数にわたる。$q$ 進の繰り上がり回数は $q$ のべきを掛けても変わらないため、$q$ の指数は小さい行 $A$ で計算できる。 [候補列の上限と各列の正確な値](Erdos700/PowerFamilies.lean)

**指数の数え上げ.** 十分大きい $e$ では $h=\lfloor\log_q(m-1)\rfloor$ が一定となる。$Y=m(m-1)$ とおき、$B_\ell=\ell^{\lceil\log_\ell Y\rceil+v_\ell(m)-1}$ とする。$\ell\mid m$ に対しては $v_\ell(Y)=v_\ell(m)$ である。$q^{e-h}$ の $B_\ell$ 進表示に最大の数字が現れれば、前節と同じ繰り上がりが全候補を同時に扱う。一方、$q^u\equiv q^v\bmod\ell^R$ から $u\equiv v\bmod\ell^{\max(R-c,0)}$ を導ける。ここで $c$ は $q,\ell$ のみで決まる。奇素数では $q^{\ell-1}$ に付値の持ち上げ公式を適用し、$\ell=2$ では指数差を二倍して偶数指数の公式を使う。 [法が素数べきのときの周期](Erdos700/PowerPeriods.lean)

$r=1+\lfloor\log_{B_\ell} E\rfloor$、$B_\ell^r=\ell^R$ とおく。$s=e-h\le E$ は、$q^s$ の法 $\ell^R$ での剰余と $\lfloor s/\ell^{\max(R-c,0)}\rfloor$ の組で一意に定まる。最大の数字を欠くとき、前者は高々 $(B_\ell-1)^r$ 通り、後者は高々 $\ell^c$ 通りである。短い初期区間を加え、各 $\ell\mid m$ の上界を足すと定理2を得る。$B_\ell$ は $q$ に依存しないので、$\delta_m$ をすべての $q$ に共通に取れる。 [有限個数の上界](Erdos700/ExponentDensity.lean)

**等差数列.** $e_0\ge\max(1,\lfloor\log_q(m-1)\rfloor)$ かつ $f(mq^{e_0})=m$ とする。各 $\ell\mid m$ に対して $R_\ell=1+\lfloor\log_\ell(mq^{e_0})\rfloor$ とおく。$\ell^{R_\ell}$ を法とする $q$ の乗法位数の最小公倍数を $T$ とすれば、$j\ge0$ の全範囲で $f(mq^{e_0+jT})=m$ となる。初項で起きた繰り上がりが同じ位置で保存され、各候補列の新しい最大公約数が元の値の倍数になることを形式証明した。任意の法 $D\ge1$ と剰余類を指定し、初項に任意の下限を課しても、その類の中に全項で等号となる無限等差数列を取れる。たとえば $m=4,q=3,e_0=2$ では $f(4\cdot3^{2+16j})=4$ がすべての $j\ge0$ で成り立つ。 [公差の構成と任意の剰余類における存在証明](Erdos700/Progressions.lean)

## 余因子 $4$ と $6$ の全指数での値

**定理.** 任意の奇素数 $q$ と整数 $e\ge1$ に対して $f(4q^e)=4$ が成り立つ。ただ一つの例外は $q=3,e=1$ で、$f(12)=3$ である。また、すべての $e\ge1$ で $f(6\cdot5^e)=6$ となる。原稿で例示した $4\cdot3^{2+16j}$ と、添付コードで公差を求めた $6\cdot5^{1+216j}$ について、これで各等差数列の外の指数も判定できる。 [形式証明](Erdos700/SmallCofactors.lean)

$h\le e$ と $a\le e$ を固定し、$A=mq^h$、$z=q^{e-h}$ とおく。$q^{h+1}\ge m$ のとき、最大公約数 $g<m$ を与える列は $k=tz$ に限られる。$Az\mid tz\,g$ から $A\mid tg$ が従い、候補列の公式から

$$
\min(a,v_q(g))=\min\!\left(a,v_q\!\binom At\right)
$$

も必要である。$1\le t\le\lfloor A/2\rfloor$、$1\le g<m$ の範囲に両方を満たす組がなければ、同じ $h,a$ を使えるすべての指数で等号が確定する。 [有限の表から無限族への証明](Erdos700/SmallCofactors.lean)

| 行 $A$ と基数 $q$ | $A\mid tg$ を満たす組 $(t,g)$ | 各組に対応する $v_q(\binom At)$ |
|---|---|---|
| $12,\ q=3$ | $(6,2),(4,3)$ | $1,2$ |
| $30,\ q=5$ | $(15,2),(10,3),(15,4),(6,5),(12,5)$ | $1,1,1,2,2$ |

いずれも $h=1,a=2$ で全候補が消えるため、$e\ge2$ が一度に決まる。残る $e=1$ では $f(12)=3$、$f(30)=6$ を直接求める。$m=4,\ q\ge5$ の場合には $h=0$ と取れ、$x=q^e$ とおくと候補は $k=x$ と $k=2x$ だけになる。前者の最大公約数は $4$、後者では $v_2(\binom{4x}{2x})$ が $x$ の二進桁和に等しい。奇数 $x>1$ の二進桁和は少なくとも $2$ なので、後者も $4$ を下回れない。 [二進桁和を使う証明](Erdos700/SmallCofactors.lean) · [計算による照合](verify_large_prime.py)

## $n=9\cdot2^e$ と問題 #406

$e\ge4$ のとき、$2^{e-1}$ の三進表示に数字 $2$ が現れれば $f(9\cdot2^e)=9$、現れなければ $4$ である。原稿の主張をすべての $e$ について形式化した。$9$ を下回れるのは中央の列だけで、その列の二項係数の $2$ 進付値はちょうど $2$ である。残る $3$ の整除性は中央の二項係数に対する桁条件で決まる。例外指数の集合の有限性と、「三進表示に $2$ を含まない $2$ のべきが有限個か」という #406 の有限性命題の同値もLeanで証明した。たとえば $e=9$ では $2^8=(100111)_3$ なので $f(4608)=4$ となる。 [指数族の形式証明](Erdos700/Families.lean) · [問題 #406](https://www.erdosproblems.com/406)

Sayeは指数 $t\le2\cdot3^{45}$ まで、三進表示に $2$ を含まない $2^t$ が $1,4,256$ に限られることを計算で検証した。この結果を移せば $4\le e\le2\cdot3^{45}+1$ の例外は $e=9$ のみである。無限範囲での有限性は引き続き別の問題である。Holdum・Klausen・Rasmussenには、素数進表示と中央二項係数の整除性に関する先行の密度定理がある。 [Saye (2022)](https://cs.uwaterloo.ca/journals/JIS/VOL25/Saye/saye3.html) · [Holdum・Klausen・Rasmussen (2015)](https://math.colgate.edu/~integers/p43/p43.pdf)

## 問題文と証明の範囲

1978年の原論文で分母に現れるのは最大の素数べき約数（本稿の $Q$）、現在の問題集で分母に現れるのは最大素因数 $P$ である。たとえば $n=12$ では $f(12)=3=12/Q$、$12/P=4$ となる。一般定理は二つの等号集合を、$n$ の素因数分解と有限回の分割で得られる部分和だけで指定する。LeanではFormal Conjecturesが採用する集合の下限による $f$ の定義でも、該当する合成数の集合と明示した解集合が一致する。したがって各合成数について、二項係数を計算せずに判定できる。 [集合等式の形式証明](Erdos700/AnswerSets.lean) · [Erdős–Szekeres原論文 pp. 98–99](https://static.renyi.hu/~p_erdos/1978-46.pdf) · [照合したFormal Conjecturesの版](https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/FormalConjectures/ErdosProblems/700.lean)

#700(b) は $f(n)>\sqrt n$ を満たす合成数の無限性、(c) はすべての合成数にわたる対数上界を問う。本研究の全合成数に対する解集合は (a) のものである。公開討論には、特定の合成数族を桁で調べる先行の観察もある。一般判定および追加結果の文献上の優先性と、(a) の特徴づけとしての外部評価は未確認である。 [問題 #700 の公開討論](https://www.erdosproblems.com/forum/thread/700?order=oldest)
