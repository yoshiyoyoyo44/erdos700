# エルデシュ問題 #700(a)　全合成数の等号判定と指数族

2026年11月18日付の研究ノート、Leanによる形式証明、11月19日の追加結果と検証コードを収録しています。 [元の研究ノート（PDF）](erdos-700-general-criterion.pdf) · [固定余因子の密度と例外の分類](RESEARCH.md)

合成数 $n$ に対して、二項係数と $n$ の最大公約数の最小値を調べます。

$$
f(n)=\min_{2\le k\le\lfloor n/2\rfloor}\gcd\!\left(n,\binom{n}{k}\right).
$$

$P$ を $n$ の最大素因数、$Q$ を $n$ を割る最大の素数べきとします。Erdős–Szekeresの原論文では $f(n)=n/Q$、問題集の #700(a) では $f(n)=n/P$ となる合成数を問います。 [原論文（1978年）](https://static.renyi.hu/~p_erdos/1978-46.pdf) · [Erdős Problems #700](https://www.erdosproblems.com/700)

## 主な結果

- **全合成数の等号判定（定理1）**　素数べきの分割から得られる部分和の共通部分を使い、両方の等号に対する必要十分条件を与えます。
- **固定した素数と余因子（定理2）**　$m\ge 2$ と $m$ を割らない素数 $q$ を固定すると、$1\le e\le E$ で $f(mq^e)<m$ となる指数の個数は、ある $\delta_m>0$ に対して $O_{m,q}(E^{1-\delta_m})$ です。
- **三進表記との関係**　$e\ge 4$ において $f(9\cdot 2^e)=4$ となるのは、$2^{e-1}$ の三進表記に数字 $2$ が現れない場合に限ります。この族における原論文版の例外指数の有限性は、#406と同値です。 [Erdős Problems #406](https://www.erdosproblems.com/406)
- **素数を動かしたときの等号**　任意の整数 $m\ge2$ を固定すると、$p>m$ を満たす素数のうち $f(mp)=m$ となるものの相対密度は $1$ です。$p\le X$ の例外数には $C_m X^{1-\delta_m}$ という上界があり、$\delta_m>0$ です。 [個数の上界](Erdos700/Sparse.lean) · [素数に対する密度](Erdos700/Density.lean)
- **$n=8p$ の完全分類**　素数 $p>8$ について、$p-1$ または $3p-1$ が $2$ のべきなら $f(8p)=4$、それ以外は $f(8p)=8$ です。 [形式証明](Erdos700/EightPrime.lean)
- **全指数で決まる族**　任意の奇素数 $q$ と $e\ge1$ について $f(4q^e)=4$ で、唯一の例外は $f(12)=3$ です。また $f(6\cdot5^e)=6$ はすべての $e\ge1$ で成立します。 [形式証明と有限の判定表](Erdos700/SmallCofactors.lean)

## Leanによる形式証明

定理1を、すべての合成数について原論文版と問題集版を同時に扱う定理 `Erdos700.all_composite_criteria` として証明しています。素数べきの場合には $f(p^a)=p$（$a\ge 2$）となり、問題集版の等号を満たすのは素数の平方に限られます。 [定理1の全文](Erdos700/Classification.lean) · [問題文の定義での解集合](Erdos700/AnswerSets.lean) · [素数べきの場合](Erdos700/PrimePowers.lean)

証明では $p^{j+1}$ 一つを $p^j$ の $p$ 個のコピーに分割する操作を定義し、部分和 $k$ に必要な最小分割回数が $\binom{n}{k}$ の $p$ 進付値と一致することを示します。この結果を、$n$ を割る最大の素数べき $Q$ を初めて超える約数に適用します。 [分割回数と付値](Erdos700/Splits.lean) · [二項係数と最大公約数](Erdos700/Arithmetic.lean) · [共通部分和による等号判定](Erdos700/Criterion.lean)

LeanとMathlibのバージョンは `v4.33.0-rc1` です。Elanを用意し、リポジトリのルートで次のコマンドを実行すると証明を検査できます。

```sh
lake exe cache get
lake build
```

ビルド済みの証明をLeanカーネルで再検査するには、対象のモジュールを指定できます。

```sh
lake env leanchecker Erdos700.AnswerSets
lake env leanchecker Erdos700.ExponentDensity Erdos700.Progressions
```

元のPDFの定理2も形式証明しました。指数の上限を $E$ とすると、例外数は $C_{m,q}E^{1-\delta_m}$ 以下で、同じ $m$ に対するすべての素数 $q\nmid m$ に共通の $\delta_m>0$ が使えます。等号を与える一つの指数から無限等差数列を構成する定理、任意の剰余類にそのような数列が存在する定理、具体例 $f(4\cdot3^{2+16j})=4$ もすべての $j\ge0$ について検証しています。 [候補列の公式](Erdos700/PowerFamilies.lean) · [例外指数の密度](Erdos700/ExponentDensity.lean) · [無限等差数列](Erdos700/Progressions.lean)

$n=9\cdot2^e$ の公式と #406 との同値、$n=8p$ の完全分類、および素数 $p$ を動かす密度定理の証明も収録しています。 [三進表示の証明](Erdos700/Families.lean) · [研究ノートと検証範囲](RESEARCH.md)

## 計算の再現

Python 3.10以降の標準ライブラリで実行できます。 [検証コード](verify_erdos700_general.py)

```sh
python verify_erdos700_general.py
```

$4\le n\le 5000$ の合成数4,330個について、判定結果を定義からの直接計算と照合します。等号が成立するのは原論文版で2,811個、問題集版で2,578個です。$n\le 144$ では、分割から直接求めた部分和の集合を桁ごとの計算とも比較します。

追加の計算は次のコマンドで再現できます。$n=8p$ の分類を $p\le100000$ の該当素数9,588個で照合し、そのうち $p\le500$ の91個では元の定義のすべての列も直接調べます。余因子 $4,6$ の新しい指数族についても19,840件を照合し、うち130件で全列の最小値を直接計算します。 [追加の検証コード](verify_large_prime.py)

```sh
python -B verify_large_prime.py
```

一般判定が対象とするのは #700(a) の二つの等号集合です。研究ノートの学術的な新規性と外部査読は未確認です。照合した公開記録では (a) を未解決として扱っています。 [問題集での掲載状況](https://www.erdosproblems.com/history/700) · [公開されているLeanの問題文](https://github.com/google-deepmind/formal-conjectures/blob/2c24ebe7eb2a79b47f9ffcab618cd611c2bc1ea6/FormalConjectures/ErdosProblems/700.lean)
