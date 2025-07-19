# Batch 3

## AIME

### `AIME_bBeautiful`

Let $b\ge 2$ be an integer.
Call a positive integer $n$ $b$-eautiful if it has exactly two digits
when expressed in base $b$ and these two digits sum to $\sqrt n$.
For example, $81$ is $13$-eautiful because $81 = 63_{13}$ and $6 + 3 = \sqrt{81}$.
Find the least integer $b \ge 2$ for which there are more than ten $b$-eautiful integers.

<https://artofproblemsolving.com/wiki/index.php/2024_AIME_II_Problems/Problem_14>

[`Numina/AIME_bBeautiful.lean`](Numina/AIME_bBeautiful.lean)

```lean
theorem number_theory_93241 :
    IsLeast {b | 2 ≤ b ∧
      {n | (Nat.digits b n).length = 2 ∧ (Nat.digits b n).sum = sqrt n}.encard > 10} 211 := by
```

### `AIME_67739`

Let $S$ be the number of ordered pairs of integers $(a,b)$ with $1 \leq a \leq 100$ and
$b \geq 0$ such that the polynomial $x^2 + a x + b$ can be factored into the product of two
(not necessarily distinct) linear factors with integer coefficients.
Find the remainder when $S$ is divided by $1000$.

<https://artofproblemsolving.com/wiki/index.php/2018_AIME_I_Problems/Problem_1>

[`Numina/AIME_67739.lean`](Numina/AIME_67739.lean)

```lean
theorem algebra_67739 : Set.ncard {(a, b) : ℤ × ℤ | a ∈ Finset.Icc 1 100 ∧ 0 ≤ b ∧
    ∃ u v : ℤ, X ^ 2 + C a * X + C b = (X + C u) * (X + C v)} % 1000 = 600 := by
```

### `AIME_96952`

Let $z_1 = 18 + 83i$, $z_2 = 18 + 39i$ and $z_3 = 78 + 99i$, where $i = \sqrt{-1}$.
Let $z$ be the unique complex number with the properties that
$\frac{z_3 - z_1}{z_2 - z_1} \frac{z - z_2}{z - z_3}$ is a real number and
the imaginary part of $z$ is the greatest possible. Find the real part of $z$.

<https://artofproblemsolving.com/wiki/index.php/2017_AIME_I_Problems/Problem_10>

[`Numina/AIME_96952.lean`](Numina/AIME_96952.lean)

```lean
theorem algebra_96952 {z₁ z₂ z₃ : ℂ}
    (hz₁ : z₁ = 18 + 83 * I) (hz₂ : z₂ = 18 + 39 * I) (hz₃ : z₃ = 78 + 99 * I) :
    ∃ z, ((z₃ - z₁) / (z₂ - z₁) * ((z - z₂) / (z - z₃))).im = 0 ∧
      z.re = 56 ∧
      ∀ x, ((z₃ - z₁) / (z₂ - z₁) * ((x - z₂) / (x - z₃))).im = 0 → z.im ≥ x.im := by
```

### `AIME_30933`

Let S be the set of all perfect squares whose rightmost three digits in base 10 are 256.
Let T be the set of all numbers of the form $\frac{x - 256}{1000}$, where $x$ is in S.
In other words, T is the set of numbers that result when the last three digits
of each number in S are truncated.
Find the remainder when the tenth smallest element of T is divided by 1000.

<https://artofproblemsolving.com/wiki/index.php/2012_AIME_I_Problems/Problem_10>

[`Numina/AIME_30933.lean`](Numina/AIME_30933.lean)

```lean
theorem number_theory_30933 (s t : Set ℕ)
    (hs : s = {m : ℕ | m % 1000 = 256 ∧ ∃ k, m = k ^ 2})
    (ht : t = {n : ℕ | ∃ m ∈ s, n = m / 1000}) :
    Nat.nth (· ∈ t) 9 % 1000 = 170 := by
```

### `AIME_96580`

Let $P$ be the product of the roots of $z^6 + z^4 + z^3 + z^2 + 1 = 0$
that have a positive imaginary part, and suppose that $P = r (\cos(θ∘) + i \sin(θ∘))$,
where $0 < r$ and $0 ≤ θ < 360$. Find $θ$.

<https://artofproblemsolving.com/wiki/index.php/1996_AIME_Problems/Problem_11>

[`Numina/AIME_96580.lean`](Numina/AIME_96580.lean)

```lean
theorem algebra_96580 :
    ∃ (h : Set.Finite {z : ℂ | z ^ 6 + z ^ 4 + z ^ 3 + z ^ 2 + 1 = 0 ∧ 0 < z.im}),
      toIcoMod Real.two_pi_pos 0 (∏ z in h.toFinset, z).arg = 2 * π * (276 / 360) := by
```

### `AIME_97905`

Given that

$$
\begin{eqnarray*}
&(1)& x\text{ and }y\text{ are both integers between 100 and 999, inclusive;} \\
&(2)& y\text{ is the number formed by reversing the digits of }x\text{; and} \\
&(3)& z=|x-y|.
\end{eqnarray*}
$$

How many distinct values of z are possible?

<https://artofproblemsolving.com/wiki/index.php/2002_AIME_II_Problems/Problem_1>

[`Numina/AIME_97905.lean`](Numina/AIME_97905.lean)

```lean
theorem number_theory_97905 :
    Set.ncard {z : ℤ | ∃ x y : ℕ, x ∈ Set.Ico 100 1000 ∧ y ∈ Set.Ico 100 1000 ∧
      z = |(x - y : ℤ)| ∧ Nat.digits 10 y = (Nat.digits 10 x).reverse} = 9 := by
```

### `AIME_97639`

Find the sum of all positive integers $b < 1000$ such that the base-$b$ integer $36_b$
is a perfect square and the base-$b$ integer $27_b$ is a perfect cube.

[`Numina/AIME_97639.lean`](Numina/AIME_97639.lean)

```lean
theorem number_theory_97639 :
    ∑ᶠ b ∈ {b : ℕ | 0 < b ∧ b < 1000 ∧ (∃ k, Nat.digits b (k ^ 2) = [6, 3]) ∧
      ∃ m, Nat.digits b (m ^ 3) = [7, 2]}, b = 371 := by
```

### `AIME_97068`

A rational number written in base eight is $ab.cd$, where all digits are nonzero.
The same number in base twelve is $bb.ba$.
Find the base-ten number $abc$. 

[`Numina/AIME_97068.lean`](Numina/AIME_97068.lean)

```lean
theorem number_theory_97068 {a b c d : ℕ}
    (ha0 : a ≠ 0) (hb0 : b ≠ 0) (hc0 : c ≠ 0) (hd0 : d ≠ 0)
    (ha_lt : a < 8) (hb_lt : b < 8) (hc_lt : c < 8) (hd_lt : d < 8)
    (h : (a * 8 + b + c / 8 + d / 8^2 : ℝ) = b * 12 + b + b / 12 + a / 12^2) :
    a * 100 + b * 10 + c = 321 := by
```

### `AIME_93450`

The formula for converting Fahrenheit temperature F to the corresponding
Celsius temperature C is C = 5 / 9 * (F - 32).
An integer Fahrenheit temperature is converted to Celsius, rounded to the nearest integer,
converted back to Fahrenheit, and again rounded to the nearest integer.
For how many integer Fahrenheit temperatures between 32 and 1000 inclusive does
the original temperature equal the final temperature?

[`Numina/AIME_93450.lean`](Numina/AIME_93450.lean)

```lean
theorem algebra_93450 {toC toF : ℝ → ℝ} (h_toC : ∀ x, toC x = 5 / 9 * (x - 32))
    (h_toF : ∀ x, toF x = 9 / 5 * x + 32) :
    {x : ℤ | 32 ≤ x ∧ x ≤ 1000 ∧ round (toF (round (toC x))) = x}.ncard = 539 := by
```

### `AIME_98439`

Alpha and Beta both took part in a two-day problem-solving competition.
At the end of the second day, each had attempted questions worth a total of 500 points.
Alpha scored 160 points out of 300 points attempted on the first day,
and scored 140 points out of 200 points attempted on the second day.
Beta who did not attempt 300 points on the first day,
had a positive integer score on each of the two days,
and Beta's daily success rate (points scored divided by points attempted)
on each day was less than Alpha's on that day.
Alpha's two-day success ratio was 300/500 = 3/5.
The largest possible two-day success ratio that Beta could achieve is m / n, where
m and n are relatively prime positive integers. What is m + n?

[`Numina/AIME_98439.lean`](Numina/AIME_98439.lean)

```lean
theorem algebra_98439 :
    IsGreatest ((fun (a, b, _) ↦ a + b) '' {(a, b, q) : ℕ × ℕ × ℕ |
      a ∈ Set.Ioc 0 q ∧ b ∈ Set.Ioc 0 (500 - q) ∧
      (a / q : ℝ) < 160 / 300 ∧ (b / (500 - q) : ℝ) < 140 / 200}) 349 ∧
    Nat.Coprime 349 500 ∧ 349 + 500 = 849 := by
```


## AMC

### `AMC_94957`

For real numbers $x$, let

$$ P(x) = 1 + \cos(x) + i \sin(x) - \cos(2 x) - i \ sin(2 x) + \cos(3 x) + i \sin(3 x) $$

where $i = \sqrt{-1}$. For how many values of $x$ with $0 \leq x < 2 \pi$ does $P(x) = 0$?
(A) 0, (B) 1, (C) 2, (D) 3, (E) 4

<https://artofproblemsolving.com/wiki/index.php/2021_Fall_AMC_12B_Problems/Problem_21>

[`Numina/AMC_94957.lean`](Numina/AMC_94957.lean)

```lean
theorem algebra_94957 {p : ℝ → ℂ}
    (hp : ∀ x, p x = 1 + cos x + I * sin x - cos (2 * x) - I * sin (2 * x) +
      cos (3 * x) + I * sin (3 * x)) :
    {x | 0 ≤ x ∧ x < 2 * π ∧ p x = 0}.encard = 0 := by
```

### `AMC_94998`

For $n$ a positive integer, let $R(n)$ be the sum of the remainders when $n$ is divided by
$2$, $3$, $4$, $5$, $6$, $7$, $8$, $9$, and $10$.
For example, $R(15) = 1 + 0 + 3 + 0 + 3 + 1 + 7 + 6 + 5 = 26$.
How many two-digit positive integers $n$ satisfy $R(n) = R(n+1)$?
(A) 0, (B) 1, (C) 2, (D) 3, (E) 4

[`Numina/AMC_94998.lean`](Numina/AMC_94998.lean)

```lean
theorem number_theory_94998 (r : ℕ → ℕ) (hr : ∀ n, r n = ∑ k in .Icc 2 10, n % k) :
    Finset.card {n ∈ .Ico 10 100 | r n = r (n + 1)} = 2 := by
```

### `AMC_97963`

Let A be the set of positive integers that have no prime factors other than 2, 3, or 5.
The infinite sum
1/1 + 1/2 + 1/3 + 1/4 + 1/5 + 1/6 + 1/8 + 1/9 + 1/10 + 1/12 + 1/15 + 1/16 + 1/18 + 1/20 + ⋯
of the reciprocals of the elements of A can be expressed as m / n,
where m and n are relatively prime positive integers. What is m + n?
(A) 16
(B) 17
(C) 19
(D) 23
(E) 36

<https://artofproblemsolving.com/wiki/index.php/2018_AMC_12A_Problems/Problem_19>

[`Numina/AMC_97963.lean`](Numina/AMC_97963.lean)

```lean
theorem number_theory_97963 : ∃ m n : ℕ,
    ∑' k : Nat.factoredNumbers {2, 3, 5}, (k : ℝ)⁻¹ = m / n ∧
    Nat.Coprime m n ∧ m + n = 19 := by
```

### `AMC_93855`

How many positive integers n satisfy $(n + 1000) / 70 = \lfloor \sqrt{n} \rfloor$?
(Recall that $\lfloor x \rfloor$ is the greatest integer not exceeding $x$.)
(A) 2
(B) 4
(C) 6
(D) 30
(E) 32

<https://artofproblemsolving.com/wiki/index.php/2020_AMC_12B_Problems/Problem_21>

[`Numina/AMC_93855.lean`](Numina/AMC_93855.lean)

```lean
theorem number_theory_93855 :
    Set.ncard {n : ℕ | 0 < n ∧ (n + 1000 : ℝ) / 70 = ⌊√n⌋₊} = 6 := by
```

### `AMC_94341`

A geometric sequence $(a_n)$ has $a_1 = \sin(x)$, $a_2 = \cos(x)$, $a_3 = \tan(x)$ for some
real number $x$. For what value of $n$ does $a_n = 1 + \cos(x)$?
(A) 4
(B) 5
(C) 6
(D) 7
(E) 8

[`Numina/AMC_94341.lean`](Numina/AMC_94341.lean)

```lean
theorem algebra_94341 {x : ℝ} (a : ℕ → ℝ) {r : ℝ} (ha : ∀ n, a n = a 0 * r ^ n)
    (ha0 : a 0 = sin x) (ha1 : a 1 = cos x) (ha2 : a 2 = tan x)
    (h_cos : cos x ≠ 0) :
    a 7 = 1 + cos x := by
```

### `AMC_95577`

How many complex numbers satisfy the equation $z^5 = z'$
where $z'$ is the conjugate of the complex number $z$?
(A) 2
(B) 3
(C) 5
(D) 6
(E) 7

[`Numina/AMC_95577.lean`](Numina/AMC_95577.lean)

```lean
theorem algebra_95577 : {z : ℂ | z ^ 5 = starRingEnd ℂ z}.ncard = 7 := by
```

### `AMC_95209`

Consider sequences of positive real numbers of the form x, 2000, y, … in which
every term after the first is 1 less than the product of its two immediate neighbors.
For how many different values of x does the term 2001 appear somewhere in the sequence?
(A) 1
(B) 2
(C) 3
(D) 4
(E) more than 4

[`Numina/AMC_95209.lean`](Numina/AMC_95209.lean)

```lean
theorem algebra_95209 (a : ℝ → ℕ → ℝ) (h_pos : ∀ x n, 0 < a x n)
    (ha0 : ∀ x, a x 0 = x) (ha1 : ∀ x, a x 1 = 2000)
    (ha : ∀ x n, a x (n + 1) = a x n * a x (n + 2) - 1) :
    ∃ s : Finset ℝ, {x > 0 | 2001 ∈ Set.range (a x)} = s ∧ s.card = 4 := by
```

### `AMC_95071`

The parabola with equation $p(x) = a x^2 + b x + c$ and vertex $(h, k)$
is reflected about the line $y = k$.
This results in the parabola with equation $q(x) = d x^2 + e x + f$.
Which of the following equals $a + b + c + d + e + f$?
(A) $2 b$
(B) $2 c$
(C) $2 a + 2 b$
(D) $2 h$
(E) $2 k$

[`Numina/AMC_95071.lean`](Numina/AMC_95071.lean)

```lean
theorem algebra_95071 {a b c d e f k : ℝ} {p q : ℝ → ℝ}
    (hp : ∀ x, p x = a * x ^ 2 + b * x + c) (hq : ∀ x, q x = d * x ^ 2 + e * x + f)
    (hpq : ∀ x, q x - k = -(p x - k)) :
    a + b + c + d + e + f = 2 * k := by
```

### `AMC_94615`

Let $f(x) = a x^2 + b x + c$ where $a, b, c$ are integers.
Suppose that $f(1) = 0$, $50 < f(7) < 60$, $70 < f(8) < 80$,
and $5000 k < f(100) < 5000 (k + 1)$ for some integer $k$.
What is $k$?
(A) 1
(B) 2
(C) 3
(D) 4
(E) 5

[`Numina/AMC_94615.lean`](Numina/AMC_94615.lean)

```lean
theorem algebra_94615 (a b c : ℤ) (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h1 : f 1 = 0) (h2 : f 7 ∈ Set.Ioo 50 60) (h3 : f 8 ∈ Set.Ioo 70 80)
    {k : ℤ} (h4 : f 100 ∈ Set.Ioo (5000 * k) (5000 * (k + 1))) :
    k = 3 := by
```

### `AMC_93411`

Mrs. Walter gave an exam in a mathematics class of five students.
She entered the scores in random order into a spreadsheet,
which recalculated the class average after each score was entered.
Mrs. Walter noticed that after each score was entered, the average was always an integer.
The scores (listed in ascending order) were 71, 76, 80, 82, and 91.
What was the last score Mrs. Walters entered?
(A) 71
(B) 76
(C) 80
(D) 82
(E) 91

[`Numina/AMC_93411.lean`](Numina/AMC_93411.lean)

```lean
theorem number_theory_93411 (a b c d e : ℕ) (h : [a, b, c, d, e] ~ [71, 76, 80, 82, 91])
    (h2 : 2 ∣ d + e) (h3 : 3 ∣ c + d + e) (h4 : 4 ∣ b + c + d + e) : a = 80 := by
```

### `AMC_65302`

Cities A and B are 45 miles apart.
Alicia lives in A and Beth lives in B.
Alicia bikes towards B at 18 miles per hour.
Leaving at the same time, Beth bikes toward A at 12 miles per hour.
How many miles from City A will they be when they meet?
(A) 20
(B) 24
(C) 25
(D) 26
(E) 27

[`Numina/AMC_65302.lean`](Numina/AMC_65302.lean)

```lean
theorem algebra_65302 {d v1 v2 : ℝ} (hd : d = 45) (hv1 : v1 = 18) (hv2 : v2 = 12) {x t : ℝ}
    (h1 : x = v1 * t) (h2 : x = d - v2 * t) : x = 27 := by
```


## Other

### `problem_295444`

Positive real numbers $a$, $b$, $c$ satisfy $a^3 + b^3 = c^3$.
Prove: $a^2 + b^2 - c^2 > 6 (c - a) (c - b)$.

[`Numina/problem_295444.lean`](Numina/problem_295444.lean)

```lean
theorem inequalities_295444 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 = c ^ 3) :
    a ^ 2 + b ^ 2 - c ^ 2 > 6 * (c - a) * (c - b) := by
```

### `problem_198296`

The reduced quadratic trinomial $f(x)$ has two distinct roots.
Can it happen that the equation $f(f(x)) = 0$ has three distinct roots,
and the equation $f(f(f(x))) = 0$ has seven distinct roots?

[`Numina/problem_198296.lean`](Numina/problem_198296.lean)

```lean
theorem algebra_198296 {f : ℝ → ℝ} (hf : ∃ b c, f = fun x ↦ x ^ 2 + b * x + c)
    (h1_card : {x | f x = 0}.encard = 2) :
    ¬({x | f (f x) = 0}.encard = 3 ∧ {x | f (f (f x)) = 0}.encard = 7) := by
```

### `problem_159432`

Given $x, y, z > 0$, and $x + y + z = 1$.
Prove $(1/x^2 + x) (1/y^2 + y) * (1/z^2 + z) ≥ (28/3)^3$.

[`Numina/problem_159432.lean`](Numina/problem_159432.lean)

```lean
theorem inequalities_159432 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hsum : x + y + z = 1) :
    ((1 / x ^ 2 + x) * (1 / y ^ 2 + y) * (1 / z ^ 2 + z)) ≥ (28 / 3) ^ 3 := by
```

### `problem_209992`

Prove that there are infinitely many natural numbers that cannot be represented
as the sum of the square of an integer and a prime number.

[`Numina/problem_209992.lean`](Numina/problem_209992.lean)

```lean
theorem number_theory_209992 :
    ∀ a : ℕ, ∃ x > a, ¬∃ n p : ℕ, p.Prime ∧ x = n ^ 2 + p := by
```

### `problem_180196`

Show $\frac{1}{2} + \log_{9} x - \log_{3}(5 x) > \log_{\frac{1}{3}}(x+3)$.

[`Numina/problem_180196.lean`](Numina/problem_180196.lean)

```lean
theorem algebra_180196 {x : ℝ} (hx : 0 < x) :
    1/2 + logb 9 x - logb 3 (5 * x) > logb (1/3) (x + 3) := by
```

### `problem_200534`

Prove: For any real numbers $a_{1}, a_{2}, \cdots, a_{1987}$ and any positive numbers
$b_{1}, b_{2}, \cdots, b_{1987}$, we have

$$
\frac{\left(a_{1}+a_{2}+\cdots+a_{1987}\right)^{2}}{b_{1}+b_{2}+\cdots+b_{1987}} \leqslant
  \frac{a_{1}^{2}}{b_{1}}+\frac{a_{2}^{2}}{b_{2}}+\cdots+\frac{a_{1987}^{2}}{b_{1987}} .
$$

[`Numina/problem_200534.lean`](Numina/problem_200534.lean)

```lean
theorem inequalities_200534 (a b : Fin 1987 → ℝ) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, a i ^ 2 / b i := by
```

### `problem_138682`

For any integers $x$ and $y$, the algebraic expression
$x^5 + 3 x^4 y - 5 x^3 y^2 - 15 x^2 y^3 + 4 x y^4 + 12 y^5$ cannot equal 33.

[`Numina/problem_138682.lean`](Numina/problem_138682.lean)

```lean
theorem algebra_138682 : ∀ x y : ℤ,
    x^5 + 3 * x^4 * y - 5 * x^3 * y^2 - 15 * x^2 * y^3 + 4 * x * y^4 + 12 * y^5 ≠ 33 := by
```

### `problem_def`

Given $f(x) = \cos (2 x) + p |\cos (x)| + p, x \in \mathbb{R}$.
Let the maximum value of $f(x)$ be $h(p)$, then the expression for $h(p)$ is

$$
h(p) = \begin{cases}
  p - 1, & p < -2 \\
  2 p + 1, & p \ge 2.
\end{cases}
$$

[`Numina/problem_def.lean`](Numina/problem_def.lean)

```lean
theorem algebra_114412 {f : ℝ → ℝ → ℝ} (hf : ∀ p x, f p x = cos (2 * x) + p * |cos x| + p)
    (g : ℝ → ℝ) (hg : ∀ p, g p = ⨆ x, f p x) :
    ∀ p, g p = if p < -2 then p - 1 else 2 * p + 1 := by
```

