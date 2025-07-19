# Batch 3

## AIME

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

