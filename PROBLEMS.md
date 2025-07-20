# IMO

### `IMO_23856`

Let $f : [0, 1] \rightarrow \mathbb{R}$ be continuous and satisfy:

$$
\begin{aligned}
b f(2 x) & = f(x), & & 0 \leq x \leq 1 / 2 \\
f(x) & = b + (1-b) f(2 x - 1), & & 1 / 2 \leq x \leq 1
\end{aligned}
$$

where $b=\frac{1+c}{2+c}, c>0$.
Show that $0 < f(x) - x < c$ for every $x, 0 < x < 1$.

[`Numina/IMO_23856.lean`](Numina/IMO_23856.lean)

```lean
theorem algebra_23856 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc 0 1))
    {b c : ℝ} (hb : b = (1 + c) / (2 + c)) (hc : 0 < c)
    (hf₁ : ∀ x ∈ Set.Icc 0 (1 / 2), b * f (2 * x) = f x)
    (hf₂ : ∀ x ∈ Set.Icc (1 / 2) 1, f x = b + (1 - b) * f (2 * x - 1)) :
    ∀ x ∈ Set.Ioo 0 1, f x - x ∈ Set.Ioo 0 c := by
```

### `IMO_25148`

Each positive integer $a$ undergoes the following procedure in order to obtain
the number $d = d(a)$:
1. move the last digit of $a$ to the first position to obtain the number $b$;
2. square $b$ to obtain the number $c$;
3. move the first digit of $c$ to the end to obtain the number $d$.
(All the numbers in the problem are considered to be represented in base 10.)
For example, for $a=2003$, we have $b=3200, c=10240000$, and $d = 02400001 = 2400001 = d(2003)$.
Find all numbers $a$ for which $d(a) = a^{2}$.

[`Numina/IMO_25148.lean`](Numina/IMO_25148.lean)

```lean
def d (a : ℕ) : ℕ :=
  ofDigits 10 <| rotateRight <| digits 10 <|
  (ofDigits 10 <| rotate (n := 1) <| digits 10 a) ^ 2

theorem number_theory_25148 {a : ℕ} (ha : a ≠ 0) :
    d a = a ^ 2 ↔ a ∈ {1, 2, 3} ∪ Set.range (fun n ↦ ofDigits 10 (1 :: replicate (n + 1) 2)) := by
```

### `IMO_23602`

Evaluate $S = \sum_{k=1}^{n} k (k+1) \cdots (k+p)$, where $n$ and $p$ are positive integers.

[`Numina/IMO_23602.lean`](Numina/IMO_23602.lean)

```lean
theorem algebra_23602 {n p : ℕ} :
    ∑ k ∈ Icc 1 n, ∏ i ∈ range (p + 1), (k + i) =
    (∏ i ∈ range (p + 2), (n + i)) / (p + 2) := by
```


# Batch 6

### `problem_221351`

Given a natural number $x = 9^{n} - 1$, where $n$ is a natural number. It is known that
$x$ has exactly three distinct prime divisors, one of which is 13. Find $x$.

[`Numina/problem_221351.lean`](Numina/problem_221351.lean)

```lean
theorem number_theory_221351 (x : ℕ) (n : ℕ) (hx : x = 9 ^ n - 1)
    (h_card : x.primeFactors.card = 3) (h13 : 13 ∣ x) :
    x = 728 := by
```

### `problem_247029`

If $n$ is a natural number greater than 1, such that

$$
\left[\frac{n}{1}\right] + \left[\frac{n}{2}\right] + \ldots + \left[\frac{n}{n}\right] =
2 + \left[\frac{n-1}{1}\right] + \left[\frac{n-1}{2}\right] + \ldots + \left[\frac{n-1}{n-1}\right]
$$

then $n$ is a prime number. Prove it!

[`Numina/problem_247029.lean`](Numina/problem_247029.lean)

```lean
theorem number_theory_247029 (n : ℕ) :
    ∑ k ∈ Icc 1 n, n / k = 2 + ∑ k ∈ Icc 1 (n - 1), (n - 1) / k → n.Prime := by
```

### `problem_152180`

Simplify:

$$ C_{n}^{0} \sin (\alpha) - C_{n}^{1} \sin (\alpha + \theta) + \cdots +
  (-1)^{n} C_{n}^{n} \sin (\alpha+n \theta) $$

[`Numina/problem_152180.lean`](Numina/problem_152180.lean)

```lean
theorem algebra_152180 {n : ℕ} (α θ : ℝ) :
    ∑ k ∈ range (n + 1), (-1) ^ k * n.choose k * Real.sin (α + k * θ) =
    2 ^ n * Real.sin (θ / 2) ^ n * Real.sin (α + n * (θ - π) / 2 ) := by
```

### `problem_122932`

How many integers $m$ satisfy both the following properties:

(i) $1 \leq m \leq 5000$;

(ii) $[\sqrt{m}]=[\sqrt{m+125}]$ ?

(Here $[x]$ denotes the largest integer not exceeding $x$, for any real number $x$.)

[`Numina/problem_122932.lean`](Numina/problem_122932.lean)

```lean
theorem number_theory_122932 :
    {m : ℕ | m ∈ Set.Icc 1 5000 ∧ ⌊√m⌋₊ = ⌊√(m + 125)⌋₊}.ncard = 72 := by
```

### `problem_234330`

Let $\frac{r}{u}$ and $\frac{s}{v}$ be fractions with positive denominators such that
$s u - r v = 1$. It is to be proven:

1) that every fraction whose value lies between $\frac{r}{u}$ and $\frac{s}{v}$
can be written in the form

$$ \frac{l r + m s}{l u + m v} $$

where $l$ and $m$ are positive integers, and

2) that conversely, the values of fractions of the said form lie between
$\frac{r}{u}$ and $\frac{s}{v}$.

[`Numina/problem_234330.lean`](Numina/problem_234330.lean)

```lean
theorem number_theory_234330 (r s : ℤ) (u v : ℕ) (hu : u ≠ 0) (hv : v ≠ 0)
    (h : s * u - r * v = 1) :
    (∀ x : ℚ, x ∈ (.uIoo (r / u) (s / v) : Set ℚ) →
      ∃ l m : ℕ, l ≠ 0 ∧ m ≠ 0 ∧ (l * r + m * s) / (l * u + m * v) = x) ∧
    ∀ l m : ℕ, l ≠ 0 → m ≠ 0 →
      ((l * r + m * s) / (l * u + m * v) : ℚ) ∈ (.uIoo (r / u) (s / v) : Set ℚ) := by
```

### `problem_213467`

$n$ is a positive integer. Try to determine how many real numbers $x$ satisfy
$1 \le x < n$ and $x^{3} - [x^{3}] = (x - [x])^{3}$.

[`Numina/problem_213467.lean`](Numina/problem_213467.lean)

```lean
theorem algebra_213467 (n : ℕ) (hn : 0 < n) :
    {x : ℝ | x ∈ Set.Ico 1 ↑n ∧ x^3 - ⌊x^3⌋ = (x - ⌊x⌋)^3}.ncard = n^3 - n := by
```

### `problem_242129`

Let $f(x) = a_{0} + a_{1} x + a_{2} x^{2} + \ldots + a_{n} x^{n}$, $a_{i} \ge 0$
($i = 0, 1, 2, \ldots n$), and in the interval $[-1, +1]$, $|f(x)| \le 1$.
Show that in this interval $\left|f^{\prime}(x)\right| \le n$;
the equality holds only when $f(x) = x^{n}$.

[`Numina/problem_242129.lean`](Numina/problem_242129.lean)

```lean
theorem algebra_242129 (n : ℕ) (a : Fin (n + 1) → ℝ) (ha : ∀ i, 0 ≤ a i)
    (f : ℝ[X]) (hf : f = ∑ i, C (a i) * X ^ i.val)
    (hf_abs : ∀ x ∈ Set.Icc (-1) 1, |f.eval x| ≤ 1) :
    (∀ x ∈ Set.Icc (-1) 1, |f.derivative.eval x| ≤ n) ∧
    (0 < n → ((∃ x ∈ Set.Icc (-1) 1, |f.derivative.eval x| = n) ↔ f = X ^ n)) := by
```

### `problem_226583`

Prove that any natural number $n$ can be uniquely represented in the form
$n = F_{k_{1}} + F_{k_{2}} + \ldots + F_{k_{m}}$, where
$k_{1} > k_{2} + 1, k_{2} > k_{3} + 1, \ldots, k_{m-1} > k_{m} + 1, k_{m} > 1$.

[`Numina/problem_226583.lean`](Numina/problem_226583.lean)

```lean
theorem number_theory_226583 {n : ℕ} :
    ∃! l : List ℕ, (l.Chain' fun i j ↦ j + 1 < i) ∧ (∀ h : l ≠ [], 1 < l.getLast h) ∧
      (l.map Nat.fib).sum = n := by
```

### `problem_101699`

Solve the system of equations:

$$
\begin{aligned}
\frac{1}{\sqrt{1 + 2 x^2}}+\frac{1}{\sqrt{1 + 2 y^2}} = \frac{2}{\sqrt{1 + 2 x y}}, \\
\sqrt{x (1 - 2 x)} + \sqrt{y (1 - 2 y)} = \frac{2}{9}
\end{aligned}
$$

[`Numina/problem_101699.lean`](Numina/problem_101699.lean)

```lean
theorem algebra_101699 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hx' : 0 ≤ x * (1 - 2 * x)) (hy' : 0 ≤ y * (1 - 2 * y))
    (h₁ : 1 / √(1 + 2 * x ^ 2) + 1 / √(1 + 2 * y ^ 2) = 2 / √(1 + 2 * x * y))
    (h₂ : √(x * (1 - 2 * x)) + √(y * (1 - 2 * y)) = 2 / 9) :
    x = y ∧ (x = 1 / 4 + √73 / 36 ∨ x = 1 / 4 - √73 / 36) := by
```

### `problem_122492`

Let $b \geqslant 2$ be an integer. Prove, using a generating series, that every
natural number has a unique decomposition in base $b$.

[`Numina/problem_122492.lean`](Numina/problem_122492.lean)

```lean
theorem number_theory_122492 (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∃! l : List ℕ, (∀ x ∈ l, x < b) ∧ (∀ (h : l ≠ []), l.getLast h ≠ 0) ∧
      Nat.ofDigits b l = n := by
```

### `problem_127824`

Prove that for any positive numbers $a_1, a_2, \cdots, a_n$, the inequality

$$ \frac{1}{a_1} + \frac{2}{a_1 + a_2} + \cdots + \frac{n}{a_1 + \cdots + a_n} <
  4 \left(\frac{1}{a_1} + \cdots + \frac{1}{a_n}\right) $$

holds.

[`Numina/problem_127824.lean`](Numina/problem_127824.lean)

```lean
theorem inequalities_127824 {n : ℕ} (hn_pos : 0 < n) (a : Fin n → ℝ) (ha_pos : ∀ i, 0 < a i) :
    ∑ i : Fin n, (i + 1 : ℕ) / (∑ j ≤ i, a j) < 4 * ∑ i, (a i)⁻¹ := by
```

### `problem_286896`

Let $x, y, z \in \mathbf{R}^{+}, x^{2}+y^{2}+z^{2}=1$. Find

$$ \frac{x^{5}}{y^{2}+z^{2}-y z}+\frac{y^{5}}{z^{2}+x^{2}-z x}+\frac{z^{5}}{x^{2}+y^{2}-x y} $$

the minimum value.

[`Numina/problem_286896.lean`](Numina/problem_286896.lean)

```lean
theorem inequalities_286896 :
  IsLeast
    {t | ∃ x y z, 0 < x ∧ 0 < y ∧ 0 < z ∧ x^2 + y^2 + z^2 = 1 ∧
      t = x^5 / (y^2 + z^2 - y * z) + y^5 / (z^2 + x^2 - z * x) + z^5 / (x^2 + y^2 - x * y)}
    (√3 / 3) := by
```

### `problem_295394`

Find all positive integers $N$, such that it equals the sum of the digits of $N^{3}$.

[`Numina/problem_295394.lean`](Numina/problem_295394.lean)

```lean
theorem number_theory_295394 (n : ℕ) :
    n ≠ 0 ∧ n = (Nat.digits 10 (n ^ 3)).sum ↔
    n = 1 ∨ n = 8 ∨ n = 17 ∨ n = 18 ∨ n = 26 ∨ n = 27 := by
```

### `problem_175773`

Let $n$ be an integer of the form $a^2 + b^2$ where $a$ and $b$ are relatively prime integers
and such that if $p$ is a prime, $p \leq \sqrt{n}$, then $p$ divides $a b$.
Determine all such $n$.

[`Numina/problem_175773.lean`](Numina/problem_175773.lean)

```lean
theorem number_theory_175773 (n : ℕ) :
    (∃ a b, a.Coprime b ∧ n = a^2 + b^2 ∧ ∀ p : ℕ, p ≤ √n → p.Prime → p ∣ a * b) ↔
    n = 1 ∨ n = 2 ∨ n = 5 ∨ n = 13 := by
```

### `problem_214659`

For which real parameters $a$ does there exist a complex number $z$ such that

$$ |z + \sqrt{2}| = \sqrt{a^{2} - 3 a + 2} \quad \text { and } \quad |z + i \sqrt{2}| < a ? $$

[`Numina/problem_214659.lean`](Numina/problem_214659.lean)

```lean
theorem algebra_214659 (a : ℝ) :
    (0 ≤ a^2 - 3 * a + 2 ∧ ∃ z : ℂ, abs (z + √2) = √(a^2 - 3 * a + 2) ∧ abs (z + I * √2) < a) ↔
      2 < a := by
```

### `problem_141351`

Let $x_i > 0$ ($i = 1, 2, \ldots, n$), $a \in \mathbf{R}^{+}$ and
$\sum_{i=1}^{n} x_i = s \leqslant a$. Prove that:

$$ \prod_{i=1}^{n} \frac{a + x_i}{a - x_i} \geqslant \left(\frac{n a + s}{n a - s}\right)^n . $$

[`Numina/problem_141351.lean`](Numina/problem_141351.lean)

```lean
theorem inequalities_141351 {n : ℕ} (x : Fin n → ℝ) (hx : ∀ i, 0 < x i)
    (a : ℝ) (ha : 0 < a) (s : ℝ) (hs : s = ∑ i, x i) (hsa : s ≤ a) :
    ((n * a + s) / (n * a - s)) ^ n ≤ ∏ i, (a + x i) / (a - x i) := by
```

### `problem_102449`

Let $a, b, c \in [0,1]$. Show that:

$$ \frac{a}{b+c+1} + \frac{b}{c+a+1} + \frac{c}{a+b+1} + (1-a)(1-b)(1-c) \leqslant 1 $$

[`Numina/problem_102449.lean`](Numina/problem_102449.lean)

```lean
theorem inequalities_102449 (a b c : ℝ)
    (ha : a ∈ Set.Icc 0 1) (hb : b ∈ Set.Icc 0 1) (hc : c ∈ Set.Icc 0 1) :
    a / (b + c + 1) + b / (c + a + 1) + c / (a + b + 1) + (1 - a) * (1 - b) * (1 - c) ≤ 1 := by
```

### `problem_244639`

$A = \{a, b, c\}$ is a set containing three positive integers. Prove that we can find a set
$B = \{x, y\} \subset A$ such that for all odd positive integers $m, n$ we have

$$ 10 \mid x^{m} y^{n} - x^{n} y^{m} $$

[`Numina/problem_244639.lean`](Numina/problem_244639.lean)

```lean
theorem number_theory_244639 (a : Finset ℕ) (ha_pos : ∀ x ∈ a, 0 < x) (ha_card : #a = 3) :
    ∃ x y, x ≠ y ∧ {x, y} ⊆ a ∧ ∀ m n, Odd m → Odd n → (10 : ℤ) ∣ x^m * y^n - x^n * y^m := by
```

### `problem_206432`

Reduce each of the first billion natural numbers (billion $=10^{9}$) to a single digit by
taking its digit sum repeatedly. Do we get more 1s than 2s ?

[`Numina/problem_206432.lean`](Numina/problem_206432.lean)

```lean
theorem number_theory_206432 :
    Nat.count (repeatedDigitSum 10 (Nat.one_lt_succ_succ _) · = 1) (10 ^ 9 + 1) >
    Nat.count (repeatedDigitSum 10 (Nat.one_lt_succ_succ _) · = 2) (10 ^ 9 + 1) := by
```

### `problem_229436`

Prove that if $x > -1$ and $x \neq 0$, then

$$ \frac{2 |x|}{2 + x} < |\ln (1+x)| < \frac{|x|}{\sqrt{1 + x}} $$


[`Numina/problem_229436.lean`](Numina/problem_229436.lean)

```lean
theorem inequalities_229436 {x : ℝ} (hx_gt : x > -1) (hx_ne : x ≠ 0) :
    2 * |x| / (2 + x) < |log (1 + x)| ∧ |log (1 + x)| < |x| / √(1 + x) := by
```

### `problem_149462`

Let $x_{1}, \ldots, x_{n} > 0$ with $x_{1} \dots x_{n} = 1$. Show that

$$
x_{1}^{n-1} + x_{2}^{n-1} + \cdots + x_{n}^{n-1} \geqslant \frac{1}{x_{1}} + \ldots \frac{1}{x_{n}}
$$

[`Numina/problem_149462.lean`](Numina/problem_149462.lean)

```lean
theorem inequalities_149462 (n : ℕ) (x : Fin n → ℝ) (hx : ∀ i, 0 < x i) (hx_prod : ∏ i, x i = 1) :
    ∑ i, (x i)⁻¹ ≤ ∑ i, (x i) ^ (n - 1) := by
```

### `problem_270990`

Show that the equation

$$ 1 + x + \frac{x^{2}}{2!} + \frac{x^{3}}{3!} + \cdots + \frac{x^{2 n}}{(2 n)!} = 0 $$

has no real roots.

[`Numina/problem_270990.lean`](Numina/problem_270990.lean)

```lean
theorem algebra_270990 (n : ℕ) :
    ¬∃ x : ℝ, ∑ i ∈ Finset.range (2 * n + 1), x ^ i / (Nat.factorial i) = 0 := by
```

### `problem_245605`

Represent the number 100 as the sum of the maximum possible number of pairwise coprime natural
numbers. Explanation: the condition means that the greatest common divisor of any two numbers used
in the sum is 1.

[`Numina/problem_245605.lean`](Numina/problem_245605.lean)

```lean
theorem number_theory_245605 :
    {2, 3, 5, 7, 11, 13, 17, 19, 23} ∈ {s : Finset ℕ | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100} ∧
    IsMaxOn Finset.card {s : Finset ℕ | Set.Pairwise s Coprime ∧ ∑ x ∈ s, x = 100}
      {2, 3, 5, 7, 11, 13, 17, 19, 23} := by
```

### `problem_159991`

Let $0 < x_{i} < π$ ($i = 1, 2, \ldots, n$), prove that:

$$ \prod_{i=1}^{n} \sin(x_{i}) \leqslant
  \left[\sin\left(\frac{1}{n} \sum_{i=1}^{n} x_{i}\right)\right]^{n} . $$

[`Numina/problem_159991.lean`](Numina/problem_159991.lean)

```lean
theorem inequalities_159991 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hx : ∀ i, x i ∈ Ioo 0 π) :
    ∏ i, sin (x i) ≤ (sin (1 / n * ∑ i, x i)) ^ n := by
```


# Batch 5

### `problem_125818`

Find all integers $k > 1$ such that for some distinct positive integers $a, b$, the number
$k^a + 1$ can be obtained from $k^b + 1$ by reversing the order of its (decimal) digits.

<https://web.archive.org/web/20041210123510/http://www.kalva.demon.co.uk/soviet/ssoln/ssol9220.html>

[`Numina/problem_125818.lean`](Numina/problem_125818.lean)

```lean
theorem number_theory_125818 (k : ℕ) (hk_gt : 1 < k) :
    (∃ a b, 0 < a ∧ 0 < b ∧ a ≠ b ∧
      Nat.digits 10 (k ^ a + 1) = (Nat.digits 10 (k ^ b + 1)).reverse) ↔
    k = 3 := by
```

### `problem_179469`

Determine the number of all pairs $(a, b)$ of single-digit natural numbers $a$ and $b$ for which
$a < \overline{a, b} < b$ holds! Here, 0 is considered a single-digit number, and $\overline{a, b}$
denotes the decimal number that has the digit $a$ before the decimal point and the digit $b$ after
the decimal point.

[`Numina/problem_179469.lean`](Numina/problem_179469.lean)

```lean
theorem number_theory_179469 :
    {(a, b) : ℕ × ℕ | a < 10 ∧ b < 10 ∧
      a < a + (b / 10 : ℚ) ∧ a + (b / 10 : ℚ) < b}.ncard = 45 := by
```

### `problem_230328`

Let $k_{1} < k_{2} < k_{3} < \cdots$ be positive integers, and no two of them are consecutive,
and for $m = 1, 2, 3, \ldots$, $S_{m} = k_{1} + k_{2} + \cdots + k_{m}$. Prove that for every
positive integer $n$, the interval $[S_{n}, S_{n+1})$ contains at least one perfect square.

[`Numina/problem_230328.lean`](Numina/problem_230328.lean)

```lean
theorem number_theory_230328 (k : ℕ → ℕ) (hk : StrictMono k)
    (hk_pos : ∀ n, 0 < k n) (hk_consec : ∀ n, k (n + 1) ≠ k n + 1)
    (S : ℕ → ℕ) (hS : ∀ m, S m = ∑ i in Finset.range (m + 1), k i) (n : ℕ) :
    ∃ m, m ^ 2 ∈ Set.Ico (S n) (S (n + 1)) := by
```

### `problem_291009`

Let $n$ be a natural number. Prove that the binary representation of the integer
$n (2^{n} - 1)$ contains exactly $n$ occurrences of the digit 1.

[`Numina/problem_291009.lean`](Numina/problem_291009.lean)

```lean
theorem number_theory_291009 (n : ℕ) :
    (Nat.digits 2 (n * (2 ^ n - 1))).count 1 = n := by
```

### `problem_262514`

Let $p > 3$ be a prime number. Show that $p^{2}$ is a divisor of

$$ \sum_{k=1}^{p-1} k^{2 p + 1} $$

[`Numina/problem_262514.lean`](Numina/problem_262514.lean)

```lean
theorem number_theory_262514 (p : ℕ) (hp : p.Prime) (h : 3 < p) :
    p ^ 2 ∣ ∑ k ∈ Ico 1 p, k ^ (2 * p + 1) := by
```

### `problem_219484`

Let's find all positive integers $n$ for which $2^{n} - 1$ and $2^{n+2} - 1$ are both prime,
and $2^{n+1}-1$ is not divisible by 7.

[`Numina/problem_219484.lean`](Numina/problem_219484.lean)

```lean
theorem number_theory_219484 (n : ℕ) (hn : 0 < n) :
    Nat.Prime (2 ^ n - 1) ∧ Nat.Prime (2 ^ (n + 2) - 1) ∧ ¬7 ∣ 2 ^ (n + 1) - 1 ↔ n = 3 := by
```

### `problem_111609`

Let the temperature $T$ of an object be a function of time $t$:
$T(t) = a t^3 + b t^2  + c t + d$ ($a \neq 0$)$, where the temperature is in
${ }^{\circ} \mathrm{C}$ and the time is in hours, with $t = 0$ representing 12:00, and
positive $t$ values representing times after 12:00.
If the temperature of the object is measured to be $8^{\circ} \mathrm{C}$ at 8:00,
$60^{\circ} \mathrm{C}$ at 12:00, and $58^{\circ} \mathrm{C}$ at 13:00, and it is known that the
rate of change of the object's temperature at 8:00 and 16:00 is the same.
(1) Write the function relating the object's temperature $T$ to time $t$;
(2) At what time between 10:00 and 14:00 (inclusive) is the temperature of the object the highest?
And find the highest temperature.

[`Numina/problem_111609.lean`](Numina/problem_111609.lean)

```lean
theorem algebra_111609 {a b c d : ℝ} (ha : a ≠ 0)
    (f : ℝ[X]) (hf : f = C a * X ^ 3 + C b * X ^ 2 + C c * X + C d)
    (hf_0800 : f.eval (-4) = 8) (hf_1200 : f.eval 0 = 60) (hf_1300 : f.eval 1 = 58)
    (hf_deriv_eq : f.derivative.eval (-4) = f.derivative.eval 4) :
    (a = 1 ∧ b = 0 ∧ c = -3 ∧ d = 60) ∧
    (∀ x ∈ Set.Icc (-2) 2, f.eval x ≤ 62) ∧
    {x ∈ Set.Icc (-2) 2 | f.eval x = 62} = {-1, 2} := by
```

### `problem_122216`

For any positive integer $n > 1$, let $P(n)$ denote the largest prime not exceeding $n$.
Let $N(n)$ denote the next prime larger than $P(n)$. (For example $P(10) = 7$ and $N(10) = 11$,
while $P(11) = 11$ and $N(11) = 13$.) If $n+1$ is a prime number, prove that the value of the sum

$$
\frac{1}{P(2) N(2)} + \frac{1}{P(3) N(3)} + \frac{1}{P(4) N(4)} + \cdots + \frac{1}{P(n) N(n)} =
\frac{n - 1}{2 n + 2}
$$

[`Numina/problem_122216.lean`](Numina/problem_122216.lean)

```lean
theorem number_theory_122216 {P N : ℕ → ℕ}
    (hP : ∀ n, P n = sSup {p | p.Prime ∧ p ≤ n})
    (hN : ∀ n, N n = sInf {p | p.Prime ∧ n < p})
    (n : ℕ) (hn : 1 < n) (h_prime : (n + 1).Prime) :
    ∑ i ∈ Icc 2 n, 1 / (P i * N i : ℚ) = (n - 1) / (2 * n + 2) := by
```

### `problem_260669`

If a positive integer $n$ makes the equation $x^3 + y^3 = z^n$ have positive integer solutions
$(x, y, z)$, then $n$ is called a "good number". Then, the number of good numbers not exceeding
2019 is?

[`Numina/problem_260669.lean`](Numina/problem_260669.lean)

```lean
def isGood (n : ℕ) := ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^n

theorem number_theory_260669 (h_fermat : ¬∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x^3 + y^3 = z^3) :
    {n ≤ 2019 | isGood n}.ncard = 1346 := by
```

### `problem_222793`

Prove the Intermediate Value Theorem for a quadratic trinomial.

[`Numina/problem_222793.lean`](Numina/problem_222793.lean)

```lean
theorem algebra_222793 (c₀ c₁ c₂ : ℝ) (f : ℝ → ℝ) (hf : ∀ x, f x = c₂ * x ^ 2 + c₁ * x + c₀)
    (a b y : ℝ) (hy : y ∈ Set.uIcc (f a) (f b)) :
    ∃ x ∈ Set.uIcc a b, f x = y := by
```

### `problem_118182`

Find all natural numbers $a$ and $b$ such that $\sqrt{a} - \sqrt{b}$ is a root
of the equation $x^2 + a x - b = 0$.

[`Numina/problem_118182.lean`](Numina/problem_118182.lean)

```lean
theorem algebra_118182 (a b : ℕ) :
    (√a - √b)^2 + a * (√a - √b) - b = 0 ↔ a = 0 ∨ a = 2 ∧ b = 1 := by
```

### `problem_205122`

The sequences $\{a_{n}\}$ and $\{b_{n}\}$ are infinite arithmetic and geometric sequences,
respectively. The sum of the first $n$ terms of $\{a_{n}\}$ is $S_{n} = \frac{3 n^2 + 5 n}{2}$.
In the sequence $\{b_{n}\}$, $b_{3}=4$ and $b_{6}=32$. Let $\{c_{n}\}(n \in \mathbf{N}^{+})$ be
the new sequence formed by all common terms of $\{a_{n}\}$ and $\{b_{n}\}$ (in the original order).
Prove that $\{c_{n}\}$ is a geometric sequence.

[`Numina/problem_205122.lean`](Numina/problem_205122.lean)

```lean
theorem algebra_205122 {a b : ℕ → ℝ}
    (ha : ∃ d, ∀ n, a n = a 0 + d * n) (hb : ∃ q, ∀ n, b n = b 0 * q ^ n)
    (hs : ∀ n, ∑ i in Finset.range n, a i = (3 * n ^ 2 + 5 * n : ℝ) / 2)
    (hb2 : b 2 = 4) (hb5 : b 5 = 32) :
    Set.range (fun n ↦ 4 ^ (n + 1)) = Set.range a ∩ Set.range b := by
```

### `problem_184865`

Natural numbers $a < b < c$ are such that $b+a$ is divisible by $b−a$, and $c+b$ is
divisible by $c−b$. The number $a$ is written with 2011 digits, and the number $b−2012$ is
written with 2012 digits. How many digits does the number $c$ have?

[`Numina/problem_184865.lean`](Numina/problem_184865.lean)

```lean
theorem number_theory_184865 (a b c : ℕ) (hab : a < b) (hbc : b < c)
    (hab_dvd : b - a ∣ b + a) (hbc_dvd : c - b ∣ c + b)
    (ha_digits : (Nat.digits 10 a).length = 2011)
    (hb_digits : (Nat.digits 10 (b - 2012)).length = 2012) :
    (Nat.digits 10 c).length = 2012 := by
```

### `problem_125542`

The sum of the squares of two consecutive positive integers can be a square,
for example $3^2 + 4^2 = 5^2$.
Show that the sum of the squares of 3 or 6 consecutive positive integers cannot be a square.
Give an example of the sum of the squares of 11 consecutive positive integers which is a square.

[`Numina/problem_125542.lean`](Numina/problem_125542.lean)

```lean
theorem number_theory_125542 :
    (¬∃ n m, ∑ i ∈ Finset.range 3, (n + i) ^ 2 = m ^ 2) ∧
    (¬∃ n m, ∑ i ∈ Finset.range 6, (n + i) ^ 2 = m ^ 2) ∧
    ∑ i ∈ Finset.range 11, (18 + i) ^ 2 = 77^2 := by
```

### `problem_202399`

Prove the inequalities:

a) $\sqrt[n]{a_1 \cdots a_n} ≤ \frac{a_1 + \cdots + a_n}{n}$ (Cauchy's inequality);

b) $(\frac{b_1 + \cdots + b_n}{n})^{b_1 + \cdots + b_n} ≤ b_1^{b_1} \cdots b_n^{b_n}$

c) $c_1^{b_1} \cdots c_n^{b_n} ≤ c_1 b_1 + \cdots + c_n b_n$, where $b_1 + \cdots + b_n = 1$.

The values of the variables are assumed to be positive.

[`Numina/problem_202399.lean`](Numina/problem_202399.lean)

```lean
theorem inequalities_202399 {n : ℕ} (hn : 0 < n) (a b c : Fin n → ℝ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i) (hc_pos : ∀ i, 0 < c i)
    (hb : ∑ i, b i = 1) :
    (∏ i, a i) ^ (1 / n : ℝ) ≤ (∑ i, a i) / n ∧
    ((∑ i, b i) / n) ^ (∑ i, b i) ≤ ∏ i, (b i) ^ (b i) ∧
    ∏ i, (c i) ^ (b i) ≤ ∑ i, c i * b i := by
```

### `problem_188980`

Kolya Vasin wrote down an example of multiplication, and then replaced all the digits with
letters: the same digits with the same letters, and different digits with different letters.
The resulting equation is $\overline{a b} \cdot \overline{c d} = \overline{e f f e}$.
Did Kolya make a mistake?

[`Numina/problem_188980.lean`](Numina/problem_188980.lean)

```lean
theorem number_theory_188980 (a b c d e f : ℕ) (h_nodup : [a, b, c, d, e, f].Nodup) :
    ¬∃ x y z : ℕ, Nat.digits 10 x = [b, a] ∧ Nat.digits 10 y = [d, c] ∧
      Nat.digits 10 z = [e, f, f, e] ∧ x * y = z := by
```

### `problem_128360`

$p(x)$ is a polynomial of degree $n$ with real coefficients and is non-negative for all $x$.
Show that $p(x) + p'(x) + p''(x) + \cdots \text{($n + 1$ terms)} ≥ 0$ for all $x$.

[`Numina/problem_128360.lean`](Numina/problem_128360.lean)

```lean
theorem algebra_128360 (p : Polynomial ℝ)
    (hp_nonneg : ∀ x, 0 ≤ p.eval x) :
    ∀ x, 0 ≤ ∑ i ∈ Finset.range (p.natDegree + 1), (derivative^[i] p).eval x := by
```

### `problem_112767`

Let $a, b, c$ be positive real numbers such that $a b c = 1$. Prove that

$$ \frac{1}{a+b} + \frac{1}{b+c} + \frac{1}{a+c} \leq \frac{a^{2}+b^{2}+c^{2}}{2} $$

[`Numina/problem_112767.lean`](Numina/problem_112767.lean)

```lean
theorem inequalities_112767 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a + b) + 1 / (b + c) + 1 / (a + c) ≤ (a ^ 2 + b ^ 2 + c ^ 2) / 2 := by
```

### `problem_148288`

If for any $x \in(-\infty,-1)$, we have

$$ (m - m^{2}) 4^{x} + 2^{x} + 1 > 0, $$

then the range of real number $m$ is?

[`Numina/problem_148288.lean`](Numina/problem_148288.lean)

```lean
theorem inequalities_148288 (m : ℝ) :
    (∀ x : ℝ, x < -1 → 0 < (m - m^2) * 4^x + 2^x + 1) ↔ m ∈ Set.Icc (-2) 3 := by
```

### `problem_100122`

Let $a, b, c$ be positive real numbers such that $a b c = 1$. Show that

$$
\frac{1}{a^{3} + b c} + \frac{1}{b^{3} + c a} + \frac{1}{c^{3} + a b} \leq
  \frac{(a b + b c + c a)^{2}}{6}
$$

[`Numina/problem_100122.lean`](Numina/problem_100122.lean)

```lean
theorem inequalities_100122 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 3 + b * c) + 1 / (b ^ 3 + c * a) + 1 / (c ^ 3 + a * b) ≤
      ((a * b + b * c + c * a) ^ 2) / 6 :=
```

### `problem_223945`

Prove that for any natural $n \geqslant 2$ the number $2^{4 n + 2} + 1$ is
not the product of two prime numbers.

[`Numina/problem_223945.lean`](Numina/problem_223945.lean)

```lean
theorem number_theory_223945 (n : ℕ) (hn : 2 ≤ n) :
    ¬∃ p q, 2 ^ (4 * n + 2) + 1 = p * q ∧ p.Prime ∧ q.Prime := by
```

### `problem_145653`

Let $f(x)$ and $g(x)$ be odd and even functions defined on $R$, respectively, and
$f(x) + g(x) = 2^x$. If for $x \in [1, 2]$, the inequality $a f(x) + g(2x) \geq 0$ always holds,
then the range of the real number $a$ is?

[`Numina/problem_145653.lean`](Numina/problem_145653.lean)

```lean
theorem algebra_145653 (f g : ℝ → ℝ) (hf : f.Odd) (hg : g.Even)
    (hfg : ∀ x, f x + g x = 2 ^ x) (a : ℝ) :
    (∀ x ∈ Set.Icc 1 2, 0 ≤ a * f x + g (2 * x)) ↔ -17/6 ≤ a := by
```

### `problem_139025`

The real polynomial $p(x) ≡ x^3 + a x^2 + b x + c$ has three real roots $α < β < γ$.
Show that $\sqrt{a^2 - 3 b} < (γ - α) ≤ 2 \sqrt{a^2 / 3 - b}$.

<https://prase.cz/kalva/putnam/psoln/psol5113.html>

[`Numina/problem_139025.lean`](Numina/problem_139025.lean)

```lean
theorem algebra_139025 {a b c α β γ : ℝ}
    (h : (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots = {α, β, γ}) (hαβ : α < β) (hβγ : β < γ) :
    √(a ^ 2 - 3 * b) < γ - α ∧ γ - α ≤ 2 * √(a ^ 2 / 3 - b) := by
```

### `problem_205856`

Prove that any 39 successive natural numbers include at least one whose
digit sum is divisible by 11.

[`Numina/problem_205856.lean`](Numina/problem_205856.lean)

```lean
theorem number_theory_205856 (n : ℕ) :
    ∃ m ∈ Set.Ico n (n + 39), 11 ∣ (Nat.digits 10 m).sum := by
```

### `problem_250464`

If real numbers $a, b, x, y$ satisfy

$$ \begin{align}
a x + b y & = 3 , \\
a x^{2} + b y^{2} & = 7 , \\
a x^{3} + b y^{3} & = 16 , \\
a x^{4} + b y^{4} & = 42 ,
\end{align} $$

find the value of $a x^{5}+b y^{5}$.

[`Numina/problem_250464.lean`](Numina/problem_250464.lean)

```lean
theorem algebra_250464 (a b x y : ℝ) (h₁ : a * x + b * y = 3) (h₂ : a * x^2 + b * y^2 = 7)
    (h₃ : a * x^3 + b * y^3 = 16) (h₄ : a * x^4 + b * y^4 = 42) :
    a * x^5 + b * y^5 = 20 := by
```

### `problem_107999`

Solve the Diophantine equation $6(x^{2} + y^{2}) = z^{2} + t^{2}$.

[`Numina/problem_107999.lean`](Numina/problem_107999.lean)

```lean
theorem number_theory_107999 (x y z t : ℕ) (h : 6 * (x ^ 2 + y ^ 2) = z ^ 2 + t ^ 2) :
    (x, y, z, t) = 0 := by
```

### `problem_198767`

Determine all pairs $(a, b)$ of prime numbers for which the following holds:

$$ 3 a^{2} + a = b^{2} + b $$

[`Numina/problem_198767.lean`](Numina/problem_198767.lean)

```lean
theorem number_theory_198767 (a b : ℕ) (ha : a.Prime) (hb : b.Prime) (h : 3 * a^2 + a = b^2 + b) :
    a = 3 ∧ b = 5 := by
```


# Batch 4

### `problem_251758`

$$
\frac{\tan(96°) - \tan(12°) (1 + \frac{1}{\sin(6°)})}
  {1 + \tan(96°) \tan(12°) (1 + \frac{1}{\sin(6°)})} = \text{?}
$$

[`Numina/problem_251758.lean`](Numina/problem_251758.lean)

```lean
theorem algebra_251758 :
    (tan (96 / 180 * π) - tan (12 / 180 * π) * (1 + 1 / sin (6 / 180 * π))) /
    (1 + tan (96 / 180 * π) * tan (12 / 180 * π) * (1 + 1 / sin (6 / 180 * π))) = √3 / 3 := by
```

### `problem_223902`

For how many primes $p$ does there exist an integer $n$ such that
$\sqrt{p+n} + \sqrt{n}$ is an integer.
(A) does not exist.
(B) there is only one.
(C) more than one, but a finite number.
(D) there are infinitely many.

[`Numina/problem_223902.lean`](Numina/problem_223902.lean)

```lean
theorem number_theory_223902 : Set.Infinite {p : ℕ | p.Prime ∧ ∃ n m : ℕ, √(p + n) + √n = m} := by
```

### `problem_265535`

The function $f(x)$ is defined on $\mathbf{N}$, taking values in $\mathbf{N}$, and is a
strictly increasing function (if for any $x_{1}, x_{2} \in A$, when $x_{1} < x_{2}$, we have
$f(x_{1}) < f(x_{2})$, then $f(x)$ is called a strictly increasing function on $A$),
and satisfies the condition $f(f(k)) = 3 k$. Try to find the value of $f(1) + f(9) + f(96)$.

[`Numina/problem_265535.lean`](Numina/problem_265535.lean)

```lean
theorem algebra_265535 (f : ℕ → ℕ) (h_mono : StrictMono f) (hf : ∀ k, f (f k) = 3 * k) :
    f 1 + f 9 + f 96 = 197 := by
```

### `problem_105222`

Given the natural numbers

$$
\begin{aligned}
a & = 2 (1 + 2 + 3 + \cdots + 2016) - 2016 \\
b & = 1 + 1 \cdot 2 + 1 \cdot 2 \cdot 3 + 1 \cdot 2 \cdot 3 \cdot 4 + \cdots +
  1 \cdot 2 \cdot 3 \cdots 2016
\end{aligned}
$$

Show that:
a) a is a perfect square;
b) b is not a perfect square.

[`Numina/problem_105222.lean`](Numina/problem_105222.lean)

```lean
theorem number_theory_105222 :
    IsSquare (2 * ∑ i ∈ Finset.Icc 1 2016, i - 2016) ∧
    ¬IsSquare (∑ i ∈ Finset.Icc 1 2016, ∏ j ∈ Finset.Icc 1 i, j) := by
```

### `problem_159027`

Solve the system of equations

$$ \begin{align}
10 x^{2} + 5 y^{2} - 2 x y - 38 x - 6 y + 41 & = 0 \\
3 x^{2} - 2 y^{2} + 5 x y - 17 x - 6 y + 20 & = 0
\end{align} $$

[`Numina/problem_159027.lean`](Numina/problem_159027.lean)

```lean
theorem algebra_159027 {x y : ℝ}
    (h₁ : 10 * x ^ 2 + 5 * y ^ 2 - 2 * x * y - 38 * x - 6 * y + 41 = 0)
    (h₂ : 3 * x ^ 2 - 2 * y ^ 2 + 5 * x * y - 17 * x - 6 * y + 20 = 0) :
    x = 2 ∧ y = 1 := by
```

### `problem_271760`

Prove that if you select four consecutive terms $a_{n-1}, a_{n}, a_{n+1}, a_{n+2}$
in the Fibonacci sequence and subtract the product of the middle terms $a_{n} a_{n+1}$
from the product of the outer terms $a_{n-1} a_{n+2}$, the result will be 1 or -1.
Prove that for any Fibonacci sequence, the absolute value of the expression
$u_{n-1} u_{n+2} - u_{n} u_{n+1}$ does not depend on $n$.

[`Numina/problem_271760.lean`](Numina/problem_271760.lean)

```lean
theorem number_theory_271760 {u : ℕ → ℝ}
    (hu : ∀ n, u (n + 2) = u n + u (n + 1)) :
    (∃ c, ∀ n, |u n * u (n + 3) - u (n + 1) * u (n + 2)| = c) ∧
    (u 0 = 0 → u 1 = 1 → ∀ n, u n * u (n + 3) - u (n + 1) * u (n + 2) ∈ ({1, -1} : Set _)) := by
```

### `problem_152633`

Given that the sum of several positive integers is 2019.
Find the maximum value of their product.

[`Numina/problem_152633.lean`](Numina/problem_152633.lean)

```lean
theorem number_theory_152633 :
    IsGreatest (Multiset.prod '' {s | s.sum = 2019}) (3 ^ 673) := by
```

### `problem_171841`

Prove: For any $a_{1}, a_{2}, \cdots, a_{n} \in \mathbf{R}$, there exists
$k \in \{1, 2, \cdots, n\}$, such that for any non-negative real numbers
$b_{1} \geqslant b_{2} \geqslant \cdots \geqslant b_{n}$ not exceeding 1, we have

$$ \left|\sum_{i=1}^{n} b_{i} a_{i}\right| \leqslant \left|\sum_{i=1}^{k} a_{i}\right| $$

[`Numina/problem_171841.lean`](Numina/problem_171841.lean)

```lean
theorem inequalities_171841 (n : ℕ) (a : ℕ → ℝ) : ∃ k ≤ n,
    ∀ b : Fin n → ℝ, (∀ i, 0 ≤ b i) → (∀ i, b i ≤ 1) → Antitone b →
    |∑ i : Fin n, b i * a i| ≤ |∑ i ∈ range k, a i| := by
```

### `problem_290058`

Find all pairs of positive integers $m$ and $n$ for which
$\sqrt{m^{2} - 4} < 2 \sqrt{n} - m < \sqrt{m^{2} - 2}$.

[`Numina/problem_290058.lean`](Numina/problem_290058.lean)

```lean
theorem inequalities_290058 :
    {(m, n) : ℕ × ℕ | 0 < m ∧ 0 < n ∧ (0 : ℝ) ≤ m^2 - 4 ∧
      2 * √n - m ∈ Set.Ioo √(m^2 - 4) √(m^2 - 2)} =
    {(m, n) : ℕ × ℕ | 2 ≤ m ∧ n = m^2 - 2} := by
```

### `problem_interesting`

A natural number $n$ is interesting if the sum of the digits of $n$ is equal to the
sum of the digits of $3 n+11$. Verify that there are infinitely many interesting numbers.

[`Numina/problem_interesting.lean`](Numina/problem_interesting.lean)

```lean
theorem number_theory_255881 :
    {n | (Nat.digits 10 n).sum = (Nat.digits 10 (3 * n + 11)).sum}.Infinite := by
```

### `problem_199764`

If you write all natural numbers $n$ with $111 \leq n \leq 999$ in any order consecutively,
you will always get a sequence of digits that forms a number divisible by 37.

[`Numina/problem_199764.lean`](Numina/problem_199764.lean)

```lean
theorem number_theory_199764 (l : List ℕ) (h_perm : l ~ List.Ico 111 1000) :
    37 ∣ Nat.ofDigits 10 (l.map (Nat.digits 10)).flatten := by
```

### `problem_211660`

Does the number 11⋯1 (1000 ones) have a ten-digit divisor, all digits of which are different?

[`Numina/problem_211660.lean`](Numina/problem_211660.lean)

```lean
theorem number_theory_211660 : ¬∃ n, (Nat.digits 10 n).length = 10 ∧ (Nat.digits 10 n).Nodup ∧
    n ∣ Nat.ofDigits 10 (List.replicate 1000 1) := by
```

### `problem_111982`

Let the function $f : \mathbb{R} \rightarrow \mathbb{R}, f(x) = x + \log_{3}(1+3^{x})$.
Show that:
a) The function $f$ is invertible and $f^{-1}(x) < f(x)$
b) $f(n) ∈ \mathbb{R} \setminus \mathbb{Q}$ for all $n \in \mathbb{N}^{*}$.

[`Numina/problem_111982.lean`](Numina/problem_111982.lean)

```lean
theorem calculus_111982 (f : ℝ → ℝ) (hf : ∀ x, f x = x + logb 3 (1 + 3 ^ x)) :
    (∃ g : ℝ → ℝ, (g.LeftInverse f ∧ g.RightInverse f) ∧ ∀ x, g x < f x) ∧
    ∀ n : ℕ, n ≠ 0 → Irrational (f n) := by
```

### `problem_132790`

Calculate the indefinite integral:

$$
\int \frac{2 x^{3} + 6 x^{2} + 5 x + 4}{(x - 2)(x + 1)^{3}} d x
$$

[`Numina/problem_132790.lean`](Numina/problem_132790.lean)

```lean
theorem calculus_132790 (x : ℝ) (hx : x ≠ 2) (hx' : x ≠ -1) (C : ℝ) :
    HasDerivAt (fun x ↦ 2 * log |x - 2| + 1 / (2 * (x + 1)^2) + C)
      ((2 * x^3 + 6 * x^2 + 5 * x + 4) / ((x - 2) * (x + 1)^3)) x := by
```

### `problem_99850`

Determine the family of primitives

$$ I = \int \frac{x \ln \left(1 + \sqrt{1 + x^{2}}\right)}{\sqrt{1+x^{2}}} d x $$

[`Numina/problem_99850.lean`](Numina/problem_99850.lean)

```lean
theorem calculus_99850 (a x : ℝ) :
    ∃ c, ∫ x in a..x, x * log (1 + √(1 + x ^ 2)) / √(1 + x ^ 2) =
      (1 + √(1 + x ^ 2)) * log (1 + √(1 + x ^ 2)) - √(1 + x ^ 2) + c := by
```

### `problem_129966`

For any real numbers $a, b, c$, prove that there exists a real number $x$ such that
$a \cos(x) + b \cos(3 x) + c \cos(9 x) \ge \frac{1}{2}(|a| + |b| + |c|)$.

[`Numina/problem_129966.lean`](Numina/problem_129966.lean)

```lean
theorem inequalities_129966 (a b c : ℝ) :
    ∃ x, a * cos x + b * cos (3 * x) + c * cos (9 * x) ≥ (|a| + |b| + |c|) / 2 := by
```

### `problem_113877`

If $A \in M_{n}(\mathbb{R})$ and $A^{3} = A + I_{n}$, prove that $det(A) > 0$.

[`Numina/problem_113877.lean`](Numina/problem_113877.lean)

```lean
theorem algebra_113877 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (h : A^3 = A + 1) : A.det > 0 := by
```

### `problem_280132`

Find the positive integer tuple $(a, b, c)$ such that $a^2 + b + 3 = (b^2 - c^2)^2$.

[`Numina/problem_280132.lean`](Numina/problem_280132.lean)

```lean
theorem number_theory_280132 (a b c : ℤ) (ha_pos : 0 < a) (hb_pos : 0 < b) (hc_pos : 0 < c)
    (h : a ^ 2 + b + 3 = (b ^ 2 - c ^ 2) ^ 2) :
    (a, b, c) = (2, 2, 1) := by
```

### `problem_214766`

Let's prove that if the number $\overline{a b c}$ written in the decimal system
is divisible by 7, then the fraction $\frac{\overline{b c} + 16 a}{\overline{b c} - 61 a}$
can be simplified by 7.

[`Numina/problem_214766.lean`](Numina/problem_214766.lean)

```lean
theorem number_theory_214766 {a b c : ℤ}
    (h : 7 ∣ (100 * a + 10 * b + c)) :
    7 ∣ (b * 10 + c + 16 * a) ∧ 7 ∣ (b * 10 + c - 61 * a) := by
```

### `problem_178166`

Given

$$
\begin{align}
a + b + c &= 5, \\
a^{2} + b^{2} + c^{2} & = 15, \\
a^{3} + b^{3} + c^{3} & = 47.
\end{align}
$$

Find the value $(a^{2} + a b + b^{2}) (b^{2} + b c + c^{2}) (c^{2} + c a + a^{2})$.

[`Numina/problem_178166.lean`](Numina/problem_178166.lean)

```lean
theorem algebra_178166 {a b c : ℝ} (h₁ : a + b + c = 5) (h₂ : a^2 + b^2 + c^2 = 15)
    (h₃ : a^3 + b^3 + c^3 = 47) :
    (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) = 625 := by
```

### `problem_287054`

Given the sequence $\{a_{n}\}$ satisfies $3 a_{n+1} + a_{n} = 4$ ($n \geqslant 1$) and
$a_{1} = 9$, with the sum of its first $n$ terms being $S_{n}$, then the smallest integer $n$
that satisfies the inequality $|S_{n} - n - 6\| < \frac{1}{125}$ is what?

[`Numina/problem_287054.lean`](Numina/problem_287054.lean)

```lean
theorem algebra_287054 {a : ℕ → ℝ} (ha : ∀ n, 3 * a (n + 1) + a n = 4) (ha1 : a 0 = 9) :
    IsLeast {n | |∑ k in Finset.range n, a k - n - 6| < 125⁻¹} 7 := by
```

### `problem_117773`

Given $f(x) = x^2 + c$, and $f(f(x)) = f(x^2 + 1)$.

(1) Let $g(x) = f(f(x))$, find the analytical expression of the function $g(x)$;

(2) Let $\varphi(x) = g(x) - \lambda f(x)$, try to find the value of the real number
$\lambda$ such that $\varphi(x)$ is a decreasing function on $(-\infty,-1]$ and
an increasing function on $[-1,0)$.

[`Numina/problem_117773.lean`](Numina/problem_117773.lean)

```lean
theorem algebra_117773 {f g : ℝ → ℝ} (hf : ∃ c, ∀ x, f x = x ^ 2 + c)
    (hff : ∀ x, f (f x) = f (x ^ 2 + 1))
    (hg : ∀ x, g x = f (f x)) :
    (∀ x, g x = x ^ 4 + 2 * x ^ 2 + 2) ∧ AntitoneOn (fun x ↦ g x - 4 * f x) (Set.Iic (-1)) ∧
      MonotoneOn (fun x ↦ g x - 4 * f x) (Set.Ico (-1) 0) := by
```

### `problem_214459`

For the elements of the sequence $a_{n}$, it holds that $a_{1} = 1337$,
and furthermore, that $a_{2 n + 1} = a_{2 n} = n - a_{n}$ for every positive integer $n$.
Determine the value of $a_{2004}$.

[`Numina/problem_214459.lean`](Numina/problem_214459.lean)

```lean
theorem algebra_214459 (a : ℕ → ℤ) (ha1 : a 1 = 1337)
    (ha_odd : ∀ n, a (2 * n + 1) = a (2 * n)) (ha_even : ∀ n, a (2 * n) = n - a n) :
    a 2004 = 2004 :=
```

### `problem_289784`

There do not exist integers $x, y$ such that $x^2 + 3 x y - 2 y^2 = 122$.

[`Numina/problem_289784.lean`](Numina/problem_289784.lean)

```lean
theorem number_theory_289784 : ¬∃ x y : ℤ, x ^ 2 + 3 * x * y - 2 * y ^ 2 = 122 := by
```

### `problem_247723`

Solve the equation

$$ \sqrt{5 x + 1} - 2 \sqrt{4 - x} + \sqrt{5} \sqrt{x + 2} = \sqrt{61 - 4 x} $$

[`Numina/problem_247723.lean`](Numina/problem_247723.lean)

```lean
theorem algebra_247723 (x : ℝ)
    (hx₁ : 0 ≤ 5 * x + 1) (hx₂ : 0 ≤ 4 - x) (hx₃ : 0 ≤ x + 2) (hx₄ : 0 ≤ 61 - 4 * x) :
    √(5 * x + 1) - 2 * √(4 - x) + √5 * √(x + 2) = √(61 - 4 * x) ↔ x = 3 := by
```

### `problem_110877`

Let $a$ be an integer. Show that 5 divides $a^2$ if and only if 5 divides $a$.

[`Numina/problem_110877.lean`](Numina/problem_110877.lean)

```lean
theorem number_theory_110877 (a : ℤ) : 5 ∣ a ^ 2 ↔ 5 ∣ a := by
```

### `problem_221516`

If both solutions of the equations $x^2 + p x + q = 0$ and $x^2 + p x - q = 0$ are integers,
prove that there exist integers $a$ and $b$ such that $p^2 = a^2 + b^2$.

[`Numina/problem_221516.lean`](Numina/problem_221516.lean)

```lean
theorem algebra_221516 {p q : ℝ}
    (h₁ : ∃ x₁ x₂ : ℤ, (X ^ 2 + C p * X + C q : ℝ[X]).roots = {↑x₁, ↑x₂})
    (h₂ : ∃ y₁ y₂ : ℤ, (X ^ 2 + C p * X - C q : ℝ[X]).roots = {↑y₁, ↑y₂}) :
    ∃ a b : ℤ, p ^ 2 = a ^ 2 + b ^ 2 := by
```

### `problem_139053`

Prove that √2, √3 and √5 cannot be terms in an arithmetic progression.

[`Numina/problem_139053.lean`](Numina/problem_139053.lean)

```lean
theorem number_theory_139053 : ¬∃ a d : ℝ,
    (∃ k : ℕ, √2 = a + k * d) ∧ (∃ k : ℕ, √3 = a + k * d) ∧ ∃ k : ℕ, √5 = a + k * d := by
```

### `problem_205729`

Prove the following inequality:

$$ \log _{5} 6 + \log _{6} 7 + \log _{7} 8 + \log _{8} 5 > 4 $$

[`Numina/problem_205729.lean`](Numina/problem_205729.lean)

```lean
theorem inequalities_205729 : logb 5 6 + logb 6 7 + logb 7 8 + logb 8 5 > 4 := by
```


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

<https://artofproblemsolving.com/wiki/index.php/2018_AIME_II_Problems/Problem_3>

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

<https://artofproblemsolving.com/wiki/index.php/2017_AIME_I_Problems/Problem_5>

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

<https://artofproblemsolving.com/wiki/index.php/2007_AIME_I_Problems/Problem_5>

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

<https://artofproblemsolving.com/wiki/index.php/2004_AIME_I_Problems/Problem_5>

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

$$ P(x) = 1 + \cos(x) + i \sin(x) - \cos(2 x) - i \sin(2 x) + \cos(3 x) + i \sin(3 x) $$

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

<https://artofproblemsolving.com/wiki/index.php/2021_Fall_AMC_12B_Problems/Problem_25>

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

<https://artofproblemsolving.com/wiki/index.php/2010_AMC_12B_Problems/Problem_20>

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

<https://artofproblemsolving.com/wiki/index.php/2023_AMC_12A_Problems/Problem_14>

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

<https://artofproblemsolving.com/wiki/index.php/2001_AMC_12_Problems/Problem_25>

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

<https://artofproblemsolving.com/wiki/index.php/2001_AMC_12_Problems/Problem_13>

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

<https://artofproblemsolving.com/wiki/index.php/2011_AMC_12A_Problems/Problem_20>

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

<https://artofproblemsolving.com/wiki/index.php/2000_AMC_12_Problems/Problem_9>

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

<https://artofproblemsolving.com/wiki/index.php/2023_AMC_12A_Problems/Problem_1>

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

