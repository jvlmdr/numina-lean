# Problems

### `AMC_95071`

[`Numina/AMC_95071.lean`](Numina/AMC_95071.lean)

The parabola with equation $p(x) = a x^2 + b x + c$ and vertex $(h, k)$
is reflected about the line $y = k$.
This results in the parabola with equation $q(x) = d x^2 + e x + f$.
Which of the following equals $a + b + c + d + e + f$?
(A) $2 b$
(B) $2 c$
(C) $2 a + 2 b$
(D) $2 h$
(E) $2 k$

```lean
theorem algebra_95071 {a b c d e f k : ℝ} {p q : ℝ → ℝ}
    (hp : ∀ x, p x = a * x ^ 2 + b * x + c) (hq : ∀ x, q x = d * x ^ 2 + e * x + f)
    (hpq : ∀ x, q x - k = -(p x - k)) :
    a + b + c + d + e + f = 2 * k := by
```

### `AMC_94615`

[`Numina/AMC_94615.lean`](Numina/AMC_94615.lean)

Let $f(x) = a * x^2 + b * x + c$ where $a, b, c$ are integers.
Suppose that $f(1) = 0$, $50 < f(7) < 60$, $70 < f(8) < 80$,
and $5000 k < f(100) < 5000 (k + 1)$ for some integer $k$.
What is $k$?
(A) 1
(B) 2
(C) 3
(D) 4
(E) 5

```lean
theorem algebra_94615 (a b c : ℤ) (f : ℤ → ℤ) (hf : ∀ x, f x = a * x ^ 2 + b * x + c)
    (h1 : f 1 = 0) (h2 : f 7 ∈ Set.Ioo 50 60) (h3 : f 8 ∈ Set.Ioo 70 80)
    {k : ℤ} (h4 : f 100 ∈ Set.Ioo (5000 * k) (5000 * (k + 1))) :
    k = 3 := by
```

### `AMC_93411`

[`Numina/AMC_93411.lean`](Numina/AMC_93411.lean)

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

```lean
theorem number_theory_93411 (a b c d e : ℕ) (h : [a, b, c, d, e] ~ [71, 76, 80, 82, 91])
    (h2 : 2 ∣ d + e) (h3 : 3 ∣ c + d + e) (h4 : 4 ∣ b + c + d + e) : a = 80 := by
```

### `AMC_65302`

[`Numina/AMC_65302.lean`](Numina/AMC_65302.lean)

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

```lean
theorem algebra_65302 {d v1 v2 : ℝ} (hd : d = 45) (hv1 : v1 = 18) (hv2 : v2 = 12) {x t : ℝ}
    (h1 : x = v1 * t) (h2 : x = d - v2 * t) : x = 27 := by
```

