-- https://cloud.kili-technology.com/label/projects/label/cm8cszy9501pt5kayihf5tlgt

import Mathlib

open Real

/- Prove: For any real numbers $a_{1}, a_{2}, \cdots, a_{1987}$ and any positive numbers
$b_{1}, b_{2}, \cdots, b_{1987}$, we have
$$
\frac{\left(a_{1}+a_{2}+\cdots+a_{1987}\right)^{2}}{b_{1}+b_{2}+\cdots+b_{1987}} \leqslant
  \frac{a_{1}^{2}}{b_{1}}+\frac{a_{2}^{2}}{b_{2}}+\cdots+\frac{a_{1987}^{2}}{b_{1987}} .
$$
 -/

theorem inequalities_200534 (a b : Fin 1987 → ℝ) (hb : ∀ i, 0 < b i) :
    (∑ i, a i) ^ 2 / ∑ i, b i ≤ ∑ i, a i ^ 2 / b i :=
  Finset.univ.sq_sum_div_le_sum_sq_div a fun i _ ↦ hb i
