-- https://cloud.kili-technology.com/label/projects/label/cm7enil0200sfzz87bml2zpcj

import Mathlib

/- Cities A and B are 45 miles apart.
Alicia lives in A and Beth lives in B.
Alicia bikes towards B at 18 miles per hour.
Leaving at the same time, Beth bikes toward A at 12 miles per hour.
How many miles from City A will they be when they meet?
(A) 20
(B) 24
(C) 25
(D) 26
(E) 27 -/

theorem algebra_65302 {d v1 v2 : ℝ} (hd : d = 45) (hv1 : v1 = 18) (hv2 : v2 = 12) {x t : ℝ}
    (h1 : x = v1 * t) (h2 : x = d - v2 * t) : x = 27 := by
  nlinarith
