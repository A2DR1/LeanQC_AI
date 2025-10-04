import Generated._Header

/-- For all real x, (x + 1)^2 = x^2 + 2x + 1. -/
theorem P1_binomial (x : ℝ) :
    (x + 1) ^ 2 = x ^ 2 + 2 * x + 1 := by
  ring
