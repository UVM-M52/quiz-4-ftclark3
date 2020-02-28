-- Math 52: Quiz 5
-- Open this file in a folder that contains 'utils'.

import utils

definition divides (a b : ℤ) : Prop := ∃ (k : ℤ), b = a * k
local infix ∣ := divides

axiom not_3_divides : ∀ (m : ℤ), ¬ (3 ∣ m) ↔ 3 ∣ m - 1 ∨ 3 ∣ m + 1

theorem main : ∀ (n : ℤ), ¬ (3 ∣ n) → 3 ∣ n * n - 1 :=
begin
sorry
end
