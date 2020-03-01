-- Math 52: Quiz 5
-- Open this file in a folder that contains 'utils'.

import utils

definition divides (a b : ℤ) : Prop := ∃ (k : ℤ), b = a * k
local infix ∣ := divides

axiom not_3_divides : ∀ (m : ℤ), ¬ (3 ∣ m) ↔ 3 ∣ m - 1 ∨ 3 ∣ m + 1

theorem main : ∀ (n : ℤ), ¬ (3 ∣ n) → 3 ∣ n * n - 1 :=
begin
intro n,
rw not_3_divides,
intro H,
cases H,

    {unfold divides at H ⊢,
    cases H with a H,
    existsi(a*(n+1):ℤ ),
    rw int.distrib_left,
    rw int.distrib_left,
    rw mul_one,
    symmetry,
    calc 3 * (a * n) + 3 * a
    = 3*a*n + 3*a :by int_refl[a,n]...
    = 3*a*(n+1): by int_refl[a,n]...
    = (n-1)*(n+1): by rw H...
    = n*n - 1: by int_refl[n],
    },

    {unfold divides at H ⊢,
    cases H with a H,
    existsi(a*(n-1):ℤ ),
    --it didn't like it when I copied and pasted lines 21-
    --23 here, so I'm trying something different
    symmetry,
    calc 3 * (a * (n-1)) 
    = 3*a* (n - 1) :by int_refl[a,n]...
    = (n+1) * (n-1) :by rw H ...
    = n*n - 1 : by int_refl[n],
    },

end

--Proof: Let n be an artibrary integer. By the lemma,
--3 does not divide n is logically equivalent to the
--statement that either 3 divides n-1 or 3 divides n+1.
--Assume that either 3 divides n-1 or 3 divides n+1. The
--goal is now to show that 3 divides n*n - 1. We consider
--two cases:

--First, the case that 3 divides n-1. By the definition
--of divides, there exists some integer a for which
--n-1=3*a, and we want to show that there exists some
--integer k such that n*n-1 = 3k. Consider k = a(n+1).
--By closure under subtraction and multiplication, k
--must be an integer. Also, 3*k=3*a*(n+1)=(n-1)(n+1)
--  =n*n-1.

--Second, the case that 3 divides n+1. By the definition
--of divides, there exists some integer a for which
--n+1=3*a, and we want to show that there exists some
--integer k such that n*n-1 = 3k. Consider k = a(n-1).
--By closure under subtraction and multiplication, k
--must be an integer. Also, 3*k=3*a*(n-1)=(n-1)(n+1)
--  =n*n-1.

--Since both cases lead us to the conclusion that 3
--divides n*n-1, it is proven that, if 3 does not
--divide n, then 3 divides n*n-1. □ 