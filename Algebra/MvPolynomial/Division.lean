/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Division
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Finsupp.Weight

/-!
# Division of `MvPolynomial` by monomials

## Main definitions

* `MvPolynomial.divMonomial x s`: divides `x` by the monomial `MvPolynomial.monomial 1 s`
* `MvPolynomial.modMonomial x s`: the remainder upon dividing `x` by the monomial
  `MvPolynomial.monomial 1 s`.

## Main results

* `MvPolynomial.divMonomial_add_modMonomial`, `MvPolynomial.modMonomial_add_divMonomial`:
  `divMonomial` and `modMonomial` are well-behaved as quotient and remainder operators.

## Implementation notes

Where possible, the results in this file should be first proved in the generality of
`AddMonoidAlgebra`, and then the versions specialized to `MvPolynomial` proved in terms of these.

-/

@[expose] public section


variable {σ R : Type*} [CommSemiring R]

namespace MvPolynomial

section CopiedDeclarations

/-! Please ensure the declarations in this section are direct translations of `AddMonoidAlgebra`
results. -/


/--
Definition of `divMonomial` / `divMonomial` 的定义

English:
definition divMonomial
  signature: (p : MvPolynomial σ R) (s : σ ->₀ Nat)
  body: AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

@[simp]

中文:
定义 divMonomial
  签名: (p : MvPolynomial σ R) (s : σ ->₀ 自然数)
  定义体: AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

@[simp]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.divOf
-/
noncomputable def divMonomial (p : MvPolynomial σ R) (s : σ ->₀ Nat) : MvPolynomial σ R :=
  AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

@[simp]
/--
theorem `coeff_divMonomial` / 定理 `coeff_divMonomial`

English:
theorem coeff_divMonomial
  given: (s : σ ->₀ Nat) (x : MvPolynomial σ R) (s' : σ ->₀ Nat)
  proof: rfl

@[simp]

中文:
定理 coeff_divMonomial
  条件: (s : σ ->₀ 自然数) (x : MvPolynomial σ R) (s' : σ ->₀ 自然数)
  证明: rfl

@[simp]
-/
theorem coeff_divMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) (s' : σ ->₀ Nat) :
    coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x :=
  rfl

@[simp]
/--
theorem `support_divMonomial` / 定理 `support_divMonomial`

English:
theorem support_divMonomial
  given: (s : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: rfl

@[simp]

中文:
定理 support_divMonomial
  条件: (s : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: rfl

@[simp]
-/
theorem support_divMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) :
    (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.preimage _ (add_right_injective s).injOn :=
  rfl

@[simp]
/--
theorem `zero_divMonomial` / 定理 `zero_divMonomial`

English:
theorem zero_divMonomial
  given: (s : σ ->₀ Nat)
  statement: (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
  proof: AddMonoidAlgebra.zero_divOf _

中文:
定理 zero_divMonomial
  条件: (s : σ ->₀ 自然数)
  结论: (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
  证明: AddMonoidAlgebra.zero_divOf _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.zero_divOf, zero_divOf
-/
theorem zero_divMonomial (s : σ ->₀ Nat) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.zero_divOf _

/--
theorem `divMonomial_zero` / 定理 `divMonomial_zero`

English:
theorem divMonomial_zero
  given: (x : MvPolynomial σ R)
  statement: x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x
  proof: x.divOf_zero

中文:
定理 divMonomial_zero
  条件: (x : MvPolynomial σ R)
  结论: x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x
  证明: x.divOf_zero

Depends on / 依赖: divOf_zero, x.divOf_zero
-/
theorem divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x :=
  x.divOf_zero

set_option backward.isDefEq.respectTransparency false in
/--
theorem `add_divMonomial` / 定理 `add_divMonomial`

English:
theorem add_divMonomial
  given: (x y : MvPolynomial σ R) (s : σ ->₀ Nat)
  proof: by
  simp [divMonomial, MvPolynomial, AddMonoidAlgebra.add_divOf]

中文:
定理 add_divMonomial
  条件: (x y : MvPolynomial σ R) (s : σ ->₀ 自然数)
  证明: by
  simp [divMonomial, MvPolynomial, AddMonoidAlgebra.add_divOf]

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.add_divOf, MvPolynomial, add_divOf, divMonomial
-/
theorem add_divMonomial (x y : MvPolynomial σ R) (s : σ ->₀ Nat) :
    (x + y) /ᵐᵒⁿᵒᵐⁱᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s := by
  simp [divMonomial, MvPolynomial, AddMonoidAlgebra.add_divOf]

/--
theorem `divMonomial_add` / 定理 `divMonomial_add`

English:
theorem divMonomial_add
  given: (a b : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: x.divOf_add _ _

@[simp]

中文:
定理 divMonomial_add
  条件: (a b : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: x.divOf_add _ _

@[simp]

Depends on / 依赖: divOf_add, x.divOf_add
-/
theorem divMonomial_add (a b : σ ->₀ Nat) (x : MvPolynomial σ R) :
    x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b :=
  x.divOf_add _ _

@[simp]
/--
theorem `divMonomial_monomial_mul` / 定理 `divMonomial_monomial_mul`

English:
theorem divMonomial_monomial_mul
  given: (a : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: x.of'_mul_divOf _

@[simp]

中文:
定理 divMonomial_monomial_mul
  条件: (a : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: x.of'_mul_divOf _

@[simp]

Depends on / 依赖: _mul_divOf, x.of
-/
theorem divMonomial_monomial_mul (a : σ ->₀ Nat) (x : MvPolynomial σ R) :
    monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.of'_mul_divOf _

@[simp]
/--
theorem `divMonomial_mul_monomial` / 定理 `divMonomial_mul_monomial`

English:
theorem divMonomial_mul_monomial
  given: (a : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: x.mul_of'_divOf _

@[simp]

中文:
定理 divMonomial_mul_monomial
  条件: (a : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: x.mul_of'_divOf _

@[simp]

Depends on / 依赖: _divOf, mul_of, x.mul_of
-/
theorem divMonomial_mul_monomial (a : σ ->₀ Nat) (x : MvPolynomial σ R) :
    x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.mul_of'_divOf _

@[simp]
/--
theorem `divMonomial_monomial` / 定理 `divMonomial_monomial`

English:
theorem divMonomial_monomial
  given: (a : σ ->₀ Nat)
  statement: monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R)
  proof: AddMonoidAlgebra.of'_divOf _

中文:
定理 divMonomial_monomial
  条件: (a : σ ->₀ 自然数)
  结论: monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R)
  证明: AddMonoidAlgebra.of'_divOf _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.of, _divOf
-/
theorem divMonomial_monomial (a : σ ->₀ Nat) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R) :=
  AddMonoidAlgebra.of'_divOf _

/--
Definition of `modMonomial` / `modMonomial` 的定义

English:
definition modMonomial
  signature: (x : MvPolynomial σ R) (s : σ ->₀ Nat)
  body: x.modOf s

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]

中文:
定义 modMonomial
  签名: (x : MvPolynomial σ R) (s : σ ->₀ 自然数)
  定义体: x.modOf s

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]

Depends on / 依赖: x.modOf
-/
noncomputable def modMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) : MvPolynomial σ R :=
  x.modOf s

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
/--
theorem `coeff_modMonomial_of_not_le` / 定理 `coeff_modMonomial_of_not_le`

English:
theorem coeff_modMonomial_of_not_le
  given: {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h : ¬s <= s')
  proof: x.coeff_modOf_of_not_exists_add s s' by rintro ⟨d, rfl⟩; exact h le_self_add

@[simp]

中文:
定理 coeff_modMonomial_of_not_le
  条件: {s' s : σ ->₀ 自然数} (x : MvPolynomial σ R) (h : ¬s <= s')
  证明: x.coeff_modOf_of_not_exists_add s s' by rintro ⟨d, rfl⟩; exact h le_self_add

@[simp]

Depends on / 依赖: coeff_modOf_of_not_exists_add, le_self_add, x.coeff_modOf_of_not_exists_add
-/
theorem coeff_modMonomial_of_not_le {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h : ¬s <= s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x :=
x.coeff_modOf_of_not_exists_add s s' by rintro ⟨d, rfl⟩; exact h le_self_add

@[simp]
/--
theorem `coeff_modMonomial_of_le` / 定理 `coeff_modMonomial_of_le`

English:
theorem coeff_modMonomial_of_le
  given: {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h : s <= s')
  proof: x.coeff_modOf_of_exists_add _ _ exists_add_of_le h

@[simp]

中文:
定理 coeff_modMonomial_of_le
  条件: {s' s : σ ->₀ 自然数} (x : MvPolynomial σ R) (h : s <= s')
  证明: x.coeff_modOf_of_exists_add _ _ exists_add_of_le h

@[simp]

Depends on / 依赖: coeff_modOf_of_exists_add, exists_add_of_le, x.coeff_modOf_of_exists_add
-/
theorem coeff_modMonomial_of_le {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h : s <= s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 :=
x.coeff_modOf_of_exists_add _ _ exists_add_of_le h

@[simp]
/--
theorem `monomial_mul_modMonomial` / 定理 `monomial_mul_modMonomial`

English:
theorem monomial_mul_modMonomial
  given: (s : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: x.of'_mul_modOf _

@[simp]

中文:
定理 monomial_mul_modMonomial
  条件: (s : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: x.of'_mul_modOf _

@[simp]

Depends on / 依赖: _mul_modOf, x.of
-/
theorem monomial_mul_modMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) :
    monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.of'_mul_modOf _

@[simp]
/--
theorem `mul_monomial_modMonomial` / 定理 `mul_monomial_modMonomial`

English:
theorem mul_monomial_modMonomial
  given: (s : σ ->₀ Nat) (x : MvPolynomial σ R)
  proof: x.mul_of'_modOf _

@[simp]

中文:
定理 mul_monomial_modMonomial
  条件: (s : σ ->₀ 自然数) (x : MvPolynomial σ R)
  证明: x.mul_of'_modOf _

@[simp]

Depends on / 依赖: _modOf, mul_of, x.mul_of
-/
theorem mul_monomial_modMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) :
    x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.mul_of'_modOf _

@[simp]
/--
theorem `monomial_modMonomial` / 定理 `monomial_modMonomial`

English:
theorem monomial_modMonomial
  given: (s : σ ->₀ Nat)
  statement: monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
  proof: AddMonoidAlgebra.of'_modOf _

中文:
定理 monomial_modMonomial
  条件: (s : σ ->₀ 自然数)
  结论: monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
  证明: AddMonoidAlgebra.of'_modOf _

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.of, _modOf
-/
theorem monomial_modMonomial (s : σ ->₀ Nat) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.of'_modOf _

/--
theorem `divMonomial_add_modMonomial` / 定理 `divMonomial_add_modMonomial`

English:
theorem divMonomial_add_modMonomial
  given: (x : MvPolynomial σ R) (s : σ ->₀ Nat)
  proof: AddMonoidAlgebra.divOf_add_modOf x s

中文:
定理 divMonomial_add_modMonomial
  条件: (x : MvPolynomial σ R) (s : σ ->₀ 自然数)
  证明: AddMonoidAlgebra.divOf_add_modOf x s

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.divOf_add_modOf, divOf_add_modOf
-/
theorem divMonomial_add_modMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) :
    monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x :=
  AddMonoidAlgebra.divOf_add_modOf x s

/--
theorem `modMonomial_add_divMonomial` / 定理 `modMonomial_add_divMonomial`

English:
theorem modMonomial_add_divMonomial
  given: (x : MvPolynomial σ R) (s : σ ->₀ Nat)
  proof: AddMonoidAlgebra.modOf_add_divOf x s

中文:
定理 modMonomial_add_divMonomial
  条件: (x : MvPolynomial σ R) (s : σ ->₀ 自然数)
  证明: AddMonoidAlgebra.modOf_add_divOf x s

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.modOf_add_divOf, modOf_add_divOf
-/
theorem modMonomial_add_divMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x :=
  AddMonoidAlgebra.modOf_add_divOf x s

/--
theorem `monomial_one_dvd_iff_modMonomial_eq_zero` / 定理 `monomial_one_dvd_iff_modMonomial_eq_zero`

English:
theorem monomial_one_dvd_iff_modMonomial_eq_zero
  given: {i : σ ->₀ Nat} {x : MvPolynomial σ R}
  proof: AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

中文:
定理 monomial_one_dvd_iff_modMonomial_eq_zero
  条件: {i : σ ->₀ 自然数} {x : MvPolynomial σ R}
  证明: AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

Depends on / 依赖: AddMonoidAlgebra, AddMonoidAlgebra.of, _dvd_iff_modOf_eq_zero
-/
theorem monomial_one_dvd_iff_modMonomial_eq_zero {i : σ ->₀ Nat} {x : MvPolynomial σ R} :
    monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0 :=
  AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

end CopiedDeclarations

section XLemmas

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
/--
theorem `X_mul_divMonomial` / 定理 `X_mul_divMonomial`

English:
theorem X_mul_divMonomial
  given: (i : σ) (x : MvPolynomial σ R)
  proof: divMonomial_monomial_mul _ _

@[simp]

中文:
定理 X_mul_divMonomial
  条件: (i : σ) (x : MvPolynomial σ R)
  证明: divMonomial_monomial_mul _ _

@[simp]

Depends on / 依赖: divMonomial_monomial_mul
-/
theorem X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_monomial_mul _ _

@[simp]
/--
theorem `X_divMonomial` / 定理 `X_divMonomial`

English:
theorem X_divMonomial
  given: (i : σ)
  statement: (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1
  proof: divMonomial_monomial (Finsupp.single i 1)

@[simp]

中文:
定理 X_divMonomial
  条件: (i : σ)
  结论: (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1
  证明: divMonomial_monomial (Finsupp.single i 1)

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single, divMonomial_monomial, single
-/
theorem X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1 :=
  divMonomial_monomial (Finsupp.single i 1)

@[simp]
/--
theorem `mul_X_divMonomial` / 定理 `mul_X_divMonomial`

English:
theorem mul_X_divMonomial
  given: (x : MvPolynomial σ R) (i : σ)
  proof: divMonomial_mul_monomial _ _

@[simp]

中文:
定理 mul_X_divMonomial
  条件: (x : MvPolynomial σ R) (i : σ)
  证明: divMonomial_mul_monomial _ _

@[simp]

Depends on / 依赖: divMonomial_mul_monomial
-/
theorem mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_mul_monomial _ _

@[simp]
/--
theorem `X_mul_modMonomial` / 定理 `X_mul_modMonomial`

English:
theorem X_mul_modMonomial
  given: (i : σ) (x : MvPolynomial σ R)
  proof: monomial_mul_modMonomial _ _

@[simp]

中文:
定理 X_mul_modMonomial
  条件: (i : σ) (x : MvPolynomial σ R)
  证明: monomial_mul_modMonomial _ _

@[simp]

Depends on / 依赖: monomial_mul_modMonomial
-/
theorem X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_mul_modMonomial _ _

@[simp]
/--
theorem `mul_X_modMonomial` / 定理 `mul_X_modMonomial`

English:
theorem mul_X_modMonomial
  given: (x : MvPolynomial σ R) (i : σ)
  proof: mul_monomial_modMonomial _ _

@[simp]

中文:
定理 mul_X_modMonomial
  条件: (x : MvPolynomial σ R) (i : σ)
  证明: mul_monomial_modMonomial _ _

@[simp]

Depends on / 依赖: mul_monomial_modMonomial
-/
theorem mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  mul_monomial_modMonomial _ _

@[simp]
/--
theorem `modMonomial_X` / 定理 `modMonomial_X`

English:
theorem modMonomial_X
  given: (i : σ)
  statement: (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0
  proof: monomial_modMonomial _

中文:
定理 modMonomial_X
  条件: (i : σ)
  结论: (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0
  证明: monomial_modMonomial _

Depends on / 依赖: monomial_modMonomial
-/
theorem modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_modMonomial _

/--
theorem `divMonomial_add_modMonomial_single` / 定理 `divMonomial_add_modMonomial_single`

English:
theorem divMonomial_add_modMonomial_single
  given: (x : MvPolynomial σ R) (i : σ)
  proof: divMonomial_add_modMonomial _ _

中文:
定理 divMonomial_add_modMonomial_single
  条件: (x : MvPolynomial σ R) (i : σ)
  证明: divMonomial_add_modMonomial _ _

Depends on / 依赖: divMonomial_add_modMonomial
-/
theorem divMonomial_add_modMonomial_single (x : MvPolynomial σ R) (i : σ) :
    X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_add_modMonomial _ _

/--
theorem `modMonomial_add_divMonomial_single` / 定理 `modMonomial_add_divMonomial_single`

English:
theorem modMonomial_add_divMonomial_single
  given: (x : MvPolynomial σ R) (i : σ)
  proof: modMonomial_add_divMonomial _ _

中文:
定理 modMonomial_add_divMonomial_single
  条件: (x : MvPolynomial σ R) (i : σ)
  证明: modMonomial_add_divMonomial _ _

Depends on / 依赖: modMonomial_add_divMonomial
-/
theorem modMonomial_add_divMonomial_single (x : MvPolynomial σ R) (i : σ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) = x :=
  modMonomial_add_divMonomial _ _

/--
theorem `X_dvd_iff_modMonomial_eq_zero` / 定理 `X_dvd_iff_modMonomial_eq_zero`

English:
theorem X_dvd_iff_modMonomial_eq_zero
  given: {i : σ} {x : MvPolynomial σ R}
  proof: monomial_one_dvd_iff_modMonomial_eq_zero

中文:
定理 X_dvd_iff_modMonomial_eq_zero
  条件: {i : σ} {x : MvPolynomial σ R}
  证明: monomial_one_dvd_iff_modMonomial_eq_zero

Depends on / 依赖: monomial_one_dvd_iff_modMonomial_eq_zero
-/
theorem X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} :
    X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_one_dvd_iff_modMonomial_eq_zero

end XLemmas



/--
theorem `monomial_dvd_monomial` / 定理 `monomial_dvd_monomial`

English:
theorem monomial_dvd_monomial
  given: {r s : R} {i j : σ ->₀ Nat}
  proof: by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx
    have hj := hx j
    have hi := hx i
    classical
    simp_rw [coeff_monomial, if_pos] at hj hi
    simp_rw [coeff_monomial_mul'] at hi hj
    split_ifs at hj with hi
    · exact ⟨Or.inr hi, _, hj⟩
    · exact ⟨Or.inl hj, hj

中文:
定理 monomial_dvd_monomial
  条件: {r s : R} {i j : σ ->₀ 自然数}
  证明: by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx
    have hj := hx j
    have hi := hx i
    classical
    simp_rw [coeff_monomial, if_pos] at hj hi
    simp_rw [coeff_monomial_mul'] at hi hj
    split_ifs at hj with hi
    · exact ⟨Or.inr hi, _, hj⟩
    · exact ⟨Or.inl hj, hj

Depends on / 依赖: MvPolynomial, MvPolynomial.ext_iff, Or.inl, Or.inr, add_tsub_cancel_of_le, classical, coeff_monomial, coeff_monomial_mul, dvd_zero, ext_iff, hj.symm, if_pos, monomial, monomial_mul, monomial_zero, simp_rw, split_ifs
-/
theorem monomial_dvd_monomial {r s : R} {i j : σ ->₀ Nat} :
    monomial i r ∣ monomial j s ↔ (s = 0 ∨ i <= j) ∧ r ∣ s := by
  constructor
  · rintro ⟨x, hx⟩
    rw [MvPolynomial.ext_iff] at hx
    have hj := hx j
    have hi := hx i
    classical
    simp_rw [coeff_monomial, if_pos] at hj hi
    simp_rw [coeff_monomial_mul'] at hi hj
    split_ifs at hj with hi
    · exact ⟨Or.inr hi, _, hj⟩
    · exact ⟨Or.inl hj, hj.symm ▸ dvd_zero _⟩
  · rintro ⟨h | hij, d, rfl⟩
    · simp_rw [h, monomial_zero, dvd_zero]
    · refine ⟨monomial (j - i) d, ?_⟩
      rw [monomial_mul]; rw [add_tsub_cancel_of_le hij]

@[simp]
/--
theorem `monomial_one_dvd_monomial_one` / 定理 `monomial_one_dvd_monomial_one`

English:
theorem monomial_one_dvd_monomial_one
  given: [Nontrivial R] {i j : σ ->₀ Nat}
  proof: by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

@[simp]

中文:
定理 monomial_one_dvd_monomial_one
  条件: [Nontrivial R] {i j : σ ->₀ 自然数}
  证明: by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

@[simp]

Depends on / 依赖: and_true, dvd_rfl, false_or, monomial_dvd_monomial, one_ne_zero, simp_rw
-/
theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ ->₀ Nat} :
    monomial i (1 : R) ∣ monomial j 1 ↔ i <= j := by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

@[simp]
/--
theorem `X_dvd_X` / 定理 `X_dvd_X`

English:
theorem X_dvd_X
  given: [Nontrivial R] {i j : σ}
  proof: by
  refine monomial_one_dvd_monomial_one.trans ?_
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero,
    ne_eq, reduceCtorEq, not_false_eq_true, and_true]

@[simp]

中文:
定理 X_dvd_X
  条件: [Nontrivial R] {i j : σ}
  证明: by
  refine monomial_one_dvd_monomial_one.trans ?_
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero,
    ne_eq, reduceCtorEq, not_false_eq_true, and_true]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply_ne_zero, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, and_true, monomial_one_dvd_monomial_one, monomial_one_dvd_monomial_one.trans, ne_eq, not_false_eq_true, one_le_iff_ne_zero, reduceCtorEq, simp_rw, single_apply_ne_zero, single_le_iff
-/
theorem X_dvd_X [Nontrivial R] {i j : σ} :
    (X i : MvPolynomial σ R) ∣ (X j : MvPolynomial σ R) ↔ i = j := by
  refine monomial_one_dvd_monomial_one.trans ?_
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero,
    ne_eq, reduceCtorEq, not_false_eq_true, and_true]

@[simp]
/--
theorem `X_dvd_monomial` / 定理 `X_dvd_monomial`

English:
theorem X_dvd_monomial
  given: {i : σ} {j : σ ->₀ Nat} {r : R}
  proof: by
  refine monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

中文:
定理 X_dvd_monomial
  条件: {i : σ} {j : σ ->₀ 自然数} {r : R}
  证明: by
  refine monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

Depends on / 依赖: Finsupp, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, and_true, monomial_dvd_monomial, monomial_dvd_monomial.trans, one_dvd, one_le_iff_ne_zero, simp_rw, single_le_iff
-/
theorem X_dvd_monomial {i : σ} {j : σ ->₀ Nat} {r : R} :
    (X i : MvPolynomial σ R) ∣ monomial j r ↔ r = 0 ∨ j i != 0 := by
  refine monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]

/--
theorem `eq_divMonomial_single` / 定理 `eq_divMonomial_single`

English:
theorem eq_divMonomial_single
  statement: [IsLeftCancelAdd R]
  proof: by
  ext n
  rw [coeff_divMonomial]; rw [h]; rw [coeff_add]; rw [coeff_X_mul]; rw [left_eq_add]; rw [← notMem_support_iff]
  intro hn
  simpa using hr _ hn

中文:
定理 eq_divMonomial_single
  结论: [IsLeftCancelAdd R]
  证明: by
  ext n
  rw [coeff_divMonomial]; rw [h]; rw [coeff_add]; rw [coeff_X_mul]; rw [left_eq_add]; rw [← notMem_support_iff]
  intro hn
  simpa using hr _ hn

Depends on / 依赖: coeff_X_mul, coeff_add, coeff_divMonomial, left_eq_add, notMem_support_iff
-/
theorem eq_divMonomial_single [IsLeftCancelAdd R]
    {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r)
    (hr : forall n in r.support, n i = 0) :
    q = p.divMonomial (Finsupp.single i 1) := by
  ext n
  rw [coeff_divMonomial]; rw [h]; rw [coeff_add]; rw [coeff_X_mul]; rw [left_eq_add]; rw [← notMem_support_iff]
  intro hn
  simpa using hr _ hn

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsLeftCancelAdd
  signature: R] :
  body: by
  suffices IsLeftCancelAdd (MvPolynomial σ R) from
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
  refine { add_left_cancel := fun f g h H => ?_ }
  ext d
  simpa using congr_arg (coeff d) H

中文:
实例 [IsLeftCancelAdd
  签名: R] :
  定义体: by
  suffices IsLeftCancelAdd (MvPolynomial σ R) from
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
  refine { add_left_cancel := fun f g h H => ?_ }
  ext d
  simpa using congr_arg (coeff d) H

Depends on / 依赖: AddCommMagma, AddCommMagma.IsLeftCancelAdd.toIsCancelAdd, IsLeftCancelAdd, MvPolynomial, add_left_cancel, congr_arg, toIsCancelAdd
-/
instance [IsLeftCancelAdd R] :
    IsCancelAdd (MvPolynomial σ R) := by
  suffices IsLeftCancelAdd (MvPolynomial σ R) from
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
  refine { add_left_cancel := fun f g h H => ?_ }
  ext d
  simpa using congr_arg (coeff d) H

/--
theorem `eq_modMonomial_single` / 定理 `eq_modMonomial_single`

English:
theorem eq_modMonomial_single
  statement: [IsLeftCancelAdd R]
  proof: by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

中文:
定理 eq_modMonomial_single
  结论: [IsLeftCancelAdd R]
  证明: by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

Depends on / 依赖: add_right_inj, divMonomial_add_modMonomial_single, eq_comm, eq_divMonomial_single, p.divMonomial_add_modMonomial_single
-/
theorem eq_modMonomial_single [IsLeftCancelAdd R]
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : p = X i * q + r) (hr : forall n in r.support, n i = 0) :
    r = p.modMonomial (Finsupp.single i 1) := by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

section CommRing

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

/--
theorem `eq_modMonomial_single_iff` / 定理 `eq_modMonomial_single_iff`

English:
theorem eq_modMonomial_single_iff
  given: (h : X i ∣ p - r)
  proof: by
  refine ⟨fun h n => ?_, fun hr => ?_⟩
  · contrapose!
    intro hn
    rw [h]; rw [notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]

中文:
定理 eq_modMonomial_single_iff
  条件: (h : X i ∣ p - r)
  证明: by
  refine ⟨fun h n => ?_, fun hr => ?_⟩
  · contrapose!
    intro hn
    rw [h]; rw [notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]

Depends on / 依赖: Nat.one_le_iff_ne_zero, coeff_modMonomial_of_le, contrapose, eq_modMonomial_single, notMem_support_iff, one_le_iff_ne_zero, sub_eq_iff_eq_add
-/
theorem eq_modMonomial_single_iff (h : X i ∣ p - r) :
    r = p.modMonomial (Finsupp.single i 1) ↔
      forall n in r.support, n i = 0 := by
  refine ⟨fun h n => ?_, fun hr => ?_⟩
  · contrapose!
    intro hn
    rw [h]; rw [notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]

/--
theorem `X_dvd_mul_iff` / 定理 `X_dvd_mul_iff`

English:
theorem X_dvd_mul_iff
  given: [IsCancelMulZero R]
  proof: by
  nontriviality R
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := p.m

中文:
定理 X_dvd_mul_iff
  条件: [IsCancelMulZero R]
  证明: by
  nontriviality R
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := p.m

Depends on / 依赖: Finset, Finset.sum_eq_zero, Finsupp, Finsupp.single, X_dvd_iff_modMonomial_eq_zero, classical, coeff_mul, contrapose, eq_modMonomial_single_iff, modMonomial, modMonomial_add_divMonomial_single, mul_eq_zero, nontriviality, notMem_support_iff, p.modMonomial, p.modMonomial_add_divMonomial_single, q.modMonomial, q.modMonomial_add_divMonomial_single, single, sum_eq_zero
-/
theorem X_dvd_mul_iff [IsCancelMulZero R] :
    X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q := by
  nontriviality R
  constructor
  · intro h
    suffices (p.modMonomial (Finsupp.single i 1)) * (q.modMonomial (Finsupp.single i 1)) =
          (p * q).modMonomial (Finsupp.single i 1) by
      simp only [X_dvd_iff_modMonomial_eq_zero] at h ⊢
      rwa [h, mul_eq_zero] at this
    have hp := p.modMonomial_add_divMonomial_single i
    have hq := q.modMonomial_add_divMonomial_single i
    rw [eq_modMonomial_single_iff]
    · intro n
      contrapose
      intro hn
      classical
      rw [notMem_support_iff]; rw [coeff_mul]
      apply Finset.sum_eq_zero
      intro x hx
      simp only [Finset.mem_antidiagonal] at hx
      simp only [← hx, Finsupp.coe_add, Pi.add_apply, Nat.add_eq_zero_iff, not_and_or] at hn
      rcases hn with hn | hn
      · rw [coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
      · rw [mul_comm, coeff_modMonomial_of_le, zero_mul]
        simpa [← Nat.one_le_iff_ne_zero] using hn
    · nth_rewrite 1 [← hp]
      nth_rewrite 1 [← hq]
      simp only [add_mul, mul_add, add_assoc, add_sub_cancel_left]
      simp only [← mul_assoc, mul_comm _ (X i)]
      simp only [mul_assoc, ← mul_add (X i)]
      apply dvd_mul_right
  · rintro (h | h)
    · exact dvd_mul_of_dvd_left h q
    · exact dvd_mul_of_dvd_right h p

/--
theorem `X_prime` / 定理 `X_prime`

English:
theorem X_prime
  given: [IsCancelMulZero R] [Nontrivial R]
  statement: Prime (X i : MvPolynomial σ R)
  proof: by
  refine ⟨X_ne_zero i, ?_, fun p q => X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu

中文:
定理 X_prime
  条件: [IsCancelMulZero R] [Nontrivial R]
  结论: Prime (X i : MvPolynomial σ R)
  证明: by
  refine ⟨X_ne_zero i, ?_, fun p q => X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu

Depends on / 依赖: X_dvd_mul_iff, X_dvd_mul_iff.mp, X_ne_zero, apply_fun, constantCoeff, isUnit_iff_exists
-/
theorem X_prime [IsCancelMulZero R] [Nontrivial R] : Prime (X i : MvPolynomial σ R) := by
  refine ⟨X_ne_zero i, ?_, fun p q => X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu

/--
theorem `dvd_X_mul_iff` / 定理 `dvd_X_mul_iff`

English:
theorem dvd_X_mul_iff
  given: [IsCancelMulZero R]
  proof: by
  constructor
  · rintro ⟨r, hp⟩
    have : X i ∣ p ∨ X i ∣ r := by simp [← X_dvd_mul_iff, ← hp]
    apply this.symm.imp
    · rintro ⟨r, rfl⟩
      obtain rfl : q = p * r := by rw [← X_mul_cancel_left_iff (i := i), hp, mul_left_comm]
      exact dvd_mul_right p r
    · intro hip
      refine ⟨hi

中文:
定理 dvd_X_mul_iff
  条件: [IsCancelMulZero R]
  证明: by
  constructor
  · rintro ⟨r, hp⟩
    have : X i ∣ p ∨ X i ∣ r := by simp [← X_dvd_mul_iff, ← hp]
    apply this.symm.imp
    · rintro ⟨r, rfl⟩
      obtain rfl : q = p * r := by rw [← X_mul_cancel_left_iff (i := i), hp, mul_left_comm]
      exact dvd_mul_right p r
    · intro hip
      refine ⟨hi

Depends on / 依赖: X_dvd_iff_modMonomial_eq_zero, X_dvd_mul_iff, X_mul_cancel_left_iff, dvd_mul_of_dvd_right, dvd_mul_right, modMonomial_add_divMonomial_single, mul_assoc, mul_left_comm, p.modMonomial_add_divMonomial_single, this.symm.imp, zero_add
-/
theorem dvd_X_mul_iff [IsCancelMulZero R] :
    p ∣ X i * q ↔ p ∣ q ∨ (X i ∣ p ∧ p.divMonomial (Finsupp.single i 1) ∣ q) := by
  constructor
  · rintro ⟨r, hp⟩
    have : X i ∣ p ∨ X i ∣ r := by simp [← X_dvd_mul_iff, ← hp]
    apply this.symm.imp
    · rintro ⟨r, rfl⟩
      obtain rfl : q = p * r := by rw [← X_mul_cancel_left_iff (i := i), hp, mul_left_comm]
      exact dvd_mul_right p r
    · intro hip
      refine ⟨hip, ?_⟩
      rw [X_dvd_iff_modMonomial_eq_zero] at hip
      rw [← p.modMonomial_add_divMonomial_single i]; rw [hip]; rw [zero_add]; rw [mul_assoc]; rw [X_mul_cancel_left_iff] at hp
      use r
  · rintro (hp | ⟨hi, hq⟩)
    · exact dvd_mul_of_dvd_right hp (X i)
    · suffices p = X i * p.divMonomial (Finsupp.single i 1) by
        rw [this]
        exact mul_dvd_mul_left (X i) hq
      conv_lhs => rw [← p.modMonomial_add_divMonomial (Finsupp.single i 1)]
      simpa only [← C_mul_X_eq_monomial, C_1, one_mul, add_eq_right,
        ← X_dvd_iff_modMonomial_eq_zero]

/--
theorem `dvd_monomial_mul_iff_exists` / 定理 `dvd_monomial_mul_iff_exists`

English:
theorem dvd_monomial_mul_iff_exists
  given: [IsCancelMulZero R] {n : σ ->₀ Nat}
  proof: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices forall (d) (n : σ ->₀ Nat) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ exists m r, m <= 

中文:
定理 dvd_monomial_mul_iff_exists
  条件: [IsCancelMulZero R] {n : σ ->₀ 自然数}
  证明: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices forall (d) (n : σ ->₀ Nat) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ exists m r, m <= 

Depends on / 依赖: Finsupp, Finsupp.degree_eq_zero_iff, MvPolynomial, Subsingleton, Subsingleton.elim, and_self, and_true, degree, degree_eq_zero_iff, dvd_refl, exists_const, le_refl, monomial, monomial_zero, n.degree, nonpos_iff_eq_zero, one_mul, subsingleton_or_nontrivial, true_iff
-/
theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ ->₀ Nat} :
    p ∣ monomial n 1 * q ↔ exists m r, m <= n ∧ r ∣ q ∧ p = monomial m 1 * r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices forall (d) (n : σ ->₀ Nat) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ exists m r, m <= n ∧ r ∣ q ∧ p = monomial m 1 * r from this n.degree n rfl p q
  intro d
  induction d with
  | zero =>
    intro n hn p
    rw [Finsupp.degree_eq_zero_iff] at hn
    simp only [hn, monomial_zero', C_1, one_mul, nonpos_iff_eq_zero, exists_and_left,
      exists_eq_left, exists_eq_right', implies_true]
  | succ d hd =>
    intro n hn p q
    refine ⟨fun hp => ?_, fun ⟨m, r, hmn, hrq, hp⟩ => ?_⟩
    · obtain ⟨i, hi⟩ : n.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro hn'
        simp [hn'] at hn
      let n' := n - Finsupp.single i 1
      have hn' : n' + Finsupp.single i 1 = n := by
        apply Finsupp.sub_add_single_one_cancel
        rwa [← Finsupp.mem_support_iff]
      have hnn' : n' <= n := by simp [← hn']
      have hd' : n'.degree = d := by
        rw [← add_left_inj]; rw [← hn]; rw [← hn']
        simp
      rw [← hn']; rw [monomial_add_single]; rw [pow_one]; rw [mul_comm _ (X i)]; rw [mul_assoc]; rw [dvd_X_mul_iff] at hp
      rcases hp with hp | hp
      · obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' p q).mp hp
        exact ⟨m, r, le_trans hm hnn', hr, hp⟩
      · obtain ⟨p', rfl⟩ := hp.1
        obtain ⟨m, r, hm, hr, hp⟩ := (hd n' hd' _ _).mp hp.2
        use m + Finsupp.single i 1, r, ?_, hr
        · simp [monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, ← hp]
        · simpa [← hn'] using hm
    · rw [hp, ← add_tsub_cancel_of_le hmn, ← mul_one 1, ← monomial_mul, mul_one, mul_assoc]
      apply mul_dvd_mul dvd_rfl
      apply dvd_mul_of_dvd_right hrq

end CommRing

end MvPolynomial
