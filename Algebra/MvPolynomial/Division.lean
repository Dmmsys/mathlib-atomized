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


/-- Divide by `monomial 1 s`, discarding terms not divisible by this. -/
/-
**MvPolynomial.divMonomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：divMonomial (p : MvPolynomial σ R) (s : σ ->₀ Nat) : MvPolynomial σ R
参数：p : MvPolynomial σ R；s : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divide by `monomial 1 s`, discarding terms not divisible by this.
-/
noncomputable def divMonomial (p : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  AddMonoidAlgebra.divOf p s

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

@[simp]
/-
**MvPolynomial.coeff_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_divMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) (s' : σ ->₀ Nat) 
: coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x
参数：s : σ ->₀ Nat；x : MvPolynomial σ R；s' : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) (s' : σ →₀ ℕ) :
    coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x :=
  rfl

@[simp]
/-
**MvPolynomial.support_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：support_divMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) : (x /ᵐᵒⁿᵒᵐⁱᵃˡ 
s).support = x.support.preimage _ (add_right_injective s).injOn
参数：s : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_divMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    (x /ᵐᵒⁿᵒᵐⁱᵃˡ s).support = x.support.preimage _ (add_right_injective s).injOn :=
  rfl

@[simp]
/-
**MvPolynomial.zero_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：zero_divMonomial (s : σ ->₀ Nat) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
参数：s : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.zero_divOf`：zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0
-/
theorem zero_divMonomial (s : σ →₀ ℕ) : (0 : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.zero_divOf _
/-
**MvPolynomial.divMonomial_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x
参数：x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.divOf_zero`：divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem divMonomial_zero (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ 0 = x :=
  x.divOf_zero

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.add_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：add_divMonomial (x y : MvPolynomial σ R) (s : σ ->₀ Nat) : (x + y) /ᵐᵒⁿᵒᵐⁱ
ᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s
参数：x y : MvPolynomial σ R；s : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.add_divOf`：add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ
 g = x /ᵒᶠ g + y /ᵒᶠ g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_divMonomial (x y : MvPolynomial σ R) (s : σ →₀ ℕ) :
    (x + y) /ᵐᵒⁿᵒᵐⁱᵃˡ s = x /ᵐᵒⁿᵒᵐⁱᵃˡ s + y /ᵐᵒⁿᵒᵐⁱᵃˡ s := by
  simp [divMonomial, MvPolynomial, AddMonoidAlgebra.add_divOf]
/-
**MvPolynomial.divMonomial_add** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：divMonomial_add (a b : σ ->₀ Nat) (x : MvPolynomial σ R) : x /ᵐᵒⁿᵒᵐⁱᵃˡ (a 
+ b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b
参数：a b : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.divOf_add`：divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + 
b) = x /ᵒᶠ a /ᵒᶠ b
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem divMonomial_add (a b : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x /ᵐᵒⁿᵒᵐⁱᵃˡ (a + b) = x /ᵐᵒⁿᵒᵐⁱᵃˡ a /ᵐᵒⁿᵒᵐⁱᵃˡ b :=
  x.divOf_add _ _

@[simp]
/-
**MvPolynomial.divMonomial_monomial_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：divMonomial_monomial_mul (a : σ ->₀ Nat) (x : MvPolynomial σ R) : monomial
 a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x
参数：a : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.of'_mul_divOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G] (a : G)   (x : A
ddMonoidAlgebra k G)…
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem divMonomial_monomial_mul (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.of'_mul_divOf _

@[simp]
/-
**MvPolynomial.divMonomial_mul_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：divMonomial_mul_monomial (a : σ ->₀ Nat) (x : MvPolynomial σ R) : x * mono
mial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x
参数：a : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.mul_of'_divOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G]   (x : AddMonoid
Algebra k G) (a : G)…
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem divMonomial_mul_monomial (a : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x :=
  x.mul_of'_divOf _

@[simp]
/-
**MvPolynomial.divMonomial_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：divMonomial_monomial (a : σ ->₀ Nat) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvP
olynomial σ R)
参数：a : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.of'_divOf`：∀ {k : Type u_1} {G : Type u_2} [inst : Semi
ring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G] (a : G),   (AddMonoi
dAlgebra.of' k G…
-/
theorem divMonomial_monomial (a : σ →₀ ℕ) : monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R) :=
  AddMonoidAlgebra.of'_divOf _

/-- The remainder upon division by `monomial 1 s`. -/
/-
**MvPolynomial.modMonomial** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：modMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) : MvPolynomial σ R
参数：x : MvPolynomial σ R；s : σ ->₀ Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The remainder upon division by `monomial 1 s`.
-/
noncomputable def modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) : MvPolynomial σ R :=
  x.modOf s

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
/-
**MvPolynomial.coeff_modMonomial_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：coeff_modMonomial_of_not_le {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h :
 ¬s <= s') : coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x
参数：x : MvPolynomial σ R；h : ¬s <= s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_not_exists_add`：coeff_modOf_of_not_exist
s_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d) : (x %ᵒᶠ g).coeff 
g' = x.coeff g'
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coeff_modMonomial_of_not_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : ¬s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff s' x :=
  x.coeff_modOf_of_not_exists_add s s' <| by rintro ⟨d, rfl⟩; exact h le_self_add

@[simp]
/-
**MvPolynomial.coeff_modMonomial_of_le** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_modMonomial_of_le {s' s : σ ->₀ Nat} (x : MvPolynomial σ R) (h : s <
= s') : coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0
参数：x : MvPolynomial σ R；h : s <= s'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_exists_add`：coeff_modOf_of_exists_add (x
 : k[G]) (g : G) (g' : G) (h : exists d, g' = g + d) : (x %ᵒᶠ g).coeff g' = 0
· 使用定理 `ExistsAddOfLE.exists_add_of_le`：∀ {α : Type u} {inst : Add α} {inst_1 : 
LE α} [self : ExistsAddOfLE α] {a b : α}, a ≤ b → ∃ c, b = a + c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem coeff_modMonomial_of_le {s' s : σ →₀ ℕ} (x : MvPolynomial σ R) (h : s ≤ s') :
    coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0 :=
  x.coeff_modOf_of_exists_add _ _ <| exists_add_of_le h

@[simp]
/-
**MvPolynomial.monomial_mul_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：monomial_mul_modMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) : monomial
 s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
参数：s : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.of'_mul_modOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] (g : G) (x : AddMonoidAlgebra k G),   (Ad
dMonoidAlgebra.of' k…
-/
theorem monomial_mul_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.of'_mul_modOf _

@[simp]
/-
**MvPolynomial.mul_monomial_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
形式化陈述：mul_monomial_modMonomial (s : σ ->₀ Nat) (x : MvPolynomial σ R) : x * mono
mial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
参数：s : σ ->₀ Nat；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.mul_of'_modOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] (x : AddMonoidAlgebra k G) (g : G),   (x 
* AddMonoidAlgebra.o…
-/
theorem mul_monomial_modMonomial (s : σ →₀ ℕ) (x : MvPolynomial σ R) :
    x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  x.mul_of'_modOf _

@[simp]
/-
**MvPolynomial.monomial_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_modMonomial (s : σ ->₀ Nat) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
参数：s : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.of'_modOf`：∀ {k : Type u_1} {G : Type u_2} [inst : Semi
ring k] [inst_1 : AddCommMonoid G] (g : G),   (AddMonoidAlgebra.of' k G g).modOf
 g = 0
-/
theorem monomial_modMonomial (s : σ →₀ ℕ) : monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0 :=
  AddMonoidAlgebra.of'_modOf _
/-
**MvPolynomial.divMonomial_add_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：divMonomial_add_modMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) : monom
ial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x
参数：x : MvPolynomial σ R；s : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.divOf_add_modOf`：divOf_add_modOf [IsCancelAdd G] (x : k
[G]) (g : G) : of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem divMonomial_add_modMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐⁱᵃˡ s = x :=
  AddMonoidAlgebra.divOf_add_modOf x s
/-
**MvPolynomial.modMonomial_add_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：modMonomial_add_divMonomial (x : MvPolynomial σ R) (s : σ ->₀ Nat) : x %ᵐᵒ
ⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x
参数：x : MvPolynomial σ R；s : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.modOf_add_divOf`：modOf_add_divOf [IsCancelAdd G] (x : k
[G]) (g : G) : x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem modMonomial_add_divMonomial (x : MvPolynomial σ R) (s : σ →₀ ℕ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = x :=
  AddMonoidAlgebra.modOf_add_divOf x s
/-
**MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero** 是 Mathlib 中的一个定理，位于命名空
间 `MvPolynomial`。
形式化陈述：monomial_one_dvd_iff_modMonomial_eq_zero {i : σ ->₀ Nat} {x : MvPolynomial
 σ R} : monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero`：∀ {k : Type u_1} {G : Type u
_2} [inst : Semiring k] [inst_1 : AddCommMonoid G] [IsCancelAdd G]   {x : AddMon
oidAlgebra k G} {g : G}, AddMono…
· 使用定理 `Finsupp.instIsCancelAdd`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddZero
Class M] [IsCancelAdd M], IsCancelAdd (ι →₀ M)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
-/
theorem monomial_one_dvd_iff_modMonomial_eq_zero {i : σ →₀ ℕ} {x : MvPolynomial σ R} :
    monomial i (1 : R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0 :=
  AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

end CopiedDeclarations

section XLemmas

local infixl:70 " /ᵐᵒⁿᵒᵐⁱᵃˡ " => divMonomial

local infixl:70 " %ᵐᵒⁿᵒᵐⁱᵃˡ " => modMonomial

@[simp]
/-
**MvPolynomial.X_mul_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) : X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsu
pp.single i 1 = x
参数：i : σ；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.divMonomial_monomial_mul`：divMonomial_monomial_mul (a : σ -
>₀ Nat) (x : MvPolynomial σ R) : monomial a 1 * x /ᵐᵒⁿᵒᵐⁱᵃˡ a = x
-/
theorem X_mul_divMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_monomial_mul _ _

@[simp]
/-
**MvPolynomial.X_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single 
i 1 = 1
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.divMonomial_monomial`：divMonomial_monomial (a : σ ->₀ Nat) 
: monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = (1 : MvPolynomial σ R)
-/
theorem X_divMonomial (i : σ) : (X i : MvPolynomial σ R) /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 1 :=
  divMonomial_monomial (Finsupp.single i 1)

@[simp]
/-
**MvPolynomial.mul_X_divMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) : x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsu
pp.single i 1 = x
参数：x : MvPolynomial σ R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.divMonomial_mul_monomial`：divMonomial_mul_monomial (a : σ -
>₀ Nat) (x : MvPolynomial σ R) : x * monomial a 1 /ᵐᵒⁿᵒᵐⁱᵃˡ a = x
-/
theorem mul_X_divMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_mul_monomial _ _

@[simp]
/-
**MvPolynomial.X_mul_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) : X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsu
pp.single i 1 = 0
参数：i : σ；x : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_mul_modMonomial`：monomial_mul_modMonomial (s : σ -
>₀ Nat) (x : MvPolynomial σ R) : monomial s 1 * x %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
-/
theorem X_mul_modMonomial (i : σ) (x : MvPolynomial σ R) :
    X i * x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_mul_modMonomial _ _

@[simp]
/-
**MvPolynomial.mul_X_modMonomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) : x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsu
pp.single i 1 = 0
参数：x : MvPolynomial σ R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.mul_monomial_modMonomial`：mul_monomial_modMonomial (s : σ -
>₀ Nat) (x : MvPolynomial σ R) : x * monomial s 1 %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
-/
theorem mul_X_modMonomial (x : MvPolynomial σ R) (i : σ) :
    x * X i %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  mul_monomial_modMonomial _ _

@[simp]
/-
**MvPolynomial.modMonomial_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single 
i 1 = 0
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_modMonomial`：monomial_modMonomial (s : σ ->₀ Nat) 
: monomial s (1 : R) %ᵐᵒⁿᵒᵐⁱᵃˡ s = 0
-/
theorem modMonomial_X (i : σ) : (X i : MvPolynomial σ R) %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_modMonomial _
/-
**MvPolynomial.divMonomial_add_modMonomial_single** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：divMonomial_add_modMonomial_single (x : MvPolynomial σ R) (i : σ) : X i * 
(x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x
参数：x : MvPolynomial σ R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.divMonomial_add_modMonomial`：divMonomial_add_modMonomial (x
 : MvPolynomial σ R) (s : σ ->₀ Nat) : monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) + x %ᵐᵒⁿᵒᵐ
ⁱᵃˡ s = x
-/
theorem divMonomial_add_modMonomial_single (x : MvPolynomial σ R) (i : σ) :
    X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = x :=
  divMonomial_add_modMonomial _ _
/-
**MvPolynomial.modMonomial_add_divMonomial_single** 是 Mathlib 中的一个定理，位于命名空间 `MvP
olynomial`。
形式化陈述：modMonomial_add_divMonomial_single (x : MvPolynomial σ R) (i : σ) : x %ᵐᵒⁿ
ᵒᵐⁱᵃˡ Finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) = x
参数：x : MvPolynomial σ R；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.modMonomial_add_divMonomial`：modMonomial_add_divMonomial (x
 : MvPolynomial σ R) (s : σ ->₀ Nat) : x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱ
ᵃˡ s) = x
-/
theorem modMonomial_add_divMonomial_single (x : MvPolynomial σ R) (i : σ) :
    x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) = x :=
  modMonomial_add_divMonomial _ _
/-
**MvPolynomial.X_dvd_iff_modMonomial_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} : X i ∣ x ↔ x
 %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.monomial_one_dvd_iff_modMonomial_eq_zero`：monomial_one_dvd_
iff_modMonomial_eq_zero {i : σ ->₀ Nat} {x : MvPolynomial σ R} : monomial i (1 :
 R) ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ i = 0
-/
theorem X_dvd_iff_modMonomial_eq_zero {i : σ} {x : MvPolynomial σ R} :
    X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0 :=
  monomial_one_dvd_iff_modMonomial_eq_zero

end XLemmas

/-! ### Some results about dvd (`∣`) on `monomial` and `X` -/


/-
**MvPolynomial.monomial_dvd_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：monomial_dvd_monomial {r s : R} {i j : σ ->₀ Nat} : monomial i r ∣ monomia
l j s ↔ (s = 0 ∨ i <= j) ∧ r ∣ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.ext_iff`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring
 R] {p q : MvPolynomial σ R},   p = q ↔ ∀ (m : σ →₀ ℕ), MvPolynomial.coeff m p =
 MvPolynom…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MvPolynomial.coeff_monomial_mul'`：coeff_monomial_mul' (m) (s : σ ->₀ Nat
) (r : R) (p : MvPolynomial σ R) : coeff m (monomial s r * p) = if s <= m then r
 * coeff (m - s) p els…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.monomial_zero`：monomial_zero {s : σ ->₀ Nat} : monomial s (
0 : R) = 0
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Finsupp.instCanonicallyOrderedAddOfAddLeftMono`：∀ {ι : Type u_1} {α : Ty
pe u_3} [inst : AddCommMonoid α] [inst_1 : PartialOrder α] [CanonicallyOrderedAd
d α]   [inst_3 : Sub α] [OrderedSub …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
### Some results about dvd (`∣`) on `monomial` and `X`
-/
theorem monomial_dvd_monomial {r s : R} {i j : σ →₀ ℕ} :
    monomial i r ∣ monomial j s ↔ (s = 0 ∨ i ≤ j) ∧ r ∣ s := by
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
      rw [monomial_mul, add_tsub_cancel_of_le hij]

@[simp]
/-
**MvPolynomial.monomial_one_dvd_monomial_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPolyno
mial`。
形式化陈述：monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ ->₀ Nat} : monomial 
i (1 : R) ∣ monomial j 1 ↔ i <= j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.monomial_dvd_monomial`：monomial_dvd_monomial {r s : R} {i j
 : σ ->₀ Nat} : monomial i r ∣ monomial j s ↔ (s = 0 ∨ i <= j) ∧ r ∣ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem monomial_one_dvd_monomial_one [Nontrivial R] {i j : σ →₀ ℕ} :
    monomial i (1 : R) ∣ monomial j 1 ↔ i ≤ j := by
  rw [monomial_dvd_monomial]
  simp_rw [one_ne_zero, false_or, dvd_rfl, and_true]

@[simp]
/-
**MvPolynomial.X_dvd_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_dvd_X [Nontrivial R] {i j : σ} : (X i : MvPolynomial σ R) ∣ (X j : MvPol
ynomial σ R) ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MvPolynomial.monomial_one_dvd_monomial_one`：monomial_one_dvd_monomial_on
e [Nontrivial R] {i j : σ ->₀ Nat} : monomial i (1 : R) ∣ monomial j 1 ↔ i <= j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem X_dvd_X [Nontrivial R] {i j : σ} :
    (X i : MvPolynomial σ R) ∣ (X j : MvPolynomial σ R) ↔ i = j := by
  refine monomial_one_dvd_monomial_one.trans ?_
  simp_rw [Finsupp.single_le_iff, Nat.one_le_iff_ne_zero, Finsupp.single_apply_ne_zero,
    ne_eq, reduceCtorEq, not_false_eq_true, and_true]

@[simp]
/-
**MvPolynomial.X_dvd_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_dvd_monomial {i : σ} {j : σ ->₀ Nat} {r : R} : (X i : MvPolynomial σ R) 
∣ monomial j r ↔ r = 0 ∨ j i != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `MvPolynomial.monomial_dvd_monomial`：monomial_dvd_monomial {r s : R} {i j
 : σ ->₀ Nat} : monomial i r ∣ monomial j s ↔ (s = 0 ∨ i <= j) ∧ r ∣ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem X_dvd_monomial {i : σ} {j : σ →₀ ℕ} {r : R} :
    (X i : MvPolynomial σ R) ∣ monomial j r ↔ r = 0 ∨ j i ≠ 0 := by
  refine monomial_dvd_monomial.trans ?_
  simp_rw [one_dvd, and_true, Finsupp.single_le_iff, Nat.one_le_iff_ne_zero]
/-
**MvPolynomial.eq_divMonomial_single** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_divMonomial_single [IsLeftCancelAdd R] {i : σ} {p q r : MvPolynomial σ 
R} (h : p = X i * q + r) (hr : forall n in r.support, n i = 0) : q = p.divMonomi
al (Finsupp.single i 1)
参数：h : p = X i * q + r；hr : forall n in r.support, n i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coeff_divMonomial`：coeff_divMonomial (s : σ ->₀ Nat) (x : M
vPolynomial σ R) (s' : σ ->₀ Nat) : coeff s' (x /ᵐᵒⁿᵒᵐⁱᵃˡ s) = coeff (s + s') x
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `MvPolynomial.coeff_X_mul`：coeff_X_mul (m) (s : σ) (p : MvPolynomial σ R)
 : coeff (Finsupp.single s 1 + m) (X s * p) = coeff m p
· 使用定理 `left_eq_add`：∀ {M : Type u_4} [inst : AddMonoid M] [IsLeftCancelAdd M] {
a b : M}, a = a + b ↔ b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
-/
theorem eq_divMonomial_single [IsLeftCancelAdd R]
    {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r)
    (hr : ∀ n ∈ r.support, n i = 0) :
    q = p.divMonomial (Finsupp.single i 1) := by
  ext n
  rw [coeff_divMonomial, h, coeff_add, coeff_X_mul, left_eq_add, ← notMem_support_iff]
  intro hn
  simpa using hr _ hn
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsLeftCancelAdd R] :
    IsCancelAdd (MvPolynomial σ R) := by
  suffices IsLeftCancelAdd (MvPolynomial σ R) from
    AddCommMagma.IsLeftCancelAdd.toIsCancelAdd _
  refine { add_left_cancel := fun f g h H ↦ ?_ }
  ext d
  simpa using congr_arg (coeff d) H
/-
**MvPolynomial.eq_modMonomial_single** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：eq_modMonomial_single [IsLeftCancelAdd R] {σ : Type*} {i : σ} {p q r : MvP
olynomial σ R} (h : p = X i * q + r) (hr : forall n in r.support, n i = 0) : r =
 p.modMonomial (Finsupp.single i 1)
参数：h : p = X i * q + r；hr : forall n in r.support, n i = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `MvPolynomial.instIsCancelAddOfIsLeftCancelAdd`：∀ {σ : Type u_1} {R : Typ
e u_2} [inst : CommSemiring R] [IsLeftCancelAdd R], IsCancelAdd (MvPolynomial σ 
R)
· 使用定理 `MvPolynomial.eq_divMonomial_single`：eq_divMonomial_single [IsLeftCancelA
dd R] {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r) (hr : forall n in
 r.support, n i = 0) : q…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.divMonomial_add_modMonomial_single`：divMonomial_add_modMono
mial_single (x : MvPolynomial σ R) (i : σ) : X i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i
 1) + x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 …
-/
theorem eq_modMonomial_single [IsLeftCancelAdd R]
    {σ : Type*} {i : σ} {p q r : MvPolynomial σ R}
    (h : p = X i * q + r) (hr : ∀ n ∈ r.support, n i = 0) :
    r = p.modMonomial (Finsupp.single i 1) := by
  have h' := id h
  rwa [← p.divMonomial_add_modMonomial_single i,
    eq_divMonomial_single h hr, add_right_inj, eq_comm] at h'

section CommRing

variable {R : Type*} [CommRing R] {i : σ} {p q r : MvPolynomial σ R}

/-
**MvPolynomial.eq_modMonomial_single_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：eq_modMonomial_single_iff (h : X i ∣ p - r) : r = p.modMonomial (Finsupp.s
ingle i 1) ↔ forall n in r.support, n i = 0
参数：h : X i ∣ p - r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `MvPolynomial.coeff_modMonomial_of_le`：coeff_modMonomial_of_le {s' s : σ 
->₀ Nat} (x : MvPolynomial σ R) (h : s <= s') : coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.eq_modMonomial_single`：eq_modMonomial_single [IsLeftCancelA
dd R] {σ : Type*} {i : σ} {p q r : MvPolynomial σ R} (h : p = X i * q + r) (hr :
 forall n in r.support, …
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
-/
theorem eq_modMonomial_single_iff (h : X i ∣ p - r) :
    r = p.modMonomial (Finsupp.single i 1) ↔
      ∀ n ∈ r.support, n i = 0 := by
  refine ⟨fun h n ↦ ?_, fun hr ↦ ?_⟩
  · contrapose!
    intro hn
    rw [h, notMem_support_iff]
    apply coeff_modMonomial_of_le
    simpa [Nat.one_le_iff_ne_zero]
  · obtain ⟨q, hq⟩ := h
    apply eq_modMonomial_single (q := q) _ hr
    rwa [← sub_eq_iff_eq_add]
/-
**MvPolynomial.X_dvd_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_dvd_mul_iff [IsCancelMulZero R] : X i ∣ p * q ↔ X i ∣ p ∨ X i ∣ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `MvPolynomial.modMonomial_add_divMonomial_single`：modMonomial_add_divMono
mial_single (x : MvPolynomial σ R) (i : σ) : x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X 
i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) …
· 使用定理 `MvPolynomial.eq_modMonomial_single_iff`：eq_modMonomial_single_iff (h : X
 i ∣ p - r) : r = p.modMonomial (Finsupp.single i 1) ↔ forall n in r.support, n 
i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `MvPolynomial.notMem_support_iff`：notMem_support_iff {p : MvPolynomial σ 
R} {m : σ ->₀ Nat} : m ∉ p.support ↔ p.coeff m = 0
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `MvPolynomial.coeff_modMonomial_of_le`：coeff_modMonomial_of_le {s' s : σ 
->₀ Nat} (x : MvPolynomial σ R) (h : s <= s') : coeff s' (x %ᵐᵒⁿᵒᵐⁱᵃˡ s) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `MvPolynomial.instNoZeroDivisors`：∀ {R : Type u} {σ : Type u_1} [inst : C
ommSemiring R] [NoZeroDivisors R], NoZeroDivisors (MvPolynomial σ R)
· 使用定理 `IsRightCancelMulZero.to_noZeroDivisors`：∀ (M₀ : Type u_1) [inst : MulZer
oClass M₀] [IsRightCancelMulZero M₀], NoZeroDivisors M₀
（共 33 条，此处仅展示前 30 条）
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
      rw [notMem_support_iff, coeff_mul]
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
/-
**MvPolynomial.X_prime** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：X_prime [IsCancelMulZero R] [Nontrivial R] : Prime (X i : MvPolynomial σ R
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.X_ne_zero`：X_ne_zero [Nontrivial R] (s : σ) : X (R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.constantCoeff_X`：constantCoeff_X (i : σ) : constantCoeff (X
 i : MvPolynomial σ R) = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.X_dvd_mul_iff`：X_dvd_mul_iff [IsCancelMulZero R] : X i ∣ p 
* q ↔ X i ∣ p ∨ X i ∣ q
-/
theorem X_prime [IsCancelMulZero R] [Nontrivial R] : Prime (X i : MvPolynomial σ R) := by
  refine ⟨X_ne_zero i, ?_, fun p q ↦ X_dvd_mul_iff.mp⟩
  intro h
  rw [isUnit_iff_exists] at h
  rcases h with ⟨u, hu, -⟩
  apply_fun constantCoeff at hu
  simp at hu
/-
**MvPolynomial.dvd_X_mul_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：dvd_X_mul_iff [IsCancelMulZero R] : p ∣ X i * q ↔ p ∣ q ∨ (X i ∣ p ∧ p.div
Monomial (Finsupp.single i 1) ∣ q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `MvPolynomial.X_mul_cancel_left_iff`：X_mul_cancel_left_iff {i : σ} : X i 
* p = X i * q ↔ p = q
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MvPolynomial.X_dvd_iff_modMonomial_eq_zero`：X_dvd_iff_modMonomial_eq_zer
o {i : σ} {x : MvPolynomial σ R} : X i ∣ x ↔ x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 = 0
· 使用定理 `MvPolynomial.modMonomial_add_divMonomial_single`：modMonomial_add_divMono
mial_single (x : MvPolynomial σ R) (i : σ) : x %ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1 + X 
i * (x /ᵐᵒⁿᵒᵐⁱᵃˡ Finsupp.single i 1) …
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `MvPolynomial.modMonomial_add_divMonomial`：modMonomial_add_divMonomial (x
 : MvPolynomial σ R) (s : σ ->₀ Nat) : x %ᵐᵒⁿᵒᵐⁱᵃˡ s + monomial s 1 * (x /ᵐᵒⁿᵒᵐⁱ
ᵃˡ s) = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `mul_dvd_mul_left`：mul_dvd_mul_left (a : α) (h : b ∣ c) : a * b ∣ a * c
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
      rw [← p.modMonomial_add_divMonomial_single i, hip,
        zero_add, mul_assoc, X_mul_cancel_left_iff] at hp
      use r
  · rintro (hp | ⟨hi, hq⟩)
    · exact dvd_mul_of_dvd_right hp (X i)
    · suffices p = X i * p.divMonomial (Finsupp.single i 1) by
        rw [this]
        exact mul_dvd_mul_left (X i) hq
      conv_lhs => rw [← p.modMonomial_add_divMonomial (Finsupp.single i 1)]
      simpa only [← C_mul_X_eq_monomial, C_1, one_mul, add_eq_right,
        ← X_dvd_iff_modMonomial_eq_zero]
/-
**MvPolynomial.dvd_monomial_mul_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomi
al`。
形式化陈述：dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ ->₀ Nat} : p ∣ mono
mial n 1 * q ↔ exists m r, m <= n ∧ r ∣ q ∧ p = monomial m 1 * r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finsupp.degree_eq_zero_iff`：degree_eq_zero_iff {R : Type*} [AddCommMonoi
d R] [PartialOrder R] [CanonicallyOrderedAdd R] (d : σ ->₀ R) : degree d = 0 ↔ d
 = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finsupp.instIsBotZeroClass`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddC
ommMonoid α] [inst_1 : PartialOrder α] [IsBotZeroClass α],   IsBotZeroClass (ι →
₀ α)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.support_nonempty_iff`：support_nonempty_iff {f : α ->₀ M} : f.sup
port.Nonempty ↔ f != 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `Finsupp.sub_add_single_one_cancel`：sub_add_single_one_cancel {u : ι ->₀ 
Nat} {i : ι} (h : u i != 0) : u - single i 1 + single i 1 = u
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 64 条，此处仅展示前 30 条）
-/
theorem dvd_monomial_mul_iff_exists [IsCancelMulZero R] {n : σ →₀ ℕ} :
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · simp only [Subsingleton.elim _ p, dvd_refl, and_self, and_true, exists_const, true_iff]
    refine ⟨n, le_refl n⟩
  suffices ∀ (d) (n : σ →₀ ℕ) (hd : n.degree = d) (p q : MvPolynomial σ R),
    p ∣ monomial n 1 * q ↔ ∃ m r, m ≤ n ∧ r ∣ q ∧ p = monomial m 1 * r from this n.degree n rfl p q
  intro d
  induction d with
  | zero =>
    intro n hn p
    rw [Finsupp.degree_eq_zero_iff] at hn
    simp only [hn, monomial_zero', C_1, one_mul, nonpos_iff_eq_zero, exists_and_left,
      exists_eq_left, exists_eq_right', implies_true]
  | succ d hd =>
    intro n hn p q
    refine ⟨fun hp ↦ ?_, fun ⟨m, r, hmn, hrq, hp⟩ ↦ ?_⟩
    · obtain ⟨i, hi⟩ : n.support.Nonempty := by
        rw [Finsupp.support_nonempty_iff]
        intro hn'
        simp [hn'] at hn
      let n' := n - Finsupp.single i 1
      have hn' : n' + Finsupp.single i 1 = n := by
        apply Finsupp.sub_add_single_one_cancel
        rwa [← Finsupp.mem_support_iff]
      have hnn' : n' ≤ n := by simp [← hn']
      have hd' : n'.degree = d := by
        rw [← add_left_inj, ← hn, ← hn']
        simp
      rw [← hn', monomial_add_single, pow_one, mul_comm _ (X i), mul_assoc, dvd_X_mul_iff] at hp
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

