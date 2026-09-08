/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Division of `AddMonoidAlgebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `LaurentPolynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `AddMonoidAlgebra.divOf x g`: divides `x` by the monomial `AddMonoidAlgebra.of k G g`
* `AddMonoidAlgebra.modOf x g`: the remainder upon dividing `x` by the monomial
  `AddMonoidAlgebra.of k G g`.

## Main results

* `AddMonoidAlgebra.divOf_add_modOf`, `AddMonoidAlgebra.modOf_add_divOf`: `divOf` and
  `modOf` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroupDvd`. The results in this file could be duplicated for
`MonoidAlgebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/

@[expose] public section


variable {k G : Type*} [Semiring k]

namespace AddMonoidAlgebra

section

variable [AddCommMonoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
/-
**AddMonoidAlgebra.divOf** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：divOf [IsCancelAdd G] (x : k[G]) (g : G) : k[G] where -- note: comapping b
y `+ g` has the effect of subtracting `g` from every element in -- the support, 
and discarding the elements of the support from which `g` can't be subtracted. -
- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`, --
 then no discarding occurs. coeff
参数：x : k[G]；g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Divide by `of' k G g`, discarding terms not divisible by this.
-/
noncomputable def divOf [IsCancelAdd G] (x : k[G]) (g : G) : k[G] where
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  coeff := x.coeff.comapDomain (g + ·) (add_right_injective g).injOn

local infixl:70 " /ᵒᶠ " => divOf

section divOf
variable [IsCancelAdd G]

/-
**AddMonoidAlgebra.coeff_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] [inst_2 : IsCancelAdd G] (g : G)   (x : AddMonoidAlgebra k G) (g' : G), (x.
divOf g).coeff g' = x.coeff (g + g')
参数：g : G；x : AddMonoidAlgebra k G；g' : G；x.divOf g；g + g'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coeff_divOf (g : G) (x : k[G]) (g' : G) : (x /ᵒᶠ g).coeff g' = x.coeff (g + g') := rfl

@[deprecated (since := "2026-06-18")] alias divOf_apply := coeff_divOf

@[simp]
/-
**AddMonoidAlgebra.support_coeff_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：support_coeff_divOf (g : G) (x : k[G]) : (x /ᵒᶠ g).coeff.support = x.coeff
.support.preimage (g + ·) (add_right_injective g).injOn
参数：g : G；x : k[G]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_coeff_divOf (g : G) (x : k[G]) :
    (x /ᵒᶠ g).coeff.support = x.coeff.support.preimage (g + ·) (add_right_injective g).injOn :=
  rfl

@[deprecated (since := "2026-06-18")] alias support_divOf := support_coeff_divOf

@[simp]
/-
**AddMonoidAlgebra.zero_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0 := by ext; simp

@[simp]
/-
**AddMonoidAlgebra.divOf_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x
参数：x : k[G]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x := by ext; simp
/-
**AddMonoidAlgebra.add_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g
参数：x y : k[G]；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g := by ext; simp
/-
**AddMonoidAlgebra.divOf_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b
参数：x : k[G]；a b : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by ext; simp [add_assoc]

/-- A bundled version of `AddMonoidAlgebra.divOf`. -/
@[simps]
/-
**AddMonoidAlgebra.divOfHom** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：divOfHom : Multiplicative G ->* AddMonoid.End k[G] where toFun g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled version of `AddMonoidAlgebra.divOf`.
-/
noncomputable def divOfHom : Multiplicative G →* AddMonoid.End k[G] where
  toFun g :=
    { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)
/-
**AddMonoidAlgebra.of'_mul_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] [inst_2 : IsCancelAdd G] (a : G)   (x : AddMonoidAlgebra k G), (AddMonoidAl
gebra.of' k G a * x).divOf a = x
参数：a : G；x : AddMonoidAlgebra k G；AddMonoidAlgebra.of' k G a * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_single_mul_add`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddMonoid M] [IsCancelAdd M] (x : AddMonoidAlgebra 
R M)   (r : R) (m m' : M), …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of'_mul_divOf (a : G) (x : k[G]) : of' k G a * x /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, coeff_single_mul_add, one_mul]
/-
**AddMonoidAlgebra.mul_of'_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] [inst_2 : IsCancelAdd G]   (x : AddMonoidAlgebra k G) (a : G), (x * AddMono
idAlgebra.of' k G a).divOf a = x
参数：x : AddMonoidAlgebra k G；a : G；x * AddMonoidAlgebra.of' k G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddMonoidAlgebra.coeff_mul_single_add`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddMonoid M] [IsCancelAdd M] (x : AddMonoidAlgebra 
R M)   (r : R) (m m' : M), …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mul_of'_divOf (x : k[G]) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, add_comm a, coeff_mul_single_add, mul_one]
/-
**AddMonoidAlgebra.of'_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] [inst_2 : IsCancelAdd G] (a : G),   (AddMonoidAlgebra.of' k G a).divOf a = 
1
参数：a : G；AddMonoidAlgebra.of' k G a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.divOf.congr_simp`：∀ {k : Type u_1} {G : Type u_2} [inst
 : Semiring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G]   (x x_1 : Ad
dMonoidAlgebra k G), x …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddMonoidAlgebra.mul_of'_divOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G]   (x : AddMonoid
Algebra k G) (a : G)…
-/
theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a

end divOf

/-- The remainder upon division by `of' k G g`. -/
/-
**AddMonoidAlgebra.modOf** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：modOf (x : k[G]) (g : G) : k[G]
参数：x : k[G]；g : G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The remainder upon division by `of' k G g`.
-/
noncomputable def modOf (x : k[G]) (g : G) : k[G] :=
  letI := Classical.decPred fun g₁ => ∃ g₂, g₁ = g + g₂
  .ofCoeff <| x.coeff.filter fun g₁ => ¬∃ g₂, g₁ = g + g₂

local infixl:70 " %ᵒᶠ " => modOf

@[simp]
/-
**AddMonoidAlgebra.coeff_modOf_of_not_exists_add** 是 Mathlib 中的一个定理，位于命名空间 `AddM
onoidAlgebra`。
形式化陈述：coeff_modOf_of_not_exists_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, 
g' = g + d) : (x %ᵒᶠ g).coeff g' = x.coeff g'
参数：x : k[G]；g : G；g' : G；h : ¬exists d, g' = g + d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.filter_apply_pos`：filter_apply_pos {a : α} (h : p a) : f.filter 
p a = f a
-/
theorem coeff_modOf_of_not_exists_add (x : k[G]) (g : G) (g' : G) (h : ¬∃ d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = x.coeff g' := by
  classical exact Finsupp.filter_apply_pos _ _ h

@[deprecated (since := "2026-06-18")]
alias modOf_apply_of_not_exists_add := coeff_modOf_of_not_exists_add

@[simp]
/-
**AddMonoidAlgebra.coeff_modOf_of_exists_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：coeff_modOf_of_exists_add (x : k[G]) (g : G) (g' : G) (h : exists d, g' = 
g + d) : (x %ᵒᶠ g).coeff g' = 0
参数：x : k[G]；g : G；g' : G；h : exists d, g' = g + d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.filter_apply_neg`：filter_apply_neg {a : α} (h : ¬p a) : f.filter
 p a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
theorem coeff_modOf_of_exists_add (x : k[G]) (g : G) (g' : G) (h : ∃ d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = 0 := by
  classical exact Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]

@[deprecated (since := "2026-06-18")] alias modOf_apply_of_exists_add := coeff_modOf_of_exists_add

@[simp]
/-
**AddMonoidAlgebra.coeff_modOf_add_self** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：coeff_modOf_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (d + g) 
= 0
参数：x : k[G]；g : G；d : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_exists_add`：coeff_modOf_of_exists_add (x
 : k[G]) (g : G) (g' : G) (h : exists d, g' = g + d) : (x %ᵒᶠ g).coeff g' = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem coeff_modOf_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (d + g) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_add_self := coeff_modOf_add_self
/-
**AddMonoidAlgebra.coeff_modOf_self_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：coeff_modOf_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) 
= 0
参数：x : k[G]；g : G；d : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_exists_add`：coeff_modOf_of_exists_add (x
 : k[G]) (g : G) (g' : G) (h : exists d, g' = g + d) : (x %ᵒᶠ g).coeff g' = 0
-/
theorem coeff_modOf_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, rfl⟩

@[deprecated (since := "2026-06-18")] alias modOf_apply_self_add := coeff_modOf_self_add
/-
**AddMonoidAlgebra.of'_mul_modOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] (g : G) (x : AddMonoidAlgebra k G),   (AddMonoidAlgebra.of' k G g * x).modO
f g = 0
参数：g : G；x : AddMonoidAlgebra k G；AddMonoidAlgebra.of' k G g * x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_modOf_self_add`：coeff_modOf_self_add (x : k[G]) (
g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_not_exists_add`：coeff_modOf_of_not_exist
s_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d) : (x %ᵒᶠ g).coeff 
g' = x.coeff g'
· 使用定理 `AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne`：∀ {R : Type u_1} {M 
: Type u_4} [inst : Semiring R] {m m' : M} [inst_1 : Add M] (r : R) (x : AddMono
idAlgebra R M),   (∀ (d : M), m + d ≠ m'…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
theorem of'_mul_modOf (g : G) (x : k[G]) : of' k G g * x %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_single_mul_of_forall_add_ne]
    simpa [eq_comm] using h
/-
**AddMonoidAlgebra.mul_of'_modOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] (x : AddMonoidAlgebra k G) (g : G),   (x * AddMonoidAlgebra.of' k G g).modO
f g = 0
参数：x : AddMonoidAlgebra k G；g : G；x * AddMonoidAlgebra.of' k G g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_modOf_self_add`：coeff_modOf_self_add (x : k[G]) (
g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_not_exists_add`：coeff_modOf_of_not_exist
s_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d) : (x %ᵒᶠ g).coeff 
g' = x.coeff g'
· 使用定理 `AddMonoidAlgebra.coeff_mul_single_of_forall_add_ne`：∀ {R : Type u_1} {M 
: Type u_4} [inst : Semiring R] {m m' : M} [inst_1 : Add M] (r : R) (x : AddMono
idAlgebra R M),   (∀ (d : M), d + m ≠ m'…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem mul_of'_modOf (x : k[G]) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_mul_single_of_forall_add_ne]
    simpa [eq_comm, add_comm] using h
/-
**AddMonoidAlgebra.of'_modOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] (g : G),   (AddMonoidAlgebra.of' k G g).modOf g = 0
参数：g : G；AddMonoidAlgebra.of' k G g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddMonoidAlgebra.mul_of'_modOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] (x : AddMonoidAlgebra k G) (g : G),   (x 
* AddMonoidAlgebra.o…
-/
theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g
/-
**AddMonoidAlgebra.divOf_add_modOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：divOf_add_modOf [IsCancelAdd G] (x : k[G]) (g : G) : of' k G g * (x /ᵒᶠ g)
 + x %ᵒᶠ g = x
参数：x : k[G]；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ext`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R
] {x y : AddMonoidAlgebra R M}, x.coeff = y.coeff → x = y
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_modOf_self_add`：coeff_modOf_self_add (x : k[G]) (
g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddMonoidAlgebra.coeff_single_mul_add`：∀ {R : Type u_1} {M : Type u_4} [
inst : Semiring R] [inst_1 : AddMonoid M] [IsCancelAdd M] (x : AddMonoidAlgebra 
R M)   (r : R) (m m' : M), …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `AddMonoidAlgebra.coeff_divOf`：∀ {k : Type u_1} {G : Type u_2} [inst : Se
miring k] [inst_1 : AddCommMonoid G] [inst_2 : IsCancelAdd G] (g : G)   (x : Add
MonoidAlgebra k G)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.coeff_modOf_of_not_exists_add`：coeff_modOf_of_not_exist
s_add (x : k[G]) (g : G) (g' : G) (h : ¬exists d, g' = g + d) : (x %ᵒᶠ g).coeff 
g' = x.coeff g'
· 使用定理 `AddMonoidAlgebra.coeff_single_mul_of_forall_add_ne`：∀ {R : Type u_1} {M 
: Type u_4} [inst : Semiring R] {m m' : M} [inst_1 : Add M] (r : R) (x : AddMono
idAlgebra R M),   (∀ (d : M), m + d ≠ m'…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem divOf_add_modOf [IsCancelAdd G] (x : k[G]) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  ext g'
  dsimp only [coeff_add, of'_apply, Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add, add_zero, coeff_single_mul_add, one_mul, coeff_divOf]
  · rw [coeff_modOf_of_not_exists_add x _ _ h, coeff_single_mul_of_forall_add_ne, zero_add]
    simpa [eq_comm] using h
/-
**AddMonoidAlgebra.modOf_add_divOf** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：modOf_add_divOf [IsCancelAdd G] (x : k[G]) (g : G) : x %ᵒᶠ g + of' k G g *
 (x /ᵒᶠ g) = x
参数：x : k[G]；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `AddMonoidAlgebra.divOf_add_modOf`：divOf_add_modOf [IsCancelAdd G] (x : k
[G]) (g : G) : of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x
-/
theorem modOf_add_divOf [IsCancelAdd G] (x : k[G]) (g : G) :
    x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x := by
  rw [add_comm, divOf_add_modOf]
/-
**AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：∀ {k : Type u_1} {G : Type u_2} [inst : Semiring k] [inst_1 : AddCommMonoi
d G] [IsCancelAdd G]   {x : AddMonoidAlgebra k G} {g : G}, AddMonoidAlgebra.of' 
k G g ∣ x ↔ x.modOf g = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.of'_mul_modOf`：∀ {k : Type u_1} {G : Type u_2} [inst : 
Semiring k] [inst_1 : AddCommMonoid G] (g : G) (x : AddMonoidAlgebra k G),   (Ad
dMonoidAlgebra.of' k…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.divOf_add_modOf`：divOf_add_modOf [IsCancelAdd G] (x : k
[G]) (g : G) : of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
-/
theorem of'_dvd_iff_modOf_eq_zero [IsCancelAdd G] {x : k[G]} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g, h, add_zero]
    exact dvd_mul_right _ _

end

end AddMonoidAlgebra

