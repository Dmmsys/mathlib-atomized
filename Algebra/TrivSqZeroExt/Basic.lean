/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Eric Wieser, Antoine Chambert-Loir, María-Inés de Frutos-Fernández
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Order.Group.Nat

/-!
# Trivial Square-Zero Extension

Given a ring `R` together with an `(R, R)`-bimodule `M`, the trivial square-zero extension of `M`
over `R` is defined to be the `R`-algebra `R ⊕ M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + m₁ r₂`.

It is a square-zero extension because `M^2 = 0`.

Note that expressing this requires bimodules; we write these in general for a
not-necessarily-commutative `R` as:
```lean
variable {R M : Type*} [Semiring R] [AddCommMonoid M]
variable [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
```
If we instead work with a commutative `R'` acting symmetrically on `M`, we write
```lean
variable {R' M : Type*} [CommSemiring R'] [AddCommMonoid M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]
```
noting that in this context `IsCentralScalar R' M` implies `SMulCommClass R' R'ᵐᵒᵖ M`.

Many of the later results in this file are only stated for the commutative `R'` for simplicity.

## Main definitions

* `TrivSqZeroExt.inl`, `TrivSqZeroExt.inr`: the canonical inclusions into
  `TrivSqZeroExt R M`.
* `TrivSqZeroExt.fst`, `TrivSqZeroExt.snd`: the canonical projections from
  `TrivSqZeroExt R M`.
* `triv_sq_zero_ext.algebra`: the associated `R`-algebra structure.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[S] A` are uniquely defined by an algebra morphism `f : R →ₐ[S] A`
  on `R` and a linear map `g : M →ₗ[S] A` on `M` such that:
  * `g x * g y = 0`: the elements of `M` continue to square to zero.
  * `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: left and right actions are preserved by
    `g`.
* `TrivSqZeroExt.lift`: the universal property of the trivial square-zero extension; algebra
  morphisms `TrivSqZeroExt R M →ₐ[R] A` are uniquely defined by linear maps `M →ₗ[R] A` for
  which the product of any two elements in the range is zero.

-/

@[expose] public section

universe u v w

/-- "Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` over `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
/-
**TrivSqZeroExt** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TrivSqZeroExt (R : Type u) (M : Type v)
参数：R : Type u；M : Type v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
"Trivial Square-Zero Extension".

Given a module `M` over a ring `R`, the trivial square-zero extension of `M` ove
r `R` is defined
to be the `R`-algebra `R × M` with multiplication given by
`(r₁ + m₁) * (r₂ + m₂) = r₁ r₂ + r₁ m₂ + r₂ m₁`.

It is a square-zero extension because `M^2 = 0`.
-/
def TrivSqZeroExt (R : Type u) (M : Type v) :=
  R × M

local notation "tsze" => TrivSqZeroExt

open scoped RightActions

namespace TrivSqZeroExt

open MulOpposite

section Basic

variable {R : Type u} {M : Type v}

/-- The canonical inclusion `R → TrivSqZeroExt R M`. -/
/-
**TrivSqZeroExt.inl** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl [Zero M] (r : R) : tsze R M
参数：r : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `R → TrivSqZeroExt R M`.
-/
def inl [Zero M] (r : R) : tsze R M :=
  (r, 0)

/-- The canonical inclusion `M → TrivSqZeroExt R M`. -/
/-
**TrivSqZeroExt.inr** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr [Zero R] (m : M) : tsze R M
参数：m : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion `M → TrivSqZeroExt R M`.
-/
def inr [Zero R] (m : M) : tsze R M :=
  (0, m)

/-- The canonical projection `TrivSqZeroExt R M → R`. -/
/-
**TrivSqZeroExt.fst** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst (x : tsze R M) : R
参数：x : tsze R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection `TrivSqZeroExt R M → R`.
-/
def fst (x : tsze R M) : R :=
  x.1

/-- The canonical projection `TrivSqZeroExt R M → M`. -/
/-
**TrivSqZeroExt.snd** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd (x : tsze R M) : M
参数：x : tsze R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical projection `TrivSqZeroExt R M → M`.
-/
def snd (x : tsze R M) : M :=
  x.2

@[simp]
/-
**TrivSqZeroExt.fst_mk** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_mk (r : R) (m : M) : fst (r, m) = r
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mk (r : R) (m : M) : fst (r, m) = r :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_mk** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_mk (r : R) (m : M) : snd (r, m) = m
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mk (r : R) (m : M) : snd (r, m) = m :=
  rfl

@[ext]
/-
**TrivSqZeroExt.ext** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y
参数：h1 : x.fst = y.fst；h2 : x.snd = y.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
-/
theorem ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2

section

variable (M)

@[simp]
/-
**TrivSqZeroExt.fst_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst = r :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0
参数：r : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_comp_inl [Zero M] : fst ∘ (inl : R -> tsze R M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inl [Zero M] : fst ∘ (inl : R → tsze R M) = id :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_comp_inl [Zero M] : snd ∘ (inl : R -> tsze R M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inl [Zero M] : snd ∘ (inl : R → tsze R M) = 0 :=
  rfl

end

section

variable (R)

@[simp]
/-
**TrivSqZeroExt.fst_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd = m :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_comp_inr [Zero R] : fst ∘ (inr : M -> tsze R M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_comp_inr [Zero R] : fst ∘ (inr : M → tsze R M) = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_comp_inr [Zero R] : snd ∘ (inr : M -> tsze R M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_comp_inr [Zero R] : snd ∘ (inr : M → tsze R M) = id :=
  rfl

end

/-
**TrivSqZeroExt.fst_surjective** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_surjective [Nonempty M] : Function.Surjective (fst : tsze R M -> R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.fst_surjective`：fst_surjective [h : Nonempty β] : Function.Surjecti
ve (@fst α β)
-/
theorem fst_surjective [Nonempty M] : Function.Surjective (fst : tsze R M → R) :=
  Prod.fst_surjective
/-
**TrivSqZeroExt.snd_surjective** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_surjective [Nonempty R] : Function.Surjective (snd : tsze R M -> M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.snd_surjective`：snd_surjective [h : Nonempty α] : Function.Surjecti
ve (@snd α β)
-/
theorem snd_surjective [Nonempty R] : Function.Surjective (snd : tsze R M → M) :=
  Prod.snd_surjective
/-
**TrivSqZeroExt.inl_injective** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_injective [Zero M] : Function.Injective (inl : R -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
-/
theorem inl_injective [Zero M] : Function.Injective (inl : R → tsze R M) :=
  Function.LeftInverse.injective <| fst_inl _
/-
**TrivSqZeroExt.inr_injective** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_injective [Zero R] : Function.Injective (inr : M -> tsze R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `TrivSqZeroExt.snd_inr`：snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd
 = m
-/
theorem inr_injective [Zero R] : Function.Injective (inr : M → tsze R M) :=
  Function.LeftInverse.injective <| snd_inr _

end Basic

/-! ### Structures inherited from `Prod`

Additive operators and scalar multiplication operate elementwise. -/


section Additive

variable {T : Type*} {S : Type*} {R : Type u} {M : Type v}

/-
**TrivSqZeroExt.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inhabited [Inhabited R] [Inhabited M] : Inhabited (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited [Inhabited R] [Inhabited M] : Inhabited (tsze R M) :=
  inferInstanceAs <| Inhabited (R × M)
/-
**TrivSqZeroExt.zero** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：zero [Zero R] [Zero M] : Zero (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance zero [Zero R] [Zero M] : Zero (tsze R M) :=
  inferInstanceAs <| Zero (R × M)
/-
**TrivSqZeroExt.add** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：add [Add R] [Add M] : Add (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance add [Add R] [Add M] : Add (tsze R M) :=
  inferInstanceAs <| Add (R × M)
/-
**TrivSqZeroExt.sub** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：sub [Sub R] [Sub M] : Sub (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance sub [Sub R] [Sub M] : Sub (tsze R M) :=
  inferInstanceAs <| Sub (R × M)
/-
**TrivSqZeroExt.neg** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：neg [Neg R] [Neg M] : Neg (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance neg [Neg R] [Neg M] : Neg (tsze R M) :=
  inferInstanceAs <| Neg (R × M)
/-
**TrivSqZeroExt.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addSemigroup [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addSemigroup [AddSemigroup R] [AddSemigroup M] : AddSemigroup (tsze R M) :=
  inferInstanceAs <| AddSemigroup (R × M)
/-
**TrivSqZeroExt.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addZeroClass [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addZeroClass [AddZeroClass R] [AddZeroClass M] : AddZeroClass (tsze R M) :=
  inferInstanceAs <| AddZeroClass (R × M)
/-
**TrivSqZeroExt.smul** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：smul [SMul S R] [SMul S M] : SMul S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smul [SMul S R] [SMul S M] : SMul S (tsze R M) :=
  inferInstanceAs <| SMul S (R × M)
/-
**TrivSqZeroExt.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addMonoid [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) where nsmul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid [AddMonoid R] [AddMonoid M] : AddMonoid (tsze R M) where
  nsmul := letI := smul (S := ℕ) (R := R) (M := M); (· • ·)
  __ : AddMonoid (tsze R M) := inferInstanceAs <| AddMonoid (R × M)
/-
**TrivSqZeroExt.addGroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addGroup [AddGroup R] [AddGroup M] : AddGroup (tsze R M) where zsmul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroup [AddGroup R] [AddGroup M] : AddGroup (tsze R M) where
  zsmul := letI := smul (S := ℤ) (R := R) (M := M); (· • ·)
  __ : AddGroup (tsze R M) := inferInstanceAs <| AddGroup (R × M)
/-
**TrivSqZeroExt.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addCommSemigroup [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigr
oup (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup [AddCommSemigroup R] [AddCommSemigroup M] : AddCommSemigroup (tsze R M) :=
  inferInstanceAs <| AddCommSemigroup (R × M)
/-
**TrivSqZeroExt.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addCommMonoid [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R 
M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid [AddCommMonoid R] [AddCommMonoid M] : AddCommMonoid (tsze R M) :=
  inferInstanceAs <| AddCommMonoid (R × M)
/-
**TrivSqZeroExt.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addCommGroup [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup [AddCommGroup R] [AddCommGroup M] : AddCommGroup (tsze R M) :=
  inferInstanceAs <| AddCommGroup (R × M)
/-
**TrivSqZeroExt.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isScalarTower [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S] [IsSc
alarTower T S R] [IsScalarTower T S M] : IsScalarTower T S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isScalarTower [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMul T S]
    [IsScalarTower T S R] [IsScalarTower T S M] : IsScalarTower T S (tsze R M) :=
  inferInstanceAs <| IsScalarTower T S (R × M)
/-
**TrivSqZeroExt.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：smulCommClass [SMul T R] [SMul T M] [SMul S R] [SMul S M] [SMulCommClass T
 S R] [SMulCommClass T S M] : SMulCommClass T S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulCommClass [SMul T R] [SMul T M] [SMul S R] [SMul S M]
    [SMulCommClass T S R] [SMulCommClass T S M] : SMulCommClass T S (tsze R M) :=
  inferInstanceAs <| SMulCommClass T S (R × M)
/-
**TrivSqZeroExt.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isCentralScalar [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentr
alScalar S R] [IsCentralScalar S M] : IsCentralScalar S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCentralScalar [SMul S R] [SMul S M] [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsCentralScalar S R]
    [IsCentralScalar S M] : IsCentralScalar S (tsze R M) :=
  inferInstanceAs <| IsCentralScalar S (R × M)
/-
**TrivSqZeroExt.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mulAction [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R
 M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction [Monoid S] [MulAction S R] [MulAction S M] : MulAction S (tsze R M) :=
  inferInstanceAs <| MulAction S (R × M)
/-
**TrivSqZeroExt.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：distribMulAction [Monoid S] [AddMonoid R] [AddMonoid M] [DistribMulAction 
S R] [DistribMulAction S M] : DistribMulAction S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction [Monoid S] [AddMonoid R] [AddMonoid M]
    [DistribMulAction S R] [DistribMulAction S M] : DistribMulAction S (tsze R M) :=
  inferInstanceAs <| DistribMulAction S (R × M)
/-
**TrivSqZeroExt.module** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：module [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Modu
le S M] : Module S (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [Module S R] [Module S M] :
    Module S (tsze R M) :=
  inferInstanceAs <| Module S (R × M)

/-- The trivial square-zero extension is nontrivial if it is over a nontrivial ring. -/
/-
**TrivSqZeroExt.instNontrivial_of_left** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`
。
形式化陈述：instNontrivial_of_left {R M : Type*} [Nontrivial R] [Nonempty M] : Nontriv
ial (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial square-zero extension is nontrivial if it is over a nontrivial ring.
-/
instance instNontrivial_of_left {R M : Type*} [Nontrivial R] [Nonempty M] :
    Nontrivial (tsze R M) :=
  inferInstanceAs <| Nontrivial (R × M)

/-- The trivial square-zero extension is nontrivial if it is over a nontrivial module. -/
/-
**TrivSqZeroExt.instNontrivial_of_right** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt
`。
形式化陈述：instNontrivial_of_right {R M : Type*} [Nonempty R] [Nontrivial M] : Nontri
vial (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial square-zero extension is nontrivial if it is over a nontrivial modul
e.
-/
instance instNontrivial_of_right {R M : Type*} [Nonempty R] [Nontrivial M] :
    Nontrivial (tsze R M) :=
  inferInstanceAs <| Nontrivial (R × M)

@[simp]
/-
**TrivSqZeroExt.fst_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_add** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.f
st
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).fst = x₁.fst + x₂.fst :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_add** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.s
nd
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_add [Add R] [Add M] (x₁ x₂ : tsze R M) : (x₁ + x₂).snd = x₁.snd + x₂.snd :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_neg** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_neg [Neg R] [Neg M] (x : tsze R M) : (-x).fst = -x.fst :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_neg** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_neg [Neg R] [Neg M] (x : tsze R M) : (-x).snd = -x.snd :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_sub** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).fst = x₁.fst - x₂.f
st
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).fst = x₁.fst - x₂.fst :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_sub** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.s
nd
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_sub [Sub R] [Sub M] (x₁ x₂ : tsze R M) : (x₁ - x₂).snd = x₁.snd - x₂.snd :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • 
x.fst
参数：s : S；x : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).fst = s • x.fst :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • 
x.snd
参数：s : S；x : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_smul [SMul S R] [SMul S M] (s : S) (x : tsze R M) : (s • x).snd = s • x.snd :=
  rfl
/-
**TrivSqZeroExt.fst_sum** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> t
sze R M) : (∑ i in s, f i).fst = ∑ i in s, (f i).fst
参数：s : Finset ι；f : ι -> tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.fst_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
-/
theorem fst_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst :=
  Prod.fst_sum
/-
**TrivSqZeroExt.snd_sum** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> t
sze R M) : (∑ i in s, f i).snd = ∑ i in s, (f i).snd
参数：s : Finset ι；f : ι -> tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.snd_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : Add
CommMonoid M] [inst_1 : AddCommMonoid N] {s : Finset ι}   {f : ι → M × N}, (∑ c 
∈ …
-/
theorem snd_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → tsze R M) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd :=
  Prod.snd_sum

section

variable (M)

@[simp]
/-
**TrivSqZeroExt.inl_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.inl_add** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) : (inl (r₁ + r₂) : tsze R M) 
= inl r₁ + inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inl_add [Add R] [AddZeroClass M] (r₁ r₂ : R) :
    (inl (r₁ + r₂) : tsze R M) = inl r₁ + inl r₂ :=
  ext rfl (add_zero 0).symm

@[simp]
/-
**TrivSqZeroExt.inl_neg** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_neg [Neg R] [NegZeroClass M] (r : R) : (inl (-r) : tsze R M) = -inl r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem inl_neg [Neg R] [NegZeroClass M] (r : R) : (inl (-r) : tsze R M) = -inl r :=
  ext rfl neg_zero.symm

@[simp]
/-
**TrivSqZeroExt.inl_sub** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) : (inl (r₁ - r₂) : tsze R
 M) = inl r₁ - inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem inl_sub [Sub R] [SubNegZeroMonoid M] (r₁ r₂ : R) :
    (inl (r₁ - r₂) : tsze R M) = inl r₁ - inl r₂ :=
  ext rfl (sub_zero _).symm

@[simp]
/-
**TrivSqZeroExt.inl_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S
) (r : R) : (inl (s • r) : tsze R M) = s • inl r
参数：s : S；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem inl_smul [Monoid S] [AddMonoid M] [SMul S R] [DistribMulAction S M] (s : S) (r : R) :
    (inl (s • r) : tsze R M) = s • inl r :=
  ext rfl (smul_zero s).symm
/-
**TrivSqZeroExt.inl_sum** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> R
) : (inl (∑ i in s, f i) : tsze R M) = ∑ i in s, inl (f i)
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem inl_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → R) :
    (inl (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, inl (f i) :=
  map_sum (LinearMap.inl ℕ _ _) _ _

end

section

variable (R)

@[simp]
/-
**TrivSqZeroExt.inr_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inr_zero [Zero R] [Zero M] : (inr 0 : tsze R M) = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.inr_add** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) : (inr (m₁ + m₂) : tsze R M) 
= inr m₁ + inr m₂
参数：m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inr_add [AddZeroClass R] [Add M] (m₁ m₂ : M) :
    (inr (m₁ + m₂) : tsze R M) = inr m₁ + inr m₂ :=
  ext (add_zero 0).symm rfl

@[simp]
/-
**TrivSqZeroExt.inr_neg** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_neg [NegZeroClass R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem inr_neg [NegZeroClass R] [Neg M] (m : M) : (inr (-m) : tsze R M) = -inr m :=
  ext neg_zero.symm rfl

@[simp]
/-
**TrivSqZeroExt.inr_sub** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_sub [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M) : (inr (m₁ - m₂) : tsze R
 M) = inr m₁ - inr m₂
参数：m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem inr_sub [SubNegZeroMonoid R] [Sub M] (m₁ m₂ : M) :
    (inr (m₁ - m₂) : tsze R M) = inr m₁ - inr m₂ :=
  ext (sub_zero _).symm rfl

@[simp]
/-
**TrivSqZeroExt.inr_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_smul [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M) : (inr (r
 • m) : tsze R M) = r • inr m
参数：r : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
theorem inr_smul [Zero R] [SMulZeroClass S R] [SMul S M] (r : S) (m : M) :
    (inr (r • m) : tsze R M) = r • inr m :=
  ext (smul_zero _).symm rfl
/-
**TrivSqZeroExt.inr_sum** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι -> M
) : (inr (∑ i in s, f i) : tsze R M) = ∑ i in s, inr (f i)
参数：s : Finset ι；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem inr_sum {ι} [AddCommMonoid R] [AddCommMonoid M] (s : Finset ι) (f : ι → M) :
    (inr (∑ i ∈ s, f i) : tsze R M) = ∑ i ∈ s, inr (f i) :=
  map_sum (LinearMap.inr ℕ _ _) _ _

end

/-
**TrivSqZeroExt.inl_fst_add_inr_snd_eq** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`
。
形式化陈述：inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) : 
inl x.fst + inr x.snd = x
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem inl_fst_add_inr_snd_eq [AddZeroClass R] [AddZeroClass M] (x : tsze R M) :
    inl x.fst + inr x.snd = x :=
  ext (add_zero x.1) (zero_add x.2)

/-- To show a property hold on all `TrivSqZeroExt R M` it suffices to show it holds
on terms of the form `inl r + inr m`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
/-
**TrivSqZeroExt.ind** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M -> Prop
} (inl_add_inr : forall r m, P (inl r + inr m)) (x) : P x
参数：inl_add_inr : forall r m, P (inl r + inr m)；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroCla
ss R] [AddZeroClass M] (x : tsze R M) : inl x.fst + inr x.snd = x

--- 原说明 ---
To show a property hold on all `TrivSqZeroExt R M` it suffices to show it holds
on terms of the form `inl r + inr m`.
-/
theorem ind {R M} [AddZeroClass R] [AddZeroClass M] {P : TrivSqZeroExt R M → Prop}
    (inl_add_inr : ∀ r m, P (inl r + inr m)) (x) : P x :=
  inl_fst_add_inr_snd_eq x ▸ inl_add_inr x.1 x.2

/-- This cannot be marked `@[ext]` as it ends up being used instead of `LinearMap.prod_ext` when
working with `R × M`. -/
/-
**TrivSqZeroExt.linearMap_ext** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCom
mMonoid N] [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M ->ₗ[S] N⦄ (hl 
: forall r, f (inl r) = g (inl r)) (hr : forall m, f (inr m) = g (inr m)) : f = 
g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.prod_ext`：prod_ext {f g : M × M₂ ->ₗ[R] M₃} (hl : f.comp (inl 
_ _ _) = g.comp (inl _ _ _)) (hr : f.comp (inr _ _ _) = g.comp (inr _ _ _)) : f 
= g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g

--- 原说明 ---
This cannot be marked `@[ext]` as it ends up being used instead of `LinearMap.pr
od_ext` when
working with `R × M`.
-/
theorem linearMap_ext {N} [Semiring S] [AddCommMonoid R] [AddCommMonoid M] [AddCommMonoid N]
    [Module S R] [Module S M] [Module S N] ⦃f g : tsze R M →ₗ[S] N⦄
    (hl : ∀ r, f (inl r) = g (inl r)) (hr : ∀ m, f (inr m) = g (inr m)) : f = g :=
  LinearMap.prod_ext (LinearMap.ext hl) (LinearMap.ext hr)

variable (R M)

/-- The canonical `R`-linear inclusion `M → TrivSqZeroExt R M`. -/
@[simps apply]
/-
**TrivSqZeroExt.inrHom** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M ->ₗ[R] tsze R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-linear inclusion `M → TrivSqZeroExt R M`.
-/
def inrHom [Semiring R] [AddCommMonoid M] [Module R M] : M →ₗ[R] tsze R M :=
  { LinearMap.inr R R M with toFun := inr }

/-- The canonical `R`-linear projection `TrivSqZeroExt R M → M`. -/
@[simps apply]
/-
**TrivSqZeroExt.sndHom** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `R`-linear projection `TrivSqZeroExt R M → M`.
-/
def sndHom [Semiring R] [AddCommMonoid M] [Module R M] : tsze R M →ₗ[R] M :=
  { LinearMap.snd _ _ _ with toFun := snd }

end Additive

/-! ### Multiplicative structure -/


section Mul

variable {R : Type u} {M : Type v}

/-
**TrivSqZeroExt.one** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：one [One R] [Zero M] : One (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance one [One R] [Zero M] : One (tsze R M) :=
  ⟨(1, 0)⟩
/-
**TrivSqZeroExt.mul** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] : Mul (tsze R M) :=
  ⟨fun x y => (x.1 * y.1, x.1 •> y.2 + x.2 <• y.1)⟩

@[simp]
/-
**TrivSqZeroExt.fst_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_one [One R] [Zero M] : (1 : tsze R M).snd = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.fst_mul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) : (x₁ 
* x₂).fst = x₁.fst * x₂.fst
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).fst = x₁.fst * x₂.fst :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_mul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) : (x₁ 
* x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst
参数：x₁ x₂ : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] (x₁ x₂ : tsze R M) :
    (x₁ * x₂).snd = x₁.fst •> x₂.snd + x₁.snd <• x₂.fst :=
  rfl

section

variable (M)

@[simp]
/-
**TrivSqZeroExt.inl_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.inl_mul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction 
Rᵐᵒᵖ M] (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem inl_mul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl r₁ * inl r₂ :=
  ext rfl <| show (0 : M) = r₁ •> (0 : M) + (0 : M) <• r₂ by rw [smul_zero, zero_add, smul_zero]
/-
**TrivSqZeroExt.inl_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAct
ion Rᵐᵒᵖ M] (r₁ r₂ : R) : (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂)
参数：r₁ r₂ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_mul`：inl_mul [Monoid R] [AddMonoid M] [DistribMulActio
n R M] [DistribMulAction Rᵐᵒᵖ M] (r₁ r₂ : R) : (inl (r₁ * r₂) : tsze R M) = inl 
r₁ * inl r₂
-/
theorem inl_mul_inl [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r₁ r₂ : R) : (inl r₁ * inl r₂ : tsze R M) = inl (r₁ * r₂) :=
  (inl_mul M r₁ r₂).symm

end

section

variable (R)

@[simp]
/-
**TrivSqZeroExt.inr_mul_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m
₁ m₂ : M) : (inr m₁ * inr m₂ : tsze R M) = 0
参数：m₁ m₂ : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MulOpposite.op_zero`：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 
= 0
-/
theorem inr_mul_inr [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) :
    (inr m₁ * inr m₂ : tsze R M) = 0 :=
  ext (mul_zero _) <|
    show (0 : R) •> m₂ + m₁ <• (0 : R) = 0 by rw [zero_smul, zero_add, op_zero, zero_smul]

end

/-
**TrivSqZeroExt.inl_mul_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_mul_inr [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M] [Distr
ibMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inl r * inr m : tsze R M) = inr (r • m)
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inl_mul_inr [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inl r * inr m : tsze R M) = inr (r • m) :=
  ext (mul_zero r) <|
    show r • m + (0 : Rᵐᵒᵖ) • (0 : M) = r • m by rw [smul_zero, add_zero]
/-
**TrivSqZeroExt.inr_mul_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inr_mul_inl [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M] [Distr
ibMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inr m * inl r : tsze R M) = inr (m <• r)
参数：r : R；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem inr_mul_inl [MonoidWithZero R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inr m * inl r : tsze R M) = inr (m <• r) :=
  ext (zero_mul r) <|
    show (0 : R) •> (0 : M) + m <• r = m <• r by rw [smul_zero, zero_add]
/-
**TrivSqZeroExt.inl_mul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_mul_eq_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMu
lAction Rᵐᵒᵖ M] (r : R) (x : tsze R M) : inl r * x = r •> x
参数：r : R；x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem inl_mul_eq_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (r : R) (x : tsze R M) :
    inl r * x = r •> x :=
  ext rfl (by dsimp; rw [smul_zero, add_zero])
/-
**TrivSqZeroExt.mul_inl_eq_op_smul** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mul_inl_eq_op_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [Distri
bMulAction Rᵐᵒᵖ M] (x : tsze R M) (r : R) : x * inl r = x <• r
参数：x : tsze R M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mul_inl_eq_op_smul [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (r : R) :
    x * inl r = x <• r :=
  ext rfl (by dsimp; rw [smul_zero, zero_add])
/-
**TrivSqZeroExt.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mulOneClass [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAct
ion Rᵐᵒᵖ M] : MulOneClass (tsze R M) where one_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulOneClass [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    MulOneClass (tsze R M) where
  one_mul := fun x =>
    ext (one_mul x.1) <|
      show (1 : R) •> x.2 + (0 : M) <• x.1 = x.2 by rw [one_smul, smul_zero, add_zero]
  mul_one := fun x =>
    ext (mul_one x.1) <|
      show x.1 • (0 : M) + x.2 <• (1 : R) = x.2 by rw [smul_zero, zero_add, op_one, one_smul]
/-
**TrivSqZeroExt.addMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addMonoidWithOne [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (ts
ze R M) where natCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoidWithOne [AddMonoidWithOne R] [AddMonoid M] : AddMonoidWithOne (tsze R M) where
  natCast := fun n => inl n
  natCast_zero := by simp [Nat.cast]
  natCast_succ := fun _ => by ext <;> simp [Nat.cast]

@[simp]
/-
**TrivSqZeroExt.fst_natCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (n : tsze R M).
fst = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).fst = n :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (n : tsze R M).
snd = 0
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (n : tsze R M).snd = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.inl_natCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_natCast [AddMonoidWithOne R] [AddMonoid M] (n : Nat) : (inl n : tsze R
 M) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_natCast [AddMonoidWithOne R] [AddMonoid M] (n : ℕ) : (inl n : tsze R M) = n :=
  rfl
/-
**TrivSqZeroExt.addGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：addGroupWithOne [AddGroupWithOne R] [AddGroup M] : AddGroupWithOne (tsze R
 M) where intCast
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addGroupWithOne [AddGroupWithOne R] [AddGroup M] : AddGroupWithOne (tsze R M) where
  intCast := fun z => inl z
  intCast_ofNat := fun _n => ext (Int.cast_natCast _) rfl
  intCast_negSucc := fun _n => ext (Int.cast_negSucc _) neg_zero.symm

@[simp]
/-
**TrivSqZeroExt.fst_intCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (z : tsze R M).fs
t = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).fst = z :=
  rfl

@[simp]
/-
**TrivSqZeroExt.snd_intCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (z : tsze R M).sn
d = 0
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (z : tsze R M).snd = 0 :=
  rfl

@[simp]
/-
**TrivSqZeroExt.inl_intCast** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_intCast [AddGroupWithOne R] [AddGroup M] (z : Int) : (inl z : tsze R M
) = z
参数：z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inl_intCast [AddGroupWithOne R] [AddGroup M] (z : ℤ) : (inl z : tsze R M) = z :=
  rfl
/-
**TrivSqZeroExt.nonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：nonAssocSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ 
M] : NonAssocSemiring (tsze R M) where zero_mul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocSemiring [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocSemiring (tsze R M) where
  zero_mul := fun x =>
    ext (zero_mul x.1) <|
      show (0 : R) •> x.2 + (0 : M) <• x.1 = 0 by rw [zero_smul, zero_add, smul_zero]
  mul_zero := fun x =>
    ext (mul_zero x.1) <|
      show x.1 • (0 : M) + (0 : Rᵐᵒᵖ) • x.2 = 0 by rw [smul_zero, zero_add, zero_smul]
  left_distrib := fun x₁ x₂ x₃ =>
    ext (mul_add x₁.1 x₂.1 x₃.1) <|
      show
        x₁.1 •> (x₂.2 + x₃.2) + x₁.2 <• (x₂.1 + x₃.1) =
          x₁.1 •> x₂.2 + x₁.2 <• x₂.1 + (x₁.1 •> x₃.2 + x₁.2 <• x₃.1)
        by simp_rw [smul_add, MulOpposite.op_add, add_smul, add_add_add_comm]
  right_distrib := fun x₁ x₂ x₃ =>
    ext (add_mul x₁.1 x₂.1 x₃.1) <|
      show
        (x₁.1 + x₂.1) •> x₃.2 + (x₁.2 + x₂.2) <• x₃.1 =
          x₁.1 •> x₃.2 + x₁.2 <• x₃.1 + (x₂.1 •> x₃.2 + x₂.2 <• x₃.1)
        by simp_rw [add_smul, smul_add, add_add_add_comm]
/-
**TrivSqZeroExt.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Ring R] →       [inst_1 : AddC
ommGroup M] → [_root_.Module R M] → [_root_.Module Rᵐᵒᵖ M] → NonAssocRing (TrivS
qZeroExt R M)
参数：TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance nonAssocRing [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] :
    NonAssocRing (tsze R M) where

/-- In the general non-commutative case, the power operator is

$$\begin{align}
(r + m)^n &= r^n + r^{n-1}m + r^{n-2}mr + \cdots + rmr^{n-2} + mr^{n-1} \\
          & =r^n + \sum_{i = 0}^{n - 1} r^{(n - 1) - i} m r^{i}
\end{align}$$

In the commutative case this becomes the simpler $(r + m)^n = r^n + nr^{n-1}m$.
-/
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In the general non-commutative case, the power operator is

$$\begin{align}
(r + m)^n &= r^n + r^{n-1}m + r^{n-2}mr + \cdots + rmr^{n-2} + mr^{n-1} \\
          & =r^n + \sum_{i = 0}^{n - 1} r^{(n - 1) - i} m r^{i}
\end{align}$$

In the commutative case this becomes the simpler $(r + m)^n = r^n + nr^{n-1}m$.
-/
instance [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] :
    Pow (tsze R M) ℕ :=
  ⟨fun x n =>
    ⟨x.fst ^ n, ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum⟩⟩

@[simp]
/-
**TrivSqZeroExt.fst_pow** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction 
Rᵐᵒᵖ M] (x : tsze R M) (n : Nat) : fst (x ^ n) = x.fst ^ n
参数：x : tsze R M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) : fst (x ^ n) = x.fst ^ n :=
  rfl
/-
**TrivSqZeroExt.snd_pow_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMul
Action Rᵐᵒᵖ M] (x : tsze R M) (n : Nat) : snd (x ^ n) = ((List.range n).map fun 
i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum
参数：x : tsze R M；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_pow_eq_sum [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    (x : tsze R M) (n : ℕ) :
    snd (x ^ n) = ((List.range n).map fun i => x.fst ^ (n.pred - i) •> x.snd <• x.fst ^ i).sum :=
  rfl
/-
**TrivSqZeroExt.snd_pow_of_smul_comm** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M] [Dist
ribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : Nat) (h : x.sn
d <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • x.fst ^ n.pred •> x.snd
参数：x : tsze R M；n : Nat；h : x.snd <• x.fst = x.fst •> x.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `_private.Mathlib.Algebra.TrivSqZeroExt.Basic.0.TrivSqZeroExt.snd_pow_of_
smul_comm.aux`：∀ {R : Type u} {M : Type v} [inst : Monoid R] [inst_1 : AddMonoid
 M] [inst_2 : DistribMulAction R M]   [inst_3 : DistribMulAction Rᵐᵒᵖ M] [S…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Nat.pred_zero`：Nat.pred 0 = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `List.range_zero`：List.range 0 = []
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.sum_nil`：∀ {α : Type u} [inst : Add α] [inst_1 : Zero α], [].sum = 
0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.sum_eq_card_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (l : List 
M) (m : M), (∀ x ∈ l, x = m) → l.sum = l.length • m
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
-/
theorem snd_pow_of_smul_comm [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • x.fst ^ n.pred •> x.snd := by
  simp_rw [snd_pow_eq_sum, ← smul_comm (_ : R) (_ : Rᵐᵒᵖ), aux, smul_smul, ← pow_add]
  match n with
  | 0 => rw [Nat.pred_zero, pow_zero, List.range_zero, zero_smul, List.map_nil, List.sum_nil]
  | (Nat.succ n) =>
    simp_rw [Nat.pred_succ]
    exact (List.sum_eq_card_nsmul _ (x.fst ^ n • x.snd) (by grind)).trans
      (by rw [List.length_map, List.length_range])
where
  aux : ∀ n : ℕ, x.snd <• x.fst ^ n = x.fst ^ n •> x.snd := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, op_mul, mul_smul, mul_smul, ← h, smul_comm (_ : R) (op x.fst) x.snd, ih]
/-
**TrivSqZeroExt.snd_pow_of_smul_comm'** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M] [Dis
tribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : Nat) (h : x.s
nd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred)
参数：x : tsze R M；n : Nat；h : x.snd <• x.fst = x.fst •> x.snd。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.snd_pow_of_smul_comm`：snd_pow_of_smul_comm [Monoid R] [Add
Monoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ
 M] (x : tsze R M) (n : …
· 使用定理 `_private.Mathlib.Algebra.TrivSqZeroExt.Basic.0.TrivSqZeroExt.snd_pow_of_
smul_comm.aux`：∀ {R : Type u} {M : Type v} [inst : Monoid R] [inst_1 : AddMonoid
 M] [inst_2 : DistribMulAction R M]   [inst_3 : DistribMulAction Rᵐᵒᵖ M] [S…
-/
theorem snd_pow_of_smul_comm' [Monoid R] [AddMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (x : tsze R M) (n : ℕ)
    (h : x.snd <• x.fst = x.fst •> x.snd) : snd (x ^ n) = n • (x.snd <• x.fst ^ n.pred) := by
  rw [snd_pow_of_smul_comm _ _ h, snd_pow_of_smul_comm.aux _ h]

@[simp]
/-
**TrivSqZeroExt.snd_pow** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAct
ion Rᵐᵒᵖ M] [IsCentralScalar R M] (x : tsze R M) (n : Nat) : snd (x ^ n) = n • x
.fst ^ n.pred • x.snd
参数：x : tsze R M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.snd_pow_of_smul_comm`：snd_pow_of_smul_comm [Monoid R] [Add
Monoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ
 M] (x : tsze R M) (n : …
· 使用定理 `SMulCommClass.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul N α] [inst_2 : SMul Nᵐᵒᵖ α]   [IsCentralScalar N
 α] [SMulCom…
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
theorem snd_pow [CommMonoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [IsCentralScalar R M] (x : tsze R M) (n : ℕ) : snd (x ^ n) = n • x.fst ^ n.pred • x.snd :=
  snd_pow_of_smul_comm _ _ (op_smul_eq_smul _ _)

@[simp]
/-
**TrivSqZeroExt.inl_pow** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction 
Rᵐᵒᵖ M] (r : R) (n : Nat) : (inl r ^ n : tsze R M) = inl (r ^ n)
参数：r : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.length_range`：∀ {n : ℕ}, (List.range n).length = n
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_pow [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R)
    (n : ℕ) : (inl r ^ n : tsze R M) = inl (r ^ n) :=
  ext rfl <| by simp [snd_pow_eq_sum, List.map_const']
/-
**TrivSqZeroExt.monoid** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：monoid [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction R
ᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] : Monoid (tsze R M) where mul_assoc
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] : Monoid (tsze R M) where
  mul_assoc := fun x y z =>
    ext (mul_assoc x.1 y.1 z.1) <|
      show
        (x.1 * y.1) •> z.2 + (x.1 •> y.2 + x.2 <• y.1) <• z.1 =
          x.1 •> (y.1 •> z.2 + y.2 <• z.1) + x.2 <• (y.1 * z.1)
        by simp_rw [smul_add, ← mul_smul, add_assoc, smul_comm, op_mul]
  npow := fun n x => x ^ n
  npow_zero := fun x => ext (pow_zero x.fst) (by simp [snd_pow_eq_sum])
  npow_succ := fun n x =>
    ext (pow_succ _ _)
      (by
        simp_rw [snd_mul, snd_pow_eq_sum, Nat.pred_succ]
        cases n
        · simp [List.range_succ]
        rw [List.sum_range_succ']
        simp only [pow_zero, op_one, Nat.sub_zero, one_smul, Nat.succ_sub_succ_eq_sub, fst_pow,
          Nat.pred_succ, List.smul_sum, List.map_map, Function.comp_def]
        simp_rw [← smul_comm (_ : R) (_ : Rᵐᵒᵖ), smul_smul, pow_succ]
        rfl)
/-
**TrivSqZeroExt.fst_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulA
ction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.m
ap fst).prod
参数：l : List (tsze R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `TrivSqZeroExt.fst_one`：fst_one [One R] [Zero M] : (1 : tsze R M).fst = 1
· 使用定理 `TrivSqZeroExt.fst_mul`：fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] 
(x₁ x₂ : tsze R M) : (x₁ * x₂).fst = x₁.fst * x₂.fst
-/
theorem fst_list_prod [Monoid R] [AddMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.fst = (l.map fst).prod :=
  map_list_prod ({ toFun := fst, map_one' := fst_one, map_mul' := fst_mul } : tsze R M →* R) _
/-
**TrivSqZeroExt.semiring** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Semiring R] →       [inst_1 : 
AddCommMonoid M] →         [inst_2 : _root_.Module R M] →           [inst_3 : _r
oot_.Module Rᵐᵒᵖ M] → [SMulCommClass R Rᵐᵒᵖ M] → Semiring (TrivSqZeroExt R M)
参数：TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semiring [Semiring R] [AddCommMonoid M]
    [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] : Semiring (tsze R M) where

/-- The second element of a product $\prod_{i=0}^n (r_i + m_i)$ is a sum of terms of the form
$r_0\cdots r_{i-1}m_ir_{i+1}\cdots r_n$. -/
/-
**TrivSqZeroExt.snd_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_list_prod [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [Distrib
MulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) : l.prod.snd = 
(l.zipIdx.map fun x : tsze R M × Nat => ((l.map fst).take x.2).prod •> x.fst.snd
 <• ((l.map fst).drop x.2.succ).prod).sum
参数：l : List (tsze R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.drop_nil`：∀ {α : Type u} {i : ℕ}, List.drop i [] = []
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.zipIdx_cons'`：∀ {α : Type u_1} {i : ℕ} {x : α} {xs : List α},   (x 
:: xs).zipIdx i = (x, i) :: List.map (Prod.map id fun x => x + 1) (xs.zipIdx i)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `TrivSqZeroExt.fst_list_prod`：fst_list_prod [Monoid R] [AddMonoid M] [Dis
tribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] (l : List 
(tsze R M)) : l.p…
· 使用定理 `List.smul_sum`：List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (
r • ·)).sum
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The second element of a product $\prod_{i=0}^n (r_i + m_i)$ is a sum of terms of
 the form
$r_0\cdots r_{i-1}m_ir_{i+1}\cdots r_n$.
-/
theorem snd_list_prod [Monoid R] [AddCommMonoid M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M]
    [SMulCommClass R Rᵐᵒᵖ M] (l : List (tsze R M)) :
    l.prod.snd =
      (l.zipIdx.map fun x : tsze R M × ℕ =>
          ((l.map fst).take x.2).prod •> x.fst.snd <• ((l.map fst).drop x.2.succ).prod).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.zipIdx_cons']
    simp_rw [List.map_cons, List.map_map, Function.comp_def, Prod.map_snd, Prod.map_fst, id,
      List.take_zero, List.take_succ_cons, List.prod_nil, List.prod_cons, snd_mul, one_smul,
      List.drop, mul_smul, List.sum_cons, fst_list_prod, ih, List.smul_sum, List.map_map,
      ← smul_comm (_ : R) (_ : Rᵐᵒᵖ)]
    exact add_comm _ _
/-
**TrivSqZeroExt.ring** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : Ring R] →       [inst_1 : AddC
ommGroup M] →         [inst_2 : _root_.Module R M] →           [inst_3 : _root_.
Module Rᵐᵒᵖ M] → [SMulCommClass R Rᵐᵒᵖ M] → Ring (TrivSqZeroExt R M)
参数：TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ring [Ring R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M] :
    Ring (tsze R M) where
/-
**TrivSqZeroExt.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：commMonoid [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M] [Distri
bMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] : CommMonoid (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid [CommMonoid R] [AddCommMonoid M] [DistribMulAction R M]
    [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] : CommMonoid (tsze R M) :=
  { TrivSqZeroExt.monoid with
    mul_comm := fun x₁ x₂ =>
      ext (mul_comm x₁.1 x₂.1) <|
        show x₁.1 •> x₂.2 + x₁.2 <• x₂.1 = x₂.1 •> x₁.2 + x₂.2 <• x₁.1 by
          rw [op_smul_eq_smul, op_smul_eq_smul, add_comm] }
/-
**TrivSqZeroExt.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : CommSemiring R] →       [inst_
1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] →           [inst_3 
: _root_.Module Rᵐᵒᵖ M] → [IsCentralScalar R M] → CommSemiring (TrivSqZeroExt R 
M)
参数：TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commSemiring [CommSemiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M]
    [IsCentralScalar R M] : CommSemiring (tsze R M) where
/-
**TrivSqZeroExt.commRing** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：{R : Type u} →   {M : Type v} →     [inst : CommRing R] →       [inst_1 : 
AddCommGroup M] →         [inst_2 : _root_.Module R M] →           [inst_3 : _ro
ot_.Module Rᵐᵒᵖ M] → [IsCentralScalar R M] → CommRing (TrivSqZeroExt R M)
参数：TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commRing [CommRing R] [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    CommRing (tsze R M) where

variable (R M)

/-- The canonical inclusion of rings `R → TrivSqZeroExt R M`. -/
@[simps apply]
/-
**TrivSqZeroExt.inlHom** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inlHom [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] : R ->+
* tsze R M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical inclusion of rings `R → TrivSqZeroExt R M`.
-/
def inlHom [Semiring R] [AddCommMonoid M] [Module R M] [Module Rᵐᵒᵖ M] : R →+* tsze R M where
  toFun := inl
  map_one' := inl_one M
  map_mul' := inl_mul M
  map_zero' := inl_zero M
  map_add' := inl_add M

end Mul

section Inv
variable {R : Type u} {M : Type v}
variable [Neg M] [Inv R] [SMul Rᵐᵒᵖ M] [SMul R M]

/-- Inversion of the trivial-square-zero extension, sending $r + m$ to $r^{-1} - r^{-1}mr^{-1}$.

Strictly this is only a _two_-sided inverse when the left and right actions associate. -/
/-
**TrivSqZeroExt.instInv** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：instInv : Inv (tsze R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inversion of the trivial-square-zero extension, sending $r + m$ to $r^{-1} - r^{
-1}mr^{-1}$.

Strictly this is only a _two_-sided inverse when the left and right actions asso
ciate.
-/
instance instInv : Inv (tsze R M) :=
  ⟨fun b => (b.1⁻¹, -(b.1⁻¹ •> b.2 <• b.1⁻¹))⟩
/-
**TrivSqZeroExt.fst_inv** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_1 : Inv R] [inst_2 : SMul
 Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M), x⁻¹.fst = x.fst⁻¹
参数：x : TrivSqZeroExt R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem fst_inv (x : tsze R M) : fst x⁻¹ = (fst x)⁻¹ :=
  rfl
/-
**TrivSqZeroExt.snd_inv** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_1 : Inv R] [inst_2 : SMul
 Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M), x⁻¹.snd = -(MulOpposite.
op x.fst⁻¹ • x.fst⁻¹ • x.snd)
参数：x : TrivSqZeroExt R M；MulOpposite.op x.fst⁻¹ • x.fst⁻¹ • x.snd。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem snd_inv (x : tsze R M) : snd x⁻¹ = -((fst x)⁻¹ •> snd x <• (fst x)⁻¹) :=
  rfl

end Inv

/-! This section is heavily inspired by analogous results about matrices. -/
section Invertible
variable {R : Type u} {M : Type v}
variable [AddCommGroup M] [Semiring R] [Module Rᵐᵒᵖ M] [Module R M]

/-- `x.fst : R` is invertible when `x : tzre R M` is. -/
/-
**TrivSqZeroExt.invertibleFstOfInvertible** 是 Mathlib 中的一个缩写定义，位于命名空间 `TrivSqZer
oExt`。
形式化陈述：invertibleFstOfInvertible (x : tsze R M) [Invertible x] : Invertible x.fst
 where invOf
参数：x : tsze R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x.fst : R` is invertible when `x : tzre R M` is.
-/
abbrev invertibleFstOfInvertible (x : tsze R M) [Invertible x] : Invertible x.fst where
  invOf := (⅟x).fst
  invOf_mul_self := by rw [← fst_mul, invOf_mul_self, fst_one]
  mul_invOf_self := by rw [← fst_mul, mul_invOf_self, fst_one]
/-
**TrivSqZeroExt.fst_invOf** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).fst = ⅟(
x.fst)
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem fst_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).fst = ⅟(x.fst) := by
  let := invertibleFstOfInvertible x
  convert! (rfl : _ = ⅟x.fst)
/-
**TrivSqZeroExt.mul_left_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mul_left_eq_one (r : R) (x : tsze R M) (h : r * x.fst = 1) : (inl r + inr 
(-((r •> x.snd) <• r))) * x = 1
参数：r : R；x : tsze R M；h : r * x.fst = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `op_smul_op_smul`：op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b
 <• (a₁ * a₂)
· 使用定理 `MulOpposite.op_one`：∀ {α : Type u_1} [inst : One α], MulOpposite.op 1 = 
1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
-/
theorem mul_left_eq_one (r : R) (x : tsze R M) (h : r * x.fst = 1) :
    (inl r + inr (-((r •> x.snd) <• r))) * x = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, op_smul_op_smul, h, op_one, one_smul,
      add_neg_cancel]
/-
**TrivSqZeroExt.mul_right_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：mul_right_eq_one (x : tsze R M) (r : R) (h : x.fst * r = 1) : x * (inl r +
 inr (-(r •> (x.snd <• r)))) = 1
参数：x : tsze R M；r : R；h : x.fst * r = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
theorem mul_right_eq_one (x : tsze R M) (r : R) (h : x.fst * r = 1) :
    x * (inl r + inr (-(r •> (x.snd <• r)))) = 1 := by
  ext <;> dsimp
  · rw [add_zero, h]
  · rw [add_zero, zero_add, smul_neg, smul_smul, h, one_smul, neg_add_cancel]

variable [SMulCommClass R Rᵐᵒᵖ M]

set_option backward.isDefEq.respectTransparency false in
/-- `x : tzre R M` is invertible when `x.fst : R` is. -/
/-
**TrivSqZeroExt.invertibleOfInvertibleFst** 是 Mathlib 中的一个缩写定义，位于命名空间 `TrivSqZer
oExt`。
形式化陈述：invertibleOfInvertibleFst (x : tsze R M) [Invertible x.fst] : Invertible x
 where invOf
参数：x : tsze R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x : tzre R M` is invertible when `x.fst : R` is.
-/
abbrev invertibleOfInvertibleFst (x : tsze R M) [Invertible x.fst] : Invertible x where
  invOf := (⅟x.fst, -(⅟x.fst •> x.snd <• ⅟x.fst))
  invOf_mul_self := by
    convert! mul_left_eq_one _ _ (invOf_mul_self x.fst)
    ext <;> simp
  mul_invOf_self := by
    convert! mul_right_eq_one _ _ (mul_invOf_self x.fst)
    ext <;> simp [smul_comm]
/-
**TrivSqZeroExt.snd_invOf** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] : (⅟x).snd = -(
⅟x.fst •> x.snd <• ⅟x.fst)
参数：x : tsze R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Invertible.congr`：Invertible.congr [Invertible a] [Invertible b] (h : a 
= b) : ⅟a = ⅟b
-/
theorem snd_invOf (x : tsze R M) [Invertible x] [Invertible x.fst] :
    (⅟x).snd = -(⅟x.fst •> x.snd <• ⅟x.fst) := by
  let := invertibleOfInvertibleFst x
  convert! congr_arg (TrivSqZeroExt.snd (R := R) (M := M)) (_ : _ = ⅟x)
  convert! rfl

/-- Together `TrivSqZeroExt.detInvertibleOfInvertible` and `TrivSqZeroExt.invertibleOfDetInvertible`
form an equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
/-
**TrivSqZeroExt.invertibleEquivInvertibleFst** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZe
roExt`。
形式化陈述：invertibleEquivInvertibleFst (x : tsze R M) : Invertible x ≃ Invertible x.
fst where toFun _
参数：x : tsze R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Together `TrivSqZeroExt.detInvertibleOfInvertible` and `TrivSqZeroExt.invertible
OfDetInvertible`
form an equivalence, although both sides of the equiv are subsingleton anyway.
-/
def invertibleEquivInvertibleFst (x : tsze R M) : Invertible x ≃ Invertible x.fst where
  toFun _ := invertibleFstOfInvertible x
  invFun _ := invertibleOfInvertibleFst x
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

/-- When lowered to a prop, `Matrix.invertibleEquivInvertibleFst` forms an `iff`. -/
/-
**TrivSqZeroExt.isUnit_iff_isUnit_fst** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_iff_isUnit_fst {x : tsze R M} : IsUnit x ↔ IsUnit x.fst
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
When lowered to a prop, `Matrix.invertibleEquivInvertibleFst` forms an `iff`.
-/
theorem isUnit_iff_isUnit_fst {x : tsze R M} : IsUnit x ↔ IsUnit x.fst := by
  simp only [← nonempty_invertible_iff_isUnit, (invertibleEquivInvertibleFst x).nonempty_congr]

@[simp]
/-
**TrivSqZeroExt.isUnit_inl_iff** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_inl_iff {r : R} : IsUnit (inl r : tsze R M) ↔ IsUnit r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.isUnit_iff_isUnit_fst`：isUnit_iff_isUnit_fst {x : tsze R M
} : IsUnit x ↔ IsUnit x.fst
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isUnit_inl_iff {r : R} : IsUnit (inl r : tsze R M) ↔ IsUnit r := by
  rw [isUnit_iff_isUnit_fst, fst_inl]

@[simp]
/-
**TrivSqZeroExt.isUnit_inr_iff** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_inr_iff {m : M} : IsUnit (inr m : tsze R M) ↔ Subsingleton R
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_inr_iff {m : M} : IsUnit (inr m : tsze R M) ↔ Subsingleton R := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inr, isUnit_zero_iff, subsingleton_iff_zero_eq_one]

end Invertible

section DivisionSemiring
variable {R : Type u} {M : Type v}
variable [DivisionSemiring R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

/-
**TrivSqZeroExt.inv_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] (r : R), 
(TrivSqZeroExt.inl r)⁻¹ = TrivSqZeroExt.inl r⁻¹
参数：r : R；TrivSqZeroExt.inl r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.fst_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.fst = …
· 使用定理 `TrivSqZeroExt.fst_inl`：fst_inl [Zero M] (r : R) : (inl r : tsze R M).fst
 = r
· 使用定理 `TrivSqZeroExt.snd_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.snd = …
· 使用定理 `TrivSqZeroExt.snd_inl`：snd_inl [Zero M] (r : R) : (inl r : tsze R M).snd
 = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
protected theorem inv_inl (r : R) :
    (inl r)⁻¹ = (inl (r⁻¹ : R) : tsze R M) := by
  ext
  · rw [fst_inv, fst_inl, fst_inl]
  · rw [snd_inv, fst_inl, snd_inl, snd_inl, smul_zero, smul_zero, neg_zero]

@[simp]
/-
**TrivSqZeroExt.inv_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inv_inr (m : M) : (inr m)⁻¹ = (0 : tsze R M)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.fst_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.fst = …
· 使用定理 `TrivSqZeroExt.fst_inr`：fst_inr [Zero R] (m : M) : (inr m : tsze R M).fst
 = 0
· 使用定理 `TrivSqZeroExt.fst_zero`：fst_zero [Zero R] [Zero M] : (0 : tsze R M).fst 
= 0
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `TrivSqZeroExt.snd_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.snd = …
· 使用定理 `TrivSqZeroExt.snd_inr`：snd_inr [Zero R] (m : M) : (inr m : tsze R M).snd
 = m
· 使用定理 `MulOpposite.op_zero`：∀ {α : Type u_1} [inst : Zero α], MulOpposite.op 0 
= 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `TrivSqZeroExt.snd_zero`：snd_zero [Zero R] [Zero M] : (0 : tsze R M).snd 
= 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem inv_inr (m : M) : (inr m)⁻¹ = (0 : tsze R M) := by
  ext
  · rw [fst_inv, fst_inr, fst_zero, inv_zero]
  · rw [snd_inv, snd_inr, fst_inr, inv_zero, op_zero, zero_smul, snd_zero, neg_zero]

@[simp]
/-
**TrivSqZeroExt.inv_zero** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M], 0⁻¹ = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_zero`：inl_zero [Zero R] [Zero M] : (inl 0 : tsze R M) 
= 0
· 使用定理 `TrivSqZeroExt.inv_inl`：∀ {R : Type u} {M : Type v} [inst : DivisionSemir
ing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _ro
ot_.Module …
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
-/
protected theorem inv_zero : (0 : tsze R M)⁻¹ = (0 : tsze R M) := by
  rw [← inl_zero, TrivSqZeroExt.inv_inl, inv_zero]

@[simp]
/-
**TrivSqZeroExt.inv_one** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M], 1⁻¹ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_one`：inl_one [One R] [Zero M] : (inl 1 : tsze R M) = 1
· 使用定理 `TrivSqZeroExt.inv_inl`：∀ {R : Type u} {M : Type v} [inst : DivisionSemir
ing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _ro
ot_.Module …
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
-/
protected theorem inv_one : (1 : tsze R M)⁻¹ = (1 : tsze R M) := by
  rw [← inl_one, TrivSqZeroExt.inv_inl, inv_one]
/-
**TrivSqZeroExt.inv_mul_cancel** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] {x : Triv
SqZeroExt R M}, x.fst ≠ 0 → x⁻¹ * x = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `TrivSqZeroExt.mul_left_eq_one`：mul_left_eq_one (r : R) (x : tsze R M) (h
 : r * x.fst = 1) : (inl r + inr (-((r •> x.snd) <• r))) * x = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
-/
protected theorem inv_mul_cancel {x : tsze R M} (hx : fst x ≠ 0) : x⁻¹ * x = 1 := by
  convert mul_left_eq_one _ _ (_root_.inv_mul_cancel₀ hx)
  ext <;> simp

variable [SMulCommClass R Rᵐᵒᵖ M]
/-
**TrivSqZeroExt.invOf_eq_inv** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] [SMulComm
Class R Rᵐᵒᵖ M] (x : TrivSqZeroExt R M) [inst_5 : Invertible x], ⅟x = x⁻¹
参数：x : TrivSqZeroExt R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.fst_invOf`：fst_invOf (x : tsze R M) [Invertible x] [Invert
ible x.fst] : (⅟x).fst = ⅟(x.fst)
· 使用定理 `invOf_eq_inv`：invOf_eq_inv (a : α) [Invertible a] : ⅟a = a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TrivSqZeroExt.snd_invOf`：snd_invOf (x : tsze R M) [Invertible x] [Invert
ible x.fst] : (⅟x).snd = -(⅟x.fst •> x.snd <• ⅟x.fst)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
@[simp] theorem invOf_eq_inv (x : tsze R M) [Invertible x] : ⅟x = x⁻¹ := by
  let := invertibleFstOfInvertible x
  ext <;> simp [fst_invOf, snd_invOf]
/-
**TrivSqZeroExt.mul_inv_cancel** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] [SMulComm
Class R Rᵐᵒᵖ M] {x : TrivSqZeroExt R M}, x.fst ≠ 0 → x * x⁻¹ = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.invOf_eq_inv`：∀ {R : Type u} {M : Type v} [inst : Division
Semiring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 
: _root_.Module …
· 使用定理 `mul_invOf_self`：mul_invOf_self [Mul α] [One α] (a : α) [Invertible a] : 
a * ⅟a = 1
-/
protected theorem mul_inv_cancel {x : tsze R M} (hx : fst x ≠ 0) : x * x⁻¹ = 1 := by
  have : Invertible x.fst := Units.invertible (.mk0 _ hx)
  have := invertibleOfInvertibleFst x
  rw [← invOf_eq_inv, mul_invOf_self]
/-
**TrivSqZeroExt.mul_inv_rev** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] [SMulComm
Class R Rᵐᵒᵖ M] (a b : TrivSqZeroExt R M), (a * b)⁻¹ = b⁻¹ * a⁻¹
参数：a b : TrivSqZeroExt R M；a * b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.fst_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.fst = …
· 使用定理 `TrivSqZeroExt.fst_mul`：fst_mul [Mul R] [Add M] [SMul R M] [SMul Rᵐᵒᵖ M] 
(x₁ x₂ : tsze R M) : (x₁ * x₂).fst = x₁.fst * x₂.fst
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用引理 `op_smul_op_smul`：op_smul_op_smul (b : β) (a₁ a₂ : α) : b <• a₁ <• a₂ = b
 <• (a₁ * a₂)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inv_mul_cancel_right₀`：inv_mul_cancel_right₀ (h : b != 0) (a : G₀) : a *
 b⁻¹ * b = a
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
-/
protected theorem mul_inv_rev (a b : tsze R M) :
    (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  ext
  · rw [fst_inv, fst_mul, fst_mul, mul_inv_rev, fst_inv, fst_inv]
  · simp only [snd_inv, snd_mul, fst_mul, fst_inv]
    simp only [smul_neg, smul_add]
    simp_rw [mul_inv_rev, smul_comm (_ : R), op_smul_op_smul, smul_smul, add_comm, neg_add]
    obtain ha0 | ha := eq_or_ne (fst a) 0
    · simp [ha0]
    obtain hb0 | hb := eq_or_ne (fst b) 0
    · simp [hb0]
    rw [inv_mul_cancel_right₀ ha, mul_inv_cancel_left₀ hb]
/-
**TrivSqZeroExt.inv_inv** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionSemiring R] [inst_1 : AddCommG
roup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] [SMulComm
Class R Rᵐᵒᵖ M] {x : TrivSqZeroExt R M}, x.fst ≠ 0 → x⁻¹⁻¹ = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `TrivSqZeroExt.mul_inv_cancel`：∀ {R : Type u} {M : Type v} [inst : Divisi
onSemiring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_
3 : _root_.Module …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `TrivSqZeroExt.fst_inv`：∀ {R : Type u} {M : Type v} [inst : Neg M] [inst_
1 : Inv R] [inst_2 : SMul Rᵐᵒᵖ M] [inst_3 : SMul R M]   (x : TrivSqZeroExt R M),
 x⁻¹.fst = …
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
protected theorem inv_inv {x : tsze R M} (hx : fst x ≠ 0) : x⁻¹⁻¹ = x :=
  -- adapted from `Matrix.nonsing_inv_nonsing_inv`
  calc
    x⁻¹⁻¹ = 1 * x⁻¹⁻¹ := by rw [one_mul]
    _ = x * x⁻¹ * x⁻¹⁻¹ := by rw [TrivSqZeroExt.mul_inv_cancel hx]
    _ = x := by
      rw [mul_assoc, TrivSqZeroExt.mul_inv_cancel, mul_one]
      rw [fst_inv]
      apply inv_ne_zero hx

@[simp]
/-
**TrivSqZeroExt.isUnit_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：isUnit_inv_iff {x : tsze R M} : IsUnit x⁻¹ ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isUnit_inv_iff {x : tsze R M} : IsUnit x⁻¹ ↔ IsUnit x := by
  simp_rw [isUnit_iff_isUnit_fst, fst_inv, isUnit_iff_ne_zero, ne_eq, inv_eq_zero]

end DivisionSemiring

section DivisionRing
variable {R : Type u} {M : Type v}
variable [DivisionRing R] [AddCommGroup M] [Module Rᵐᵒᵖ M] [Module R M]

/-
**TrivSqZeroExt.inv_neg** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : DivisionRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module Rᵐᵒᵖ M]   [inst_3 : _root_.Module R M] {x : TrivSqZe
roExt R M}, (-x)⁻¹ = -x⁻¹
参数：-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.ext`：ext {x y : tsze R M} (h1 : x.fst = y.fst) (h2 : x.snd
 = y.snd) : x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
protected theorem inv_neg {x : tsze R M} : (-x)⁻¹ = -(x⁻¹) := by
  ext <;> simp [inv_neg]

end DivisionRing

section Algebra

variable (S : Type*) (R R' : Type u) (M : Type v)
variable [CommSemiring S] [Semiring R] [CommSemiring R'] [AddCommMonoid M]
variable [Algebra S R] [Module S M] [Module R M] [Module Rᵐᵒᵖ M] [SMulCommClass R Rᵐᵒᵖ M]
variable [IsScalarTower S R M] [IsScalarTower S Rᵐᵒᵖ M]
variable [Module R' M] [Module R'ᵐᵒᵖ M] [IsCentralScalar R' M]

/-
**TrivSqZeroExt.algebra'** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algebra' : Algebra S (tsze R M) where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance algebra' : Algebra S (tsze R M) where
  algebraMap := (TrivSqZeroExt.inlHom R M).comp (algebraMap S R)
  commutes' := fun s x =>
    ext (Algebra.commutes _ _) <|
      show algebraMap S R s •> x.snd + (0 : M) <• x.fst
          = x.fst •> (0 : M) + x.snd <• algebraMap S R s by
        rw [smul_zero, smul_zero, add_zero, zero_add]
        rw [Algebra.algebraMap_eq_smul_one, MulOpposite.op_smul, op_one, smul_assoc,
          one_smul, smul_assoc, one_smul]
  smul_def' := fun s x =>
    ext (Algebra.smul_def _ _) <|
      show s • x.snd = algebraMap S R s •> x.snd + (0 : M) <• x.fst by
        rw [smul_zero, add_zero, algebraMap_smul]

-- shortcut instance for the common case
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R' (tsze R' M) :=
  TrivSqZeroExt.algebra' _ _ _
/-
**TrivSqZeroExt.algebraMap_eq_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algebraMap_eq_inl : ⇑(algebraMap R' (tsze R' M)) = inl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
-/
theorem algebraMap_eq_inl : ⇑(algebraMap R' (tsze R' M)) = inl :=
  rfl
/-
**TrivSqZeroExt.algebraMap_eq_inlHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algebraMap_eq_inlHom : algebraMap R' (tsze R' M) = inlHom R' M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
-/
theorem algebraMap_eq_inlHom : algebraMap R' (tsze R' M) = inlHom R' M :=
  rfl
/-
**TrivSqZeroExt.algebraMap_eq_inl'** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algebraMap_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S
 R s)
参数：s : S。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMap_eq_inl' (s : S) : algebraMap S (tsze R M) s = inl (algebraMap S R s) :=
  rfl

/-- The canonical `S`-algebra projection `TrivSqZeroExt R M → R`. -/
@[simps]
/-
**TrivSqZeroExt.fstHom** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fstHom : tsze R M ->ₐ[S] R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `S`-algebra projection `TrivSqZeroExt R M → R`.
-/
def fstHom : tsze R M →ₐ[S] R where
  toFun := fst
  map_one' := fst_one
  map_mul' := fst_mul
  map_zero' := fst_zero (M := M)
  map_add' := fst_add
  commutes' _r := fst_inl M _

/-- `R'` as an algebra over `TrivSqZeroExt R' M`. Not an instance since it creates a different
`Algebra (TrivSqZeroExt R' M) (TrivSqZeroExt R' M)` instance from `TrivSqZeroExt.algebra'`. -/
/-
**TrivSqZeroExt.algebraBase** 是 Mathlib 中的一个缩写定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algebraBase : Algebra (tsze R' M) R' where algebraMap
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R'` as an algebra over `TrivSqZeroExt R' M`. Not an instance since it creates a
 different
`Algebra (TrivSqZeroExt R' M) (TrivSqZeroExt R' M)` instance from `TrivSqZeroExt
.algebra'`.
-/
abbrev algebraBase : Algebra (tsze R' M) R' where
  algebraMap := (fstHom R' R' M).toRingHom
  smul x r := x.fst * r
  commutes' _ _ := mul_comm ..
  smul_def' _ _ := rfl

attribute [local instance] algebraBase in
/-
**TrivSqZeroExt.** 是 Mathlib 中的一个实例，位于命名空间 `TrivSqZeroExt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsScalarTower R' (tsze R' M) R' where
  smul_assoc _ _ _ := mul_assoc ..

/-- The canonical `S`-algebra inclusion `R → TrivSqZeroExt R M`. -/
@[simps]
/-
**TrivSqZeroExt.inlAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：inlAlgHom : R ->ₐ[S] tsze R M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical `S`-algebra inclusion `R → TrivSqZeroExt R M`.
-/
def inlAlgHom : R →ₐ[S] tsze R M where
  toFun := inl
  map_one' := inl_one _
  map_mul' := inl_mul _
  map_zero' := inl_zero (M := M)
  map_add' := inl_add _
  commutes' _r := (algebraMap_eq_inl' _ _ _ _).symm

variable {R R' S M}
/-
**TrivSqZeroExt.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M ->ₐ[R'] A⦄ (h 
: forall m, f (inr m) = g (inr m)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `TrivSqZeroExt.linearMap_ext`：linearMap_ext {N} [Semiring S] [AddCommMono
id R] [AddCommMonoid M] [AddCommMonoid N] [Module S R] [Module S M] [Module S N]
 ⦃f g : tsze R M …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f g : tsze R' M →ₐ[R'] A⦄
    (h : ∀ m, f (inr m) = g (inr m)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (fun _r => (f.commutes _).trans (g.commutes _).symm) h

@[ext]
/-
**TrivSqZeroExt.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M ->ₐ[S] A⦄ (hinl
 : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R M)) (hinr : f.toLinearMap.co
mp (inrHom R M |>.restrictScalars S) = g.toLinearMap.comp (inrHom R M |>.restric
tScalars S)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgHom.toLinearMap_injective`：toLinearMap_injective : Function.Injective
 (toLinearMap : _ -> A ->ₗ[R] B)
· 使用定理 `TrivSqZeroExt.linearMap_ext`：linearMap_ext {N} [Semiring S] [AddCommMono
id R] [AddCommMonoid M] [AddCommMonoid N] [Module S R] [Module S M] [Module S N]
 ⦃f g : tsze R M …
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f g : tsze R M →ₐ[S] A⦄
    (hinl : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R M))
    (hinr : f.toLinearMap.comp (inrHom R M |>.restrictScalars S) =
      g.toLinearMap.comp (inrHom R M |>.restrictScalars S)) : f = g :=
  AlgHom.toLinearMap_injective <|
    linearMap_ext (AlgHom.congr_fun hinl) (LinearMap.congr_fun hinr)

variable {A : Type*} [Semiring A] [Algebra S A] [Algebra R' A]

set_option backward.defeqAttrib.useBackward true in
/--
Assemble an algebra morphism `TrivSqZeroExt R M →ₐ[S] A` from separate morphisms on `R` and `M`.

Namely, we require that for an algebra morphism `f : R →ₐ[S] A` and a linear map `g : M →ₗ[S] A`,
we have:

* `g x * g y = 0`: the elements of `M` continue to square to zero.
* `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: scalar multiplication on the left and
  right is sent to left- and right- multiplication by the image under `f`.

See `TrivSqZeroExt.liftEquiv` for this as an equiv; namely that any such algebra morphism can be
factored in this way.

When `R` is commutative, this can be invoked with `f = Algebra.ofId R A`, which satisfies `hfg` and
`hgf`. This version is captured as an equiv by `TrivSqZeroExt.liftEquivOfComm`. -/
/-
**TrivSqZeroExt.lift** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x * g y = 0) (h
fg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• r) = g x * f
 r) : tsze R M ->ₐ[S] A
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Assemble an algebra morphism `TrivSqZeroExt R M →ₐ[S] A` from separate morphisms
 on `R` and `M`.

Namely, we require that for an algebra morphism `f : R →ₐ[S] A` and a linear map
 `g : M →ₗ[S] A`,
we have:

* `g x * g y = 0`: the elements of `M` continue to square to zero.
* `g (r •> x) = f r * g x` and `g (x <• r) = g x * f r`: scalar multiplication o
n the left and
  right is sent to left- and right- multiplication by the image under `f`.

See `TrivSqZeroExt.liftEquiv` for this as an equiv; namely that any such algebra
 morphism can be
factored in this way.

When `R` is commutative, this can be invoked with `f = Algebra.ofId R A`, which 
satisfies `hfg` and
`hgf`. This version is captured as an equiv by `TrivSqZeroExt.liftEquivOfComm`.
-/
def lift (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) : tsze R M →ₐ[S] A :=
  AlgHom.ofLinearMap
    ((f.comp <| fstHom S R M).toLinearMap + g ∘ₗ (sndHom R M |>.restrictScalars S))
    (show f 1 + g (0 : M) = 1 by rw [map_zero, map_one, add_zero])
    (TrivSqZeroExt.ind fun r₁ m₁ =>
      TrivSqZeroExt.ind fun r₂ m₂ => by
        dsimp
        simp only [add_zero, zero_add, add_mul, mul_add, hg]
        rw [← map_mul, map_add, add_comm (g _), add_assoc, hfg, hgf])
/-
**TrivSqZeroExt.lift_def** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_def (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x * g y = 0
) (hfg : forall r x, g (r • x) = f r * g x) (hgf : forall r x, g (op r • x) = g 
x * f r) (x : tsze R M) : lift f g hg hfg hgf x = f x.fst + g x.snd
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r • x) = f r * g x；hgf : forall r x, g (op r • x) = g x * f r；x : tsze R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_def (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r • x) = f r * g x)
    (hgf : ∀ r x, g (op r • x) = g x * f r) (x : tsze R M) :
    lift f g hg hfg hgf x = f x.fst + g x.snd :=
  rfl

@[simp]
/-
**TrivSqZeroExt.lift_apply_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_apply_inl (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x * g
 y = 0) (hfg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• r)
 = g x * f r) (r : R) : lift f g hg hfg hgf (inl r) = f r
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem lift_apply_inl (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (r : R) :
    lift f g hg hfg hgf (inl r) = f r :=
  show f r + g 0 = f r by rw [map_zero, add_zero]

@[simp]
/-
**TrivSqZeroExt.lift_apply_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_apply_inr (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x * g
 y = 0) (hfg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• r)
 = g x * f r) (m : M) : lift f g hg hfg hgf (inr m) = g m
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem lift_apply_inr (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r)
    (m : M) :
    lift f g hg hfg hgf (inr m) = g m :=
  show f 0 + g m = g m by rw [map_zero, zero_add]

@[simp]
/-
**TrivSqZeroExt.lift_comp_inlHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_comp_inlHom (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x *
 g y = 0) (hfg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• 
r) = g x * f r) : (lift f g hg hfg hgf).comp (inlAlgHom S R M) = f
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `TrivSqZeroExt.lift_apply_inl`：lift_apply_inl (f : R ->ₐ[S] A) (g : M ->ₗ
[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r * g 
x) (hgf : forall r…
-/
theorem lift_comp_inlHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).comp (inlAlgHom S R M) = f :=
  AlgHom.ext <| lift_apply_inl f g hg hfg hgf

@[simp]
/-
**TrivSqZeroExt.lift_comp_inrHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_comp_inrHom (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x *
 g y = 0) (hfg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• 
r) = g x * f r) : (lift f g hg hfg hgf).toLinearMap.comp (inrHom R M |>.restrict
Scalars S) = g
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TrivSqZeroExt.lift_apply_inr`：lift_apply_inr (f : R ->ₐ[S] A) (g : M ->ₗ
[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r * g 
x) (hgf : forall r…
-/
theorem lift_comp_inrHom (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).toLinearMap.comp (inrHom R M |>.restrictScalars S) = g :=
  LinearMap.ext <| lift_apply_inr f g hg hfg hgf

/-- When applied to `inr` and `inl` themselves, `lift` is the identity. -/
@[simp]
/-
**TrivSqZeroExt.lift_inlAlgHom_inrHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：lift_inlAlgHom_inrHom : lift (inlAlgHom _ _ _) (inrHom R M |>.restrictScal
ars S) (inr_mul_inr R) (fun _ _ => (inl_mul_inr _ _).symm) (fun _ _ => (inr_mul_
inl _ _).symm) = AlgHom.id S (tsze R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.algHom_ext'`：algHom_ext' {A} [Semiring A] [Algebra S A] ⦃f
 g : tsze R M ->ₐ[S] A⦄ (hinl : f.comp (inlAlgHom S R M) = g.comp (inlAlgHom S R
 M)) (hinr : f.…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TrivSqZeroExt.inr_mul_inr`：inr_mul_inr [Semiring R] [AddCommMonoid M] [M
odule R M] [Module Rᵐᵒᵖ M] (m₁ m₂ : M) : (inr m₁ * inr m₂ : tsze R M) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_mul_inr`：inl_mul_inr [MonoidWithZero R] [AddMonoid M] 
[DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inl r * inr 
m : tsze R M) =…
· 使用定理 `TrivSqZeroExt.inr_mul_inl`：inr_mul_inl [MonoidWithZero R] [AddMonoid M] 
[DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] (r : R) (m : M) : (inr m * inl 
r : tsze R M) =…
· 使用定理 `TrivSqZeroExt.lift_comp_inlHom`：lift_comp_inlHom (f : R ->ₐ[S] A) (g : M
 ->ₗ[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r 
* g x) (hgf : forall…
· 使用定理 `TrivSqZeroExt.lift_comp_inrHom`：lift_comp_inrHom (f : R ->ₐ[S] A) (g : M
 ->ₗ[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r 
* g x) (hgf : forall…

--- 原说明 ---
When applied to `inr` and `inl` themselves, `lift` is the identity.
-/
theorem lift_inlAlgHom_inrHom :
    lift (inlAlgHom _ _ _) (inrHom R M |>.restrictScalars S)
      (inr_mul_inr R) (fun _ _ => (inl_mul_inr _ _).symm) (fun _ _ => (inr_mul_inl _ _).symm) =
    AlgHom.id S (tsze R M) :=
  algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)


@[simp]
/-
**TrivSqZeroExt.range_inlAlgHom_sup_adjoin_range_inr** 是 Mathlib 中的一个定理，位于命名空间 `
TrivSqZeroExt`。
形式化陈述：range_inlAlgHom_sup_adjoin_range_inr : (inlAlgHom S R M).range ⊔ Algebra.a
djoin S (Set.range inr) = (⊤ : Subalgebra S (tsze R M))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TrivSqZeroExt.inl_fst_add_inr_snd_eq`：inl_fst_add_inr_snd_eq [AddZeroCla
ss R] [AddZeroClass M] (x : tsze R M) : inl x.fst + inr x.snd = x
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `Algebra.subset_adjoin`：subset_adjoin : s subseteq adjoin R s
-/
theorem range_inlAlgHom_sup_adjoin_range_inr :
    (inlAlgHom S R M).range ⊔ Algebra.adjoin S (Set.range inr) = (⊤ : Subalgebra S (tsze R M)) := by
  refine top_unique fun x hx => ?_; clear hx
  rw [← x.inl_fst_add_inr_snd_eq]
  refine add_mem ?_ ?_
  · exact le_sup_left (α := Subalgebra S _) <| Set.mem_range_self x.fst
  · exact le_sup_right (α := Subalgebra S _) <| Algebra.subset_adjoin <| Set.mem_range_self x.snd

@[simp]
/-
**TrivSqZeroExt.range_liftAux** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：range_liftAux (f : R ->ₐ[S] A) (g : M ->ₗ[S] A) (hg : forall x y, g x * g 
y = 0) (hfg : forall r x, g (r •> x) = f r * g x) (hgf : forall r x, g (x <• r) 
= g x * f r) : (lift f g hg hfg hgf).range = f.range ⊔ Algebra.adjoin S (Set.ran
ge g)
参数：f : R ->ₐ[S] A；g : M ->ₗ[S] A；hg : forall x y, g x * g y = 0；hfg : forall r x
, g (r •> x) = f r * g x；hgf : forall r x, g (x <• r) = g x * f r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.map_sup`：map_sup (f : A ->ₐ[R] B) (S T : Subalgebra R A) : (S ⊔ 
T).map f = S.map f ⊔ T.map f
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `TrivSqZeroExt.lift_comp_inlHom`：lift_comp_inlHom (f : R ->ₐ[S] A) (g : M
 ->ₗ[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r 
* g x) (hgf : forall…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TrivSqZeroExt.lift_apply_inr`：lift_apply_inr (f : R ->ₐ[S] A) (g : M ->ₗ
[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r * g 
x) (hgf : forall r…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.map_top`：map_top (f : A ->ₐ[R] B) : (⊤ : Subalgebra R A).map f =
 f.range
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_liftAux (f : R →ₐ[S] A) (g : M →ₗ[S] A)
    (hg : ∀ x y, g x * g y = 0)
    (hfg : ∀ r x, g (r •> x) = f r * g x)
    (hgf : ∀ r x, g (x <• r) = g x * f r) :
    (lift f g hg hfg hgf).range = f.range ⊔ Algebra.adjoin S (Set.range g) := by
  simp_rw [← Algebra.map_top, ← range_inlAlgHom_sup_adjoin_range_inr, Algebra.map_sup,
    AlgHom.map_adjoin, ← AlgHom.range_comp, lift_comp_inlHom, ← Set.range_comp, Function.comp_def,
    lift_apply_inr, Algebra.map_top]

/-- A universal property of the trivial square-zero extension, providing a unique
`TrivSqZeroExt R M →ₐ[R] A` for every pair of maps `f : R →ₐ[S] A` and `g : M →ₗ[S] A`,
where the range of `g` has no non-zero products, and scaling the input to `g` on the left or right
amounts to a corresponding multiplication by `f` in the output.

This isomorphism is named to match the very similar `Complex.lift`. -/
@[simps! apply symm_apply_coe]
/-
**TrivSqZeroExt.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：liftEquiv : {fg : (R ->ₐ[S] A) × (M ->ₗ[S] A) // (forall x y, fg.2 x * fg.
2 y = 0) ∧ (forall r x, fg.2 (r •> x) = fg.1 r * fg.2 x) ∧ (forall r x, fg.2 (x 
<• r) = fg.2 x * fg.1 r)} ≃ (tsze R M ->ₐ[S] A) where toFun fg
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A universal property of the trivial square-zero extension, providing a unique
`TrivSqZeroExt R M →ₐ[R] A` for every pair of maps `f : R →ₐ[S] A` and `g : M →ₗ
[S] A`,
where the range of `g` has no non-zero products, and scaling the input to `g` on
 the left or right
amounts to a corresponding multiplication by `f` in the output.

This isomorphism is named to match the very similar `Complex.lift`.
-/
def liftEquiv :
    {fg : (R →ₐ[S] A) × (M →ₗ[S] A) //
      (∀ x y, fg.2 x * fg.2 y = 0) ∧
      (∀ r x, fg.2 (r •> x) = fg.1 r * fg.2 x) ∧
      (∀ r x, fg.2 (x <• r) = fg.2 x * fg.1 r)} ≃ (tsze R M →ₐ[S] A) where
  toFun fg := lift fg.val.1 fg.val.2 fg.prop.1 fg.prop.2.1 fg.prop.2.2
  invFun F :=
    ⟨(F.comp (inlAlgHom _ _ _), F.toLinearMap ∘ₗ (inrHom _ _ |>.restrictScalars _)),
      (fun _x _y =>
        (map_mul F _ _).symm.trans <| (F.congr_arg <| inr_mul_inr _ _ _).trans (map_zero F)),
      (fun _r _x => (F.congr_arg (inl_mul_inr _ _).symm).trans (map_mul F _ _)),
      (fun _r _x => (F.congr_arg (inr_mul_inl _ _).symm).trans (map_mul F _ _))⟩
  left_inv _f := Subtype.ext <| Prod.ext (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)
  right_inv _F := algHom_ext' (lift_comp_inlHom _ _ _ _ _) (lift_comp_inrHom _ _ _ _ _)

/-- A simplified version of `TrivSqZeroExt.liftEquiv` for the commutative case. -/
@[simps! apply symm_apply_coe]
/-
**TrivSqZeroExt.liftEquivOfComm** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：liftEquivOfComm : { f : M ->ₗ[R'] A // forall x y, f x * f y = 0 } ≃ (tsze
 R' M ->ₐ[R'] A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
A simplified version of `TrivSqZeroExt.liftEquiv` for the commutative case.
-/
def liftEquivOfComm :
    { f : M →ₗ[R'] A // ∀ x y, f x * f y = 0 } ≃ (tsze R' M →ₐ[R'] A) := by
  refine Equiv.trans ?_ liftEquiv
  exact {
    toFun := fun f => ⟨(Algebra.ofId _ _, f.val), f.prop,
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply],
      fun r x => by simp [Algebra.smul_def, Algebra.ofId_apply, Algebra.commutes]⟩
    invFun := fun fg => ⟨fg.val.2, fg.prop.1⟩ }

section map

variable {N P : Type*} [AddCommMonoid N] [Module R' N] [Module R'ᵐᵒᵖ N] [IsCentralScalar R' N]
  [AddCommMonoid P] [Module R' P] [Module R'ᵐᵒᵖ P] [IsCentralScalar R' P]

/-- Functoriality of `TrivSqZeroExt` when the ring is commutative: a linear map
`f : M →ₗ[R'] N` induces a morphism of `R'`-algebras from `TrivSqZeroExt R' M` to
`TrivSqZeroExt R' N`.

Note that we cannot neatly state the non-commutative case, as we do not have morphisms of bimodules.
-/
/-
**TrivSqZeroExt.map** 是 Mathlib 中的一个定义，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map (f : M ->ₗ[R'] N) : TrivSqZeroExt R' M ->ₐ[R'] TrivSqZeroExt R' N
参数：f : M ->ₗ[R'] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `TrivSqZeroExt` when the ring is commutative: a linear map
`f : M →ₗ[R'] N` induces a morphism of `R'`-algebras from `TrivSqZeroExt R' M` t
o
`TrivSqZeroExt R' N`.

Note that we cannot neatly state the non-commutative case, as we do not have mor
phisms of bimodules.
-/
def map (f : M →ₗ[R'] N) : TrivSqZeroExt R' M →ₐ[R'] TrivSqZeroExt R' N :=
  liftEquivOfComm ⟨inrHom R' N ∘ₗ f, fun _ _ => inr_mul_inr _ _ _⟩

@[simp]
/-
**TrivSqZeroExt.map_inl** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_inl (f : M ->ₗ[R'] N) (r : R') : map f (inl r) = inl r
参数：f : M ->ₗ[R'] N；r : R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.map.eq_1`：∀ {R' : Type u} {M : Type v} [inst : CommSemirin
g R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [inst_3 : _root
_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.liftEquivOfComm_apply`：∀ {R' : Type u} {M : Type v} [inst 
: CommSemiring R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [i
nst_3 : _root_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.lift_apply_inl`：lift_apply_inl (f : R ->ₐ[S] A) (g : M ->ₗ
[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r * g 
x) (hgf : forall r…
· 使用定理 `Algebra.ofId_apply`：ofId_apply (r) : ofId R A r = algebraMap R A r
· 使用定理 `TrivSqZeroExt.algebraMap_eq_inl`：algebraMap_eq_inl : ⇑(algebraMap R' (ts
ze R' M)) = inl
-/
theorem map_inl (f : M →ₗ[R'] N) (r : R') : map f (inl r) = inl r := by
  rw [map, liftEquivOfComm_apply, lift_apply_inl, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
/-
**TrivSqZeroExt.map_inr** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x) = inr (f x)
参数：f : M ->ₗ[R'] N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.map.eq_1`：∀ {R' : Type u} {M : Type v} [inst : CommSemirin
g R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [inst_3 : _root
_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.liftEquivOfComm_apply`：∀ {R' : Type u} {M : Type v} [inst 
: CommSemiring R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [i
nst_3 : _root_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.lift_apply_inr`：lift_apply_inr (f : R ->ₐ[S] A) (g : M ->ₗ
[S] A) (hg : forall x y, g x * g y = 0) (hfg : forall r x, g (r •> x) = f r * g 
x) (hgf : forall r…
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `TrivSqZeroExt.inrHom_apply`：∀ (R : Type u) (M : Type v) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (m : M),   (TrivSqZe
roExt.inrHom R M…
-/
theorem map_inr (f : M →ₗ[R'] N) (x : M) : map f (inr x) = inr (f x) := by
  rw [map, liftEquivOfComm_apply, lift_apply_inr, LinearMap.comp_apply, inrHom_apply]

@[simp]
/-
**TrivSqZeroExt.fst_map** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fst_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M) : fst (map f x) = fst x
参数：f : M ->ₗ[R'] N；x : TrivSqZeroExt R' M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.liftEquivOfComm_apply`：∀ {R' : Type u} {M : Type v} [inst 
: CommSemiring R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [i
nst_3 : _root_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.inrHom_apply`：∀ (R : Type u) (M : Type v) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (m : M),   (TrivSqZe
roExt.inrHom R M…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem fst_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : fst (map f x) = fst x := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
/-
**TrivSqZeroExt.snd_map** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：snd_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M) : snd (map f x) = f (sn
d x)
参数：f : M ->ₗ[R'] N；x : TrivSqZeroExt R' M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.liftEquivOfComm_apply`：∀ {R' : Type u} {M : Type v} [inst 
: CommSemiring R'] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R' M]   [i
nst_3 : _root_.Module R'ᵐ…
· 使用定理 `TrivSqZeroExt.inrHom_apply`：∀ (R : Type u) (M : Type v) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (m : M),   (TrivSqZe
roExt.inrHom R M…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem snd_map (f : M →ₗ[R'] N) (x : TrivSqZeroExt R' M) : snd (map f x) = f (snd x) := by
  simp [map, lift_def, Algebra.ofId_apply, algebraMap_eq_inl]

@[simp]
/-
**TrivSqZeroExt.map_comp_inlAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_comp_inlAlgHom (f : M ->ₗ[R'] N) : (map f).comp (inlAlgHom R' R' M) = 
inlAlgHom R' R' N
参数：f : M ->ₗ[R'] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.map_inl`：map_inl (f : M ->ₗ[R'] N) (r : R') : map f (inl r
) = inl r
-/
theorem map_comp_inlAlgHom (f : M →ₗ[R'] N) :
    (map f).comp (inlAlgHom R' R' M) = inlAlgHom R' R' N :=
  AlgHom.ext <| map_inl _

@[simp]
/-
**TrivSqZeroExt.map_comp_inrHom** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_comp_inrHom (f : M ->ₗ[R'] N) : (map f).toLinearMap ∘ₗ inrHom R' M = i
nrHom R' N ∘ₗ f
参数：f : M ->ₗ[R'] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.map_inr`：map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x)
 = inr (f x)
-/
theorem map_comp_inrHom (f : M →ₗ[R'] N) :
    (map f).toLinearMap ∘ₗ inrHom R' M = inrHom R' N ∘ₗ f :=
  LinearMap.ext <| map_inr _

@[simp]
/-
**TrivSqZeroExt.fstHom_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：fstHom_comp_map (f : M ->ₗ[R'] N) : (fstHom R' R' N).comp (map f) = fstHom
 R' R' M
参数：f : M ->ₗ[R'] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.fst_map`：fst_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M
) : fst (map f x) = fst x
-/
theorem fstHom_comp_map (f : M →ₗ[R'] N) :
    (fstHom R' R' N).comp (map f) = fstHom R' R' M :=
  AlgHom.ext <| fst_map _

@[simp]
/-
**TrivSqZeroExt.sndHom_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：sndHom_comp_map (f : M ->ₗ[R'] N) : sndHom R' N ∘ₗ (map f).toLinearMap = f
 ∘ₗ sndHom R' M
参数：f : M ->ₗ[R'] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `TrivSqZeroExt.snd_map`：snd_map (f : M ->ₗ[R'] N) (x : TrivSqZeroExt R' M
) : snd (map f x) = f (snd x)
-/
theorem sndHom_comp_map (f : M →ₗ[R'] N) :
    sndHom R' N ∘ₗ (map f).toLinearMap = f ∘ₗ sndHom R' M :=
  LinearMap.ext <| snd_map _

@[simp]
/-
**TrivSqZeroExt.map_id** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_id : map (LinearMap.id : M ->ₗ[R'] M) = AlgHom.id R' _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.algHom_ext`：algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f 
g : tsze R' M ->ₐ[R'] A⦄ (h : forall m, f (inr m) = g (inr m)) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.map_inr`：map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x)
 = inr (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem map_id : map (LinearMap.id : M →ₗ[R'] M) = AlgHom.id R' _ := by
  apply algHom_ext
  simp only [map_inr, LinearMap.id_coe, id_eq, AlgHom.coe_id, forall_const]
/-
**TrivSqZeroExt.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `TrivSqZeroExt`。
形式化陈述：map_comp_map (f : M ->ₗ[R'] N) (g : N ->ₗ[R'] P) : map (g.comp f) = (map g
).comp (map f)
参数：f : M ->ₗ[R'] N；g : N ->ₗ[R'] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TrivSqZeroExt.algHom_ext`：algHom_ext {A} [Semiring A] [Algebra R' A] ⦃f 
g : tsze R' M ->ₐ[R'] A⦄ (h : forall m, f (inr m) = g (inr m)) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TrivSqZeroExt.map_inr`：map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x)
 = inr (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem map_comp_map (f : M →ₗ[R'] N) (g : N →ₗ[R'] P) :
    map (g.comp f) = (map g).comp (map f) := by
  apply algHom_ext
  simp only [map_inr, LinearMap.coe_comp, Function.comp_apply, AlgHom.coe_comp, forall_const]

end map

end Algebra

end TrivSqZeroExt

