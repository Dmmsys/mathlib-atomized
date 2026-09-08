/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kevin Buzzard, Kim Morrison, Johan Commelin, Chris Hughes,
  Johannes Hölzl, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.Algebra.Group.Hom.Defs

/-!
# Multiplicative homomorphisms respect semiconjugation and commutation.
-/

public section

assert_not_exists MonoidWithZero DenselyOrdered

section Commute

variable {F M N : Type*} [Mul M] [Mul N] {a x y : M} [FunLike F M N]

@[to_additive (attr := simp)]
/-
**SemiconjBy.map** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul M] [inst_1 : Mu
l N] {a x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], SemiconjBy a x 
y → ∀ (f : F), SemiconjBy (f a) (f x) (f y)
参数：f : F；f a；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
protected theorem SemiconjBy.map [MulHomClass F M N] (h : SemiconjBy a x y) (f : F) :
    SemiconjBy (f a) (f x) (f y) := by simpa only [SemiconjBy, map_mul] using congr_arg f h

@[to_additive (attr := simp)]
/-
**Commute.map** 是 Mathlib 中的一个定理，位于命名空间 `Commute`。
形式化陈述：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul M] [inst_1 : Mu
l N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Commute x y → ∀ (
f : F), Commute (f x) (f y)
参数：f : F；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : M
ul M] [inst_1 : Mul N] {a x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N
], S…
-/
protected theorem Commute.map [MulHomClass F M N] (h : Commute x y) (f : F) : Commute (f x) (f y) :=
  SemiconjBy.map h f

@[to_additive]
/-
**SemiconjBy.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SemiconjBy`。
形式化陈述：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul M] [inst_1 : Mu
l N] {a x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N] {f : F}, Functio
n.Injective ⇑f → SemiconjBy (f a) (f x) (f y) → SemiconjBy a x y
参数：f a；f x；f y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
protected theorem SemiconjBy.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : SemiconjBy (f a) (f x) (f y)) : SemiconjBy a x y :=
  hf (by simpa only [SemiconjBy, map_mul] using h)

@[to_additive]
/-
**Commute.of_map** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Commute.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f) (h 
: Commute (f x) (f y)) : Commute x y
参数：hf : Function.Injective f；h : Commute (f x) (f y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
-/
theorem Commute.of_map [MulHomClass F M N] {f : F} (hf : Function.Injective f)
    (h : Commute (f x) (f y)) : Commute x y :=
  hf (by simpa only [map_mul] using h.eq)

@[to_additive]
/-
**semiconjBy_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：semiconjBy_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f)
 {x y : M} : SemiconjBy (f a) (f x) (f y) ↔ SemiconjBy a x y
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemiconjBy.of_map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst 
: Mul M] [inst_1 : Mul N] {a x y : M} [inst_2 : FunLike F M N]   [MulHomClass F 
M N] {f…
· 使用定理 `SemiconjBy.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : M
ul M] [inst_1 : Mul N] {a x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N
], S…
-/
theorem semiconjBy_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    SemiconjBy (f a) (f x) (f y) ↔ SemiconjBy a x y :=
  ⟨.of_map hf, (.map · f)⟩

@[to_additive]
/-
**commute_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：commute_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x
 y : M} : Commute (f x) (f y) ↔ Commute x y
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Commute.of_map`：Commute.of_map [MulHomClass F M N] {f : F} (hf : Functio
n.Injective f) (h : Commute (f x) (f y)) : Commute x y
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
-/
theorem commute_map_iff [MulHomClass F M N] {f : F} (hf : Function.Injective f) {x y : M} :
    Commute (f x) (f y) ↔ Commute x y :=
  ⟨.of_map hf, (.map · f)⟩

end Commute

