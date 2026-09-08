/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# The five lemma in terms of modules

The five lemma for all abelian categories is proven in
`CategoryTheory.Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`. But for universe generality
and ease of application in the unbundled setting, we reprove them here.

## Main results

- `LinearMap.surjective_of_surjective_of_surjective_of_injective`: a four lemma
- `LinearMap.injective_of_surjective_of_injective_of_injective`: another four lemma
- `LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective`: the five lemma

## Explanation of the variables

In this file we always consider the following commutative diagram of groups (resp. modules)

```
M₁ --f₁--> M₂ --f₂--> M₃ --f₃--> M₄ --f₄--> M₅
|          |          |          |          |
i₁         i₂         i₃         i₄         i₅
|          |          |          |          |
v          v          v          v          v
N₁ --g₁--> N₂ --g₂--> N₃ --g₃--> N₄ --g₄--> N₅
```

with exact rows.

-/

public section

assert_not_exists Cardinal

namespace MonoidHom

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [Group M₁] [Group M₂] [Group M₃] [Group M₄] [Group M₅]
variable [Group N₁] [Group N₂] [Group N₃] [Group N₄] [Group N₅]
variable (f₁ : M₁ →* M₂) (f₂ : M₂ →* M₃) (f₃ : M₃ →* M₄) (f₄ : M₄ →* M₅)
variable (g₁ : N₁ →* N₂) (g₂ : N₂ →* N₃) (g₃ : N₃ →* N₄) (g₄ : N₄ →* N₅)
variable (i₁ : M₁ →* N₁) (i₂ : M₂ →* N₂) (i₃ : M₃ →* N₃) (i₄ : M₄ →* N₄)
  (i₅ : M₅ →* N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.MulExact f₁ f₂) (hf₂ : Function.MulExact f₂ f₃)
  (hf₃ : Function.MulExact f₃ f₄) (hg₁ : Function.MulExact g₁ g₂)
  (hg₂ : Function.MulExact g₂ g₃) (hg₃ : Function.MulExact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of groups. For a diagram explaining the variables,
see the module docstring. -/
@[to_additive /-- One four lemma in terms of additive groups.
For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.surjective_of_surjective_of_surjective_of_injective** 是 Mathlib 中的一个
引理，位于命名空间 `MonoidHom`。
形式化陈述：surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjec
tive i₁) (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) : Function
.Surjective i₂
参数：hi₁ : Function.Surjective i₁；hi₃ : Function.Surjective i₃；hi₄ : Function.Inje
ctive i₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.MulExact.apply_apply_eq_one`：apply_apply_eq_one [One P] (h : Mu
lExact f g) (x : M) : g (f x) = 1
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
-/
lemma surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ := by
  intro x
  obtain ⟨y, hy⟩ := hi₃ (g₂ x)
  obtain ⟨a, rfl⟩ : y ∈ Set.range f₂ := (hf₂ _).mp <| by
    simpa [hy, hg₂.apply_apply_eq_one, map_eq_one_iff _ hi₄] using (DFunLike.congr_fun hc₃ y).symm
  obtain ⟨b, hb⟩ : x / i₂ a ∈ Set.range g₁ := (hg₁ _).mp <| by
    simp [← hy, show g₂ (i₂ a) = i₃ (f₂ a) by simpa using DFunLike.congr_fun hc₂ a]
  obtain ⟨o, rfl⟩ := hi₁ b
  use f₁ o * a
  simp [← show g₁ (i₁ o) = i₂ (f₁ o) by simpa using DFunLike.congr_fun hc₁ o, hb]

include hf₁ hg₁ hc₁ hc₂ in
-- Need to remove hybrid addition/multiplication instances on `Unit` so that `to_additive` can
-- correctly convert the multiplicative instances on `Unit` to additive instances
attribute [-instance] PUnit.commRing in
/-- A special case of one four lemma such that the left-most term is one in terms of
groups. For a diagram explaining the variables, see the module docstring. -/
@[to_additive /-- A special case of one four lemma such that the left-most term is zero in terms
of additive groups. For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.surjective_of_surjective_of_injective_of_left_exact** 是 Mathlib 中的一个
引理，位于命名空间 `MonoidHom`。
形式化陈述：surjective_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjec
tive i₂) (hi₃ : Function.Injective i₃) (hg₀ : Function.Injective g₁) : Function.
Surjective i₁
参数：hi₂ : Function.Surjective i₂；hi₃ : Function.Injective i₃；hg₀ : Function.Injec
tive g₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.surjective_of_surjective_of_surjective_of_injective`：surjectiv
e_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁) (hi₃ :
 Function.Surjective i₃) (hi₄ : Function.Injective …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_one`：comp_one [MulOne M] [MulOneClass N] [MulOneClass P] 
(f : N ->* P) : f.comp (1 : M ->* N) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma surjective_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjective i₂)
    (hi₃ : Function.Injective i₃) (hg₀ : Function.Injective g₁) : Function.Surjective i₁ := by
  refine surjective_of_surjective_of_surjective_of_injective (1 : Unit →* M₁) f₁ f₂ (1 : Unit →* N₁)
    g₁ g₂ 1 i₁ i₂ i₃ (by simp) hc₁ hc₂ hf₁ (fun y ↦ ?_) hg₁ (fun | .unit => ⟨0, rfl⟩) hi₂ hi₃
  simp only [Set.mem_range, one_apply, exists_const]
  exact ⟨fun h ↦ (hg₀ ((map_one _).trans h.symm)), fun h ↦ h ▸ (map_one _)⟩

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of groups. For a diagram explaining the variables,
see the module docstring. -/
@[to_additive /-- One four lemma in terms of additive groups.
For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.injective_of_surjective_of_injective_of_injective** 是 Mathlib 中的一个引理
，位于命名空间 `MonoidHom`。
形式化陈述：injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjecti
ve i₁) (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) : Function.In
jective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Injective i₂；hi₄ : Function.Injec
tive i₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用引理 `Function.MulExact.apply_apply_eq_one`：apply_apply_eq_one [One P] (h : Mu
lExact f g) (x : M) : g (f x) = 1
-/
lemma injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) : Function.Injective i₃ := by
  rw [injective_iff_map_eq_one]
  intro m hm
  obtain ⟨x, rfl⟩ := (hf₂ m).mp <| by
    suffices h : i₄ (f₃ m) = 1 by rwa [map_eq_one_iff _ hi₄] at h
    simp [← show g₃ (i₃ m) = i₄ (f₃ m) by simpa using DFunLike.congr_fun hc₃ m, hm]
  obtain ⟨y, hy⟩ := (hg₁ _).mp <| by
    rwa [show g₂ (i₂ x) = i₃ (f₂ x) by simpa using DFunLike.congr_fun hc₂ x]
  obtain ⟨a, rfl⟩ := hi₁ y
  rw [show g₁ (i₁ a) = i₂ (f₁ a) by simpa using DFunLike.congr_fun hc₁ a] at hy
  apply hi₂ at hy
  subst hy
  rw [hf₁.apply_apply_eq_one]

include hf₁ hg₁ hc₁ hc₂ in
-- Need to remove hybrid addition/multiplication instances on `Unit` so that `to_additive` can
-- correctly convert the multiplicative instances on `Unit` to additive instances
attribute [-instance] PUnit.commRing in
/-- A special case of one four lemma such that the right-most term is one in terms of
groups. For a diagram explaining the variables, see the module docstring. -/
@[to_additive /-- A special case of one four lemma such that the right-most term is zero in terms
of additive groups. For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.injective_of_surjective_of_injective_of_right_exact** 是 Mathlib 中的一个
引理，位于命名空间 `MonoidHom`。
形式化陈述：injective_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjec
tive i₁) (hi₂ : Function.Injective i₂) (hf₂ : Function.Surjective f₂) : Function
.Injective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Injective i₂；hf₂ : Function.Surje
ctive f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.injective_of_surjective_of_injective_of_injective`：injective_o
f_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁) (hi₂ : Fun
ction.Injective i₂) (hi₄ : Function.Injective i₄)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHom.comp_one`：comp_one [MulOne M] [MulOneClass N] [MulOneClass P] 
(f : N ->* P) : f.comp (1 : M ->* N) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma injective_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hf₂ : Function.Surjective f₂) : Function.Injective i₃ :=
  injective_of_surjective_of_injective_of_injective f₁ f₂ (1 : M₃ →* Unit) g₁ g₂ (1 : N₃ →* Unit)
    i₁ i₂ i₃ 1 hc₁ hc₂ (by simp) hf₁ (fun y ↦ by simpa using hf₂ y) hg₁ hi₁ hi₂
    (fun | .unit => by simp)

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of groups. For a diagram explaining the variables,
see the module docstring. -/
@[to_additive /-- The five lemma in terms of additive groups.
For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.bijective_of_surjective_of_bijective_of_bijective_of_injective** 是 M
athlib 中的一个引理，位于命名空间 `MonoidHom`。
形式化陈述：bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Func
tion.Surjective i₁) (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) 
(hi₅ : Function.Injective i₅) : Function.Bijective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Bijective i₂；hi₄ : Function.Bijec
tive i₄；hi₅ : Function.Injective i₅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.injective_of_surjective_of_injective_of_injective`：injective_o
f_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁) (hi₂ : Fun
ction.Injective i₂) (hi₄ : Function.Injective i₄)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MonoidHom.surjective_of_surjective_of_surjective_of_injective`：surjectiv
e_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁) (hi₃ :
 Function.Surjective i₃) (hi₄ : Function.Injective …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of_surjective_of_injective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄
      hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of_surjective_of_surjective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of the five lemma in terms of groups. For a diagram explaining the
variables, see the module docstring. -/
@[to_additive /-- A special case of the five lemma in terms of additive groups.
For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.bijective_of_bijective_of_injective_of_left_exact** 是 Mathlib 中的一个引理
，位于命名空间 `MonoidHom`。
形式化陈述：bijective_of_bijective_of_injective_of_left_exact (hi₂ : Function.Bijectiv
e i₂) (hi₃ : Function.Injective i₃) (hf₀ : Function.Injective f₁) (hg₀ : Functio
n.Injective g₁) : Function.Bijective i₁
参数：hi₂ : Function.Bijective i₂；hi₃ : Function.Injective i₃；hf₀ : Function.Inject
ive f₁；hg₀ : Function.Injective g₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidHom.surjective_of_surjective_of_injective_of_left_exact`：surjectiv
e_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjective i₂) (hi₃ :
 Function.Injective i₃) (hg₀ : Function.Injective g…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma bijective_of_bijective_of_injective_of_left_exact (hi₂ : Function.Bijective i₂)
    (hi₃ : Function.Injective i₃) (hf₀ : Function.Injective f₁) (hg₀ : Function.Injective g₁) :
    Function.Bijective i₁ :=
  ⟨fun {x y} h ↦ (hf₀ (hi₂.1 (congr($hc₁ x).symm.trans (congr(g₁ $h).trans congr($hc₁ y))))),
    surjective_of_surjective_of_injective_of_left_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃
      hc₁ hc₂ hf₁ hg₁ hi₂.2 hi₃ hg₀⟩

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of the five lemma in terms of groups. For a diagram explaining the
variables, see the module docstring. -/
@[to_additive /-- A special case of the five lemma in terms of additive groups.
For a diagram explaining the variables, see the module docstring. -/]
/-
**MonoidHom.bijective_of_surjective_of_bijective_of_right_exact** 是 Mathlib 中的一个
引理，位于命名空间 `MonoidHom`。
形式化陈述：bijective_of_surjective_of_bijective_of_right_exact (hi₁ : Function.Surjec
tive i₁) (hi₂ : Function.Bijective i₂) (hf₂ : Function.Surjective f₂) (hg₂ : Fun
ction.Surjective g₂) : Function.Bijective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Bijective i₂；hf₂ : Function.Surje
ctive f₂；hg₂ : Function.Surjective g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MonoidHom.injective_of_surjective_of_injective_of_right_exact`：injective
_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjective i₁) (hi₂ :
 Function.Injective i₂) (hf₂ : Function.Surjective …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma bijective_of_surjective_of_bijective_of_right_exact (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hf₂ : Function.Surjective f₂) (hg₂ : Function.Surjective g₂) :
    Function.Bijective i₃ := by
  refine ⟨injective_of_surjective_of_injective_of_right_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃
    hc₁ hc₂ hf₁ hg₁ hi₁ hi₂.1 hf₂, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hg₂ y
  obtain ⟨y, rfl⟩ := hi₂.2 y
  exact ⟨f₂ y, congr($hc₂ y).symm⟩

end MonoidHom

namespace LinearMap

variable {R : Type*} [CommRing R]
variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
variable [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
variable [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
variable [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
variable (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
variable (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
variable (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) (i₃ : M₃ →ₗ[R] N₃) (i₄ : M₄ →ₗ[R] N₄)
  (i₅ : M₅ →ₗ[R] N₅)
variable (hc₁ : g₁.comp i₁ = i₂.comp f₁) (hc₂ : g₂.comp i₂ = i₃.comp f₂)
  (hc₃ : g₃.comp i₃ = i₄.comp f₃) (hc₄ : g₄.comp i₄ = i₅.comp f₄)
variable (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
variable (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)

include hf₂ hg₁ hg₂ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
/-
**LinearMap.surjective_of_surjective_of_surjective_of_injective** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjec
tive i₁) (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) : Function
.Surjective i₂
参数：hi₁ : Function.Surjective i₁；hi₃ : Function.Surjective i₃；hi₄ : Function.Inje
ctive i₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.surjective_of_surjective_of_surjective_of_injective`：∀ {M₁ 
: Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} {M₄ : Type u_4} {N₁ : Type u_6} {N₂ 
: Type u_7} {N₃ : Type u_8}   {N₄ : Type u_9} [inst : …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring.
-/
lemma surjective_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₃ : Function.Surjective i₃) (hi₄ : Function.Injective i₄) :
    Function.Surjective i₂ :=
  AddMonoidHom.surjective_of_surjective_of_surjective_of_injective
    f₁.toAddMonoidHom f₂.toAddMonoidHom f₃.toAddMonoidHom g₁.toAddMonoidHom g₂.toAddMonoidHom
    g₃.toAddMonoidHom i₁.toAddMonoidHom i₂.toAddMonoidHom i₃.toAddMonoidHom i₄.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₁ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₃ x) hf₂ hg₁ hg₂ hi₁ hi₃ hi₄

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of one four lemma such that the left-most term is zero in terms of modules.
For a diagram explaining the variables, see the module docstring. -/
/-
**LinearMap.surjective_of_surjective_of_injective_of_left_exact** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：surjective_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjec
tive i₂) (hi₃ : Function.Injective i₃) (hg₀ : Function.Injective g₁) : Function.
Surjective i₁
参数：hi₂ : Function.Surjective i₂；hi₃ : Function.Injective i₃；hg₀ : Function.Injec
tive g₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.surjective_of_surjective_of_surjective_of_injective`：surjectiv
e_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁) (hi₃ :
 Function.Surjective i₃) (hi₄ : Function.Injective …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A special case of one four lemma such that the left-most term is zero in terms o
f modules.
For a diagram explaining the variables, see the module docstring.
-/
lemma surjective_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjective i₂)
    (hi₃ : Function.Injective i₃) (hg₀ : Function.Injective g₁) : Function.Surjective i₁ := by
  refine surjective_of_surjective_of_surjective_of_injective (0 : Unit →ₗ[R] M₁) f₁ f₂
    (0 : Unit →ₗ[R] N₁) g₁ g₂ 0 i₁ i₂ i₃ (by simp) hc₁ hc₂ hf₁ (fun y ↦ ?_) hg₁
    (fun | .unit => ⟨0, rfl⟩) hi₂ hi₃
  simp only [Set.mem_range, zero_apply, exists_const]
  exact ⟨fun h ↦ (hg₀ ((map_zero _).trans h.symm)), fun h ↦ h ▸ (map_zero _)⟩

include hf₁ hf₂ hg₁ hc₁ hc₂ hc₃ in
/-- One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
/-
**LinearMap.injective_of_surjective_of_injective_of_injective** 是 Mathlib 中的一个引理
，位于命名空间 `LinearMap`。
形式化陈述：injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjecti
ve i₁) (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) : Function.In
jective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Injective i₂；hi₄ : Function.Injec
tive i₄。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.injective_of_surjective_of_injective_of_injective`：∀ {M₁ : 
Type u_1} {M₂ : Type u_2} {M₃ : Type u_3} {M₄ : Type u_4} {N₁ : Type u_6} {N₂ : 
Type u_7} {N₃ : Type u_8}   {N₄ : Type u_9} [inst : …
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
One four lemma in terms of modules. For a diagram explaining the variables,
see the module docstring.
-/
lemma injective_of_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hi₄ : Function.Injective i₄) :
    Function.Injective i₃ :=
  AddMonoidHom.injective_of_surjective_of_injective_of_injective
    f₁.toAddMonoidHom f₂.toAddMonoidHom f₃.toAddMonoidHom g₁.toAddMonoidHom g₂.toAddMonoidHom
    g₃.toAddMonoidHom i₁.toAddMonoidHom i₂.toAddMonoidHom i₃.toAddMonoidHom i₄.toAddMonoidHom
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₁ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₂ x)
    (AddMonoidHom.ext fun x ↦ DFunLike.congr_fun hc₃ x) hf₁ hf₂ hg₁ hi₁ hi₂ hi₄

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of one four lemma such that the right-most term is zero in terms of (additive)
groups. For a diagram explaining the variables, see the module docstring. -/
/-
**LinearMap.injective_of_surjective_of_injective_of_right_exact** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：injective_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjec
tive i₁) (hi₂ : Function.Injective i₂) (hf₂ : Function.Surjective f₂) : Function
.Injective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Injective i₂；hf₂ : Function.Surje
ctive f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.injective_of_surjective_of_injective_of_injective`：injective_o
f_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁) (hi₂ : Fun
ction.Injective i₂) (hi₄ : Function.Injective i₄)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp_zero`：comp_zero (g : M₂ ->ₛₗ[σ₂₃] M₃) : (g.comp (0 : M ->
ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A special case of one four lemma such that the right-most term is zero in terms 
of (additive)
groups. For a diagram explaining the variables, see the module docstring.
-/
lemma injective_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Injective i₂) (hf₂ : Function.Surjective f₂) : Function.Injective i₃ :=
  injective_of_surjective_of_injective_of_injective f₁ f₂ (0 : M₃ →ₗ[R] Unit) g₁ g₂
    (0 : N₃ →ₗ[R] Unit) i₁ i₂ i₃ 0 hc₁ hc₂ (by simp) hf₁ (fun y ↦ by simpa using hf₂ y) hg₁ hi₁ hi₂
      (fun | .unit => by simp)

include hf₁ hf₂ hf₃ hg₁ hg₂ hg₃ hc₁ hc₂ hc₃ hc₄ in
/-- The five lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
/-
**LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective** 是 M
athlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Func
tion.Surjective i₁) (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) 
(hi₅ : Function.Injective i₅) : Function.Bijective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Bijective i₂；hi₄ : Function.Bijec
tive i₄；hi₅ : Function.Injective i₅。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.injective_of_surjective_of_injective_of_injective`：injective_o
f_surjective_of_injective_of_injective (hi₁ : Function.Surjective i₁) (hi₂ : Fun
ction.Injective i₂) (hi₄ : Function.Injective i₄)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `LinearMap.surjective_of_surjective_of_surjective_of_injective`：surjectiv
e_of_surjective_of_surjective_of_injective (hi₁ : Function.Surjective i₁) (hi₃ :
 Function.Surjective i₃) (hi₄ : Function.Injective …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
The five lemma in terms of modules. For a diagram explaining the variables,
see the module docstring.
-/
lemma bijective_of_surjective_of_bijective_of_bijective_of_injective (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hi₄ : Function.Bijective i₄) (hi₅ : Function.Injective i₅) :
    Function.Bijective i₃ :=
  ⟨injective_of_surjective_of_injective_of_injective f₁ f₂ f₃ g₁ g₂ g₃ i₁ i₂ i₃ i₄
      hc₁ hc₂ hc₃ hf₁ hf₂ hg₁ hi₁ hi₂.1 hi₄.1,
    surjective_of_surjective_of_surjective_of_injective f₂ f₃ f₄ g₂ g₃ g₄ i₂ i₃ i₄ i₅
      hc₂ hc₃ hc₄ hf₃ hg₂ hg₃ hi₂.2 hi₄.2 hi₅⟩

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of the five lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
/-
**LinearMap.bijective_of_bijective_of_injective_of_left_exact** 是 Mathlib 中的一个引理
，位于命名空间 `LinearMap`。
形式化陈述：bijective_of_bijective_of_injective_of_left_exact (hi₂ : Function.Bijectiv
e i₂) (hi₃ : Function.Injective i₃) (hf₀ : Function.Injective f₁) (hg₀ : Functio
n.Injective g₁) : Function.Bijective i₁
参数：hi₂ : Function.Bijective i₂；hi₃ : Function.Injective i₃；hf₀ : Function.Inject
ive f₁；hg₀ : Function.Injective g₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.surjective_of_surjective_of_injective_of_left_exact`：surjectiv
e_of_surjective_of_injective_of_left_exact (hi₂ : Function.Surjective i₂) (hi₃ :
 Function.Injective i₃) (hg₀ : Function.Injective g…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A special case of the five lemma in terms of modules. For a diagram explaining t
he variables,
see the module docstring.
-/
lemma bijective_of_bijective_of_injective_of_left_exact (hi₂ : Function.Bijective i₂)
    (hi₃ : Function.Injective i₃) (hf₀ : Function.Injective f₁) (hg₀ : Function.Injective g₁) :
    Function.Bijective i₁ :=
  ⟨fun {x y} h ↦ (hf₀ (hi₂.1 (congr($hc₁ x).symm.trans (congr(g₁ $h).trans congr($hc₁ y))))),
    surjective_of_surjective_of_injective_of_left_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃
      hc₁ hc₂ hf₁ hg₁ hi₂.2 hi₃ hg₀⟩

include hf₁ hg₁ hc₁ hc₂ in
/-- A special case of the five lemma in terms of modules. For a diagram explaining the variables,
see the module docstring. -/
/-
**LinearMap.bijective_of_surjective_of_bijective_of_right_exact** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap`。
形式化陈述：bijective_of_surjective_of_bijective_of_right_exact (hi₁ : Function.Surjec
tive i₁) (hi₂ : Function.Bijective i₂) (hf₂ : Function.Surjective f₂) (hg₂ : Fun
ction.Surjective g₂) : Function.Bijective i₃
参数：hi₁ : Function.Surjective i₁；hi₂ : Function.Bijective i₂；hf₂ : Function.Surje
ctive f₂；hg₂ : Function.Surjective g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.injective_of_surjective_of_injective_of_right_exact`：injective
_of_surjective_of_injective_of_right_exact (hi₁ : Function.Surjective i₁) (hi₂ :
 Function.Injective i₂) (hf₂ : Function.Surjective …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
A special case of the five lemma in terms of modules. For a diagram explaining t
he variables,
see the module docstring.
-/
lemma bijective_of_surjective_of_bijective_of_right_exact (hi₁ : Function.Surjective i₁)
    (hi₂ : Function.Bijective i₂) (hf₂ : Function.Surjective f₂) (hg₂ : Function.Surjective g₂) :
    Function.Bijective i₃ := by
  refine ⟨injective_of_surjective_of_injective_of_right_exact f₁ f₂ g₁ g₂ i₁ i₂ i₃
    hc₁ hc₂ hf₁ hg₁ hi₁ hi₂.1 hf₂, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := hg₂ y
  obtain ⟨y, rfl⟩ := hi₂.2 y
  exact ⟨f₂ y, congr($hc₂ y).symm⟩

end LinearMap

