/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Commute
public import Mathlib.Algebra.GroupWithZero.Units.Lemmas
public import Mathlib.Algebra.GroupWithZero.WithZero

/-!
# Homomorphisms for products of groups with zero

This file defines homomorphisms for products of groups with zero,
which is identified with the `WithZero` of the product of the units of the groups.

The product of groups with zero `WithZero (αˣ × βˣ)` is a
group with zero itself with natural inclusions.

TODO: Give `GrpWithZero` instances of `HasBinaryProducts` and `HasBinaryCoproducts`,
as well as a terminal object.

-/

@[expose] public section

namespace MonoidWithZeroHom

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/-
**MonoidWithZeroHom.one_apply_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZero
Hom`。
形式化陈述：one_apply_apply_eq {M₀ N₀ G₀ : Type*} [GroupWithZero M₀] [MulZeroOneClass 
N₀] [Nontrivial N₀] [NoZeroDivisors N₀] [MulZeroOneClass G₀] [DecidablePred fun 
x : M₀ => x = 0] [DecidablePred fun x : N₀ => x = 0] (f : M₀ ->*₀ N₀) (x : M₀) :
 (1 : N₀ ->*₀ G₀) (f x) = (1 : M₀ ->*₀ G₀) x
参数：f : M₀ ->*₀ N₀；x : M₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0

--- 原说明 ---
The trivial group-with-zero hom is absorbing for composition.
-/
lemma one_apply_apply_eq {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) (x : M₀) :
    (1 : N₀ →*₀ G₀) (f x) = (1 : M₀ →*₀ G₀) x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [one_apply_of_ne_zero hx, one_apply_of_ne_zero]
    rwa [map_ne_zero f]

/-- The trivial group-with-zero hom is absorbing for composition. -/
@[simp]
/-
**MonoidWithZeroHom.one_comp** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：one_comp {M₀ N₀ G₀ : Type*} [GroupWithZero M₀] [MulZeroOneClass N₀] [Nontr
ivial N₀] [NoZeroDivisors N₀] [MulZeroOneClass G₀] [DecidablePred fun x : M₀ => 
x = 0] [DecidablePred fun x : N₀ => x = 0] (f : M₀ ->*₀ N₀) : (1 : N₀ ->*₀ G₀).c
omp f = (1 : M₀ ->*₀ G₀)
参数：f : M₀ ->*₀ N₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用引理 `MonoidWithZeroHom.one_apply_apply_eq`：one_apply_apply_eq {M₀ N₀ G₀ : Typ
e*} [GroupWithZero M₀] [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀] 
[MulZeroOneClass G₀] [Deci…

--- 原说明 ---
The trivial group-with-zero hom is absorbing for composition.
-/
lemma one_comp {M₀ N₀ G₀ : Type*}
    [GroupWithZero M₀]
    [MulZeroOneClass N₀] [Nontrivial N₀] [NoZeroDivisors N₀]
    [MulZeroOneClass G₀]
    [DecidablePred fun x : M₀ ↦ x = 0] [DecidablePred fun x : N₀ ↦ x = 0]
    (f : M₀ →*₀ N₀) :
    (1 : N₀ →*₀ G₀).comp f = (1 : M₀ →*₀ G₀) :=
  ext <| one_apply_apply_eq _

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`G₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
/-
**MonoidWithZeroHom.inl** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inl [DecidablePred fun x : G₀ => x = 0] : G₀ ->*₀ WithZero (G₀ˣ × H₀ˣ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism fr
om
`G₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identif
ied
as their product.
-/
def inl [DecidablePred fun x : G₀ ↦ x = 0] : G₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inl _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism from
`H₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identified
as their product. -/
/-
**MonoidWithZeroHom.inr** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inr [DecidablePred fun x : H₀ => x = 0] : H₀ ->*₀ WithZero (G₀ˣ × H₀ˣ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given groups with zero `G₀`, `H₀`, the natural inclusion ordered homomorphism fr
om
`H₀` to `WithZero (G₀ˣ × H₀ˣ)`, which is the group with zero that can be identif
ied
as their product.
-/
def inr [DecidablePred fun x : H₀ ↦ x = 0] : H₀ →*₀ WithZero (G₀ˣ × H₀ˣ) :=
  (WithZero.map' (.inr _ _)).comp
    (.ofClass WithZero.withZeroUnitsEquiv.symm)

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `G₀`, which is the group with zero that can be identified
as their product. -/
/-
**MonoidWithZeroHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：fst : WithZero (G₀ˣ × H₀ˣ) ->*₀ G₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0

--- 原说明 ---
Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `G₀`, which is the group with zero that can be identif
ied
as their product.
-/
def fst : WithZero (G₀ˣ × H₀ˣ) →*₀ G₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.fst ..))

/-- Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `H₀`, which is the group with zero that can be identified
as their product. -/
/-
**MonoidWithZeroHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：snd : WithZero (G₀ˣ × H₀ˣ) ->*₀ H₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0

--- 原说明 ---
Given groups with zero `G₀`, `H₀`, the natural projection homomorphism from
`WithZero (G₀ˣ × H₀ˣ)` to `H₀`, which is the group with zero that can be identif
ied
as their product.
-/
def snd : WithZero (G₀ˣ × H₀ˣ) →*₀ H₀ :=
  WithZero.lift' ((Units.coeHom _).comp (.snd ..))

variable {G₀ H₀}

@[simp]
/-
**MonoidWithZeroHom.inl_apply_unit** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：inl_apply_unit [DecidablePred fun x : G₀ => x = 0] (x : G₀ˣ) : inl G₀ H₀ x
 = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ))
参数：x : G₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.withZeroUnitsEquiv_symm_apply`：∀ {G : Type u_4} [inst : GroupWi
thZero G] [inst_1 : DecidablePred fun a => a = 0] (a : G),   WithZero.withZeroUn
itsEquiv.symm a = if h : a =…
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_apply_unit [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀ˣ) :
    inl G₀ H₀ x = ((x, (1 : H₀ˣ)) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inl]

@[simp]
/-
**MonoidWithZeroHom.inr_apply_unit** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：inr_apply_unit [DecidablePred fun x : H₀ => x = 0] (x : H₀ˣ) : inr G₀ H₀ x
 = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ))
参数：x : H₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithZero.withZeroUnitsEquiv_symm_apply`：∀ {G : Type u_4} [inst : GroupWi
thZero G] [inst_1 : DecidablePred fun a => a = 0] (a : G),   WithZero.withZeroUn
itsEquiv.symm a = if h : a =…
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_apply_unit [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀ˣ) :
    inr G₀ H₀ x = (((1 : G₀ˣ), x) : WithZero (G₀ˣ × H₀ˣ)) := by
  simp [inr]
/-
**MonoidWithZeroHom.fst_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {G₀ : Type u_1} {H₀ : Type u_2} [inst : GroupWithZero G₀] [inst_1 : Grou
pWithZero H₀] (x : G₀ˣ × H₀ˣ),   (MonoidWithZeroHom.fst G₀ H₀) ↑x = ↑x.1
参数：x : G₀ˣ × H₀ˣ；MonoidWithZeroHom.fst G₀ H₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma fst_apply_coe (x : G₀ˣ × H₀ˣ) : fst G₀ H₀ x = x.fst := by rfl
/-
**MonoidWithZeroHom.snd_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：∀ {G₀ : Type u_1} {H₀ : Type u_2} [inst : GroupWithZero G₀] [inst_1 : Grou
pWithZero H₀] (x : G₀ˣ × H₀ˣ),   (MonoidWithZeroHom.snd G₀ H₀) ↑x = ↑x.2
参数：x : G₀ˣ × H₀ˣ；MonoidWithZeroHom.snd G₀ H₀。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma snd_apply_coe (x : G₀ˣ × H₀ˣ) : snd G₀ H₀ x = x.snd := by rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MonoidWithZeroHom.fst_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：fst_inl [DecidablePred fun x : G₀ => x = 0] (x : G₀) : fst _ H₀ (inl _ _ x
) = x
参数：x : G₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
-/
theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    fst _ H₀ (inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, fst, inl]

@[simp]
/-
**MonoidWithZeroHom.fst_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：fst_comp_inl [DecidablePred fun x : G₀ => x = 0] : (fst ..).comp (inl G₀ H
₀) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `MonoidWithZeroHom.fst_inl`：fst_inl [DecidablePred fun x : G₀ => x = 0] (
x : G₀) : fst _ H₀ (inl _ _ x) = x
-/
theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (fst ..).comp (inl G₀ H₀) = .id _ :=
  ext fun _ ↦ fst_inl _

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MonoidWithZeroHom.snd_comp_inl** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：snd_comp_inl [DecidablePred fun x : G₀ => x = 0] : (snd ..).comp (inl G₀ H
₀) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用引理 `MonoidWithZeroHom.one_apply_val_unit`：one_apply_val_unit {M₀ N₀ : Type*}
 [MonoidWithZero M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [N
ontrivial M₀] [NoZeroDivis…
-/
theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (snd ..).comp (inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, snd, inl]
/-
**MonoidWithZeroHom.snd_inl_apply_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWi
thZeroHom`。
形式化陈述：snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ => x = 0] {x : G₀} (hx 
: x != 0) : snd _ _ (inl _ H₀ x) = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.comp_apply`：comp_apply (g : β ->*₀ γ) (f : α ->*₀ β) (
x : α) : g.comp f x = g (f x)
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `MonoidWithZeroHom.snd_comp_inl`：snd_comp_inl [DecidablePred fun x : G₀ =
> x = 0] : (snd ..).comp (inl G₀ H₀) = 1
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
-/
theorem snd_inl_apply_of_ne_zero [DecidablePred fun x : G₀ ↦ x = 0] {x : G₀} (hx : x ≠ 0) :
    snd _ _ (inl _ H₀ x) = 1 := by
  rw [← comp_apply, snd_comp_inl, one_apply_of_ne_zero hx]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MonoidWithZeroHom.fst_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：fst_comp_inr [DecidablePred fun x : H₀ => x = 0] : (fst ..).comp (inr G₀ H
₀) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `MonoidWithZeroHom.one_apply_zero`：one_apply_zero {M₀ N₀ : Type*} [MulZer
oOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [Nontrivi
al M₀] [NoZeroDivisors…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用引理 `MonoidWithZeroHom.one_apply_val_unit`：one_apply_val_unit {M₀ N₀ : Type*}
 [MonoidWithZero M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 0] [N
ontrivial M₀] [NoZeroDivis…
-/
theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (fst ..).comp (inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, fst, inr]
/-
**MonoidWithZeroHom.fst_inr_apply_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWi
thZeroHom`。
形式化陈述：fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ => x = 0] {x : H₀} (hx 
: x != 0) : fst _ _ (inr G₀ _ x) = 1
参数：hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MonoidWithZeroHom.comp_apply`：comp_apply (g : β ->*₀ γ) (f : α ->*₀ β) (
x : α) : g.comp f x = g (f x)
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.noZeroDivisors`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀
], NoZeroDivisors G₀
· 使用定理 `MonoidWithZeroHom.fst_comp_inr`：fst_comp_inr [DecidablePred fun x : H₀ =
> x = 0] : (fst ..).comp (inr G₀ H₀) = 1
· 使用引理 `MonoidWithZeroHom.one_apply_of_ne_zero`：one_apply_of_ne_zero {M₀ N₀ : Ty
pe*} [MulZeroOneClass M₀] [MulZeroOneClass N₀] [DecidablePred fun x : M₀ => x = 
0] [Nontrivial M₀] [NoZeroDi…
-/
theorem fst_inr_apply_of_ne_zero [DecidablePred fun x : H₀ ↦ x = 0] {x : H₀} (hx : x ≠ 0) :
    fst _ _ (inr G₀ _ x) = 1 := by
  rw [← comp_apply, fst_comp_inr, one_apply_of_ne_zero hx]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**MonoidWithZeroHom.snd_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：snd_inr [DecidablePred fun x : H₀ => x = 0] (x : H₀) : snd _ _ (inr G₀ _ x
) = x
参数：x : H₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WithZero.lift'`：lift'_zero (f : α ->* β) : lift' f (0 : WithZero α) = 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
-/
theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    snd _ _ (inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, snd, inr]

@[simp]
/-
**MonoidWithZeroHom.snd_comp_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：snd_comp_inr [DecidablePred fun x : H₀ => x = 0] : (snd ..).comp (inr G₀ H
₀) = .id _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHom.ext`：∀ {α : Type u_2} {β : Type u_3} [inst : MulZeroOn
eClass α] [inst_1 : MulZeroOneClass β] ⦃f g : α →*₀ β⦄,   (∀ (x : α), f x = g x)
 → f = g
· 使用定理 `MonoidWithZeroHom.snd_inr`：snd_inr [DecidablePred fun x : H₀ => x = 0] (
x : H₀) : snd _ _ (inr G₀ _ x) = x
-/
theorem snd_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (snd ..).comp (inr G₀ H₀) = .id _ :=
  ext fun _ ↦ snd_inr _
/-
**MonoidWithZeroHom.inl_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inl_injective [DecidablePred fun x : G₀ => x = 0] : Function.Injective (in
l G₀ H₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.fst_inl`：fst_inl [DecidablePred fun x : G₀ => x = 0] (
x : G₀) : fst _ H₀ (inl _ _ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (inl G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨fst .., fun _ ↦ by simp⟩
/-
**MonoidWithZeroHom.inr_injective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`。
形式化陈述：inr_injective [DecidablePred fun x : H₀ => x = 0] : Function.Injective (in
r G₀ H₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.snd_inr`：snd_inr [DecidablePred fun x : H₀ => x = 0] (
x : H₀) : snd _ _ (inr G₀ _ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (inr G₀ H₀) :=
  Function.HasLeftInverse.injective ⟨snd .., fun _ ↦ by simp⟩
/-
**MonoidWithZeroHom.fst_surjective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：fst_surjective : Function.Surjective (fst G₀ H₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.fst_inl`：fst_inl [DecidablePred fun x : G₀ => x = 0] (
x : G₀) : fst _ H₀ (inl _ _ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fst_surjective : Function.Surjective (fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inl .., fun _ ↦ by simp⟩
/-
**MonoidWithZeroHom.snd_surjective** 是 Mathlib 中的一个引理，位于命名空间 `MonoidWithZeroHom`
。
形式化陈述：snd_surjective : Function.Surjective (snd G₀ H₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHom.snd_inr`：snd_inr [DecidablePred fun x : H₀ => x = 0] (
x : H₀) : snd _ _ (inr G₀ _ x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_surjective : Function.Surjective (snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨inr .., fun _ ↦ by simp⟩

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidWithZeroHom.inl_mul_inr_eq_mk_of_unit** 是 Mathlib 中的一个定理，位于命名空间 `MonoidW
ithZeroHom`。
形式化陈述：inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) : (inl G₀ H₀ m * inr G₀ H₀ n
) = (m, n)
参数：m : G₀ˣ；n : H₀ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (inl G₀ H₀ m * inr G₀ H₀ n) = (m, n) := by
  simp [inl, WithZero.withZeroUnitsEquiv, inr, ← WithZero.coe_mul]

set_option backward.isDefEq.respectTransparency false in
/-
**MonoidWithZeroHom.commute_inl_inr** 是 Mathlib 中的一个定理，位于命名空间 `MonoidWithZeroHom
`。
形式化陈述：commute_inl_inr (m : G₀) (n : H₀) : Commute (inl G₀ H₀ m) (inr G₀ H₀ n)
参数：m : G₀；n : H₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.eq_zero_or_unit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G
₀] (a : G₀), a = 0 ∨ ∃ u, a = ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Units.mk0_val`：mk0_val (u : G₀ˣ) (h : (u : G₀) != 0) : mk0 (u : G₀) h = 
u
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (inl G₀ H₀ m) (inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [inl, inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end MonoidWithZeroHom

