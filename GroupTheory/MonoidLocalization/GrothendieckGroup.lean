/-
Copyright (c) 2025 Alex J. Best, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Maps

/-!
# Grothendieck group

The Grothendieck group of a commutative monoid `M` is the "smallest" commutative group `G`
containing `M`, in the sense that monoid homs `M → H` are in bijection with monoid homs `G → H` for
any commutative group `H`.

Note that "Grothendieck group" also refers to the analogous construction in an abelian category
obtained by formally making the last term of each short exact sequence invertible.

### References

* [*Grothendieck group*, Wikipedia](https://en.wikipedia.org/wiki/Grothendieck_group#Grothendieck_group_of_a_commutative_monoid)
-/

@[expose] public section

open Function Localization

namespace Algebra
variable {M G : Type*} [CommMonoid M] [CommGroup G]

variable (M) in
/-- The Grothendieck group of a monoid `M` is the localization at its top submonoid. -/
@[to_additive
/-- The Grothendieck group of an additive monoid `M` is the localization at its top submonoid. -/]
/-
**Algebra.GrothendieckGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra`。
形式化陈述：GrothendieckGroup : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev GrothendieckGroup : Type _ := Localization (⊤ : Submonoid M)

namespace GrothendieckGroup

/-- The inclusion from a commutative monoid `M` to its Grothendieck group.

Note that this is only injective if `M` is cancellative. -/
@[to_additive
/-- The inclusion from an additive commutative monoid `M` to its Grothendieck group.

Note that this is only injective if `M` is cancellative. -/]
/-
**Algebra.GrothendieckGroup.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebra.Grothendieck
Group`。
形式化陈述：of : M ->* GrothendieckGroup M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev of : M →* GrothendieckGroup M := (monoidOf ⊤).toMonoidHom

@[to_additive]
/-
**Algebra.GrothendieckGroup.of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Grot
hendieckGroup`。
形式化陈述：of_injective [IsCancelMul M] : Injective (of (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma of_injective [IsCancelMul M] : Injective (of (M := M)) :=
  fun m₁ m₂ ↦ by simp [of, ← mk_one_eq_monoidOf_mk, mk_eq_mk_iff']

@[to_additive]
/-
**Algebra.GrothendieckGroup.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.GrothendieckGrou
p`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (GrothendieckGroup M) where
  inv := rec (fun m s ↦ (.mk s ⟨m, Submonoid.mem_top m⟩ : GrothendieckGroup M))
    fun {m₁ m₂ s₁ s₂} h ↦ by simpa [r_iff_exists, mk_eq_mk_iff, eq_comm, mul_comm] using h

@[to_additive (attr := simp)]
/-
**Algebra.GrothendieckGroup.inv_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Grothendie
ckGroup`。
形式化陈述：inv_mk (m : M) (s : (⊤ : Submonoid M)) : (mk m s)⁻¹ = .mk s ⟨m, Submonoid.
mem_top _⟩
参数：m : M；s : (⊤ : Submonoid M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_mk (m : M) (s : (⊤ : Submonoid M)) : (mk m s)⁻¹ = .mk s ⟨m, Submonoid.mem_top _⟩ := rfl

/-- The Grothendieck group is a group. -/
@[to_additive /-- The Grothendieck group is a group. -/]
/-
**Algebra.GrothendieckGroup.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Gro
thendieckGroup`。
形式化陈述：instCommGroup : CommGroup (GrothendieckGroup M) where __ : CommMonoid (Gro
thendieckGroup M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck group is a group.
-/
instance instCommGroup : CommGroup (GrothendieckGroup M) where
  __ : CommMonoid (GrothendieckGroup M) := inferInstance
  inv_mul_cancel a := by
    cases a using ind
    rw [inv_mk, mk_eq_monoidOf_mk', ← Submonoid.LocalizationMap.mk'_mul]
    convert! Submonoid.LocalizationMap.mk'_self' _ _
    rw [mul_comm, Submonoid.coe_mul]

@[to_additive (attr := simp)]
/-
**Algebra.GrothendieckGroup.mk_div_mk** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Grothen
dieckGroup`。
形式化陈述：mk_div_mk (m₁ m₂ : M) (s₁ s₂ : (⊤ : Submonoid M)) : mk m₁ s₁ / mk m₂ s₂ = 
.mk (m₁ * s₂) ⟨s₁ * m₂, Submonoid.mem_top _⟩
参数：m₁ m₂ : M；s₁ s₂ : (⊤ : Submonoid M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.mem_top`：mem_top (x : M) : x in (⊤ : Submonoid M)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Localization.mk_mul`：mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (
a * c) (b * d)
-/
lemma mk_div_mk (m₁ m₂ : M) (s₁ s₂ : (⊤ : Submonoid M)) :
    mk m₁ s₁ / mk m₂ s₂ = .mk (m₁ * s₂) ⟨s₁ * m₂, Submonoid.mem_top _⟩ := by
  simp [div_eq_mul_inv, mk_mul]; rfl

/-- A monoid homomorphism from a monoid `M` to a group `G` lifts to a group homomorphism from the
Grothendieck group of `M` to `G`. -/
@[to_additive (attr := simps symm_apply)
/-- A monoid homomorphism from a monoid `M` to a group `G` lifts to a group homomorphism from the
Grothendieck group of `M` to `G`. -/]
/-
**Algebra.GrothendieckGroup.lift** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Grothendieck
Group`。
形式化陈述：lift : (M ->* G) ≃ (GrothendieckGroup M ->* G) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def lift : (M →* G) ≃ (GrothendieckGroup M →* G) where
  toFun f := (monoidOf ⊤).lift (g := f) fun _ ↦ Group.isUnit _
  invFun f := f.comp of
  left_inv f := by ext; simp
  right_inv f := by ext; simp

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**Algebra.GrothendieckGroup.lift_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebra.Grothe
ndieckGroup`。
形式化陈述：lift_apply (f : M ->* G) (x : GrothendieckGroup M) : lift f x = f ((monoid
Of ⊤).sec x).1 / f ((monoidOf ⊤).sec x).2
参数：f : M ->* G；x : GrothendieckGroup M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.LocalizationMap.lift_apply`：lift_apply (z) : f.lift hg z = g (
f.sec z).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec z).2)⁻¹
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
-/
lemma lift_apply (f : M →* G) (x : GrothendieckGroup M) :
    lift f x = f ((monoidOf ⊤).sec x).1 / f ((monoidOf ⊤).sec x).2 := by
  simp [lift, (monoidOf ⊤).lift_apply, div_eq_mul_inv]; congr

end Algebra.GrothendieckGroup

