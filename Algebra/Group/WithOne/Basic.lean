/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.WithOne.Defs

/-!
# More operations on `WithOne` and `WithZero`

This file defines various bundled morphisms on `WithOne` and `WithZero`
that were not available in `Algebra/Group/WithOne/Defs`.

## Main definitions

* `WithOne.lift`, `WithZero.lift`
* `WithOne.map`, `WithZero.map`
-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

namespace WithOne

set_option backward.isDefEq.respectTransparency false in
@[to_additive]
/-
**WithOne.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `WithOne`。
形式化陈述：instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) where inv_
inv a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveInv [InvolutiveInv α] : InvolutiveInv (WithOne α) where
  inv_inv a := (Option.map_map _ _ _).trans <| by simp_rw [inv_comp_inv, Option.map_id, id]

section

/-- `WithOne.coe` as a bundled morphism -/
@[to_additive (attr := simps apply) /-- `WithZero.coe` as a bundled morphism -/]
/-
**WithOne.coeMulHom** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：coeMulHom [Mul α] : α ->ₙ* WithOne α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WithOne.coe` as a bundled morphism
-/
def coeMulHom [Mul α] : α →ₙ* WithOne α where
  toFun := coe
  map_mul' _ _ := rfl

end

section lift

variable [Mul α] [MulOneClass β]

/-- Lift a semigroup homomorphism `f` to a bundled monoid homomorphism. -/
@[to_additive /--
Lift an additive semigroup homomorphism `f` to a bundled additive monoid homomorphism. -/]
/-
**WithOne.lift** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：lift : (α ->ₙ* β) ≃ (WithOne α ->* β) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift : (α →ₙ* β) ≃ (WithOne α →* β) where
  toFun f :=
    { toFun := WithOne.recOneCoe 1 f, map_one' := rfl,
      map_mul' := fun x y => x.cases_on (by simp) (fun x => y.cases_on (by simp) (f.map_mul x)) }
  invFun F := F.toMulHom.comp coeMulHom
  right_inv F := MonoidHom.ext fun x => WithOne.cases_on x F.map_one.symm (fun _ => rfl)

variable (f : α →ₙ* β)

@[to_additive (attr := simp)]
/-
**WithOne.lift_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：lift_coe (x : α) : lift f x = f x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_coe (x : α) : lift f x = f x :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：lift_one : lift f 1 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_one : lift f 1 = 1 :=
  rfl

@[to_additive]
/-
**WithOne.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：lift_unique (f : WithOne α ->* β) : f = lift (f.toMulHom.comp coeMulHom)
参数：f : WithOne α ->* β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_unique (f : WithOne α →* β) : f = lift (f.toMulHom.comp coeMulHom) :=
  (lift.apply_symm_apply f).symm

@[to_additive (attr := simp)]
/-
**WithOne.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：lift_symm_apply (f : WithOne α ->* β) (x : α) : lift.symm f x = f x
参数：f : WithOne α ->* β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply (f : WithOne α →* β) (x : α) : lift.symm f x = f x := rfl

@[to_additive]
/-
**WithOne.lift_symm_injective_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `WithOne`。
形式化陈述：lift_symm_injective_of_injective {f : WithOne α ->* β} (hf : Function.Inje
ctive f) : Function.Injective (lift.symm f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
lemma lift_symm_injective_of_injective {f : WithOne α →* β} (hf : Function.Injective f) :
    Function.Injective (lift.symm f) :=
  fun _ _ ↦ by simp [hf.eq_iff]

end lift

section Map

variable [Mul α] [Mul β] [Mul γ]

/-- Given a multiplicative map from `α → β` returns a monoid homomorphism
  from `WithOne α` to `WithOne β` -/
@[to_additive /-- Given an additive map from `α → β` returns an additive monoid homomorphism from
`WithZero α` to `WithZero β` -/]
/-
**WithOne.mapMulHom** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
形式化陈述：mapMulHom (f : α ->ₙ* β) : WithOne α ->* WithOne β
参数：f : α ->ₙ* β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mapMulHom (f : α →ₙ* β) : WithOne α →* WithOne β :=
  lift (coeMulHom.comp f)

@[to_additive (attr := simp)]
/-
**WithOne.mapMulHom_coe** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_coe (f : α ->ₙ* β) (a : α) : mapMulHom f (a : WithOne α) = f a
参数：f : α ->ₙ* β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMulHom_coe (f : α →ₙ* β) (a : α) : mapMulHom f (a : WithOne α) = f a :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne.mapMulHom_id** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_id : mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
-/
theorem mapMulHom_id : mapMulHom (MulHom.id α) = MonoidHom.id (WithOne α) := by
  ext x
  induction x <;> rfl

@[to_additive]
/-
**WithOne.mapMulHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : Mul α] [inst_1 : Mul β] {f : α →ₙ* β},
   Function.Injective ⇑f → Function.Injective ⇑(WithOne.mapMulHom f)
参数：WithOne.mapMulHom f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
-/
theorem mapMulHom_injective {f : α →ₙ* β} (hf : Function.Injective f) :
    Function.Injective (mapMulHom f)
  | none, none, _ => rfl
  | (a₁ : α), (a₂ : α), H => by simpa [hf.eq_iff] using H

@[to_additive]
/-
**WithOne.mapMulHom_injective'** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_injective' : Function.Injective (WithOne.mapMulHom (α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.ext`：MulHom.ext [Mul M] [Mul N] ⦃f g : M ->ₙ* N⦄ (h : forall x, f
 x = g x) : f = g
· 使用引理 `WithOne.coe_injective`：coe_injective : Function.Injective (coe : α -> Wi
thOne α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mapMulHom_injective' :
    Function.Injective (WithOne.mapMulHom (α := α) (β := β)) :=
  fun f g h ↦ MulHom.ext fun x ↦ coe_injective <| by simp only [← mapMulHom_coe, h]

@[to_additive (attr := simp)]
/-
**WithOne.mapMulHom_inj** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_inj {f g : α ->ₙ* β} : mapMulHom f = mapMulHom g ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `WithOne.mapMulHom_injective'`：mapMulHom_injective' : Function.Injective 
(WithOne.mapMulHom (α
-/
theorem mapMulHom_inj {f g : α →ₙ* β} : mapMulHom f = mapMulHom g ↔ f = g :=
  mapMulHom_injective'.eq_iff

@[to_additive]
/-
**WithOne.mapMulHom_mapMulHom** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_mapMulHom (f : α ->ₙ* β) (g : β ->ₙ* γ) (x) : mapMulHom g (mapMu
lHom f x) = mapMulHom (g.comp f) x
参数：f : α ->ₙ* β；g : β ->ₙ* γ；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mapMulHom_mapMulHom (f : α →ₙ* β) (g : β →ₙ* γ) (x) :
    mapMulHom g (mapMulHom f x) = mapMulHom (g.comp f) x := by
  induction x <;> rfl

@[to_additive (attr := simp)]
/-
**WithOne.mapMulHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
形式化陈述：mapMulHom_comp (f : α ->ₙ* β) (g : β ->ₙ* γ) : mapMulHom (g.comp f) = (map
MulHom g).comp (mapMulHom f)
参数：f : α ->ₙ* β；g : β ->ₙ* γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithOne.mapMulHom_mapMulHom`：mapMulHom_mapMulHom (f : α ->ₙ* β) (g : β -
>ₙ* γ) (x) : mapMulHom g (mapMulHom f x) = mapMulHom (g.comp f) x
-/
theorem mapMulHom_comp (f : α →ₙ* β) (g : β →ₙ* γ) :
    mapMulHom (g.comp f) = (mapMulHom g).comp (mapMulHom f) :=
  MonoidHom.ext fun x => (mapMulHom_mapMulHom f g x).symm

/-- A version of `Equiv.optionCongr` for `WithOne`. -/
@[to_additive (attr := simps apply) /-- A version of `Equiv.optionCongr` for `WithZero`. -/]
/-
**WithOne._root_.MulEquiv.withOneCongr** 是 Mathlib 中的一个定义，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Equiv.optionCongr` for `WithOne`.
-/
def _root_.MulEquiv.withOneCongr (e : α ≃* β) : WithOne α ≃* WithOne β :=
  { mapMulHom e.toMulHom with
    toFun := mapMulHom e.toMulHom, invFun := mapMulHom e.symm.toMulHom,
    left_inv := (by induction · <;> simp)
    right_inv := (by induction · <;> simp) }

@[to_additive (attr := simp)]
/-
**WithOne._root_.MulEquiv.withOneCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquiv.withOneCongr_refl : (MulEquiv.refl α).withOneCongr = MulEquiv.refl _ :=
  MulEquiv.toMonoidHom_injective mapMulHom_id

@[to_additive (attr := simp)]
/-
**WithOne._root_.MulEquiv.withOneCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquiv.withOneCongr_symm (e : α ≃* β) :
    e.withOneCongr.symm = e.symm.withOneCongr :=
  rfl

@[to_additive (attr := simp)]
/-
**WithOne._root_.MulEquiv.withOneCongr_trans** 是 Mathlib 中的一个定理，位于命名空间 `WithOne`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquiv.withOneCongr_trans (e₁ : α ≃* β) (e₂ : β ≃* γ) :
    e₁.withOneCongr.trans e₂.withOneCongr = (e₁.trans e₂).withOneCongr :=
  MulEquiv.toMonoidHom_injective (mapMulHom_comp _ _).symm

end Map

end WithOne

