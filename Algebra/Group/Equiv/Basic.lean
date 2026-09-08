/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Spread

/-!
# Multiplicative and additive equivs

This file contains basic results on `MulEquiv` and `AddEquiv`.

## Tags

Equiv, MulEquiv, AddEquiv
-/

@[expose] public section

assert_not_exists Fintype

open Function

variable {F α β M M₁ M₂ M₃ N N₁ N₂ N₃ P Q G H : Type*}

variable [EquivLike F α β]

@[to_additive]
/-
**MulEquivClass.toMulEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulEquivClass.toMulEquiv_injective [Mul α] [Mul β] [MulEquivClass F α β] :
 Function.Injective ((↑) : F -> α ≃* β)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem MulEquivClass.toMulEquiv_injective [Mul α] [Mul β] [MulEquivClass F α β] :
    Function.Injective ((↑) : F → α ≃* β) :=
  fun _ _ e ↦ DFunLike.ext _ _ fun a ↦ congr_arg (fun e : α ≃* β ↦ e.toFun a) e
/-
**MulEquivClass.isDedekindFiniteMonoid_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquivCl
ass`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : EquivLike F α β] [i
nst_1 : MulOne α] [inst_2 : MulOne β]   [MulEquivClass F α β] [OneHomClass F α β
] (f : F), IsDedekindFiniteMonoid α ↔ IsDedekindFiniteMonoid β
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MulEquivClass.map_mul`：∀ {F : Type u_9} {A : outParam (Type u_10)} {B : 
outParam (Type u_11)} {inst : Mul A} {inst_1 : Mul B}   {inst_2 : EquivLike F A 
B} [self : …
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `IsDedekindFiniteMonoid.of_injective`：∀ {M : Type u_4} {N : Type u_5} {F 
: Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [Mo
noidHomClass F M N] (f : …
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
@[to_additive] theorem MulEquivClass.isDedekindFiniteMonoid_iff [MulOne α] [MulOne β]
    [MulEquivClass F α β] [OneHomClass F α β] (f : F) :
    IsDedekindFiniteMonoid α ↔ IsDedekindFiniteMonoid β where
  mp _ := let e := MulEquivClass.toMulEquiv f
    let g : β →* α := ⟨⟨e.symm, e.injective <| (e.right_inv ..).trans (map_one f).symm⟩, map_mul _⟩
    .of_injective g e.symm.injective
  mpr _ := let g : α →* β := ⟨⟨f, map_one f⟩, map_mul f⟩
    .of_injective g (EquivLike.injective f)

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive /-- The `AddEquiv` between two `AddMonoid`s with a unique element. -/]
/-
**MulEquiv.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `MulEquiv` between two monoids with a unique element.
-/
def ofUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N] : M ≃* N :=
  { Equiv.ofUnique M N with map_mul' := fun _ _ => Subsingleton.elim _ _ }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive /-- There is a unique additive monoid homomorphism between two additive monoids with
  a unique element. -/]
/-
**MulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N] : Unique (M ≃* N) where
  default := ofUnique
  uniq _ := ext fun _ => Subsingleton.elim _ _

variable (α M) in
/-- If `α` has a unique term, then the product of magmas `α → M` is isomorphic to `M`. -/
@[to_additive (attr := simps!)
/-- If `α` has a unique term, then the product of magmas `α → M` is isomorphic to `M`. -/]
/-
**MulEquiv.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：funUnique [Unique α] : (α -> M) ≃* M where toEquiv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def funUnique [Unique α] : (α → M) ≃* M where
  toEquiv := .funUnique ..
  map_mul' := by simp

end Mul

/-!
## Monoids
-/

/-- A multiplicative analogue of `Equiv.arrowCongr`,
where the equivalence between the targets is multiplicative.
-/
@[to_additive (attr := simps apply) /-- An additive analogue of `Equiv.arrowCongr`,
  where the equivalence between the targets is additive. -/]
/-
**MulEquiv.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) : (M
 -> P) ≃* (N -> Q) where toFun h n
参数：f : M ≃ N；g : P ≃* Q。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
def arrowCongr {M N P Q : Type*} [Mul P] [Mul Q] (f : M ≃ N) (g : P ≃* Q) :
    (M → P) ≃* (N → Q) where
  toFun h n := g (h (f.symm n))
  invFun k m := g.symm (k (f m))
  left_inv h := by ext; simp
  right_inv k := by ext; simp
  map_mul' h k := by ext; simp

section monoidHomCongrEquiv
variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [Monoid N] [Monoid N₁] [Monoid N₂] [Monoid N₃]

/-- The equivalence `(M₁ →* N) ≃ (M₂ →* N)` obtained by postcomposition with
a multiplicative equivalence `e : M₁ ≃* M₂`. -/
@[to_additive (attr := simps apply)
/-- The equivalence `(M₁ →+ N) ≃ (M₂ →+ N)` obtained by postcomposition with
an additive equivalence `e : M₁ ≃+ M₂`. -/]
/-
**MulEquiv.monoidHomCongrLeftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) : (M₁ ->* N) ≃ (M₂ ->* N) where toF
un f
参数：e : M₁ ≃* M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) : (M₁ →* N) ≃ (M₂ →* N) where
  toFun f := f.comp e.symm.toMonoidHom
  invFun f := f.comp e.toMonoidHom
  left_inv f := by ext; simp
  right_inv f := by ext; simp

/-- The equivalence `(M →* N₁) ≃ (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive (attr := simps apply)
/-- The equivalence `(M →+ N₁) ≃ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`. -/]
/-
**MulEquiv.monoidHomCongrRightEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRightEquiv (e : N₁ ≃* N₂) : (M ->* N₁) ≃ (M ->* N₂) where to
Fun
参数：e : N₁ ≃* N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomCongrRightEquiv (e : N₁ ≃* N₂) : (M →* N₁) ≃ (M →* N₂) where
  toFun := e.toMonoidHom.comp
  invFun := e.symm.toMonoidHom.comp
  left_inv f := by ext; simp
  right_inv f := by ext; simp

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrLeftEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeftEquiv_refl : monoidHomCongrLeftEquiv (.refl M) = .refl (
M ->* N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrLeftEquiv_refl : monoidHomCongrLeftEquiv (.refl M) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrRightEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRightEquiv_refl : monoidHomCongrRightEquiv (.refl N) = .refl
 (M ->* N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrRightEquiv_refl : monoidHomCongrRightEquiv (.refl N) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_monoidHomCongrLeftEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) : (monoidHomCongrLeftEquiv e).
symm = monoidHomCongrLeftEquiv (N
参数：e : M₁ ≃* M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma symm_monoidHomCongrLeftEquiv (e : M₁ ≃* M₂) :
    (monoidHomCongrLeftEquiv e).symm = monoidHomCongrLeftEquiv (N := N) e.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_monoidHomCongrRightEquiv** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_monoidHomCongrRightEquiv (e : N₁ ≃* N₂) : (monoidHomCongrRightEquiv e
).symm = monoidHomCongrRightEquiv (M
参数：e : N₁ ≃* N₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma symm_monoidHomCongrRightEquiv (e : N₁ ≃* N₂) :
    (monoidHomCongrRightEquiv e).symm = monoidHomCongrRightEquiv (M := M) e.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrLeftEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeftEquiv_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) : monoidHo
mCongrLeftEquiv (N
参数：e₁₂ : M₁ ≃* M₂；e₂₃ : M₂ ≃* M₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrLeftEquiv_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    monoidHomCongrLeftEquiv (N := N) (e₁₂.trans e₂₃) =
      (monoidHomCongrLeftEquiv e₁₂).trans (monoidHomCongrLeftEquiv e₂₃) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrRightEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRightEquiv_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) : monoidH
omCongrRightEquiv (M
参数：e₁₂ : N₁ ≃* N₂；e₂₃ : N₂ ≃* N₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrRightEquiv_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    monoidHomCongrRightEquiv (M := M) (e₁₂.trans e₂₃) =
      (monoidHomCongrRightEquiv e₁₂).trans (monoidHomCongrRightEquiv e₂₃) := rfl

end monoidHomCongrEquiv

section monoidHomCongr
variable [MulOneClass M] [MulOneClass M₁] [MulOneClass M₂] [MulOneClass M₃]
  [CommMonoid N] [CommMonoid N₁] [CommMonoid N₂] [CommMonoid N₃]

/-- The isomorphism `(M₁ →* N) ≃* (M₂ →* N)` obtained by postcomposition with
a multiplicative equivalence `e : M₁ ≃* M₂`. -/
@[to_additive (attr := simps! apply)
/-- The isomorphism `(M₁ →+ N) ≃+ (M₂ →+ N)` obtained by postcomposition with
an additive equivalence `e : M₁ ≃+ M₂`. -/]
/-
**MulEquiv.monoidHomCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeft (e : M₁ ≃* M₂) : (M₁ ->* N) ≃* (M₂ ->* N) where __
参数：e : M₁ ≃* M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomCongrLeft (e : M₁ ≃* M₂) : (M₁ →* N) ≃* (M₂ →* N) where
  __ := e.monoidHomCongrLeftEquiv
  map_mul' f g := by ext; simp

/-- The isomorphism `(M →* N₁) ≃* (M →* N₂)` obtained by postcomposition with
a multiplicative equivalence `e : N₁ ≃* N₂`. -/
@[to_additive (attr := simps! apply)
/-- The isomorphism `(M →+ N₁) ≃+ (M →+ N₂)` obtained by postcomposition with
an additive equivalence `e : N₁ ≃+ N₂`. -/]
/-
**MulEquiv.monoidHomCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRight (e : N₁ ≃* N₂) : (M ->* N₁) ≃* (M ->* N₂) where __
参数：e : N₁ ≃* N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def monoidHomCongrRight (e : N₁ ≃* N₂) : (M →* N₁) ≃* (M →* N₂) where
  __ := e.monoidHomCongrRightEquiv
  map_mul' f g := by ext; simp

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrLeft_refl** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeft_refl : monoidHomCongrLeft (.refl M) = .refl (M ->* N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrLeft_refl : monoidHomCongrLeft (.refl M) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrRight_refl** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRight_refl : monoidHomCongrRight (.refl N) = .refl (M ->* N)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrRight_refl : monoidHomCongrRight (.refl N) = .refl (M →* N) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_monoidHomCongrLeft** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_monoidHomCongrLeft (e : M₁ ≃* M₂) : (monoidHomCongrLeft e).symm = mon
oidHomCongrLeft (N
参数：e : M₁ ≃* M₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_monoidHomCongrLeft (e : M₁ ≃* M₂) :
    (monoidHomCongrLeft e).symm = monoidHomCongrLeft (N := N) e.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_monoidHomCongrRight** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_monoidHomCongrRight (e : N₁ ≃* N₂) : (monoidHomCongrRight e).symm = m
onoidHomCongrRight (M
参数：e : N₁ ≃* N₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_monoidHomCongrRight (e : N₁ ≃* N₂) :
    (monoidHomCongrRight e).symm = monoidHomCongrRight (M := M) e.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrLeft_trans** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrLeft_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) : monoidHomCong
rLeft (N
参数：e₁₂ : M₁ ≃* M₂；e₂₃ : M₂ ≃* M₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrLeft_trans (e₁₂ : M₁ ≃* M₂) (e₂₃ : M₂ ≃* M₃) :
    monoidHomCongrLeft (N := N) (e₁₂.trans e₂₃) =
      (monoidHomCongrLeft e₁₂).trans (monoidHomCongrLeft e₂₃) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.monoidHomCongrRight_trans** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：monoidHomCongrRight_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) : monoidHomCon
grRight (M
参数：e₁₂ : N₁ ≃* N₂；e₂₃ : N₂ ≃* N₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma monoidHomCongrRight_trans (e₁₂ : N₁ ≃* N₂) (e₂₃ : N₂ ≃* N₃) :
    monoidHomCongrRight (M := M) (e₁₂.trans e₂₃) =
      (monoidHomCongrRight e₁₂).trans (monoidHomCongrRight e₂₃) := rfl

end monoidHomCongr

/-- A family of multiplicative equivalences `Π j, (Ms j ≃* Ns j)` generates a
multiplicative equivalence between `Π j, Ms j` and `Π j, Ns j`.

This is the `MulEquiv` version of `Equiv.piCongrRight`, and the dependent version of
`MulEquiv.arrowCongr`.
-/
@[to_additive (attr := simps apply)
  /-- A family of additive equivalences `Π j, (Ms j ≃+ Ns j)`
  generates an additive equivalence between `Π j, Ms j` and `Π j, Ns j`.

  This is the `AddEquiv` version of `Equiv.piCongrRight`, and the dependent version of
  `AddEquiv.arrowCongr`. -/]
/-
**MulEquiv.piCongrRight** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：piCongrRight {η : Type*} {Ms Ns : η -> Type*} [forall j, Mul (Ms j)] [fora
ll j, Mul (Ns j)] (es : forall j, Ms j ≃* Ns j) : (forall j, Ms j) ≃* forall j, 
Ns j
参数：Ms j；Ns j；es : forall j, Ms j ≃* Ns j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def piCongrRight {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (∀ j, Ms j) ≃* ∀ j, Ns j :=
  { Equiv.piCongrRight fun j => (es j).toEquiv with
    toFun := fun x j => es j (x j),
    invFun := fun x j => (es j).symm (x j),
    map_mul' := fun x y => funext fun j => map_mul (es j) (x j) (y j) }

@[to_additive (attr := simp)]
/-
**MulEquiv.piCongrRight_refl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：piCongrRight_refl {η : Type*} {Ms : η -> Type*} [forall j, Mul (Ms j)] : (
piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _
参数：Ms j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_refl {η : Type*} {Ms : η → Type*} [∀ j, Mul (Ms j)] :
    (piCongrRight fun j => MulEquiv.refl (Ms j)) = MulEquiv.refl _ := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.piCongrRight_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：piCongrRight_symm {η : Type*} {Ms Ns : η -> Type*} [forall j, Mul (Ms j)] 
[forall j, Mul (Ns j)] (es : forall j, Ms j ≃* Ns j) : (piCongrRight es).symm = 
piCongrRight fun i => (es i).symm
参数：Ms j；Ns j；es : forall j, Ms j ≃* Ns j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_symm {η : Type*} {Ms Ns : η → Type*} [∀ j, Mul (Ms j)] [∀ j, Mul (Ns j)]
    (es : ∀ j, Ms j ≃* Ns j) : (piCongrRight es).symm = piCongrRight fun i => (es i).symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.piCongrRight_trans** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：piCongrRight_trans {η : Type*} {Ms Ns Ps : η -> Type*} [forall j, Mul (Ms 
j)] [forall j, Mul (Ns j)] [forall j, Mul (Ps j)] (es : forall j, Ms j ≃* Ns j) 
(fs : forall j, Ns j ≃* Ps j) : (piCongrRight es).trans (piCongrRight fs) = piCo
ngrRight fun i => (es i).trans (fs i)
参数：Ms j；Ns j；Ps j；es : forall j, Ms j ≃* Ns j；fs : forall j, Ns j ≃* Ps j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem piCongrRight_trans {η : Type*} {Ms Ns Ps : η → Type*} [∀ j, Mul (Ms j)]
    [∀ j, Mul (Ns j)] [∀ j, Mul (Ps j)] (es : ∀ j, Ms j ≃* Ns j) (fs : ∀ j, Ns j ≃* Ps j) :
    (piCongrRight es).trans (piCongrRight fs) = piCongrRight fun i => (es i).trans (fs i) := rfl

/-- A family indexed by a type with a unique element
is `MulEquiv` to the element at the single index. -/
@[to_additive (attr := simps!)
  /-- A family indexed by a type with a unique element
  is `AddEquiv` to the element at the single index. -/]
/-
**MulEquiv.piUnique** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：piUnique {ι : Type*} (M : ι -> Type*) [forall j, Mul (M j)] [Unique ι] : (
forall j, M j) ≃* M default
参数：M : ι -> Type*；M j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def piUnique {ι : Type*} (M : ι → Type*) [∀ j, Mul (M j)] [Unique ι] :
    (∀ j, M j) ≃* M default :=
  { Equiv.piUnique M with map_mul' := fun _ _ => Pi.mul_apply _ _ _ }

end MulEquiv

namespace Equiv

section InvolutiveInv

variable (G) [InvolutiveInv G]

/-- Inversion on a `Group` or `GroupWithZero` is a permutation of the underlying type. -/
@[to_additive (attr := simps! -fullyApplied apply)
    /-- Negation on an `AddGroup` is a permutation of the underlying type. -/]
/-
**Equiv.inv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：(G : Type u_14) → [InvolutiveInv G] → Equiv.Perm G
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inv_involutive`：inv_involutive : Function.Involutive (Inv.inv : G -> G)
-/
protected def inv : Perm G :=
  inv_involutive.toPerm _

variable {G}

@[to_additive (attr := simp)]
/-
**Equiv.inv_symm** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：inv_symm : (Equiv.inv G).symm = Equiv.inv G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem inv_symm : (Equiv.inv G).symm = Equiv.inv G := rfl

end InvolutiveInv

end Equiv

