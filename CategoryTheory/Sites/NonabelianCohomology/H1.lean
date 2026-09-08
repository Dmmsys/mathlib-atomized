/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.Grp.Basic

/-! # The cohomology of a sheaf of groups in degree 1

In this file, we shall define the cohomology in degree 1 of a sheaf
of groups (TODO).

Currently, given a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` and a family
of objects `U : I → C`, we define 1-cochains/1-cocycles/H^1 with values
in `G` over `U`. (This definition neither requires the assumption that `G`
is a sheaf, nor that `U` covers the terminal object.)
As we do not assume that `G` is a presheaf of abelian groups, this
cohomology theory is only defined in low degrees; in the abelian
case, it would be a particular case of Čech cohomology (TODO).

## TODO

* show that if `1 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 1` is a short exact sequence of sheaves
  of groups, and `x₃` is a global section of `G₃` which can be locally lifted
  to a section of `G₂`, there is an associated canonical cohomology class of `G₁`
  which is trivial iff `x₃` can be lifted to a global section of `G₂`.
  (This should hold more generally if `G₂` is a sheaf of sets on which `G₁` acts
  freely, and `G₃` is the quotient sheaf.)
* deduce a similar result for abelian sheaves
* when the notion of quasi-coherent sheaves on schemes is defined, show that
  if `0 ⟶ Q ⟶ M ⟶ N ⟶ 0` is an exact sequence of abelian sheaves over a scheme `X`
  and `Q` is the underlying sheaf of a quasi-coherent sheaf, then `M(U) ⟶ N(U)`
  is surjective for any affine open `U`.
* take the colimit of `OneCohomology G U` over all covering families `U` (for
  a Grothendieck topology)

# References

* [J. Frenkel, *Cohomologie non abélienne et espaces fibrés*][frenkel1957]

-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GrpCat.{w}) {I : Type w'} (U : I → C)

/-- A zero cochain consists of a family of sections. -/
/-
**CategoryTheory.PresheafOfGroups.ZeroCochain** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.PresheafOfGroups`。
形式化陈述：ZeroCochain
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A zero cochain consists of a family of sections.
-/
def ZeroCochain := ∀ (i : I), G.obj (Opposite.op (U i))
/-
**CategoryTheory.PresheafOfGroups.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pre
sheafOfGroups`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (ZeroCochain G U) := Pi.group

namespace Cochain₀

@[simp]
/-
**CategoryTheory.PresheafOfGroups.Cochain₀.one_apply** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PresheafOfGroups.Cochain₀`。
形式化陈述：one_apply (i : I) : (1 : ZeroCochain G U) i = 1
参数：i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_apply (i : I) : (1 : ZeroCochain G U) i = 1 := rfl

@[simp]
/-
**CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PresheafOfGroups.Cochain₀`。
形式化陈述：inv_apply (γ : ZeroCochain G U) (i : I) : γ⁻¹ i = (γ i)⁻¹
参数：γ : ZeroCochain G U；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_apply (γ : ZeroCochain G U) (i : I) : γ⁻¹ i = (γ i)⁻¹ := rfl

@[simp]
/-
**CategoryTheory.PresheafOfGroups.Cochain₀.mul_apply** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PresheafOfGroups.Cochain₀`。
形式化陈述：mul_apply (γ₁ γ₂ : ZeroCochain G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i
参数：γ₁ γ₂ : ZeroCochain G U；i : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_apply (γ₁ γ₂ : ZeroCochain G U) (i : I) : (γ₁ * γ₂) i = γ₁ i * γ₂ i := rfl

end Cochain₀

/-- A 1-cochain of a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` on a family `U : I → C` of objects
consists of the data of an element in `G.obj (Opposite.op T)` whenever we have elements
`i` and `j` in `I` and maps `a : T ⟶ U i` and `b : T ⟶ U j`, and it must satisfy a compatibility
with respect to precomposition. (When the binary product of `U i` and `U j` exists, this
data for all `T`, `a` and `b` corresponds to the data of a section of `G` on this product.) -/
@[ext]
/-
**CategoryTheory.PresheafOfGroups.OneCochain** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.PresheafOfGroups`。
形式化陈述：OneCochain where /-- the data involved in a 1-cochain -/ ev (i j : I) ⦃T :
 C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T) ev_precomp (i j : I) ⦃T 
T' : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) : G.map φ.op (ev i j a b) = e
v i j (φ ≫ a) (φ ≫ b)
参数：i j : I。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 1-cochain of a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` on a family `U : I → C` o
f objects
consists of the data of an element in `G.obj (Opposite.op T)` whenever we have e
lements
`i` and `j` in `I` and maps `a : T ⟶ U i` and `b : T ⟶ U j`, and it must satisfy
 a compatibility
with respect to precomposition. (When the binary product of `U i` and `U j` exis
ts, this
data for all `T`, `a` and `b` corresponds to the data of a section of `G` on thi
s product.)
-/
structure OneCochain where
  /-- the data involved in a 1-cochain -/
  ev (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) : G.obj (Opposite.op T)
  ev_precomp (i j : I) ⦃T T' : C⦄ (φ : T ⟶ T') (a : T' ⟶ U i) (b : T' ⟶ U j) :
    G.map φ.op (ev i j a b) = ev i j (φ ≫ a) (φ ≫ b) := by aesop

namespace OneCochain

attribute [simp] OneCochain.ev_precomp

/-
**CategoryTheory.PresheafOfGroups.OneCochain.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.PresheafOfGroups.OneCochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (OneCochain G U) where
  one := { ev := fun _ _ _ _ _ ↦ 1 }

@[simp]
/-
**CategoryTheory.PresheafOfGroups.OneCochain.one_ev** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PresheafOfGroups.OneCochain`。
形式化陈述：one_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) : (1 : OneCochain G U
).ev i j a b = 1
参数：i j : I；a : T ⟶ U i；b : T ⟶ U j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_ev (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (1 : OneCochain G U).ev i j a b = 1 := rfl

variable {G U}
/-
**CategoryTheory.PresheafOfGroups.OneCochain.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.PresheafOfGroups.OneCochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul (OneCochain G U) where
  mul γ₁ γ₂ := { ev := fun i j _ a b ↦ γ₁.ev i j a b * γ₂.ev i j a b }

@[simp]
/-
**CategoryTheory.PresheafOfGroups.OneCochain.mul_ev** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PresheafOfGroups.OneCochain`。
形式化陈述：mul_ev (γ₁ γ₂ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U
 j) : (γ₁ * γ₂).ev i j a b = γ₁.ev i j a b * γ₂.ev i j a b
参数：γ₁ γ₂ : OneCochain G U；i j : I；a : T ⟶ U i；b : T ⟶ U j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mul_ev (γ₁ γ₂ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ₁ * γ₂).ev i j a b = γ₁.ev i j a b * γ₂.ev i j a b := rfl
/-
**CategoryTheory.PresheafOfGroups.OneCochain.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.PresheafOfGroups.OneCochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inv (OneCochain G U) where
  inv γ := { ev := fun i j _ a b ↦ (γ.ev i j a b)⁻¹ }

@[simp]
/-
**CategoryTheory.PresheafOfGroups.OneCochain.inv_ev** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PresheafOfGroups.OneCochain`。
形式化陈述：inv_ev (γ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) 
: (γ⁻¹).ev i j a b = (γ.ev i j a b)⁻¹
参数：γ : OneCochain G U；i j : I；a : T ⟶ U i；b : T ⟶ U j。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inv_ev (γ : OneCochain G U) (i j : I) {T : C} (a : T ⟶ U i) (b : T ⟶ U j) :
    (γ⁻¹).ev i j a b = (γ.ev i j a b)⁻¹ := rfl
/-
**CategoryTheory.PresheafOfGroups.OneCochain.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.PresheafOfGroups.OneCochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (OneCochain G U) where
  mul_assoc _ _ _ := by ext; apply mul_assoc
  one_mul _ := by ext; apply one_mul
  mul_one _ := by ext; apply mul_one
  inv_mul_cancel _ := by ext; apply inv_mul_cancel

end OneCochain

/-- A 1-cocycle is a 1-cochain which satisfies the cocycle condition. -/
/-
**CategoryTheory.PresheafOfGroups.OneCocycle** 是 Mathlib 中的一个结构，位于命名空间 `Category
Theory.PresheafOfGroups`。
形式化陈述：OneCocycle extends OneCochain G U where ev_trans (i j k : I) ⦃T : C⦄ (a : 
T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) : ev i j a b * ev j k b c = ev i k a c
参数：i j k : I。
继承自：OneCochain G U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A 1-cocycle is a 1-cochain which satisfies the cocycle condition.
-/
structure OneCocycle extends OneCochain G U where
  ev_trans (i j k : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) (c : T ⟶ U k) :
      ev i j a b * ev j k b c = ev i k a c := by aesop

namespace OneCocycle

/-
**CategoryTheory.PresheafOfGroups.OneCocycle.** 是 Mathlib 中的一个实例，位于命名空间 `Categor
yTheory.PresheafOfGroups.OneCocycle`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (OneCocycle G U) where
  one := OneCocycle.mk 1

@[simp]
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.one_toOneCochain** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：one_toOneCochain : (1 : OneCocycle G U).toOneCochain = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma one_toOneCochain : (1 : OneCocycle G U).toOneCochain = 1 := rfl

@[simp]
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.ev_refl** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：ev_refl (γ : OneCocycle G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) : γ.ev i i a a 
= 1
参数：γ : OneCocycle G U；i : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `CategoryTheory.PresheafOfGroups.OneCocycle.ev_trans`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {G : CategoryTheory.Functor Cᵒᵖ GrpCat} {I
 : Type w'}   {U : I → C} (self : Categor…
-/
lemma ev_refl (γ : OneCocycle G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) :
    γ.ev i i a a = 1 := by
  simpa using γ.ev_trans i i i a a a
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.ev_symm** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：ev_symm (γ : OneCocycle G U) (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j)
 : γ.ev i j a b = (γ.ev j i b a)⁻¹
参数：γ : OneCocycle G U；i j : I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `CategoryTheory.PresheafOfGroups.OneCocycle.ev_trans`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {G : CategoryTheory.Functor Cᵒᵖ GrpCat} {I
 : Type w'}   {U : I → C} (self : Categor…
· 使用引理 `CategoryTheory.PresheafOfGroups.OneCocycle.ev_refl`：ev_refl (γ : OneCocy
cle G U) (i : I) ⦃T : C⦄ (a : T ⟶ U i) : γ.ev i i a a = 1
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
lemma ev_symm (γ : OneCocycle G U) (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j) :
    γ.ev i j a b = (γ.ev j i b a)⁻¹ := by
  rw [← mul_left_inj (γ.ev j i b a), γ.ev_trans i j i a b a,
    ev_refl, inv_mul_cancel]

end OneCocycle

variable {G U}

/-- The assertion that two cochains in `OneCochain G U` are cohomologous via
an explicit zero-cochain. -/
/-
**CategoryTheory.PresheafOfGroups.OneCohomologyRelation** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.PresheafOfGroups`。
形式化陈述：OneCohomologyRelation (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U) : Pro
p
参数：γ₁ γ₂ : OneCochain G U；α : ZeroCochain G U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The assertion that two cochains in `OneCochain G U` are cohomologous via
an explicit zero-cochain.
-/
def OneCohomologyRelation (γ₁ γ₂ : OneCochain G U) (α : ZeroCochain G U) : Prop :=
  ∀ (i j : I) ⦃T : C⦄ (a : T ⟶ U i) (b : T ⟶ U j),
    G.map a.op (α i) * γ₁.ev i j a b = γ₂.ev i j a b * G.map b.op (α j)

namespace OneCohomologyRelation

/-
**CategoryTheory.PresheafOfGroups.OneCohomologyRelation.refl** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation`。
形式化陈述：refl (γ : OneCochain G U) : OneCohomologyRelation γ γ 1
参数：γ : OneCochain G U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma refl (γ : OneCochain G U) : OneCohomologyRelation γ γ 1 := fun _ _ _ _ _ ↦ by simp
/-
**CategoryTheory.PresheafOfGroups.OneCohomologyRelation.symm** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation`。
形式化陈述：symm {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRela
tion γ₁ γ₂ α) : OneCohomologyRelation γ₂ γ₁ α⁻¹
参数：h : OneCohomologyRelation γ₁ γ₂ α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_left_inj`：mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `CategoryTheory.PresheafOfGroups.Cochain₀.inv_apply`：inv_apply (γ : ZeroC
ochain G U) (i : I) : γ⁻¹ i = (γ i)⁻¹
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma symm {γ₁ γ₂ : OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α) :
    OneCohomologyRelation γ₂ γ₁ α⁻¹ := fun i j T a b ↦ by
  rw [← mul_left_inj (G.map b.op (α j)), mul_assoc, ← h i j a b,
    mul_assoc, Cochain₀.inv_apply, map_inv, inv_mul_cancel_left,
    Cochain₀.inv_apply, map_inv, inv_mul_cancel, mul_one]
/-
**CategoryTheory.PresheafOfGroups.OneCohomologyRelation.trans** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation`。
形式化陈述：trans {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U} (h₁₂ : OneCohomo
logyRelation γ₁ γ₂ α) (h₂₃ : OneCohomologyRelation γ₂ γ₃ β) : OneCohomologyRelat
ion γ₁ γ₃ (β * α)
参数：h₁₂ : OneCohomologyRelation γ₁ γ₂ α；h₂₃ : OneCohomologyRelation γ₂ γ₃ β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma trans {γ₁ γ₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U}
    (h₁₂ : OneCohomologyRelation γ₁ γ₂ α) (h₂₃ : OneCohomologyRelation γ₂ γ₃ β) :
    OneCohomologyRelation γ₁ γ₃ (β * α) := fun i j T a b ↦ by
  dsimp
  rw [map_mul, map_mul, mul_assoc, h₁₂ i j a b, ← mul_assoc,
    h₂₃ i j a b, mul_assoc]

end OneCohomologyRelation

namespace OneCocycle

/-- The cohomology (equivalence) relation on 1-cocycles. -/
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous** 是 Mathlib 中的一个定义，位
于命名空间 `CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：IsCohomologous (γ₁ γ₂ : OneCocycle G U) : Prop
参数：γ₁ γ₂ : OneCocycle G U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cohomology (equivalence) relation on 1-cocycles.
-/
def IsCohomologous (γ₁ γ₂ : OneCocycle G U) : Prop :=
  ∃ (α : ZeroCochain G U), OneCohomologyRelation γ₁.toOneCochain γ₂.toOneCochain α

variable (G U)
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.equivalence_isCohomologous** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：equivalence_isCohomologous : _root_.Equivalence (IsCohomologous (G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation.refl`：refl (γ : On
eCochain G U) : OneCohomologyRelation γ γ 1
· 使用引理 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation.symm`：symm {γ₁ γ₂ 
: OneCochain G U} {α : ZeroCochain G U} (h : OneCohomologyRelation γ₁ γ₂ α) : On
eCohomologyRelation γ₂ γ₁ α⁻¹
· 使用引理 `CategoryTheory.PresheafOfGroups.OneCohomologyRelation.trans`：trans {γ₁ γ
₂ γ₃ : OneCochain G U} {α β : ZeroCochain G U} (h₁₂ : OneCohomologyRelation γ₁ γ
₂ α) (h₂₃ : OneCohomologyRelation γ₂ γ₃ β) : OneC…
-/
lemma equivalence_isCohomologous :
    _root_.Equivalence (IsCohomologous (G := G) (U := U)) where
  refl γ := ⟨_, OneCohomologyRelation.refl γ.toOneCochain⟩
  symm := by
    rintro γ₁ γ₂ ⟨α, h⟩
    exact ⟨_, h.symm⟩
  trans := by
    rintro γ₁ γ₂ γ₂ ⟨α, h⟩ ⟨β, h'⟩
    exact ⟨_, h.trans h'⟩

end OneCocycle

variable (G U) in
/-- The cohomology in degree 1 of a presheaf of groups
`G : Cᵒᵖ ⥤ GrpCat` on a family of objects `U : I → C`. -/
/-
**CategoryTheory.PresheafOfGroups.H1** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
resheafOfGroups`。
形式化陈述：H1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cohomology in degree 1 of a presheaf of groups
`G : Cᵒᵖ ⥤ GrpCat` on a family of objects `U : I → C`.
-/
def H1 := Quot (OneCocycle.IsCohomologous (G := G) (U := U))

/-- The cohomology class of a 1-cocycle. -/
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.class** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     {G : Cate
goryTheory.Functor Cᵒᵖ GrpCat} →       {I : Type w'} →         {U : I → C} → Cat
egoryTheory.PresheafOfGroups.OneCocycle G U → CategoryTheory.PresheafOfGroups.H1
 G U
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cohomology class of a 1-cocycle.
-/
def OneCocycle.class (γ : OneCocycle G U) : H1 G U := Quot.mk _ γ
/-
**CategoryTheory.PresheafOfGroups.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pre
sheafOfGroups`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (H1 G U) where
  one := OneCocycle.class 1
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.class_eq_iff** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.PresheafOfGroups.OneCocycle`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {G : CategoryTheo
ry.Functor Cᵒᵖ GrpCat} {I : Type w'}   {U : I → C} (γ₁ γ₂ : CategoryTheory.Presh
eafOfGroups.OneCocycle G U), γ₁.class = γ₂.class ↔ γ₁.IsCohomologous γ₂
参数：γ₁ γ₂ : CategoryTheory.PresheafOfGroups.OneCocycle G U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equivalence.quot_mk_eq_iff`：Equivalence.quot_mk_eq_iff {α : Type*} {r : 
α -> α -> Prop} (h : Equivalence r) (x y : α) : Quot.mk r x = Quot.mk r y ↔ r x 
y
· 使用引理 `CategoryTheory.PresheafOfGroups.OneCocycle.equivalence_isCohomologous`：e
quivalence_isCohomologous : _root_.Equivalence (IsCohomologous (G
-/
lemma OneCocycle.class_eq_iff (γ₁ γ₂ : OneCocycle G U) :
    γ₁.class = γ₂.class ↔ γ₁.IsCohomologous γ₂ :=
  (equivalence_isCohomologous _ _).quot_mk_eq_iff _ _
/-
**CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous.class_eq** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.PresheafOfGroups.OneCocycle.IsCohomologous`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {G : CategoryTheo
ry.Functor Cᵒᵖ GrpCat} {I : Type w'}   {U : I → C} {γ₁ γ₂ : CategoryTheory.Presh
eafOfGroups.OneCocycle G U}, γ₁.IsCohomologous γ₂ → γ₁.class = γ₂.class
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma OneCocycle.IsCohomologous.class_eq {γ₁ γ₂ : OneCocycle G U} (h : γ₁.IsCohomologous γ₂) :
    γ₁.class = γ₂.class :=
  Quot.sound h

end PresheafOfGroups

end CategoryTheory

