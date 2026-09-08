/-
Copyright (c) 2025 Sahan Wijetunga. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sahan Wijetunga
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Isometric linear maps

In this file, we define isometries of bilinear spaces as linear maps that respect the
associated bilinear forms.
This file should be kept in sync with the corresponding file for quadratic maps, namely
`Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean`

## Main definitions

* ` LinearMap.BilinForm.Isometry`: `LinearMap`s which respect a given pair of bilinear forms

## Notation

`B₁ →bᵢ B₂` is notation for `B₁.Isometry B₂`.
-/
@[expose] public section

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace LinearMap

namespace BilinForm

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]

/-- An isometry between two bilinear spaces `M₁, B₁` and `M₂, B₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the bilinear forms. -/
/-
**LinearMap.BilinForm.Isometry** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：{R : Type u_1} →   {M₁ : Type u_3} →     {M₂ : Type u_4} →       [inst : C
ommSemiring R] →         [inst_1 : AddCommMonoid M₁] →           [inst_2 : AddCo
mmMonoid M₂] →             [inst_3 : _root_.Module R M₁] →               [inst_4
 : _root_.Module R M₂] → LinearMap.BilinForm R M₁ → LinearMap.BilinForm R M₂ → T
ype (max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometry between two bilinear spaces `M₁, B₁` and `M₂, B₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the bilinear forms.
-/
structure Isometry (B₁ : LinearMap.BilinForm R M₁) (B₂ : LinearMap.BilinForm R M₂)
    extends M₁ →ₗ[R] M₂ where
  /-- The bilinear forms agree across the map. -/
  map_app' (m m' : M₁) : B₂ (toFun m) (toFun m') = B₁ m m'

namespace Isometry

@[inherit_doc]
notation:25 B₁ " →bᵢ " B₂:0 => Isometry B₁ B₂

variable {B₁ : LinearMap.BilinForm R M₁} {B₂ : LinearMap.BilinForm R M₂}
variable {B₃ : LinearMap.BilinForm R M₃} {B₄ : LinearMap.BilinForm R M₄}

/-
**LinearMap.BilinForm.Isometry.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap.
BilinForm.Isometry`。
形式化陈述：instFunLike : FunLike (B₁ ->bᵢ B₂) M₁ M₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (B₁ →bᵢ B₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h
/-
**LinearMap.BilinForm.Isometry.instLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `Lin
earMap.BilinForm.Isometry`。
形式化陈述：instLinearMapClass : LinearMapClass (B₁ ->bᵢ B₂) R M₁ M₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
instance instLinearMapClass : LinearMapClass (B₁ →bᵢ B₂) R M₁ M₂ where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul
/-
**LinearMap.BilinForm.Isometry.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.BilinForm.Isometry`。
形式化陈述：toLinearMap_injective : Function.Injective (Isometry.toLinearMap : (B₁ ->b
ᵢ B₂) -> M₁ ->ₗ[R] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toLinearMap_injective :
    Function.Injective (Isometry.toLinearMap : (B₁ →bᵢ B₂) → M₁ →ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
/-
**LinearMap.BilinForm.Isometry.ext** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m.Isometry`。
形式化陈述：ext ⦃f g : B₁ ->bᵢ B₂⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : B₁ →bᵢ B₂⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. -/
/-
**LinearMap.BilinForm.Isometry.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.
BilinForm.Isometry.Simps`。
形式化陈述：{R : Type u_1} →   {M₁ : Type u_3} →     {M₂ : Type u_4} →       [inst : C
ommSemiring R] →         [inst_1 : AddCommMonoid M₁] →           [inst_2 : AddCo
mmMonoid M₂] →             [inst_3 : _root_.Module R M₁] →               [inst_4
 : _root_.Module R M₂] →                 {B₁ : LinearMap.BilinForm R M₁} → {B₂ :
 LinearMap.BilinForm R M₂} → (B₁ →bᵢ B₂) → M₁ → M₂
参数：B₁ →bᵢ B₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
protected def Simps.apply (f : B₁ →bᵢ B₂) : M₁ → M₂ := f

initialize_simps_projections Isometry (toFun → apply)

@[simp]
/-
**LinearMap.BilinForm.Isometry.map_app** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm.Isometry`。
形式化陈述：map_app (f : B₁ ->bᵢ B₂) (m m' : M₁) : B₂ (f m) (f m') = B₁ m m'
参数：f : B₁ ->bᵢ B₂；m m' : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Isometry.map_app'`：∀ {R : Type u_1} {M₁ : Type u_3} 
{M₂ : Type u_4} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]   [inst_2 : 
AddCommMonoid M₂] [inst_3 :…
-/
theorem map_app (f : B₁ →bᵢ B₂) (m m' : M₁) : B₂ (f m) (f m') = B₁ m m' :=
  f.map_app' m  m'

@[simp]
/-
**LinearMap.BilinForm.Isometry.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm.Isometry`。
形式化陈述：coe_toLinearMap (f : B₁ ->bᵢ B₂) : ⇑f.toLinearMap = f
参数：f : B₁ ->bᵢ B₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap (f : B₁ →bᵢ B₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a bilinear form to itself. -/
@[simps!]
/-
**LinearMap.BilinForm.Isometry.id** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm
.Isometry`。
形式化陈述：id (B : LinearMap.BilinForm R M) : B ->bᵢ B where __
参数：B : LinearMap.BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isometry from a bilinear form to itself.
-/
def id (B : LinearMap.BilinForm R M) : B →bᵢ B where
  __ := LinearMap.id
  map_app' _ _ := rfl

/-- The identity isometry between equal bilinear forms. -/
@[simps!]
/-
**LinearMap.BilinForm.Isometry.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinFo
rm.Isometry`。
形式化陈述：ofEq {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂) : B₁ ->bᵢ B₂ where _
_
参数：h : B₁ = B₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isometry between equal bilinear forms.
-/
def ofEq {B₁ B₂ : LinearMap.BilinForm R M₁} (h : B₁ = B₂) : B₁ →bᵢ B₂ where
  __ := LinearMap.id
  map_app' _ _ := h ▸ rfl

@[simp]
/-
**LinearMap.BilinForm.Isometry.ofEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm.Isometry`。
形式化陈述：ofEq_rfl {B : LinearMap.BilinForm R M₁} : ofEq (rfl : B = B) = .id B
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_rfl {B : LinearMap.BilinForm R M₁} : ofEq (rfl : B = B) = .id B := rfl

/-- The composition of two isometries between bilinear forms. -/
@[simps]
/-
**LinearMap.BilinForm.Isometry.comp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinFo
rm.Isometry`。
形式化陈述：comp (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) : B₁ ->bᵢ B₃ where toFun x
参数：g : B₂ ->bᵢ B₃；f : B₁ ->bᵢ B₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two isometries between bilinear forms.
-/
def comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) : B₁ →bᵢ B₃ where
  toFun x := g (f x)
  map_app' x y := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ →ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ →ₗ[R] M₂)

@[simp]
/-
**LinearMap.BilinForm.Isometry.toLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap.BilinForm.Isometry`。
形式化陈述：toLinearMap_comp (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) : (g.comp f).toLinearMa
p = g.toLinearMap.comp f.toLinearMap
参数：g : B₂ ->bᵢ B₃；f : B₁ ->bᵢ B₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_comp (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.Isometry.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm.Isometry`。
形式化陈述：id_comp (f : B₁ ->bᵢ B₂) : (id B₂).comp f = f
参数：f : B₁ ->bᵢ B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Isometry.ext`：ext ⦃f g : B₁ ->bᵢ B₂⦄ (h : forall x, 
f x = g x) : f = g
-/
theorem id_comp (f : B₁ →bᵢ B₂) : (id B₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**LinearMap.BilinForm.Isometry.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm.Isometry`。
形式化陈述：comp_id (f : B₁ ->bᵢ B₂) : f.comp (id B₁) = f
参数：f : B₁ ->bᵢ B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Isometry.ext`：ext ⦃f g : B₁ ->bᵢ B₂⦄ (h : forall x, 
f x = g x) : f = g
-/
theorem comp_id (f : B₁ →bᵢ B₂) : f.comp (id B₁) = f :=
  ext fun _ => rfl
/-
**LinearMap.BilinForm.Isometry.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinForm.Isometry`。
形式化陈述：comp_assoc (h : B₃ ->bᵢ B₄) (g : B₂ ->bᵢ B₃) (f : B₁ ->bᵢ B₂) : (h.comp g)
.comp f = h.comp (g.comp f)
参数：h : B₃ ->bᵢ B₄；g : B₂ ->bᵢ B₃；f : B₁ ->bᵢ B₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.Isometry.ext`：ext ⦃f g : B₁ ->bᵢ B₂⦄ (h : forall x, 
f x = g x) : f = g
-/
theorem comp_assoc (h : B₃ →bᵢ B₄) (g : B₂ →bᵢ B₃) (f : B₁ →bᵢ B₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/-- There is a zero map from any module with the zero form. -/
/-
**LinearMap.BilinForm.Isometry.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap.BilinForm.I
sometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a zero map from any module with the zero form.
-/
instance : Zero ((0 : LinearMap.BilinForm R M₁) →bᵢ B₂) where
  zero := { (0 : M₁ →ₗ[R] M₂) with map_app' := fun _ _ => map_zero _ }

/-- There is a zero map from the trivial module. -/
/-
**LinearMap.BilinForm.Isometry.hasZeroOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `
LinearMap.BilinForm.Isometry`。
形式化陈述：hasZeroOfSubsingleton [Subsingleton M₁] : Zero (B₁ ->bᵢ B₂) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a zero map from the trivial module.
-/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (B₁ →bᵢ B₂) where
  zero :=
  { (0 : M₁ →ₗ[R] M₂) with
    map_app' := fun x y => by
      rw [Subsingleton.elim x 0, Subsingleton.elim y 0]
      simp }

/-- Maps into the zero module are trivial -/
/-
**LinearMap.BilinForm.Isometry.** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap.BilinForm.I
sometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps into the zero module are trivial
-/
instance [Subsingleton M₂] : Subsingleton (B₁ →bᵢ B₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end BilinForm

end LinearMap

