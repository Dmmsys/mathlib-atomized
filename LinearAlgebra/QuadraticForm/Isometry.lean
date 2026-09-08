/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Isometric linear maps

## Main definitions

* `QuadraticMap.Isometry`: `LinearMap`s which map between two different quadratic forms

## Notation

`Q₁ →qᵢ Q₂` is notation for `Q₁.Isometry Q₂`.
-/

@[expose] public section

variable {R M M₁ M₂ M₃ M₄ N : Type*}

namespace QuadraticMap

variable [CommSemiring R]
variable [AddCommMonoid M]
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃] [AddCommMonoid M₄]
variable [AddCommMonoid N]
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R N]

/-- An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the quadratic forms. -/
/-
**QuadraticMap.Isometry** 是 Mathlib 中的一个归纳类型，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_1} →   {M₁ : Type u_3} →     {M₂ : Type u_4} →       {N : Type
 u_7} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M₁] 
→             [inst_2 : AddCommMonoid M₂] →               [inst_3 : AddCommMonoi
d N] →                 [inst_4 : _root_.Module R M₁] →                   [inst_5
 : _root_.Module R M₂] →                     [inst_6 : _root_.Module R N] → Quad
raticMap R M₁ N → QuadraticMap R M₂ N → Type (max u_3 u_4)
参数：max u_3 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An isometry between two quadratic spaces `M₁, Q₁` and `M₂, Q₂` over a ring `R`,
is a linear map between `M₁` and `M₂` that commutes with the quadratic forms.
-/
structure Isometry (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) extends M₁ →ₗ[R] M₂ where
  /-- The quadratic form agrees across the map. -/
  map_app' : ∀ m, Q₂ (toFun m) = Q₁ m

namespace Isometry

@[inherit_doc]
notation:25 Q₁ " →qᵢ " Q₂:0 => Isometry Q₁ Q₂

variable {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}
variable {Q₃ : QuadraticMap R M₃ N} {Q₄ : QuadraticMap R M₄ N}

/-
**QuadraticMap.Isometry.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.Isom
etry`。
形式化陈述：instFunLike : FunLike (Q₁ ->qᵢ Q₂) M₁ M₂ where coe f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (Q₁ →qᵢ Q₂) M₁ M₂ where
  coe f := f.toLinearMap
  coe_injective f g h := by cases f; cases g; congr; exact DFunLike.coe_injective h
/-
**QuadraticMap.Isometry.instLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticM
ap.Isometry`。
形式化陈述：instLinearMapClass : LinearMapClass (Q₁ ->qᵢ Q₂) R M₁ M₂ where map_add f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
-/
instance instLinearMapClass : LinearMapClass (Q₁ →qᵢ Q₂) R M₁ M₂ where
  map_add f := f.toLinearMap.map_add
  map_smulₛₗ f := f.toLinearMap.map_smul
/-
**QuadraticMap.Isometry.toLinearMap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Quadrat
icMap.Isometry`。
形式化陈述：toLinearMap_injective : Function.Injective (Isometry.toLinearMap : (Q₁ ->q
ᵢ Q₂) -> M₁ ->ₗ[R] M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem toLinearMap_injective :
    Function.Injective (Isometry.toLinearMap : (Q₁ →qᵢ Q₂) → M₁ →ₗ[R] M₂) := fun _f _g h =>
  DFunLike.coe_injective (congr_arg DFunLike.coe h :)

@[ext]
/-
**QuadraticMap.Isometry.ext** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isometry`。
形式化陈述：ext ⦃f g : Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : Q₁ →qᵢ Q₂⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- See Note [custom simps projection]. -/
/-
**QuadraticMap.Isometry.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isom
etry.Simps`。
形式化陈述：{R : Type u_1} →   {M₁ : Type u_3} →     {M₂ : Type u_4} →       {N : Type
 u_7} →         [inst : CommSemiring R] →           [inst_1 : AddCommMonoid M₁] 
→             [inst_2 : AddCommMonoid M₂] →               [inst_3 : AddCommMonoi
d N] →                 [inst_4 : _root_.Module R M₁] →                   [inst_5
 : _root_.Module R M₂] →                     [inst_6 : _root_.Module R N] →     
                  {Q₁ : QuadraticMap R M₁ N} → {Q₂ : QuadraticMap R M₂ N} → (Q₁ 
→qᵢ Q₂) → M₁ → M₂
参数：Q₁ →qᵢ Q₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
protected def Simps.apply (f : Q₁ →qᵢ Q₂) : M₁ → M₂ := f

initialize_simps_projections Isometry (toFun → apply)

@[simp]
/-
**QuadraticMap.Isometry.map_app** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isometry
`。
形式化陈述：map_app (f : Q₁ ->qᵢ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m
参数：f : Q₁ ->qᵢ Q₂；m : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.Isometry.map_app'`：∀ {R : Type u_1} {M₁ : Type u_3} {M₂ : T
ype u_4} {N : Type u_7} [inst : CommSemiring R] [inst_1 : AddCommMonoid M₁]   [i
nst_2 : AddCommMonoi…
-/
theorem map_app (f : Q₁ →qᵢ Q₂) (m : M₁) : Q₂ (f m) = Q₁ m :=
  f.map_app' m

@[simp]
/-
**QuadraticMap.Isometry.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.
Isometry`。
形式化陈述：coe_toLinearMap (f : Q₁ ->qᵢ Q₂) : ⇑f.toLinearMap = f
参数：f : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap (f : Q₁ →qᵢ Q₂) : ⇑f.toLinearMap = f :=
  rfl

/-- The identity isometry from a quadratic form to itself. -/
@[simps!]
/-
**QuadraticMap.Isometry.id** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isometry`。
形式化陈述：id (Q : QuadraticMap R M N) : Q ->qᵢ Q where __
参数：Q : QuadraticMap R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isometry from a quadratic form to itself.
-/
def id (Q : QuadraticMap R M N) : Q →qᵢ Q where
  __ := LinearMap.id
  map_app' _ := rfl

/-- The identity isometry between equal quadratic forms. -/
@[simps!]
/-
**QuadraticMap.Isometry.ofEq** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isometry`。
形式化陈述：ofEq {Q₁ Q₂ : QuadraticMap R M₁ N} (h : Q₁ = Q₂) : Q₁ ->qᵢ Q₂ where __
参数：h : Q₁ = Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity isometry between equal quadratic forms.
-/
def ofEq {Q₁ Q₂ : QuadraticMap R M₁ N} (h : Q₁ = Q₂) : Q₁ →qᵢ Q₂ where
  __ := LinearMap.id
  map_app' _ := h ▸ rfl

@[simp]
/-
**QuadraticMap.Isometry.ofEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isometr
y`。
形式化陈述：ofEq_rfl {Q : QuadraticMap R M₁ N} : ofEq (rfl : Q = Q) = .id Q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofEq_rfl {Q : QuadraticMap R M₁ N} : ofEq (rfl : Q = Q) = .id Q := rfl

/-- The composition of two isometries between quadratic forms. -/
@[simps]
/-
**QuadraticMap.Isometry.comp** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap.Isometry`。
形式化陈述：comp (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) : Q₁ ->qᵢ Q₃ where toFun x
参数：g : Q₂ ->qᵢ Q₃；f : Q₁ ->qᵢ Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two isometries between quadratic forms.
-/
def comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) : Q₁ →qᵢ Q₃ where
  toFun x := g (f x)
  map_app' x := by rw [← f.map_app, ← g.map_app]
  __ := (g.toLinearMap : M₂ →ₗ[R] M₃) ∘ₗ (f.toLinearMap : M₁ →ₗ[R] M₂)

@[simp]
/-
**QuadraticMap.Isometry.toLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap
.Isometry`。
形式化陈述：toLinearMap_comp (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) : (g.comp f).toLinearMa
p = g.toLinearMap.comp f.toLinearMap
参数：g : Q₂ ->qᵢ Q₃；f : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_comp (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) :
    (g.comp f).toLinearMap = g.toLinearMap.comp f.toLinearMap :=
  rfl

@[simp]
/-
**QuadraticMap.Isometry.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isometry
`。
形式化陈述：id_comp (f : Q₁ ->qᵢ Q₂) : (id Q₂).comp f = f
参数：f : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.Isometry.ext`：ext ⦃f g : Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g
 x) : f = g
-/
theorem id_comp (f : Q₁ →qᵢ Q₂) : (id Q₂).comp f = f :=
  ext fun _ => rfl

@[simp]
/-
**QuadraticMap.Isometry.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isometry
`。
形式化陈述：comp_id (f : Q₁ ->qᵢ Q₂) : f.comp (id Q₁) = f
参数：f : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.Isometry.ext`：ext ⦃f g : Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g
 x) : f = g
-/
theorem comp_id (f : Q₁ →qᵢ Q₂) : f.comp (id Q₁) = f :=
  ext fun _ => rfl
/-
**QuadraticMap.Isometry.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.Isome
try`。
形式化陈述：comp_assoc (h : Q₃ ->qᵢ Q₄) (g : Q₂ ->qᵢ Q₃) (f : Q₁ ->qᵢ Q₂) : (h.comp g)
.comp f = h.comp (g.comp f)
参数：h : Q₃ ->qᵢ Q₄；g : Q₂ ->qᵢ Q₃；f : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.Isometry.ext`：ext ⦃f g : Q₁ ->qᵢ Q₂⦄ (h : forall x, f x = g
 x) : f = g
-/
theorem comp_assoc (h : Q₃ →qᵢ Q₄) (g : Q₂ →qᵢ Q₃) (f : Q₁ →qᵢ Q₂) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  ext fun _ => rfl

/-- There is a zero map from any module with the zero form. -/
/-
**QuadraticMap.Isometry.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a zero map from any module with the zero form.
-/
instance : Zero ((0 : QuadraticMap R M₁ N) →qᵢ Q₂) where
  zero := { (0 : M₁ →ₗ[R] M₂) with map_app' := fun _ => map_zero _ }

/-- There is a zero map from the trivial module. -/
/-
**QuadraticMap.Isometry.hasZeroOfSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Quadrat
icMap.Isometry`。
形式化陈述：hasZeroOfSubsingleton [Subsingleton M₁] : Zero (Q₁ ->qᵢ Q₂) where zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a zero map from the trivial module.
-/
instance hasZeroOfSubsingleton [Subsingleton M₁] : Zero (Q₁ →qᵢ Q₂) where
  zero :=
  { (0 : M₁ →ₗ[R] M₂) with
    map_app' := fun m => Subsingleton.elim 0 m ▸ (map_zero _).trans (map_zero _).symm }

/-- Maps into the zero module are trivial -/
/-
**QuadraticMap.Isometry.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap.Isometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Maps into the zero module are trivial
-/
instance [Subsingleton M₂] : Subsingleton (Q₁ →qᵢ Q₂) :=
  ⟨fun _ _ => ext fun _ => Subsingleton.elim _ _⟩

end Isometry

end QuadraticMap

