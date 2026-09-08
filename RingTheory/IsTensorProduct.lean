/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The characteristic predicate of tensor product

## Main definitions

- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `IsBaseChange`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being an
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `Algebra.IsPushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
  asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/

@[expose] public section

universe u v₁ v₂ v₃ v₄

open TensorProduct

section IsTensorProduct

variable {R : Type*} [CommSemiring R]
variable {M₁ M₂ M M' : Type*}
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']
variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)
variable {N₁ N₂ N : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]
variable [Module R N₁] [Module R N₂] [Module R N]
variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `IsTensorProduct f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
/-
**IsTensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTensorProduct : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `IsTensorProduct f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)

variable (R M N) {f}
/-
**TensorProduct.isTensorProduct** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
-/
theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) := by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id

namespace IsTensorProduct

variable {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps! apply]
/-
**IsTensorProduct.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
形式化陈述：equiv (h : IsTensorProduct f) : M₁ otimes[R] M₂ ≃ₗ[R] M
参数：h : IsTensorProduct f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ 
⊗[R] M₂`.
-/
noncomputable def equiv (h : IsTensorProduct f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h

@[simp]
/-
**IsTensorProduct.equiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：equiv_toLinearMap (h : IsTensorProduct f) : h.equiv.toLinearMap = TensorPr
oduct.lift f
参数：h : IsTensorProduct f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equiv_toLinearMap (h : IsTensorProduct f) :
    h.equiv.toLinearMap = TensorProduct.lift f :=
  rfl

@[simp]
/-
**IsTensorProduct.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) : h.equiv.sym
m (f x₁ x₂) = x₁ otimesₜ x₂
参数：h : IsTensorProduct f；x₁ : M₁；x₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTensorProduct.equiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {M
₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst
_2 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
/-
**IsTensorProduct.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
形式化陈述：lift (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') : M ->ₗ[R] M'
参数：h : IsTensorProduct f；f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ
[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`.
-/
noncomputable def lift (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') :
    M →ₗ[R] M' :=
  (TensorProduct.lift f').comp h.equiv.symm.toLinearMap
/-
**IsTensorProduct.lift_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：lift_eq (h : IsTensorProduct f) (f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M') (x₁ : M₁) (x
₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂
参数：h : IsTensorProduct f；f' : M₁ ->ₗ[R] M₂ ->ₗ[R] M'；x₁ : M₁；x₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_eq (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') (x₁ : M₁)
    (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ := by
  simp [lift]

/-- The tensor product of a pair of linear maps between modules. -/
/-
**IsTensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
形式化陈述：map (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N₁) 
(i₂ : M₂ ->ₗ[R] N₂) : M ->ₗ[R] N
参数：hf : IsTensorProduct f；hg : IsTensorProduct g；i₁ : M₁ ->ₗ[R] N₁；i₂ : M₂ ->ₗ[R
] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of a pair of linear maps between modules.
-/
noncomputable def map (hf : IsTensorProduct f) (hg : IsTensorProduct g)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
  hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)

@[simp]
/-
**IsTensorProduct.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ ->ₗ[R] N
₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x
₁) (i₂ x₂)
参数：hf : IsTensorProduct f；hg : IsTensorProduct g；i₁ : M₁ ->ₗ[R] N₁；i₂ : M₂ ->ₗ[R
] N₂；x₁ : M₁；x₂ : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁)
    (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) := by
  simp [map]

@[elab_as_elim]
/-
**IsTensorProduct.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：inductionOn (h : IsTensorProduct f) {motive : M -> Prop} (m : M) (zero : m
otive 0) (tmul : forall x y, motive (f x y)) (add : forall x y, motive x -> moti
ve y -> motive (x + y)) : motive m
参数：h : IsTensorProduct f；m : M；zero : motive 0；tmul : forall x y, motive (f x y)
；add : forall x y, motive x -> motive y -> motive (x + y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `TensorProduct.lift.tmul`：∀ {R : Type u_1} {R₂ : Type u_2} [inst : CommSe
miring R] [inst_1 : CommSemiring R₂] {σ₁₂ : R →+* R₂} {M : Type u_7}   {N : Type
 u_8} {P₂ : T…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem inductionOn (h : IsTensorProduct f) {motive : M → Prop} (m : M)
    (zero : motive 0) (tmul : ∀ x y, motive (f x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive m := by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change motive (TensorProduct.lift f y)
  induction y with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply tmul
  | add _ _ _ _ =>
    rw [map_add]
    apply add <;> assumption
/-
**IsTensorProduct.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
形式化陈述：of_equiv (e : M₁ otimes[R] M₂ ≃ₗ[R] M) (he : forall x y, e (x otimesₜ y) =
 f x y) : IsTensorProduct f
参数：e : M₁ otimes[R] M₂ ≃ₗ[R] M；he : forall x y, e (x otimesₜ y) = f x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
lemma of_equiv (e : M₁ ⊗[R] M₂ ≃ₗ[R] M) (he : ∀ x y, e (x ⊗ₜ y) = f x y) :
    IsTensorProduct f := by
  have : TensorProduct.lift f = e := by
    ext x y
    simp [he]
  simpa [IsTensorProduct, this] using e.bijective

section map

variable {P₁ P₂ P : Type*} [AddCommMonoid P₁] [AddCommMonoid P₂]
  [AddCommMonoid P] [Module R P₁] [Module R P₂] [Module R P] {p : P₁ →ₗ[R] P₂ →ₗ[R] P}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (hp : IsTensorProduct p)
  (i₁ : N₁ →ₗ[R] P₁) (j₁ : M₁ →ₗ[R] N₁) (i₂ : N₂ →ₗ[R] P₂) (j₂ : M₂ →ₗ[R] N₂)

/-
**IsTensorProduct.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg 
j₁ j₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = hg.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂ :=
  LinearMap.ext <| fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])
/-
**IsTensorProduct.map_map** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：map_map (x : M) : hg.map hp i₁ i₂ ((hf.map hg j₁ j₂) x) = hf.map hp (i₁ ∘ₗ
 j₁) (i₂ ∘ₗ j₂) x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTensorProduct.map_comp`：map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = h
g.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂
-/
theorem map_map (x : M) :
    hg.map hp i₁ i₂ ((hf.map hg j₁ j₂) x) = hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) x :=
  DFunLike.congr_fun (hf.map_comp hg hp i₁ j₁ i₂ j₂).symm x

@[simp]
/-
**IsTensorProduct.map_id** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：map_id : hf.map hf (LinearMap.id : M₁ ->ₗ[R] M₁) (LinearMap.id : M₂ ->ₗ[R]
 M₂) = LinearMap.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem map_id :
    hf.map hf (LinearMap.id : M₁ →ₗ[R] M₁) (LinearMap.id : M₂ →ₗ[R] M₂) = LinearMap.id :=
  LinearMap.ext <| fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ h₁ h₂ ↦ by simp [h₁, h₂])

@[simp]
/-
**IsTensorProduct.map_one** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M₁ : Type u_2} {M₂ : Type u_3} {
M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid M] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R M] {f : M₁ →ₗ[R] M₂ →ₗ[R] M} (hf : IsTensorProduct f)
, hf.map hf 1 1 = 1
参数：hf : IsTensorProduct f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTensorProduct.map_id`：map_id : hf.map hf (LinearMap.id : M₁ ->ₗ[R] M₁)
 (LinearMap.id : M₂ ->ₗ[R] M₂) = LinearMap.id
-/
protected theorem map_one : hf.map hf (1 : M₁ →ₗ[R] M₁) (1 : M₂ →ₗ[R] M₂) = 1 :=
  hf.map_id
/-
**IsTensorProduct.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M₁ : Type u_2} {M₂ : Type u_3} {
M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid M] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R M] {f : M₁ →ₗ[R] M₂ →ₗ[R] M} (hf : IsTensorProduct f)
 (i₁ i₂ : M₁ →ₗ[R] M₁)   (j₁ j₂ : M₂ →ₗ[R] M₂), hf.map hf (i₁ * i₂) (j₁ * j₂) = 
hf.map hf i₁ j₁ * hf.map hf i₂ j₂
参数：hf : IsTensorProduct f；i₁ i₂ : M₁ →ₗ[R] M₁；j₁ j₂ : M₂ →ₗ[R] M₂；i₁ * i₂；j₁ * j
₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTensorProduct.map_comp`：map_comp : hf.map hp (i₁ ∘ₗ j₁) (i₂ ∘ₗ j₂) = h
g.map hp i₁ i₂ ∘ₗ hf.map hg j₁ j₂
-/
protected theorem map_mul (i₁ i₂ : M₁ →ₗ[R] M₁) (j₁ j₂ : M₂ →ₗ[R] M₂) :
    hf.map hf (i₁ * i₂) (j₁ * j₂) = hf.map hf i₁ j₁ * hf.map hf i₂ j₂ :=
  hf.map_comp hf hf i₁ i₂ j₁ j₂
/-
**IsTensorProduct.map_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsTensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M₁ : Type u_2} {M₂ : Type u_3} {
M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst_2 : AddCommMonoid M₂] [inst_3 
: AddCommMonoid M] [inst_4 : _root_.Module R M₁] [inst_5 : _root_.Module R M₂]  
 [inst_6 : _root_.Module R M] {f : M₁ →ₗ[R] M₂ →ₗ[R] M} (hf : IsTensorProduct f)
 (i : M₁ →ₗ[R] M₁) (j : M₂ →ₗ[R] M₂)   (n : ℕ), hf.map hf i j ^ n = hf.map hf (i
 ^ n) (j ^ n)
参数：hf : IsTensorProduct f；i : M₁ →ₗ[R] M₁；j : M₂ →ₗ[R] M₂；n : ℕ；i ^ n；j ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `IsTensorProduct.map.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R]
 {M₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [i
nst_2 : AddCommMonoi…
· 使用定理 `IsTensorProduct.map_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M₁ : 
Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst_2 :
 AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsTensorProduct.map_mul`：∀ {R : Type u_1} [inst : CommSemiring R] {M₁ : 
Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst_2 :
 AddCommMonoi…
-/
protected theorem map_pow (i : M₁ →ₗ[R] M₁) (j : M₂ →ₗ[R] M₂) (n : ℕ) :
    hf.map hf i j ^ n = hf.map hf (i ^ n) (j ^ n) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ, ih, hf.map_mul]

end map


section

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
  {M₁ M₂ M₃ M₁₂ M₂₃ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [AddCommMonoid M₁₂] [AddCommMonoid M₂₃]
  [Module R M₁]
  [Module R M₂] [Module S M₂] [IsScalarTower R S M₂]
  [Module R M₃] [Module S M₃] [IsScalarTower R S M₃]
  [Module R M₁₂] [Module S M₁₂] [IsScalarTower R S M₁₂]
  [Module R M₂₃] [Module S M₂₃] [IsScalarTower R S M₂₃]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation): Use the more linear `IsTensorProduct.assoc`. -/
/-
**IsTensorProduct.assocAux** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Use the more linear `IsTensorProduct.assoc`.
-/
private noncomputable def assocAux
    (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[R] M₁ ⊗[R] M₂₃ :=
  letI : Module S (M₁ ⊗[R] M₂) :=
    AddEquiv.module S hf.equiv.toAddEquiv
  haveI heq (s : S) (y : M₁) (x : M₂) : s • y ⊗ₜ[R] x = y ⊗ₜ[R] (s • x) := by
    change hf.equiv.symm (s • _) = _
    dsimp
    rw [← map_smul]
    apply hf.equiv_symm_apply
  haveI : IsScalarTower R S (M₁ ⊗[R] M₂) := hf.equiv.isScalarTower S
  letI e₀ : M₂ ⊗[R] M₁ ≃ₗ[S] M₁ ⊗[R] M₂ :=
    { __ := TensorProduct.comm R M₂ M₁
      map_smul' s x := by induction x <;> simp_all [TensorProduct.smul_tmul'] }
  LinearEquiv.symm <|
    TensorProduct.congr (.refl _ _) (hg.equiv.symm.restrictScalars R) ≪≫ₗ
    TensorProduct.comm _ _ _ ≪≫ₗ
    (AlgebraTensorModule.congr (TensorProduct.comm _ _ _) (.refl _ _)).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.assoc R S S M₃ M₂ M₁).restrictScalars R ≪≫ₗ
    (TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (TensorProduct.congr e₀ (.refl _ _)).restrictScalars R ≪≫ₗ
    (TensorProduct.congr (hf.equiv.linearEquiv S) (.refl _ _)).restrictScalars R

variable (f : M₁ →ₗ[R] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
/-
**IsTensorProduct.assocAux_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma assocAux_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (IsTensorProduct.assocAux f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ := by
  simp [IsTensorProduct.assocAux]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**IsTensorProduct.assocAux_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma assocAux_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    IsTensorProduct.assocAux f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ := by
  have : hf.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := hf.equiv_symm_apply _ _
  simp [IsTensorProduct.assocAux, this]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M₃)`.
We state this for a general `M₁₂ = M₁ ⊗[R] M₂` and `M₂₃ = M₂ ⊗[R] M₃`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorModule.assoc`.
-/
@[no_expose]
/-
**IsTensorProduct.assoc** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
形式化陈述：assoc {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁] [IsScalarTo
wer R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂] (f : 
M₁ ->ₗ[T] M₂ ->ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R)) (g : M
₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g) : M₁₂ otimes[S] M₃ ≃ₗ[T] M₁ oti
mes[R] M₂₃ where toAddEquiv
参数：f : M₁ ->ₗ[T] M₂ ->ₗ[S] M₁₂；hf : IsTensorProduct (f.restrictScalars₁₂ R R)；g 
: M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃；hg : IsTensorProduct g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the canonical isomorphism `(M₁ ⊗[R] M₂) ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] (M₂ ⊗[S] M
₃)`.
We state this for a general `M₁₂ = M₁ ⊗[R] M₂` and `M₂₃ = M₂ ⊗[R] M₃`.
For the version where `R` and `S` are flipped, see `TensorProduct.AlgebraTensorM
odule.assoc`.
-/
noncomputable def assoc {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁]
    [IsScalarTower R T M₁] [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
    (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ where
  toAddEquiv := IsTensorProduct.assocAux (f.restrictScalars₁₂ R S) hf g hg
  map_smul' t x := by
    induction x with
    | zero => simp
    | add x y _ _ => simp_all
    | tmul x y =>
    obtain ⟨x, rfl⟩ := hf.equiv.surjective x
    induction x with
    | zero => simp
    | add x y _ _ => simp_all [add_tmul]
    | tmul x z =>
      have : t • (f x) z = f (t • x) z := by simp
      dsimp
      rw [smul_tmul', this, ← f.restrictScalars₁₂_apply_apply R S,
        ← f.restrictScalars₁₂_apply_apply R S, IsTensorProduct.assocAux_tmul,
        IsTensorProduct.assocAux_tmul, TensorProduct.smul_tmul']

variable {T : Type*} [CommSemiring T] [Algebra R T] [Module T M₁] [IsScalarTower R T M₁]
  [Module T M₁₂] [SMulCommClass S T M₁₂] [IsScalarTower R T M₁₂]
  (f : M₁ →ₗ[T] M₂ →ₗ[S] M₁₂) (hf : IsTensorProduct (f.restrictScalars₁₂ R R))
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)

@[simp]
/-
**IsTensorProduct.assoc_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
形式化陈述：assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) : assoc f hf g hg (f x₁ x₂ otimes
ₜ x₃) = x₁ otimesₜ g x₂ x₃
参数：x₁ : M₁；x₂ : M₂；x₃ : M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.IsTensorProduct.0.IsTensorProduct.assocAux_t
mul`：∀ {R : Type u_9} {S : Type u_10} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   {M₁ : Type u_11} {M₂ : Type u_12…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assoc f hf g hg (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  assocAux_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

@[simp]
/-
**IsTensorProduct.assoc_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
形式化陈述：assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) : (assoc f hf g hg).symm (x₁
 otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃
参数：x₁ : M₁；x₂ : M₂；x₃ : M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.IsTensorProduct.0.IsTensorProduct.assocAux_s
ymm_tmul`：∀ {R : Type u_9} {S : Type u_10} [inst : CommSemiring R] [inst_1 : Com
mSemiring S] [inst_2 : Algebra R S]   {M₁ : Type u_11} {M₂ : Type u_12…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
-/
lemma assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assoc f hf g hg).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  assocAux_symm_tmul (f.restrictScalars₁₂ R S) hf g hg _ _ _

/-- Variant of `IsTensorProduct.assoc` taking an `R`-bilinear map `f` and proofs that
`f` is `T` linear in the first and `S`-linear in the second argument. -/
/-
**IsTensorProduct.assocOfMapSMul** 是 Mathlib 中的一个定义，位于命名空间 `IsTensorProduct`。
形式化陈述：assocOfMapSMul (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂) (hf : IsTensorProduct f) (g :
 M₂ ->ₗ[S] M₃ ->ₗ[S] M₂₃) (hg : IsTensorProduct g) (h₁ : forall (t : T) (x : M₁)
 (y : M₂), f (t • x) y = t • f x y) (h₂ : forall (s : S) (x : M₁) (y : M₂), f x 
(s • y) = s • f x y) : M₁₂ otimes[S] M₃ ≃ₗ[T] M₁ otimes[R] M₂₃
参数：f : M₁ ->ₗ[R] M₂ ->ₗ[R] M₁₂；hf : IsTensorProduct f；g : M₂ ->ₗ[S] M₃ ->ₗ[S] M₂
₃；hg : IsTensorProduct g；h₁ : forall (t : T) (x : M₁) (y : M₂), f (t • x) y = t 
• f x y；h₂ : forall (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Variant of `IsTensorProduct.assoc` taking an `R`-bilinear map `f` and proofs tha
t
`f` is `T` linear in the first and `S`-linear in the second argument.
-/
noncomputable def assocOfMapSMul (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
    (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
    (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
    (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y) :
    M₁₂ ⊗[S] M₃ ≃ₗ[T] M₁ ⊗[R] M₂₃ :=
  IsTensorProduct.assoc (.mk₂' _ _ (f ·) (by simp) (by simp [h₁]) (by simp) (by simp [h₂])) hf g hg

variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M₁₂) (hf : IsTensorProduct f)
  (g : M₂ →ₗ[S] M₃ →ₗ[S] M₂₃) (hg : IsTensorProduct g)
  (h₁ : ∀ (t : T) (x : M₁) (y : M₂), f (t • x) y = t • f x y)
  (h₂ : ∀ (s : S) (x : M₁) (y : M₂), f x (s • y) = s • f x y)

@[simp]
/-
**IsTensorProduct.assocOfMapSMul_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct
`。
形式化陈述：assocOfMapSMul_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) : assocOfMapSMul f hf g 
hg h₁ h₂ (f x₁ x₂ otimesₜ x₃) = x₁ otimesₜ g x₂ x₃
参数：x₁ : M₁；x₂ : M₂；x₃ : M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTensorProduct.assoc_tmul`：assoc_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) : a
ssoc f hf g hg (f x₁ x₂ otimesₜ x₃) = x₁ otimesₜ g x₂ x₃
-/
lemma assocOfMapSMul_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    assocOfMapSMul f hf g hg h₁ h₂ (f x₁ x₂ ⊗ₜ x₃) = x₁ ⊗ₜ g x₂ x₃ :=
  IsTensorProduct.assoc_tmul ..

@[simp]
/-
**IsTensorProduct.assocOfMapSMul_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorPr
oduct`。
形式化陈述：assocOfMapSMul_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) : (assocOfMapSMul f
 hf g hg h₁ h₂).symm (x₁ otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃
参数：x₁ : M₁；x₂ : M₂；x₃ : M₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTensorProduct.assoc_symm_tmul`：assoc_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃
 : M₃) : (assoc f hf g hg).symm (x₁ otimesₜ g x₂ x₃) = f x₁ x₂ otimesₜ x₃
-/
lemma assocOfMapSMul_symm_tmul (x₁ : M₁) (x₂ : M₂) (x₃ : M₃) :
    (assocOfMapSMul f hf g hg h₁ h₂).symm (x₁ ⊗ₜ g x₂ x₃) = f x₁ x₂ ⊗ₜ x₃ :=
  IsTensorProduct.assoc_symm_tmul ..

end

section

/-
**IsTensorProduct.compr** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compr₂_linearEquiv (ist : IsTensorProduct f) (e : M ≃ₗ[R] M') :
    IsTensorProduct (f.compr₂ e.toLinearMap) := by
  simp only [IsTensorProduct] at ist ⊢
  rw [TensorProduct.lift_compr₂]
  exact e.bijective.comp ist
/-
**IsTensorProduct.compl** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl₂_comp_linearEquiv (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂) :
    IsTensorProduct ((f.comp e₁.toLinearMap).compl₂ e₂.toLinearMap) := by
  simp only [IsTensorProduct] at ist ⊢
  rw [← TensorProduct.lift_comp_map, ← LinearMap.rTensor_comp_lTensor]
  exact ist.comp ((e₁.rTensor M₂).bijective.comp (e₂.lTensor N₁).bijective)
/-
**IsTensorProduct.comp_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
形式化陈述：comp_linearEquiv (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) : IsTensorPr
oduct (f.comp e₁.toLinearMap)
参数：ist : IsTensorProduct f；e₁ : N₁ ≃ₗ[R] M₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsTensorProduct.compl₂_comp_linearEquiv`：compl₂_comp_linearEquiv (ist : 
IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) (e₂ : N₂ ≃ₗ[R] M₂) : IsTensorProduct ((f.c
omp e₁.toLinearMap).compl₂ e₂…
-/
lemma comp_linearEquiv (ist : IsTensorProduct f) (e₁ : N₁ ≃ₗ[R] M₁) :
    IsTensorProduct (f.comp e₁.toLinearMap) :=
  ist.compl₂_comp_linearEquiv e₁ (LinearEquiv.refl R M₂)
/-
**IsTensorProduct.compl** 是 Mathlib 中的一个引理，位于命名空间 `IsTensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma compl₂_linearEquiv (ist : IsTensorProduct f) (e₂ : N₂ ≃ₗ[R] M₂) :
    IsTensorProduct (f.compl₂ e₂.toLinearMap) :=
  ist.compl₂_comp_linearEquiv (LinearEquiv.refl R M₁) e₂

end

end IsTensorProduct

end IsTensorProduct

section IsBaseChange

variable {R : Type*} {M : Type v₁} {N : Type v₂} (S : Type v₃)
variable [AddCommMonoid M] [AddCommMonoid N] [CommSemiring R]
variable [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : M →ₗ[R] N)

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
/-
**IsBaseChange** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBaseChange : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with 
a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦
 s • f m` is the
tensor product.
-/
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M →ₗ[R] N)).flip f).restrictScalars R)

variable {S f} (h : IsBaseChange S f)
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors through `f`. -/
noncomputable nonrec def IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
  { h.lift
      (((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R) with
    map_smul' := fun r x => by
      let F := ((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R
      have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      induction x using h.inductionOn with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | tmul s m =>
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul, hF, hF, mul_smul]
      | add x₁ x₂ e₁ e₂ => rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }

nonrec theorem IsBaseChange.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x := by
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert! hF 1 x <;> rw [one_smul]

/-
**IsBaseChange.lift_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.lift_comp (g : M ->ₗ[R] Q) : ((h.lift g).restrictScalars R).c
omp f = g
参数：g : M ->ₗ[R] Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsBaseChange.lift_eq`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {S : 
Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : CommSem
iring R] […
-/
theorem IsBaseChange.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.lift_eq g)

end

section
include h

@[elab_as_elim]
nonrec theorem IsBaseChange.inductionOn (x : N) (motive : N → Prop) (zero : motive 0)
    (tmul : ∀ m : M, motive (f m)) (smul : ∀ (s : S) (n), motive n → motive (s • n))
    (add : ∀ n₁ n₂, motive n₁ → motive n₂ → motive (n₁ + n₂)) : motive x :=
  h.inductionOn x zero (fun _ _ => smul _ _ (tmul _)) add

/-
**IsBaseChange.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.algHom_ext (g₁ g₂ : N ->ₗ[S] Q) (e : forall x, g₁ (f x) = g₂ 
(f x)) : g₁ = g₂
参数：g₁ g₂ : N ->ₗ[S] Q；e : forall x, g₁ (f x) = g₂ (f x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsBaseChange.inductionOn`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {
S : Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : Com
mSemiring R] […
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
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
-/
theorem IsBaseChange.algHom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ := by
  ext x
  refine h.inductionOn x _ ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul, g₂.map_smul, e']
  · intro x y e₁ e₂
    rw [map_add, map_add, e₁, e₂]
/-
**IsBaseChange.algHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.algHom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N ->ₗ
[S] Q) (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ 
= g₂
参数：g₁ g₂ : N ->ₗ[S] Q；e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R)
.comp f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsBaseChange.algHom_ext`：IsBaseChange.algHom_ext (g₁ g₂ : N ->ₗ[S] Q) (e
 : forall x, g₁ (f x) = g₂ (f x)) : g₁ = g₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
theorem IsBaseChange.algHom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N →ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)

end

variable (R M N S)

/-
**TensorProduct.isBaseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `TensorProduct.isTensorProduct`：TensorProduct.isTensorProduct : IsTensorP
roduct (TensorProduct.mk R M N)
-/
theorem TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1) := by
  delta IsBaseChange
  convert! TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) ⊗ₜ[R] x = s ⊗ₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _

variable {R M N S}

set_option backward.isDefEq.respectTransparency false in
/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable nonrec def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N :=
  { h.equiv with
    map_smul' := fun r x => by
      change h.equiv (r • x) = r • h.equiv x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · rw [smul_zero, map_zero, smul_zero]
      · intro x y
        simp [smul_tmul', Algebra.linearMap_apply, smul_comm r x]
      · intro x y hx hy
        rw [map_add, smul_add, map_add, smul_add, hx, hy] }

@[simp]
/-
**IsBaseChange.equiv_tmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s otimesₜ m) = s • f m
参数：s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • f m :=
  rfl

@[simp]
/-
**IsBaseChange.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 otimesₜ m
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `IsBaseChange.equiv_tmul`：IsBaseChange.equiv_tmul (s : S) (m : M) : h.equ
iv (s otimesₜ m) = s • f m
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
theorem IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m := by
  rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**IsBaseChange.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N) (he : forall x, e (1 oti
mesₜ x) = f x) : IsBaseChange S f
参数：e : S otimes[R] M ≃ₗ[S] N；he : forall x, e (1 otimesₜ x) = f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `IsTensorProduct.of_equiv`：of_equiv (e : M₁ otimes[R] M₂ ≃ₗ[R] M) (he : f
orall x y, e (x otimesₜ y) = f x y) : IsTensorProduct f
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma IsBaseChange.of_equiv (e : S ⊗[R] M ≃ₗ[S] N) (he : ∀ x, e (1 ⊗ₜ x) = f x) :
    IsBaseChange S f := by
  apply IsTensorProduct.of_equiv (e.restrictScalars R)
  intro x y
  simp [show x ⊗ₜ[R] y = x • (1 ⊗ₜ[R] y) by simp [smul_tmul'], he]

variable (R S) in
/-
**IsBaseChange.linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.linearMap : IsBaseChange S (Algebra.linearMap R S)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
-/
theorem IsBaseChange.linearMap : IsBaseChange S (Algebra.linearMap R S) :=
  of_equiv (AlgebraTensorModule.rid R S S) fun x ↦ by
    simpa using (Algebra.algebraMap_eq_smul_one x).symm

variable [Module R Q] [IsScalarTower R S Q] {f' : P →ₗ[R] Q}
/-
**IsBaseChange.iff_of_equiv_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.iff_of_equiv_comm (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[S] Q) (comm : f
'.comp eM.toLinearMap = (eN.restrictScalars R).comp f) : IsBaseChange S f ↔ IsBa
seChange S f'
参数：eM : M ≃ₗ[R] P；eN : N ≃ₗ[S] Q；comm : f'.comp eM.toLinearMap = (eN.restrictSca
lars R).comp f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.compr₂.congr_simp`：∀ {A : Type u_1} {R : Type u_2} [inst : Sem
iring A] [inst_1 : CommSemiring R] {M : Type u_5} {Nₗ : Type u_8}   {Pₗ : Type u
_9} {Qₗ : Type u_…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `IsTensorProduct.compr₂_linearEquiv`：compr₂_linearEquiv (ist : IsTensorPr
oduct f) (e : M ≃ₗ[R] M') : IsTensorProduct (f.compr₂ e.toLinearMap)
· 使用引理 `IsTensorProduct.compl₂_linearEquiv`：compl₂_linearEquiv (ist : IsTensorPr
oduct f) (e₂ : N₂ ≃ₗ[R] M₂) : IsTensorProduct (f.compl₂ e₂.toLinearMap)
-/
lemma IsBaseChange.iff_of_equiv_comm (eM : M ≃ₗ[R] P) (eN : N ≃ₗ[S] Q)
    (comm : f'.comp eM.toLinearMap = (eN.restrictScalars R).comp f) :
    IsBaseChange S f ↔ IsBaseChange S f' := by
  simp only [IsBaseChange]
  have (m : M) : f' (eM m) = eN (f m) := LinearMap.congr_fun comm m
  refine ⟨fun ist ↦ ?_, fun ist ↦ ?_⟩
  · convert! (ist.compl₂_linearEquiv eM.symm).compr₂_linearEquiv (eN.restrictScalars R)
    ext s m'
    obtain ⟨m, rfl⟩ := eM.surjective m'
    simp [this]
  · convert! (ist.compl₂_linearEquiv eM).compr₂_linearEquiv (eN.symm.restrictScalars R)
    ext s m
    simp [this]
/-
**IsBaseChange.comp_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.comp_equiv (e : M ≃ₗ[R] P) (f : P ->ₗ[R] N) (isb : IsBaseChan
ge S f) : IsBaseChange S (f.comp e.toLinearMap)
参数：e : M ≃ₗ[R] P；f : P ->ₗ[R] N；isb : IsBaseChange S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `IsBaseChange.iff_of_equiv_comm`：IsBaseChange.iff_of_equiv_comm (eM : M ≃
ₗ[R] P) (eN : N ≃ₗ[S] Q) (comm : f'.comp eM.toLinearMap = (eN.restrictScalars R)
.comp f) : IsBaseCha…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearEquiv.restrictScalars_toLinearMap`：∀ (R : Type u_1) {S : Type u_4}
 {M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [ins
t_2 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsBaseChange.comp_equiv (e : M ≃ₗ[R] P) (f : P →ₗ[R] N) (isb : IsBaseChange S f) :
    IsBaseChange S (f.comp e.toLinearMap) :=
  (IsBaseChange.iff_of_equiv_comm e (LinearEquiv.refl S N) (LinearMap.ext fun y ↦ by simp)).mpr isb

section

variable (A : Type*) [CommSemiring A]
variable [Algebra R A] [Algebra S A] [IsScalarTower R S A]
variable [Module S M] [IsScalarTower R S M]
variable [Module A N] [IsScalarTower S A N] [IsScalarTower R A N]

/-- If `N` is the base change of `M` to `A`, then `N ⊗[R] P` is the base change
of `M ⊗[R] P` to `A`. This is simply the isomorphism
`A ⊗[S] (M ⊗[R] P) ≃ₗ[A] (A ⊗[S] M) ⊗[R] P`. -/
/-
**isBaseChange_tensorProduct_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isBaseChange_tensorProduct_map {f : M ->ₗ[S] N} (hf : IsBaseChange A f) : 
IsBaseChange A (AlgebraTensorModule.map f (LinearMap.id (R
参数：hf : IsBaseChange A f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
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
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…

--- 原说明 ---
If `N` is the base change of `M` to `A`, then `N ⊗[R] P` is the base change
of `M ⊗[R] P` to `A`. This is simply the isomorphism
`A ⊗[S] (M ⊗[R] P) ≃ₗ[A] (A ⊗[S] M) ⊗[R] P`.
-/
lemma isBaseChange_tensorProduct_map {f : M →ₗ[S] N} (hf : IsBaseChange A f) :
    IsBaseChange A (AlgebraTensorModule.map f (LinearMap.id (R := R) (M := P))) := by
  let e : A ⊗[S] (M ⊗[R] P) ≃ₗ[A] N ⊗[R] P := (AlgebraTensorModule.assoc R S A A M P).symm.trans
    (AlgebraTensorModule.congr hf.equiv (LinearEquiv.refl R P))
  refine IsBaseChange.of_equiv e (fun x ↦ ?_)
  induction x with
  | zero => simp
  | tmul => simp [e, IsBaseChange.equiv_tmul]
  | add _ _ h1 h2 => simp [tmul_add, h1, h2]

end

variable (f) in
/-
**IsBaseChange.of_lift_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.of_lift_unique (h : forall (Q : Type max v₁ v₂ v₃) [AddCommMo
noid Q], forall [Module R Q] [Module S Q], forall [IsScalarTower R S Q], forall 
g : M ->ₗ[R] Q, exists! g' : N ->ₗ[S] Q, (g'.restrictScalars R).comp f = g) : Is
BaseChange S f
参数：h : forall (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Mo
dule S Q], forall [IsScalarTower R S Q], forall g : M ->ₗ[R] Q, exists! g' : N -
>ₗ[S] Q, (g'.restrictScalars R).comp f = g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.cancel_left`：cancel_left (hf : Injective f) : f.comp g = f.com
p g' ↔ g = g'
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `ULift.ext`：ext (x y : ULift α) (h : x.down = y.down) : x = y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem IsBaseChange.of_lift_unique
    (h : ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
      ∀ [Module R Q] [Module S Q], ∀ [IsScalarTower R S Q],
        ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f := by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S ⊗[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S ⊗[R] M →ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M →ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S ⊗[R] M →ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S ⊗[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinearMap f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul, hg]
    rfl
/-
**IsBaseChange.iff_lift_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.iff_lift_unique : IsBaseChange S f ↔ forall (Q : Type max v₁ 
v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall [IsScalarTowe
r R S Q], forall g : M ->ₗ[R] Q, exists! g' : N ->ₗ[S] Q, (g'.restrictScalars R)
.comp f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsBaseChange.lift_comp`：IsBaseChange.lift_comp (g : M ->ₗ[R] Q) : ((h.li
ft g).restrictScalars R).comp f = g
· 使用定理 `IsBaseChange.algHom_ext'`：IsBaseChange.algHom_ext' [Module R Q] [IsScala
rTower R S Q] (g₁ g₂ : N ->ₗ[S] Q) (e : (g₁.restrictScalars R).comp f = (g₂.rest
rictScalars R)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsBaseChange.of_lift_unique`：IsBaseChange.of_lift_unique (h : forall (Q 
: Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall
 [IsScalarTower R…
-/
theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q],
            ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intro Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩

set_option backward.isDefEq.respectTransparency false in
/-
**IsBaseChange.ofEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap
参数：e : M ≃ₗ[R] N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.of_lift_unique`：IsBaseChange.of_lift_unique (h : forall (Q 
: Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall
 [IsScalarTower R…
· 使用定理 `Module.ext`：∀ {R : Type u} {M : Type v} {inst : Semiring R} {inst_1 : Ad
dCommMonoid M} {x y : _root_.Module R M},   SMul.smul = SMul.smul → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap := by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    change (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q, smul_smul, ← @smul_assoc _ _ _ (id _) (id _) (id _) I₄, smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp

variable {T O : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [AddCommMonoid O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]
variable [IsScalarTower R S O] [IsScalarTower R T O]
/-
**IsBaseChange.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.comp {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {g : N ->ₗ[S] O
} (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f)
参数：hf : IsBaseChange S f；hg : IsBaseChange T g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsBaseChange.of_lift_unique`：IsBaseChange.of_lift_unique (h : forall (Q 
: Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall
 [IsScalarTower R…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `IsScalarTower.to₁₂₄`：∀ (M : Type u_9) (N : Type u_10) (P : Type u_11) (Q
 : Type u_12) [inst : SMul M N] [inst_1 : SMul M P]   [inst_2 : SMul M Q] [inst_
3 : SMul …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsBaseChange.lift_eq`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {S : 
Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : CommSem
iring R] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBaseChange.algHom_ext'`：IsBaseChange.algHom_ext' [Module R Q] [IsScala
rTower R S Q] (g₁ g₂ : N ->ₗ[S] Q) (e : (g₁.restrictScalars R).comp f = (g₂.rest
rictScalars R)…
· 使用定理 `IsBaseChange.lift_comp`：IsBaseChange.lift_comp (g : M ->ₗ[R] Q) : ((h.li
ft g).restrictScalars R).comp f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O}
    (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  let := Module.compHom Q (algebraMap S T)
  have : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := IsScalarTower.to₁₂₄ _ _ T _
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp, IsBaseChange.lift_comp, ← e]
  ext
  rfl

/-- If `N` is the base change of `M` to `S` and `O` the base change of `M` to `T`, then
`O` is the base change of `N` to `T`. -/
/-
**IsBaseChange.of_comp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.of_comp {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[S
] O} (hc : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f)) : IsBaseChange T h
参数：hf : IsBaseChange S f；hc : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsBaseChange.of_lift_unique`：IsBaseChange.of_lift_unique (h : forall (Q 
: Type max v₁ v₂ v₃) [AddCommMonoid Q], forall [Module R Q] [Module S Q], forall
 [IsScalarTower R…
· 使用定理 `IsScalarTower.restrictScalars`：IsScalarTower.restrictScalars [Module S M
] : letI
· 使用定理 `IsScalarTower.of_algebraMap_smul`：of_algebraMap_smul [SMul R M] (h : for
all (r : R) (x : M), algebraMap R A r • x = r • x) : IsScalarTower R A M where s
mul_assoc r a x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsBaseChange.algHom_ext'`：IsBaseChange.algHom_ext' [Module R Q] [IsScala
rTower R S Q] (g₁ g₂ : N ->ₗ[S] Q) (e : (g₁.restrictScalars R).comp f = (g₂.rest
rictScalars R)…
· 使用定理 `IsBaseChange.lift_comp`：IsBaseChange.lift_comp (g : M ->ₗ[R] Q) : ((h.li
ft g).restrictScalars R).comp f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_assoc`：comp_assoc {R₄ M₄ : Type*} [Semiring R₄] [AddCommM
onoid M₄] [Module R₄ M₄] {σ₃₄ : R₃ ->+* R₄} {σ₂₄ : R₂ ->+* R₄} {σ₁₄ : R₁ ->+* R₄
} [RingHom…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
If `N` is the base change of `M` to `S` and `O` the base change of `M` to `T`, t
hen
`O` is the base change of `N` to `T`.
-/
lemma IsBaseChange.of_comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {h : N →ₗ[S] O}
    (hc : IsBaseChange T ((h : N →ₗ[R] O) ∘ₗ f)) :
    IsBaseChange T h := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ r
  let : Module R Q := .restrictScalars R S Q
  have : IsScalarTower R S Q := .restrictScalars R S Q
  have : IsScalarTower R T Q := IsScalarTower.of_algebraMap_smul fun r x ↦ by
    simp [IsScalarTower.algebraMap_apply R S T]
  let r' : M →ₗ[R] Q := r ∘ₗ f
  let q : O →ₗ[T] Q := hc.lift r'
  refine ⟨q, ?_, ?_⟩
  · apply hf.algHom_ext'
    simp [r', q, LinearMap.comp_assoc, hc.lift_comp]
  · intro q' hq'
    apply hc.algHom_ext'
    apply_fun LinearMap.restrictScalars R at hq'
    rw [← LinearMap.comp_assoc]
    rw [show q'.restrictScalars R ∘ₗ h.restrictScalars R = _ from hq', hc.lift_comp]

/-- If `N` is the base change `M` to `S`, then `O` is the base change of `M` to `T` if and
only if `O` is the base change of `N` to `T`. -/
/-
**IsBaseChange.comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsBaseChange.comp_iff {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {h : N ->ₗ[
S] O} : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f) ↔ IsBaseChange T h
参数：hf : IsBaseChange S f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用引理 `IsBaseChange.of_comp`：IsBaseChange.of_comp {f : M ->ₗ[R] N} (hf : IsBase
Change S f) {h : N ->ₗ[S] O} (hc : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f)) : IsB
aseChange …
· 使用定理 `IsBaseChange.comp`：IsBaseChange.comp {f : M ->ₗ[R] N} (hf : IsBaseChange
 S f) {g : N ->ₗ[S] O} (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScal
ars R).…

--- 原说明 ---
If `N` is the base change `M` to `S`, then `O` is the base change of `M` to `T` 
if and
only if `O` is the base change of `N` to `T`.
-/
lemma IsBaseChange.comp_iff {f : M →ₗ[R] N} (hf : IsBaseChange S f) {h : N →ₗ[S] O} :
    IsBaseChange T ((h : N →ₗ[R] O) ∘ₗ f) ↔ IsBaseChange T h :=
  ⟨fun hc ↦ IsBaseChange.of_comp hf hc, fun hh ↦ IsBaseChange.comp hf hh⟩

/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `M` be an `R`-module, `P` be an `S`
  module, `N` be the base change of `M` to `S`, then `P ⊗[S] N` is isomorphic to `P ⊗[R] M`
  as `S`-modules. -/
/-
**IsBaseChange.tensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsBaseChange.tensorEquiv {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (P : Typ
e*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] : P otimes[
S] N ≃ₗ[S] P otimes[R] M
参数：hf : IsBaseChange S f；P : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative ring, `S` be an `R`-algebra, `M` be an `R`-module, `P` 
be an `S`
  module, `N` be the base change of `M` to `S`, then `P ⊗[S] N` is isomorphic to
 `P ⊗[R] M`
  as `S`-modules.
-/
noncomputable def IsBaseChange.tensorEquiv {f : M →ₗ[R] N} (hf : IsBaseChange S f) (P : Type*)
    [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] : P ⊗[S] N ≃ₗ[S] P ⊗[R] M :=
  LinearEquiv.lTensor P hf.equiv.symm ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S P M
/-
**IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap {f : M ->ₗ[R] N} (hf : IsBas
eChange S f) (x : R) : hf.map hf LinearMap.id (LinearMap.lsmul R M x) = LinearMa
p.lsmul S N (algebraMap R S x)
参数：hf : IsBaseChange S f；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
-/
theorem IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap
    {f : M →ₗ[R] N} (hf : IsBaseChange S f) (x : R) :
    hf.map hf LinearMap.id (LinearMap.lsmul R M x) = LinearMap.lsmul S N (algebraMap R S x) := by
  ext y
  refine IsTensorProduct.inductionOn hf y (by simp) ?_ (fun _ _ ha hb ↦ by simp [ha, hb])
  intro s m
  rw [hf.map_eq hf]
  simpa using smul_comm x s (f m)

variable {R' S' : Type*} [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

open IsScalarTower (toAlgHom algebraMap_apply)

variable (R S R' S')

/-- A type-class stating that the following diagram of scalar towers
```
R  →  S
↓     ↓
R' →  S'
```
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
/-
**Algebra.IsPushout** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebra`。
形式化陈述：(R : Type u_1) →   (S : Type v₃) →     [inst : CommSemiring R] →       [in
st_1 : CommSemiring S] →         [inst_2 : Algebra R S] →           (R' : Type u
_6) →             (S' : Type u_7) →               [inst_3 : CommSemiring R'] →  
               [inst_4 : CommSemiring S'] →                   [inst_5 : Algebra 
R R'] →                     [inst_6 : Algebra S S'] →                       [ins
t_7 : Algebra R' S'] →                         [inst_8 : Algebra R S'] → [IsScal
arTower R R' S'] → [IsScalarTower R S S'] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type-class stating that the following diagram of scalar towers
```
R  →  S
↓     ↓
R' →  S'
```
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
class Algebra.IsPushout : Prop where
  out : IsBaseChange S (toAlgHom R R' S').toLinearMap

/-- The isomorphism `S' ≃ S ⊗[R] R` given `Algebra.IsPushout R S R' S'`. -/
noncomputable
/-
**Algebra.IsPushout.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.equiv [h : Algebra.IsPushout R S R' S'] : S otimes[R] R'
 ≃ₐ[S] S' where __
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
-/
def Algebra.IsPushout.equiv [h : Algebra.IsPushout R S R' S'] : S ⊗[R] R' ≃ₐ[S] S' where
  __ := h.out.equiv
  map_mul' x y := by
    dsimp
    induction x with
    | zero => simp
    | add x y _ _ => simp [*, add_mul]
    | tmul a b =>
      induction y with
      | zero => simp
      | add x y _ _ => simp [*, mul_add]
      | tmul x y => simp [IsBaseChange.equiv_tmul, Algebra.smul_def, mul_mul_mul_comm]
  commutes' := by simp [IsBaseChange.equiv_tmul, Algebra.smul_def]
/-
**Algebra.IsPushout.equiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.equiv_tmul [h : Algebra.IsPushout R S R' S'] (a : S) (b 
: R') : equiv R S R' S' (a otimesₜ b) = algebraMap _ _ a * algebraMap _ _ b
参数：a : S；b : R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
· 使用定理 `IsBaseChange.equiv_tmul`：IsBaseChange.equiv_tmul (s : S) (m : M) : h.equ
iv (s otimesₜ m) = s • f m
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
-/
lemma Algebra.IsPushout.equiv_tmul [h : Algebra.IsPushout R S R' S'] (a : S) (b : R') :
    equiv R S R' S' (a ⊗ₜ b) = algebraMap _ _ a * algebraMap _ _ b :=
  (h.out.equiv_tmul _ _).trans (Algebra.smul_def _ _)
/-
**Algebra.IsPushout.equiv_symm_algebraMap_left** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.equiv_symm_algebraMap_left [Algebra.IsPushout R S R' S']
 (a : S) : (equiv R S R' S').symm (algebraMap S S' a) = a otimesₜ 1
参数：a : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用引理 `Algebra.IsPushout.equiv_tmul`：Algebra.IsPushout.equiv_tmul [h : Algebra.
IsPushout R S R' S'] (a : S) (b : R') : equiv R S R' S' (a otimesₜ b) = algebraM
ap _ _ a * algebra…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma Algebra.IsPushout.equiv_symm_algebraMap_left [Algebra.IsPushout R S R' S'] (a : S) :
    (equiv R S R' S').symm (algebraMap S S' a) = a ⊗ₜ 1 := by
  rw [(equiv R S R' S').symm_apply_eq, equiv_tmul, map_one, mul_one]
/-
**Algebra.IsPushout.equiv_symm_algebraMap_right** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.equiv_symm_algebraMap_right [Algebra.IsPushout R S R' S'
] (a : R') : (equiv R S R' S').symm (algebraMap R' S' a) = 1 otimesₜ a
参数：a : R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.symm_apply_eq`：symm_apply_eq (e : A₁ ≃ₐ[R] A₂) {x y} : e.symm x
 = y ↔ x = e y
· 使用引理 `Algebra.IsPushout.equiv_tmul`：Algebra.IsPushout.equiv_tmul [h : Algebra.
IsPushout R S R' S'] (a : S) (b : R') : equiv R S R' S' (a otimesₜ b) = algebraM
ap _ _ a * algebra…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma Algebra.IsPushout.equiv_symm_algebraMap_right [Algebra.IsPushout R S R' S'] (a : R') :
    (equiv R S R' S').symm (algebraMap R' S' a) = 1 ⊗ₜ a := by
  rw [(equiv R S R' S').symm_apply_eq, equiv_tmul, map_one, one_mul]

variable {R S R' S'}

@[symm]
/-
**Algebra.IsPushout.symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPusho
ut R R' S S' where out
参数：h : Algebra.IsPushout R S R' S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AddEquiv.map_add'`：∀ {A : Type u_9} {B : Type u_10} [inst : Add A] [inst
_1 : Add B] (self : A ≃+ B) (x y : A),   self.toFun (x + y) = self.toFun x + sel
f.toFun…
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `Algebra.IsPushout.equiv_tmul`：Algebra.IsPushout.equiv_tmul [h : Algebra.
IsPushout R S R' S'] (a : S) (b : R') : equiv R S R' S' (a otimesₜ b) = algebraM
ap _ _ a * algebra…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
（共 39 条，此处仅展示前 30 条）
-/
theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' where
  out := .of_equiv
    { __ := (TensorProduct.comm R ..).toAddEquiv.trans (equiv R S R' S').toAddEquiv,
      map_smul' _ x := x.induction_on (by simp) (fun _ _ ↦ by
        simp [equiv_tmul, Algebra.smul_def, mul_left_comm]) (by simp +contextual) }
    fun _ ↦ by simp [equiv_tmul]

variable (R S R' S')
/-
**Algebra.IsPushout.comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R
 R' S S'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
-/
theorem Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S' :=
  ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R R S S where
  out := .of_equiv (TensorProduct.lid R S) fun _ ↦ by simp
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.IsPushout R S R S := .symm inferInstance

variable {R S R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra
/-
**TensorProduct.isPushout** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TensorProduct.isPushout {R S T : Type*} [CommSemiring R] [CommSemiring S] 
[CommSemiring T] [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (S otimes
[R] T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.isBaseChange`：TensorProduct.isBaseChange : IsBaseChange S 
(TensorProduct.mk R S M 1)
-/
instance TensorProduct.isPushout {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (S ⊗[R] T) :=
  ⟨TensorProduct.isBaseChange R T S⟩
/-
**TensorProduct.isPushout'** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：TensorProduct.isPushout' {R S T : Type*} [CommSemiring R] [CommSemiring S]
 [CommSemiring T] [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (S otime
s[R] T)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.symm`：Algebra.IsPushout.symm (h : Algebra.IsPushout R 
S R' S') : Algebra.IsPushout R R' S S' where out
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance TensorProduct.isPushout' {R S T : Type*} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (S ⊗[R] T) :=
  Algebra.IsPushout.symm inferInstance
/-
**Algebra.IsPushout.tensorProduct_tensorProduct** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.tensorProduct_tensorProduct (R S A B : Type*) [CommSemir
ing R] [CommSemiring S] [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra
 R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S] {_ : Algebra (A otimes[R
] S) (B otimes[R] S)} {_ : IsScalarTower A (A otimes[R] S) (B otimes[R] S)} (H :
 (algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebra.TensorProduct.include
Right.toRingHom = Algebra.TensorProduct.includeRight.toRingHom) : Algebra.IsPush
out A B (A otimes[R] S) (B
参数：R S A B : Type*；A otimes[R] S；B otimes[R] S；A otimes[R] S；B otimes[R] S；H : (
algebraMap (A otimes[R] S) (B otimes[R] S)).comp Algebra.TensorProduct.includeRi
ght.toRingHom = Algebra.TensorProduct.includeRight.toRingHom。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `isBaseChange_tensorProduct_map`：isBaseChange_tensorProduct_map {f : M ->
ₗ[S] N} (hf : IsBaseChange A f) : IsBaseChange A (AlgebraTensorModule.map f (Lin
earMap.id (R
· 使用定理 `IsBaseChange.linearMap`：IsBaseChange.linearMap : IsBaseChange S (Algebra
.linearMap R S)
-/
lemma Algebra.IsPushout.tensorProduct_tensorProduct
    (R S A B : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra R S]
    {_ : Algebra (A ⊗[R] S) (B ⊗[R] S)} {_ : IsScalarTower A (A ⊗[R] S) (B ⊗[R] S)}
    (H : (algebraMap (A ⊗[R] S) (B ⊗[R] S)).comp Algebra.TensorProduct.includeRight.toRingHom =
      Algebra.TensorProduct.includeRight.toRingHom) :
    Algebra.IsPushout A B (A ⊗[R] S) (B ⊗[R] S) := by
  constructor
  convert! isBaseChange_tensorProduct_map (R := R) (P := S) _ (IsBaseChange.linearMap A B)
  ext s
  simpa using congr($H s)

/-- If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomorphism `S' → A`.
-/
@[simps! -isSimp apply]
/-
**Algebra.pushoutDesc** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semirin
g A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (hf : forall x y, f x * g 
y = g y * f x) : S' ->ₐ[R] A
参数：f : S ->ₐ[R] A；g : R' ->ₐ[R] A；hf : forall x y, f x * g y = g y * f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and 
`g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomor
phism `S' → A`.
-/
noncomputable def Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (hf : ∀ x y, f x * g y = g y * f x) :
    S' →ₐ[R] A :=
  (Algebra.TensorProduct.lift f g hf).comp
    ((Algebra.IsPushout.equiv R S R' S').symm.toAlgHom.restrictScalars R)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.pushoutDesc_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.pushoutDesc_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiri
ng A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) (x : S) : Algebra.pus
houtDesc S' f g H (algebraMap S S' x) = f x
参数：f : S ->ₐ[R] A；g : R' ->ₐ[R] A；H；x : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.pushoutDesc_apply`：∀ {R : Type u_1} {S : Type v₃} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {R' : Type u_6}   (S'
 : Type u_7) [i…
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Algebra.pushoutDesc_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : S) :
    Algebra.pushoutDesc S' f g H (algebraMap S S' x) = f x := by
  simp [Algebra.pushoutDesc_apply]
/-
**Algebra.lift_algHom_comp_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.lift_algHom_comp_left [Algebra.IsPushout R S R' S'] {A : Type*} [S
emiring A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) : (Algebra.pusho
utDesc S' f g H).comp (toAlgHom R S S') = f
参数：f : S ->ₐ[R] A；g : R' ->ₐ[R] A；H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Algebra.pushoutDesc_left`：Algebra.pushoutDesc_left [Algebra.IsPushout R 
S R' S'] {A : Type*} [Semiring A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] 
A) (H) (x : S)…
-/
theorem Algebra.lift_algHom_comp_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R S S') = f :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x :)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.pushoutDesc_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.pushoutDesc_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semir
ing A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) (x : R') : Algebra.p
ushoutDesc S' f g H (algebraMap R' S' x) = g x
参数：f : S ->ₐ[R] A；g : R' ->ₐ[R] A；H；x : R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.pushoutDesc_apply`：∀ {R : Type u_1} {S : Type v₃} [inst : CommSe
miring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] {R' : Type u_6}   (S'
 : Type u_7) [i…
· 使用引理 `Algebra.IsPushout.equiv_symm_algebraMap_right`：Algebra.IsPushout.equiv_s
ymm_algebraMap_right [Algebra.IsPushout R S R' S'] (a : R') : (equiv R S R' S').
symm (algebraMap R' S' a) = 1 otime…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Algebra.pushoutDesc_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : R') :
    Algebra.pushoutDesc S' f g H (algebraMap R' S' x) = g x := by
  simp [Algebra.pushoutDesc_apply, Algebra.IsPushout.equiv_symm_algebraMap_right]
/-
**Algebra.lift_algHom_comp_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.lift_algHom_comp_right [Algebra.IsPushout R S R' S'] {A : Type*} [
Semiring A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R] A) (H) : (Algebra.push
outDesc S' f g H).comp (toAlgHom R R' S') = g
参数：f : S ->ₐ[R] A；g : R' ->ₐ[R] A；H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Algebra.pushoutDesc_right`：Algebra.pushoutDesc_right [Algebra.IsPushout 
R S R' S'] {A : Type*} [Semiring A] [Algebra R A] (f : S ->ₐ[R] A) (g : R' ->ₐ[R
] A) (H) (x : R…
-/
theorem Algebra.lift_algHom_comp_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R R' S') = g :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x :)

@[ext (iff := false)]
/-
**Algebra.IsPushout.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type*}
 [Semiring A] [Algebra R A] {f g : S' ->ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') 
= g.comp (toAlgHom R R' S')) (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R
 S S')) : f = g
参数：h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S')；h₂ : f.comp (toAlg
Hom R S S') = g.comp (toAlgHom R S S')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `IsBaseChange.inductionOn`：∀ {R : Type u_1} {M : Type v₁} {N : Type v₂} {
S : Type v₃} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : Com
mSemiring R] […
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
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
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
-/
theorem Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] {f g : S' →ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S'))
    (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R S S')) : f = g := by
  ext x
  refine H.1.inductionOn x _ ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def, map_mul, map_mul, e]
    congr 1
    exact (AlgHom.congr_fun h₂ s :)
  · intro s₁ s₂ e₁ e₂
    rw [map_add, map_add, e₁, e₂]

variable (R S R')
/--
Let the following be a commutative diagram of rings
```
  R  →  S  →  T
  ↓     ↓     ↓
  R' →  S' →  T'
```
where the left-hand square is a pushout. Then the following are equivalent:
- the big rectangle is a pushout.
- the right-hand square is a pushout.

Note that this is essentially the isomorphism `T ⊗[S] (S ⊗[R] R') ≃ₐ[T] T ⊗[R] R'`.
-/
/-
**Algebra.IsPushout.comp_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.comp_iff {T' : Type*} [CommSemiring T'] [Algebra R T'] [
Algebra S' T'] [Algebra S T'] [Algebra T T'] [Algebra R' T'] [IsScalarTower R T 
T'] [IsScalarTower S T T'] [IsScalarTower S S' T'] [IsScalarTower R R' T'] [IsSc
alarTower R S' T'] [IsScalarTower R' S' T'] [Algebra.IsPushout R S R' S'] : Alge
bra.IsPushout R T R' T' ↔ Algebra.IsPushout S T S' T'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.isPushout_iff`：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiri
ng R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (R' : Type u_6)   (S' : T
ype u_7) [i…
· 使用引理 `IsBaseChange.comp_iff`：IsBaseChange.comp_iff {f : M ->ₗ[R] N} (hf : IsBa
seChange S f) {h : N ->ₗ[S] O} : IsBaseChange T ((h : N ->ₗ[R] O) ∘ₗ f) ↔ IsBase
Change T h
· 使用定理 `Algebra.IsPushout.out`：∀ {R : Type u_1} {S : Type v₃} {inst : CommSemiri
ng R} {inst_1 : CommSemiring S} {inst_2 : Algebra R S} {R' : Type u_6}   {S' : T
ype u_7} {i…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Let the following be a commutative diagram of rings
```
  R  →  S  →  T
  ↓     ↓     ↓
  R' →  S' →  T'
```
where the left-hand square is a pushout. Then the following are equivalent:
- the big rectangle is a pushout.
- the right-hand square is a pushout.

Note that this is essentially the isomorphism `T ⊗[S] (S ⊗[R] R') ≃ₐ[T] T ⊗[R] R
'`.
-/
lemma Algebra.IsPushout.comp_iff {T' : Type*} [CommSemiring T'] [Algebra R T']
    [Algebra S' T'] [Algebra S T'] [Algebra T T'] [Algebra R' T']
    [IsScalarTower R T T'] [IsScalarTower S T T'] [IsScalarTower S S' T']
    [IsScalarTower R R' T'] [IsScalarTower R S' T'] [IsScalarTower R' S' T']
    [Algebra.IsPushout R S R' S'] :
    Algebra.IsPushout R T R' T' ↔ Algebra.IsPushout S T S' T' := by
  let f : R' →ₗ[R] S' := (IsScalarTower.toAlgHom R R' S').toLinearMap
  have : IsScalarTower R S T' := .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_apply R S' T', algebraMap_apply R S S', ← algebraMap_apply S S' T']
  have heq : (toAlgHom S S' T').toLinearMap.restrictScalars R ∘ₗ f =
      (toAlgHom R R' T').toLinearMap := by
    ext x
    simp [f, ← IsScalarTower.algebraMap_apply]
  rw [isPushout_iff, isPushout_iff, ← heq, IsBaseChange.comp_iff]
  exact Algebra.IsPushout.out

variable {R R' S S'} in
/-
**Algebra.IsPushout.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.IsPushout.of_equiv [h : IsPushout R R' S S'] {T : Type*} [CommSemi
ring T] [Algebra R' T] [Algebra S T] [Algebra R T] [IsScalarTower R S T] [IsScal
arTower R R' T] (e : S' ≃ₐ[R'] T) (he : e.toRingHom.comp (algebraMap S S') = alg
ebraMap S T) : IsPushout R R' S T
参数：e : S' ≃ₐ[R'] T；he : e.toRingHom.comp (algebraMap S S') = algebraMap S T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.isPushout_iff`：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiri
ng R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (R' : Type u_6)   (S' : T
ype u_7) [i…
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma Algebra.IsPushout.of_equiv [h : IsPushout R R' S S']
    {T : Type*} [CommSemiring T] [Algebra R' T] [Algebra S T] [Algebra R T]
    [IsScalarTower R S T] [IsScalarTower R R' T] (e : S' ≃ₐ[R'] T)
    (he : e.toRingHom.comp (algebraMap S S') = algebraMap S T) :
    IsPushout R R' S T := by
  rw [isPushout_iff] at h ⊢
  refine IsBaseChange.of_equiv (h.equiv ≪≫ₗ e.toLinearEquiv) fun x ↦ ?_
  simpa [h.equiv_tmul] using DFunLike.congr_fun he x

namespace Algebra

variable (A B : Type*)
  [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- (Implementation) If `B = S ⊗[R] A`, this is the canonical `R`-isomorphism:
`B ⊗[A] M ≃ₗ[S] S ⊗[R] M`. See `IsPushout.cancelBaseChange` for the `S`-linear version. -/
noncomputable
/-
**Algebra.IsPushout.cancelBaseChangeAux** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.IsPus
hout`。
形式化陈述：(R : Type u_1) →   (S : Type v₃) →     [inst : CommSemiring R] →       [in
st_1 : CommSemiring S] →         [inst_2 : Algebra R S] →           (A : Type u_
8) →             (B : Type u_9) →               [inst_3 : CommRing A] →         
        [inst_4 : CommRing B] →                   [inst_5 : Algebra R A] →      
               [inst_6 : Algebra R B] →                       [inst_7 : Algebra 
A B] →                         [inst_8 : Algebra S B] →                         
  [inst_9 : IsScalarTower R A B] →                             [inst_10 : IsScal
arTower R S B] →                               [Algebra.IsPushout R S A B] →    
                             (M : Type u_10) →                                  
 [inst_12 : AddCommGroup M] →                                     [inst_13 : _ro
ot_.Module R M] →                                       [inst_14 : _root_.Module
 A M] →                                         [IsScalarTower R A M] → TensorPr
oduct A B M ≃ₗ[R] TensorProduct R S M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsPushout.cancelBaseChangeAux : B ⊗[A] M ≃ₗ[R] S ⊗[R] M :=
  have : IsPushout R A S B := IsPushout.symm inferInstance
  (AlgebraTensorModule.congr ((IsPushout.equiv R A S B).toLinearEquiv).symm
      (LinearEquiv.refl _ _)).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange _ _ A _ _).restrictScalars R ≪≫ₗ
    (_root_.TensorProduct.comm _ _ _).restrictScalars R

@[simp]
/-
**Algebra.IsPushout.cancelBaseChangeAux_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.IsPushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (M : Type u_10) [
inst_12 : AddCommGroup M] [inst_13 : _root_.Module R M]   [inst_14 : _root_.Modu
le A M] [inst_15 : IsScalarTower R A M] (s : S) (m : M),   (Algebra.IsPushout.ca
ncelBaseChangeAux R S A B M).symm (s ⊗ₜ[R] m) = (algebraMap S B) s ⊗ₜ[A] m
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；M : Type u_10；s : S；m : M；
Algebra.IsPushout.cancelBaseChangeAux R S A B M；s ⊗ₜ[R] m；algebraMap S B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.restrictScalars_symm_apply`：∀ (R : Type u_1) {S : Type u_4} 
{M : Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst
_2 : AddCommMonoid M] [inst_…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlgEquiv.toLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用引理 `Algebra.IsPushout.equiv_tmul`：Algebra.IsPushout.equiv_tmul [h : Algebra.
IsPushout R S R' S'] (a : S) (b : R') : equiv R S R' S' (a otimesₜ b) = algebraM
ap _ _ a * algebra…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPushout.cancelBaseChangeAux_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChangeAux R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m := by
  simp [IsPushout.cancelBaseChangeAux, IsPushout.equiv_tmul]

/-- If `B = S ⊗[R] A`, this is the canonical `S`-isomorphism: `B ⊗[A] M ≃ₗ[S] S ⊗[R] M`.
This is the cancelling on the left version of
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. -/
noncomputable
/-
**Algebra.IsPushout.cancelBaseChange** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.IsPushou
t`。
形式化陈述：(R : Type u_1) →   (S : Type v₃) →     [inst : CommSemiring R] →       [in
st_1 : CommSemiring S] →         [inst_2 : Algebra R S] →           (A : Type u_
8) →             (B : Type u_9) →               [inst_3 : CommRing A] →         
        [inst_4 : CommRing B] →                   [inst_5 : Algebra R A] →      
               [inst_6 : Algebra R B] →                       [inst_7 : Algebra 
A B] →                         [inst_8 : Algebra S B] →                         
  [inst_9 : IsScalarTower R A B] →                             [inst_10 : IsScal
arTower R S B] →                               [Algebra.IsPushout R S A B] →    
                             (M : Type u_10) →                                  
 [inst_12 : AddCommGroup M] →                                     [inst_13 : _ro
ot_.Module R M] →                                       [inst_14 : _root_.Module
 A M] →                                         [IsScalarTower R A M] → TensorPr
oduct A B M ≃ₗ[S] TensorProduct R S M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def IsPushout.cancelBaseChange : B ⊗[A] M ≃ₗ[S] S ⊗[R] M :=
  LinearEquiv.symm <|
  AddEquiv.toLinearEquiv (IsPushout.cancelBaseChangeAux R S A B M).symm <| by
    intro s x
    induction x with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s' m => simp [Algebra.smul_def, TensorProduct.smul_tmul']

@[simp]
/-
**Algebra.IsPushout.cancelBaseChange_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsP
ushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (M : Type u_10) [
inst_12 : AddCommGroup M] [inst_13 : _root_.Module R M]   [inst_14 : _root_.Modu
le A M] [inst_15 : IsScalarTower R A M] (m : M),   (Algebra.IsPushout.cancelBase
Change R S A B M) (1 ⊗ₜ[A] m) = 1 ⊗ₜ[R] m
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；M : Type u_10；m : M；Algebr
a.IsPushout.cancelBaseChange R S A B M；1 ⊗ₜ[A] m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.restrictScalars_apply`：∀ (R : Type u_1) {S : Type u_4} {M : 
Type u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : 
AddCommMonoid M] [inst_…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPushout.cancelBaseChange_tmul (m : M) :
    IsPushout.cancelBaseChange R S A B M (1 ⊗ₜ m) = 1 ⊗ₜ m := by
  change ((cancelBaseChangeAux R S A B M).symm).symm (1 ⊗ₜ[A] m) = 1 ⊗ₜ[R] m
  simp [cancelBaseChangeAux, TensorProduct.one_def]

@[simp]
/-
**Algebra.IsPushout.cancelBaseChange_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.IsPushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (M : Type u_10) [
inst_12 : AddCommGroup M] [inst_13 : _root_.Module R M]   [inst_14 : _root_.Modu
le A M] [inst_15 : IsScalarTower R A M] (s : S) (m : M),   (Algebra.IsPushout.ca
ncelBaseChange R S A B M).symm (s ⊗ₜ[R] m) = (algebraMap S B) s ⊗ₜ[A] m
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；M : Type u_10；s : S；m : M；
Algebra.IsPushout.cancelBaseChange R S A B M；s ⊗ₜ[R] m；algebraMap S B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsPushout.cancelBaseChangeAux_symm_tmul`：∀ (R : Type u_1) (S : T
ype v₃) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]
 (A : Type u_8)   (B : Type u_9) [ins…
-/
lemma IsPushout.cancelBaseChange_symm_tmul (s : S) (m : M) :
    (IsPushout.cancelBaseChange R S A B M).symm (s ⊗ₜ m) = algebraMap S B s ⊗ₜ m :=
  IsPushout.cancelBaseChangeAux_symm_tmul R S A B M s m

variable (C : Type*) [CommRing C] [Algebra R C] [Algebra A C] [IsScalarTower R A C]

/-- Algebra version of `IsPushout.cancelBaseChange`. -/
/-
**Algebra.IsPushout.cancelBaseChangeAlg** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.IsPus
hout`。
形式化陈述：(R : Type u_1) →   (S : Type v₃) →     [inst : CommSemiring R] →       [in
st_1 : CommSemiring S] →         [inst_2 : Algebra R S] →           (A : Type u_
8) →             (B : Type u_9) →               [inst_3 : CommRing A] →         
        [inst_4 : CommRing B] →                   [inst_5 : Algebra R A] →      
               [inst_6 : Algebra R B] →                       [inst_7 : Algebra 
A B] →                         [inst_8 : Algebra S B] →                         
  [inst_9 : IsScalarTower R A B] →                             [inst_10 : IsScal
arTower R S B] →                               [Algebra.IsPushout R S A B] →    
                             (C : Type u_11) →                                  
 [inst_12 : CommRing C] →                                     [inst_13 : Algebra
 R C] →                                       [inst_14 : Algebra A C] →         
                                [IsScalarTower R A C] → TensorProduct A B C ≃ₐ[S
] TensorProduct R S C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra version of `IsPushout.cancelBaseChange`.
-/
noncomputable def IsPushout.cancelBaseChangeAlg : B ⊗[A] C ≃ₐ[S] S ⊗[R] C := by
  refine AlgEquiv.symm
    (AlgEquiv.ofLinearEquiv (IsPushout.cancelBaseChange R S A B C).symm ?_ ?_)
  · simp [TensorProduct.one_def]
  · apply LinearMap.map_mul_of_map_mul_tmul
    simp

@[simp]
/-
**Algebra.IsPushout.toLinearEquiv_cancelBaseChangeAlg** 是 Mathlib 中的一个定理，位于命名空间 
`Algebra.IsPushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (C : Type u_11) [
inst_12 : CommRing C] [inst_13 : Algebra R C]   [inst_14 : Algebra A C] [inst_15
 : IsScalarTower R A C],   ↑(Algebra.IsPushout.cancelBaseChangeAlg R S A B C) = 
Algebra.IsPushout.cancelBaseChange R S A B C
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；C : Type u_11；Algebra.IsPu
shout.cancelBaseChangeAlg R S A B C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma IsPushout.toLinearEquiv_cancelBaseChangeAlg :
    (IsPushout.cancelBaseChangeAlg R S A B C).toLinearEquiv =
      IsPushout.cancelBaseChange R S A B C := by
  rfl

@[simp]
/-
**Algebra.IsPushout.cancelBaseChangeAlg_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsPushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (C : Type u_11) [
inst_12 : CommRing C] [inst_13 : Algebra R C]   [inst_14 : Algebra A C] [inst_15
 : IsScalarTower R A C] (c : C),   (Algebra.IsPushout.cancelBaseChangeAlg R S A 
B C) (1 ⊗ₜ[A] c) = 1 ⊗ₜ[R] c
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；C : Type u_11；c : C；Algebr
a.IsPushout.cancelBaseChangeAlg R S A B C；1 ⊗ₜ[A] c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Algebra.IsPushout.cancelBaseChange_tmul`：∀ (R : Type u_1) (S : Type v₃) 
[inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (A : Ty
pe u_8)   (B : Type u_9) [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPushout.cancelBaseChangeAlg_tmul (c : C) :
    IsPushout.cancelBaseChangeAlg R S A B C (1 ⊗ₜ c) = 1 ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebra.IsPushout`。
形式化陈述：∀ (R : Type u_1) (S : Type v₃) [inst : CommSemiring R] [inst_1 : CommSemir
ing S] [inst_2 : Algebra R S] (A : Type u_8)   (B : Type u_9) [inst_3 : CommRing
 A] [inst_4 : CommRing B] [inst_5 : Algebra R A] [inst_6 : Algebra R B]   [inst_
7 : Algebra A B] [inst_8 : Algebra S B] [inst_9 : IsScalarTower R A B] [inst_10 
: IsScalarTower R S B]   [inst_11 : Algebra.IsPushout R S A B] (C : Type u_11) [
inst_12 : CommRing C] [inst_13 : Algebra R C]   [inst_14 : Algebra A C] [inst_15
 : IsScalarTower R A C] (s : S) (c : C),   (Algebra.IsPushout.cancelBaseChangeAl
g R S A B C).symm (s ⊗ₜ[R] c) = (algebraMap S B) s ⊗ₜ[A] c
参数：R : Type u_1；S : Type v₃；A : Type u_8；B : Type u_9；C : Type u_11；s : S；c : C；
Algebra.IsPushout.cancelBaseChangeAlg R S A B C；s ⊗ₜ[R] c；algebraMap S B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `AlgEquiv.ofLinearEquiv_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `Algebra.IsPushout.cancelBaseChange_symm_tmul`：∀ (R : Type u_1) (S : Type
 v₃) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S] (A
 : Type u_8)   (B : Type u_9) [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPushout.cancelBaseChangeAlg_symm_tmul (s : S) (c : C) :
    (IsPushout.cancelBaseChangeAlg R S A B C).symm (s ⊗ₜ c) = algebraMap S B s ⊗ₜ c := by
  simp [cancelBaseChangeAlg]

variable (S : Type*) [CommRing S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]
  [Algebra.IsPushout R S A B]

attribute [local instance] TensorProduct.rightAlgebra in
/-
**Algebra.IsPushout.cancelBaseChange_symm_comp_lTensor** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.IsPushout`。
形式化陈述：∀ (R : Type u_1) [inst : CommSemiring R] (A : Type u_8) [inst_1 : CommRing
 A] [inst_2 : Algebra R A] (C : Type u_11)   [inst_3 : CommRing C] [inst_4 : Alg
ebra R C] [inst_5 : Algebra A C] [inst_6 : IsScalarTower R A C] (S : Type u_12) 
  [inst_7 : CommRing S] [inst_8 : Algebra R S],   (↑(Algebra.IsPushout.cancelBas
eChangeAlg R S A (TensorProduct R S A) C).symm).comp       (Algebra.TensorProduc
t.lTensor S (IsScalarTower.toAlgHom R A C)) =     Algebra.TensorProduct.includeL
eft
参数：R : Type u_1；A : Type u_8；C : Type u_11；S : Type u_12；↑(Algebra.IsPushout.can
celBaseChangeAlg R S A (TensorProduct R S A) C).symm；Algebra.TensorProduct.lTens
or S (IsScalarTower.toAlgHom R A C)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.TensorProduct.ext_ring`：∀ {R : Type u_4} {S : Type u_5} {A : Typ
e u_6} {B : Type u_7} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_
2 : Semiring A] [ins…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClass`：∀ {R : Type u_4} {S : Type u_5} {A : Type u_6} [inst 
: CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [inst_3 : Al
gebra R…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.IsPushout.cancelBaseChangeAlg_symm_tmul`：∀ (R : Type u_1) (S : T
ype v₃) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]
 (A : Type u_8)   (B : Type u_9) [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPushout.cancelBaseChange_symm_comp_lTensor :
    AlgHom.comp (IsPushout.cancelBaseChangeAlg R S A (S ⊗[R] A) C).symm.toAlgHom
      (TensorProduct.lTensor _ (IsScalarTower.toAlgHom R A C)) =
      TensorProduct.includeLeft := by
  ext
  simp [← TensorProduct.one_def, ← TensorProduct.tmul_one_eq_one_tmul, RingHom.algebraMap_toAlgebra]

end Algebra

end IsBaseChange

