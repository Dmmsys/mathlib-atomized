/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# The general linear group of linear maps

The general linear group is defined to be the group of invertible linear maps from `M` to itself.

See also `Matrix.GeneralLinearGroup`

## Main definitions

* `LinearMap.GeneralLinearGroup`

-/

@[expose] public section


variable (R M : Type*)

namespace LinearMap

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- The group of invertible linear maps from `M` to itself -/
/-
**LinearMap.GeneralLinearGroup** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap`。
形式化陈述：GeneralLinearGroup
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group of invertible linear maps from `M` to itself
-/
abbrev GeneralLinearGroup :=
  (M →ₗ[R] M)ˣ

namespace GeneralLinearGroup

variable {R M}

/-- An invertible linear map `f` determines an equivalence from `M` to itself. -/
/-
**LinearMap.GeneralLinearGroup.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMa
p.GeneralLinearGroup`。
形式化陈述：toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M
参数：f : GeneralLinearGroup R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An invertible linear map `f` determines an equivalence from `M` to itself.
-/
def toLinearEquiv (f : GeneralLinearGroup R M) : M ≃ₗ[R] M :=
  { f.val with
    invFun := f.inv.toFun
    left_inv := fun m ↦ show (f.inv * f.val) m = m by simp
    right_inv := fun m ↦ show (f.val * f.inv) m = m by simp }
/-
**LinearMap.GeneralLinearGroup.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : LinearMap.GeneralLinearGroup R M), ⇑f.t
oLinearEquiv = ⇑↑f
参数：f : LinearMap.GeneralLinearGroup R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toLinearEquiv (f : GeneralLinearGroup R M) :
    f.toLinearEquiv = (f : M → M) := rfl
/-
**LinearMap.GeneralLinearGroup.toLinearEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：toLinearEquiv_mul (f g : GeneralLinearGroup R M) : (f * g).toLinearEquiv =
 f.toLinearEquiv * g.toLinearEquiv
参数：f g : GeneralLinearGroup R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_mul (f g : GeneralLinearGroup R M) :
    (f * g).toLinearEquiv = f.toLinearEquiv * g.toLinearEquiv := by
  rfl
/-
**LinearMap.GeneralLinearGroup.toLinearEquiv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：toLinearEquiv_inv (f : GeneralLinearGroup R M) : (f⁻¹).toLinearEquiv = (f.
toLinearEquiv)⁻¹
参数：f : GeneralLinearGroup R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_inv (f : GeneralLinearGroup R M) :
    (f⁻¹).toLinearEquiv = (f.toLinearEquiv)⁻¹ := by
  rfl

/-- An equivalence from `M` to itself determines an invertible linear map. -/
/-
**LinearMap.GeneralLinearGroup.ofLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LinearMa
p.GeneralLinearGroup`。
形式化陈述：ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where val
参数：f : M ≃ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence from `M` to itself determines an invertible linear map.
-/
def ofLinearEquiv (f : M ≃ₗ[R] M) : GeneralLinearGroup R M where
  val := f
  inv := (f.symm : M →ₗ[R] M)
  val_inv := LinearMap.ext fun _ ↦ f.apply_symm_apply _
  inv_val := LinearMap.ext fun _ ↦ f.symm_apply_apply _
/-
**LinearMap.GeneralLinearGroup.coe_ofLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   (f : M ≃ₗ[R] M), ⇑↑(LinearMap.GeneralLinearG
roup.ofLinearEquiv f) = ⇑f
参数：f : M ≃ₗ[R] M；LinearMap.GeneralLinearGroup.ofLinearEquiv f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_ofLinearEquiv (f : M ≃ₗ[R] M) :
    ofLinearEquiv f = (f : M → M) := rfl
/-
**LinearMap.GeneralLinearGroup.ofLinearEquiv_mul** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：ofLinearEquiv_mul (f g : M ≃ₗ[R] M) : ofLinearEquiv (f * g) = ofLinearEqui
v f * ofLinearEquiv g
参数：f g : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearEquiv_mul (f g : M ≃ₗ[R] M) :
    ofLinearEquiv (f * g) = ofLinearEquiv f * ofLinearEquiv g := by
  rfl
/-
**LinearMap.GeneralLinearGroup.ofLinearEquiv_inv** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.GeneralLinearGroup`。
形式化陈述：ofLinearEquiv_inv (f : M ≃ₗ[R] M) : ofLinearEquiv (f⁻¹) = (ofLinearEquiv f
)⁻¹
参数：f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofLinearEquiv_inv (f : M ≃ₗ[R] M) :
    ofLinearEquiv (f⁻¹) = (ofLinearEquiv f)⁻¹ := by
  rfl

@[simp]
/-
**LinearMap.GeneralLinearGroup.ofLinearEquiv_smul** 是 Mathlib 中的一个引理，位于命名空间 `Lin
earMap.GeneralLinearGroup`。
形式化陈述：ofLinearEquiv_smul (f : M ≃ₗ[R] M) (x : M) : ofLinearEquiv f • x = f x
参数：f : M ≃ₗ[R] M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ofLinearEquiv_smul (f : M ≃ₗ[R] M) (x : M) :
    ofLinearEquiv f • x = f x := rfl

variable (R M) in
/-- The general linear group on `R` and `M` is multiplicatively equivalent to the type of linear
equivalences between `M` and itself. -/
/-
**LinearMap.GeneralLinearGroup.generalLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Lin
earMap.GeneralLinearGroup`。
形式化陈述：generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The general linear group on `R` and `M` is multiplicatively equivalent to the ty
pe of linear
equivalences between `M` and itself.
-/
def generalLinearEquiv : GeneralLinearGroup R M ≃* M ≃ₗ[R] M where
  toFun := toLinearEquiv
  invFun := ofLinearEquiv
  map_mul' x y := by ext; rfl

@[simp]
/-
**LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap** 是 Mathlib 中的一个定
理，位于命名空间 `LinearMap.GeneralLinearGroup`。
形式化陈述：generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) : (generalLin
earEquiv R M f : M ->ₗ[R] M) = f
参数：f : GeneralLinearGroup R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
theorem generalLinearEquiv_to_linearMap (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f : M →ₗ[R] M) = f := by ext; rfl

@[simp]
/-
**LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.GeneralLinearGroup`。
形式化陈述：coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) : (generalLinearEqui
v R M f) = (f : M -> M)
参数：f : GeneralLinearGroup R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_generalLinearEquiv (f : GeneralLinearGroup R M) :
    (generalLinearEquiv R M f) = (f : M → M) := rfl

section Functoriality

variable {R₁ R₂ R₃ M₁ M₂ M₃ : Type*}
  [Semiring R₁] [Semiring R₂] [Semiring R₃]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R₁ M₁] [Module R₂ M₂] [Module R₃ M₃]
  {σ₁₂ : R₁ →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R₁ →+* R₃}
  {σ₂₁ : R₂ →+* R₁} {σ₃₂ : R₃ →+* R₂} {σ₃₁ : R₃ →+* R₁}
  [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₁₃ σ₃₁]
  [RingHomInvPair σ₂₁ σ₁₂] [RingHomInvPair σ₃₂ σ₂₃] [RingHomInvPair σ₃₁ σ₁₃]
  [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]

/-- A semilinear equivalence from `V` to `W` determines an isomorphism of general linear
groups. -/
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Linea
rMap.GeneralLinearGroup`。
形式化陈述：congrLinearEquiv (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) : GeneralLinearGroup R₁ M₁ ≃* Gene
ralLinearGroup R₂ M₂
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A semilinear equivalence from `V` to `W` determines an isomorphism of general li
near
groups.
-/
def congrLinearEquiv (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    GeneralLinearGroup R₁ M₁ ≃* GeneralLinearGroup R₂ M₂ :=
  Units.mapEquiv (LinearEquiv.conjRingEquiv e₁₂).toMulEquiv
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.GeneralLinearGroup`。
形式化陈述：∀ {R₁ : Type u_3} {R₂ : Type u_4} {M₁ : Type u_6} {M₂ : Type u_7} [inst : 
Semiring R₁] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M₁] [inst_3 : AddC
ommMonoid M₂] [inst_4 : _root_.Module R₁ M₁] [inst_5 : _root_.Module R₂ M₂]   {σ
₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [inst_6 : RingHomInvPair σ₁₂ σ₂₁] [inst_7 : Ri
ngHomInvPair σ₂₁ σ₁₂]   (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : LinearMap.GeneralLinearGroup
 R₁ M₁),   (LinearMap.GeneralLinearGroup.congrLinearEquiv e₁₂) g =     LinearMap
.GeneralLinearGroup.ofLinearEquiv (e₁₂.symm.trans (g.toLinearEquiv.trans e₁₂))
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂；g : LinearMap.GeneralLinearGroup R₁ M₁；LinearMap.General
LinearGroup.congrLinearEquiv e₁₂；e₁₂.symm.trans (g.toLinearEquiv.trans e₁₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma congrLinearEquiv_apply (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (g : GeneralLinearGroup R₁ M₁) :
    congrLinearEquiv e₁₂ g = ofLinearEquiv (e₁₂.symm.trans <| g.toLinearEquiv.trans e₁₂) :=
  rfl
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.GeneralLinearGroup`。
形式化陈述：∀ {R₁ : Type u_3} {R₂ : Type u_4} {M₁ : Type u_6} {M₂ : Type u_7} [inst : 
Semiring R₁] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M₁] [inst_3 : AddC
ommMonoid M₂] [inst_4 : _root_.Module R₁ M₁] [inst_5 : _root_.Module R₂ M₂]   {σ
₁₂ : R₁ →+* R₂} {σ₂₁ : R₂ →+* R₁} [inst_6 : RingHomInvPair σ₁₂ σ₂₁] [inst_7 : Ri
ngHomInvPair σ₂₁ σ₁₂]   (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂),   (LinearMap.GeneralLinearGroup.
congrLinearEquiv e₁₂).symm = LinearMap.GeneralLinearGroup.congrLinearEquiv e₁₂.s
ymm
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂；LinearMap.GeneralLinearGroup.congrLinearEquiv e₁₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma congrLinearEquiv_symm (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) :
    (congrLinearEquiv e₁₂).symm = congrLinearEquiv e₁₂.symm :=
  rfl

@[simp]
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv_trans** 是 Mathlib 中的一个引理，位于命名空间 
`LinearMap.GeneralLinearGroup`。
形式化陈述：congrLinearEquiv_trans {N₁ N₂ N₃ : Type*} [AddCommMonoid N₁] [AddCommMonoi
d N₂] [AddCommMonoid N₃] [Module R N₁] [Module R N₂] [Module R N₃] (e₁₂ : N₁ ≃ₗ[
R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) : (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃)
 = congrLinearEquiv (e₁₂.trans e₂₃)
参数：e₁₂ : N₁ ≃ₗ[R] N₂；e₂₃ : N₂ ≃ₗ[R] N₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congrLinearEquiv_trans
    {N₁ N₂ N₃ : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
    [Module R N₁] [Module R N₂] [Module R N₃] (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) = congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

/-- Stronger form of `congrLinearEquiv.trans` applying to semilinear maps. Not a simp lemma as
`σ₁₃` and `σ₃₁` cannot be inferred from the LHS. -/
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv_trans'** 是 Mathlib 中的一个引理，位于命名空间
 `LinearMap.GeneralLinearGroup`。
形式化陈述：congrLinearEquiv_trans' (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) : (c
ongrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) = congrLinearEquiv (e₁₂.trans 
e₂₃)
参数：e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂；e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Stronger form of `congrLinearEquiv.trans` applying to semilinear maps. Not a sim
p lemma as
`σ₁₃` and `σ₃₁` cannot be inferred from the LHS.
-/
lemma congrLinearEquiv_trans' (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) :
    (congrLinearEquiv e₁₂).trans (congrLinearEquiv e₂₃) =
      congrLinearEquiv (e₁₂.trans e₂₃) :=
  rfl

@[simp]
/-
**LinearMap.GeneralLinearGroup.congrLinearEquiv_refl** 是 Mathlib 中的一个引理，位于命名空间 `
LinearMap.GeneralLinearGroup`。
形式化陈述：congrLinearEquiv_refl : congrLinearEquiv (LinearEquiv.refl R₁ M₁) = MulEqu
iv.refl (GeneralLinearGroup R₁ M₁)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma congrLinearEquiv_refl :
    congrLinearEquiv (LinearEquiv.refl R₁ M₁) = MulEquiv.refl (GeneralLinearGroup R₁ M₁) :=
  rfl

end Functoriality

end GeneralLinearGroup

end LinearMap

