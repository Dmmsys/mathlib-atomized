/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bilinear form and linear maps

This file describes the relation between bilinear forms and linear maps.

## TODO

A lot of this file is now redundant following the replacement of the dedicated `_root_.BilinForm`
structure with `LinearMap.BilinForm`, which is just an alias for `M →ₗ[R] M →ₗ[R] R`. For example
`LinearMap.BilinForm.toLinHom` is now just the identity map. This redundant code should be removed.

## Notation

Given any term `B` of type `BilinForm`, due to a coercion, can use
the notation `B x y` to refer to the function field, i.e. `B x y = B.bilin x y`.

In this file we use the following type variables:
- `M`, `M'`, ... are modules over the commutative semiring `R`,
- `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
- `V`, ... is a vector space over the field `K`.

## References

* <https://en.wikipedia.org/wiki/Bilinear_form>

## Tags

Bilinear form,
-/

@[expose] public section

open LinearMap (BilinForm)
open LinearMap (BilinMap)
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

section ToLin'

/-- Auxiliary definition to define `toLinHom`; see below. -/
/-
**LinearMap.BilinForm.toLinHomAux** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition to define `toLinHom`; see below.
-/
def toLinHomAux₁ (A : BilinForm R M) (x : M) : M →ₗ[R] R := A x

variable (B)
/-
**LinearMap.BilinForm.sum_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sum_left {α} (t : Finset α) (g : α -> M) (w : M) : B (∑ i in t, g i) w = ∑
 i in t, B (g i) w
参数：t : Finset α；g : α -> M；w : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
-/
theorem sum_left {α} (t : Finset α) (g : α → M) (w : M) :
    B (∑ i ∈ t, g i) w = ∑ i ∈ t, B (g i) w :=
  B.map_sum₂ t g w

variable (w : M)
/-
**LinearMap.BilinForm.sum_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sum_right {α} (t : Finset α) (w : M) (g : α -> M) : B w (∑ i in t, g i) = 
∑ i in t, B w (g i)
参数：t : Finset α；w : M；g : α -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem sum_right {α} (t : Finset α) (w : M) (g : α → M) :
    B w (∑ i ∈ t, g i) = ∑ i ∈ t, B w (g i) := map_sum _ _ _
/-
**LinearMap.BilinForm.sum_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：sum_apply {α} (t : Finset α) (B : α -> BilinForm R M) (v w : M) : (∑ i in 
t, B i) v w = ∑ i in t, B i v w
参数：t : Finset α；B : α -> BilinForm R M；v w : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_apply {α} (t : Finset α) (B : α → BilinForm R M) (v w : M) :
    (∑ i ∈ t, B i) v w = ∑ i ∈ t, B i v w := by
  simp only [coe_sum, Finset.sum_apply]

variable {B}

/-- The linear map obtained from a `BilinForm` by fixing the right co-ordinate and evaluating in
the left. -/
/-
**LinearMap.BilinForm.toLinHomFlip** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：toLinHomFlip : BilinForm R M ->ₗ[R] M ->ₗ[R] M ->ₗ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map obtained from a `BilinForm` by fixing the right co-ordinate and e
valuating in
the left.
-/
def toLinHomFlip : BilinForm R M →ₗ[R] M →ₗ[R] M →ₗ[R] R :=
  flipHom.toLinearMap
/-
**LinearMap.BilinForm.toLin'Flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bili
nForm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   (A : LinearMap.BilinForm R M) (x : M), ⇑
((LinearMap.BilinForm.toLinHomFlip A) x) = fun y => (A y) x
参数：A : LinearMap.BilinForm R M；x : M；(LinearMap.BilinForm.toLinHomFlip A) x；A y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem toLin'Flip_apply (A : BilinForm R M) (x : M) : toLinHomFlip (M := M) A x = fun y => A y x :=
  rfl

end ToLin'

end BilinForm

end LinearMap

namespace LinearMap

variable {R' : Type*} [CommSemiring R'] [Algebra R' R] [Module R' M] [IsScalarTower R' R M]

/-- Apply a linear map on the output of a bilinear form. -/
@[simps!]
/-
**LinearMap.compBilinForm** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：compBilinForm (f : R ->ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M
参数：f : R ->ₗ[R'] R'；B : BilinForm R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a linear map on the output of a bilinear form.
-/
def compBilinForm (f : R →ₗ[R'] R') (B : BilinForm R M) : BilinForm R' M :=
  compr₂ (restrictScalars₁₂ R' R' B) f

end LinearMap

namespace LinearMap

namespace BilinForm

section Comp

variable {M' : Type w} [AddCommMonoid M'] [Module R M']

/-- Apply a linear map on the left and right argument of a bilinear form. -/
/-
**LinearMap.BilinForm.comp** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：comp (B : BilinForm R M') (l r : M ->ₗ[R] M') : BilinForm R M
参数：B : BilinForm R M'；l r : M ->ₗ[R] M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a linear map on the left and right argument of a bilinear form.
-/
def comp (B : BilinForm R M') (l r : M →ₗ[R] M') : BilinForm R M := B.compl₁₂ l r

/-- Apply a linear map to the left argument of a bilinear form. -/
/-
**LinearMap.BilinForm.compLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：compLeft (B : BilinForm R M) (f : M ->ₗ[R] M) : BilinForm R M
参数：B : BilinForm R M；f : M ->ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a linear map to the left argument of a bilinear form.
-/
def compLeft (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp f LinearMap.id

/-- Apply a linear map to the right argument of a bilinear form. -/
/-
**LinearMap.BilinForm.compRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：compRight (B : BilinForm R M) (f : M ->ₗ[R] M) : BilinForm R M
参数：B : BilinForm R M；f : M ->ₗ[R] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a linear map to the right argument of a bilinear form.
-/
def compRight (B : BilinForm R M) (f : M →ₗ[R] M) : BilinForm R M :=
  B.comp LinearMap.id f
/-
**LinearMap.BilinForm.comp_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：comp_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm 
R M'') (l r : M ->ₗ[R] M') (l' r' : M' ->ₗ[R] M'') : (B.comp l' r').comp l r = B
.comp (l'.comp l) (r'.comp r)
参数：B : BilinForm R M''；l r : M ->ₗ[R] M'；l' r' : M' ->ₗ[R] M''。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_comp {M'' : Type*} [AddCommMonoid M''] [Module R M''] (B : BilinForm R M'')
    (l r : M →ₗ[R] M') (l' r' : M' →ₗ[R] M'') :
    (B.comp l' r').comp l r = B.comp (l'.comp l) (r'.comp r) :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.compLeft_compRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：compLeft_compRight (B : BilinForm R M) (l r : M ->ₗ[R] M) : (B.compLeft l)
.compRight r = B.comp l r
参数：B : BilinForm R M；l r : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compLeft_compRight (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compLeft l).compRight r = B.comp l r :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.compRight_compLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：compRight_compLeft (B : BilinForm R M) (l r : M ->ₗ[R] M) : (B.compRight r
).compLeft l = B.comp l r
参数：B : BilinForm R M；l r : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRight_compLeft (B : BilinForm R M) (l r : M →ₗ[R] M) :
    (B.compRight r).compLeft l = B.comp l r :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：comp_apply (B : BilinForm R M') (l r : M ->ₗ[R] M') (v w) : B.comp l r v w
 = B (l v) (r w)
参数：B : BilinForm R M'；l r : M ->ₗ[R] M'；v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (B : BilinForm R M') (l r : M →ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w) :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.compLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：compLeft_apply (B : BilinForm R M) (f : M ->ₗ[R] M) (v w) : B.compLeft f v
 w = B (f v) w
参数：B : BilinForm R M；f : M ->ₗ[R] M；v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compLeft_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compLeft f v w = B (f v) w :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.compRight_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：compRight_apply (B : BilinForm R M) (f : M ->ₗ[R] M) (v w) : B.compRight f
 v w = B v (f w)
参数：B : BilinForm R M；f : M ->ₗ[R] M；v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem compRight_apply (B : BilinForm R M) (f : M →ₗ[R] M) (v w) : B.compRight f v w = B v (f w) :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.comp_id_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：comp_id_left (B : BilinForm R M) (r : M ->ₗ[R] M) : B.comp LinearMap.id r 
= B.compRight r
参数：B : BilinForm R M；r : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
-/
theorem comp_id_left (B : BilinForm R M) (r : M →ₗ[R] M) :
    B.comp LinearMap.id r = B.compRight r := by
  ext
  rfl

@[simp]
/-
**LinearMap.BilinForm.comp_id_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：comp_id_right (B : BilinForm R M) (l : M ->ₗ[R] M) : B.comp l LinearMap.id
 = B.compLeft l
参数：B : BilinForm R M；l : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
-/
theorem comp_id_right (B : BilinForm R M) (l : M →ₗ[R] M) :
    B.comp l LinearMap.id = B.compLeft l := by
  ext
  rfl

@[simp]
/-
**LinearMap.BilinForm.compLeft_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B
参数：B : BilinForm R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
-/
theorem compLeft_id (B : BilinForm R M) : B.compLeft LinearMap.id = B := by
  ext
  rfl

@[simp]
/-
**LinearMap.BilinForm.compRight_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B
参数：B : BilinForm R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
-/
theorem compRight_id (B : BilinForm R M) : B.compRight LinearMap.id = B := by
  ext
  rfl

-- Shortcut for `comp_id_{left,right}` followed by `comp{Right,Left}_id`,
-- Needs higher priority to be applied
@[simp high]
/-
**LinearMap.BilinForm.comp_id_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B
参数：B : BilinForm R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
-/
theorem comp_id_id (B : BilinForm R M) : B.comp LinearMap.id LinearMap.id = B := by
  ext
  rfl
/-
**LinearMap.BilinForm.comp_inj** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：comp_inj (B₁ B₂ : BilinForm R M') {l r : M ->ₗ[R] M'} (hₗ : Function.Surje
ctive l) (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂
参数：B₁ B₂ : BilinForm R M'；hₗ : Function.Surjective l；hᵣ : Function.Surjective r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.ext`：ext (H : forall x y : M, B x y = D x y) : B = D
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.comp_apply`：comp_apply (B : BilinForm R M') (l r : M
 ->ₗ[R] M') (v w) : B.comp l r v w = B (l v) (r w)
-/
theorem comp_inj (B₁ B₂ : BilinForm R M') {l r : M →ₗ[R] M'} (hₗ : Function.Surjective l)
    (hᵣ : Function.Surjective r) : B₁.comp l r = B₂.comp l r ↔ B₁ = B₂ := by
  constructor <;> intro h
  · -- B₁.comp l r = B₂.comp l r → B₁ = B₂
    ext x y
    obtain ⟨x', rfl⟩ := hₗ x
    obtain ⟨y', rfl⟩ := hᵣ y
    rw [← comp_apply, ← comp_apply, h]
  · -- B₁ = B₂ → B₁.comp l r = B₂.comp l r
    rw [h]

end Comp

variable {M' M'' : Type*}
variable [AddCommMonoid M'] [AddCommMonoid M''] [Module R M'] [Module R M'']

section congr

/-- Apply a linear equivalence on the arguments of a bilinear form. -/
/-
**LinearMap.BilinForm.congr** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：congr (e : M ≃ₗ[R] M') : BilinForm R M ≃ₗ[R] BilinForm R M'
参数：e : M ≃ₗ[R] M'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Apply a linear equivalence on the arguments of a bilinear form.
-/
def congr (e : M ≃ₗ[R] M') : BilinForm R M ≃ₗ[R] BilinForm R M' :=
  LinearEquiv.congrRight (LinearEquiv.congrLeft _ _ e) ≪≫ₗ LinearEquiv.congrLeft _ _ e

@[simp]
/-
**LinearMap.BilinForm.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：congr_apply (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M') : congr e B x 
y = B (e.symm x) (e.symm y)
参数：e : M ≃ₗ[R] M'；B : BilinForm R M；x y : M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem congr_apply (e : M ≃ₗ[R] M') (B : BilinForm R M) (x y : M') :
    congr e B x y = B (e.symm x) (e.symm y) :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：congr_symm (e : M ≃ₗ[R] M') : (congr e).symm = congr e.symm
参数：e : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem congr_symm (e : M ≃ₗ[R] M') : (congr e).symm = congr e.symm := by
  rfl

@[simp]
/-
**LinearMap.BilinForm.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：congr_refl : congr (LinearEquiv.refl R M) = LinearEquiv.refl R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
-/
theorem congr_refl : congr (LinearEquiv.refl R M) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => ext₂ fun _ _ => rfl
/-
**LinearMap.BilinForm.congr_trans** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：congr_trans (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'') : (congr e).trans (congr f
) = congr (e.trans f)
参数：e : M ≃ₗ[R] M'；f : M' ≃ₗ[R] M''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem congr_trans (e : M ≃ₗ[R] M') (f : M' ≃ₗ[R] M'') :
    (congr e).trans (congr f) = congr (e.trans f) :=
  rfl
/-
**LinearMap.BilinForm.congr_congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：congr_congr (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M) : cong
r e (congr f B) = congr (f.trans e) B
参数：e : M' ≃ₗ[R] M''；f : M ≃ₗ[R] M'；B : BilinForm R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem congr_congr (e : M' ≃ₗ[R] M'') (f : M ≃ₗ[R] M') (B : BilinForm R M) :
    congr e (congr f B) = congr (f.trans e) B :=
  rfl
/-
**LinearMap.BilinForm.congr_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：congr_comp (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' ->ₗ[R] M') : (c
ongr e B).comp l r = B.comp (LinearMap.comp (e.symm : M' ->ₗ[R] M) l) (LinearMap
.comp (e.symm : M' ->ₗ[R] M) r)
参数：e : M ≃ₗ[R] M'；B : BilinForm R M；l r : M'' ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem congr_comp (e : M ≃ₗ[R] M') (B : BilinForm R M) (l r : M'' →ₗ[R] M') :
    (congr e B).comp l r =
      B.comp (LinearMap.comp (e.symm : M' →ₗ[R] M) l)
        (LinearMap.comp (e.symm : M' →ₗ[R] M) r) :=
  rfl
/-
**LinearMap.BilinForm.comp_congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：comp_congr (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' ->ₗ[R] M) : co
ngr e (B.comp l r) = B.comp (l.comp (e.symm : M'' ->ₗ[R] M')) (r.comp (e.symm : 
M'' ->ₗ[R] M'))
参数：e : M' ≃ₗ[R] M''；B : BilinForm R M；l r : M' ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem comp_congr (e : M' ≃ₗ[R] M'') (B : BilinForm R M) (l r : M' →ₗ[R] M) :
    congr e (B.comp l r) =
      B.comp (l.comp (e.symm : M'' →ₗ[R] M')) (r.comp (e.symm : M'' →ₗ[R] M')) :=
  rfl

end congr

section congrRight₂

variable {N₁ N₂ N₃ : Type*}
variable [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N₃]
variable [Module R N₁] [Module R N₂] [Module R N₃]

/-- When `N₁` and `N₂` are equivalent, bilinear maps on `M` into `N₁` are equivalent to bilinear
maps into `N₂`. -/
/-
**LinearMap.BilinForm._root_.LinearEquiv.congrRight** 是 Mathlib 中的一个定义，位于命名空间 `L
inearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `N₁` and `N₂` are equivalent, bilinear maps on `M` into `N₁` are equivalent
 to bilinear
maps into `N₂`.
-/
def _root_.LinearEquiv.congrRight₂ (e : N₁ ≃ₗ[R] N₂) : BilinMap R M N₁ ≃ₗ[R] BilinMap R M N₂ :=
  LinearEquiv.congrRight (LinearEquiv.congrRight e)

@[simp]
/-
**LinearMap.BilinForm._root_.LinearEquiv.congrRight** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrRight₂_apply (e : N₁ ≃ₗ[R] N₂) (B : BilinMap R M N₁) :
    LinearEquiv.congrRight₂ e B = compr₂ B e := rfl

@[simp]
/-
**LinearMap.BilinForm._root_.LinearEquiv.congrRight** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrRight₂_refl :
    LinearEquiv.congrRight₂ (.refl R N₁) = .refl R (BilinMap R M N₁) := rfl

@[simp]
/-
**LinearMap.BilinForm._root_.LinearEquiv.congrRight_symm** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrRight_symm (e : N₁ ≃ₗ[R] N₂) :
    (LinearEquiv.congrRight₂ e (M := M)).symm = LinearEquiv.congrRight₂ e.symm :=
  rfl
/-
**LinearMap.BilinForm._root_.LinearEquiv.congrRight** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrRight₂_trans (e₁₂ : N₁ ≃ₗ[R] N₂) (e₂₃ : N₂ ≃ₗ[R] N₃) :
    LinearEquiv.congrRight₂ (M := M) (e₁₂ ≪≫ₗ e₂₃) =
    LinearEquiv.congrRight₂ e₁₂ ≪≫ₗ LinearEquiv.congrRight₂ e₂₃ :=
  rfl

end congrRight₂

section LinMulLin

/-- `linMulLin f g` is the bilinear form mapping `x` and `y` to `f x * g y` -/
/-
**LinearMap.BilinForm.linMulLin** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：linMulLin (f g : M ->ₗ[R] R) : BilinForm R M
参数：f g : M ->ₗ[R] R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`linMulLin f g` is the bilinear form mapping `x` and `y` to `f x * g y`
-/
def linMulLin (f g : M →ₗ[R] R) : BilinForm R M := (LinearMap.mul R R).compl₁₂ f g

variable {f g : M →ₗ[R] R}

@[simp]
/-
**LinearMap.BilinForm.linMulLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bilin
Form`。
形式化陈述：linMulLin_apply (x y) : linMulLin f g x y = f x * g y
参数：x y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_apply (x y) : linMulLin f g x y = f x * g y :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.linMulLin_comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：linMulLin_comp (l r : M' ->ₗ[R] M) : (linMulLin f g).comp l r = linMulLin 
(f.comp l) (g.comp r)
参数：l r : M' ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_comp (l r : M' →ₗ[R] M) :
    (linMulLin f g).comp l r = linMulLin (f.comp l) (g.comp r) :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.linMulLin_compLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：linMulLin_compLeft (l : M ->ₗ[R] M) : (linMulLin f g).compLeft l = linMulL
in (f.comp l) g
参数：l : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_compLeft (l : M →ₗ[R] M) :
    (linMulLin f g).compLeft l = linMulLin (f.comp l) g :=
  rfl

@[simp]
/-
**LinearMap.BilinForm.linMulLin_compRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：linMulLin_compRight (r : M ->ₗ[R] M) : (linMulLin f g).compRight r = linMu
lLin f (g.comp r)
参数：r : M ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_compRight (r : M →ₗ[R] M) :
    (linMulLin f g).compRight r = linMulLin f (g.comp r) :=
  rfl

end LinMulLin

section Basis

variable {F₂ : BilinForm R M}
variable {ι : Type*} (b : Basis ι R M)

/-- Two bilinear forms are equal when they are equal on all basis vectors. -/
/-
**LinearMap.BilinForm.ext_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：ext_basis (h : forall i j, B (b i) (b j) = F₂ (b i) (b j)) : B = F₂
参数：h : forall i j, B (b i) (b j) = F₂ (b i) (b j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.ext`：ext {f₁ f₂ : M ->ₛₗ[σ] M₁} (h : forall i, f₁ (b i) = f
₂ (b i)) : f₁ = f₂

--- 原说明 ---
Two bilinear forms are equal when they are equal on all basis vectors.
-/
theorem ext_basis (h : ∀ i j, B (b i) (b j) = F₂ (b i) (b j)) : B = F₂ :=
  b.ext fun i => b.ext fun j => h i j

/-- Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis. -/
/-
**LinearMap.BilinForm.sum_repr_mul_repr_mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：sum_repr_mul_repr_mul (x y : M) : ((b.repr x).sum fun i xi => (b.repr y).s
um fun j yj => xi • yj • B (b i) (b j)) = B x y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.linearCombination_repr`：linearCombination_repr : Finsupp.li
nearCombination _ b (b.repr x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.BilinForm.sum_left`：sum_left {α} (t : Finset α) (g : α -> M) (
w : M) : B (∑ i in t, g i) w = ∑ i in t, B (g i) w
· 使用定理 `LinearMap.BilinForm.sum_right`：sum_right {α} (t : Finset α) (w : M) (g :
 α -> M) : B w (∑ i in t, g i) = ∑ i in t, B w (g i)
· 使用定理 `LinearMap.BilinForm.smul_left`：smul_left (a : R) (x y : M) : B (a • x) y
 = a * B x y
· 使用定理 `LinearMap.BilinForm.smul_right`：smul_right (a : R) (x y : M) : B x (a • 
y) = a * B x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Write out `B x y` as a sum over `B (b i) (b j)` if `b` is a basis.
-/
theorem sum_repr_mul_repr_mul (x y : M) :
    ((b.repr x).sum fun i xi => (b.repr y).sum fun j yj => xi • yj • B (b i) (b j)) = B x y := by
  conv_rhs => rw [← b.linearCombination_repr x, ← b.linearCombination_repr y]
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_left, sum_right, smul_left, smul_right,
    smul_eq_mul]

end Basis

end BilinForm

end LinearMap

