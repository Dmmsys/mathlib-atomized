/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kexing Ying
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal

/-!
# Bilinear form

This file defines orthogonal bilinear forms.

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
open Module

universe u v w

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁}

namespace LinearMap

namespace BilinForm

/-- The proposition that two elements of a bilinear form space are orthogonal. For orthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`. -/
@[deprecated "Use `B x y = 0`." (since := "2026-03-30")]
/-
**LinearMap.BilinForm.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：IsOrtho (B : BilinForm R M) (x y : M) : Prop
参数：B : BilinForm R M；x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that two elements of a bilinear form space are orthogonal. For o
rthogonality
of an indexed set of elements, use `BilinForm.iIsOrtho`.
-/
def IsOrtho (B : BilinForm R M) (x y : M) : Prop :=
  B x y = 0

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.BilinForm.isOrtho_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinForm
`。
形式化陈述：isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOrtho_def {B : BilinForm R M} {x y : M} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.BilinForm.isOrtho_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isOrtho_zero_left`：isOrtho_zero_left (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[
I₂] M) (x) : IsOrtho B (0 : M₁) x
-/
theorem isOrtho_zero_left (x : M) : IsOrtho B (0 : M) x := LinearMap.isOrtho_zero_left B x

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.BilinForm.isOrtho_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：isOrtho_zero_right (x : M) : IsOrtho B x (0 : M)
参数：x : M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.zero_right`：zero_right (x : M) : B x 0 = 0
-/
theorem isOrtho_zero_right (x : M) : IsOrtho B x (0 : M) :=
  zero_right x
/-
**LinearMap.BilinForm.ne_zero_of_not_isOrtho_self** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.BilinForm`。
形式化陈述：ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : B x x != 0)
 : x != 0
参数：x : V；hx₁ : B x x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
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
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem ne_zero_of_not_isOrtho_self {B : BilinForm K V} (x : V) (hx₁ : B x x ≠ 0) : x ≠ 0 := by
  by_contra; simp [this] at hx₁
/-
**LinearMap.BilinForm.IsRefl.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm.IsRefl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B : LinearMap.BilinForm R M}, B.IsRefl 
→ ∀ {x y : M}, (B x) y = 0 ↔ (B y) x = 0
参数：B x；B y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.IsRefl.eq_zero`：eq_zero (H : B.IsRefl) : forall {x y
 : M}, B x y = 0 -> B y x = 0
-/
theorem IsRefl.eq_iff (H : B.IsRefl) {x y : M} : B x y = 0 ↔ B y x = 0 :=
  ⟨eq_zero H, eq_zero H⟩

@[deprecated (since := "2026-03-31")]
alias IsRefl.ortho_comm := IsRefl.eq_iff
/-
**LinearMap.BilinForm.IsAlt.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m.IsAlt`。
形式化陈述：∀ {R₁ : Type u_3} {M₁ : Type u_4} [inst : CommRing R₁] [inst_1 : AddCommGr
oup M₁] [inst_2 : _root_.Module R₁ M₁]   {B₁ : LinearMap.BilinForm R₁ M₁}, B₁.Is
Alt → ∀ {x y : M₁}, (B₁ x) y = 0 ↔ (B₁ y) x = 0
参数：B₁ x；B₁ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.eq_iff`：eq_iff (H : B.IsAlt) {x y} : B x y = 0 ↔ B y x =
 0
-/
theorem IsAlt.eq_iff (H : B₁.IsAlt) {x y : M₁} : B₁ x y = 0 ↔ B₁ y x = 0 :=
  LinearMap.IsAlt.eq_iff H

@[deprecated (since := "2026-03-31")]
alias IsAlt.ortho_comm := IsAlt.eq_iff
/-
**LinearMap.BilinForm.IsSymm.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm.IsSymm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B : LinearMap.BilinForm R M}, B.IsSymm 
→ ∀ {x y : M}, (B x) y = 0 ↔ (B y) x = 0
参数：B x；B y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsSymm.eq_iff`：eq_iff (H : B.IsSymm) {x y} : B x y = 0 ↔ B y x
 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.BilinForm.isSymm_iff`：isSymm_iff : IsSymm B ↔ LinearMap.IsSymm
 B
-/
theorem IsSymm.eq_iff (H : B.IsSymm) {x y : M} : B x y = 0 ↔ B y x = 0 :=
  LinearMap.IsSymm.eq_iff (isSymm_iff.1 H)

@[deprecated (since := "2026-03-31")]
alias IsSymm.ortho_comm := IsSymm.eq_iff

/-- A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. -/
/-
**LinearMap.BilinForm.iIsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：iIsOrtho {n : Type w} (B : BilinForm R M) (v : n -> M) : Prop
参数：B : BilinForm R M；v : n -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of vectors `v` is orthogonal with respect to some bilinear form `B` if and
 only
if for all `i ≠ j`, `B (v i) (v j) = 0`.
-/
def iIsOrtho {n : Type w} (B : BilinForm R M) (v : n → M) : Prop :=
  B.IsOrthoᵢ v
/-
**LinearMap.BilinForm.iIsOrtho_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFor
m`。
形式化陈述：iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n -> M} : B.iIsOrtho v 
↔ forall i j : n, i != j -> B (v i) (v j) = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iIsOrtho_def {n : Type w} {B : BilinForm R M} {v : n → M} :
    B.iIsOrtho v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl

section

variable {R₄ M₄ : Type*} [CommRing R₄] [IsDomain R₄]
variable [AddCommGroup M₄] [Module R₄ M₄] {G : BilinForm R₄ M₄}

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.BilinForm.isOrtho_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a != 0) : IsOrtho G (a • x) y 
↔ IsOrtho G x y
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem isOrtho_smul_left {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G (a • x) y ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [LinearMap.smul_apply, smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim

@[deprecated "`BilinMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.BilinForm.isOrtho_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a != 0) : IsOrtho G x (a • y)
 ↔ IsOrtho G x y
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
-/
theorem isOrtho_smul_right {x y : M₄} {a : R₄} (ha : a ≠ 0) :
    IsOrtho G x (a • y) ↔ IsOrtho G x y := by
  dsimp only [IsOrtho]
  rw [map_smul]
  simp only [smul_eq_mul, mul_eq_zero, or_iff_right_iff_imp]
  exact fun a ↦ (ha a).elim

/-- A set of orthogonal vectors `v` with respect to some bilinear form `B` is linearly independent
  if for all `i`, `B (v i) (v i) ≠ 0`. -/
/-
**LinearMap.BilinForm.linearIndependent_of_iIsOrtho** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n -> V
} (hv₁ : B.iIsOrtho v) (hv₂ : forall i, B (v i) (v i) != 0) : LinearIndependent 
K v
参数：hv₁ : B.iIsOrtho v；hv₂ : forall i, B (v i) (v i) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `LinearMap.BilinForm.zero_left`：zero_left (x : M) : B 0 x = 0
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.BilinForm.iIsOrtho_def`：iIsOrtho_def {n : Type w} {B : BilinFo
rm R M} {v : n -> M} : B.iIsOrtho v ↔ forall i j : n, i != j -> B (v i) (v j) = 
0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_zero_of_ne_zero_of_mul_right_eq_zero`：eq_zero_of_ne_zero_of_mul_right
_eq_zero (hx : x != 0) (hxy : y * x = 0) : y = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.BilinForm.smul_left`：smul_left (a : R) (x y : M) : B (a • x) y
 = a * B x y
· 使用定理 `LinearMap.BilinForm.sum_left`：sum_left {α} (t : Finset α) (g : α -> M) (
w : M) : B (∑ i in t, g i) w = ∑ i in t, B (g i) w

--- 原说明 ---
A set of orthogonal vectors `v` with respect to some bilinear form `B` is linear
ly independent
  if for all `i`, `B (v i) (v i) ≠ 0`.
-/
theorem linearIndependent_of_iIsOrtho {n : Type w} {B : BilinForm K V} {v : n → V}
    (hv₁ : B.iIsOrtho v) (hv₂ : ∀ i, B (v i) (v i) ≠ 0) : LinearIndependent K v := by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n => w i • v i) (v i) = 0 := by rw [hs, zero_left]
  have hsum : (s.sum fun j : n => w j * B (v j) (v i)) = w i * B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _ hij
    rw [iIsOrtho_def.1 hv₁ _ _ hij, mul_zero]
  simp_rw [sum_left, smul_left, hsum] at this
  exact eq_zero_of_ne_zero_of_mul_right_eq_zero (hv₂ i) this

end

section Orthogonal

/-- The orthogonal complement of a submodule `N` with respect to some bilinear form is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B y x = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this definition has a
chirality; in addition to this "right" orthogonal complement one could define a "left" orthogonal
complement for which, for all `y` in `N`, `B x y = 0`.  This variant definition is not currently
provided in mathlib. -/
/-
**LinearMap.BilinForm.orthogonal** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinForm`
。
形式化陈述：orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M
参数：B : BilinForm R M；N : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of a submodule `N` with respect to some bilinear form 
is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `
N`, `B y x = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear forms this 
definition has a
chirality; in addition to this "right" orthogonal complement one could define a 
"left" orthogonal
complement for which, for all `y` in `N`, `B x y = 0`.  This variant definition 
is not currently
provided in mathlib.
-/
def orthogonal (B : BilinForm R M) (N : Submodule R M) : Submodule R M := N.orthogonalBilin B

variable {N L : Submodule R M}

@[simp]
/-
**LinearMap.BilinForm.mem_orthogonal_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：mem_orthogonal_iff {N : Submodule R M} {m : M} : m in B.orthogonal N ↔ for
all n in N, B n m = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_orthogonal_iff {N : Submodule R M} {m : M} :
    m ∈ B.orthogonal N ↔ ∀ n ∈ N, B n m = 0 :=
  Iff.rfl
/-
**LinearMap.BilinForm.orthogonal_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinF
orm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {B : LinearMap.BilinForm R M}, B.orthogo
nal ⊥ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma orthogonal_bot : B.orthogonal ⊥ = ⊤ := by ext; simp
/-
**LinearMap.BilinForm.orthogonal_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.BilinFo
rm`。
形式化陈述：orthogonal_le (h : N <= L) : B.orthogonal L <= B.orthogonal N
参数：h : N <= L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orthogonal_le (h : N ≤ L) : B.orthogonal L ≤ B.orthogonal N := fun _ hn l hl => hn l (h hl)
/-
**LinearMap.BilinForm.le_orthogonal_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinForm`。
形式化陈述：le_orthogonal_orthogonal (b : B.IsRefl) : N <= B.orthogonal (B.orthogonal 
N)
参数：b : B.IsRefl。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_orthogonal_orthogonal (b : B.IsRefl) : N ≤ B.orthogonal (B.orthogonal N) :=
  fun n hn _ hm => b _ _ (hm n hn)
/-
**LinearMap.BilinForm.orthogonal_top_eq_ker** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：orthogonal_top_eq_ker (hB : B.IsRefl) : B.orthogonal ⊤ = LinearMap.ker B
参数：hB : B.IsRefl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearMap.BilinForm.IsRefl.eq_iff`：∀ {R : Type u_1} {M : Type u_2} [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B 
: LinearMap.BilinForm R…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma orthogonal_top_eq_ker (hB : B.IsRefl) :
    B.orthogonal ⊤ = LinearMap.ker B := by
  ext; simp [LinearMap.ext_iff, hB.eq_iff]
/-
**LinearMap.BilinForm.orthogonal_top_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：orthogonal_top_eq_bot (hB : B.Nondegenerate) : B.orthogonal ⊤ = ⊥
参数：hB : B.Nondegenerate。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma orthogonal_top_eq_bot (hB : B.Nondegenerate) :
    B.orthogonal ⊤ = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun x hx ↦ hB.2 x (by simpa using! hx)

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
/-
**LinearMap.BilinForm.span_singleton_inf_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.BilinForm`。
形式化陈述：span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : B x
 x != 0) : K ∙ x ⊓ B.orthogonal (K ∙ x) = ⊥
参数：hx : B x x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.span_singleton_inf_orthogonal_eq_bot`：span_singleton_inf_ortho
gonal_eq_bot (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x : V₁) (hx : B x x != 0) : (K₁ 
∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = …
-/
theorem span_singleton_inf_orthogonal_eq_bot {B : BilinForm K V} {x : V} (hx : B x x ≠ 0) :
    K ∙ x ⊓ B.orthogonal (K ∙ x) = ⊥ :=
  LinearMap.span_singleton_inf_orthogonal_eq_bot B _ hx

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
/-
**LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap.BilinForm`。
形式化陈述：orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) : B.ort
hogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x)
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.orthogonal_span_singleton_eq_to_lin_ker`：orthogonal_span_singl
eton_eq_to_lin_ker {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V) : (K ∙ x).orthogonalBilin
 B = LinearMap.ker (B x)
-/
theorem orthogonal_span_singleton_eq_toLin_ker {B : BilinForm K V} (x : V) :
    B.orthogonal (K ∙ x) = LinearMap.ker (LinearMap.BilinForm.toLinHomAux₁ B x) :=
  LinearMap.orthogonal_span_singleton_eq_to_lin_ker ..
/-
**LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.BilinForm`。
形式化陈述：span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : B x
 x != 0) : K ∙ x ⊔ B.orthogonal (K ∙ x) = ⊤
参数：hx : B x x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.span_singleton_sup_orthogonal_eq_top`：span_singleton_sup_ortho
gonal_eq_top {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) : (K ∙ x) ⊔ (K 
∙ x).orthogonalBilin B = ⊤
-/
theorem span_singleton_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : B x x ≠ 0) :
    K ∙ x ⊔ B.orthogonal (K ∙ x) = ⊤ :=
  LinearMap.span_singleton_sup_orthogonal_eq_top hx

/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
/-
**LinearMap.BilinForm.isCompl_span_singleton_orthogonal** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap.BilinForm`。
形式化陈述：isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : B x x 
!= 0) : IsCompl (K ∙ x) (B.orthogonal <| K ∙ x)
参数：hx : B x x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isCompl_span_singleton_orthogonal`：isCompl_span_singleton_orth
ogonal {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) : IsCompl (K ∙ x) ((K
 ∙ x).orthogonalBilin B)

--- 原说明 ---
Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the si
ngleton of `x`
  is complement to its orthogonal complement.
-/
theorem isCompl_span_singleton_orthogonal {B : BilinForm K V} {x : V} (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) (B.orthogonal <| K ∙ x) :=
  LinearMap.isCompl_span_singleton_orthogonal hx

end Orthogonal

variable {M₂' : Type*}
variable [AddCommMonoid M₂'] [Module R M₂']

/-- The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `Disjoint W (B.orthogonal W)`. -/
/-
**LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal** 是 Mathlib 
中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B
.IsRefl) {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict 
W).Nondegenerate
参数：B : BilinForm R₁ M₁；b : B.IsRefl；hW : Disjoint W (B.orthogonal W)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.nondegenerate_restrict_of_disjoint_orthogonal`：nondegenerate_r
estrict_of_disjoint_orthogonal {B : M ->ₗ[R] M ->ₗ[R] M₁} (hB : B.IsRefl) {W : S
ubmodule R M} (hW : Disjoint W (W.orthogonalB…

--- 原说明 ---
The restriction of a reflexive bilinear form `B` onto a submodule `W` is
nondegenerate if `Disjoint W (B.orthogonal W)`.
-/
theorem nondegenerate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl)
    {W : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) : (B.restrict W).Nondegenerate :=
  LinearMap.nondegenerate_restrict_of_disjoint_orthogonal b hW

/-- An orthogonal basis with respect to a nondegenerate bilinear form has no self-orthogonal
elements. -/
/-
**LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate** 是 Mathl
ib 中的一个定理，位于命名空间 `LinearMap.BilinForm.iIsOrtho`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {n : Type w} [Nontrivial R] {B : LinearM
ap.BilinForm R M} {v : Module.Basis n R M},   B.iIsOrtho ⇑v → B.Nondegenerate → 
∀ (i : n), (B (v i)) (v i) ≠ 0
参数：i : n；B (v i)；v i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft`：∀ {n : Type
 u_19} {R : Type u_20} {M : Type u_21} {M₁ : Type u_22} [inst : CommSemiring R] 
[inst_1 : AddCommMonoid M]   [inst_2 : AddCommMon…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
An orthogonal basis with respect to a nondegenerate bilinear form has no self-or
thogonal
elements.
-/
theorem iIsOrtho.not_isOrtho_basis_self_of_nondegenerate {n : Type w} [Nontrivial R]
    {B : BilinForm R M} {v : Basis n R M} (h : B.iIsOrtho v) (hB : B.Nondegenerate) (i : n) :
    B (v i) (v i) ≠ 0 :=
  h.not_isOrtho_basis_self_of_separatingLeft hB.1 i

/-- Given an orthogonal basis with respect to a bilinear form, the bilinear form is nondegenerate
iff the basis has no elements which are self-orthogonal. -/
/-
**LinearMap.BilinForm.iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self** 是 Math
lib 中的一个定理，位于命名空间 `LinearMap.BilinForm.iIsOrtho`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {n : Type w} [IsDomain R] (B : LinearMap
.BilinForm R M) (v : Module.Basis n R M),   B.iIsOrtho ⇑v → (B.Nondegenerate ↔ ∀
 (i : n), (B (v i)) (v i) ≠ 0)
参数：B : LinearMap.BilinForm R M；v : Module.Basis n R M；B.Nondegenerate ↔ ∀ (i : n
), (B (v i)) (v i) ≠ 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.iIsOrtho.not_isOrtho_basis_self_of_nondegenerate`：∀ 
{R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M]   {n : Type w} [Nontrivial R…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `LinearMap.IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self`：∀ {n : Type 
u_19} {R : Type u_20} {M : Type u_21} {M₁ : Type u_22} [inst : CommSemiring R] [
inst_1 : AddCommMonoid M]   [inst_2 : AddCommMon…
· 使用定理 `instIsTorsionFree`：∀ {R : Type u_1} [inst : Semiring R], Module.IsTorsio
nFree R R

--- 原说明 ---
Given an orthogonal basis with respect to a bilinear form, the bilinear form is 
nondegenerate
iff the basis has no elements which are self-orthogonal.
-/
theorem iIsOrtho.nondegenerate_iff_not_isOrtho_basis_self {n : Type w} [IsDomain R]
    (B : BilinForm R M) (v : Basis n R M) (hO : B.iIsOrtho v) :
    B.Nondegenerate ↔ ∀ i, B (v i) (v i) ≠ 0 :=
  ⟨hO.not_isOrtho_basis_self_of_nondegenerate, hO.nondegenerate_of_not_isOrtho_basis_self _⟩

section

/-
**LinearMap.BilinForm.toLin_restrict_ker_eq_inf_ker** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：toLin_restrict_ker_eq_inf_ker (B : BilinForm K V) (W : Subspace K V) : (Li
nearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.ker
参数：B : BilinForm K V；W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem toLin_restrict_ker_eq_inf_ker (B : BilinForm K V) (W : Subspace K V) :
    (LinearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.ker := by
  ext x; constructor <;> intro hx
  · rcases hx with ⟨⟨x, hx⟩, hker, rfl⟩
    constructor
    · simp [hx]
    · simpa
  · simp_rw [Submodule.mem_map, LinearMap.mem_ker]
    exact ⟨⟨x, hx.1⟩, hx.right, rfl⟩
/-
**LinearMap.BilinForm.toLin_restrict_ker_eq_inf_orthogonal** 是 Mathlib 中的一个定理，位于
命名空间 `LinearMap.BilinForm`。
形式化陈述：toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V
) (b : B.IsRefl) : (LinearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.orth
ogonal ⊤
参数：B : BilinForm K V；W : Subspace K V；b : B.IsRefl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.orthogonal_top_eq_ker`：orthogonal_top_eq_ker (hB : B
.IsRefl) : B.orthogonal ⊤ = LinearMap.ker B
· 使用定理 `LinearMap.BilinForm.toLin_restrict_ker_eq_inf_ker`：toLin_restrict_ker_eq
_inf_ker (B : BilinForm K V) (W : Subspace K V) : (LinearMap.ker <| B.domRestric
t W).map W.subtype = W ⊓ B.ker
-/
theorem toLin_restrict_ker_eq_inf_orthogonal (B : BilinForm K V) (W : Subspace K V) (b : B.IsRefl) :
    (LinearMap.ker <| B.domRestrict W).map W.subtype = W ⊓ B.orthogonal ⊤ := by
  rw [orthogonal_top_eq_ker b]
  exact toLin_restrict_ker_eq_inf_ker ..
/-
**LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal** 是 M
athlib 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V) (
W : Subspace K V) : (LinearMap.range (B.domRestrict W)).dualCoannihilator = B.or
thogonal W
参数：B : BilinForm K V；W : Subspace K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.mem_orthogonal_iff`：mem_orthogonal_iff {N : Submodul
e R M} {m : M} : m in B.orthogonal N ↔ forall n in N, B n m = 0
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.mem_dualCoannihilator`：mem_dualCoannihilator {Φ : Submodule R 
(Module.Dual R M)} (x : M) : x in Φ.dualCoannihilator ↔ forall φ in Φ, (φ x : R)
 = 0
-/
theorem toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V)
    (W : Subspace K V) :
    (LinearMap.range (B.domRestrict W)).dualCoannihilator = B.orthogonal W := by
  ext x; constructor <;> rw [mem_orthogonal_iff] <;> intro hx
  · intro y hy
    rw [Submodule.mem_dualCoannihilator] at hx
    exact hx (B.domRestrict W ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
  · rw [Submodule.mem_dualCoannihilator]
    rintro _ ⟨⟨w, hw⟩, rfl⟩
    exact hx w hw
/-
**LinearMap.BilinForm.ker_restrict_eq_of_codisjoint** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：ker_restrict_eq_of_codisjoint {p q : Submodule R M} (hpq : Codisjoint p q)
 {B : LinearMap.BilinForm R M} (hB : forall x in p, forall y in q, B x y = 0) : 
LinearMap.ker (B.restrict p) = (LinearMap.ker B).comap p.subtype
参数：hpq : Codisjoint p q；hB : forall x in p, forall y in q, B x y = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.codisjoint_iff_exists_add_eq`：codisjoint_iff_exists_add_eq : C
odisjoint p p' ↔ forall z, exists x y, x in p ∧ y in p' ∧ x + y = z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearMap.BilinForm.restrict_apply`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (B
 : LinearMap.BilinForm R…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
lemma ker_restrict_eq_of_codisjoint {p q : Submodule R M} (hpq : Codisjoint p q)
    {B : LinearMap.BilinForm R M} (hB : ∀ x ∈ p, ∀ y ∈ q, B x y = 0) :
    LinearMap.ker (B.restrict p) = (LinearMap.ker B).comap p.subtype := by
  ext ⟨z, hz⟩
  simp only [LinearMap.mem_ker, Submodule.mem_comap, Submodule.coe_subtype]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · ext w
    obtain ⟨x, y, hx, hy, rfl⟩ := Submodule.codisjoint_iff_exists_add_eq.mp hpq w
    simpa [hB z hz y hy] using LinearMap.congr_fun h ⟨x, hx⟩
  · ext ⟨x, hx⟩
    simpa using LinearMap.congr_fun h x
/-
**LinearMap.BilinForm.inf_orthogonal_self_le_ker_restrict** 是 Mathlib 中的一个引理，位于命
名空间 `LinearMap.BilinForm`。
形式化陈述：inf_orthogonal_self_le_ker_restrict {W : Submodule R M} (b₁ : B.IsRefl) : 
W ⊓ B.orthogonal W <= (LinearMap.ker <| B.restrict W).map W.subtype
参数：b₁ : B.IsRefl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.BilinForm.restrict_apply`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (B
 : LinearMap.BilinForm R…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma inf_orthogonal_self_le_ker_restrict {W : Submodule R M} (b₁ : B.IsRefl) :
    W ⊓ B.orthogonal W ≤ (LinearMap.ker <| B.restrict W).map W.subtype := by
  rintro v ⟨hv : v ∈ W, hv' : v ∈ B.orthogonal W⟩
  simp only [Submodule.mem_map, mem_ker, restrict_apply, Submodule.coe_subtype, Subtype.exists,
    exists_and_left, exists_prop, exists_eq_right_right]
  refine ⟨?_, hv⟩
  ext ⟨w, hw⟩
  exact b₁ w v <| hv' w hw

variable [FiniteDimensional K V]

open Module Submodule

variable {B : BilinForm K V}
/-
**LinearMap.BilinForm.finrank_add_finrank_orthogonal'** 是 Mathlib 中的一个定理，位于命名空间 
`LinearMap.BilinForm`。
形式化陈述：finrank_add_finrank_orthogonal' (W : Submodule K V) : finrank K W + finran
k K (B.orthogonal W) = finrank K V + finrank K (W ⊓ B.ker : Subspace K V)
参数：W : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.toLin_restrict_ker_eq_inf_ker`：toLin_restrict_ker_eq
_inf_ker (B : BilinForm K V) (W : Subspace K V) : (LinearMap.ker <| B.domRestric
t W).map W.subtype = W ⊓ B.ker
· 使用定理 `LinearMap.BilinForm.toLin_restrict_range_dualCoannihilator_eq_orthogonal
`：toLin_restrict_range_dualCoannihilator_eq_orthogonal (B : BilinForm K V) (W : 
Subspace K V) : (LinearMap.range (B.domRestrict W)).dualCoanni…
· 使用定理 `Submodule.finrank_map_subtype_eq`：Submodule.finrank_map_subtype_eq (p : 
Submodule R M) (q : Submodule R p) : finrank R (q.map p.subtype) = finrank R q
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subspace.finrank_add_finrank_dualCoannihilator_eq`：finrank_add_finrank_d
ualCoannihilator_eq (W : Subspace K (Module.Dual K V)) : finrank K W + finrank K
 W.dualCoannihilator = finrank K V
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
-/
theorem finrank_add_finrank_orthogonal' (W : Submodule K V) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.ker : Subspace K V) := by
  rw [← toLin_restrict_ker_eq_inf_ker _ _, ←
    toLin_restrict_range_dualCoannihilator_eq_orthogonal _ _, finrank_map_subtype_eq]
  conv_rhs =>
    rw [← @Subspace.finrank_add_finrank_dualCoannihilator_eq K V _ _ _ _
        (LinearMap.range (B.domRestrict W)),
      add_comm, ← add_assoc, add_comm (finrank K (LinearMap.ker (B.domRestrict W))),
      LinearMap.finrank_range_add_finrank_ker]
/-
**LinearMap.BilinForm.finrank_add_finrank_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.BilinForm`。
形式化陈述：finrank_add_finrank_orthogonal (b₁ : B.IsRefl) (W : Submodule K V) : finra
nk K W + finrank K (B.orthogonal W) = finrank K V + finrank K (W ⊓ B.orthogonal 
⊤ : Subspace K V)
参数：b₁ : B.IsRefl；W : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.orthogonal_top_eq_ker`：orthogonal_top_eq_ker (hB : B
.IsRefl) : B.orthogonal ⊤ = LinearMap.ker B
· 使用定理 `LinearMap.BilinForm.finrank_add_finrank_orthogonal'`：finrank_add_finrank
_orthogonal' (W : Submodule K V) : finrank K W + finrank K (B.orthogonal W) = fi
nrank K V + finrank K (W ⊓ B.ker : Subspa…
-/
theorem finrank_add_finrank_orthogonal (b₁ : B.IsRefl) (W : Submodule K V) :
    finrank K W + finrank K (B.orthogonal W) =
      finrank K V + finrank K (W ⊓ B.orthogonal ⊤ : Subspace K V) := by
  rw [orthogonal_top_eq_ker b₁]
  exact finrank_add_finrank_orthogonal' _
/-
**LinearMap.BilinForm.finrank_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：finrank_orthogonal (hB : B.Nondegenerate) (W : Submodule K V) : finrank K 
(B.orthogonal W) = finrank K V - finrank K W
参数：hB : B.Nondegenerate；W : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.finrank_add_finrank_orthogonal'`：finrank_add_finrank
_orthogonal' (W : Submodule K V) : finrank K W + finrank K (B.orthogonal W) = fi
nrank K V + finrank K (W ⊓ B.ker : Subspa…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `inf_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderBo
t α] (a : α), a ⊓ ⊥ = ⊥
· 使用定理 `LinearMap.BilinForm.Nondegenerate.ker_eq_bot`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {B : LinearMap.BilinForm R…
-/
lemma finrank_orthogonal (hB : B.Nondegenerate) (W : Submodule K V) :
    finrank K (B.orthogonal W) = finrank K V - finrank K W := by
  have := finrank_add_finrank_orthogonal' (B := B) W
  rw [hB.ker_eq_bot, inf_bot_eq, finrank_bot, add_zero] at this
  lia
/-
**LinearMap.BilinForm.orthogonal_orthogonal** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：orthogonal_orthogonal (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodu
le K V) : B.orthogonal (B.orthogonal W) = W
参数：hB : B.Nondegenerate；hB₀ : B.IsRefl；W : Submodule K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.eq_of_le_of_finrank_le`：eq_of_le_of_finrank_le {S₁ S₂ : Submod
ule K V} [FiniteDimensional K S₂] (hle : S₁ <= S₂) (hd : finrank K S₂ <= finrank
 K S₁) : S₁ = S₂
· 使用定理 `LinearMap.BilinForm.le_orthogonal_orthogonal`：le_orthogonal_orthogonal (
b : B.IsRefl) : N <= B.orthogonal (B.orthogonal N)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LinearMap.BilinForm.finrank_orthogonal`：finrank_orthogonal (hB : B.Nonde
generate) (W : Submodule K V) : finrank K (B.orthogonal W) = finrank K V - finra
nk K W
-/
lemma orthogonal_orthogonal (hB : B.Nondegenerate) (hB₀ : B.IsRefl) (W : Submodule K V) :
    B.orthogonal (B.orthogonal W) = W := by
  apply (eq_of_le_of_finrank_le (LinearMap.BilinForm.le_orthogonal_orthogonal hB₀) _).symm
  simp only [finrank_orthogonal hB]
  lia

variable {W : Submodule K V}
/-
**LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint** 是 Mathlib 中的一个引理，位于命名空间 
`LinearMap.BilinForm`。
形式化陈述：isCompl_orthogonal_iff_disjoint (hB₀ : B.IsRefl) : IsCompl W (B.orthogonal
 W) ↔ Disjoint W (B.orthogonal W)
参数：hB₀ : B.IsRefl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `LinearMap.BilinForm.finrank_add_finrank_orthogonal`：finrank_add_finrank_
orthogonal (b₁ : B.IsRefl) (W : Submodule K V) : finrank K W + finrank K (B.orth
ogonal W) = finrank K V + finrank K (W ⊓…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isCompl_orthogonal_iff_disjoint (hB₀ : B.IsRefl) :
    IsCompl W (B.orthogonal W) ↔ Disjoint W (B.orthogonal W) := by
  refine ⟨IsCompl.disjoint, fun h ↦ ⟨h, ?_⟩⟩
  rw [codisjoint_iff]
  apply (eq_top_of_finrank_eq <| (finrank_le _).antisymm _)
  calc
    finrank K V ≤ finrank K V + finrank K ↥(W ⊓ B.orthogonal ⊤) := le_self_add
    _ ≤ finrank K ↥(W ⊔ B.orthogonal W) + finrank K ↥(W ⊓ B.orthogonal W) := ?_
    _ ≤ finrank K ↥(W ⊔ B.orthogonal W) := by simp [h.eq_bot]
  rw [finrank_sup_add_finrank_inf_eq, finrank_add_finrank_orthogonal hB₀ W]

/-- A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is nondegenerate. -/
/-
**LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate** 是 Mathlib 中
的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：isCompl_orthogonal_of_restrict_nondegenerate (b₁ : B.IsRefl) (b₂ : (B.rest
rict W).Nondegenerate) : IsCompl W (B.orthogonal W)
参数：b₁ : B.IsRefl；b₂ : (B.restrict W).Nondegenerate。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.BilinForm.restrict_apply`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (B
 : LinearMap.BilinForm R…
· 使用定理 `IsCompl.of_eq`：of_eq (h₁ : x ⊓ y = ⊥) (h₂ : x ⊔ y = ⊤) : IsCompl x y
· 使用定理 `Submodule.eq_top_of_finrank_eq`：∀ {K : Type u} {V : Type v} [inst : Divi
sionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   [FiniteDime
nsional K V] {S : Su…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.finrank_le`：Submodule.finrank_le [Module.Finite R M] (s : Subm
odule R M) : finrank R s <= finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `Submodule.finrank_sup_add_finrank_inf_eq`：finrank_sup_add_finrank_inf_eq
 (s t : Submodule K V) [FiniteDimensional K s] [FiniteDimensional K t] : finrank
 K ↑(s ⊔ t) + finrank K ↑(s ⊓ …
· 使用定理 `LinearMap.BilinForm.finrank_add_finrank_orthogonal`：finrank_add_finrank_
orthogonal (b₁ : B.IsRefl) (W : Submodule K V) : finrank K W + finrank K (B.orth
ogonal W) = finrank K V + finrank K (W ⊓…
· 使用定理 `le_self_add`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ a + b

--- 原说明 ---
A subspace is complement to its orthogonal complement with respect to some
reflexive bilinear form if that bilinear form restricted on to the subspace is n
ondegenerate.
-/
theorem isCompl_orthogonal_of_restrict_nondegenerate
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) : IsCompl W (B.orthogonal W) := by
  have : W ⊓ B.orthogonal W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx₁, hx₂⟩ := mem_inf.1 hx
    refine Subtype.mk_eq_mk.1 (b₂.1 ⟨x, hx₁⟩ ?_)
    rintro ⟨n, hn⟩
    simp only [restrict_apply, domRestrict_apply]
    exact b₁ n x (b₁ x n (b₁ n x (hx₂ n hn)))
  refine IsCompl.of_eq this (eq_top_of_finrank_eq <| (finrank_le _).antisymm ?_)
  conv_rhs => rw [← add_zero (finrank K _)]
  rw [← finrank_bot K V, ← this, finrank_sup_add_finrank_inf_eq,
    finrank_add_finrank_orthogonal b₁]
  exact le_self_add

/-- A subspace is complement to its orthogonal complement with respect to some reflexive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegenerate. -/
/-
**LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal** 是 Mathlib 
中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：restrict_nondegenerate_iff_isCompl_orthogonal (b₁ : B.IsRefl) : (B.restric
t W).Nondegenerate ↔ IsCompl W (B.orthogonal W)
参数：b₁ : B.IsRefl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`：isComp
l_orthogonal_of_restrict_nondegenerate (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nond
egenerate) : IsCompl W (B.orthogonal W)
· 使用定理 `LinearMap.BilinForm.nondegenerate_restrict_of_disjoint_orthogonal`：nonde
generate_restrict_of_disjoint_orthogonal (B : BilinForm R₁ M₁) (b : B.IsRefl) {W
 : Submodule R₁ M₁} (hW : Disjoint W (B.orthogonal W)) …
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y

--- 原说明 ---
A subspace is complement to its orthogonal complement with respect to some refle
xive bilinear
form if and only if that bilinear form restricted on to the subspace is nondegen
erate.
-/
theorem restrict_nondegenerate_iff_isCompl_orthogonal
    (b₁ : B.IsRefl) : (B.restrict W).Nondegenerate ↔ IsCompl W (B.orthogonal W) :=
  ⟨fun b₂ => isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂, fun h =>
    B.nondegenerate_restrict_of_disjoint_orthogonal b₁ h.1⟩
/-
**LinearMap.BilinForm.orthogonal_eq_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：orthogonal_eq_top_iff (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) 
: B.orthogonal W = ⊤ ↔ W = ⊥
参数：b₁ : B.IsRefl；b₂ : (B.restrict W).Nondegenerate。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
· 使用定理 `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`：isComp
l_orthogonal_of_restrict_nondegenerate (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nond
egenerate) : IsCompl W (B.orthogonal W)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_top_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), a ⊓ ⊤ = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.BilinForm.orthogonal_bot`：∀ {R : Type u_1} {M : Type u_2} [ins
t : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {B
 : LinearMap.BilinForm R…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma orthogonal_eq_top_iff (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) :
    B.orthogonal W = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).inf_eq_bot
  rwa [h, inf_top_eq] at this
/-
**LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot** 是 
Mathlib 中的一个引理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot (b₁ : B.IsRefl) (b₂ 
: (B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) : W = ⊤
参数：b₁ : B.IsRefl；b₂ : (B.restrict W).Nondegenerate；b₃ : B.orthogonal W = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate`：isComp
l_orthogonal_of_restrict_nondegenerate (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nond
egenerate) : IsCompl W (B.orthogonal W)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
lemma eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) :
    W = ⊤ := by
  have := (B.isCompl_orthogonal_of_restrict_nondegenerate b₁ b₂).sup_eq_top
  rwa [b₃, sup_bot_eq] at this
/-
**LinearMap.BilinForm.orthogonal_eq_bot_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap
.BilinForm`。
形式化陈述：orthogonal_eq_bot_iff (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) 
(b₃ : B.Nondegenerate) : B.orthogonal W = ⊥ ↔ W = ⊤
参数：b₁ : B.IsRefl；b₂ : (B.restrict W).Nondegenerate；b₃ : B.Nondegenerate。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.BilinForm.eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bo
t`：eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot (b₁ : B.IsRefl) (b₂ : (
B.restrict W).Nondegenerate) (b₃ : B.orthogonal W = ⊥) : W = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma orthogonal_eq_bot_iff
    (b₁ : B.IsRefl) (b₂ : (B.restrict W).Nondegenerate) (b₃ : B.Nondegenerate) :
    B.orthogonal W = ⊥ ↔ W = ⊤ := by
  refine ⟨eq_top_of_restrict_nondegenerate_of_orthogonal_eq_bot b₁ b₂, fun h ↦ ?_⟩
  rw [h, eq_bot_iff]
  exact fun x hx ↦ b₃.1 x fun y ↦ b₁ y x <| by simpa using! hx y

end

/-! We note that we cannot use `BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` for the
lemma below since the below lemma does not require `V` to be finite dimensional. However,
`BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal` does not require `B` to be nondegenerate
on the whole space. -/


/-- The restriction of a reflexive, non-degenerate bilinear form on the orthogonal complement of
the span of a singleton is also non-degenerate. -/
/-
**LinearMap.BilinForm.restrict_nondegenerate_orthogonal_spanSingleton** 是 Mathli
b 中的一个定理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：restrict_nondegenerate_orthogonal_spanSingleton (B : BilinForm K V) (b₁ : 
B.Nondegenerate) (b₂ : B.IsRefl) {x : V} (hx : B x x != 0) : Nondegenerate B.res
trict B.orthogonal (K ∙ x)
参数：B : BilinForm K V；b₁ : B.Nondegenerate；b₂ : B.IsRefl；hx : B x x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.span_singleton_sup_orthogonal_eq_top`：span_singleton
_sup_orthogonal_eq_top {B : BilinForm K V} {x : V} (hx : B x x != 0) : K ∙ x ⊔ B
.orthogonal (K ∙ x) = ⊤
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.BilinForm.add_right`：add_right (x y z : M) : B x (y + z) = B x
 y + B x z
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearMap.BilinForm.add_left`：add_left (x y z : M) : B (x + y) z = B x z
 + B y z

--- 原说明 ---
The restriction of a reflexive, non-degenerate bilinear form on the orthogonal c
omplement of
the span of a singleton is also non-degenerate.
-/
theorem restrict_nondegenerate_orthogonal_spanSingleton (B : BilinForm K V) (b₁ : B.Nondegenerate)
    (b₂ : B.IsRefl) {x : V} (hx : B x x ≠ 0) :
    Nondegenerate <| B.restrict <| B.orthogonal (K ∙ x) := by
  have (n : V) : n ∈ K ∙ x ⊔ B.orthogonal (K ∙ x) :=
    (span_singleton_sup_orthogonal_eq_top hx).symm ▸ Submodule.mem_top
  refine ⟨fun m hm => Submodule.coe_eq_zero.1 (b₁.1 m fun n ↦ ?_),
    fun m hm => Submodule.coe_eq_zero.1 (b₁.2 m fun n ↦ ?_)⟩ <;>
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 <| this n
  · rw [add_right, b₂ y m <| m.2 y hy, show B m z = 0 from hm ⟨z, hz⟩, add_zero]
  · rw [add_left, m.2 y hy, show B z m = 0 from hm ⟨z, hz⟩, add_zero]

end BilinForm

end LinearMap

