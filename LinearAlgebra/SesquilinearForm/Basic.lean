/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow
-/
module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Sesquilinear maps

This file provides properties about sesquilinear maps and forms. The maps considered are of the
form `M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M`, where `I₁ : R₁ →+* R` and `I₂ : R₂ →+* R` are ring homomorphisms and
`M₁` is a module over `R₁`, `M₂` is a module over `R₂` and `M` is a module over `R`.
Sesquilinear forms are the special case that `M₁ = M₂`, `M = R₁ = R₂ = R`, and `I₁ = RingHom.id R`.
Taking additionally `I₂ = RingHom.id R`, then one obtains bilinear forms.

Sesquilinear maps are a special case of the bilinear maps defined in `BilinearMap.lean`, and many
basic lemmas about construction and elementary calculations are found there.

## Main declarations

* `IsSymm`, `IsAlt`: states that a sesquilinear form is symmetric and alternating, respectively

## References

* <https://en.wikipedia.org/wiki/Sesquilinear_form#Over_arbitrary_rings>

## Tags

Sesquilinear form, Sesquilinear map
-/

@[expose] public section

open Module

variable {R R₁ R₂ R₃ M M₁ M₂ M₃ Mₗ₁ Mₗ₁' Mₗ₂ Mₗ₂' K K₁ K₂ V V₁ V₂ n : Type*}

namespace LinearMap

/-! ### Orthogonal vectors -/


section CommRing

-- the `ₗ` subscript variables are for special cases about linear (as opposed to semilinear) maps
variable [CommSemiring R] [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁] [CommSemiring R₂]
  [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M] [Module R M]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- The proposition that two elements of a sesquilinear map space are orthogonal -/
@[deprecated "Use `B x y = 0`" (since := "2026-03-30")]
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that two elements of a sesquilinear map space are orthogonal
-/
def IsOrtho (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop :=
  B x y = 0

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.isOrtho_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isOrtho_def {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} {x y} : B.IsOrtho x y ↔ B x y 
= 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOrtho_def {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} {x y} : B.IsOrtho x y ↔ B x y = 0 :=
  Iff.rfl

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.isOrtho_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isOrtho_zero_left (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x) : IsOrtho B (0 : M₁)
 x
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem isOrtho_zero_left (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B (0 : M₁) x := by
  dsimp only [IsOrtho]
  rw [map_zero B, zero_apply]

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.isOrtho_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isOrtho_zero_right (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x) : IsOrtho B x (0 : 
M₂)
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
-/
theorem isOrtho_zero_right (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) (x) : IsOrtho B x (0 : M₂) :=
  map_zero (B x)

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.isOrtho_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isOrtho_flip {B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₁'] M} {x y} : B.IsOrtho x y ↔ B.fl
ip.IsOrtho y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOrtho_flip {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {x y} : B.IsOrtho x y ↔ B.flip.IsOrtho y x := by
  simp_rw [isOrtho_def, flip_apply]

open scoped Function in -- required for scoped `on` notation
/-- A set of vectors `v` is orthogonal with respect to some bilinear map `B` if and only
if for all `i ≠ j`, `B (v i) (v j) = 0`. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of vectors `v` is orthogonal with respect to some bilinear map `B` if and 
only
if for all `i ≠ j`, `B (v i) (v j) = 0`.
-/
def IsOrthoᵢ (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) (v : n → M₁) : Prop :=
  Pairwise ((fun n m => B n m = 0) on v)
/-
**LinearMap.isOrtho** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOrthoᵢ_def {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M} {v : n → M₁} :
    B.IsOrthoᵢ v ↔ ∀ i j : n, i ≠ j → B (v i) (v j) = 0 :=
  Iff.rfl
/-
**LinearMap.isOrtho** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isOrthoᵢ_flip (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₁'] M) {v : n → M₁} :
    B.IsOrthoᵢ v ↔ B.flip.IsOrthoᵢ v := by
  simp_rw [isOrthoᵢ_def]
  constructor <;> exact fun h i j hij ↦ h j i hij.symm

end CommRing

section Field

variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [Field K₂] [AddCommGroup V₂] [Module K₂ V₂]
  {I₁ : K₁ →+* K} {I₂ : K₂ →+* K} {I₁' : K₁ →+* K} {J₁ : K →+* K} {J₂ : K →+* K}

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.ortho_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ortho_smul_left {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₁} (ha : a != 
0) : IsOrtho B x y ↔ IsOrtho B (a • x) y
参数：ha : a != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_smulₛₗ₂`：map_smulₛₗ₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (r : 
R) (x y) : f (r • x) y = ρ₁₂ r • f x y
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `map_eq_zero`：map_eq_zero : f a = 0 ↔ a = 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem ortho_smul_left {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] V} {x y} {a : K₁} (ha : a ≠ 0) :
    IsOrtho B x y ↔ IsOrtho B (a • x) y := by
  dsimp only [IsOrtho]
  constructor <;> intro H
  · rw [map_smulₛₗ₂, H, smul_zero]
  · rw [map_smulₛₗ₂, smul_eq_zero] at H
    rcases H with H | H
    · rw [map_eq_zero I₁] at H
      trivial
    · exact H

@[deprecated "`LinearMap.IsOrtho` has been deprecated" (since := "2026-03-30")]
/-
**LinearMap.ortho_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：ortho_smul_right {B : V₁ ->ₛₗ[I₁] V₂ ->ₛₗ[I₂] V} {x y} {a : K₂} {ha : a !=
 0} : IsOrtho B x y ↔ IsOrtho B x (a • y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_smulₛₗ`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃
 : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ortho_smul_right {B : V₁ →ₛₗ[I₁] V₂ →ₛₗ[I₂] V} {x y} {a : K₂} {ha : a ≠ 0} :
    IsOrtho B x y ↔ IsOrtho B x (a • y) := by
  simp_all [IsOrtho]

/-- A set of orthogonal vectors `v` with respect to some sesquilinear map `B` is linearly
  independent if for all `i`, `B (v i) (v i) ≠ 0`. -/
/-
**LinearMap.linearIndependent_of_isOrtho** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of orthogonal vectors `v` with respect to some sesquilinear map `B` is lin
early
  independent if for all `i`, `B (v i) (v i) ≠ 0`.
-/
theorem linearIndependent_of_isOrthoᵢ {B : V₁ →ₛₗ[I₁] V₁ →ₛₗ[I₁'] V} {v : n → V₁}
    (hv₁ : B.IsOrthoᵢ v) (hv₂ : ∀ i, B (v i) (v i) ≠ 0) : LinearIndependent K₁ v := by
  rw [linearIndependent_iff']
  intro s w hs i hi
  have : B (s.sum fun i : n ↦ w i • v i) (v i) = 0 := by rw [hs, map_zero, zero_apply]
  have hsum : (s.sum fun j : n ↦ I₁ (w j) • B (v j) (v i)) = I₁ (w i) • B (v i) (v i) := by
    apply Finset.sum_eq_single_of_mem i hi
    intro j _hj hij
    rw [isOrthoᵢ_def.1 hv₁ _ _ hij, smul_zero]
  simp_rw [B.map_sum₂, map_smulₛₗ₂, hsum] at this
  apply (map_eq_zero I₁).mp
  exact (smul_eq_zero.mp this).elim _root_.id (hv₂ i · |>.elim)

end Field

/-! ### Reflexive bilinear maps -/

section Reflexive

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-- The proposition that a sesquilinear map is reflexive -/
/-
**LinearMap.IsRefl** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsRefl (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sesquilinear map is reflexive
-/
def IsRefl (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x y, B x y = 0 → B y x = 0

namespace IsRefl

section
variable (H : B.IsRefl)
include H

/-
**LinearMap.IsRefl.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：eq_zero : forall {x y}, B x y = 0 -> B y x = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_zero : ∀ {x y}, B x y = 0 → B y x = 0 := fun {x y} ↦ H x y
/-
**LinearMap.IsRefl.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：eq_iff {x y} : B x y = 0 ↔ B y x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_iff {x y} : B x y = 0 ↔ B y x = 0 := ⟨H x y, H y x⟩

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff
/-
**LinearMap.IsRefl.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：domRestrict (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl
参数：p : Submodule R₁ M₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem domRestrict (p : Submodule R₁ M₁) : (B.domRestrict₁₂ p p).IsRefl :=
  fun _ _ ↦ by
  simp_rw [domRestrict₁₂_apply]
  exact H _ _
end

@[simp]
/-
**LinearMap.IsRefl.flip_isRefl_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：flip_isRefl_iff : B.flip.IsRefl ↔ B.IsRefl
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
-/
theorem flip_isRefl_iff : B.flip.IsRefl ↔ B.IsRefl :=
  forall_comm
/-
**LinearMap.IsRefl.ker_flip** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：ker_flip (H : B.IsRefl) : B.flip.ker = B.ker
参数：H : B.IsRefl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearMap.IsRefl.eq_iff`：eq_iff {x y} : B x y = 0 ↔ B y x = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma ker_flip (H : B.IsRefl) : B.flip.ker = B.ker := by
  ext x
  simp [LinearMap.ext_iff, H.eq_iff]
/-
**LinearMap.IsRefl.ker_flip_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsRefl`。
形式化陈述：ker_flip_eq_bot (H : B.IsRefl) (h : LinearMap.ker B = ⊥) : LinearMap.ker B
.flip = ⊥
参数：H : B.IsRefl；h : LinearMap.ker B = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsRefl.ker_flip`：ker_flip (H : B.IsRefl) : B.flip.ker = B.ker
-/
theorem ker_flip_eq_bot (H : B.IsRefl) (h : LinearMap.ker B = ⊥) : LinearMap.ker B.flip = ⊥ := by
  rwa [H.ker_flip]
/-
**LinearMap.IsRefl.ker_eq_bot_iff_ker_flip_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Lin
earMap.IsRefl`。
形式化陈述：ker_eq_bot_iff_ker_flip_eq_bot (H : B.IsRefl) : LinearMap.ker B = ⊥ ↔ Line
arMap.ker B.flip = ⊥
参数：H : B.IsRefl。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.IsRefl.ker_flip`：ker_flip (H : B.IsRefl) : B.flip.ker = B.ker
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot_iff_ker_flip_eq_bot (H : B.IsRefl) :
    LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥ := by
  rwa [ker_flip]

end IsRefl

end Reflexive

/-! ### Symmetric bilinear forms -/

section Symmetric

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I : R →+* R} {B : M →ₛₗ[I] M →ₗ[R] R}

/-- The proposition that a sesquilinear form is symmetric -/
/-
**LinearMap.IsSymm** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → {I : R →+* R} → (M →ₛₗ
[I] M →ₗ[R] R) → Prop
参数：M →ₛₗ[I] M →ₗ[R] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sesquilinear form is symmetric
-/
structure IsSymm (B : M →ₛₗ[I] M →ₗ[R] R) : Prop where
  protected eq : ∀ x y, I (B x y) = B y x
/-
**LinearMap.isSymm_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymm_def {B : M ->ₛₗ[I] M ->ₗ[R] R} : B.IsSymm ↔ forall x y, I (B x y) =
 B y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem isSymm_def {B : M →ₛₗ[I] M →ₗ[R] R} : B.IsSymm ↔ ∀ x y, I (B x y) = B y x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

namespace IsSymm

/-
**LinearMap.IsSymm.isRefl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm`。
形式化陈述：isRefl (H : B.IsSymm) : B.IsRefl
参数：H : B.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem isRefl (H : B.IsSymm) : B.IsRefl := fun x y H1 ↦ by
  rw [← H.eq]
  simp [H1]
/-
**LinearMap.IsSymm.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm`。
形式化陈述：eq_iff (H : B.IsSymm) {x y} : B x y = 0 ↔ B y x = 0
参数：H : B.IsSymm。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsRefl.eq_iff`：eq_iff {x y} : B x y = 0 ↔ B y x = 0
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
-/
theorem eq_iff (H : B.IsSymm) {x y} : B x y = 0 ↔ B y x = 0 := H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff
/-
**LinearMap.IsSymm.domRestrict** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm`。
形式化陈述：domRestrict (H : B.IsSymm) (p : Submodule R M) : (B.domRestrict₁₂ p p).IsS
ymm where eq _ _
参数：H : B.IsSymm；p : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
-/
theorem domRestrict (H : B.IsSymm) (p : Submodule R M) : (B.domRestrict₁₂ p p).IsSymm where
  eq _ _ := by
    simp_rw [domRestrict₁₂_apply]
    exact H.eq _ _

end IsSymm

@[simp]
/-
**LinearMap.isSymm_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymm_zero : (0 : M ->ₛₗ[I] M ->ₗ[R] R).IsSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem isSymm_zero : (0 : M →ₛₗ[I] M →ₗ[R] R).IsSymm := ⟨fun _ _ => map_zero _⟩
/-
**LinearMap.IsSymm.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsSymm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B C : M →ₛₗ[I] M →ₗ[R] R}
, B.IsSymm → C.IsSymm → (B + C).IsSymm
参数：B + C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected lemma IsSymm.add {C : M →ₛₗ[I] M →ₗ[R] R} (hB : B.IsSymm) (hC : C.IsSymm) :
    (B + C).IsSymm where
  eq x y := by simp [hB.eq, hC.eq]
/-
**LinearMap.BilinMap.isSymm_iff_eq_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {N : Type u_20} [inst_3 : AddCommMonoid 
N] [inst_4 : _root_.Module R N] {B : LinearMap.BilinMap R M N},   (∀ (x y : M), 
(B x) y = (B y) x) ↔ B = LinearMap.flip B
参数：∀ (x y : M), (B x) y = (B y) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem BilinMap.isSymm_iff_eq_flip {N : Type*} [AddCommMonoid N] [Module R N]
    {B : LinearMap.BilinMap R M N} : (∀ x y, B x y = B y x) ↔ B = B.flip := by
  simp [LinearMap.ext_iff₂]
/-
**LinearMap.isSymm_iff_eq_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isSymm_iff_eq_flip {B : LinearMap.BilinForm R M} : B.IsSymm ↔ B = B.flip
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.isSymm_def`：isSymm_def {B : M ->ₛₗ[I] M ->ₗ[R] R} : B.IsSymm ↔
 forall x y, I (B x y) = B y x
· 使用定理 `LinearMap.BilinMap.isSymm_iff_eq_flip`：∀ {R : Type u_1} {M : Type u_5} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Type u_20} [inst_3 : …
-/
theorem isSymm_iff_eq_flip {B : LinearMap.BilinForm R M} : B.IsSymm ↔ B = B.flip :=
  isSymm_def.trans BilinMap.isSymm_iff_eq_flip

end Symmetric

/-! ### Positive semidefinite sesquilinear forms -/

section PositiveSemidefinite

variable [CommSemiring R] [AddCommMonoid M] [Module R M] {I₁ I₂ : R →+* R}

/-- A sesquilinear form `B` is **nonnegative** if for any `x` we have `0 ≤ B x x`. -/
/-
**LinearMap.IsNonneg** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] →         [inst_2 : _root_.Module R M] → {I₁ I₂ : R →+*
 R} → [LE R] → (M →ₛₗ[I₁] M →ₛₗ[I₂] R) → Prop
参数：M →ₛₗ[I₁] M →ₛₗ[I₂] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sesquilinear form `B` is **nonnegative** if for any `x` we have `0 ≤ B x x`.
-/
structure IsNonneg [LE R] (B : M →ₛₗ[I₁] M →ₛₗ[I₂] R) where
  nonneg : ∀ x, 0 ≤ B x x
/-
**LinearMap.isNonneg_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNonneg_def [LE R] {B : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R} : B.IsNonneg ↔ forall x,
 0 <= B x x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma isNonneg_def [LE R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} : B.IsNonneg ↔ ∀ x, 0 ≤ B x x :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

@[simp]
/-
**LinearMap.isNonneg_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isNonneg_zero [Preorder R] : IsNonneg (0 : M ->ₛₗ[I₁] M ->ₛₗ[I₂] R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma isNonneg_zero [Preorder R] : IsNonneg (0 : M →ₛₗ[I₁] M →ₛₗ[I₂] R) := ⟨fun _ ↦ le_rfl⟩
/-
**LinearMap.IsNonneg.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsNonneg`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {I₁ I₂ : R →+* R} [inst_3 : Preorder R] 
[AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₛₗ[I₂] R},   B.IsNonneg → C.IsNonneg → (B + 
C).IsNonneg
参数：B + C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `add_nonneg`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder 
α] [AddLeftMono α] {a b : α}, 0 ≤ a → 0 ≤ b → 0 ≤ a + b
· 使用定理 `LinearMap.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_5} [inst : CommS
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ I₂ : R 
→+* R} [inst_3 …
-/
protected lemma IsNonneg.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₛₗ[I₂] R}
    (hB : B.IsNonneg) (hC : C.IsNonneg) : (B + C).IsNonneg where
  nonneg x := add_nonneg (hB.nonneg x) (hC.nonneg x)
/-
**LinearMap.IsNonneg.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsNonneg`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {I₁ I₂ : R →+* R} [inst_3 : Preorder R] 
[PosMulMono R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} {c : R},   B.IsNonneg → 0 ≤ c → (c • 
B).IsNonneg
参数：c • B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `LinearMap.IsNonneg.nonneg`：∀ {R : Type u_1} {M : Type u_5} [inst : CommS
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ I₂ : R 
→+* R} [inst_3 …
-/
protected lemma IsNonneg.smul [Preorder R] [PosMulMono R] {B : M →ₛₗ[I₁] M →ₛₗ[I₂] R} {c : R}
    (hB : B.IsNonneg) (hc : 0 ≤ c) : (c • B).IsNonneg where
  nonneg x := mul_nonneg hc (hB.nonneg x)

/-- A sesquilinear form `B` is **positive semidefinite** if it is symmetric and nonnegative. -/
/-
**LinearMap.IsPosSemidef** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → {I₁ : R →+* R} → [LE R
] → (M →ₛₗ[I₁] M →ₗ[R] R) → Prop
参数：M →ₛₗ[I₁] M →ₗ[R] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sesquilinear form `B` is **positive semidefinite** if it is symmetric and nonn
egative.
-/
structure IsPosSemidef [LE R] (B : M →ₛₗ[I₁] M →ₗ[R] R) extends
  isSymm : B.IsSymm,
  isNonneg : B.IsNonneg
/-
**LinearMap.isPosSemidef_def** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isPosSemidef_def [LE R] {B : M ->ₛₗ[I₁] M ->ₗ[R] R} : B.IsPosSemidef ↔ B.I
sSymm ∧ B.IsNonneg
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_5} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ : R
 →+* R} [inst_3 : L…
· 使用定理 `LinearMap.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_5} [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ :
 R →+* R} [inst_3 : L…
-/
lemma isPosSemidef_def [LE R] {B : M →ₛₗ[I₁] M →ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg :=
  ⟨fun h ↦ ⟨h.isSymm, h.isNonneg⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, h₂⟩⟩

@[simp]
/-
**LinearMap.isPosSemidef_zero** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap`。
形式化陈述：isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : M ->ₛₗ[I₁] M ->ₗ[R] R) 
where isSymm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.isSymm_zero`：isSymm_zero : (0 : M ->ₛₗ[I] M ->ₗ[R] R).IsSymm
· 使用引理 `LinearMap.isNonneg_zero`：isNonneg_zero [Preorder R] : IsNonneg (0 : M ->
ₛₗ[I₁] M ->ₛₗ[I₂] R)
-/
lemma isPosSemidef_zero [Preorder R] : IsPosSemidef (0 : M →ₛₗ[I₁] M →ₗ[R] R) where
  isSymm := isSymm_zero
  isNonneg := isNonneg_zero
/-
**LinearMap.IsPosSemidef.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPosSemidef`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {I₁ : R →+* R} [inst_3 : Preorder R] [Ad
dLeftMono R] {B C : M →ₛₗ[I₁] M →ₗ[R] R},   B.IsPosSemidef → C.IsPosSemidef → (B
 + C).IsPosSemidef
参数：B + C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `LinearMap.isPosSemidef_def`：isPosSemidef_def [LE R] {B : M ->ₛₗ[I₁] M ->
ₗ[R] R} : B.IsPosSemidef ↔ B.IsSymm ∧ B.IsNonneg
· 使用定理 `LinearMap.IsSymm.add`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B
 C : M →ₛₗ…
· 使用定理 `LinearMap.IsPosSemidef.isSymm`：∀ {R : Type u_1} {M : Type u_5} [inst : C
ommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ : R
 →+* R} [inst_3 : L…
· 使用定理 `LinearMap.IsNonneg.add`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ I₂ : R →+*
 R} [inst_3 …
· 使用定理 `LinearMap.IsPosSemidef.isNonneg`：∀ {R : Type u_1} {M : Type u_5} [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I₁ :
 R →+* R} [inst_3 : L…
-/
protected lemma IsPosSemidef.add [Preorder R] [AddLeftMono R] {B C : M →ₛₗ[I₁] M →ₗ[R] R}
    (hB : B.IsPosSemidef) (hC : C.IsPosSemidef) : (B + C).IsPosSemidef :=
  isPosSemidef_def.2 ⟨hB.isSymm.add hC.isSymm, hB.isNonneg.add hC.isNonneg⟩

end PositiveSemidefinite

/-! ### Alternating bilinear maps -/

section Alternating

section CommSemiring

section AddCommMonoid

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-- The proposition that a sesquilinear map is alternating -/
/-
**LinearMap.IsAlt** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsAlt (B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₁ ->ₛₗ[I₂] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that a sesquilinear map is alternating
-/
def IsAlt (B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M) : Prop :=
  ∀ x, B x x = 0

variable (H : B.IsAlt)
include H
/-
**LinearMap.IsAlt.self_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAlt`。
形式化陈述：∀ {R : Type u_1} {R₁ : Type u_2} {M : Type u_5} {M₁ : Type u_6} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 
: CommSemiring R₁] [inst_4 : AddCommMonoid M₁] [inst_5 : _root_.Module R₁ M₁]   
{I₁ I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}, B.IsAlt → ∀ (x : M₁), (B x) x 
= 0
参数：x : M₁；B x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsAlt.self_eq_zero (x : M₁) : B x x = 0 :=
  H x
/-
**LinearMap.IsAlt.eq_of_add_add_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsA
lt`。
形式化陈述：∀ {R : Type u_1} {R₁ : Type u_2} {M : Type u_5} {M₁ : Type u_6} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 
: CommSemiring R₁] [inst_4 : AddCommMonoid M₁] [inst_5 : _root_.Module R₁ M₁]   
{I₁ I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M},   B.IsAlt → ∀ [IsCancelAdd M] 
{a b c : M₁}, a + b + c = 0 → (B a) b = (B b) c
参数：B a；B b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem IsAlt.eq_of_add_add_eq_zero [IsCancelAdd M] {a b c : M₁} (hAdd : a + b + c = 0) :
    B a b = B b c := by
  have : B a a + B a b + B a c = B a c + B b c + B c c := by
    simp_rw [← map_add, ← map_add₂, hAdd, map_zero, LinearMap.zero_apply]
  rw [H, H, zero_add, add_zero, add_comm] at this
  exact add_left_cancel this

end AddCommMonoid

section AddCommGroup

namespace IsAlt

variable [CommSemiring R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I₁ : R₁ →+* R} {I₂ : R₁ →+* R} {I : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-
**LinearMap.IsAlt.neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAlt`。
形式化陈述：neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x
参数：H : B.IsAlt；x y : M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAlt.self_eq_zero`：∀ {R : Type u_1} {R₁ : Type u_2} {M : Type
 u_5} {M₁ : Type u_6} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst
_2 : _root_.Module…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x := by
  have H1 : B (y + x) (y + x) = 0 := self_eq_zero H (y + x)
  simpa [map_add, self_eq_zero H, add_eq_zero_iff_neg_eq] using H1
/-
**LinearMap.IsAlt.isRefl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAlt`。
形式化陈述：isRefl (H : B.IsAlt) : B.IsRefl
参数：H : B.IsAlt。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsAlt.neg`：neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
-/
theorem isRefl (H : B.IsAlt) : B.IsRefl := by
  intro x y h
  rw [← neg H, h, neg_zero]
/-
**LinearMap.IsAlt.eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAlt`。
形式化陈述：eq_iff (H : B.IsAlt) {x y} : B x y = 0 ↔ B y x = 0
参数：H : B.IsAlt。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsRefl.eq_iff`：eq_iff {x y} : B x y = 0 ↔ B y x = 0
· 使用定理 `LinearMap.IsAlt.isRefl`：isRefl (H : B.IsAlt) : B.IsRefl
-/
theorem eq_iff (H : B.IsAlt) {x y} : B x y = 0 ↔ B y x = 0 := H.isRefl.eq_iff

@[deprecated (since := "2026-03-30")]
alias ortho_comm := eq_iff

end IsAlt

end AddCommGroup

end CommSemiring

section Semiring

variable [CommRing R] [AddCommGroup M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] {I : R₁ →+* R}

/-
**LinearMap.isAlt_iff_eq_neg_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isAlt_iff_eq_neg_flip [NoZeroDivisors R] [CharZero R] {B : M₁ ->ₛₗ[I] M₁ -
>ₛₗ[I] R} : B.IsAlt ↔ B = -B.flip
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsAlt.neg`：neg (H : B.IsAlt) (x y : M₁) : -B x y = B y x
· 使用定理 `LinearMap.congr_fun₂`：congr_fun₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (h : 
f = g) (x y) : f x y = g x y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_self_eq_zero`：add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0
-/
theorem isAlt_iff_eq_neg_flip [NoZeroDivisors R] [CharZero R] {B : M₁ →ₛₗ[I] M₁ →ₛₗ[I] R} :
    B.IsAlt ↔ B = -B.flip := by
  constructor <;> intro h
  · ext
    simp_rw [neg_apply, flip_apply]
    exact (h.neg _ _).symm
  intro x
  let h' := congr_fun₂ h x x
  simp only [neg_apply, flip_apply, ← add_eq_zero_iff_eq_neg] at h'
  exact add_self_eq_zero.mp h'

end Semiring

end Alternating

end LinearMap

namespace LinearMap

/-! ### Adjoint pairs -/

section AdjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable [AddCommMonoid M₂] [Module R M₂]
variable [AddCommMonoid M₃] [Module R M₃]
variable {I : R →+* R}
variable {B F : M →ₗ[R] M →ₛₗ[I] M₃} {B' : M₁ →ₗ[R] M₁ →ₛₗ[I] M₃} {B'' : M₂ →ₗ[R] M₂ →ₛₗ[I] M₃}
variable {f f' : M →ₗ[R] M₁} {g g' : M₁ →ₗ[R] M}
variable (B B' f g)

/-- Given a pair of modules equipped with bilinear maps, this is the condition for a pair of
maps between them to be mutually adjoint. -/
/-
**LinearMap.IsAdjointPair** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsAdjointPair (f : M -> M₁) (g : M₁ -> M)
参数：f : M -> M₁；g : M₁ -> M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a pair of modules equipped with bilinear maps, this is the condition for a
 pair of
maps between them to be mutually adjoint.
-/
def IsAdjointPair (f : M → M₁) (g : M₁ → M) :=
  ∀ x y, B' (f x) y = B x (g y)

variable {B B' f g}
/-
**LinearMap.isAdjointPair_iff_comp_eq_compl** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAdjointPair_iff_comp_eq_compl₂ : IsAdjointPair B B' f g ↔ B'.comp f = B.compl₂ g := by
  constructor <;> intro h
  · ext x y
    rw [comp_apply, compl₂_apply]
    exact h x y
  · intro _ _
    rw [← compl₂_apply, ← comp_apply, h]
/-
**LinearMap.isAdjointPair_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isAdjointPair_zero : IsAdjointPair B B' 0 0
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
-/
theorem isAdjointPair_zero : IsAdjointPair B B' 0 0 := fun _ _ ↦ by
  simp only [Pi.zero_apply, map_zero, zero_apply]
/-
**LinearMap.isAdjointPair_id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isAdjointPair_id : IsAdjointPair B B (_root_.id : M -> M) (_root_.id : M -
> M)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isAdjointPair_id : IsAdjointPair B B (_root_.id : M → M) (_root_.id : M → M) :=
  fun _ _ ↦ rfl
/-
**LinearMap.isAdjointPair_one** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isAdjointPair_one : IsAdjointPair B B (1 : Module.End R M) (1 : Module.End
 R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.isAdjointPair_id`：isAdjointPair_id : IsAdjointPair B B (_root_
.id : M -> M) (_root_.id : M -> M)
-/
theorem isAdjointPair_one : IsAdjointPair B B (1 : Module.End R M) (1 : Module.End R M) :=
  isAdjointPair_id
/-
**LinearMap.IsAdjointPair.add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAdjointPair
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} {M₃ : Type u_8} [inst : Co
mmSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 
: AddCommMonoid M₁] [inst_4 : _root_.Module R M₁] [inst_5 : AddCommMonoid M₃]   
[inst_6 : _root_.Module R M₃] {I : R →+* R} {B : M →ₗ[R] M →ₛₗ[I] M₃} {B' : M₁ →
ₗ[R] M₁ →ₛₗ[I] M₃} {f f' : M → M₁}   {g g' : M₁ → M}, B.IsAdjointPair B' f g → B
.IsAdjointPair B' f' g' → B.IsAdjointPair B' (f + f') (g + g')
参数：f + f'；g + g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `LinearMap.map_add₂`：map_add₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y) :
 f (x₁ + x₂) y = f x₁ y + f x₂ y
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
-/
theorem IsAdjointPair.add {f f' : M → M₁} {g g' : M₁ → M} (h : IsAdjointPair B B' f g)
    (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f + f') (g + g') := fun x _ ↦ by
  rw [Pi.add_apply, Pi.add_apply, B'.map_add₂, (B x).map_add, h, h']
/-
**LinearMap.IsAdjointPair.comp** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAdjointPai
r`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} {M₂ : Type u_7} {M₃ : Type
 u_8} [inst : CommSemiring R]   [inst_1 : AddCommMonoid M] [inst_2 : _root_.Modu
le R M] [inst_3 : AddCommMonoid M₁] [inst_4 : _root_.Module R M₁]   [inst_5 : Ad
dCommMonoid M₂] [inst_6 : _root_.Module R M₂] [inst_7 : AddCommMonoid M₃] [inst_
8 : _root_.Module R M₃]   {I : R →+* R} {B : M →ₗ[R] M →ₛₗ[I] M₃} {B' : M₁ →ₗ[R]
 M₁ →ₛₗ[I] M₃} {B'' : M₂ →ₗ[R] M₂ →ₛₗ[I] M₃} {f : M → M₁}   {g : M₁ → M} {f' : M
₁ → M₂} {g' : M₂ → M₁},   B.IsAdjointPair B' f g → B'.IsAdjointPair B'' f' g' → 
B.IsAdjointPair B'' (f' ∘ f) (g ∘ g')
参数：f' ∘ f；g ∘ g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem IsAdjointPair.comp {f : M → M₁} {g : M₁ → M} {f' : M₁ → M₂} {g' : M₂ → M₁}
    (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B' B'' f' g') :
    IsAdjointPair B B'' (f' ∘ f) (g ∘ g') := fun _ _ ↦ by
  rw [Function.comp_def, Function.comp_def, h', h]
/-
**LinearMap.IsAdjointPair.mul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAdjointPair
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₃ : Type u_8} [inst : CommSemiring R] [i
nst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid 
M₃] [inst_4 : _root_.Module R M₃] {I : R →+* R}   {B : M →ₗ[R] M →ₛₗ[I] M₃} {f g
 f' g' : Module.End R M},   B.IsAdjointPair B ⇑f ⇑g → B.IsAdjointPair B ⇑f' ⇑g' 
→ B.IsAdjointPair B ⇑(f * f') ⇑(g' * g)
参数：f * f'；g' * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsAdjointPair.comp`：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type
 u_6} {M₂ : Type u_7} {M₃ : Type u_8} [inst : CommSemiring R]   [inst_1 : AddCom
mMonoid M] [inst_2…
-/
theorem IsAdjointPair.mul {f g f' g' : Module.End R M} (h : IsAdjointPair B B f g)
    (h' : IsAdjointPair B B f' g') : IsAdjointPair B B (f * f') (g' * g) :=
  h'.comp h

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M]
variable [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂]
variable {B F : M →ₗ[R] M →ₗ[R] M₂} {B' : M₁ →ₗ[R] M₁ →ₗ[R] M₂}
variable {f f' : M → M₁} {g g' : M₁ → M}

/-
**LinearMap.IsAdjointPair.sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAdjointPair
`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} {M₂ : Type u_7} [inst : Co
mmRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : Add
CommGroup M₁] [inst_4 : _root_.Module R M₁] [inst_5 : AddCommGroup M₂]   [inst_6
 : _root_.Module R M₂] {B : M →ₗ[R] M →ₗ[R] M₂} {B' : M₁ →ₗ[R] M₁ →ₗ[R] M₂} {f f
' : M → M₁} {g g' : M₁ → M},   B.IsAdjointPair B' f g → B.IsAdjointPair B' f' g'
 → B.IsAdjointPair B' (f - f') (g - g')
参数：f - f'；g - g'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `LinearMap.map_sub₂`：map_sub₂ (f : M' ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P') (x y z) :
 f (x - y) z = f x z - f y z
· 使用定理 `LinearMap.map_sub`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₂ : 
Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommGroup M]
 [inst_…
-/
theorem IsAdjointPair.sub (h : IsAdjointPair B B' f g) (h' : IsAdjointPair B B' f' g') :
    IsAdjointPair B B' (f - f') (g - g') := fun x _ ↦ by
  rw [Pi.sub_apply, Pi.sub_apply, B'.map_sub₂, (B x).map_sub, h, h']
/-
**LinearMap.IsAdjointPair.smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsAdjointPai
r`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} {M₂ : Type u_7} [inst : Co
mmRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : Add
CommGroup M₁] [inst_4 : _root_.Module R M₁] [inst_5 : AddCommGroup M₂]   [inst_6
 : _root_.Module R M₂] {B : M →ₗ[R] M →ₗ[R] M₂} {B' : M₁ →ₗ[R] M₁ →ₗ[R] M₂} {f :
 M → M₁} {g : M₁ → M} (c : R),   B.IsAdjointPair B' f g → B.IsAdjointPair B' (c 
• f) (c • g)
参数：c : R；c • f；c • g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsAdjointPair.smul (c : R) (h : IsAdjointPair B B' f g) :
    IsAdjointPair B B' (c • f) (c • g) := fun _ _ ↦ by
  simp [h _]

end AddCommGroup

section OrthogonalMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (B : LinearMap.BilinForm R M) (f : M → M)

/-- A linear transformation `f` is orthogonal with respect to a bilinear form `B` if `B` is
bi-invariant with respect to `f`. -/
/-
**LinearMap.IsOrthogonal** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrthogonal : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear transformation `f` is orthogonal with respect to a bilinear form `B` if
 `B` is
bi-invariant with respect to `f`.
-/
def IsOrthogonal : Prop :=
  ∀ x y, B (f x) (f y) = B x y

variable {B f}

@[simp]
/-
**LinearMap._root_.LinearEquiv.isAdjointPair_symm_iff** 是 Mathlib 中的一个引理，位于命名空间 
`LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearEquiv.isAdjointPair_symm_iff {f : M ≃ M} :
    LinearMap.IsAdjointPair B B f f.symm ↔ B.IsOrthogonal f :=
  ⟨fun hf x y ↦ by simpa using hf x (f y), fun hf x y ↦ by simpa using hf x (f.symm y)⟩
/-
**LinearMap.isOrthogonal_of_forall_apply_same** 是 Mathlib 中的一个引理，位于命名空间 `LinearM
ap`。
形式化陈述：isOrthogonal_of_forall_apply_same {F : Type*} [FunLike F M M] [LinearMapCl
ass F R M M] (f : F) (h : IsLeftRegular (2 : R)) (hB : B.IsSymm) (hf : forall x,
 B (f x) (f x) = B x x) : B.IsOrthogonal f
参数：f : F；h : IsLeftRegular (2 : R)；hB : B.IsSymm；hf : forall x, B (f x) (f x) = 
B x x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma isOrthogonal_of_forall_apply_same {F : Type*} [FunLike F M M] [LinearMapClass F R M M]
    (f : F) (h : IsLeftRegular (2 : R)) (hB : B.IsSymm) (hf : ∀ x, B (f x) (f x) = B x x) :
    B.IsOrthogonal f := by
  intro x y
  suffices 2 * B (f x) (f y) = 2 * B x y from h this
  have := hf (x + y)
  simp only [map_add, LinearMap.add_apply, hf x, hf y, show B y x = B x y from hB.eq y x] at this
  rw [show B (f y) (f x) = B (f x) (f y) from hB.eq (f y) (f x)] at this
  simp only [add_assoc, add_right_inj] at this
  simp only [← add_assoc, add_left_inj] at this
  simpa only [← two_mul] using this

end OrthogonalMap

end AdjointPair

/-! ### Self-adjoint pairs -/

section SelfadjointPair

section AddCommMonoid

variable [CommSemiring R]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R M₁]
variable {I : R →+* R}
variable (B F : M →ₗ[R] M →ₛₗ[I] M₁)

/-- The condition for an endomorphism to be "self-adjoint" with respect to a pair of bilinear maps
on the underlying module. In the case that these two maps are identical, this is the usual concept
of self adjointness. In the case that one of the maps is the negation of the other, this is the
usual concept of skew adjointness. -/
/-
**LinearMap.IsPairSelfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsPairSelfAdjoint (f : M -> M)
参数：f : M -> M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition for an endomorphism to be "self-adjoint" with respect to a pair of
 bilinear maps
on the underlying module. In the case that these two maps are identical, this is
 the usual concept
of self adjointness. In the case that one of the maps is the negation of the oth
er, this is the
usual concept of skew adjointness.
-/
def IsPairSelfAdjoint (f : M → M) :=
  IsAdjointPair B F f f

/-- An endomorphism of a module is self-adjoint with respect to a bilinear map if it serves as an
adjoint for itself. -/
/-
**LinearMap.IsSelfAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_5} →     {M₁ : Type u_6} →       [inst : Co
mmSemiring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.
Module R M] →             [inst_3 : AddCommMonoid M₁] →               [inst_4 : 
_root_.Module R M₁] → {I : R →+* R} → (M →ₗ[R] M →ₛₗ[I] M₁) → (M → M) → Prop
参数：M →ₗ[R] M →ₛₗ[I] M₁；M → M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An endomorphism of a module is self-adjoint with respect to a bilinear map if it
 serves as an
adjoint for itself.
-/
protected def IsSelfAdjoint (f : M → M) :=
  IsAdjointPair B B f f

end AddCommMonoid

section AddCommGroup

variable [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁]
variable [AddCommGroup M₂] [Module R M₂] (B F : M →ₗ[R] M →ₗ[R] M₂)

/-- The set of pair-self-adjoint endomorphisms are a submodule of the type of all endomorphisms. -/
/-
**LinearMap.isPairSelfAdjointSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of pair-self-adjoint endomorphisms are a submodule of the type of all en
domorphisms.
-/
def isPairSelfAdjointSubmodule : Submodule R (Module.End R M) where
  carrier := { f | IsPairSelfAdjoint B F f }
  zero_mem' := isAdjointPair_zero
  add_mem' hf hg := hf.add hg
  smul_mem' c _ h := h.smul c

/-- An endomorphism of a module is skew-adjoint with respect to a bilinear map if its negation
serves as an adjoint. -/
/-
**LinearMap.IsSkewAdjoint** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsSkewAdjoint (f : M -> M)
参数：f : M -> M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An endomorphism of a module is skew-adjoint with respect to a bilinear map if it
s negation
serves as an adjoint.
-/
def IsSkewAdjoint (f : M → M) :=
  IsAdjointPair B B f (-f)

/-- The set of self-adjoint endomorphisms of a module with bilinear map is a submodule. (In fact
it is a Jordan subalgebra.) -/
/-
**LinearMap.selfAdjointSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：selfAdjointSubmodule
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of self-adjoint endomorphisms of a module with bilinear map is a submodu
le. (In fact
it is a Jordan subalgebra.)
-/
def selfAdjointSubmodule :=
  isPairSelfAdjointSubmodule B B

/-- The set of skew-adjoint endomorphisms of a module with bilinear map is a submodule. (In fact
it is a Lie subalgebra.) -/
/-
**LinearMap.skewAdjointSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：skewAdjointSubmodule
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of skew-adjoint endomorphisms of a module with bilinear map is a submodu
le. (In fact
it is a Lie subalgebra.)
-/
def skewAdjointSubmodule :=
  isPairSelfAdjointSubmodule (-B) B

variable {B F}

@[simp]
/-
**LinearMap.mem_isPairSelfAdjointSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`
。
形式化陈述：mem_isPairSelfAdjointSubmodule (f : Module.End R M) : f in isPairSelfAdjoi
ntSubmodule B F ↔ IsPairSelfAdjoint B F f
参数：f : Module.End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_isPairSelfAdjointSubmodule (f : Module.End R M) :
    f ∈ isPairSelfAdjointSubmodule B F ↔ IsPairSelfAdjoint B F f :=
  Iff.rfl
/-
**LinearMap.isPairSelfAdjoint_equiv** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：isPairSelfAdjoint_equiv (e : M₁ ≃ₗ[R] M) (f : Module.End R M) : IsPairSelf
Adjoint B F f ↔ IsPairSelfAdjoint (B.compl₁₂ e e) (F.compl₁₂ e e) (e.symm.conj f
)
参数：e : M₁ ≃ₗ[R] M；f : Module.End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.compl₁₂_inj`：compl₁₂_inj [SMulCommClass R₂ R₁ Pₗ] {f₁ f₂ : Mₗ 
->ₗ[R₁] N ->ₗ[R₂] Pₗ} {g : Qₗ ->ₗ[R₁] Mₗ} {g' : Qₗ' ->ₗ[R₂] N} (hₗ : Function.Su
rjective g)…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isPairSelfAdjoint_equiv (e : M₁ ≃ₗ[R] M) (f : Module.End R M) :
    IsPairSelfAdjoint B F f ↔
      IsPairSelfAdjoint (B.compl₁₂ e e) (F.compl₁₂ e e) (e.symm.conj f) := by
  have hₗ :
    (F.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).comp (e.symm.conj f) =
      (F.comp f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, coe_comp, LinearEquiv.coe_coe, compl₁₂_apply,
      LinearEquiv.apply_symm_apply, Function.comp_apply]
  have hᵣ :
    (B.compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M)).compl₂ (e.symm.conj f) =
      (B.compl₂ f).compl₁₂ (↑e : M₁ →ₗ[R] M) (↑e : M₁ →ₗ[R] M) := by
    ext
    simp only [LinearEquiv.symm_conj_apply, compl₂_apply, coe_comp, LinearEquiv.coe_coe,
      compl₁₂_apply, LinearEquiv.apply_symm_apply, Function.comp_apply]
  have he : Function.Surjective (⇑(↑e : M₁ →ₗ[R] M) : M₁ → M) := e.surjective
  simp_rw [IsPairSelfAdjoint, isAdjointPair_iff_comp_eq_compl₂, hₗ, hᵣ, compl₁₂_inj he he]
/-
**LinearMap.isSkewAdjoint_iff_neg_self_adjoint** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map`。
形式化陈述：isSkewAdjoint_iff_neg_self_adjoint (f : M -> M) : B.IsSkewAdjoint f ↔ IsAd
jointPair (-B) B f f
参数：f : M -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSkewAdjoint_iff_neg_self_adjoint (f : M → M) :
    B.IsSkewAdjoint f ↔ IsAdjointPair (-B) B f f :=
  show (∀ x y, B (f x) y = B x ((-f) y)) ↔ ∀ x y, B (f x) y = (-B) x (f y) by simp

@[simp]
/-
**LinearMap.mem_selfAdjointSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_selfAdjointSubmodule (f : Module.End R M) : f in B.selfAdjointSubmodul
e ↔ B.IsSelfAdjoint f
参数：f : Module.End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_selfAdjointSubmodule (f : Module.End R M) :
    f ∈ B.selfAdjointSubmodule ↔ B.IsSelfAdjoint f :=
  Iff.rfl

@[simp]
/-
**LinearMap.mem_skewAdjointSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_skewAdjointSubmodule (f : Module.End R M) : f in B.skewAdjointSubmodul
e ↔ B.IsSkewAdjoint f
参数：f : Module.End R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.isSkewAdjoint_iff_neg_self_adjoint`：isSkewAdjoint_iff_neg_self
_adjoint (f : M -> M) : B.IsSkewAdjoint f ↔ IsAdjointPair (-B) B f f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_skewAdjointSubmodule (f : Module.End R M) :
    f ∈ B.skewAdjointSubmodule ↔ B.IsSkewAdjoint f := by
  rw [isSkewAdjoint_iff_neg_self_adjoint]
  exact Iff.rfl

end AddCommGroup

end SelfadjointPair

/-! ### Nondegenerate bilinear maps -/

section Nondegenerate

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring R₁] [AddCommMonoid M₁]
  [Module R₁ M₁] [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
  {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {I₁' : R₁ →+* R}

/-- A bilinear map is called left-separating if
the only element that is left-orthogonal to every other element is `0`; i.e.,
for every nonzero `x` in `M₁`, there exists `y` in `M₂` with `B x y ≠ 0`. -/
/-
**LinearMap.SeparatingLeft** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：SeparatingLeft (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear map is called left-separating if
the only element that is left-orthogonal to every other element is `0`; i.e.,
for every nonzero `x` in `M₁`, there exists `y` in `M₂` with `B x y ≠ 0`.
-/
def SeparatingLeft (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ x : M₁, (∀ y : M₂, B x y = 0) → x = 0

variable (M₁ M₂ I₁ I₂)

/-- In a non-trivial module, zero is not non-degenerate. -/
/-
**LinearMap.not_separatingLeft_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：not_separatingLeft_zero [Nontrivial M₁] : ¬(0 : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M)
.SeparatingLeft
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x

--- 原说明 ---
In a non-trivial module, zero is not non-degenerate.
-/
theorem not_separatingLeft_zero [Nontrivial M₁] : ¬(0 : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M).SeparatingLeft :=
  let ⟨m, hm⟩ := exists_ne (0 : M₁)
  fun h ↦ hm (h m fun _n ↦ rfl)

variable {M₁ M₂ I₁ I₂}
/-
**LinearMap.SeparatingLeft.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Separati
ngLeft`。
形式化陈述：∀ {R : Type u_1} {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_5} {M₁ : Type
 u_6} {M₂ : Type u_7} [inst : CommSemiring R]   [inst_1 : AddCommMonoid M] [inst
_2 : _root_.Module R M] [inst_3 : CommSemiring R₁] [inst_4 : AddCommMonoid M₁]  
 [inst_5 : _root_.Module R₁ M₁] [inst_6 : CommSemiring R₂] [inst_7 : AddCommMono
id M₂] [inst_8 : _root_.Module R₂ M₂]   {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} [Nontriv
ial M₁] {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}, B.SeparatingLeft → B ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.not_separatingLeft_zero`：not_separatingLeft_zero [Nontrivial M
₁] : ¬(0 : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M).SeparatingLeft
-/
theorem SeparatingLeft.ne_zero [Nontrivial M₁] {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}
    (h : B.SeparatingLeft) : B ≠ 0 := fun h0 ↦ not_separatingLeft_zero M₁ M₂ I₁ I₂ <| h0 ▸ h

/-- A bilinear map is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`. -/
/-
**LinearMap.SeparatingRight** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：SeparatingRight (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear map is called right-separating if
the only element that is right-orthogonal to every other element is `0`; i.e.,
for every nonzero `y` in `M₂`, there exists `x` in `M₁` with `B x y ≠ 0`.
-/
def SeparatingRight (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  ∀ y : M₂, (∀ x : M₁, B x y = 0) → y = 0

/-- A bilinear map is called non-degenerate if it is left-separating and right-separating. -/
/-
**LinearMap.Nondegenerate** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：Nondegenerate (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear map is called non-degenerate if it is left-separating and right-separ
ating.
-/
def Nondegenerate (B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M) : Prop :=
  SeparatingLeft B ∧ SeparatingRight B

section Linear

variable [AddCommMonoid Mₗ₁] [AddCommMonoid Mₗ₂] [AddCommMonoid Mₗ₁'] [AddCommMonoid Mₗ₂']

variable [Module R Mₗ₁] [Module R Mₗ₂] [Module R Mₗ₁'] [Module R Mₗ₂']
variable {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] M} (e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂')

/-
**LinearMap.SeparatingLeft.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Separating
Left`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : Type u_9} {Mₗ₁' : Type u_10} {Mₗ₂ :
 Type u_11} {Mₗ₂' : Type u_12}   [inst : CommSemiring R] [inst_1 : AddCommMonoid
 M] [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid Mₗ₁]   [inst_4 : AddCom
mMonoid Mₗ₂] [inst_5 : AddCommMonoid Mₗ₁'] [inst_6 : AddCommMonoid Mₗ₂']   [inst
_7 : _root_.Module R Mₗ₁] [inst_8 : _root_.Module R Mₗ₂] [inst_9 : _root_.Module
 R Mₗ₁']   [inst_10 : _root_.Module R Mₗ₂'] {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] M} (e₁ : Mₗ
₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'),   B.SeparatingLeft → ((e₁.arrowCongr (e₂.ar
rowCongr (LinearEquiv.refl R M))) B).SeparatingLeft
参数：e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁'；e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'；(e₁.arrowCongr (e₂.arrowCongr (Linear
Equiv.refl R M))) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.map_eq_zero_iff`：map_eq_zero_iff {x : M} : e x = 0 ↔ x = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem SeparatingLeft.congr (h : B.SeparatingLeft) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft := by
  intro x hx
  rw [← e₁.symm.map_eq_zero_iff]
  refine h (e₁.symm x) fun y ↦ ?_
  specialize hx (e₂ y)
  simp only [LinearEquiv.arrowCongr_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.map_eq_zero_iff] at hx
  exact hx
/-
**LinearMap.SeparatingRight.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Separatin
gRight`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : Type u_9} {Mₗ₁' : Type u_10} {Mₗ₂ :
 Type u_11} {Mₗ₂' : Type u_12}   [inst : CommSemiring R] [inst_1 : AddCommMonoid
 M] [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid Mₗ₁]   [inst_4 : AddCom
mMonoid Mₗ₂] [inst_5 : AddCommMonoid Mₗ₁'] [inst_6 : AddCommMonoid Mₗ₂']   [inst
_7 : _root_.Module R Mₗ₁] [inst_8 : _root_.Module R Mₗ₂] [inst_9 : _root_.Module
 R Mₗ₁']   [inst_10 : _root_.Module R Mₗ₂'] {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] M} (e₁ : Mₗ
₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'),   B.SeparatingRight → ((e₁.arrowCongr (e₂.a
rrowCongr (LinearEquiv.refl R M))) B).SeparatingRight
参数：e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁'；e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'；(e₁.arrowCongr (e₂.arrowCongr (Linear
Equiv.refl R M))) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.SeparatingLeft.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : T
ype u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : CommS
emiring R] [inst_1 :…
-/
theorem SeparatingRight.congr (h : B.SeparatingRight) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingRight :=
  SeparatingLeft.congr (B := B.flip) e₂ e₁ h
/-
**LinearMap.Nondegenerate.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Nondegenera
te`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : Type u_9} {Mₗ₁' : Type u_10} {Mₗ₂ :
 Type u_11} {Mₗ₂' : Type u_12}   [inst : CommSemiring R] [inst_1 : AddCommMonoid
 M] [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid Mₗ₁]   [inst_4 : AddCom
mMonoid Mₗ₂] [inst_5 : AddCommMonoid Mₗ₁'] [inst_6 : AddCommMonoid Mₗ₂']   [inst
_7 : _root_.Module R Mₗ₁] [inst_8 : _root_.Module R Mₗ₂] [inst_9 : _root_.Module
 R Mₗ₁']   [inst_10 : _root_.Module R Mₗ₂'] {B : Mₗ₁ →ₗ[R] Mₗ₂ →ₗ[R] M} (e₁ : Mₗ
₁ ≃ₗ[R] Mₗ₁') (e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'),   B.Nondegenerate → ((e₁.arrowCongr (e₂.arr
owCongr (LinearEquiv.refl R M))) B).Nondegenerate
参数：e₁ : Mₗ₁ ≃ₗ[R] Mₗ₁'；e₂ : Mₗ₂ ≃ₗ[R] Mₗ₂'；(e₁.arrowCongr (e₂.arrowCongr (Linear
Equiv.refl R M))) B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.SeparatingLeft.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : T
ype u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : CommS
emiring R] [inst_1 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.SeparatingRight.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : 
Type u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : Comm
Semiring R] [inst_1 :…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Nondegenerate.congr (h : B.Nondegenerate) :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).Nondegenerate :=
  ⟨h.1.congr e₁ e₂, h.2.congr e₁ e₂⟩

@[simp]
/-
**LinearMap.separatingLeft_congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：separatingLeft_congr_iff : (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl
 R M)) B).SeparatingLeft ↔ B.SeparatingLeft
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.SeparatingLeft.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : T
ype u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : CommS
emiring R] [inst_1 :…
-/
theorem separatingLeft_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft ↔ B.SeparatingLeft :=
  ⟨fun h ↦ by
    convert! h.congr e₁.symm e₂.symm
    ext x y
    simp,
   SeparatingLeft.congr e₁ e₂⟩

@[simp]
/-
**LinearMap.separatingRight_congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：separatingRight_congr_iff : (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.ref
l R M)) B).SeparatingRight ↔ B.SeparatingRight
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.separatingLeft_congr_iff`：separatingLeft_congr_iff : (e₁.arrow
Congr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft ↔ B.SeparatingLef
t
-/
theorem separatingRight_congr_iff : (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M))
      B).SeparatingRight ↔ B.SeparatingRight :=
  separatingLeft_congr_iff (B := B.flip) e₂ e₁

@[simp]
/-
**LinearMap.nondegenerate_congr_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：nondegenerate_congr_iff : (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl 
R M)) B).Nondegenerate ↔ B.Nondegenerate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.separatingLeft_congr_iff`：separatingLeft_congr_iff : (e₁.arrow
Congr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingLeft ↔ B.SeparatingLef
t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearMap.separatingRight_congr_iff`：separatingRight_congr_iff : (e₁.arr
owCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).SeparatingRight ↔ B.Separating
Right
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearMap.Nondegenerate.congr`：∀ {R : Type u_1} {M : Type u_5} {Mₗ₁ : Ty
pe u_9} {Mₗ₁' : Type u_10} {Mₗ₂ : Type u_11} {Mₗ₂' : Type u_12}   [inst : CommSe
miring R] [inst_1 :…
-/
theorem nondegenerate_congr_iff :
    (e₁.arrowCongr (e₂.arrowCongr (LinearEquiv.refl R M)) B).Nondegenerate ↔ B.Nondegenerate :=
  ⟨fun h ↦ ⟨separatingLeft_congr_iff e₁ e₂ |>.mp h.1, separatingRight_congr_iff e₁ e₂ |>.mp h.2⟩,
    .congr e₁ e₂⟩

end Linear

@[simp]
/-
**LinearMap.flip_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_separatingRight {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.flip.SeparatingRi
ght ↔ B.SeparatingLeft
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem flip_separatingRight {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.flip.SeparatingRight ↔ B.SeparatingLeft :=
  ⟨fun hB x hy ↦ hB x hy, fun hB x hy ↦ hB x hy⟩

@[simp]
/-
**LinearMap.flip_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_separatingLeft {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.flip.SeparatingLef
t ↔ SeparatingRight B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip_separatingRight`：flip_separatingRight {B : M₁ ->ₛₗ[I₁] M₂
 ->ₛₗ[I₂] M} : B.flip.SeparatingRight ↔ B.SeparatingLeft
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_flip`：flip_flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : f.flip.
flip = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem flip_separatingLeft {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.flip.SeparatingLeft ↔ SeparatingRight B := by rw [← flip_separatingRight, flip_flip]

@[simp]
/-
**LinearMap.flip_nondegenerate** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：flip_nondegenerate {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.flip.Nondegenerate 
↔ B.Nondegenerate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `LinearMap.flip_separatingRight`：flip_separatingRight {B : M₁ ->ₛₗ[I₁] M₂
 ->ₛₗ[I₂] M} : B.flip.SeparatingRight ↔ B.SeparatingLeft
· 使用定理 `LinearMap.flip_separatingLeft`：flip_separatingLeft {B : M₁ ->ₛₗ[I₁] M₂ -
>ₛₗ[I₂] M} : B.flip.SeparatingLeft ↔ SeparatingRight B
-/
theorem flip_nondegenerate {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} : B.flip.Nondegenerate ↔ B.Nondegenerate :=
  Iff.trans and_comm (and_congr flip_separatingRight flip_separatingLeft)
/-
**LinearMap.separatingLeft_iff_linear_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：separatingLeft_iff_linear_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.S
eparatingLeft ↔ forall x : M₁, B x = 0 -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
-/
theorem separatingLeft_iff_linear_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ ∀ x : M₁, B x = 0 → x = 0 := by
  constructor <;> intro h x hB
  · simpa only [hB, zero_apply, eq_self_iff_true, forall_const] using h x
  have h' : B x = 0 := by
    ext
    rw [zero_apply]
    exact hB _
  exact h x h'
/-
**LinearMap.separatingRight_iff_linear_flip_nontrivial** 是 Mathlib 中的一个定理，位于命名空间
 `LinearMap`。
形式化陈述：separatingRight_iff_linear_flip_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M}
 : B.SeparatingRight ↔ forall y : M₂, B.flip y = 0 -> y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip_separatingLeft`：flip_separatingLeft {B : M₁ ->ₛₗ[I₁] M₂ -
>ₛₗ[I₂] M} : B.flip.SeparatingLeft ↔ SeparatingRight B
· 使用定理 `LinearMap.separatingLeft_iff_linear_nontrivial`：separatingLeft_iff_linea
r_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ forall x : M₁,
 B x = 0 -> x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem separatingRight_iff_linear_flip_nontrivial {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingRight ↔ ∀ y : M₂, B.flip y = 0 → y = 0 := by
  rw [← flip_separatingLeft, separatingLeft_iff_linear_nontrivial]

/-- A bilinear map is left-separating if and only if it has a trivial kernel. -/
/-
**LinearMap.separatingLeft_iff_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：separatingLeft_iff_ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.Separati
ngLeft ↔ LinearMap.ker B = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.separatingLeft_iff_linear_nontrivial`：separatingLeft_iff_linea
r_nontrivial {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ forall x : M₁,
 B x = 0 -> x = 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0

--- 原说明 ---
A bilinear map is left-separating if and only if it has a trivial kernel.
-/
theorem separatingLeft_iff_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingLeft ↔ LinearMap.ker B = ⊥ :=
  Iff.trans separatingLeft_iff_linear_nontrivial LinearMap.ker_eq_bot'.symm

/-- A bilinear map is right-separating if and only if its flip has a trivial kernel. -/
/-
**LinearMap.separatingRight_iff_flip_ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：separatingRight_iff_flip_ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.Se
paratingRight ↔ LinearMap.ker B.flip = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip_separatingLeft`：flip_separatingLeft {B : M₁ ->ₛₗ[I₁] M₂ -
>ₛₗ[I₂] M} : B.flip.SeparatingLeft ↔ SeparatingRight B
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A bilinear map is right-separating if and only if its flip has a trivial kernel.
-/
theorem separatingRight_iff_flip_ker_eq_bot {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M} :
    B.SeparatingRight ↔ LinearMap.ker B.flip = ⊥ := by
  rw [← flip_separatingLeft, separatingLeft_iff_ker_eq_bot]

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R →+* R}

/-
**LinearMap.IsRefl.nondegenerate_iff_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.IsRefl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_
1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup M₁] [i
nst_4 : _root_.Module R M₁] {B : M →ₗ[R] M →ₗ[R] M₁},   B.IsRefl → (B.Nondegener
ate ↔ B.SeparatingLeft)
参数：B.Nondegenerate ↔ B.SeparatingLeft。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingRight_iff_flip_ker_eq_bot`：separatingRight_iff_flip_
ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingRight ↔ LinearMap.ker B
.flip = ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.IsRefl.ker_eq_bot_iff_ker_flip_eq_bot`：ker_eq_bot_iff_ker_flip
_eq_bot (H : B.IsRefl) : LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
-/
theorem IsRefl.nondegenerate_iff_separatingLeft {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingLeft := by
  refine ⟨fun h ↦ h.1, fun hB' ↦ ⟨hB', ?_⟩⟩
  rw [separatingRight_iff_flip_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mp]
  rwa [← separatingLeft_iff_ker_eq_bot]
/-
**LinearMap.IsRefl.nondegenerate_iff_separatingRight** 是 Mathlib 中的一个定理，位于命名空间 `
LinearMap.IsRefl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_
1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup M₁] [i
nst_4 : _root_.Module R M₁] {B : M →ₗ[R] M →ₗ[R] M₁},   B.IsRefl → (B.Nondegener
ate ↔ B.SeparatingRight)
参数：B.Nondegenerate ↔ B.SeparatingRight。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsRefl.ker_eq_bot_iff_ker_flip_eq_bot`：ker_eq_bot_iff_ker_flip
_eq_bot (H : B.IsRefl) : LinearMap.ker B = ⊥ ↔ LinearMap.ker B.flip = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.separatingRight_iff_flip_ker_eq_bot`：separatingRight_iff_flip_
ker_eq_bot {B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingRight ↔ LinearMap.ker B
.flip = ⊥
-/
theorem IsRefl.nondegenerate_iff_separatingRight {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl) :
    B.Nondegenerate ↔ B.SeparatingRight := by
  refine ⟨fun h ↦ h.2, fun hB' ↦ ⟨?_, hB'⟩⟩
  rw [separatingLeft_iff_ker_eq_bot, hB.ker_eq_bot_iff_ker_flip_eq_bot.mpr]
  rwa [← separatingRight_iff_flip_ker_eq_bot]
/-
**LinearMap.disjoint_ker_of_nondegenerate_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap`。
形式化陈述：disjoint_ker_of_nondegenerate_restrict {B : M ->ₗ[R] M ->ₗ[R] M₁} {W : Sub
module R M} (hW : (B.domRestrict₁₂ W W).Nondegenerate) : Disjoint W (LinearMap.k
er B)
参数：hW : (B.domRestrict₁₂ W W).Nondegenerate。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma disjoint_ker_of_nondegenerate_restrict {B : M →ₗ[R] M →ₗ[R] M₁} {W : Submodule R M}
    (hW : (B.domRestrict₁₂ W W).Nondegenerate) :
    Disjoint W (LinearMap.ker B) := by
  refine Submodule.disjoint_def.mpr fun x hx hx' ↦ ?_
  let x' : W := ⟨x, hx⟩
  suffices x' = 0 by simpa [x']
  apply hW.1 x'
  simp_rw [Subtype.forall, domRestrict₁₂_apply]
  intro y hy
  rw [mem_ker] at hx'
  simp [x', hx']
/-
**LinearMap.IsSymm.nondegenerate_restrict_of_isCompl_ker** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.IsSymm`。
形式化陈述：∀ {R : Type u_1} {M : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {B : M →ₗ[R] M →ₗ[R] R}, B.IsSymm → ∀ {W : Su
bmodule R M}, IsCompl W B.ker → (B.domRestrict₁₂ W W).Nondegenerate
参数：B.domRestrict₁₂ W W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `IsCompl.sup_eq_top`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : Bounde
dOrder α] {x y : α}, IsCompl x y → x ⊔ y = ⊤
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `IsCompl.inf_eq_bot`：inf_eq_bot (h : IsCompl x y) : x ⊓ y = ⊥
-/
lemma IsSymm.nondegenerate_restrict_of_isCompl_ker {B : M →ₗ[R] M →ₗ[R] R} (hB : B.IsSymm)
    {W : Submodule R M} (hW : IsCompl W (LinearMap.ker B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y ↦ hB.isRefl (W.subtype x) (W.subtype y)
  rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ hx'
  simp only [Submodule.mk_eq_zero]
  replace hx' : ∀ y ∈ W, B x y = 0 := by simpa [Subtype.forall] using! hx'
  replace hx' : x ∈ W ⊓ ker B := by
    refine ⟨hx, ?_⟩
    ext y
    obtain ⟨u, hu, v, hv, rfl⟩ : ∃ u ∈ W, ∃ v ∈ ker B, u + v = y := by
      rw [← Submodule.mem_sup, hW.sup_eq_top]; exact Submodule.mem_top
    suffices B x u = 0 by rw [mem_ker] at hv; simpa [← hB.eq v, hv]
    exact hx' u hu
  simpa [hW.inf_eq_bot] using! hx'

end CommRing

section IsOrthoᵢ

variable {R M M₁ : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁]
    [Module R M] [Module R M₁] {I I' : R →+* R} {B : M →ₛₗ[I] M →ₛₗ[I'] M₁}

/-- An orthogonal basis with respect to a left-separating bilinear map has no self-orthogonal
elements. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthogonal basis with respect to a left-separating bilinear map has no self-o
rthogonal
elements.
-/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingLeft [Nontrivial R]
    {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingLeft)
    (i : n) : B (v i) (v i) ≠ 0 := by
  intro ho
  refine v.ne_zero i (hB (v i) fun m ↦ ?_)
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  apply Finset.sum_eq_zero
  rintro j -
  rw [map_smulₛₗ]
  suffices B (v i) (v j) = 0 by rw [this, smul_zero]
  obtain rfl | hij := eq_or_ne i j
  · exact ho
  · exact h hij

/-- An orthogonal basis with respect to a right-separating bilinear map has no self-orthogonal
elements. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orthogonal basis with respect to a right-separating bilinear map has no self-
orthogonal
elements.
-/
theorem IsOrthoᵢ.not_isOrtho_basis_self_of_separatingRight [Nontrivial R]
    {v : Basis n R M} (h : B.IsOrthoᵢ v) (hB : B.SeparatingRight)
    (i : n) : B (v i) (v i) ≠ 0 := by
  rw [isOrthoᵢ_flip] at h
  exact h.not_isOrtho_basis_self_of_separatingLeft (flip_separatingLeft.mpr hB) i

variable [IsDomain R] [IsTorsionFree R M₁]

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is left-separating if
the basis has no elements which are self-orthogonal. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an orthogonal basis with respect to a bilinear map, the bilinear map is le
ft-separating if
the basis has no elements which are self-orthogonal.
-/
theorem IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : ∀ i, B (v i) (v i) ≠ 0) : B.SeparatingLeft := by
  intro m hB
  obtain ⟨vi, rfl⟩ := v.repr.symm.surjective m
  rw [LinearEquiv.map_eq_zero_iff]
  ext i
  rw [Finsupp.zero_apply]
  specialize hB (v i)
  simp_rw [Basis.repr_symm_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum₂,
           map_smulₛₗ₂] at hB
  rw [Finset.sum_eq_single i] at hB
  · cases smul_eq_zero.mp hB
    · assumption
    · specialize h i
      contradiction
  · intro j _hj hij
    replace hij : B (v j) (v i) = 0 := hO hij
    rw [hij, RingHom.id_apply, smul_zero]
  · intro hi
    replace hi : vi i = 0 := Finsupp.notMem_support_iff.mp hi
    rw [hi, RingHom.id_apply, zero_smul]

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is right-separating
if the basis has no elements which are self-orthogonal. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an orthogonal basis with respect to a bilinear map, the bilinear map is ri
ght-separating
if the basis has no elements which are self-orthogonal.
-/
lemma IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : ∀ i, B (v i) (v i) ≠ 0) : B.SeparatingRight := by
  rw [isOrthoᵢ_flip] at hO
  rw [← flip_separatingLeft]
  refine IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO fun i ↦ ?_
  exact h i

/-- Given an orthogonal basis with respect to a bilinear map, the bilinear map is nondegenerate
if the basis has no elements which are self-orthogonal. -/
/-
**LinearMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：IsOrtho (B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M) (x : M₁) (y : M₂) : Prop
参数：B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M；x : M₁；y : M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an orthogonal basis with respect to a bilinear map, the bilinear map is no
ndegenerate
if the basis has no elements which are self-orthogonal.
-/
theorem IsOrthoᵢ.nondegenerate_of_not_isOrtho_basis_self {B : M →ₗ[R] M →ₗ[R] M₁} (v : Basis n R M)
    (hO : B.IsOrthoᵢ v) (h : ∀ i, B (v i) (v i) ≠ 0) : B.Nondegenerate :=
  ⟨IsOrthoᵢ.separatingLeft_of_not_isOrtho_basis_self v hO h,
    IsOrthoᵢ.separatingRight_iff_not_isOrtho_basis_self v hO h⟩

end IsOrthoᵢ

end Nondegenerate

namespace BilinForm

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.BilinForm.apply_smul_sub_smul_sub_eq** 是 Mathlib 中的一个引理，位于命名空间 `Line
arMap.BilinForm`。
形式化陈述：apply_smul_sub_smul_sub_eq [CommRing R] [AddCommGroup M] [Module R M] (B :
 LinearMap.BilinForm R M) (x y : M) : B ((B x y) • x - (B x x) • y) ((B x y) • x
 - (B x x) • y) = (B x x) * ((B x x) * (B y y) - (B x y) * (B y x))
参数：B : LinearMap.BilinForm R M；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `_private.Mathlib.LinearAlgebra.SesquilinearForm.Basic.0.LinearMap.BilinF
orm.apply_smul_sub_smul_sub_eq._abel_1_1`：∀ {R : Type u_1} {M : Type u_2} [inst 
: CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (B : Line
arMap.BilinForm R M) (…
-/
lemma apply_smul_sub_smul_sub_eq [CommRing R] [AddCommGroup M] [Module R M]
    (B : LinearMap.BilinForm R M) (x y : M) :
    B ((B x y) • x - (B x x) • y) ((B x y) • x - (B x x) • y) =
      (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
  simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul, mul_sub,
    mul_comm (B x y) (B x x), mul_left_comm (B x y) (B x x)]
  abel

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M)

/-- The **Cauchy-Schwarz inequality** for positive semidefinite forms. -/
@[wikidata Q190546]
/-
**LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le** 是 Mathlib 中的一个引理，位于
命名空间 `LinearMap.BilinForm`。
形式化陈述：apply_mul_apply_le_of_forall_zero_le (hs : forall x, 0 <= B x x) (x y : M)
 : (B x y) * (B y x) <= (B x x) * (B y y)
参数：hs : forall x, 0 <= B x x；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.BilinForm.apply_smul_sub_smul_sub_eq`：apply_smul_sub_smul_sub_
eq [CommRing R] [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M) (x y
 : M) : B ((B x y) • x - (B x x) • y…
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `nonneg_of_mul_nonneg_right`：nonneg_of_mul_nonneg_right [PosMulStrictMono
 R] (h : 0 <= a * b) (ha : 0 < a) : 0 <= b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `mul_self_nonneg`：mul_self_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLe
ftMono R] (a : R) : 0 <= a * a
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The **Cauchy-Schwarz inequality** for positive semidefinite forms.
-/
lemma apply_mul_apply_le_of_forall_zero_le (hs : ∀ x, 0 ≤ B x x) (x y : M) :
    (B x y) * (B y x) ≤ (B x x) * (B y y) := by
  have aux (x y : M) : 0 ≤ (B x x) * ((B x x) * (B y y) - (B x y) * (B y x)) := by
    rw [← apply_smul_sub_smul_sub_eq B x y]
    exact hs (B x y • x - B x x • y)
  rcases lt_or_ge 0 (B x x) with hx | hx
  · exact sub_nonneg.mp <| nonneg_of_mul_nonneg_right (aux x y) hx
  · replace hx : B x x = 0 := le_antisymm hx (hs x)
    rcases lt_or_ge 0 (B y y) with hy | hy
    · rw [mul_comm (B x y), mul_comm (B x x)]
      exact sub_nonneg.mp <| nonneg_of_mul_nonneg_right (aux y x) hy
    · replace hy : B y y = 0 := le_antisymm hy (hs y)
      suffices B x y = - B y x by simpa [this, hx, hy] using mul_self_nonneg (B y x)
      rw [eq_neg_iff_add_eq_zero]
      apply le_antisymm
      · simpa [hx, hy, le_neg_iff_add_nonpos_left] using hs (x - y)
      · simpa [hx, hy] using hs (x + y)

/-- The **Cauchy-Schwarz inequality** for positive semidefinite symmetric forms. -/
/-
**LinearMap.BilinForm.apply_sq_le_of_symm** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.B
ilinForm`。
形式化陈述：apply_sq_le_of_symm (hs : forall x, 0 <= B x x) (hB : B.IsSymm) (x y : M) 
: (B x y) ^ 2 <= (B x x) * (B y y)
参数：hs : forall x, 0 <= B x x；hB : B.IsSymm；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用引理 `LinearMap.BilinForm.apply_mul_apply_le_of_forall_zero_le`：apply_mul_appl
y_le_of_forall_zero_le (hs : forall x, 0 <= B x x) (x y : M) : (B x y) * (B y x)
 <= (B x x) * (B y y)

--- 原说明 ---
The **Cauchy-Schwarz inequality** for positive semidefinite symmetric forms.
-/
lemma apply_sq_le_of_symm (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) (x y : M) :
    (B x y) ^ 2 ≤ (B x x) * (B y y) := by
  rw [show (B x y) ^ 2 = (B x y) * (B y x) by rw [sq, ← hB.eq, RingHom.id_apply]]
  exact apply_mul_apply_le_of_forall_zero_le B hs x y

/-- The equality case of **Cauchy-Schwarz**. -/
/-
**LinearMap.BilinForm.not_linearIndependent_of_apply_mul_apply_eq** 是 Mathlib 中的
一个引理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：not_linearIndependent_of_apply_mul_apply_eq (hp : forall x, x != 0 -> 0 < 
B x x) (x y : M) (he : (B x y) * (B y x) = (B x x) * (B y y)) : ¬ LinearIndepend
ent R ![x, y]
参数：hp : forall x, x != 0 -> 0 < B x x；x y : M；he : (B x y) * (B y x) = (B x x) *
 (B y y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `mul_eq_zero_of_right`：mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0)
 : a * b = 0
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.BilinForm.apply_smul_sub_smul_sub_eq`：apply_smul_sub_smul_sub_
eq [CommRing R] [AddCommGroup M] [Module R M] (B : LinearMap.BilinForm R M) (x y
 : M) : B ((B x y) • x - (B x x) • y…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `LinearIndependent.eq_zero_of_pair`：LinearIndependent.eq_zero_of_pair {x 
y : M} (h : LinearIndependent R ![x, y]) {s t : R} (h' : s • x + t • y = 0) : s 
= 0 ∧ t = 0
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b

--- 原说明 ---
The equality case of **Cauchy-Schwarz**.
-/
lemma not_linearIndependent_of_apply_mul_apply_eq (hp : ∀ x, x ≠ 0 → 0 < B x x)
    (x y : M) (he : (B x y) * (B y x) = (B x x) * (B y y)) :
    ¬ LinearIndependent R ![x, y] := by
  have hz : (B x y) • x - (B x x) • y = 0 := by
    by_contra hc
    exact (ne_of_lt (hp ((B x) y • x - (B x) x • y) hc)).symm <|
      (apply_smul_sub_smul_sub_eq B x y).symm ▸ (mul_eq_zero_of_right ((B x) x)
      (sub_eq_zero_of_eq he.symm))
  by_contra hL
  by_cases hx : x = 0
  · simpa [hx] using LinearIndependent.ne_zero 0 hL
  · have h := sub_eq_zero.mpr (sub_eq_zero.mp hz).symm
    rw [sub_eq_add_neg, ← neg_smul, add_comm] at h
    exact (Ne.symm (ne_of_lt (hp x hx))) (LinearIndependent.eq_zero_of_pair hL h).2
/-
**LinearMap.BilinForm.apply_apply_same_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Li
nearMap.BilinForm`。
形式化陈述：apply_apply_same_eq_zero_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {
x : M} : B x x = 0 ↔ x in LinearMap.ker B
参数：hs : forall x, 0 <= B x x；hB : B.IsSymm。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `LinearMap.BilinForm.apply_sq_le_of_symm`：apply_sq_le_of_symm (hs : foral
l x, 0 <= B x x) (hB : B.IsSymm) (x y : M) : (B x y) ^ 2 <= (B x x) * (B y y)
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma apply_apply_same_eq_zero_iff (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) {x : M} :
    B x x = 0 ↔ x ∈ LinearMap.ker B := by
  rw [LinearMap.mem_ker]
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  ext y
  have := B.apply_sq_le_of_symm hs hB x y
  simp only [h, zero_mul] at this
  exact eq_zero_of_pow_eq_zero <| le_antisymm this (sq_nonneg (B x y))
/-
**LinearMap.BilinForm.nondegenerate_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bil
inForm`。
形式化陈述：nondegenerate_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) : B.Nondegen
erate ↔ forall x, B x x = 0 ↔ x = 0
参数：hs : forall x, 0 <= B x x；hB : B.IsSymm。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `LinearMap.BilinForm.apply_apply_same_eq_zero_iff`：apply_apply_same_eq_ze
ro_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {x : M} : B x x = 0 ↔ x in Li
nearMap.ker B
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma nondegenerate_iff (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ ∀ x, B x x = 0 ↔ x = 0 := by
  simp_rw [hB.isRefl.nondegenerate_iff_separatingLeft, separatingLeft_iff_ker_eq_bot,
    Submodule.eq_bot_iff, B.apply_apply_same_eq_zero_iff hs hB, mem_ker]
  exact forall_congr' fun x ↦ by aesop

/-- A convenience variant of `LinearMap.BilinForm.nondegenerate_iff` characterising nondegeneracy as
positive definiteness. -/
/-
**LinearMap.BilinForm.nondegenerate_iff'** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Bi
linForm`。
形式化陈述：nondegenerate_iff' (hs : forall x, 0 <= B x x) (hB : B.IsSymm) : B.Nondege
nerate ↔ forall x, x != 0 -> 0 < B x x
参数：hs : forall x, 0 <= B x x；hB : B.IsSymm。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.BilinForm.nondegenerate_iff`：nondegenerate_iff (hs : forall x,
 0 <= B x x) (hB : B.IsSymm) : B.Nondegenerate ↔ forall x, B x x = 0 ↔ x = 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
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
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b

--- 原说明 ---
A convenience variant of `LinearMap.BilinForm.nondegenerate_iff` characterising 
nondegeneracy as
positive definiteness.
-/
lemma nondegenerate_iff' (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm) :
    B.Nondegenerate ↔ ∀ x, x ≠ 0 → 0 < B x x := by
  rw [B.nondegenerate_iff hs hB]
  contrapose!
  exact exists_congr fun x ↦ ⟨by aesop, fun ⟨h₀, h⟩ ↦ Or.inl ⟨le_antisymm h (hs x), h₀⟩⟩
/-
**LinearMap.BilinForm.nondegenerate_restrict_iff_disjoint_ker** 是 Mathlib 中的一个引理
，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：nondegenerate_restrict_iff_disjoint_ker (hs : forall x, 0 <= B x x) (hB : 
B.IsSymm) {W : Submodule R M} : (B.domRestrict₁₂ W W).Nondegenerate ↔ Disjoint W
 (LinearMap.ker B)
参数：hs : forall x, 0 <= B x x；hB : B.IsSymm。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LinearMap.disjoint_ker_of_nondegenerate_restrict`：disjoint_ker_of_nondeg
enerate_restrict {B : M ->ₗ[R] M ->ₗ[R] M₁} {W : Submodule R M} (hW : (B.domRest
rict₁₂ W W).Nondegenerate) : Disjoint …
· 使用定理 `LinearMap.IsSymm.isRefl`：isRefl (H : B.IsSymm) : B.IsRefl
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用引理 `LinearMap.BilinForm.apply_apply_same_eq_zero_iff`：apply_apply_same_eq_ze
ro_iff (hs : forall x, 0 <= B x x) (hB : B.IsSymm) {x : M} : B x x = 0 ↔ x in Li
nearMap.ker B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Disjoint.eq_bot`：Disjoint.eq_bot : Disjoint a b -> a ⊓ b = ⊥
-/
lemma nondegenerate_restrict_iff_disjoint_ker (hs : ∀ x, 0 ≤ B x x) (hB : B.IsSymm)
    {W : Submodule R M} :
    (B.domRestrict₁₂ W W).Nondegenerate ↔ Disjoint W (LinearMap.ker B) := by
  refine ⟨disjoint_ker_of_nondegenerate_restrict, fun hW ↦ ?_⟩
  have hB' : (B.domRestrict₁₂ W W).IsRefl := fun x y ↦ hB.isRefl (W.subtype x) (W.subtype y)
  rw [IsRefl.nondegenerate_iff_separatingLeft hB']
  intro ⟨x, hx⟩ h
  simp_rw [Subtype.forall, domRestrict₁₂_apply] at h
  specialize h x hx
  rw [B.apply_apply_same_eq_zero_iff hs hB] at h
  have key : x ∈ W ⊓ LinearMap.ker B := ⟨hx, h⟩
  simpa [hW.eq_bot] using key

variable [IsTorsionFree R M]

set_option backward.isDefEq.respectTransparency false in
/-- Strict **Cauchy-Schwarz** is equivalent to linear independence for positive definite forms. -/
/-
**LinearMap.BilinForm.apply_mul_apply_lt_iff_linearIndependent** 是 Mathlib 中的一个引
理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：apply_mul_apply_lt_iff_linearIndependent (hp : forall x, x != 0 -> 0 < B x
 x) (x y : M) : B x y * B y x < B x x * B y y ↔ LinearIndependent R ![x, y]
参数：hp : forall x, x != 0 -> 0 < B x x；x y : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 62 条，此处仅展示前 30 条）

--- 原说明 ---
Strict **Cauchy-Schwarz** is equivalent to linear independence for positive defi
nite forms.
-/
lemma apply_mul_apply_lt_iff_linearIndependent (hp : ∀ x, x ≠ 0 → 0 < B x x) (x y : M) :
    B x y * B y x < B x x * B y y ↔ LinearIndependent R ![x, y] := by
  have hle z : 0 ≤ B z z := by obtain rfl | hz := eq_or_ne z 0 <;> simp [le_of_lt, *]
  constructor
  · contrapose!
    intro h
    rw [LinearIndependent.pair_iff] at h
    push Not at h
    obtain ⟨r, s, hl, h0⟩ := h
    by_cases hr : r = 0; · simp_all
    by_cases hs : s = 0; · simp_all
    suffices
        (B (r • x) (r • x)) * (B (s • y) (s • y)) = (B (r • x) (s • y)) * (B (s • y) (r • x)) by
      simp only [map_smul, smul_apply, smul_eq_mul] at this
      rw [show r * (r * (B x) x) * (s * (s * (B y) y)) = (r * r * s * s) * ((B x) x * (B y) y) by
        ring, show s * (r * (B x) y) * (r * (s * (B y) x)) = (r * r * s * s) * ((B x) y * (B y) x)
        by ring] at this
      have hrs : r * r * s * s ≠ 0 := by simp [hr, hs]
      exact le_of_eq <| mul_right_injective₀ hrs this
    simp [show s • y = - r • x by rwa [neg_smul, ← add_eq_zero_iff_eq_neg']]
  · contrapose!
    intro h
    exact not_linearIndependent_of_apply_mul_apply_eq B hp x y (le_antisymm
      (apply_mul_apply_le_of_forall_zero_le B hle x y) h)

/-- Strict **Cauchy-Schwarz** is equivalent to linear independence for positive definite symmetric
forms. -/
/-
**LinearMap.BilinForm.apply_sq_lt_iff_linearIndependent_of_symm** 是 Mathlib 中的一个
引理，位于命名空间 `LinearMap.BilinForm`。
形式化陈述：apply_sq_lt_iff_linearIndependent_of_symm (hp : forall x, x != 0 -> 0 < B 
x x) (hB : B.IsSymm) (x y : M) : B x y ^ 2 < B x x * B y y ↔ LinearIndependent R
 ![x, y]
参数：hp : forall x, x != 0 -> 0 < B x x；hB : B.IsSymm；x y : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsSymm.eq`：∀ {R : Type u_1} {M : Type u_5} [inst : CommSemirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {I : R →+* R} {B 
: M →ₛₗ[I…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用引理 `LinearMap.BilinForm.apply_mul_apply_lt_iff_linearIndependent`：apply_mul_
apply_lt_iff_linearIndependent (hp : forall x, x != 0 -> 0 < B x x) (x y : M) : 
B x y * B y x < B x x * B y y ↔ LinearIndependent …

--- 原说明 ---
Strict **Cauchy-Schwarz** is equivalent to linear independence for positive defi
nite symmetric
forms.
-/
lemma apply_sq_lt_iff_linearIndependent_of_symm (hp : ∀ x, x ≠ 0 → 0 < B x x) (hB : B.IsSymm)
    (x y : M) : B x y ^ 2 < B x x * B y y ↔ LinearIndependent R ![x, y] := by
  rw [show B x y ^ 2 = B x y * B y x by rw [sq, ← hB.eq, RingHom.id_apply]]
  exact apply_mul_apply_lt_iff_linearIndependent B hp x y

end BilinForm

end LinearMap

