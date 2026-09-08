/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation

/-!
# Star structure on `CliffordAlgebra`

This file defines the "clifford conjugation", equal to `reverse (involute x)`, and assigns it the
`star` notation.

This choice is somewhat non-canonical; a star structure is also possible under `reverse` alone.
However, defining it gives us access to constructions like `unitary`.

Most results about `star` can be obtained by unfolding it via `CliffordAlgebra.star_def`.

## Main definitions

* `CliffordAlgebra.instStarRing`

-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {Q : QuadraticForm R M}

namespace CliffordAlgebra

/-
**CliffordAlgebra.instStarRing** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
形式化陈述：instStarRing : StarRing (CliffordAlgebra Q) where star x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instStarRing : StarRing (CliffordAlgebra Q) where
  star x := reverse (involute x)
  star_involutive x := by
    simp only [reverse_involute_commute.eq, reverse_reverse, involute_involute]
  star_mul x y := by simp only [map_mul, reverse.map_mul]
  star_add x y := by simp only [map_add]
/-
**CliffordAlgebra.star_def** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：star_def (x : CliffordAlgebra Q) : star x = reverse (involute x)
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_def (x : CliffordAlgebra Q) : star x = reverse (involute x) :=
  rfl
/-
**CliffordAlgebra.star_def'** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x)
参数：x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.reverse_involute`：reverse_involute : forall a : Clifford
Algebra Q, reverse (involute a) = involute (reverse a)
-/
theorem star_def' (x : CliffordAlgebra Q) : star x = involute (reverse x) :=
  reverse_involute _

@[simp]
/-
**CliffordAlgebra.star_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem star_ι (m : M) : star (ι Q m) = -ι Q m := by rw [star_def, involute_ι, map_neg, reverse_ι]

/-- Note that this not match the `star_smul` implied by `StarModule`; it certainly could if we
also conjugated all the scalars, but there appears to be nothing in the literature that advocates
doing this. -/
@[simp]
/-
**CliffordAlgebra.star_smul** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：star_smul (r : R) (x : CliffordAlgebra Q) : star (r • x) = r • star x
参数：r : R；x : CliffordAlgebra Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.star_def`：star_def (x : CliffordAlgebra Q) : star x = re
verse (involute x)
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …

--- 原说明 ---
Note that this not match the `star_smul` implied by `StarModule`; it certainly c
ould if we
also conjugated all the scalars, but there appears to be nothing in the literatu
re that advocates
doing this.
-/
theorem star_smul (r : R) (x : CliffordAlgebra Q) : star (r • x) = r • star x := by
  rw [star_def, star_def, map_smul, map_smul]

@[simp]
/-
**CliffordAlgebra.star_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：star_algebraMap (r : R) : star (algebraMap R (CliffordAlgebra Q) r) = alge
braMap R (CliffordAlgebra Q) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.star_def`：star_def (x : CliffordAlgebra Q) : star x = re
verse (involute x)
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `CliffordAlgebra.reverse.commutes`：∀ {R : Type u_1} [inst : CommRing R] {
M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {Q : Quad
raticForm R M} (r : R)…
-/
theorem star_algebraMap (r : R) :
    star (algebraMap R (CliffordAlgebra Q) r) = algebraMap R (CliffordAlgebra Q) r := by
  rw [star_def, involute.commutes, reverse.commutes]

end CliffordAlgebra

