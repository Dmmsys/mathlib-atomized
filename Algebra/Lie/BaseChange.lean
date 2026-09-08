/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.RestrictScalars
public import Mathlib.Algebra.Lie.TensorProduct

/-!
# Extension and restriction of scalars for Lie algebras and Lie modules

Lie algebras and their representations have a well-behaved theory of extension and restriction of
scalars.

## Main definitions

* `LieAlgebra.ExtendScalars.instLieAlgebra`
* `LieAlgebra.ExtendScalars.instLieModule`
* `LieAlgebra.RestrictScalars.lieAlgebra`

## Tags

lie ring, lie algebra, extension of scalars, restriction of scalars, base change
-/

@[expose] public section

open scoped TensorProduct

variable (R A L M : Type*)

namespace LieAlgebra

namespace ExtendScalars

variable [CommRing R] [CommRing A] [Algebra R A] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

set_option backward.privateInPublic true in
/-- The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A` over `R`. -/
/-
**LieAlgebra.ExtendScalars.bracket'** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.Extend
Scalars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie bracket on the extension of a Lie algebra `L` over `R` by an algebra `A`
 over `R`.
-/
private def bracket' : A ⊗[R] L →ₗ[A] A ⊗[R] M →ₗ[A] A ⊗[R] M :=
  TensorProduct.curry <|
    TensorProduct.AlgebraTensorModule.map
        (LinearMap.mul' A A) (LieModule.toModuleHom R L M : L ⊗[R] M →ₗ[R] M) ∘ₗ
      (TensorProduct.AlgebraTensorModule.tensorTensorTensorComm R R A A A L A M).toLinearMap

@[simp]
/-
**LieAlgebra.ExtendScalars.bracket'_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.E
xtendScalars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bracket'_tmul (s t : A) (x : L) (m : M) :
    bracket' R A L M (s ⊗ₜ[R] x) (t ⊗ₜ[R] m) = (s * t) ⊗ₜ ⁅x, m⁆ := rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.ExtendScalars.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.ExtendScalars`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bracket (A ⊗[R] L) (A ⊗[R] M) where bracket x m := bracket' R A L M x m
/-
**LieAlgebra.ExtendScalars.bracket_def** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Ext
endScalars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bracket_def (x : A ⊗[R] L) (m : A ⊗[R] M) : ⁅x, m⁆ = bracket' R A L M x m :=
  rfl

@[simp]
/-
**LieAlgebra.ExtendScalars.bracket_tmul** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebra.Ex
tendScalars`。
形式化陈述：bracket_tmul (s t : A) (x : L) (y : M) : ⁅s otimesₜ[R] x, t otimesₜ[R] y⁆ 
= (s * t) otimesₜ ⁅x, y⁆
参数：s t : A；x : L；y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bracket_tmul (s t : A) (x : L) (y : M) : ⁅s ⊗ₜ[R] x, t ⊗ₜ[R] y⁆ = (s * t) ⊗ₜ ⁅x, y⁆ := rfl

set_option backward.privateInPublic true in
/-
**LieAlgebra.ExtendScalars.bracket_lie_self** 是 Mathlib 中的一个定理，位于命名空间 `LieAlgebr
a.ExtendScalars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bracket_lie_self (x : A ⊗[R] L) : ⁅x, x⁆ = 0 := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero]
  · intro a l
    simp only [bracket'_tmul, TensorProduct.tmul_zero, lie_self]
  · intro z₁ z₂ h₁ h₂
    suffices bracket' R A L L z₁ z₂ + bracket' R A L L z₂ z₁ = 0 by
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂,
        zero_add, add_zero, add_comm, this]
    refine z₁.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₁ l₁; refine z₂.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero, LinearMap.zero_apply]
      · intro a₂ l₂
        simp only [← lie_skew l₂ l₁, mul_comm a₁ a₂, TensorProduct.tmul_neg, bracket'_tmul,
          add_neg_cancel]
      · intro y₁ y₂ hy₁ hy₂
        simp only [hy₁, hy₂, add_add_add_comm, add_zero, LinearMap.add_apply, map_add]
    · intro y₁ y₂ hy₁ hy₂
      simp only [add_add_add_comm, hy₁, hy₂, add_zero, LinearMap.add_apply, map_add]

set_option backward.privateInPublic true in
/-
**LieAlgebra.ExtendScalars.bracket_leibniz_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieAlg
ebra.ExtendScalars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem bracket_leibniz_lie (x y : A ⊗[R] L) (z : A ⊗[R] M) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆ := by
  simp only [bracket_def]
  refine x.induction_on ?_ ?_ ?_
  · simp only [map_zero, add_zero, LinearMap.zero_apply]
  · intro a₁ l₁
    refine y.induction_on ?_ ?_ ?_
    · simp only [map_zero, add_zero, LinearMap.zero_apply]
    · intro a₂ l₂
      refine z.induction_on ?_ ?_ ?_
      · simp only [map_zero, add_zero]
      · intro a₃ l₃; simp only [bracket'_tmul]
        rw [mul_left_comm a₂ a₁ a₃, mul_assoc, leibniz_lie, TensorProduct.tmul_add]
      · grind
    · grind [LinearMap.add_apply]
  · grind [LinearMap.add_apply]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.ExtendScalars.instLieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Ext
endScalars`。
形式化陈述：instLieRing : LieRing (A otimes[R] L) where add_lie x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Lie.BaseChange.0.LieAlgebra.ExtendScalars.brack
et_lie_self`：∀ (R : Type u_1) (A : Type u_2) (L : Type u_3) [inst : CommRing R] 
[inst_1 : CommRing A] [inst_2 : Algebra R A]   [inst_3 : LieRing L] [inst…
-/
instance instLieRing : LieRing (A ⊗[R] L) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  lie_self := bracket_lie_self R A L
  leibniz_lie := bracket_leibniz_lie R A L L
/-
**LieAlgebra.ExtendScalars.instBaseLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieAlge
bra.ExtendScalars`。
形式化陈述：instBaseLieAlgebra : LieAlgebra R (A otimes[R] L) where lie_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBaseLieAlgebra : LieAlgebra R (A ⊗[R] L) where lie_smul := by simp [bracket_def]
/-
**LieAlgebra.ExtendScalars.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.
ExtendScalars`。
形式化陈述：instLieAlgebra : LieAlgebra A (A otimes[R] L) where lie_smul _a _x _y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLieAlgebra : LieAlgebra A (A ⊗[R] L) where lie_smul _a _x _y := map_smul _ _ _

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**LieAlgebra.ExtendScalars.instLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgeb
ra.ExtendScalars`。
形式化陈述：instLieRingModule : LieRingModule (A otimes[R] L) (A otimes[R] M) where ad
d_lie x y z
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Lie.BaseChange.0.LieAlgebra.ExtendScalars.brack
et_leibniz_lie`：∀ (R : Type u_1) (A : Type u_2) (L : Type u_3) (M : Type u_4) [i
nst : CommRing R] [inst_1 : CommRing A]   [inst_2 : Algebra R A] [inst_3 : L…
-/
instance instLieRingModule : LieRingModule (A ⊗[R] L) (A ⊗[R] M) where
  add_lie x y z := by simp only [bracket_def, LinearMap.add_apply, map_add]
  lie_add x y z := by simp only [bracket_def, map_add]
  leibniz_lie := bracket_leibniz_lie R A L M

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.ExtendScalars.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.E
xtendScalars`。
形式化陈述：instLieModule : LieModule A (A otimes[R] L) (A otimes[R] M) where smul_lie
 t x m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instLieModule : LieModule A (A ⊗[R] L) (A ⊗[R] M) where
  smul_lie t x m := by simp only [bracket_def, map_smul, LinearMap.smul_apply]
  lie_smul _ _ _ := map_smul _ _ _

/-- The Lie algebra homomorphism induced by an algebra map. -/
/-
**LieAlgebra.ExtendScalars.map** 是 Mathlib 中的一个定义，位于命名空间 `LieAlgebra.ExtendScala
rs`。
形式化陈述：map {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing
 B] [Algebra R B] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] (f
 : A ->ₐ[R] B) (g : L ->ₗ⁅R⁆ L') : A otimes[R] L ->ₗ⁅R⁆ B otimes[R] L'
参数：f : A ->ₐ[R] B；g : L ->ₗ⁅R⁆ L'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Lie algebra homomorphism induced by an algebra map.
-/
def map {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] (f : A →ₐ[R] B) (g : L →ₗ⁅R⁆ L') :
    A ⊗[R] L →ₗ⁅R⁆ B ⊗[R] L' :=
  { TensorProduct.map f.toLinearMap g with
    map_lie' {x y} := by
      simp only [bracket_def, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      refine x.induction_on (by simp) ?_ ?_
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ ↦ by simp) (fun _ _ h1 h2 ↦ by simp [h1, h2])
      · intro _ _
        refine y.induction_on (by simp) (fun _ _ h ↦ by simp [h]) (by simp_all) }

@[simp]
/-
**LieAlgebra.ExtendScalars.map_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra.
ExtendScalars`。
形式化陈述：map_apply_tmul {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A
] [CommRing B] [Algebra R B] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgeb
ra R L'] {f : A ->ₐ[R] B} {g : L ->ₗ⁅R⁆ L'} (a : A) (x : L) : map f g (a otimesₜ
 x) = (f a) otimesₜ (g x)
参数：a : A；x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_apply_tmul {R A B L L' : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B]
    [Algebra R B] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] {f : A →ₐ[R] B}
    {g : L →ₗ⁅R⁆ L'} (a : A) (x : L) :
    map f g (a ⊗ₜ x) = (f a) ⊗ₜ (g x) :=
  rfl

end ExtendScalars

namespace RestrictScalars


variable [h : LieRing L]

/-
**LieAlgebra.RestrictScalars.** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.RestrictScal
ars`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieRing (RestrictScalars R A L) :=
  h

variable [CommRing A] [LieAlgebra A L]

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.RestrictScalars.lieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieAlgebra.Re
strictScalars`。
形式化陈述：lieAlgebra [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A 
L) where lie_smul t x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieAlgebra [CommRing R] [Algebra R A] : LieAlgebra R (RestrictScalars R A L) where
  lie_smul t x y := (lie_smul (algebraMap R A t) (RestrictScalars.addEquiv R A L x)
    (RestrictScalars.addEquiv R A L y) :)

end RestrictScalars

end LieAlgebra

section ExtendScalars

variable [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
/-
**LieModule.toEnd_baseChange** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.toEnd_baseChange (x : L) : toEnd A (A otimes[R] L) (A otimes[R] 
M) (1 otimesₜ x) = (toEnd R L M x).baseChange A
参数：x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
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
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LieModule.toEnd_baseChange (x : L) :
    toEnd A (A ⊗[R] L) (A ⊗[R] M) (1 ⊗ₜ x) = (toEnd R L M x).baseChange A := by
  ext; simp

namespace LieSubmodule

variable (N : LieSubmodule R L M)

open LieModule

set_option backward.isDefEq.respectTransparency false in
variable {R L M} in
/-- If `A` is an `R`-algebra, any Lie submodule of a Lie module `M` with coefficients in `R` may be
pushed forward to a Lie submodule of `A ⊗ M` with coefficients in `A`.

This "base change" operation is also known as "extension of scalars". -/
/-
**LieSubmodule.baseChange** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule`。
形式化陈述：baseChange : LieSubmodule A (A otimes[R] L) (A otimes[R] M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is an `R`-algebra, any Lie submodule of a Lie module `M` with coefficient
s in `R` may be
pushed forward to a Lie submodule of `A ⊗ M` with coefficients in `A`.

This "base change" operation is also known as "extension of scalars".
-/
def baseChange : LieSubmodule A (A ⊗[R] L) (A ⊗[R] M) :=
  { (N : Submodule R M).baseChange A with
    lie_mem := by
      intro x m hm
      rw [Submodule.mem_carrier, SetLike.mem_coe] at hm ⊢
      rw [Submodule.baseChange_eq_span] at hm
      obtain ⟨c, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).mp hm
      refine x.induction_on (by simp) (fun a y ↦ ?_) (fun y z hy hz ↦ ?_)
      · change toEnd A (A ⊗[R] L) (A ⊗[R] M) _ _ ∈ _
        simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, toEnd_apply_apply]
        refine Submodule.sum_mem _ fun ⟨_, n, hn, h⟩ _ ↦ Submodule.smul_mem _ _ ?_
        rw [Subtype.coe_mk, ← h]
        exact Submodule.tmul_mem_baseChange_of_mem _ (N.lie_mem hn)
      · rw [add_lie]
        exact ((N : Submodule R M).baseChange A).add_mem hy hz }

@[simp]
/-
**LieSubmodule.coe_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_baseChange : (N.baseChange A : Submodule A (A otimes[R] M)) = (N : Sub
module R M).baseChange A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma coe_baseChange :
    (N.baseChange A : Submodule A (A ⊗[R] M)) = (N : Submodule R M).baseChange A :=
  rfl

variable {N}

variable {R A L M} in
/-
**LieSubmodule.tmul_mem_baseChange_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodul
e`。
形式化陈述：tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m in N) : a otimesₜ[R] m 
in N.baseChange A
参数：a : A；hm : m in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.tmul_mem_baseChange_of_mem`：tmul_mem_baseChange_of_mem (a : A)
 {m : M} (hm : m in p) : a otimesₜ[R] m in p.baseChange A
-/
lemma tmul_mem_baseChange_of_mem (a : A) {m : M} (hm : m ∈ N) :
    a ⊗ₜ[R] m ∈ N.baseChange A :=
  (N : Submodule R M).tmul_mem_baseChange_of_mem a hm
/-
**LieSubmodule.mem_baseChange_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：mem_baseChange_iff {m : A otimes[R] M} : m in N.baseChange A ↔ m in Submod
ule.span A ((N : Submodule R M).map (TensorProduct.mk R A M 1))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.baseChange_eq_span`：baseChange_eq_span : p.baseChange A = span
 A (p.map (TensorProduct.mk R A M 1))
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_baseChange_iff {m : A ⊗[R] M} :
    m ∈ N.baseChange A ↔
    m ∈ Submodule.span A ((N : Submodule R M).map (TensorProduct.mk R A M 1)) := by
  rw [← Submodule.baseChange_eq_span]; rfl

@[simp]
/-
**LieSubmodule.baseChange_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：baseChange_bot : (⊥ : LieSubmodule R L M).baseChange A = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Submodule.baseChange_bot`：baseChange_bot : (⊥ : Submodule R M).baseChang
e A = ⊥
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mk.congr_simp`：∀ {R : Type u} {L : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] […
-/
lemma baseChange_bot : (⊥ : LieSubmodule R L M).baseChange A = ⊥ := by
  simp only [baseChange, bot_toSubmodule, Submodule.baseChange_bot]
  rfl

@[simp]
/-
**LieSubmodule.baseChange_top** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：baseChange_top : (⊤ : LieSubmodule R L M).baseChange A = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Submodule.baseChange_top`：baseChange_top : (⊤ : Submodule R M).baseChang
e A = ⊤
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.mk.congr_simp`：∀ {R : Type u} {L : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _roo
t_.Module R M] […
-/
lemma baseChange_top : (⊤ : LieSubmodule R L M).baseChange A = ⊤ := by
  simp only [baseChange, top_toSubmodule, Submodule.baseChange_top]
  rfl
/-
**LieSubmodule.lie_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_baseChange {I : LieIdeal R L} {N : LieSubmodule R L M} : ⁅I, N⁆.baseCh
ange A = ⁅I.baseChange A, N.baseChange A⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用引理 `LieSubmodule.coe_baseChange`：coe_baseChange : (N.baseChange A : Submodul
e A (A otimes[R] M)) = (N : Submodule R M).baseChange A
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span'`：lieIdeal_oper_eq_linear_span
' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x
 in I) (n in N) }
· 使用引理 `Submodule.baseChange_span`：baseChange_span (s : Set M) : (span R s).base
Change A = span A (TensorProduct.mk R A M 1 '' s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用引理 `LieSubmodule.tmul_mem_baseChange_of_mem`：tmul_mem_baseChange_of_mem (a :
 A) {m : M} (hm : m in N) : a otimesₜ[R] m in N.baseChange A
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Submodule.span_induction₂`：span_induction₂ {N : Type*} [AddCommMonoid N]
 [Module R N] {t : Set N} {p : (x : M) -> (y : N) -> x in span R s -> y in span 
R t -> Prop} (m…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
（共 33 条，此处仅展示前 30 条）
-/
lemma lie_baseChange {I : LieIdeal R L} {N : LieSubmodule R L M} :
    ⁅I, N⁆.baseChange A = ⁅I.baseChange A, N.baseChange A⁆ := by
  set s : Set (A ⊗[R] M) := { m | ∃ x ∈ I, ∃ n ∈ N, 1 ⊗ₜ ⁅x, n⁆ = m}
  have : (TensorProduct.mk R A M 1) '' {m | ∃ x ∈ I, ∃ n ∈ N, ⁅x, n⁆ = m} = s := by ext; simp [s]
  rw [← toSubmodule_inj, coe_baseChange, lieIdeal_oper_eq_linear_span',
    Submodule.baseChange_span, this, lieIdeal_oper_eq_linear_span']
  refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.mpr ?_)
  · rintro - ⟨x, hx, m, hm, rfl⟩
    exact ⟨1 ⊗ₜ x, tmul_mem_baseChange_of_mem 1 hx,
           1 ⊗ₜ m, tmul_mem_baseChange_of_mem 1 hm, by simp⟩
  · rintro - ⟨x, hx, m, hm, rfl⟩
    rw [mem_baseChange_iff] at hx hm
    refine Submodule.span_induction₂ (p := fun x m _ _ ↦ ⁅x, m⁆ ∈ Submodule.span A s)
      ?_ (by simp) (by simp) ?_ ?_ ?_ ?_ hx hm
    · rintro - - ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩; exact Submodule.subset_span ⟨x, hx, y, hy, by simp⟩
    all_goals { intros; simp [add_mem, Submodule.smul_mem, *] }

end LieSubmodule

end ExtendScalars

