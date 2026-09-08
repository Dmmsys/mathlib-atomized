/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Flatness is stable under composition and base change

We show that flatness is stable under composition and base change.

## Main theorems

* `Module.Flat.trans`: if `S` is a flat `R`-algebra and `M` is a flat `S`-module,
                      then `M` is a flat `R`-module
* `Module.Flat.baseChange`: if `M` is a flat `R`-module and `S` is any `R`-algebra,
                            then `S ⊗[R] M` is `S`-flat.
* `Module.Flat.of_isLocalizedModule`: if `M` is a flat `R`-module and `S` is a submonoid of `R`
                                          then the localization of `M` at `S` is flat as a module
                                          for the localization of `R` at `S`.
-/

public section

universe u v w t t'

open Function (Injective Surjective)

open LinearMap (lsmul rTensor lTensor)

open TensorProduct

namespace Module.Flat

section Composition

/-! ### Composition

Let `R` be a ring, `S` a flat `R`-algebra and `M` a flat `S`-module. To show that `M` is flat
as an `R`-module, we show that the inclusion of an `R`-submodule `N` into an `R`-module `P`
tensored on the left with `M` is injective. For this consider the composition of natural maps

`M ⊗[R] N ≃ M ⊗[S] (S ⊗[R] N) → M ⊗[S] (S ⊗[R] P) ≃ M ⊗[R] P`;

`S ⊗[R] N → S ⊗[R] P` is injective by `R`-flatness of `S`,
so the middle map is injective by `S`-flatness of `M`.
-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]

open AlgebraTensorModule in
/-- If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat. -/
/-
**Module.Flat.trans** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：trans [Flat R S] [Flat S M] : Flat R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_lTensor_injectiveₛ`：iff_lTensor_injectiveₛ : Flat R M ↔ 
forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] (N : Submodule R P), Function
.Injective (N.subtype.lT…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `TensorProduct.AlgebraTensorModule.coe_lTensor`：coe_lTensor (f : N ->ₗ[R]
 Q) : (lTensor A M f : M otimes[R] N -> M otimes[R] Q) = f.lTensor M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `EquivLike.injective_comp`：injective_comp (e : E) (f : β -> γ) : Function
.Injective (f ∘ e) ↔ Function.Injective f
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `TensorProduct.AlgebraTensorModule.lTensor_comp_cancelBaseChange`：lTensor
_comp_cancelBaseChange (f : N ->ₗ[R] Q) : lTensor _ _ f ∘ₗ cancelBaseChange R A 
B M N = (cancelBaseChange R A B M Q).toLinearMap ∘ₗ l…
· 使用定理 `EquivLike.comp_injective`：comp_injective (f : α -> β) (e : F) : Function
.Injective (e ∘ f) ↔ Function.Injective f
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
If `S` is a flat `R`-algebra, then any flat `S`-Module is also `R`-flat.
-/
theorem trans [Flat R S] [Flat S M] : Flat R M := by
  rw [Flat.iff_lTensor_injectiveₛ]
  introv
  rw [← coe_lTensor (A := S), ← EquivLike.injective_comp (cancelBaseChange R S S _ _),
    ← LinearEquiv.coe_coe, ← LinearMap.coe_comp, lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective]
  iterate 2 apply Flat.lTensor_preserves_injective_linearMap
  exact Subtype.val_injective

variable {R M} in
@[simp]
/-
**Module.Flat.ulift_left_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：ulift_left_iff : Flat (ULift.{t} R) M ↔ Flat R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.trans`：trans [Flat R S] [Flat S M] : Flat R M
· 使用引理 `Module.Flat.of_ulift`：of_ulift [Flat R (ULift.{v'} M)] : Flat R M
-/
lemma ulift_left_iff : Flat (ULift.{t} R) M ↔ Flat R M := by
  refine ⟨fun h ↦ .trans _ (ULift R) _, fun h ↦ ?_⟩
  have : Module.Flat (ULift.{t} R) R := .of_ulift
  let _ := ULift.algebra'
  exact .trans _ R _

variable {R M} in
@[simp]
/-
**Module.Flat.ulift_right_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：ulift_right_iff : Flat R (ULift.{t} M) ↔ Flat R M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.equiv_iff`：equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N
-/
lemma ulift_right_iff : Flat R (ULift.{t} M) ↔ Flat R M :=
  Flat.equiv_iff ULift.moduleEquiv

end Composition

section BaseChange

/-! ### Base change

Let `R` be a ring, `M` a flat `R`-module and `S` an `R`-algebra, then
`S ⊗[R] M` is a flat `S`-module. This is a special case of `Module.Flat.instTensorProduct`.

-/

variable (R : Type u) (S : Type v) (M : Type w)
  [CommSemiring R] [CommSemiring S] [Algebra R S]
  [AddCommMonoid M] [Module R M]

/-- If `M` is a flat `R`-module and `S` is any `R`-algebra, `S ⊗[R] M` is `S`-flat. -/
/-
**Module.Flat.baseChange** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：baseChange [Flat R M] : Flat S (S otimes[R] M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Flat.instTensorProduct`：∀ {R : Type u} {M : Type v} {N : Type u_1
} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : AddCo…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
If `M` is a flat `R`-module and `S` is any `R`-algebra, `S ⊗[R] M` is `S`-flat.
-/
instance baseChange [Flat R M] : Flat S (S ⊗[R] M) := inferInstance

/-- A base change of a flat module is flat. -/
/-
**Module.Flat.isBaseChange** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：isBaseChange [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Modul
e S N] [IsScalarTower R S N] {f : M ->ₗ[R] N} (h : IsBaseChange S f) : Flat S N
参数：N : Type t；h : IsBaseChange S f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
A base change of a flat module is flat.
-/
theorem isBaseChange [Flat R M] (N : Type t) [AddCommMonoid N] [Module R N] [Module S N]
    [IsScalarTower R S N] {f : M →ₗ[R] N} (h : IsBaseChange S f) :
    Flat S N :=
  of_linearEquiv (IsBaseChange.equiv h).symm

end BaseChange

section Localization

variable {R : Type u} {M Mp : Type*} (Rp : Type v)
  [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring Rp] [Algebra R Rp]
  [AddCommMonoid Mp] [Module R Mp] [Module Rp Mp] [IsScalarTower R Rp Mp]

/-
**Module.Flat.localizedModule** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：localizedModule [Flat R M] (S : Submonoid R) : Flat (Localization S) (Loca
lizedModule S M)
参数：S : Submonoid R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.isBaseChange`：isBaseChange [Flat R M] (N : Type t) [AddCommM
onoid N] [Module R N] [Module S N] [IsScalarTower R S N] {f : M ->ₗ[R] N} (h : I
sBaseChange S …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
-/
instance localizedModule [Flat R M] (S : Submonoid R) :
    Flat (Localization S) (LocalizedModule S M) := by
  apply Flat.isBaseChange (R := R) (S := Localization S)
    (f := LocalizedModule.mkLinearMap S M)
  rw [← isLocalizedModule_iff_isBaseChange S]
  exact localizedModuleIsLocalizedModule S
/-
**Module.Flat.of_isLocalizedModule** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp] (f
 : M ->ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp
参数：S : Submonoid R；f : M ->ₗ[R] Mp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.isBaseChange`：isBaseChange [Flat R M] (N : Type t) [AddCommM
onoid N] [Module R N] [Module S N] [IsScalarTower R S N] {f : M ->ₗ[R] N} (h : I
sBaseChange S …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
-/
theorem of_isLocalizedModule [Flat R M] (S : Submonoid R) [IsLocalization S Rp]
    (f : M →ₗ[R] Mp) [h : IsLocalizedModule S f] : Flat Rp Mp := by
  fapply Flat.isBaseChange (R := R) (M := M) (S := Rp) (N := Mp)
  exact (isLocalizedModule_iff_isBaseChange S Rp f).mp h
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {A : Type*} [CommSemiring A] [Algebra R A] [Flat R A] (S : Submonoid R) :
    Flat (Localization S) (Localization (Algebra.algebraMapSubmonoid A S)) :=
  of_isLocalizedModule _ S (IsScalarTower.toAlgHom R A _).toLinearMap

end Localization

end Module.Flat

