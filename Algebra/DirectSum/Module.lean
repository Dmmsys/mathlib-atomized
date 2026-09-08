/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`DirectSum.toModule.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`.  There is a canonical linear map from this direct sum to `M` (`DirectSum.coeLinearMap`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`.  The property is defined more generally
elsewhere as `DirectSum.IsInternal`, but its basic consequences on `Submodule`s are established
in this file.

-/

@[expose] public section

universe u v w u₁

namespace DirectSum

open DirectSum Finsupp Module

section General

variable {R : Type u} [Semiring R]
variable {ι : Type v}
variable {M : ι → Type w} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]

/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (⨁ i, M i) :=
  inferInstanceAs <| Module R (Π₀ i, M i)
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [Semiring S] [∀ i, Module S (M i)] [∀ i, SMulCommClass R S (M i)] :
    SMulCommClass R S (⨁ i, M i) :=
  inferInstanceAs <| SMulCommClass R S (Π₀ i, M i)
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Type*} [Semiring S] [SMul R S] [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
  inferInstanceAs <| IsScalarTower R S (Π₀ i, M i)
/-
**DirectSum.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
  inferInstanceAs <| IsCentralScalar R (Π₀ i, M i)
/-
**DirectSum.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i
参数：b : R；v : ⨁ i, M i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.smul_apply`：smul_apply [forall i, Zero (β i)] [forall i, SMulZe
roClass γ (β i)] (b : γ) (v : Π₀ i, β i) (i : ι) : (b • v) i = b • v i
-/
theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  DFinsupp.smul_apply _ _ _

variable (R) in
/-- Coercion from a `DirectSum` to a pi type is a `LinearMap`. -/
/-
**DirectSum.coeFnLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：coeFnLinearMap : (⨁ i, M i) ->ₗ[R] forall i, M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a `DirectSum` to a pi type is a `LinearMap`.
-/
def coeFnLinearMap : (⨁ i, M i) →ₗ[R] ∀ i, M i :=
  DFinsupp.coeFnLinearMap R

@[simp]
/-
**DirectSum.coeFnLinearMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：coeFnLinearMap_apply (v : ⨁ i, M i) : coeFnLinearMap R v = v
参数：v : ⨁ i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeFnLinearMap_apply (v : ⨁ i, M i) : coeFnLinearMap R v = v :=
  rfl

variable (R ι M)

section DecidableEq

variable [DecidableEq ι]

/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
/-
**DirectSum.lmk** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lmk : forall s : Finset ι, (forall i : (↑s : Set ι), M i.val) ->ₗ[R] ⨁ i, 
M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create the direct sum given a family `M` of `R` modules indexed over `ι`.
-/
def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i :=
  DFinsupp.lmk

/-- Inclusion of each component into the direct sum. -/
/-
**DirectSum.lof** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lof : forall i : ι, M i ->ₗ[R] ⨁ i, M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inclusion of each component into the direct sum.
-/
def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i :=
  DFinsupp.lsingle
/-
**DirectSum.lof_eq_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b
参数：i : ι；b : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b := rfl

variable {ι M}
/-
**DirectSum.single_eq_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b
参数：i : ι；b : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single_eq_lof (i : ι) (b : M i) : DFinsupp.single i b = lof R ι M i b := rfl

/-- Scalar multiplication commutes with direct sums. -/
/-
**DirectSum.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x
参数：s : Finset ι；c : R；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…

--- 原说明 ---
Scalar multiplication commutes with direct sums.
-/
theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
  (lmk R ι M s).map_smul c x

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
/-
**DirectSum.of_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x
参数：i : ι；c : R；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…

--- 原说明 ---
Scalar multiplication commutes with the inclusion of each component into the dir
ect sum.
-/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
  (lof R ι M i).map_smul c x

variable {R}
/-
**DirectSum.support_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：support_smul [forall (i : ι) (x : M i), Decidable (x != 0)] (c : R) (v : ⨁
 i, M i) : (c • v).support subseteq v.support
参数：i : ι；x : M i；x != 0；c : R；v : ⨁ i, M i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.support_smul`：support_smul {γ : Type w} [forall i, Zero (β i)] 
[forall i, SMulZeroClass γ (β i)] [forall (i : ι) (x : β i), Decidable (x != 0)]
 (b : γ) (v…
-/
theorem support_smul [∀ (i : ι) (x : M i), Decidable (x ≠ 0)] (c : R) (v : ⨁ i, M i) :
    (c • v).support ⊆ v.support :=
  DFinsupp.support_smul _ _

variable {N : Type u₁} [AddCommMonoid N] [Module R N]
variable (φ : ∀ i, M i →ₗ[R] N)
variable (R ι N)

/-- The linear map constructed using the universal property of the coproduct. -/
/-
**DirectSum.toModule** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：toModule : (⨁ i, M i) ->ₗ[R] N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map constructed using the universal property of the coproduct.
-/
def toModule : (⨁ i, M i) →ₗ[R] N :=
  DFunLike.coe (DFinsupp.lsum ℕ) φ

/-- Coproducts in the categories of modules and additive monoids commute with the forgetful functor
from modules to additive monoids. -/
/-
**DirectSum.coe_toModule_eq_coe_toAddMonoid** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum
`。
形式化陈述：coe_toModule_eq_coe_toAddMonoid : (toModule R ι N φ : (⨁ i, M i) -> N) = t
oAddMonoid fun i => (φ i).toAddMonoidHom
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coproducts in the categories of modules and additive monoids commute with the fo
rgetful functor
from modules to additive monoids.
-/
theorem coe_toModule_eq_coe_toAddMonoid :
    (toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i ↦ (φ i).toAddMonoidHom := rfl

variable {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp]
/-
**DirectSum.toModule_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x
参数：i；x : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x

--- 原说明 ---
The map constructed using the universal property gives back the original maps wh
en
restricted to each component.
-/
theorem toModule_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x :=
  toAddMonoid_of (fun i ↦ (φ i).toAddMonoidHom) i x

variable (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
/-
**DirectSum.toModule.unique** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.toModule`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] [in
st_3 : DecidableEq ι] {N : Type u₁} [inst_4 : AddCommMonoid N]   [inst_5 : _root
_.Module R N] (ψ : (DirectSum ι fun i => M i) →ₗ[R] N) (f : DirectSum ι fun i =>
 M i),   ψ f = (DirectSum.toModule R ι N fun i => ψ ∘ₗ DirectSum.lof R ι M i) f
参数：R : Type u；i : ι；M i；i : ι；M i；ψ : (DirectSum ι fun i => M i) →ₗ[R] N；f : Dir
ectSum ι fun i => M i；DirectSum.toModule R ι N fun i => ψ ∘ₗ DirectSum.lof R ι M
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoid.unique`：∀ {ι : Type v} {β : ι → Type w} [inst : (i
 : ι) → AddCommMonoid (β i)] [inst_1 : DecidableEq ι] {γ : Type u₁}   [inst_2 : 
AddCommMonoid γ] (…

--- 原说明 ---
Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components.
-/
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i ↦ ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
/-
**DirectSum.linearMap_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：linearMap_ext ⦃ψ ψ' : (⨁ i, M i) ->ₗ[R] N⦄ (H : forall i, ψ.comp (lof R ι 
M i) = ψ'.comp (lof R ι M i)) : ψ = ψ'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (Π₀ i, M i) ->ₗ[R] N⦄ (h : forall i
, φ.comp (lsingle i) = ψ.comp (lsingle i)) : φ = ψ

--- 原说明 ---
Two `LinearMap`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas].
-/
theorem linearMap_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄
    (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
  DFinsupp.lhom_ext' H

/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map. -/
/-
**DirectSum.lsetToSet** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lsetToSet (S T : Set ι) (H : S subseteq T) : (⨁ i : S, M i) ->ₗ[R] ⨁ i : T
, M i
参数：S T : Set ι；H : S subseteq T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map.
-/
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  toModule R _ _ fun i ↦ lof R T (fun i : T ↦ M i) ⟨i, H i.prop⟩

variable (ι M)

/-- Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `∀ i, M i`. -/
@[simps! apply]
/-
**DirectSum.linearEquivFunOnFintype** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] forall i, M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `Fintype α`, `linearEquivFunOnFintype R` is the natural `R`-linear equival
ence
between `⨁ i, M i` and `∀ i, M i`.
-/
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  DFinsupp.linearEquivFunOnFintype

variable {ι M}

@[simp]
/-
**DirectSum.linearEquivFunOnFintype_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) : (linearEquivFu
nOnFintype R ι M) (lof R ι M i m) = Pi.single i m
参数：i : ι；m : M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linearEquivFunOnFintype_lof [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  rfl

@[simp]
/-
**DirectSum.linearEquivFunOnFintype_symm_single** 是 Mathlib 中的一个定理，位于命名空间 `Direc
tSum`。
形式化陈述：linearEquivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : M i) : (linea
rEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m
参数：i : ι；m : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.equivFunOnFintype_symm_single`：equivFunOnFintype_symm_single [F
intype ι] (i : ι) (m : β i) : (@DFinsupp.equivFunOnFintype ι β _ _).symm (Pi.sin
gle i m) = DFinsupp.single i…
-/
theorem linearEquivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m :=
  DFinsupp.equivFunOnFintype_symm_single i m

end DecidableEq

@[simp]
/-
**DirectSum.linearEquivFunOnFintype_symm_coe** 是 Mathlib 中的一个定理，位于命名空间 `DirectSu
m`。
形式化陈述：linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) : (linearEquiv
FunOnFintype R ι M).symm f = f
参数：f : ⨁ i, M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem linearEquivFunOnFintype_symm_coe [Fintype ι] (f : ⨁ i, M i) :
    (linearEquivFunOnFintype R ι M).symm f = f :=
  (linearEquivFunOnFintype R ι M).symm_apply_apply _

/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`. -/
/-
**DirectSum.lid** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：(R : Type u) →   [inst : Semiring R] →     (M : Type v) →       (ι : optPa
ram (Type u_1) PUnit.{u_1 + 1}) →         [inst_1 : AddCommMonoid M] → [inst_2 :
 _root_.Module R M] → [Unique ι] → (DirectSum ι fun x => M) ≃ₗ[R] M
参数：Type u_1。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The natural linear equivalence between `⨁ _ : ι, M` and `M` when `Unique ι`.
-/
protected def lid (M : Type v) (ι : Type* := PUnit) [AddCommMonoid M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun _ ↦ LinearMap.id with }
/-
**DirectSum.lid_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {M : Type v} {ι : Type u_1} [inst_1 : A
ddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : Unique ι] (x : DirectSu
m ι fun x => M), (DirectSum.lid R M ι) x = x default
参数：R : Type u；x : DirectSum ι fun x => M；DirectSum.lid R M ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.id_apply`：∀ {M : Type v} {ι : Type u_1} [inst : AddCommMonoid 
M] [inst_1 : Unique ι] (x : DirectSum ι fun x => M),   (DirectSum.id M ι) x = x 
default
-/
@[simp] lemma lid_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : ⨁ _ : ι, M) : DirectSum.lid R M ι x = x default :=
  DirectSum.id_apply x
/-
**DirectSum.lid_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {M : Type v} {ι : Type u_1} [inst_1 : A
ddCommMonoid M] [inst_2 : _root_.Module R M]   [inst_3 : Unique ι] (x : M), (Dir
ectSum.lid R M ι).symm x = (DirectSum.lof R ι (fun i => M) default) x
参数：R : Type u；x : M；DirectSum.lid R M ι；DirectSum.lof R ι (fun i => M) default。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.id_symm_apply`：∀ {M : Type v} {ι : Type u_1} [inst : AddCommMo
noid M] [inst_1 : Unique ι] (x : M),   (DirectSum.id M ι).symm x = (DirectSum.of
 (fun i => M)…
-/
@[simp] lemma lid_symm_apply {M : Type v} {ι : Type*} [AddCommMonoid M] [Module R M] [Unique ι]
    (x : M) : (DirectSum.lid R M ι).symm x = lof R _ _ default x :=
  DirectSum.id_symm_apply x

/-- The projection map onto one component, as a linear map. -/
/-
**DirectSum.component** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：component (i : ι) : (⨁ i, M i) ->ₗ[R] M i
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection map onto one component, as a linear map.
-/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  DFinsupp.lapply i

variable {ι M}
/-
**DirectSum.apply_eq_component** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f
参数：f : ⨁ i, M i；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f := rfl

-- Note(kmill): `@[ext]` cannot prove `ext_iff` because `R` is not determined by `f` or `g`.
-- This is not useful as an `@[ext]` lemma as the `ext` tactic cannot infer `R`.
/-
**DirectSum.ext_component** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ext_component {f g : ⨁ i, M i} (h : forall i, component R ι M i f = compon
ent R ι M i g) : f = g
参数：h : forall i, component R ι M i f = component R ι M i g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.ext`：ext {f g : Π₀ i, β i} (h : forall i, f i = g i) : f = g
-/
theorem ext_component {f g : ⨁ i, M i} (h : ∀ i, component R ι M i f = component R ι M i g) :
    f = g :=
  DFinsupp.ext h
/-
**DirectSum.ext_component_iff** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：ext_component_iff {f g : ⨁ i, M i} : f = g ↔ forall i, component R ι M i f
 = component R ι M i g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.ext_component`：ext_component {f g : ⨁ i, M i} (h : forall i, c
omponent R ι M i f = component R ι M i g) : f = g
-/
theorem ext_component_iff {f g : ⨁ i, M i} :
    f = g ↔ ∀ i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ ↦ by rw [h], ext_component R⟩

@[simp]
/-
**DirectSum.lof_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof R ι M i) b) i = b
参数：i : ι；b : M i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_eq_same`：single_eq_same {i b} : (single i b : Π₀ i, β i)
 i = b
-/
theorem lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
  DFinsupp.single_eq_same

@[simp]
/-
**DirectSum.component.lof_self** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.component`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] [in
st_3 : DecidableEq ι] (i : ι) (b : M i),   (DirectSum.component R ι M i) ((Direc
tSum.lof R ι M i) b) = b
参数：R : Type u；i : ι；M i；i : ι；M i；i : ι；b : M i；DirectSum.component R ι M i；(Dir
ectSum.lof R ι M i) b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.lof_apply`：lof_apply [DecidableEq ι] (i : ι) (b : M i) : ((lof
 R ι M i) b) i = b
-/
theorem component.lof_self [DecidableEq ι] (i : ι) (b : M i) :
    component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b
/-
**DirectSum.component.of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.component`。
形式化陈述：∀ (R : Type u) [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] [in
st_3 : DecidableEq ι] (i j : ι) (b : M j),   (DirectSum.component R ι M i) ((Dir
ectSum.lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0
参数：R : Type u；i : ι；M i；i : ι；M i；i j : ι；b : M j；DirectSum.component R ι M i；(D
irectSum.lof R ι M j) b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.single_apply`：single_apply {i i' b} : (single i b : Π₀ i, β i) 
i' = if h : i = i' then Eq.recOn h b else 0
-/
theorem component.of [DecidableEq ι] (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOn h b else 0 :=
  DFinsupp.single_apply
/-
**DirectSum.component_comp_lof** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：component_comp_lof [DecidableEq ι] (i j : ι) : component R ι M i ∘ₗ lof R 
ι M j = if h : j = i then h ▸ .id else 0
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DirectSum.component.of`：∀ (R : Type u) [inst : Semiring R] {ι : Type v} 
{M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → 
_root_.Modul…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `DirectSum.component.lof_self`：∀ (R : Type u) [inst : Semiring R] {ι : Ty
pe v} {M : ι → Type w} [inst_1 : (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i :
 ι) → _root_.Modul…
-/
lemma component_comp_lof [DecidableEq ι] (i j : ι) :
    component R ι M i ∘ₗ lof R ι M j = if h : j = i then h ▸ .id else 0 := by
  aesop (add simp component.of)

@[simp]
/-
**DirectSum.component_comp_lof_same** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：component_comp_lof_same [DecidableEq ι] (i : ι) : component R ι M i ∘ₗ lof
 R ι M i = .id
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `DirectSum.component_comp_lof`：component_comp_lof [DecidableEq ι] (i j : 
ι) : component R ι M i ∘ₗ lof R ι M j = if h : j = i then h ▸ .id else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
-/
lemma component_comp_lof_same [DecidableEq ι] (i : ι) : component R ι M i ∘ₗ lof R ι M i = .id := by
  simp [component_comp_lof]

section map

variable {R} {N : ι → Type*}

section AddCommMonoid
variable [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]

section
variable (f : ∀ i, M i →+ N i)

/-
**DirectSum.mker_map** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：mker_map : AddMonoidHom.mker (map f) = (AddSubmonoid.pi Set.univ (fun i =>
 AddMonoidHom.mker (f i))).comap (coeFnAddMonoidHom M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.mker_mapRangeAddMonoidHom`：mker_mapRangeAddMonoidHom (f : foral
l i, β₁ i ->+ β₂ i) : AddMonoidHom.mker (mapRange.addMonoidHom f) = (AddSubmonoi
d.pi Set.univ (fun i => …
-/
lemma mker_map :
    AddMonoidHom.mker (map f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mker (f i))).comap (coeFnAddMonoidHom M) :=
  DFinsupp.mker_mapRangeAddMonoidHom f
/-
**DirectSum.mrange_map** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：mrange_map : AddMonoidHom.mrange (map f) = (AddSubmonoid.pi Set.univ (fun 
i => AddMonoidHom.mrange (f i))).comap (coeFnAddMonoidHom N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.mrange_mapRangeAddMonoidHom`：mrange_mapRangeAddMonoidHom (f : f
orall i, β₁ i ->+ β₂ i) : AddMonoidHom.mrange (mapRange.addMonoidHom f) = (AddSu
bmonoid.pi Set.univ (fun i…
-/
lemma mrange_map :
    AddMonoidHom.mrange (map f) =
      (AddSubmonoid.pi Set.univ (fun i ↦ AddMonoidHom.mrange (f i))).comap (coeFnAddMonoidHom N) :=
  DFinsupp.mrange_mapRangeAddMonoidHom f

end

variable (f : Π i, M i →ₗ[R] N i)

/-- The linear map between direct sums induced by a family of linear maps. -/
/-
**DirectSum.lmap** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lmap : (⨁ i, M i) ->ₗ[R] ⨁ i, N i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map between direct sums induced by a family of linear maps.
-/
def lmap : (⨁ i, M i) →ₗ[R] ⨁ i, N i := DFinsupp.mapRange.linearMap f
/-
**DirectSum.lmap_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] {N 
: ι → Type u_1} [inst_3 : (i : ι) → AddCommMonoid (N i)]   [inst_4 : (i : ι) → _
root_.Module R (N i)] (f : (i : ι) → M i →ₗ[R] N i) (x : DirectSum ι fun i => M 
i) (i : ι),   ((DirectSum.lmap f) x) i = (f i) (x i)
参数：i : ι；M i；i : ι；M i；i : ι；N i；i : ι；N i；f : (i : ι) → M i →ₗ[R] N i；x : Direc
tSum ι fun i => M i；i : ι；(DirectSum.lmap f) x；f i；x i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem lmap_apply (x i) : lmap f x i = f i (x i) := rfl
/-
**DirectSum.lmap_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] {N 
: ι → Type u_1} [inst_3 : (i : ι) → AddCommMonoid (N i)]   [inst_4 : (i : ι) → _
root_.Module R (N i)] (f : (i : ι) → M i →ₗ[R] N i) [inst_5 : DecidableEq ι] (i 
: ι) (x : M i),   (DirectSum.lmap f) ((DirectSum.of M i) x) = (DirectSum.of N i)
 ((f i) x)
参数：i : ι；M i；i : ι；M i；i : ι；N i；i : ι；N i；f : (i : ι) → M i →ₗ[R] N i；i : ι；x :
 M i；DirectSum.lmap f；(DirectSum.of M i) x；DirectSum.of N i；(f i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
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
@[simp] lemma lmap_of [DecidableEq ι] (i : ι) (x : M i) :
    lmap f (of M i x) = of N i (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ => map_zero _)
/-
**DirectSum.lmap_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] {N 
: ι → Type u_1} [inst_3 : (i : ι) → AddCommMonoid (N i)]   [inst_4 : (i : ι) → _
root_.Module R (N i)] (f : (i : ι) → M i →ₗ[R] N i) [inst_5 : DecidableEq ι] (i 
: ι) (x : M i),   (DirectSum.lmap f) ((DirectSum.lof R ι M i) x) = (DirectSum.lo
f R ι N i) ((f i) x)
参数：i : ι；M i；i : ι；M i；i : ι；N i；i : ι；N i；f : (i : ι) → M i →ₗ[R] N i；i : ι；x :
 M i；DirectSum.lmap f；(DirectSum.lof R ι M i) x；DirectSum.lof R ι N i；(f i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
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
@[simp] theorem lmap_lof [DecidableEq ι] (i) (x : M i) :
    lmap f (lof R _ _ _ x) = lof R _ _ _ (f i x) :=
  DFinsupp.mapRange_single (hf := fun _ ↦ map_zero _)
/-
**DirectSum.lmap_id** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)], (D
irectSum.lmap fun i => LinearMap.id) = LinearMap.id
参数：i : ι；M i；i : ι；M i；DirectSum.lmap fun i => LinearMap.id。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange.linearMap_id`：∀ {ι : Type u_1} {R : Type u_3} [inst : 
Semiring R] {β₂ : ι → Type u_9} [inst_1 : (i : ι) → AddCommMonoid (β₂ i)]   [ins
t_2 : (i : ι) → _roo…
-/
@[simp] lemma lmap_id :
    (lmap (fun i ↦ LinearMap.id (R := R) (M := M i))) = LinearMap.id :=
  DFinsupp.mapRange.linearMap_id
/-
**DirectSum.lmap_comp** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} {M : ι → Type w} [inst_1 :
 (i : ι) → AddCommMonoid (M i)]   [inst_2 : (i : ι) → _root_.Module R (M i)] {N 
: ι → Type u_1} [inst_3 : (i : ι) → AddCommMonoid (N i)]   [inst_4 : (i : ι) → _
root_.Module R (N i)] (f : (i : ι) → M i →ₗ[R] N i) {K : ι → Type u_2}   [inst_5
 : (i : ι) → AddCommMonoid (K i)] [inst_6 : (i : ι) → _root_.Module R (K i)] (g 
: (i : ι) → N i →ₗ[R] K i),   (DirectSum.lmap fun i => g i ∘ₗ f i) = DirectSum.l
map g ∘ₗ DirectSum.lmap f
参数：i : ι；M i；i : ι；M i；i : ι；N i；i : ι；N i；f : (i : ι) → M i →ₗ[R] N i；i : ι；K i
；i : ι；K i；g : (i : ι) → N i →ₗ[R] K i；DirectSum.lmap fun i => g i ∘ₗ f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange.linearMap_comp`：∀ {ι : Type u_1} {R : Type u_3} [inst 
: Semiring R] {β : ι → Type u_7} {β₁ : ι → Type u_8} {β₂ : ι → Type u_9}   [inst
_1 : (i : ι) → AddComm…
-/
@[simp] lemma lmap_comp {K : ι → Type*} [∀ i, AddCommMonoid (K i)] [∀ i, Module R (K i)]
    (g : ∀ (i : ι), N i →ₗ[R] K i) :
    (lmap (fun i ↦ (g i) ∘ₗ (f i))) = (lmap g) ∘ₗ (lmap f) :=
  DFinsupp.mapRange.linearMap_comp _ _
/-
**DirectSum.lmap_injective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lmap_injective : Function.Injective (lmap f) ↔ forall i, Function.Injectiv
e (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_injective`：mapRange_injective (f : forall i, β₁ i -> β
₂ i) (hf : forall i, f i 0 = 0) : Function.Injective (mapRange f hf) ↔ forall i,
 Function.Injecti…
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
theorem lmap_injective : Function.Injective (lmap f) ↔ ∀ i, Function.Injective (f i) := by
  exact DFinsupp.mapRange_injective (hf := fun _ ↦ map_zero _)
/-
**DirectSum.lmap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lmap_surjective : Function.Surjective (lmap f) ↔ (forall i, Function.Surje
ctive (f i))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFinsupp.mapRange_surjective`：mapRange_surjective (f : forall i, β₁ i ->
 β₂ i) (hf : forall i, f i 0 = 0) : Function.Surjective (mapRange f hf) ↔ forall
 i, Function.Surje…
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
theorem lmap_surjective : Function.Surjective (lmap f) ↔ (∀ i, Function.Surjective (f i)) := by
  exact DFinsupp.mapRange_surjective (hf := fun _ ↦ map_zero _)
/-
**DirectSum.lmap_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：lmap_eq_iff (x y : ⨁ i, M i) : lmap f x = lmap f y ↔ forall i, f i (x i) =
 f i (y i)
参数：x y : ⨁ i, M i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirectSum.map_eq_iff`：map_eq_iff (x y : ⨁ i, α i) : map f x = map f y ↔ 
forall i, f i (x i) = f i (y i)
-/
lemma lmap_eq_iff (x y : ⨁ i, M i) :
    lmap f x = lmap f y ↔ ∀ i, f i (x i) = f i (y i) :=
  map_eq_iff (fun i => (f i).toAddMonoidHom) _ _
/-
**DirectSum.toAddMonoidHom_lmap** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：toAddMonoidHom_lmap : (lmap f).toAddMonoidHom = map (fun i => (f i).toAddM
onoidHom)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toAddMonoidHom_lmap :
    (lmap f).toAddMonoidHom = map (fun i => (f i).toAddMonoidHom) :=
  rfl
/-
**DirectSum.lmap_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：lmap_eq_map (x : ⨁ i, M i) : lmap f x = map (fun i => (f i).toAddMonoidHom
) x
参数：x : ⨁ i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lmap_eq_map (x : ⨁ i, M i) : lmap f x = map (fun i => (f i).toAddMonoidHom) x :=
  rfl
/-
**DirectSum.ker_lmap** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：ker_lmap : LinearMap.ker (lmap f) = (Submodule.pi Set.univ (fun i => Linea
rMap.ker (f i))).comap (DirectSum.coeFnLinearMap R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.ker_mapRangeLinearMap`：ker_mapRangeLinearMap (f : forall i, β₁ 
i ->ₗ[R] β₂ i) : LinearMap.ker (mapRange.linearMap f) = (Submodule.pi Set.univ (
fun i => LinearMap.k…
-/
lemma ker_lmap :
    LinearMap.ker (lmap f) =
      (Submodule.pi Set.univ (fun i ↦ LinearMap.ker (f i))).comap (DirectSum.coeFnLinearMap R) :=
  DFinsupp.ker_mapRangeLinearMap f
/-
**DirectSum.range_lmap** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：range_lmap : LinearMap.range (lmap f) = (Submodule.pi Set.univ (fun i => L
inearMap.range (f i))).comap (DirectSum.coeFnLinearMap R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.range_mapRangeLinearMap`：range_mapRangeLinearMap (f : forall i,
 β₁ i ->ₗ[R] β₂ i) : LinearMap.range (mapRange.linearMap f) = (Submodule.pi Set.
univ (LinearMap.range …
-/
lemma range_lmap :
    LinearMap.range (lmap f) =
      (Submodule.pi Set.univ (fun i ↦ LinearMap.range (f i))).comap (DirectSum.coeFnLinearMap R) :=
  DFinsupp.range_mapRangeLinearMap f

end AddCommMonoid

section AddCommGroup
variable {R : Type u} {ι : Type v} {M : ι → Type w} {N : ι → Type*}

/-
**DirectSum.ker_map** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：ker_map [forall i, AddCommGroup (M i)] [forall i, AddCommMonoid (N i)] (f 
: forall i, M i ->+ N i) : (map f).ker = (AddSubgroup.pi Set.univ (f · |>.ker)).
comap (DirectSum.coeFnAddMonoidHom M)
参数：M i；N i；f : forall i, M i ->+ N i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.ker_mapRangeAddMonoidHom`：ker_mapRangeAddMonoidHom [forall i, A
ddCommGroup (β₁ i)] [forall i, AddCommMonoid (β₂ i)] (f : forall i, β₁ i ->+ β₂ 
i) : (mapRange.addMonoi…
-/
lemma ker_map [∀ i, AddCommGroup (M i)] [∀ i, AddCommMonoid (N i)] (f : ∀ i, M i →+ N i) :
    (map f).ker =
      (AddSubgroup.pi Set.univ (f · |>.ker)).comap (DirectSum.coeFnAddMonoidHom M) :=
  DFinsupp.ker_mapRangeAddMonoidHom f
/-
**DirectSum.range_map** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：range_map [forall i, AddCommGroup (M i)] [forall i, AddCommGroup (N i)] (f
 : forall i, M i ->+ N i) : (map f).range = (AddSubgroup.pi Set.univ (f · |>.ran
ge)).comap (DirectSum.coeFnAddMonoidHom N)
参数：M i；N i；f : forall i, M i ->+ N i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DFinsupp.range_mapRangeAddMonoidHom`：range_mapRangeAddMonoidHom [forall 
i, AddCommGroup (β₁ i)] [forall i, AddCommGroup (β₂ i)] (f : forall i, β₂ i ->+ 
β₁ i) : (mapRange.addMono…
-/
lemma range_map [∀ i, AddCommGroup (M i)] [∀ i, AddCommGroup (N i)] (f : ∀ i, M i →+ N i) :
    (map f).range =
      (AddSubgroup.pi Set.univ (f · |>.range)).comap (DirectSum.coeFnAddMonoidHom N) :=
  DFinsupp.range_mapRangeAddMonoidHom f

end AddCommGroup

end map

section CongrLeft

variable {κ : Type*}

/-- Reindexing terms of a direct sum is linear. -/
/-
**DirectSum.lequivCongrLeft** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k)
参数：h : ι ≃ κ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reindexing terms of a direct sum is linear.
-/
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  DFinsupp.domLCongr h

@[simp]
/-
**DirectSum.lequivCongrLeft_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) : lequivCongrLeft
 R h f k = f (h.symm k)
参数：h : ι ≃ κ；f : ⨁ i, M i；k : κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.equivCongrLeft_apply`：equivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ 
i, β i) (k : κ) : equivCongrLeft h f k = f (h.symm k)
-/
theorem lequivCongrLeft_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) :
    lequivCongrLeft R h f k = f (h.symm k) :=
  equivCongrLeft_apply _ _ _

-- We need to try very hard to avoid dependent type "issues".
/-
**DirectSum.lequivCongrLeft_lof** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：lequivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ} {i : ι} {k
 : κ} (hik : i = e.symm k) (x : M i) (y : M (e.symm k)) (hxy : cast congr(M $hik
) x = y) : lequivCongrLeft R e (lof R ι M i x) = lof R _ _ k y
参数：hik : i = e.symm k；x : M i；y : M (e.symm k)；hxy : cast congr(M $hik) x = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.ext`：∀ {ι : Type v} {β : ι → Type w} [inst : (i : ι) → AddComm
Monoid (β i)] {x y : DirectSum ι β},   (∀ (i : ι), x i = y i) → x = y
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.lequivCongrLeft_apply`：lequivCongrLeft_apply (h : ι ≃ κ) (f : 
⨁ i, M i) (k : κ) : lequivCongrLeft R h f k = f (h.symm k)
· 使用引理 `DirectSum.of_apply`：of_apply {i : ι} (j : ι) (x : β i) : of β i x j = if
 h : i = j then Eq.recOn h x else 0
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
-/
lemma lequivCongrLeft_lof [DecidableEq ι] [DecidableEq κ] {e : ι ≃ κ}
    {i : ι} {k : κ} (hik : i = e.symm k)
    (x : M i) (y : M (e.symm k)) (hxy : cast congr(M $hik) x = y) :
    lequivCongrLeft R e (lof R ι M i x) = lof R _ _ k y := by
  subst hik hxy
  ext j
  simp [lof_eq_of, of_apply]
  lia
/-
**DirectSum.lequivCongrLeft_symm_lof** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ} {k : 
κ} {x : M (h.symm k)} : (lequivCongrLeft R h).symm (lof R κ (fun k => M (h.symm 
k)) k x) = lof R ι M (h.symm k) x
参数：h.symm k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `DirectSum.lequivCongrLeft_lof`：lequivCongrLeft_lof [DecidableEq ι] [Deci
dableEq κ] {e : ι ≃ κ} {i : ι} {k : κ} (hik : i = e.symm k) (x : M i) (y : M (e.
symm k)) (hxy : cas…
-/
lemma lequivCongrLeft_symm_lof [DecidableEq ι] [DecidableEq κ] {h : ι ≃ κ}
    {k : κ} {x : M (h.symm k)} :
    (lequivCongrLeft R h).symm (lof R κ (fun k => M (h.symm k)) k x) = lof R ι M (h.symm k) x := by
  rw [LinearEquiv.symm_apply_eq]
  symm
  exact lequivCongrLeft_lof _ rfl _ _ rfl

end CongrLeft

section Sigma

variable {α : ι → Type*} {δ : ∀ i, α i → Type w}
variable [DecidableEq ι] [∀ i j, AddCommMonoid (δ i j)] [∀ i j, Module R (δ i j)]

/-- `curry` as a linear map. -/
/-
**DirectSum.sigmaLcurry** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaLcurry : (⨁ i : Σ _, _, δ i.1 i.2) ->ₗ[R] ⨁ (i) (j), δ i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`curry` as a linear map.
-/
def sigmaLcurry : (⨁ i : Σ _, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with map_smul' := fun r ↦ by convert! DFinsupp.sigmaCurry_smul (δ := δ) r }

@[simp]
/-
**DirectSum.sigmaLcurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaLcurry_apply (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i) : sigmaL
curry R f i j = f ⟨i, j⟩
参数：f : ⨁ i : Σ _, _, δ i.1 i.2；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.sigmaCurry_apply`：sigmaCurry_apply (f : ⨁ i : Σ _i, _, δ i.1 i
.2) (i : ι) (j : α i) : sigmaCurry f i j = f ⟨i, j⟩
-/
theorem sigmaLcurry_apply (f : ⨁ i : Σ _, _, δ i.1 i.2) (i : ι) (j : α i) :
    sigmaLcurry R f i j = f ⟨i, j⟩ :=
  sigmaCurry_apply f i j

/-- `uncurry` as a linear map. -/
/-
**DirectSum.sigmaLuncurry** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaLuncurry : (⨁ (i) (j), δ i j) ->ₗ[R] ⨁ i : Σ _, _, δ i.1 i.2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`uncurry` as a linear map.
-/
def sigmaLuncurry : (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σ _, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := DFinsupp.sigmaUncurry_smul }

@[simp]
/-
**DirectSum.sigmaLuncurry_apply** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaLuncur
ry R f ⟨i, j⟩ = f i j
参数：f : ⨁ (i) (j), δ i j；i : ι；j : α i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.sigmaUncurry_apply`：sigmaUncurry_apply (f : ⨁ (i) (j), δ i j) 
(i : ι) (j : α i) : sigmaUncurry f ⟨i, j⟩ = f i j
-/
theorem sigmaLuncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) :
    sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigmaUncurry_apply f i j

/-- `curryEquiv` as a linear equiv. -/
/-
**DirectSum.sigmaLcurryEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：sigmaLcurryEquiv : (⨁ i : Σ _, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`curryEquiv` as a linear equiv.
-/
def sigmaLcurryEquiv : (⨁ i : Σ _, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  DFinsupp.sigmaCurryLEquiv

end Sigma

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoid (α i)] [∀ i, Module R (α i)]

/-- Linear isomorphism obtained by separating the term of index `none` of a direct sum over
`Option ι`. -/
@[simps]
/-
**DirectSum.lequivProdDirectSum** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Linear isomorphism obtained by separating the term of index `none` of a direct s
um over
`Option ι`.
-/
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := DFinsupp.equivProdDFinsupp_smul }

end Option

end General

section Submodule

section Semiring

variable {R : Type u} [Semiring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommMonoid M] [Module R M]
variable (A : ι → Submodule R M)

/-- The canonical linear map from `⨁ i, A i` to `M` where `A` is a collection of `Submodule R M`
indexed by `ι`. This is `DirectSum.coeAddMonoidHom` as a `LinearMap`. -/
/-
**DirectSum.coeLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：coeLinearMap : (⨁ i, A i) ->ₗ[R] M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from `⨁ i, A i` to `M` where `A` is a collection of `Su
bmodule R M`
indexed by `ι`. This is `DirectSum.coeAddMonoidHom` as a `LinearMap`.
-/
def coeLinearMap : (⨁ i, A i) →ₗ[R] M :=
  toModule R ι M fun i ↦ (A i).subtype

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.coeLinearMap_eq_dfinsuppSum** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i)
 : coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x)
参数：x : DirectSum ι fun i => A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DFinsupp.sumAddHom_apply`：sumAddHom_apply [forall i, AddZeroClass (β i)]
 [forall (i) (x : β i), Decidable (x != 0)] [AddCommMonoid γ] (φ : forall i, β i
 ->+ γ) (f : Π…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeLinearMap_eq_dfinsuppSum [DecidableEq M] (x : DirectSum ι fun i => A i) :
    coeLinearMap A x = DFinsupp.sum x fun i => (fun x : A i => ↑x) := by
  simp only [coeLinearMap, toModule, DFinsupp.lsum, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [DFinsupp.sumAddHom_apply]
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype]

@[simp]
/-
**DirectSum.coeLinearMap_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i =>
 A i) i x) = x
参数：i : ι；x : A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem coeLinearMap_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i ↦ A i) i x) = x :=
  -- Porting note: spelled out arguments. (I don't know how this works.)
  toAddMonoid_of (β := fun i => A i) (fun i ↦ ((A i).subtype : A i →+ M)) i x
/-
**DirectSum.coeLinearMap_lof** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (A : ι → 
Submodule R M) (i : ι) (x : ↥(A i)),   (DirectSum.coeLinearMap A) ((DirectSum.lo
f R ι (fun i => ↥(A i)) i) x) = ↑x
参数：A : ι → Submodule R M；i : ι；x : ↥(A i)；DirectSum.coeLinearMap A；(DirectSum.lo
f R ι (fun i => ↥(A i)) i) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.coeLinearMap_of`：coeLinearMap_of (i : ι) (x : A i) : DirectSum
.coeLinearMap A (of (fun i => A i) i x) = x
-/
@[simp] lemma coeLinearMap_lof (i : ι) (x : A i) :
    DirectSum.coeLinearMap A (lof R ι (fun i ↦ A i) i x) = x :=
  coeLinearMap_of A i x

variable {A}
/-
**DirectSum.range_coeLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：range_coeLinearMap : LinearMap.range (coeLinearMap A) = ⨆ i, A i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)
-/
theorem range_coeLinearMap : LinearMap.range (coeLinearMap A) = ⨆ i, A i :=
  (Submodule.iSup_eq_range_dfinsupp_lsum _).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DirectSum.IsInternal.ofBijective_coeLinearMap_same** 是 Mathlib 中的一个定理，位于命名空间 `
DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {i : ι} (x : ↥(A i)),   ((LinearEqui
v.ofBijective (DirectSum.coeLinearMap A) h).symm ↑x) i = x
参数：h : DirectSum.IsInternal A；x : ↥(A i)；(LinearEquiv.ofBijective (DirectSum.coe
LinearMap A) h).symm ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.coeLinearMap_of`：coeLinearMap_of (i : ι) (x : A i) : DirectSum
.coeLinearMap A (of (fun i => A i) i x) = x
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
-/
theorem IsInternal.ofBijective_coeLinearMap_same (h : IsInternal A)
    {i : ι} (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = x := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_same]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne** 是 Mathlib 中的一个定理，位于命名空间 
`DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {i j : ι},   i ≠ j → ∀ (x : ↥(A i)),
 ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ↑x) j = 0
参数：h : DirectSum.IsInternal A；x : ↥(A i)；(LinearEquiv.ofBijective (DirectSum.coe
LinearMap A) h).symm ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectSum.coeLinearMap_of`：coeLinearMap_of (i : ι) (x : A i) : DirectSum
.coeLinearMap A (of (fun i => A i) i x) = x
· 使用定理 `LinearEquiv.ofBijective_symm_apply_apply`：ofBijective_symm_apply_apply [
RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) : (ofBijective f h)
.symm (f x) = x
· 使用定理 `DirectSum.of_eq_of_ne`：of_eq_of_ne (i j : ι) (x : β i) (h : j != i) : (o
f _ i x) j = 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem IsInternal.ofBijective_coeLinearMap_of_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) (x : A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 := by
  rw [← coeLinearMap_of, LinearEquiv.ofBijective_symm_apply_apply, of_eq_of_ne i j _ hij.symm]
/-
**DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem** 是 Mathlib 中的一个定理，位于命名空间
 `DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {i : ι} {x : M} (hx : x ∈ A i),   ((
LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm x) i = ⟨x, hx⟩
参数：h : DirectSum.IsInternal A；hx : x ∈ A i；(LinearEquiv.ofBijective (DirectSum.c
oeLinearMap A) h).symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.IsInternal.ofBijective_coeLinearMap_same`：∀ {R : Type u} [inst
 : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : Add
CommMonoid M]   [inst_2 : _root_.Module …
-/
theorem IsInternal.ofBijective_coeLinearMap_of_mem (h : IsInternal A)
    {i : ι} {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x i = ⟨x, hx⟩ :=
  h.ofBijective_coeLinearMap_same ⟨x, hx⟩
/-
**DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne** 是 Mathlib 中的一个定理，位于命
名空间 `DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {i j : ι},   i ≠ j → ∀ {x : M}, x ∈ 
A i → ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm x) j = 0
参数：h : DirectSum.IsInternal A；(LinearEquiv.ofBijective (DirectSum.coeLinearMap A
) h).symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.IsInternal.ofBijective_coeLinearMap_of_ne`：∀ {R : Type u} [ins
t : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : Ad
dCommMonoid M]   [inst_2 : _root_.Module …
-/
theorem IsInternal.ofBijective_coeLinearMap_of_mem_ne (h : IsInternal A)
    {i j : ι} (hij : i ≠ j) {x : M} (hx : x ∈ A i) :
    (LinearEquiv.ofBijective (coeLinearMap A) h).symm x j = 0 :=
  h.ofBijective_coeLinearMap_of_ne hij ⟨x, hx⟩

/-- If a direct sum of submodules is internal then the submodules span the module. -/
/-
**DirectSum.IsInternal.submodule_iSup_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `DirectSu
m.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M}, DirectSum.IsInternal A → iSup A = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f

--- 原说明 ---
If a direct sum of submodules is internal then the submodules span the module.
-/
theorem IsInternal.submodule_iSup_eq_top (h : IsInternal A) : iSup A = ⊤ := by
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

/-- If a direct sum of submodules is internal then the submodules are independent. -/
/-
**DirectSum.IsInternal.submodule_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.
IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M}, DirectSum.IsInternal A → iSupIndep A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep_of_dfinsupp_lsum_injective`：iSupIndep_of_dfinsupp_lsum_injecti
ve (p : ι -> Submodule R N) (h : Function.Injective (lsum Nat fun i => (p i).sub
type)) : iSupIndep p
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f

--- 原说明 ---
If a direct sum of submodules is internal then the submodules are independent.
-/
theorem IsInternal.submodule_iSupIndep (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsupp_lsum_injective _ h.injective

/-- Given an internal direct sum decomposition of a module `M`, and a basis for each of the
components of the direct sum, the disjoint union of these bases is a basis for `M`. -/
/-
**DirectSum.IsInternal.collectedBasis** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.IsInt
ernal`。
形式化陈述：{R : Type u} →   [inst : Semiring R] →     {ι : Type v} →       [dec_ι : D
ecidableEq ι] →         {M : Type u_1} →           [inst_1 : AddCommMonoid M] → 
            [inst_2 : _root_.Module R M] →               {A : ι → Submodule R M}
 →                 DirectSum.IsInternal A →                   {α : ι → Type u_2}
 → ((i : ι) → Module.Basis (α i) R ↥(A i)) → Module.Basis ((i : ι) × α i) R M
参数：(i : ι) → Module.Basis (α i) R ↥(A i)；(i : ι) × α i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an internal direct sum decomposition of a module `M`, and a basis for each
 of the
components of the direct sum, the disjoint union of these bases is a basis for `
M`.
-/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : Basis (Σ i, α i) R M where
  repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h).symm ≪≫ₗ
        DFinsupp.mapRange.linearEquiv fun i ↦ (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDFinsupp R).symm

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**DirectSum.IsInternal.collectedBasis_coe** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.I
sInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {α : ι → Type u_2}   (v : (i : ι) → 
Module.Basis (α i) R ↥(A i)), ⇑(h.collectedBasis v) = fun a => ↑((v a.fst) a.snd
)
参数：h : DirectSum.IsInternal A；v : (i : ι) → Module.Basis (α i) R ↥(A i)；h.collec
tedBasis v；(v a.fst) a.snd。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用定理 `sigmaFinsuppLequivDFinsupp_apply`：∀ {ι : Type u_1} (R : Type u_2) {η : ι
 → Type u_4} {N : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid N]   [in
st_2 : _root_.Module R…
· 使用定理 `sigmaFinsuppAddEquivDFinsupp_apply`：∀ {ι : Type u_1} {η : ι → Type u_4} 
{N : Type u_5} [inst : AddZeroClass N] (a : (i : ι) × η i →₀ N),   sigmaFinsuppA
ddEquivDFinsupp a = sigm…
· 使用定理 `sigmaFinsuppEquivDFinsupp_single`：sigmaFinsuppEquivDFinsupp_single [Deci
dableEq ι] [Zero N] (a : Σ i, η i) (n : N) : sigmaFinsuppEquivDFinsupp (Finsupp.
single a n) = @DFinsup…
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `DFinsupp.mapRange.congr_simp`：∀ {ι : Type u} {β₁ : ι → Type v₁} {β₂ : ι 
→ Type v₂} [inst : (i : ι) → Zero (β₁ i)] [inst_1 : (i : ι) → Zero (β₂ i)]   (f 
f_1 : (i : ι) → β₁…
· 使用定理 `DFinsupp.mapRange_single`：mapRange_single {f : forall i, β₁ i -> β₂ i} {
hf : forall i, f i 0 = 0} {i : ι} {b : β₁ i} : mapRange f hf (single i b) = sing
le i (f i b)
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `DFinsupp.sumAddHom_single`：sumAddHom_single [forall i, AddZeroClass (β i
)] [AddCommMonoid γ] (φ : forall i, β i ->+ γ) (i) (x : β i) : sumAddHom φ (sing
le i x) = φ i x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInternal.collectedBasis_coe (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) : ⇑(h.collectedBasis v) = fun a : Σ i, α i ↦ ↑(v a.1 a.2) := by
  simp [IsInternal.collectedBasis, coeLinearMap, DFinsupp.mapRange.linearEquiv,
    toModule, DFinsupp.lsum]
/-
**DirectSum.IsInternal.collectedBasis_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.I
sInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {α : ι → Type u_2}   (v : (i : ι) → 
Module.Basis (α i) R ↥(A i)) (a : (i : ι) × α i), (h.collectedBasis v) a ∈ A a.f
st
参数：h : DirectSum.IsInternal A；v : (i : ι) → Module.Basis (α i) R ↥(A i)；a : (i :
 ι) × α i；h.collectedBasis v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
-/
theorem IsInternal.collectedBasis_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) (a : Σ i, α i) : h.collectedBasis v a ∈ A a.1 := by simp

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.IsInternal.collectedBasis_repr_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Dir
ectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {α : ι → Type u_2}   (v : (i : ι) → 
Module.Basis (α i) R ↥(A i)) {x : M} {i : ι} {a : α i} (hx : x ∈ A i),   ((h.col
lectedBasis v).repr x) ⟨i, a⟩ = ((v i).repr ⟨x, hx⟩) a
参数：h : DirectSum.IsInternal A；v : (i : ι) → Module.Basis (α i) R ↥(A i)；hx : x ∈
 A i；(h.collectedBasis v).repr x；(v i).repr ⟨x, hx⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `sigmaFinsuppLequivDFinsupp_symm_apply`：∀ {ι : Type u_1} (R : Type u_2) {
η : ι → Type u_4} {N : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid N] 
  [inst_2 : _root_.Module R…
· 使用定理 `sigmaFinsuppAddEquivDFinsupp_symm_apply`：∀ {ι : Type u_1} {η : ι → Type 
u_4} {N : Type u_5} [inst : AddZeroClass N] (a : Π₀ (i : ι), η i →₀ N),   sigmaF
insuppAddEquivDFinsupp.symm a…
· 使用定理 `DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem`：∀ {R : Type u} [in
st : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : A
ddCommMonoid M]   [inst_2 : _root_.Module …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInternal.collectedBasis_repr_of_mem (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i : ι} {a : α i} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨i, a⟩ = (v i).repr ⟨x, hx⟩ a := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem hx]

set_option backward.isDefEq.respectTransparency false in
/-
**DirectSum.IsInternal.collectedBasis_repr_of_mem_ne** 是 Mathlib 中的一个定理，位于命名空间 `
DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} (h : DirectSum.IsInternal A) {α : ι → Type u_2}   (v : (i : ι) → 
Module.Basis (α i) R ↥(A i)) {x : M} {i j : ι},   i ≠ j → ∀ {a : α j}, x ∈ A i →
 ((h.collectedBasis v).repr x) ⟨j, a⟩ = 0
参数：h : DirectSum.IsInternal A；v : (i : ι) → Module.Basis (α i) R ↥(A i)；(h.colle
ctedBasis v).repr x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `sigmaFinsuppLequivDFinsupp_symm_apply`：∀ {ι : Type u_1} (R : Type u_2) {
η : ι → Type u_4} {N : Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid N] 
  [inst_2 : _root_.Module R…
· 使用定理 `sigmaFinsuppAddEquivDFinsupp_symm_apply`：∀ {ι : Type u_1} {η : ι → Type 
u_4} {N : Type u_5} [inst : AddZeroClass N] (a : Π₀ (i : ι), η i →₀ N),   sigmaF
insuppAddEquivDFinsupp.symm a…
· 使用定理 `DirectSum.IsInternal.ofBijective_coeLinearMap_of_mem_ne`：∀ {R : Type u} 
[inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 
: AddCommMonoid M]   [inst_2 : _root_.Module …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInternal.collectedBasis_repr_of_mem_ne (h : IsInternal A) {α : ι → Type*}
    (v : ∀ i, Basis (α i) R (A i)) {x : M} {i j : ι} (hij : i ≠ j) {a : α j} (hx : x ∈ A i) :
    (h.collectedBasis v).repr x ⟨j, a⟩ = 0 := by
  change (sigmaFinsuppLequivDFinsupp R).symm (DFinsupp.mapRange _ (fun i ↦ map_zero _) _) _ = _
  simp [h.ofBijective_coeLinearMap_of_mem_ne hij hx]

/-- When indexed by only two distinct elements, `DirectSum.IsInternal` implies
the two submodules are complementary. Over a `Ring R`, this is true as an iff, as
`DirectSum.isInternal_submodule_iff_isCompl`. -/
/-
**DirectSum.IsInternal.isCompl** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.IsInternal`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {ι : Type v} [dec_ι : DecidableEq ι] {M
 : Type u_1} [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] {A : ι → 
Submodule R M} {i j : ι},   i ≠ j → Set.univ = {i, j} → DirectSum.IsInternal A →
 IsCompl (A i) (A j)
参数：A i；A j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.pairwiseDisjoint`：iSupIndep.pairwiseDisjoint : Pairwise (Disjo
int on t)
· 使用定理 `DirectSum.IsInternal.submodule_iSupIndep`：∀ {R : Type u} [inst : Semirin
g R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid
 M]   [inst_2 : _root_.Module …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `DirectSum.IsInternal.submodule_iSup_eq_top`：∀ {R : Type u} [inst : Semir
ing R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMono
id M]   [inst_2 : _root_.Module …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}

--- 原说明 ---
When indexed by only two distinct elements, `DirectSum.IsInternal` implies
the two submodules are complementary. Over a `Ring R`, this is true as an iff, a
s
`DirectSum.isInternal_submodule_iff_isCompl`.
-/
theorem IsInternal.isCompl {A : ι → Submodule R M} {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_iSupIndep.pairwiseDisjoint hij,
    codisjoint_iff.mpr <| Eq.symm <| hi.submodule_iSup_eq_top.symm.trans <| by
      rw [← sSup_pair, iSup, ← Set.image_univ, h, Set.image_insert_eq, Set.image_singleton]⟩

end Semiring

section Ring

variable {R : Type u} [Ring R]
variable {ι : Type v} [dec_ι : DecidableEq ι]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details. -/
/-
**DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top** 是 Mathlib 中的一个定理，
位于命名空间 `DirectSum`。
形式化陈述：isInternal_submodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} 
(hi : iSupIndep A) (hs : iSup A = ⊤) : IsInternal A
参数：hi : iSupIndep A；hs : iSup A = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.dfinsupp_lsum_injective`：iSupIndep.dfinsupp_lsum_injective {p 
: ι -> Submodule R N} (h : iSupIndep p) : Function.Injective (lsum Nat fun i => 
(p i).subtype)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)

--- 原说明 ---
Note that this is not generally true for `[Semiring R]`; see
`iSupIndep.dfinsupp_lsum_injective` for details.
-/
theorem isInternal_submodule_of_iSupIndep_of_iSup_eq_top {A : ι → Submodule R M}
    (hi : iSupIndep A) (hs : iSup A = ⊤) : IsInternal A :=
  ⟨hi.dfinsupp_lsum_injective,
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 had to specify value of `f`
    (LinearMap.range_eq_top (f := DFinsupp.lsum _ _)).1 <|
      (Submodule.iSup_eq_range_dfinsupp_lsum _).symm.trans hs⟩

/-- `iff` version of `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`,
`DirectSum.IsInternal.iSupIndep`, and `DirectSum.IsInternal.submodule_iSup_eq_top`. -/
/-
**DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top** 是 Mathlib 中的一个定
理，位于命名空间 `DirectSum`。
形式化陈述：isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι -> Submodule R M
) : IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤
参数：A : ι -> Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.IsInternal.submodule_iSupIndep`：∀ {R : Type u} [inst : Semirin
g R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid
 M]   [inst_2 : _root_.Module …
· 使用定理 `DirectSum.IsInternal.submodule_iSup_eq_top`：∀ {R : Type u} [inst : Semir
ing R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMono
id M]   [inst_2 : _root_.Module …
· 使用定理 `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`：isInternal_s
ubmodule_of_iSupIndep_of_iSup_eq_top {A : ι -> Submodule R M} (hi : iSupIndep A)
 (hs : iSup A = ⊤) : IsInternal A

--- 原说明 ---
`iff` version of `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top`,
`DirectSum.IsInternal.iSupIndep`, and `DirectSum.IsInternal.submodule_iSup_eq_to
p`.
-/
theorem isInternal_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ iSupIndep A ∧ iSup A = ⊤ :=
  ⟨fun i ↦ ⟨i.submodule_iSupIndep, i.submodule_iSup_eq_top⟩,
    And.rec isInternal_submodule_of_iSupIndep_of_iSup_eq_top⟩

/-- If a collection of submodules has just two indices, `i` and `j`, then
`DirectSum.IsInternal` is equivalent to `isCompl`. -/
/-
**DirectSum.isInternal_submodule_iff_isCompl** 是 Mathlib 中的一个定理，位于命名空间 `DirectSu
m`。
形式化陈述：isInternal_submodule_iff_isCompl (A : ι -> Submodule R M) {i j : ι} (hij :
 i != j) (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j)
参数：A : ι -> Submodule R M；hij : i != j；h : (Set.univ : Set ι) = {i, j}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
· 使用定理 `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`：isInternal
_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι -> Submodule R M) : IsInternal A
 ↔ iSupIndep A ∧ iSup A = ⊤
· 使用定理 `iSup.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : SupSet α] (s : ι → α), iS
up s = sSup (Set.range s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `sSup_pair`：sSup_pair {a b : α} : sSup {a, b} = a ⊔ b
· 使用定理 `iSupIndep_pair`：iSupIndep_pair {i j : ι} (hij : i != j) (huniv : forall 
k, k = i ∨ k = j) : iSupIndep t ↔ Disjoint (t i) (t j)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `Codisjoint.eq_top`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → a ⊔ b = ⊤

--- 原说明 ---
If a collection of submodules has just two indices, `i` and `j`, then
`DirectSum.IsInternal` is equivalent to `isCompl`.
-/
theorem isInternal_submodule_iff_isCompl (A : ι → Submodule R M) {i j : ι} (hij : i ≠ j)
    (h : (Set.univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : ∀ k, k = i ∨ k = j := fun k ↦ by simpa using Set.ext_iff.mp h k
  rw [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top, iSup, ← Set.image_univ, h,
    Set.image_insert_eq, Set.image_singleton, sSup_pair, iSupIndep_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ ↦ ⟨hd, codisjoint_iff.mpr ht⟩, fun ⟨hd, ht⟩ ↦ ⟨hd, ht.eq_top⟩⟩

@[simp]
/-
**DirectSum.isInternal_ne_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：isInternal_ne_bot_iff {A : ι -> Submodule R M} : IsInternal (fun i : {i //
 A i != ⊥} => A i) ↔ IsInternal A
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_ne_bot_subtype`：iSup_ne_bot_subtype (f : ι -> α) : ⨆ i : { i // f i
 != ⊥ }, f i = ⨆ i, f i
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isInternal_ne_bot_iff {A : ι → Submodule R M} :
    IsInternal (fun i : {i // A i ≠ ⊥} ↦ A i) ↔ IsInternal A := by
  simp [isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
/-
**DirectSum.isInternal_biSup_submodule_of_iSupIndep** 是 Mathlib 中的一个引理，位于命名空间 `D
irectSum`。
形式化陈述：isInternal_biSup_submodule_of_iSupIndep {A : ι -> Submodule R M} (s : Set 
ι) (h : iSupIndep <| fun i : s => A i) : IsInternal fun (i : s) => (A i).comap (
⨆ i in s, A i).subtype
参数：s : Set ι；h : iSupIndep <| fun i : s => A i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top`：isInternal
_submodule_iff_iSupIndep_and_iSup_eq_top (A : ι -> Submodule R M) : IsInternal A
 ↔ iSupIndep A ∧ iSup A = ⊤
· 使用引理 `le_biSup`：le_biSup {ι : Type*} {s : Set ι} (f : ι -> α) {i : ι} (hi : i 
in s) : f i <= ⨆ i in s, f i
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `iSupIndep_map_orderIso_iff`：iSupIndep_map_orderIso_iff {ι : Sort*} {α β 
: Type*} [CompleteLattice α] [CompleteLattice β] (f : α ≃o β) {a : ι -> α} : iSu
pIndep (f ∘ a) ↔…
· 使用引理 `iSupIndep.of_coe_Iic_comp`：iSupIndep.of_coe_Iic_comp {ι : Sort*} {a : α}
 {t : ι -> Set.Iic a} (ht : iSupIndep ((↑) ∘ t : ι -> α)) : iSupIndep t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用引理 `Submodule.biSup_comap_subtype_eq_top`：biSup_comap_subtype_eq_top {ι : Ty
pe*} (s : Set ι) (p : ι -> Submodule R M) : ⨆ i in s, (p i).comap (⨆ i in s, p i
).subtype = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isInternal_biSup_submodule_of_iSupIndep {A : ι → Submodule R M} (s : Set ι)
    (h : iSupIndep <| fun i : s ↦ A i) :
    IsInternal <| fun (i : s) ↦ (A i).comap (⨆ i ∈ s, A i).subtype := by
  refine (isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, by simp [iSup_subtype]⟩
  let p := ⨆ i ∈ s, A i
  have hp : ∀ i ∈ s, A i ≤ p := fun i hi ↦ le_biSup A hi
  let e : Submodule R p ≃o Set.Iic p := p.mapIic
  suffices (e ∘ fun i : s ↦ (A i).comap p.subtype) = fun i ↦ ⟨A i, hp i i.property⟩ by
    rw [← iSupIndep_map_orderIso_iff e, this]
    exact .of_coe_Iic_comp h
  ext i m
  change m ∈ ((A i).comap p.subtype).map p.subtype ↔ _
  rw [Submodule.map_comap_subtype, inf_of_le_right (hp i i.property)]

/-! Now copy the lemmas for subgroup and submonoids. -/


/-
**DirectSum.IsInternal.addSubmonoid_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `DirectS
um.IsInternal`。
形式化陈述：∀ {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_2} [inst : AddCommMonoi
d M] {A : ι → AddSubmonoid M},   DirectSum.IsInternal A → iSupIndep A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用定理 `iSupIndep_of_dfinsuppSumAddHom_injective`：iSupIndep_of_dfinsuppSumAddHom
_injective (p : ι -> AddSubmonoid N) (h : Function.Injective (sumAddHom fun i =>
 (p i).subtype)) : iSupIndep p
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f

--- 原说明 ---
Now copy the lemmas for subgroup and submonoids.
-/
theorem IsInternal.addSubmonoid_iSupIndep {M : Type*} [AddCommMonoid M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsuppSumAddHom_injective _ h.injective
/-
**DirectSum.IsInternal.addSubgroup_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `DirectSu
m.IsInternal`。
形式化陈述：∀ {ι : Type v} [dec_ι : DecidableEq ι] {G : Type u_2} [inst : AddCommGroup
 G] {A : ι → AddSubgroup G},   DirectSum.IsInternal A → iSupIndep A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AddSubgroup.instAddSubgroupClass`：∀ {G : Type u_1} [inst : AddGroup G], 
AddSubgroupClass (AddSubgroup G) G
· 使用定理 `iSupIndep_of_dfinsuppSumAddHom_injective'`：iSupIndep_of_dfinsuppSumAddHo
m_injective' (p : ι -> AddSubgroup N) (h : Function.Injective (sumAddHom fun i =
> (p i).subtype)) : iSupIndep p
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
-/
theorem IsInternal.addSubgroup_iSupIndep {G : Type*} [AddCommGroup G] {A : ι → AddSubgroup G}
    (h : IsInternal A) : iSupIndep A :=
  iSupIndep_of_dfinsuppSumAddHom_injective' _ h.injective

end Ring

end Submodule

section Congr

variable {R : Type*} [Semiring R]
    {ι : Type*}
    {N : ι → Type*} [(i : ι) → AddCommMonoid (N i)] [(i : ι) → Module R (N i)]
    {P : ι → Type*} [∀ i, AddCommMonoid (P i)] [∀ i, Module R (P i)]

/-- Direct sums of isomorphic additive groups are isomorphic. -/
/-
**DirectSum.congrAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：congrAddEquiv (u : (i : ι) -> N i ≃+ P i) : (⨁ i, N i) ≃+ ⨁ i, P i where t
oAddHom
参数：u : (i : ι) -> N i ≃+ P i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Direct sums of isomorphic additive groups are isomorphic.
-/
def congrAddEquiv (u : (i : ι) → N i ≃+ P i) :
    (⨁ i, N i) ≃+ ⨁ i, P i where
  toAddHom := DirectSum.map fun i ↦ (u i).toAddMonoidHom
  invFun := DirectSum.map fun i ↦ (u i).symm.toAddMonoidHom
  left_inv x := by aesop
  right_inv y := by aesop
/-
**DirectSum.coe_congrAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_congrAddEquiv (u : (i : ι) -> N i ≃+ P i) : ⇑(congrAddEquiv u).toAddMo
noidHom = ⇑(DirectSum.map fun i => (u i).toAddMonoidHom)
参数：u : (i : ι) -> N i ≃+ P i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_congrAddEquiv (u : (i : ι) → N i ≃+ P i) :
    ⇑(congrAddEquiv u).toAddMonoidHom = ⇑(DirectSum.map fun i ↦ (u i).toAddMonoidHom) :=
  rfl

/-- Direct sums of isomorphic modules are isomorphic. -/
/-
**DirectSum.congrLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：congrLinearEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) : (⨁ i, N i) ≃ₗ[R] ⨁ i, P 
i where toAddEquiv
参数：u : (i : ι) -> N i ≃ₗ[R] P i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Direct sums of isomorphic modules are isomorphic.
-/
def congrLinearEquiv (u : (i : ι) → N i ≃ₗ[R] P i) :
    (⨁ i, N i) ≃ₗ[R] ⨁ i, P i where
  toAddEquiv := congrAddEquiv (fun i ↦ (u i).toAddEquiv)
  map_smul' r x := by
    exact (DirectSum.lmap (fun i ↦ (u i).toLinearMap)).map_smul r x
/-
**DirectSum.coe_congrLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_congrLinearEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) : ⇑(congrLinearEquiv u
) = ⇑(DirectSum.lmap (fun i => (u i).toLinearMap))
参数：u : (i : ι) -> N i ≃ₗ[R] P i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_congrLinearEquiv (u : (i : ι) → N i ≃ₗ[R] P i) :
    ⇑(congrLinearEquiv u) = ⇑(DirectSum.lmap (fun i ↦ (u i).toLinearMap)) :=
  rfl
/-
**DirectSum.congrLinearEquiv_toAddEquiv** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：congrLinearEquiv_toAddEquiv (u : (i : ι) -> N i ≃ₗ[R] P i) : (congrLinearE
quiv u).toAddEquiv = congrAddEquiv (fun i => (u i).toAddEquiv)
参数：u : (i : ι) -> N i ≃ₗ[R] P i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLinearEquiv_toAddEquiv (u : (i : ι) → N i ≃ₗ[R] P i) :
    (congrLinearEquiv u).toAddEquiv = congrAddEquiv (fun i ↦ (u i).toAddEquiv) :=
  rfl
/-
**DirectSum.congrLinearEquiv_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：congrLinearEquiv_toLinearMap (u : (i : ι) -> N i ≃ₗ[R] P i) : (congrLinear
Equiv u).toLinearMap = DirectSum.lmap (fun i => (u i).toLinearMap)
参数：u : (i : ι) -> N i ≃ₗ[R] P i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congrLinearEquiv_toLinearMap (u : (i : ι) → N i ≃ₗ[R] P i) :
    (congrLinearEquiv u).toLinearMap = DirectSum.lmap (fun i ↦ (u i).toLinearMap) :=
  rfl

end Congr

end DirectSum

