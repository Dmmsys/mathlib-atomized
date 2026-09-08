/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.GradedMulAction

/-!
# Homogeneous submodules of a graded module

This file defines homogeneous submodule of a graded module `⨁ᵢ ℳᵢ` over graded ring `⨁ᵢ 𝒜ᵢ` and
operations on them.

## Main definitions

For any `p : Submodule A M`:
* `Submodule.IsHomogeneous ℳ p`: The property that a submodule is closed under `GradedModule.proj`.
* `HomogeneousSubmodule 𝒜 ℳ`: The structure extending submodules which satisfy
  `Submodule.IsHomogeneous`.

## Implementation notes

The **notion** of homogeneous submodule does not rely on a graded ring, only a decomposition of the
module. However, most interesting properties of homogeneous submodules do rely on the base ring
being a graded ring. For technical reasons, we make `HomogeneousSubmodule` depend on a graded ring.
For example, if the definition of a homogeneous submodule does not depend on a graded ring, the
instance that `HomogeneousSubmodule` is a complete lattice cannot be synthesized due to
synthesization order.

## Tags

graded algebra, homogeneous
-/

@[expose] public section

open SetLike DirectSum Pointwise Set

variable {ιA ιM σA σM A M : Type*}

variable [Semiring A] [AddCommMonoid M] [Module A M]

section HomogeneousDef

/--
An `A`-submodule `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous components of `m` are
in `p`.
-/
/-
**Submodule.IsHomogeneous** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM -> σM) [DecidableEq ιM
] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop
参数：p : Submodule A M；ℳ : ιM -> σM。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `A`-submodule `p ⊆ M` is homogeneous if for every `m ∈ p`, all homogeneous co
mponents of `m` are
in `p`.
-/
def Submodule.IsHomogeneous (p : Submodule A M) (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] : Prop :=
  SetLike.IsHomogeneous ℳ p
/-
**Submodule.IsHomogeneous.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.IsHomogeneous.mem_iff {p : Submodule A M} (ℳ : ιM -> σM) [Decida
bleEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ] (hp : p.IsHo
mogeneous ℳ) {x} : x in p ↔ forall i, (decompose ℳ x i : M) in p
参数：ℳ : ιM -> σM；hp : p.IsHomogeneous ℳ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectSum.AddSubmonoidClass.IsHomogeneous.mem_iff`：∀ {ι : Type u_1} {M :
 Type u_3} {σ : Type u_4} [inst : DecidableEq ι] [inst_1 : AddCommMonoid M] [ins
t_2 : SetLike σ M]   [inst_3 : AddSubmo…
-/
theorem Submodule.IsHomogeneous.mem_iff {p : Submodule A M}
    (ℳ : ιM → σM)
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    (hp : p.IsHomogeneous ℳ) {x} :
    x ∈ p ↔ ∀ i, (decompose ℳ x i : M) ∈ p :=
  AddSubmonoidClass.IsHomogeneous.mem_iff ℳ _ hp

/-- For any `Semiring A`, we collect the homogeneous submodule of `A`-modules into a type. -/
/-
**HomogeneousSubmodule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ιA : Type u_1} →   {ιM : Type u_2} →     {σA : Type u_3} →       {σM : Ty
pe u_4} →         {A : Type u_5} →           {M : Type u_6} →             [inst 
: Semiring A] →               [inst_1 : AddCommMonoid M] →                 [inst
_2 : _root_.Module A M] →                   (𝒜 : ιA → σA) →                     
(ℳ : ιM → σM) →                       [inst_3 : DecidableEq ιA] →               
          [inst_4 : AddMonoid ιA] →                           [inst_5 : SetLike 
σA A] →                             [inst_6 : AddSubmonoidClass σA A] →         
                      [GradedRing 𝒜] →                                 [inst_8 :
 DecidableEq ιM] →                                   [inst_9 : SetLike σM M] →  
                                   [inst_10 : AddSubmonoidClass σM M] →         
                              [DirectSum.Decomposition ℳ] →                     
                    [inst_12 : VAdd ιA ιM] → [SetLike.GradedSMul 𝒜 ℳ] → Type u_6
参数：𝒜 : ιA → σA；ℳ : ιM → σM。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any `Semiring A`, we collect the homogeneous submodule of `A`-modules into a
 type.
-/
structure HomogeneousSubmodule (𝒜 : ιA → σA) (ℳ : ιM → σM)
    [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
    [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
    [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
    extends Submodule A M where
  is_homogeneous' : toSubmodule.IsHomogeneous ℳ

variable (𝒜 : ιA → σA) (ℳ : ιM → σM)
variable [DecidableEq ιA] [AddMonoid ιA] [SetLike σA A] [AddSubmonoidClass σA A] [GradedRing 𝒜]
variable [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σM M] [Decomposition ℳ]
variable [VAdd ιA ιM] [GradedSMul 𝒜 ℳ]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe X := X.toSubmodule
  coe_injective := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ (h : (p : Set M) = q)
    simpa using h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddSubmonoidClass (HomogeneousSubmodule 𝒜 ℳ) M where
  zero_mem p := p.toSubmodule.zero_mem
  add_mem hx hy := Submodule.add_mem _ hx hy
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulMemClass (HomogeneousSubmodule 𝒜 ℳ) A M where
  smul_mem := by
    intro x r m hm
    exact Submodule.smul_mem x.toSubmodule r hm

variable {𝒜 ℳ} in
/-
**HomogeneousSubmodule.isHomogeneous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) : p.toSu
bmodule.IsHomogeneous ℳ
参数：p : HomogeneousSubmodule 𝒜 ℳ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.is_homogeneous'`：∀ {ιA : Type u_1} {ιM : Type u_2} 
{σA : Type u_3} {σM : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A
]   [inst_1 : AddCommMonoi…
-/
theorem HomogeneousSubmodule.isHomogeneous (p : HomogeneousSubmodule 𝒜 ℳ) :
    p.toSubmodule.IsHomogeneous ℳ :=
  p.is_homogeneous'
/-
**HomogeneousSubmodule.toSubmodule_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.toSubmodule_injective : Function.Injective (Homogeneo
usSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ -> Submodule A M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousSubmodule.mk.congr_simp`：∀ {ιA : Type u_1} {ιM : Type u_2} {σ
A : Type u_3} {σM : Type u_4} {A : Type u_5} {M : Type u_6} [inst : Semiring A] 
  [inst_1 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem HomogeneousSubmodule.toSubmodule_injective :
    Function.Injective
      (HomogeneousSubmodule.toSubmodule : HomogeneousSubmodule 𝒜 ℳ → Submodule A M) :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ fun (h : x = y) ↦ by simp [h]
/-
**HomogeneousSubmodule.setLike** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where 
coe p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance HomogeneousSubmodule.setLike : SetLike (HomogeneousSubmodule 𝒜 ℳ) M where
  coe p := p.toSubmodule
  coe_injective _ _ h := HomogeneousSubmodule.toSubmodule_injective 𝒜 ℳ <| SetLike.coe_injective h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (HomogeneousSubmodule 𝒜 ℳ) := .ofSetLike (HomogeneousSubmodule 𝒜 ℳ) M

@[ext]
/-
**HomogeneousSubmodule.ext** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.ext {I J : HomogeneousSubmodule 𝒜 ℳ} (h : I.toSubmodu
le = J.toSubmodule) : I = J
参数：h : I.toSubmodule = J.toSubmodule。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.toSubmodule_injective`：HomogeneousSubmodule.toSubmo
dule_injective : Function.Injective (HomogeneousSubmodule.toSubmodule : Homogene
ousSubmodule 𝒜 ℳ -> Submodule A …
-/
theorem HomogeneousSubmodule.ext
    {I J : HomogeneousSubmodule 𝒜 ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J :=
  HomogeneousSubmodule.toSubmodule_injective _ _ h

/--
The set-theoretic extensionality of `HomogeneousSubmodule`.
-/
/-
**HomogeneousSubmodule.ext'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.ext' {I J : HomogeneousSubmodule 𝒜 ℳ} (h : forall i, 
forall x in ℳ i, x in I ↔ x in J) : I = J
参数：h : forall i, forall x in ℳ i, x in I ↔ x in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HomogeneousSubmodule.ext`：HomogeneousSubmodule.ext {I J : HomogeneousSub
module 𝒜 ℳ} (h : I.toSubmodule = J.toSubmodule) : I = J
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.IsHomogeneous.mem_iff`：Submodule.IsHomogeneous.mem_iff {p : Su
bmodule A M} (ℳ : ιM -> σM) [DecidableEq ιM] [SetLike σM M] [AddSubmonoidClass σ
M M] [Decomposition ℳ…
· 使用定理 `HomogeneousSubmodule.isHomogeneous`：HomogeneousSubmodule.isHomogeneous (
p : HomogeneousSubmodule 𝒜 ℳ) : p.toSubmodule.IsHomogeneous ℳ
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The set-theoretic extensionality of `HomogeneousSubmodule`.
-/
theorem HomogeneousSubmodule.ext' {I J : HomogeneousSubmodule 𝒜 ℳ}
    (h : ∀ i, ∀ x ∈ ℳ i, x ∈ I ↔ x ∈ J) :
    I = J := by
  ext
  rw [I.isHomogeneous.mem_iff, J.isHomogeneous.mem_iff]
  apply forall_congr'
  exact fun i ↦ h i _ (decompose ℳ _ i).2

@[simp]
/-
**HomogeneousSubmodule.mem_toSubmodule_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HomogeneousSubmodule.mem_toSubmodule_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x
 : M} : x in I.toSubmodule (A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem HomogeneousSubmodule.mem_toSubmodule_iff {I : HomogeneousSubmodule 𝒜 ℳ} {x : M} :
    x ∈ I.toSubmodule (A := A) ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

