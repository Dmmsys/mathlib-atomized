/-
Copyright (c) 2025 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Span.Defs

/-!
# Subrepresentations

This file defines subrepresentations of a monoid representation.

-/

@[expose] public section

open scoped Pointwise
open scoped MonoidAlgebra

variable {A G W M : Type*}

variable [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  (ρ : Representation A G W) [AddCommMonoid M] [Module A[G] M] in
/-- A subrepresentation of `G` of the `A`-module `W` is a submodule of `W`
which is stable under the `G`-action.
-/
@[ext]
/-
**Subrepresentation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{A : Type u_1} →   {G : Type u_2} →     {W : Type u_3} →       [inst : Sem
iring A] →         [inst_1 : Monoid G] →           [inst_2 : AddCommMonoid W] → 
[inst_3 : _root_.Module A W] → Representation A G W → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subrepresentation of `G` of the `A`-module `W` is a submodule of `W`
which is stable under the `G`-action.
-/
structure Subrepresentation where
  /-- A subrepresentation is a submodule. -/
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v ∈ toSubmodule → ρ g v ∈ toSubmodule

namespace Subrepresentation

section non_comm

variable [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W] {ρ : Representation A G W}
  [AddCommMonoid M] [Module A[G] M]

/-
**Subrepresentation.toSubmodule_injective** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresen
tation`。
形式化陈述：toSubmodule_injective : Function.Injective (toSubmodule : Subrepresentatio
n ρ -> Submodule A W)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subrepresentation.apply_mem_toSubmodule`：∀ {A : Type u_1} {G : Type u_2}
 {W : Type u_3} [inst : Semiring A] [inst_1 : Monoid G] [inst_2 : AddCommMonoid 
W]   [inst_3 : _root_.Module …
-/
lemma toSubmodule_injective :
    Function.Injective (toSubmodule : Subrepresentation ρ → Submodule A W) := by
  rintro ⟨_, _⟩
  congr!
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (Subrepresentation ρ) W where
  coe ρ' := ρ'.toSubmodule
  coe_injective := SetLike.coe_injective.comp toSubmodule_injective
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subrepresentation ρ) := .ofSetLike (Subrepresentation ρ) W

/-- A subrepresentation is a representation. -/
/-
**Subrepresentation.toRepresentation** 是 Mathlib 中的一个定义，位于命名空间 `Subrepresentatio
n`。
形式化陈述：toRepresentation (ρ' : Subrepresentation ρ) : Representation A G ρ'.toSubm
odule where toFun g
参数：ρ' : Subrepresentation ρ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Subrepresentation.apply_mem_toSubmodule`：∀ {A : Type u_1} {G : Type u_2}
 {W : Type u_3} [inst : Semiring A] [inst_1 : Monoid G] [inst_2 : AddCommMonoid 
W]   [inst_3 : _root_.Module …

--- 原说明 ---
A subrepresentation is a representation.
-/
def toRepresentation (ρ' : Subrepresentation ρ) : Representation A G ρ'.toSubmodule where
  toFun g := (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Max (Subrepresentation ρ) where
  max ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) <| by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (Subrepresentation ρ) where
  min ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) <| by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩


@[simp, norm_cast]
/-
**Subrepresentation.coe_sup** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresentation`。
形式化陈述：coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : 
Set W)
参数：ρ₁ ρ₂ : Subrepresentation ρ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.coe_sup`：coe_sup : ↑(p ⊔ p') = (p + p' : Set M)
-/
lemma coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W) :=
  Submodule.coe_sup ρ₁.toSubmodule ρ₂.toSubmodule

@[simp, norm_cast]
/-
**Subrepresentation.coe_inf** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresentation`。
形式化陈述：coe_inf (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊓ ρ₂) = (ρ₁ inter ρ₂ : Set W)
参数：ρ₁ ρ₂ : Subrepresentation ρ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_inf (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊓ ρ₂) = (ρ₁ ∩ ρ₂ : Set W) := rfl

@[simp]
/-
**Subrepresentation.toSubmodule_sup** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresentation
`。
形式化陈述：toSubmodule_sup (ρ₁ ρ₂ : Subrepresentation ρ) : (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁
.toSubmodule ⊔ ρ₂.toSubmodule
参数：ρ₁ ρ₂ : Subrepresentation ρ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_sup (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := rfl

@[simp]
/-
**Subrepresentation.toSubmodule_inf** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresentation
`。
形式化陈述：toSubmodule_inf (ρ₁ ρ₂ : Subrepresentation ρ) : (ρ₁ ⊓ ρ₂).toSubmodule = ρ₁
.toSubmodule ⊓ ρ₂.toSubmodule
参数：ρ₁ ρ₂ : Subrepresentation ρ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSubmodule_inf (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊓ ρ₂).toSubmodule = ρ₁.toSubmodule ⊓ ρ₂.toSubmodule := rfl
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Lattice (Subrepresentation ρ) :=
  toSubmodule_injective.lattice _ .rfl .rfl toSubmodule_sup toSubmodule_inf
/-
**Subrepresentation.** 是 Mathlib 中的一个实例，位于命名空间 `Subrepresentation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : BoundedOrder (Subrepresentation ρ) where
  top := ⟨⊤, by simp⟩
  le_top _ := le_top (α := Submodule A W)
  bot := ⟨⊥, by simp⟩
  bot_le _ := bot_le (α := Submodule A W)

end non_comm

variable [CommSemiring A] [Monoid G] [AddCommMonoid W] [Module A W]
  {ρ : Representation A G W} [AddCommMonoid M] [Module A[G] M]

set_option backward.isDefEq.respectTransparency false in
/-- A subrepresentation of `ρ` can be thought of as an `A[G]` submodule of `ρ.asModule`.
-/
/-
**Subrepresentation.asSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Subrepresentation`。
形式化陈述：asSubmodule (σ : Subrepresentation ρ) : Submodule A[G] ρ.asModule where __
参数：σ : Subrepresentation ρ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subrepresentation of `ρ` can be thought of as an `A[G]` submodule of `ρ.asModu
le`.
-/
def asSubmodule (σ : Subrepresentation ρ) : Submodule A[G] ρ.asModule where
  __ := σ.toSubmodule
  smul_mem' c v hv := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp [zero_smul]
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [Representation.single_smul]
      exact σ.toSubmodule.smul_mem' a (σ.apply_mem_toSubmodule g hv)

@[simp]
/-
**Subrepresentation.mem_asSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresenta
tion`。
形式化陈述：mem_asSubmodule_iff {σ : Subrepresentation ρ} {v : W} : v in asSubmodule σ
 ↔ v in σ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_asSubmodule_iff {σ : Subrepresentation ρ} {v : W} : v ∈ asSubmodule σ ↔ v ∈ σ := by rfl

/-- A subrepresentation of `ofModule M` can be thought of as an `A[G]` submodule of `M`.
-/
/-
**Subrepresentation.asSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `Subrepresentation`。
形式化陈述：asSubmodule' (σ : Subrepresentation (Representation.ofModule (k
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subrepresentation of `ofModule M` can be thought of as an `A[G]` submodule of 
`M`.
-/
def asSubmodule' (σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)) :
    Submodule A[G] M where
  __ := σ.toSubmodule
  smul_mem' c m hm := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [← mul_one a, ← smul_eq_mul, ← MonoidAlgebra.smul_single, Algebra.smul_def, mul_smul]
      exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) <| by
        simpa [Representation.ofModule, RestrictScalars.lsmul] using! σ.apply_mem_toSubmodule g hm

@[simp]
/-
**Subrepresentation.mem_asSubmodule'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subrepresent
ation`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {M : Type u_4} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module (MonoidAlg
ebra A G) M] {σ : Subrepresentation (Representation.ofModule M)} {m : M},   m ∈ 
σ.asSubmodule' ↔ m ∈ σ
参数：MonoidAlgebra A G；Representation.ofModule M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_asSubmodule'_iff {σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)}
    {m : M} : m ∈ asSubmodule' σ ↔ m ∈ σ := by rfl

/-- A submodule of an `A[G]`-module `M` can be thought of as a subrepresentation of `ofModule M`.
-/
/-
**Subrepresentation.ofSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Subrepresentation`。
形式化陈述：ofSubmodule (N : Submodule A[G] M) : Subrepresentation (Representation.ofM
odule (k
参数：N : Submodule A[G] M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule of an `A[G]`-module `M` can be thought of as a subrepresentation of 
`ofModule M`.
-/
def ofSubmodule (N : Submodule A[G] M) :
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toSubmodule := { N with
    smul_mem' a m hm := N.smul_mem' (algebraMap A A[G] a) hm }
  apply_mem_toSubmodule g v hv := by
    simpa [Representation.ofModule, RestrictScalars.lsmul] using!
      Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

@[simp]
/-
**Subrepresentation.mem_ofSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空间 `Subrepresenta
tion`。
形式化陈述：mem_ofSubmodule_iff {N : Submodule A[G] M} {m : M} : m in ofSubmodule N ↔ 
m in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofSubmodule_iff {N : Submodule A[G] M} {m : M} : m ∈ ofSubmodule N ↔ m ∈ N := by rfl

set_option backward.isDefEq.respectTransparency false in
/-- An `A[G]`-submodule of `ρ.asModule` can be thought of as a subrepresentation of `ρ`.
-/
/-
**Subrepresentation.ofSubmodule'** 是 Mathlib 中的一个定义，位于命名空间 `Subrepresentation`。
形式化陈述：ofSubmodule' (N : Submodule A[G] ρ.asModule) : Subrepresentation ρ where t
oSubmodule
参数：N : Submodule A[G] ρ.asModule。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `A[G]`-submodule of `ρ.asModule` can be thought of as a subrepresentation of 
`ρ`.
-/
def ofSubmodule' (N : Submodule A[G] ρ.asModule) : Subrepresentation ρ where
  toSubmodule := { N with
    smul_mem' a w hw := by simpa using! (N.smul_mem (algebraMap A A[G] a) hw) }
  apply_mem_toSubmodule g w hw := by
    let _ : Module A[G] W := ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w ∈ N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul, one_smul] at h
    exact h

@[simp]
/-
**Subrepresentation.mem_ofSubmodule'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subrepresent
ation`。
形式化陈述：∀ {A : Type u_1} {G : Type u_2} {W : Type u_3} [inst : CommSemiring A] [in
st_1 : Monoid G] [inst_2 : AddCommMonoid W]   [inst_3 : _root_.Module A W] {ρ : 
Representation A G W} {N : Submodule (MonoidAlgebra A G) ρ.asModule} {w : W},   
w ∈ Subrepresentation.ofSubmodule' N ↔ w ∈ N
参数：MonoidAlgebra A G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_ofSubmodule'_iff {N : Submodule A[G] ρ.asModule} {w : W} : w ∈ ofSubmodule' N ↔ w ∈ N :=
  .rfl

/-- An order-preserving equivalence between subrepresentations of `ρ` and submodules of
`ρ.asModule`. -/
@[simps]
/-
**Subrepresentation.subrepresentationSubmoduleOrderIso** 是 Mathlib 中的一个定义，位于命名空间
 `Subrepresentation`。
形式化陈述：subrepresentationSubmoduleOrderIso : Subrepresentation ρ ≃o Submodule A[G]
 ρ.asModule where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order-preserving equivalence between subrepresentations of `ρ` and submodules
 of
`ρ.asModule`.
-/
def subrepresentationSubmoduleOrderIso : Subrepresentation ρ ≃o Submodule A[G] ρ.asModule where
  toFun := asSubmodule
  invFun := ofSubmodule'
  left_inv σ := rfl
  right_inv N := rfl
  map_rel_iff' := by rfl

/-- An order-preserving equivalence between `A[G]`-submodules of an `A[G]`-module M and
subrepresentations of `ρ`. -/
@[simps]
/-
**Subrepresentation.submoduleSubrepresentationOrderIso** 是 Mathlib 中的一个定义，位于命名空间
 `Subrepresentation`。
形式化陈述：submoduleSubrepresentationOrderIso : Submodule A[G] M ≃o Subrepresentation
 (Representation.ofModule (k
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order-preserving equivalence between `A[G]`-submodules of an `A[G]`-module M 
and
subrepresentations of `ρ`.
-/
def submoduleSubrepresentationOrderIso : Submodule A[G] M ≃o
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toFun := ofSubmodule
  invFun := asSubmodule'
  left_inv N := rfl
  right_inv σ := rfl
  map_rel_iff' := by rfl

end Subrepresentation

