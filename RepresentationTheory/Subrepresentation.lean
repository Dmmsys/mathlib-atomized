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
/--
Definition of `Subrepresentation` / `Subrepresentation` 的定义

English:
structure Subrepresentation
  parameters: where
  axioms and operations (2):
    - toSubmodule : Submodule A W
    - apply_mem_toSubmodule((g : G) ⦃v) : W⦄ : v in toSubmodule -> ρ g v in toSubmodule

中文:
结构 子表示
  参数: where
  公理与运算 (2 个):
    - toSubmodule : 子模 A W
    - apply_mem_toSubmodule((g : G) ⦃v) : W⦄ : v in toSubmodule -> ρ g v in toSubmodule
-/
structure Subrepresentation where
  /-- A subrepresentation is a submodule. -/
  toSubmodule : Submodule A W
  apply_mem_toSubmodule (g : G) ⦃v : W⦄ : v in toSubmodule -> ρ g v in toSubmodule

namespace Subrepresentation

section non_comm

variable [Semiring A] [Monoid G] [AddCommMonoid W] [Module A W] {ρ : Representation A G W}
  [AddCommMonoid M] [Module A[G] M]

/--
lemma `toSubmodule_injective` / 引理 `toSubmodule_injective`

English:
lemma toSubmodule_injective
  proof: by
  rintro ⟨_, _⟩
  congr!

中文:
引理 toSubmodule_injective
  证明: by
  rintro ⟨_, _⟩
  congr!
-/
lemma toSubmodule_injective :
    Function.Injective (toSubmodule : Subrepresentation ρ -> Submodule A W) := by
  rintro ⟨_, _⟩
  congr!

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subrepresentation ρ) W
  body: ρ'.toSubmodule
  coe_injective := SetLike.coe_injective.comp toSubmodule_injective

中文:
实例 :
  签名: 集合状 (子表示 ρ) W
  定义体: ρ'.toSubmodule
  coe_injective := SetLike.coe_injective.comp toSubmodule_injective

Depends on / 依赖: toSubmodule
-/
instance : SetLike (Subrepresentation ρ) W where
  coe ρ' := ρ'.toSubmodule
  coe_injective := SetLike.coe_injective.comp toSubmodule_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subrepresentation ρ)
  body: .ofSetLike (Subrepresentation ρ) W

中文:
实例 :
  签名: 偏序 (子表示 ρ)
  定义体: .ofSetLike (Subrepresentation ρ) W

Depends on / 依赖: Subrepresentation, ofSetLike
-/
instance : PartialOrder (Subrepresentation ρ) := .ofSetLike (Subrepresentation ρ) W

/--
Definition of `toRepresentation` / `toRepresentation` 的定义

English:
definition toRepresentation
  signature: (ρ' : Subrepresentation ρ)
  body: (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

中文:
定义 toRepresentation
  签名: (ρ' : 子表示 ρ)
  定义体: (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

Depends on / 依赖: apply_mem_toSubmodule, restrict
-/
def toRepresentation (ρ' : Subrepresentation ρ) : Representation A G ρ'.toSubmodule where
  toFun g := (ρ g).restrict (ρ'.apply_mem_toSubmodule g)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (Subrepresentation ρ)
  body: .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩

中文:
实例 :
  签名: 最大值 (子表示 ρ)
  定义体: .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩

Depends on / 依赖: Submodule, Submodule.forall_mem_sup, Submodule.mem_sup.mpr, apply_mem_toSubmodule, forall_mem_sup, map_add, mem_sup, toSubmodule
-/
instance : Max (Subrepresentation ρ) where
max ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊔ ρ₂.toSubmodule) by
      simp only [Submodule.forall_mem_sup, map_add]
      intro g x₁ hx₁ x₂ hx₂
      exact Submodule.mem_sup.mpr
        ⟨ρ g x₁, ρ₁.apply_mem_toSubmodule g hx₁, ρ g x₂, ρ₂.apply_mem_toSubmodule g hx₂, rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (Subrepresentation ρ)
  body: .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩


@[simp, norm_cast]

中文:
实例 :
  签名: 最小值 (子表示 ρ)
  定义体: .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩


@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.mem_inf, and_imp, apply_mem_toSubmodule, mem_inf, toSubmodule
-/
instance : Min (Subrepresentation ρ) where
min ρ₁ ρ₂ := .mk (ρ₁.toSubmodule ⊓ ρ₂.toSubmodule) by
      simp only [Submodule.mem_inf, and_imp]
      rintro g x hx₁ hx₂
      exact ⟨ρ₁.apply_mem_toSubmodule g hx₁, ρ₂.apply_mem_toSubmodule g hx₂⟩


@[simp, norm_cast]
/--
lemma `coe_sup` / 引理 `coe_sup`

English:
lemma coe_sup
  given: (ρ₁ ρ₂ : Subrepresentation ρ)
  statement: ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W)
  proof: Submodule.coe_sup ρ₁.toSubmodule ρ₂.toSubmodule

@[simp, norm_cast]

中文:
引理 coe_sup
  条件: (ρ₁ ρ₂ : 子表示 ρ)
  结论: ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : 集合 W) + (ρ₂ : 集合 W)
  证明: Submodule.coe_sup ρ₁.toSubmodule ρ₂.toSubmodule

@[simp, norm_cast]

Depends on / 依赖: Submodule, Submodule.coe_sup, coe_sup, toSubmodule
-/
lemma coe_sup (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊔ ρ₂) = (ρ₁ : Set W) + (ρ₂ : Set W) :=
  Submodule.coe_sup ρ₁.toSubmodule ρ₂.toSubmodule

@[simp, norm_cast]
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (ρ₁ ρ₂ : Subrepresentation ρ)
  statement: ↑(ρ₁ ⊓ ρ₂) = (ρ₁ inter ρ₂ : Set W)
  proof: rfl

@[simp]

中文:
引理 coe_inf
  条件: (ρ₁ ρ₂ : 子表示 ρ)
  结论: ↑(ρ₁ ⊓ ρ₂) = (ρ₁ inter ρ₂ : 集合 W)
  证明: rfl

@[simp]
-/
lemma coe_inf (ρ₁ ρ₂ : Subrepresentation ρ) : ↑(ρ₁ ⊓ ρ₂) = (ρ₁ inter ρ₂ : Set W) := rfl

@[simp]
/--
lemma `toSubmodule_sup` / 引理 `toSubmodule_sup`

English:
lemma toSubmodule_sup
  given: (ρ₁ ρ₂ : Subrepresentation ρ)
  proof: rfl

@[simp]

中文:
引理 toSubmodule_sup
  条件: (ρ₁ ρ₂ : 子表示 ρ)
  证明: rfl

@[simp]
-/
lemma toSubmodule_sup (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊔ ρ₂).toSubmodule = ρ₁.toSubmodule ⊔ ρ₂.toSubmodule := rfl

@[simp]
/--
lemma `toSubmodule_inf` / 引理 `toSubmodule_inf`

English:
lemma toSubmodule_inf
  given: (ρ₁ ρ₂ : Subrepresentation ρ)
  proof: rfl

中文:
引理 toSubmodule_inf
  条件: (ρ₁ ρ₂ : 子表示 ρ)
  证明: rfl
-/
lemma toSubmodule_inf (ρ₁ ρ₂ : Subrepresentation ρ) :
  (ρ₁ ⊓ ρ₂).toSubmodule = ρ₁.toSubmodule ⊓ ρ₂.toSubmodule := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Lattice (Subrepresentation ρ)
  body: toSubmodule_injective.lattice _ .rfl .rfl toSubmodule_sup toSubmodule_inf

中文:
实例 :
  签名: 格 (子表示 ρ)
  定义体: toSubmodule_injective.lattice _ .rfl .rfl toSubmodule_sup toSubmodule_inf

Depends on / 依赖: lattice, toSubmodule_inf, toSubmodule_injective, toSubmodule_injective.lattice, toSubmodule_sup
-/
instance : Lattice (Subrepresentation ρ) :=
  toSubmodule_injective.lattice _ .rfl .rfl toSubmodule_sup toSubmodule_inf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: BoundedOrder (Subrepresentation ρ)
  body: ⟨⊤, by simp⟩
  le_top _ := le_top (α := Submodule A W)
  bot := ⟨⊥, by simp⟩
  bot_le _ := bot_le (α := Submodule A W)

中文:
实例 :
  签名: 有界序 (子表示 ρ)
  定义体: ⟨⊤, by simp⟩
  le_top _ := le_top (α := Submodule A W)
  bot := ⟨⊥, by simp⟩
  bot_le _ := bot_le (α := Submodule A W)
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
/--
Definition of `asSubmodule` / `asSubmodule` 的定义

English:
definition asSubmodule
  signature: (σ : Subrepresentation ρ)
  body: σ.toSubmodule
  smul_mem' c v hv := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp [zero_smul]
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [Representation.single_smul]
      exact σ.toSubmodule.smul_mem' a (σ.apply_mem_toSubmodule g hv)

@[simp]

中文:
定义 asSubmodule
  签名: (σ : 子表示 ρ)
  定义体: σ.toSubmodule
  smul_mem' c v hv := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp [zero_smul]
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [Representation.single_smul]
      exact σ.toSubmodule.smul_mem' a (σ.apply_mem_toSubmodule g hv)

@[simp]

Depends on / 依赖: toSubmodule
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
/--
lemma `mem_asSubmodule_iff` / 引理 `mem_asSubmodule_iff`

English:
lemma mem_asSubmodule_iff
  given: {σ : Subrepresentation ρ} {v : W}
  statement: v in asSubmodule σ ↔ v in σ
  proof: by rfl

中文:
引理 mem_asSubmodule_iff
  条件: {σ : 子表示 ρ} {v : W}
  结论: v in asSubmodule σ ↔ v in σ
  证明: by rfl
-/
lemma mem_asSubmodule_iff {σ : Subrepresentation ρ} {v : W} : v in asSubmodule σ ↔ v in σ := by rfl

/--
Definition of `asSubmodule'` / `asSubmodule'` 的定义

English:
definition asSubmodule'
  signature: (σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M))
  body: σ.toSubmodule
  smul_mem' c m hm := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [← mul_one a]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [Algebra.smul_def]; rw [mul_smul]
exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) by
        simpa [Representation.ofModule, RestrictScalars.lsmul] using! σ.apply_mem_toSubmodule g hm

@[simp]

中文:
定义 asSubmodule'
  签名: (σ : 子表示 (Representation.ofModule (k := A) (G := G) M))
  定义体: σ.toSubmodule
  smul_mem' c m hm := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [← mul_one a]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [Algebra.smul_def]; rw [mul_smul]
exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) by
        simpa [Representation.ofModule, RestrictScalars.lsmul] using! σ.apply_mem_toSubmodule g hm

@[simp]
-/
def asSubmodule' (σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)) :
    Submodule A[G] M where
  __ := σ.toSubmodule
  smul_mem' c m hm := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => rw [zero_smul]; exact σ.toSubmodule.zero_mem'
    | add x y hx hy => rw [add_smul]; exact σ.toSubmodule.add_mem' hx hy
    | single g a =>
      rw [← mul_one a]; rw [← smul_eq_mul]; rw [← MonoidAlgebra.smul_single]; rw [Algebra.smul_def]; rw [mul_smul]
exact σ.toSubmodule.smul_mem' ((algebraMap A A) a) by
        simpa [Representation.ofModule, RestrictScalars.lsmul] using! σ.apply_mem_toSubmodule g hm

@[simp]
/--
lemma `mem_asSubmodule'_iff` / 引理 `mem_asSubmodule'_iff`

English:
lemma mem_asSubmodule'_iff
  statement: {σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)}
  proof: by rfl

中文:
引理 mem_asSubmodule'_iff
  结论: {σ : 子表示 (Representation.ofModule (k := A) (G := G) M)}
  证明: by rfl
-/
lemma mem_asSubmodule'_iff {σ : Subrepresentation (Representation.ofModule (k := A) (G := G) M)}
    {m : M} : m in asSubmodule' σ ↔ m in σ := by rfl

/--
Definition of `ofSubmodule` / `ofSubmodule` 的定义

English:
definition ofSubmodule
  signature: (N : Submodule A[G] M)
  body: { N with
    smul_mem' a m hm := N.smul_mem' (algebraMap A A[G] a) hm }
  apply_mem_toSubmodule g v hv := by
    simpa [Representation.ofModule, RestrictScalars.lsmul] using!
      Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

@[simp]

中文:
定义 ofSubmodule
  签名: (N : 子模 A[G] M)
  定义体: { N with
    smul_mem' a m hm := N.smul_mem' (algebraMap A A[G] a) hm }
  apply_mem_toSubmodule g v hv := by
    simpa [Representation.ofModule, RestrictScalars.lsmul] using!
      Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

@[simp]
-/
def ofSubmodule (N : Submodule A[G] M) :
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toSubmodule := { N with
    smul_mem' a m hm := N.smul_mem' (algebraMap A A[G] a) hm }
  apply_mem_toSubmodule g v hv := by
    simpa [Representation.ofModule, RestrictScalars.lsmul] using!
      Submodule.smul_of_tower_mem N (MonoidAlgebra.single g 1) hv

@[simp]
/--
lemma `mem_ofSubmodule_iff` / 引理 `mem_ofSubmodule_iff`

English:
lemma mem_ofSubmodule_iff
  given: {N : Submodule A[G] M} {m : M}
  statement: m in ofSubmodule N ↔ m in N
  proof: by rfl

中文:
引理 mem_ofSubmodule_iff
  条件: {N : 子模 A[G] M} {m : M}
  结论: m in ofSubmodule N ↔ m in N
  证明: by rfl
-/
lemma mem_ofSubmodule_iff {N : Submodule A[G] M} {m : M} : m in ofSubmodule N ↔ m in N := by rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofSubmodule'` / `ofSubmodule'` 的定义

English:
definition ofSubmodule'
  signature: (N : Submodule A[G] ρ.asModule)
  body: { N with
    smul_mem' a w hw := by simpa using! (N.smul_mem (algebraMap A A[G] a) hw) }
  apply_mem_toSubmodule g w hw := by
    let _ : Module A[G] W := ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w in N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul]; rw [one_smul] at h
    exact h

@[simp]

中文:
定义 ofSubmodule'
  签名: (N : 子模 A[G] ρ.asModule)
  定义体: { N with
    smul_mem' a w hw := by simpa using! (N.smul_mem (algebraMap A A[G] a) hw) }
  apply_mem_toSubmodule g w hw := by
    let _ : Module A[G] W := ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w in N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul]; rw [one_smul] at h
    exact h

@[simp]
-/
def ofSubmodule' (N : Submodule A[G] ρ.asModule) : Subrepresentation ρ where
  toSubmodule := { N with
    smul_mem' a w hw := by simpa using! (N.smul_mem (algebraMap A A[G] a) hw) }
  apply_mem_toSubmodule g w hw := by
    let _ : Module A[G] W := ρ.instModuleMonoidAlgebraAsModule
    have h : (MonoidAlgebra.single g (1 : A)) • w in N :=
      Submodule.smul_of_tower_mem N _ hw
    rw [Representation.single_smul]; rw [one_smul] at h
    exact h

@[simp]
/--
lemma `mem_ofSubmodule'_iff` / 引理 `mem_ofSubmodule'_iff`

English:
lemma mem_ofSubmodule'_iff
  given: {N : Submodule A[G] ρ.asModule} {w : W}
  statement: w in ofSubmodule' N ↔ w in N
  proof: .rfl

中文:
引理 mem_ofSubmodule'_iff
  条件: {N : 子模 A[G] ρ.asModule} {w : W}
  结论: w in ofSubmodule' N ↔ w in N
  证明: .rfl
-/
lemma mem_ofSubmodule'_iff {N : Submodule A[G] ρ.asModule} {w : W} : w in ofSubmodule' N ↔ w in N :=
  .rfl

/-- An order-preserving equivalence between subrepresentations of `ρ` and submodules of
`ρ.asModule`. -/
@[simps]
/--
Definition of `subrepresentationSubmoduleOrderIso` / `subrepresentationSubmoduleOrderIso` 的定义

English:
definition subrepresentationSubmoduleOrderIso
  signature: : Subrepresentation ρ ≃o Submodule A[G] ρ.asModule where
  body: asSubmodule
  invFun := ofSubmodule'
  left_inv σ := rfl
  right_inv N := rfl
  map_rel_iff' := by rfl

中文:
定义 subrepresentationSubmoduleOrderIso
  签名: : 子表示 ρ ≃o 子模 A[G] ρ.asModule where
  定义体: asSubmodule
  invFun := ofSubmodule'
  left_inv σ := rfl
  right_inv N := rfl
  map_rel_iff' := by rfl

Depends on / 依赖: asSubmodule
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
/--
Definition of `submoduleSubrepresentationOrderIso` / `submoduleSubrepresentationOrderIso` 的定义

English:
definition submoduleSubrepresentationOrderIso
  signature: : Submodule A[G] M ≃o
  body: ofSubmodule
  invFun := asSubmodule'
  left_inv N := rfl
  right_inv σ := rfl
  map_rel_iff' := by rfl

中文:
定义 submoduleSubrepresentationOrderIso
  签名: : 子模 A[G] M ≃o
  定义体: ofSubmodule
  invFun := asSubmodule'
  left_inv N := rfl
  right_inv σ := rfl
  map_rel_iff' := by rfl
-/
def submoduleSubrepresentationOrderIso : Submodule A[G] M ≃o
    Subrepresentation (Representation.ofModule (k := A) (G := G) M) where
  toFun := ofSubmodule
  invFun := asSubmodule'
  left_inv N := rfl
  right_inv σ := rfl
  map_rel_iff' := by rfl

end Subrepresentation
