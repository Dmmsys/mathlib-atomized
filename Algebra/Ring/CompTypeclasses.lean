/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis, Heather Macbeth
-/
module

public import Mathlib.Algebra.Ring.Equiv

/-!
# Propositional typeclasses on several ring homs

This file contains three typeclasses used in the definition of (semi)linear maps:
* `RingHomId σ`, which expresses the fact that `σ₂₃ = id`
* `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, which expresses the fact that `σ₂₃.comp σ₁₂ = σ₁₃`
* `RingHomInvPair σ₁₂ σ₂₁`, which states that `σ₁₂` and `σ₂₁` are inverses of each other
* `RingHomSurjective σ`, which states that `σ` is surjective

These typeclasses ensure that objects such as `σ₂₃.comp σ₁₂` never end up in the type of a
semilinear map; instead, the typeclass system directly finds the appropriate `RingHom` to use.
A typical use-case is conjugate-linear maps, i.e. when `σ = Complex.conj`; this system ensures that
composing two conjugate-linear maps is a linear map, and not a `conj.comp conj`-linear map.

Instances of these typeclasses mostly involving `RingHom.id` are also provided:
* `RingHomInvPair (RingHom.id R) (RingHom.id R)`
* `[RingHomInvPair σ₁₂ σ₂₁] : RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁)`
* `RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂`
* `RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂`
* `RingHomSurjective (RingHom.id R)`
* `[RingHomInvPair σ₁ σ₂] : RingHomSurjective σ₁`

## Implementation notes

* For the typeclass `RingHomInvPair σ₁₂ σ₂₁`, `σ₂₁` is marked as an `outParam`,
  as it must typically be found via the typeclass inference system.

* Likewise, for `RingHomCompTriple σ₁₂ σ₂₃ σ₁₃`, `σ₁₃` is marked as an `outParam`,
  for the same reason.

## Tags

`RingHomCompTriple`, `RingHomInvPair`, `RingHomSurjective`
-/

@[expose] public section


variable {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable [Semiring R₁] [Semiring R₂] [Semiring R₃]

-- This at first seems not very useful. However we need this when considering
-- modules over some diagram in the category of rings,
-- e.g. when defining presheaves over a presheaf of rings.
-- See `Mathlib/Algebra/Category/ModuleCat/Presheaf.lean`.
/--
Definition of `RingHomId` / `RingHomId` 的定义

English:
class RingHomId
  parameters: {R : Type*} [Semiring R] (σ : R ->+* R)
  axioms and operations (1):
    - eq_id : σ = RingHom.id R

中文:
类 RingHomId
  参数: {R : 类型} [半环 R] (σ : R ->+* R)
  公理与运算 (1 个):
    - eq_id : σ = 环态射.id R
-/
class RingHomId {R : Type*} [Semiring R] (σ : R ->+* R) : Prop where
  eq_id : σ = RingHom.id R

instance {R : Type*} [Semiring R] : RingHomId (RingHom.id R) where
  eq_id := rfl

/--
Definition of `RingHomCompTriple` / `RingHomCompTriple` 的定义

English:
class RingHomCompTriple
  parameters: (σ₁₂ : R₁ ->+* R₂) (σ₂₃ : R₂ ->+* R₃) (σ₁₃ : outParam (R₁ ->+* R₃))
  axioms and operations (1):
    - comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

中文:
类 RingHomCompTriple
  参数: (σ₁₂ : R₁ ->+* R₂) (σ₂₃ : R₂ ->+* R₃) (σ₁₃ : outParam (R₁ ->+* R₃))
  公理与运算 (1 个):
    - comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

Depends on / 依赖: IsAffine
-/
class RingHomCompTriple (σ₁₂ : R₁ ->+* R₂) (σ₂₃ : R₂ ->+* R₃) (σ₁₃ : outParam (R₁ ->+* R₃)) :
  Prop where
  /-- The morphisms form a commutative triangle -/
  comp_eq : σ₂₃.comp σ₁₂ = σ₁₃

attribute [simp] RingHomCompTriple.comp_eq

variable {σ₁₂ : R₁ ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R₁ ->+* R₃}

namespace RingHomCompTriple

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  given: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁}
  statement: σ₂₃ (σ₁₂ x) = σ₁₃ x
  proof: RingHom.congr_fun comp_eq x

中文:
定理 comp_apply
  条件: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁}
  结论: σ₂₃ (σ₁₂ x) = σ₁₃ x
  证明: RingHom.congr_fun comp_eq x

Depends on / 依赖: IsOpenImmersion, RingHom, RingHom.congr_fun, comp_eq, congr_fun, infer_instance
-/
theorem comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x :=
  RingHom.congr_fun comp_eq x

end RingHomCompTriple

/--
Definition of `RingHomInvPair` / `RingHomInvPair` 的定义

English:
class RingHomInvPair
  parameters: (σ : R₁ ->+* R₂) (σ' : outParam (R₂ ->+* R₁))
  axioms and operations (2):
    - comp_eq : σ'.comp σ = RingHom.id R₁
    - comp_eq₂ : σ.comp σ' = RingHom.id R₂

中文:
类 RingHomInvPair
  参数: (σ : R₁ ->+* R₂) (σ' : outParam (R₂ ->+* R₁))
  公理与运算 (2 个):
    - comp_eq : σ'.comp σ = 环态射.id R₁
    - comp_eq₂ : σ.comp σ' = 环态射.id R₂
-/
class RingHomInvPair (σ : R₁ ->+* R₂) (σ' : outParam (R₂ ->+* R₁)) : Prop where
  /-- `σ'` is a left inverse of `σ` -/
  comp_eq : σ'.comp σ = RingHom.id R₁
  /-- `σ'` is a left inverse of `σ'` -/
  comp_eq₂ : σ.comp σ' = RingHom.id R₂

variable {σ : R₁ ->+* R₂} {σ' : R₂ ->+* R₁}

namespace RingHomInvPair

variable [RingHomInvPair σ σ']

/--
theorem `comp_apply_eq` / 定理 `comp_apply_eq`

English:
theorem comp_apply_eq
  given: {x : R₁}
  statement: σ' (σ x) = x
  proof: by
  rw [← RingHom.comp_apply]; rw [comp_eq]
  simp

中文:
定理 comp_apply_eq
  条件: {x : R₁}
  结论: σ' (σ x) = x
  证明: by
  rw [← RingHom.comp_apply]; rw [comp_eq]
  simp

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply, comp_eq
-/
theorem comp_apply_eq {x : R₁} : σ' (σ x) = x := by
  rw [← RingHom.comp_apply]; rw [comp_eq]
  simp

/--
theorem `comp_apply_eq₂` / 定理 `comp_apply_eq₂`

English:
theorem comp_apply_eq₂
  given: {x : R₂}
  statement: σ (σ' x) = x
  proof: by
  rw [← RingHom.comp_apply]; rw [comp_eq₂]
  simp

中文:
定理 comp_apply_eq₂
  条件: {x : R₂}
  结论: σ (σ' x) = x
  证明: by
  rw [← RingHom.comp_apply]; rw [comp_eq₂]
  simp

Depends on / 依赖: RingHom, RingHom.comp_apply, comp_apply
-/
theorem comp_apply_eq₂ {x : R₂} : σ (σ' x) = x := by
  rw [← RingHom.comp_apply]; rw [comp_eq₂]
  simp

/--
Instance `ids` / 实例 `ids`

English:
instance ids
  signature: : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁)
  body: ⟨rfl, rfl⟩

中文:
实例 ids
  签名: : RingHomInvPair (环态射.id R₁) (环态射.id R₁)
  定义体: ⟨rfl, rfl⟩
-/
instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=
  ⟨rfl, rfl⟩

/--
Instance `triples` / 实例 `triples`

English:
instance triples
  signature: {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  body: ⟨by simp only [comp_eq]⟩

中文:
实例 triples
  签名: {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  定义体: ⟨by simp only [comp_eq]⟩

Depends on / 依赖: comp_eq
-/
instance triples {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₁₂ σ₂₁ (RingHom.id R₁) :=
  ⟨by simp only [comp_eq]⟩

/--
Instance `triples₂` / 实例 `triples₂`

English:
instance triples₂
  signature: {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  body: ⟨by simp only [comp_eq₂]⟩

中文:
实例 triples₂
  签名: {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁]
  定义体: ⟨by simp only [comp_eq₂]⟩
-/
instance triples₂ {σ₂₁ : R₂ ->+* R₁} [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomCompTriple σ₂₁ σ₁₂ (RingHom.id R₂) :=
  ⟨by simp only [comp_eq₂]⟩

variable (σ σ') in
/-- The ring equivalence defined by a pair of ring homomorphisms satisfying `RingHomInvPair`. -/
@[simps!]
/--
Definition of `toRingEquiv` / `toRingEquiv` 的定义

English:
definition toRingEquiv
  signature: : R₁ ≃+* R₂
  body: .ofRingHom σ σ' comp_eq₂ comp_eq

中文:
定义 toRingEquiv
  签名: : R₁ ≃+* R₂
  定义体: .ofRingHom σ σ' comp_eq₂ comp_eq

Depends on / 依赖: comp_eq, ofRingHom
-/
def toRingEquiv : R₁ ≃+* R₂ := .ofRingHom σ σ' comp_eq₂ comp_eq

/--
lemma `of_ringEquiv` / 引理 `of_ringEquiv`

English:
lemma of_ringEquiv
  given: (e : R₁ ≃+* R₂)
  statement: RingHomInvPair (↑e : R₁ ->+* R₂) ↑e.symm
  proof: ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

中文:
引理 of_ringEquiv
  条件: (e : R₁ ≃+* R₂)
  结论: RingHomInvPair (↑e : R₁ ->+* R₂) ↑e.symm
  证明: ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

Depends on / 依赖: e.symm.symm_toRingHom_comp_toRingHom, e.symm_toRingHom_comp_toRingHom, symm_toRingHom_comp_toRingHom
-/
lemma of_ringEquiv (e : R₁ ≃+* R₂) : RingHomInvPair (↑e : R₁ ->+* R₂) ↑e.symm :=
  ⟨e.symm_toRingHom_comp_toRingHom, e.symm.symm_toRingHom_comp_toRingHom⟩

/--
theorem `of_ringEquiv_symm` / 定理 `of_ringEquiv_symm`

English:
theorem of_ringEquiv_symm
  given: (e : R₁ ≃+* R₂)
  statement: RingHomInvPair (↑e.symm : R₂ ->+* R₁) ↑e
  proof: of_ringEquiv e.symm

中文:
定理 of_ringEquiv_symm
  条件: (e : R₁ ≃+* R₂)
  结论: RingHomInvPair (↑e.symm : R₂ ->+* R₁) ↑e
  证明: of_ringEquiv e.symm

Depends on / 依赖: e.symm, of_ringEquiv
-/
theorem of_ringEquiv_symm (e : R₁ ≃+* R₂) : RingHomInvPair (↑e.symm : R₂ ->+* R₁) ↑e :=
  of_ringEquiv e.symm

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHomInvPair σ₁₂ σ₂₁]
  proof: ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

中文:
定理 symm
  条件: (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHomInvPair σ₁₂ σ₂₁]
  证明: ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

Depends on / 依赖: RingHomInvPair, RingHomInvPair.comp_eq, comp_eq
-/
theorem symm (σ₁₂ : R₁ ->+* R₂) (σ₂₁ : R₂ ->+* R₁) [RingHomInvPair σ₁₂ σ₂₁] :
    RingHomInvPair σ₂₁ σ₁₂ :=
  ⟨RingHomInvPair.comp_eq₂, RingHomInvPair.comp_eq⟩

end RingHomInvPair

namespace RingHomCompTriple

/--
Instance `ids` / 实例 `ids`

English:
instance ids
  signature: : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂
  body: ⟨by
    simp⟩

中文:
实例 ids
  签名: : RingHomCompTriple (环态射.id R₁) σ₁₂ σ₁₂
  定义体: ⟨by
    simp⟩
-/
instance ids : RingHomCompTriple (RingHom.id R₁) σ₁₂ σ₁₂ :=
  ⟨by
    simp⟩

/--
Instance `right_ids` / 实例 `right_ids`

English:
instance right_ids
  signature: : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂
  body: ⟨by
    simp⟩

中文:
实例 right_ids
  签名: : RingHomCompTriple σ₁₂ (环态射.id R₂) σ₁₂
  定义体: ⟨by
    simp⟩
-/
instance right_ids : RingHomCompTriple σ₁₂ (RingHom.id R₂) σ₁₂ :=
  ⟨by
    simp⟩

end RingHomCompTriple

/--
Definition of `RingHomSurjective` / `RingHomSurjective` 的定义

English:
class RingHomSurjective
  parameters: (σ : R₁ ->+* R₂)
  axioms and operations (1):
    - is_surjective : Function.Surjective σ

中文:
类 RingHomSurjective
  参数: (σ : R₁ ->+* R₂)
  公理与运算 (1 个):
    - is_surjective : 函数.满射 σ
-/
class RingHomSurjective (σ : R₁ ->+* R₂) : Prop where
  /-- The ring homomorphism is surjective -/
  is_surjective : Function.Surjective σ

/--
theorem `RingHom.surjective` / 定理 `RingHom.surjective`

English:
theorem RingHom.surjective
  given: (σ : R₁ ->+* R₂) [t : RingHomSurjective σ]
  statement: Function.Surjective σ
  proof: t.is_surjective

中文:
定理 环态射.surjective
  条件: (σ : R₁ ->+* R₂) [t : RingHomSurjective σ]
  结论: 函数.满射 σ
  证明: t.is_surjective

Depends on / 依赖: is_surjective, t.is_surjective
-/
theorem RingHom.surjective (σ : R₁ ->+* R₂) [t : RingHomSurjective σ] : Function.Surjective σ :=
  t.is_surjective

namespace RingHomSurjective

instance (priority := 100) invPair {σ₁ : R₁ ->+* R₂} {σ₂ : R₂ ->+* R₁} [RingHomInvPair σ₁ σ₂] :
    RingHomSurjective σ₁ :=
  ⟨fun x => ⟨σ₂ x, RingHomInvPair.comp_apply_eq₂⟩⟩

/--
Instance `ids` / 实例 `ids`

English:
instance ids
  signature: : RingHomSurjective (RingHom.id R₁)
  body: ⟨is_surjective⟩

中文:
实例 ids
  签名: : RingHomSurjective (环态射.id R₁)
  定义体: ⟨is_surjective⟩

Depends on / 依赖: is_surjective
-/
instance ids : RingHomSurjective (RingHom.id R₁) :=
  ⟨is_surjective⟩

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  given: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃]
  proof: { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }

中文:
定理 comp
  条件: [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃]
  证明: { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }

Depends on / 依赖: RingHom, RingHom.coe_comp, RingHomCompTriple, RingHomCompTriple.comp_eq, coe_comp, comp_eq, is_surjective, surjective, surjective.comp
-/
theorem comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomSurjective σ₁₂] [RingHomSurjective σ₂₃] :
    RingHomSurjective σ₁₃ :=
  { is_surjective := by
      have := σ₂₃.surjective.comp σ₁₂.surjective
      rwa [← RingHom.coe_comp, RingHomCompTriple.comp_eq] at this }

instance (σ : R₁ ≃+* R₂) : RingHomSurjective (σ : R₁ ->+* R₂) := ⟨σ.surjective⟩

end RingHomSurjective
