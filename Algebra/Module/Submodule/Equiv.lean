/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Submodule.Range

/-! ### Linear equivalences involving submodules -/

@[expose] public section

open Function

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N : Type*}

namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ ->+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₁] M) (e : M ≃ₛₗ[σ₁₂] M₂) (h : M₂ ->ₛₗ[σ₂₃] M₃)
variable (p q : Submodule R M)

/--
Definition of `ofEq` / `ofEq` 的定义

English:
definition ofEq
  signature: (h : p = q)
  body: { Equiv.setCongr (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

中文:
定义 ofEq
  签名: (h : p = q)
  定义体: { Equiv.setCongr (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

Depends on / 依赖: Equiv.setCongr, congr_arg, map_add, map_smul, setCongr
-/
def ofEq (h : p = q) : p ≃ₗ[R] q :=
  { Equiv.setCongr (congr_arg _ h) with
    map_smul' := fun _ _ => rfl
    map_add' := fun _ _ => rfl }

variable {p q}

@[simp]
/--
theorem `coe_ofEq_apply` / 定理 `coe_ofEq_apply`

English:
theorem coe_ofEq_apply
  given: (h : p = q) (x : p)
  statement: (ofEq p q h x : M) = x
  proof: rfl

@[simp]

中文:
定理 coe_ofEq_apply
  条件: (h : p = q) (x : p)
  结论: (ofEq p q h x : M) = x
  证明: rfl

@[simp]
-/
theorem coe_ofEq_apply (h : p = q) (x : p) : (ofEq p q h x : M) = x :=
  rfl

@[simp]
/--
theorem `ofEq_symm` / 定理 `ofEq_symm`

English:
theorem ofEq_symm
  given: (h : p = q)
  statement: (ofEq p q h).symm = ofEq q p h.symm
  proof: rfl

@[simp]

中文:
定理 ofEq_symm
  条件: (h : p = q)
  结论: (ofEq p q h).symm = ofEq q p h.symm
  证明: rfl

@[simp]
-/
theorem ofEq_symm (h : p = q) : (ofEq p q h).symm = ofEq q p h.symm :=
  rfl

@[simp]
/--
theorem `ofEq_rfl` / 定理 `ofEq_rfl`

English:
theorem ofEq_rfl
  statement: ofEq p p rfl = LinearEquiv.refl R p
  proof: by ext; rfl

中文:
定理 ofEq_rfl
  结论: ofEq p p rfl = 线性等价.refl R p
  证明: by ext; rfl
-/
theorem ofEq_rfl : ofEq p p rfl = LinearEquiv.refl R p := by ext; rfl

/--
Definition of `ofSubmodules` / `ofSubmodules` 的定义

English:
definition ofSubmodules
  signature: (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q)
  body: (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)

@[simp]

中文:
定义 ofSubmodules
  签名: (p : 子模 R M) (q : 子模 R₂ M₂) (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q)
  定义体: (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, e.submoduleMap, submoduleMap
-/
def ofSubmodules (p : Submodule R M) (q : Submodule R₂ M₂) (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) :
    p ≃ₛₗ[σ₁₂] q :=
  (e.submoduleMap p).trans (LinearEquiv.ofEq _ _ h)

@[simp]
/--
theorem `ofSubmodules_apply` / 定理 `ofSubmodules_apply`

English:
theorem ofSubmodules_apply
  statement: {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

@[simp]

中文:
定理 ofSubmodules_apply
  结论: {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: rfl

@[simp]
-/
theorem ofSubmodules_apply {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q) (x : p) :
    ↑(e.ofSubmodules p q h x) = e x :=
  rfl

@[simp]
/--
theorem `ofSubmodules_symm_apply` / 定理 `ofSubmodules_symm_apply`

English:
theorem ofSubmodules_symm_apply
  statement: {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: rfl

中文:
定理 ofSubmodules_symm_apply
  结论: {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: rfl
-/
theorem ofSubmodules_symm_apply {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : p.map (e : M ->ₛₗ[σ₁₂] M₂) = q)
    (x : q) : ↑((e.ofSubmodules p q h).symm x) = e.symm x :=
  rfl

/--
Definition of `ofSubmodule'` / `ofSubmodule'` 的定义

English:
definition ofSubmodule'
  signature: [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
  body: (f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.symm)).symm

中文:
定义 ofSubmodule'
  签名: [模 R M] [模 R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : 子模 R₂ M₂)
  定义体: (f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.symm)).symm

Depends on / 依赖: U.map_equiv_eq_comap_symm, f.symm, f.symm.ofSubmodules, map_equiv_eq_comap_symm, ofSubmodules
-/
def ofSubmodule' [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂) :
    U.comap (f : M ->ₛₗ[σ₁₂] M₂) ≃ₛₗ[σ₁₂] U :=
  (f.symm.ofSubmodules _ _ (U.map_equiv_eq_comap_symm f.symm)).symm

/--
theorem `ofSubmodule'_toLinearMap` / 定理 `ofSubmodule'_toLinearMap`

English:
theorem ofSubmodule'_toLinearMap
  statement: [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
  proof: by
  ext
  rfl

@[simp]

中文:
定理 ofSubmodule'_toLinearMap
  结论: [模 R M] [模 R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
  证明: by
  ext
  rfl

@[simp]
-/
theorem ofSubmodule'_toLinearMap [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) :
    (f.ofSubmodule' U).toLinearMap = (f.toLinearMap.domRestrict _).codRestrict _ Subtype.prop := by
  ext
  rfl

@[simp]
/--
theorem `ofSubmodule'_apply` / 定理 `ofSubmodule'_apply`

English:
theorem ofSubmodule'_apply
  statement: [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
  proof: rfl

@[simp]

中文:
定理 ofSubmodule'_apply
  结论: [模 R M] [模 R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : 子模 R₂ M₂)
  证明: rfl

@[simp]
-/
theorem ofSubmodule'_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂) (U : Submodule R₂ M₂)
    (x : U.comap (f : M ->ₛₗ[σ₁₂] M₂)) : (f.ofSubmodule' U x : M₂) = f (x : M) :=
  rfl

@[simp]
/--
theorem `ofSubmodule'_symm_apply` / 定理 `ofSubmodule'_symm_apply`

English:
theorem ofSubmodule'_symm_apply
  statement: [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
  proof: rfl

中文:
定理 ofSubmodule'_symm_apply
  结论: [模 R M] [模 R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
  证明: rfl
-/
theorem ofSubmodule'_symm_apply [Module R M] [Module R₂ M₂] (f : M ≃ₛₗ[σ₁₂] M₂)
    (U : Submodule R₂ M₂) (x : U) : ((f.ofSubmodule' U).symm x : M) = f.symm (x : M₂) :=
  rfl

variable (p)

/--
Definition of `ofTop` / `ofTop` 的定义

English:
definition ofTop
  signature: (h : p = ⊤)
  body: { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩ }

@[simp]

中文:
定义 ofTop
  签名: (h : p = ⊤)
  定义体: { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩ }

@[simp]

Depends on / 依赖: h.symm, invFun, p.subtype, subtype
-/
def ofTop (h : p = ⊤) : p ≃ₗ[R] M :=
  { p.subtype with
    invFun := fun x => ⟨x, h.symm ▸ trivial⟩ }

@[simp]
/--
theorem `ofTop_apply` / 定理 `ofTop_apply`

English:
theorem ofTop_apply
  given: {h} (x : p)
  statement: ofTop p h x = x
  proof: rfl

@[simp]

中文:
定理 ofTop_apply
  条件: {h} (x : p)
  结论: ofTop p h x = x
  证明: rfl

@[simp]
-/
theorem ofTop_apply {h} (x : p) : ofTop p h x = x :=
  rfl

@[simp]
/--
theorem `coe_ofTop_symm_apply` / 定理 `coe_ofTop_symm_apply`

English:
theorem coe_ofTop_symm_apply
  given: {h} (x : M)
  statement: ((ofTop p h).symm x : M) = x
  proof: rfl

中文:
定理 coe_ofTop_symm_apply
  条件: {h} (x : M)
  结论: ((ofTop p h).symm x : M) = x
  证明: rfl
-/
theorem coe_ofTop_symm_apply {h} (x : M) : ((ofTop p h).symm x : M) = x :=
  rfl

/--
theorem `ofTop_symm_apply` / 定理 `ofTop_symm_apply`

English:
theorem ofTop_symm_apply
  given: {h} (x : M)
  statement: (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩
  proof: rfl

@[simp]

中文:
定理 ofTop_symm_apply
  条件: {h} (x : M)
  结论: (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩
  证明: rfl

@[simp]
-/
theorem ofTop_symm_apply {h} (x : M) : (ofTop p h).symm x = ⟨x, h.symm ▸ trivial⟩ :=
  rfl

@[simp]
/--
theorem `toLinearMap_ofTop` / 定理 `toLinearMap_ofTop`

English:
theorem toLinearMap_ofTop
  given: {h}
  statement: (ofTop p h).toLinearMap = p.subtype
  proof: rfl

@[simp]

中文:
定理 toLinearMap_ofTop
  条件: {h}
  结论: (ofTop p h).toLinearMap = p.subtype
  证明: rfl

@[simp]
-/
theorem toLinearMap_ofTop {h} : (ofTop p h).toLinearMap = p.subtype :=
  rfl

@[simp]
/--
theorem `range` / 定理 `range`

English:
theorem range
  statement: LinearMap.range (e : M ->ₛₗ[σ₁₂] M₂) = ⊤
  proof: LinearMap.range_eq_top.2 e.toEquiv.surjective

中文:
定理 range
  结论: 线性映射.range (e : M ->ₛₗ[σ₁₂] M₂) = ⊤
  证明: LinearMap.range_eq_top.2 e.toEquiv.surjective
-/
protected theorem range : LinearMap.range (e : M ->ₛₗ[σ₁₂] M₂) = ⊤ :=
  LinearMap.range_eq_top.2 e.toEquiv.surjective

/--
theorem `eq_bot_of_equiv` / 定理 `eq_bot_of_equiv`

English:
theorem eq_bot_of_equiv
  given: [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂))
  statement: p = ⊥
  proof: by
  refine bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 ?_)
  rw [← p.mk_eq_zero hb]; rw [← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule

@[simp]

中文:
定理 eq_bot_of_equiv
  条件: [模 R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : 子模 R₂ M₂))
  结论: p = ⊥
  证明: by
  refine bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 ?_)
  rw [← p.mk_eq_zero hb]; rw [← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule

@[simp]

Depends on / 依赖: SetLike, SetLike.le_def, Submodule, Submodule.eq_zero_of_bot_submodule, Submodule.mem_bot, bot_unique, e.map_eq_zero_iff, eq_zero_of_bot_submodule, le_def, map_eq_zero_iff, mem_bot, mk_eq_zero, p.mk_eq_zero
-/
theorem eq_bot_of_equiv [Module R₂ M₂] (e : p ≃ₛₗ[σ₁₂] (⊥ : Submodule R₂ M₂)) : p = ⊥ := by
  refine bot_unique (SetLike.le_def.2 fun b hb => (Submodule.mem_bot R).2 ?_)
  rw [← p.mk_eq_zero hb]; rw [← e.map_eq_zero_iff]
  apply Submodule.eq_zero_of_bot_submodule

@[simp]
/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  given: [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃]
  proof: LinearMap.range_comp_of_range_eq_top _ e.range

中文:
定理 range_comp
  条件: [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃]
  证明: LinearMap.range_comp_of_range_eq_top _ e.range

Depends on / 依赖: LinearMap, LinearMap.range_comp_of_range_eq_top, e.range, range_comp_of_range_eq_top
-/
theorem range_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] :
    LinearMap.range (h.comp (e : M ->ₛₗ[σ₁₂] M₂) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.range h :=
  LinearMap.range_comp_of_range_eq_top _ e.range

variable {f g}

/--
Definition of `ofLeftInverse` / `ofLeftInverse` 的定义

English:
definition ofLeftInverse
  signature: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ -> M}
  body: { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

中文:
定义 ofLeftInverse
  签名: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ -> M}
  定义体: { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mem_range.mp, LinearMap.range, LinearMap.rangeRestrict, Subtype, Subtype.ext, invFun, left_inv, mem_range, rangeRestrict, right_inv, subtype, x.prop
-/
def ofLeftInverse [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {g : M₂ -> M}
    (h : Function.LeftInverse g f) : M ≃ₛₗ[σ₁₂] (LinearMap.range f) :=
  { LinearMap.rangeRestrict f with
    toFun := LinearMap.rangeRestrict f
    invFun := g ∘ (LinearMap.range f).subtype
    left_inv := h
    right_inv := fun x =>
Subtype.ext
        let ⟨x', hx'⟩ := LinearMap.mem_range.mp x.prop
        show f (g x) = x by rw [← hx', h x'] }

@[simp]
/--
theorem `ofLeftInverse_apply` / 定理 `ofLeftInverse_apply`

English:
theorem ofLeftInverse_apply
  statement: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  proof: rfl

@[simp]

中文:
定理 ofLeftInverse_apply
  结论: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  证明: rfl

@[simp]
-/
theorem ofLeftInverse_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : M) : ↑(ofLeftInverse h x) = f x :=
  rfl

@[simp]
/--
theorem `ofLeftInverse_symm_apply` / 定理 `ofLeftInverse_symm_apply`

English:
theorem ofLeftInverse_symm_apply
  statement: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  proof: rfl

中文:
定理 ofLeftInverse_symm_apply
  结论: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
  证明: rfl
-/
theorem ofLeftInverse_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (h : Function.LeftInverse g f) (x : LinearMap.range f) : (ofLeftInverse h).symm x = g x :=
  rfl

variable (f)

/--
Definition of `ofInjective` / `ofInjective` 的定义

English:
definition ofInjective
  signature: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f)
  body: ofLeftInverse Classical.choose_spec h.hasLeftInverse

@[simp]

中文:
定义 ofInjective
  签名: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : 单射 f)
  定义体: ofLeftInverse Classical.choose_spec h.hasLeftInverse

@[simp]

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, h.hasLeftInverse, hasLeftInverse, ofLeftInverse
-/
noncomputable def ofInjective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (h : Injective f) :
    M ≃ₛₗ[σ₁₂] LinearMap.range f :=
ofLeftInverse Classical.choose_spec h.hasLeftInverse

@[simp]
/--
theorem `ofInjective_apply` / 定理 `ofInjective_apply`

English:
theorem ofInjective_apply
  statement: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
  proof: rfl

@[simp]

中文:
定理 ofInjective_apply
  结论: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : 单射 f}
  证明: rfl

@[simp]
-/
theorem ofInjective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : M) : ↑(ofInjective f h x) = f x :=
  rfl

@[simp]
/--
lemma `ofInjective_symm_apply` / 引理 `ofInjective_symm_apply`

English:
lemma ofInjective_symm_apply
  statement: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
  proof: by
  obtain ⟨-, ⟨y, rfl⟩⟩ := x
  have : ⟨f y, LinearMap.mem_range_self f y⟩ = LinearEquiv.ofInjective f h y := rfl
  simp [this]

中文:
引理 ofInjective_symm_apply
  结论: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : 单射 f}
  证明: by
  obtain ⟨-, ⟨y, rfl⟩⟩ := x
  have : ⟨f y, LinearMap.mem_range_self f y⟩ = LinearEquiv.ofInjective f h y := rfl
  simp [this]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.mem_range_self, mem_range_self, ofInjective
-/
lemma ofInjective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h : Injective f}
    (x : LinearMap.range f) :
    f ((ofInjective f h).symm x) = x := by
  obtain ⟨-, ⟨y, rfl⟩⟩ := x
  have : ⟨f y, LinearMap.mem_range_self f y⟩ = LinearEquiv.ofInjective f h y := rfl
  simp [this]

/--
Definition of `ofBijective` / `ofBijective` 的定义

English:
definition ofBijective
  signature: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f)
  body: (ofInjective f hf.injective).trans ofTop _
    LinearMap.range_eq_top.2 hf.surjective

@[simp]

中文:
定义 ofBijective
  签名: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : 双射 f)
  定义体: (ofInjective f hf.injective).trans ofTop _
    LinearMap.range_eq_top.2 hf.surjective

@[simp]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, hf.injective, hf.surjective, injective, ofInjective, range_eq_top, surjective
-/
noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :
    M ≃ₛₗ[σ₁₂] M₂ :=
(ofInjective f hf.injective).trans ofTop _
    LinearMap.range_eq_top.2 hf.surjective

@[simp]
/--
theorem `ofBijective_apply` / 定理 `ofBijective_apply`

English:
theorem ofBijective_apply
  given: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M)
  proof: rfl

@[simp]

中文:
定理 ofBijective_apply
  条件: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M)
  证明: rfl

@[simp]
-/
theorem ofBijective_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {hf} (x : M) :
    ofBijective f hf x = f x :=
  rfl

@[simp]
/--
theorem `ofBijective_symm_apply_apply` / 定理 `ofBijective_symm_apply_apply`

English:
theorem ofBijective_symm_apply_apply
  given: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M)
  proof: by
  simp [LinearEquiv.symm_apply_eq]

@[simp]

中文:
定理 ofBijective_symm_apply_apply
  条件: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M)
  证明: by
  simp [LinearEquiv.symm_apply_eq]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.symm_apply_eq, symm_apply_eq
-/
theorem ofBijective_symm_apply_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h} (x : M) :
    (ofBijective f h).symm (f x) = x := by
  simp [LinearEquiv.symm_apply_eq]

@[simp]
/--
theorem `apply_ofBijective_symm_apply` / 定理 `apply_ofBijective_symm_apply`

English:
theorem apply_ofBijective_symm_apply
  statement: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h}
  proof: by
  rw [← ofBijective_apply f (hf := h) ((ofBijective f h).symm x)]; rw [apply_symm_apply]

中文:
定理 apply_ofBijective_symm_apply
  结论: [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h}
  证明: by
  rw [← ofBijective_apply f (hf := h) ((ofBijective f h).symm x)]; rw [apply_symm_apply]

Depends on / 依赖: apply_symm_apply, ofBijective, ofBijective_apply
-/
theorem apply_ofBijective_symm_apply [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] {h}
    (x : M₂) : f ((ofBijective f h).symm x) = x := by
  rw [← ofBijective_apply f (hf := h) ((ofBijective f h).symm x)]; rw [apply_symm_apply]

end

end AddCommMonoid

end LinearEquiv

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

/--
Definition of `equivSubtypeMap` / `equivSubtypeMap` 的定义

English:
definition equivSubtypeMap
  signature: (p : Submodule R M) (q : Submodule R p)
  body: { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption }

@[simp]

中文:
定义 equivSubtypeMap
  签名: (p : 子模 R M) (q : 子模 R p)
  定义体: { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption }

@[simp]

Depends on / 依赖: codRestrict, domRestrict, invFun, p.subtype.domRestrict, subtype
-/
def equivSubtypeMap (p : Submodule R M) (q : Submodule R p) : q ≃ₗ[R] q.map p.subtype :=
  { (p.subtype.domRestrict q).codRestrict _ (by rintro ⟨x, hx⟩; exact ⟨x, hx, rfl⟩) with
    invFun := by
      rintro ⟨x, hx⟩
      refine ⟨⟨x, ?_⟩, ?_⟩ <;> rcases hx with ⟨⟨_, h⟩, _, rfl⟩ <;> assumption }

@[simp]
/--
theorem `equivSubtypeMap_apply` / 定理 `equivSubtypeMap_apply`

English:
theorem equivSubtypeMap_apply
  given: {p : Submodule R M} {q : Submodule R p} (x : q)
  proof: rfl

@[simp]

中文:
定理 equivSubtypeMap_apply
  条件: {p : 子模 R M} {q : 子模 R p} (x : q)
  证明: rfl

@[simp]
-/
theorem equivSubtypeMap_apply {p : Submodule R M} {q : Submodule R p} (x : q) :
    (p.equivSubtypeMap q x : M) = p.subtype.domRestrict q x :=
  rfl

@[simp]
/--
theorem `equivSubtypeMap_symm_apply` / 定理 `equivSubtypeMap_symm_apply`

English:
theorem equivSubtypeMap_symm_apply
  given: {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype)
  proof: rfl

中文:
定理 equivSubtypeMap_symm_apply
  条件: {p : 子模 R M} {q : 子模 R p} (x : q.map p.subtype)
  证明: rfl
-/
theorem equivSubtypeMap_symm_apply {p : Submodule R M} {q : Submodule R p} (x : q.map p.subtype) :
    ((p.equivSubtypeMap q).symm x : M) = x := rfl

/-- A linear injection `M ↪ N` restricts to an equivalence `f⁻¹ p ≃ p` for any submodule `p`
contained in its range. -/
@[simps! apply]
/--
Definition of `comap_equiv_self_of_inj_of_le` / `comap_equiv_self_of_inj_of_le` 的定义

English:
definition comap_equiv_self_of_inj_of_le
  signature: {f : M ->ₗ[R] N} {p : Submodule R N}
  body: LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨_, hx⟩ => mem_comap.mp hx)
  (⟨fun x y hxy => by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

中文:
定义 comap_equiv_self_of_inj_of_le
  签名: {f : M ->ₗ[R] N} {p : 子模 R N}
  定义体: LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨_, hx⟩ => mem_comap.mp hx)
  (⟨fun x y hxy => by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, Subtype, Subtype.ext_iff, Subtype.ext_iff.mp, codRestrict, ext_iff, mem_comap, mem_comap.mp, ofBijective, p.comap, subtype
-/
noncomputable def comap_equiv_self_of_inj_of_le {f : M ->ₗ[R] N} {p : Submodule R N}
    (hf : Injective f) (h : p <= LinearMap.range f) :
    p.comap f ≃ₗ[R] p :=
  LinearEquiv.ofBijective
  ((f ∘ₗ (p.comap f).subtype).codRestrict p <| fun ⟨_, hx⟩ => mem_comap.mp hx)
  (⟨fun x y hxy => by simpa using hf (Subtype.ext_iff.mp hxy),
    fun ⟨x, hx⟩ => by obtain ⟨y, rfl⟩ := h hx; exact ⟨⟨y, hx⟩, by simp [Subtype.ext_iff]⟩⟩)

end Module

end Submodule

namespace LinearMap

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
  [Module R M] [Module R M₁] [Module R M₂] [Module R M₃]

section

variable (f : M₁ ->ₗ[R] M₂) (i : M₃ ->ₗ[R] M₂) (hi : Injective i)
  (hf : forall x, f x in LinearMap.range i)

/--
Definition of `codRestrictOfInjective` / `codRestrictOfInjective` 的定义

English:
definition codRestrictOfInjective
  signature: : M₁ ->ₗ[R] M₃
  body: (LinearEquiv.ofInjective i hi).symm ∘ₗ f.codRestrict (LinearMap.range i) hf

@[simp]

中文:
定义 codRestrictOfInjective
  签名: : M₁ ->ₗ[R] M₃
  定义体: (LinearEquiv.ofInjective i hi).symm ∘ₗ f.codRestrict (LinearMap.range i) hf

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.range, codRestrict, f.codRestrict, ofInjective
-/
noncomputable def codRestrictOfInjective : M₁ ->ₗ[R] M₃ :=
  (LinearEquiv.ofInjective i hi).symm ∘ₗ f.codRestrict (LinearMap.range i) hf

@[simp]
/--
lemma `codRestrictOfInjective_comp_apply` / 引理 `codRestrictOfInjective_comp_apply`

English:
lemma codRestrictOfInjective_comp_apply
  given: (x : M₁)
  proof: by
  simp [LinearMap.codRestrictOfInjective]

@[simp]

中文:
引理 codRestrictOfInjective_comp_apply
  条件: (x : M₁)
  证明: by
  simp [LinearMap.codRestrictOfInjective]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.codRestrictOfInjective, codRestrictOfInjective
-/
lemma codRestrictOfInjective_comp_apply (x : M₁) :
    i (LinearMap.codRestrictOfInjective f i hi hf x) = f x := by
  simp [LinearMap.codRestrictOfInjective]

@[simp]
/--
lemma `codRestrictOfInjective_comp` / 引理 `codRestrictOfInjective_comp`

English:
lemma codRestrictOfInjective_comp
  proof: by
  ext
  simp

中文:
引理 codRestrictOfInjective_comp
  证明: by
  ext
  simp
-/
lemma codRestrictOfInjective_comp :
    i ∘ₗ LinearMap.codRestrictOfInjective f i hi hf = f := by
  ext
  simp

end

variable (f : M₁ ->ₗ[R] M₂ ->ₗ[R] M) (i : M₃ ->ₗ[R] M) (hi : Injective i)
  (hf : forall x y, f x y in LinearMap.range i)

/--
Definition of `codRestrict₂` / `codRestrict₂` 的定义

English:
definition codRestrict₂
  signature: :
  body: let e : LinearMap.range i ≃ₗ[R] M₃ := (LinearEquiv.ofInjective i hi).symm
  { toFun := fun x => e.comp <| (f x).codRestrict (p := LinearMap.range i) (hf x)
    map_add' := by intro x₁ x₂; ext y; simp [f.map_add, ← e.map_add, codRestrict]
    map_smul' := by intro t x; ext y; simp [f.map_smul, ← e.ma

中文:
定义 codRestrict₂
  签名: :
  定义体: let e : LinearMap.range i ≃ₗ[R] M₃ := (LinearEquiv.ofInjective i hi).symm
  { toFun := fun x => e.comp <| (f x).codRestrict (p := LinearMap.range i) (hf x)
    map_add' := by intro x₁ x₂; ext y; simp [f.map_add, ← e.map_add, codRestrict]
    map_smul' := by intro t x; ext y; simp [f.map_smul, ← e.ma

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.range, codRestrict, e.comp, e.map_add, e.map_smul, f.map_add, f.map_smul, map_add, map_smul, ofInjective
-/
noncomputable def codRestrict₂ :
    M₁ ->ₗ[R] M₂ ->ₗ[R] M₃ :=
  let e : LinearMap.range i ≃ₗ[R] M₃ := (LinearEquiv.ofInjective i hi).symm
  { toFun := fun x => e.comp <| (f x).codRestrict (p := LinearMap.range i) (hf x)
    map_add' := by intro x₁ x₂; ext y; simp [f.map_add, ← e.map_add, codRestrict]
    map_smul' := by intro t x; ext y; simp [f.map_smul, ← e.map_smul, codRestrict] }

@[simp]
/--
lemma `codRestrict₂_apply` / 引理 `codRestrict₂_apply`

English:
lemma codRestrict₂_apply
  given: (x : M₁) (y : M₂)
  proof: by
  simp [codRestrict₂]

中文:
引理 codRestrict₂_apply
  条件: (x : M₁) (y : M₂)
  证明: by
  simp [codRestrict₂]
-/
lemma codRestrict₂_apply (x : M₁) (y : M₂) :
    i (codRestrict₂ f i hi hf x y) = f x y := by
  simp [codRestrict₂]

end LinearMap
