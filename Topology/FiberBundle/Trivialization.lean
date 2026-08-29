/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Bundle
public import Mathlib.Data.Set.Image
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.OpenPartialHomeomorph.Constructions
public import Mathlib.Topology.Order.Basic

/-!
# Trivializations

## Main definitions

### Basic definitions

* `Bundle.Trivialization F p` : structure extending open partial homeomorphisms, defining a local
  trivialization of a topological space `Z` with projection `p` and fiber `F`.

* `Bundle.Pretrivialization F proj` : trivialization as a partial equivalence, mainly used when the
  topology on the total space has not yet been defined.

### Operations on bundles

We provide the following operations on `Trivialization`s.

* `Bundle.Trivialization.compHomeomorph`: given a local trivialization `e` of a fiber bundle
  `p : Z → B` and a homeomorphism `h : Z' ≃ₜ Z`, returns a local trivialization of the fiber bundle
  `p ∘ h`.

## Implementation notes

Previously, in mathlib, there was a structure `topological_vector_bundle.trivialization` which
extended another structure `topological_fiber_bundle.trivialization` by a linearity hypothesis. As
of PR https://github.com/leanprover-community/mathlib3/pull/17359, we have changed this to a single
structure `Bundle.Trivialization`, together with a mixin class `Bundle.Trivialization.IsLinear`.

This permits all the *data* of a vector bundle to be held at the level of fiber bundles, so that the
same trivializations can underlie an object's structure as (say) a vector bundle over `ℂ` and as a
vector bundle over `ℝ`, as well as its structure simply as a fiber bundle.

This might be a little surprising, given the general trend of the library to ever-increased
bundling. But in this case the typical motivation for more bundling does not apply: there is no
algebraic or order structure on the whole type of linear (say) trivializations of a bundle.
Indeed, since trivializations only have meaning on their base sets (taking junk values outside), the
type of linear trivializations is not even particularly well-behaved.
-/

@[expose] public section

open TopologicalSpace Filter Set Bundle Function
open scoped Topology

variable {B : Type*} (F : Type*) {E : B -> Type*}
variable {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] {proj : Z -> B}

/--
Definition of `Bundle.Pretrivialization` / `Bundle.Pretrivialization` 的定义

English:
structure Bundle.Pretrivialization
  parameters: (proj : Z -> B)
  extends: PartialEquiv Z (B × F)
  axioms and operations (6):
    - open_target : IsOpen target
    - baseSet : Set B
    - open_baseSet : IsOpen baseSet
    - source_eq : source = proj ⁻¹' baseSet
    - target_eq : target = baseSet ×ˢ univ
    - proj_toFun : forall p in source, (toFun p).1 = proj p

中文:
结构 Bundle.Pretrivialization
  参数: (proj : Z -> B)
  继承: 部分等价 Z (B × F)
  公理与运算 (6 个):
    - open_target : 是开集 target
    - baseSet : 集合 B
    - open_baseSet : 是开集 baseSet
    - source_eq : source = proj ⁻¹' baseSet
    - target_eq : target = baseSet ×ˢ univ
    - proj_toFun : 对任意 p in source, (toFun p).1 = proj p
-/
structure Bundle.Pretrivialization (proj : Z -> B) extends PartialEquiv Z (B × F) where
  open_target : IsOpen target
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : forall p in source, (toFun p).1 = proj p

namespace Bundle.Pretrivialization

variable {F}
variable (e : Pretrivialization F proj) {x : Z}

/--
Definition of `toFun'` / `toFun'` 的定义

English:
definition toFun'
  signature: : Z -> (B × F)
  body: e.toFun

中文:
定义 toFun'
  签名: : Z -> (B × F)
  定义体: e.toFun
-/
@[coe] def toFun' : Z -> (B × F) := e.toFun

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Pretrivialization F proj) fun _ => Z -> B × F
  body: ⟨toFun'⟩

@[ext]

中文:
实例 :
  签名: CoeFun (Pretrivialization F proj) fun _ => Z -> B × F
  定义体: ⟨toFun'⟩

@[ext]
-/
instance : CoeFun (Pretrivialization F proj) fun _ => Z -> B × F := ⟨toFun'⟩

@[ext]
/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  statement: (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
  proof: by
  cases e; cases e'; congr

中文:
引理 ext'
  结论: (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
  证明: by
  cases e; cases e'; congr
-/
lemma ext' (e e' : Pretrivialization F proj) (h₁ : e.toPartialEquiv = e'.toPartialEquiv)
    (h₂ : e.baseSet = e'.baseSet) : e = e' := by
  cases e; cases e'; congr

-- TODO: tag this lemma with the `ext` attribute instead?
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {e e' : Pretrivialization F proj} (h₁ : forall x, e x = e' x)
  proof: by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]

中文:
引理 ext
  结论: {e e' : Pretrivialization F proj} (h₁ : 对任意 x, e x = e' x)
  证明: by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]

Depends on / 依赖: e.source_eq, source_eq
-/
lemma ext {e e' : Pretrivialization F proj} (h₁ : forall x, e x = e' x)
    (h₂ : forall x, e.toPartialEquiv.symm x = e'.toPartialEquiv.symm x) (h₃ : e.baseSet = e'.baseSet) :
    e = e' := by
  ext1 <;> [ext1; exact h₃]
  · apply h₁
  · apply h₂
  · rw [e.source_eq, e'.source_eq, h₃]

/--
lemma `toPartialEquiv_injective` / 引理 `toPartialEquiv_injective`

English:
lemma toPartialEquiv_injective
  given: [Nonempty F]
  proof: by
  refine fun e e' h => ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h

@[simp, mfld_simps]

中文:
引理 toPartialEquiv_injective
  条件: [非空 F]
  证明: by
  refine fun e e' h => ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h

@[simp, mfld_simps]

Depends on / 依赖: PartialEquiv, PartialEquiv.target, Prod.fst, congr_arg, fst_image_prod, target, target_eq, univ_nonempty
-/
lemma toPartialEquiv_injective [Nonempty F] :
    Injective (toPartialEquiv : Pretrivialization F proj -> PartialEquiv Z (B × F)) := by
  refine fun e e' h => ext' _ _ h ?_
  simpa only [fst_image_prod, univ_nonempty, target_eq]
    using congr_arg (Prod.fst '' PartialEquiv.target ·) h

@[simp, mfld_simps]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑e.toPartialEquiv = e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_coe
  结论: ⇑e.toPartialEquiv = e
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_coe : ⇑e.toPartialEquiv = e :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  given: (ex : x in e.source)
  statement: (e x).1 = proj x
  proof: e.proj_toFun x ex

中文:
定理 coe_fst
  条件: (ex : x in e.source)
  结论: (e x).1 = proj x
  证明: e.proj_toFun x ex

Depends on / 依赖: e.proj_toFun, proj_toFun
-/
theorem coe_fst (ex : x in e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex

/--
theorem `mem_source` / 定理 `mem_source`

English:
theorem mem_source
  statement: x in e.source ↔ proj x in e.baseSet
  proof: by rw [e.source_eq, mem_preimage]

中文:
定理 mem_source
  结论: x in e.source ↔ proj x in e.baseSet
  证明: by rw [e.source_eq, mem_preimage]

Depends on / 依赖: e.source_eq, mem_preimage, source_eq
-/
theorem mem_source : x in e.source ↔ proj x in e.baseSet := by rw [e.source_eq, mem_preimage]

/--
theorem `coe_fst'` / 定理 `coe_fst'`

English:
theorem coe_fst'
  given: (ex : proj x in e.baseSet)
  statement: (e x).1 = proj x
  proof: e.coe_fst (e.mem_source.2 ex)

中文:
定理 coe_fst'
  条件: (ex : proj x in e.baseSet)
  结论: (e x).1 = proj x
  证明: e.coe_fst (e.mem_source.2 ex)

Depends on / 依赖: coe_fst, e.coe_fst, e.mem_source, mem_source
-/
theorem coe_fst' (ex : proj x in e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

/--
theorem `eqOn` / 定理 `eqOn`

English:
theorem eqOn
  statement: EqOn (Prod.fst ∘ e) proj e.source
  proof: fun _ hx => e.coe_fst hx

@[simp]

中文:
定理 eqOn
  结论: EqOn (积类型.fst ∘ e) proj e.source
  证明: fun _ hx => e.coe_fst hx

@[simp]
-/
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _ hx => e.coe_fst hx

@[simp]
/--
theorem `mk_proj_snd` / 定理 `mk_proj_snd`

English:
theorem mk_proj_snd
  given: (ex : x in e.source)
  statement: (proj x, (e x).2) = e x
  proof: Prod.ext (e.coe_fst ex).symm rfl

@[simp]

中文:
定理 mk_proj_snd
  条件: (ex : x in e.source)
  结论: (proj x, (e x).2) = e x
  证明: Prod.ext (e.coe_fst ex).symm rfl

@[simp]

Depends on / 依赖: Prod.ext, coe_fst, e.coe_fst
-/
theorem mk_proj_snd (ex : x in e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl

@[simp]
/--
theorem `mk_proj_snd'` / 定理 `mk_proj_snd'`

English:
theorem mk_proj_snd'
  given: (ex : proj x in e.baseSet)
  statement: (proj x, (e x).2) = e x
  proof: Prod.ext (e.coe_fst' ex).symm rfl

中文:
定理 mk_proj_snd'
  条件: (ex : proj x in e.baseSet)
  结论: (proj x, (e x).2) = e x
  证明: Prod.ext (e.coe_fst' ex).symm rfl

Depends on / 依赖: Prod.ext, coe_fst, e.coe_fst
-/
theorem mk_proj_snd' (ex : proj x in e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl

/--
Definition of `setSymm` / `setSymm` 的定义

English:
definition setSymm
  signature: : e.target -> Z
  body: e.target.domRestrict e.toPartialEquiv.symm

中文:
定义 setSymm
  签名: : e.target -> Z
  定义体: e.target.domRestrict e.toPartialEquiv.symm

Depends on / 依赖: domRestrict, e.target.domRestrict, e.toPartialEquiv.symm, target, toPartialEquiv
-/
def setSymm : e.target -> Z :=
  e.target.domRestrict e.toPartialEquiv.symm

/--
theorem `mem_target` / 定理 `mem_target`

English:
theorem mem_target
  given: {x : B × F}
  statement: x in e.target ↔ x.1 in e.baseSet
  proof: by
  rw [e.target_eq]; rw [prod_univ]; rw [mem_preimage]

中文:
定理 mem_target
  条件: {x : B × F}
  结论: x in e.target ↔ x.1 in e.baseSet
  证明: by
  rw [e.target_eq]; rw [prod_univ]; rw [mem_preimage]

Depends on / 依赖: e.target_eq, mem_preimage, prod_univ, target_eq
-/
theorem mem_target {x : B × F} : x in e.target ↔ x.1 in e.baseSet := by
  rw [e.target_eq]; rw [prod_univ]; rw [mem_preimage]

/--
theorem `proj_symm_apply` / 定理 `proj_symm_apply`

English:
theorem proj_symm_apply
  given: {x : B × F} (hx : x in e.target)
  statement: proj (e.toPartialEquiv.symm x) = x.1
  proof: by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this

中文:
定理 proj_symm_apply
  条件: {x : B × F} (hx : x in e.target)
  结论: proj (e.toPartialEquiv.symm x) = x.1
  证明: by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this

Depends on / 依赖: coe_coe, coe_fst, e.coe_coe, e.coe_fst, e.map_target, e.right_inv, map_target, right_inv
-/
theorem proj_symm_apply {x : B × F} (hx : x in e.target) : proj (e.toPartialEquiv.symm x) = x.1 := by
  have := (e.coe_fst (e.map_target hx)).symm
  rwa [← e.coe_coe, e.right_inv hx] at this

/--
theorem `proj_symm_apply'` / 定理 `proj_symm_apply'`

English:
theorem proj_symm_apply'
  given: {b : B} {x : F} (hx : b in e.baseSet)
  proof: e.proj_symm_apply (e.mem_target.2 hx)

中文:
定理 proj_symm_apply'
  条件: {b : B} {x : F} (hx : b in e.baseSet)
  证明: e.proj_symm_apply (e.mem_target.2 hx)

Depends on / 依赖: e.mem_target, e.proj_symm_apply, mem_target, proj_symm_apply
-/
theorem proj_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) :
    proj (e.toPartialEquiv.symm (b, x)) = b :=
  e.proj_symm_apply (e.mem_target.2 hx)

/--
theorem `proj_surjOn_baseSet` / 定理 `proj_surjOn_baseSet`

English:
theorem proj_surjOn_baseSet
  given: [Nonempty F]
  statement: Set.SurjOn proj e.source e.baseSet
  proof: fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩

@[simp, mfld_simps]

中文:
定理 proj_surjOn_baseSet
  条件: [非空 F]
  结论: 集合.满射限制 proj e.source e.baseSet
  证明: fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩

@[simp, mfld_simps]
-/
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet := fun b hb =>
  let ⟨y⟩ := ‹Nonempty F›
⟨e.toPartialEquiv.symm (b, y), e.toPartialEquiv.map_target e.mem_target.2 hb,
    e.proj_symm_apply' hb⟩

@[simp, mfld_simps]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: {x : B × F} (hx : x in e.target)
  statement: e (e.toPartialEquiv.symm x) = x
  proof: e.toPartialEquiv.right_inv hx

@[simp, mfld_simps]

中文:
定理 apply_symm_apply
  条件: {x : B × F} (hx : x in e.target)
  结论: e (e.toPartialEquiv.symm x) = x
  证明: e.toPartialEquiv.right_inv hx

@[simp, mfld_simps]

Depends on / 依赖: e.toPartialEquiv.right_inv, right_inv, toPartialEquiv
-/
theorem apply_symm_apply {x : B × F} (hx : x in e.target) : e (e.toPartialEquiv.symm x) = x :=
  e.toPartialEquiv.right_inv hx

@[simp, mfld_simps]
/--
theorem `apply_symm_apply'` / 定理 `apply_symm_apply'`

English:
theorem apply_symm_apply'
  given: {b : B} {x : F} (hx : b in e.baseSet)
  proof: e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]

中文:
定理 apply_symm_apply'
  条件: {b : B} {x : F} (hx : b in e.baseSet)
  证明: e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.mem_target, mem_target
-/
theorem apply_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) :
    e (e.toPartialEquiv.symm (b, x)) = (b, x) :=
  e.apply_symm_apply (e.mem_target.2 hx)

@[simp, mfld_simps]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: {x : Z} (hx : x in e.source)
  statement: e.toPartialEquiv.symm (e x) = x
  proof: e.toPartialEquiv.left_inv hx

中文:
定理 symm_apply_apply
  条件: {x : Z} (hx : x in e.source)
  结论: e.toPartialEquiv.symm (e x) = x
  证明: e.toPartialEquiv.left_inv hx

Depends on / 依赖: e.toPartialEquiv.left_inv, left_inv, toPartialEquiv
-/
theorem symm_apply_apply {x : Z} (hx : x in e.source) : e.toPartialEquiv.symm (e x) = x :=
  e.toPartialEquiv.left_inv hx

/--
theorem `symm_apply_mk_proj` / 定理 `symm_apply_mk_proj`

English:
theorem symm_apply_mk_proj
  given: {x : Z} (ex : x in e.source)
  proof: by
  rw [← e.coe_fst ex]; rw [← e.coe_coe]; rw [e.left_inv ex]

@[simp, mfld_simps]

中文:
定理 symm_apply_mk_proj
  条件: {x : Z} (ex : x in e.source)
  证明: by
  rw [← e.coe_fst ex]; rw [← e.coe_coe]; rw [e.left_inv ex]

@[simp, mfld_simps]

Depends on / 依赖: coe_coe, coe_fst, e.coe_coe, e.coe_fst, e.left_inv, left_inv
-/
theorem symm_apply_mk_proj {x : Z} (ex : x in e.source) :
    e.toPartialEquiv.symm (proj x, (e x).2) = x := by
  rw [← e.coe_fst ex]; rw [← e.coe_coe]; rw [e.left_inv ex]

@[simp, mfld_simps]
/--
theorem `preimage_symm_proj_baseSet` / 定理 `preimage_symm_proj_baseSet`

English:
theorem preimage_symm_proj_baseSet
  proof: by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]

中文:
定理 preimage_symm_proj_baseSet
  证明: by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]

Depends on / 依赖: e.mem_target.mp, e.proj_symm_apply, inter_eq_right, inter_eq_right.mpr, mem_preimage, mem_target, proj_symm_apply
-/
theorem preimage_symm_proj_baseSet :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' e.baseSet) inter e.target = e.target := by
  refine inter_eq_right.mpr fun x hx => ?_
  simp only [mem_preimage, e.proj_symm_apply hx]
  exact e.mem_target.mp hx

@[simp, mfld_simps]
/--
theorem `preimage_symm_proj_inter` / 定理 `preimage_symm_proj_inter`

English:
theorem preimage_symm_proj_inter
  given: (s : Set B)
  proof: by
  ext ⟨x, y⟩
  suffices x in e.baseSet -> (proj (e.toPartialEquiv.symm (x, y)) in s ↔ x in s) by
    simpa only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]

中文:
定理 preimage_symm_proj_inter
  条件: (s : 集合 B)
  证明: by
  ext ⟨x, y⟩
  suffices x in e.baseSet -> (proj (e.toPartialEquiv.symm (x, y)) in s ↔ x in s) by
    simpa only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]

Depends on / 依赖: and_congr_left_iff, and_true, baseSet, e.baseSet, e.proj_symm_apply, e.toPartialEquiv.symm, mem_inter_iff, mem_univ, prodMk_mem_set_prod_eq, proj_symm_apply, toPartialEquiv
-/
theorem preimage_symm_proj_inter (s : Set B) :
    e.toPartialEquiv.symm ⁻¹' (proj ⁻¹' s) inter e.baseSet ×ˢ univ = (s inter e.baseSet) ×ˢ univ := by
  ext ⟨x, y⟩
  suffices x in e.baseSet -> (proj (e.toPartialEquiv.symm (x, y)) in s ↔ x in s) by
    simpa only [prodMk_mem_set_prod_eq, mem_inter_iff, and_true, mem_univ, and_congr_left_iff]
  intro h
  rw [e.proj_symm_apply' h]

/--
theorem `target_inter_preimage_symm_source_eq` / 定理 `target_inter_preimage_symm_source_eq`

English:
theorem target_inter_preimage_symm_source_eq
  given: (e f : Pretrivialization F proj)
  proof: by
  rw [inter_comm]; rw [f.target_eq]; rw [e.source_eq]; rw [f.preimage_symm_proj_inter]

中文:
定理 target_inter_preimage_symm_source_eq
  条件: (e f : Pretrivialization F proj)
  证明: by
  rw [inter_comm]; rw [f.target_eq]; rw [e.source_eq]; rw [f.preimage_symm_proj_inter]

Depends on / 依赖: e.source_eq, f.preimage_symm_proj_inter, f.target_eq, inter_comm, preimage_symm_proj_inter, source_eq, target_eq
-/
theorem target_inter_preimage_symm_source_eq (e f : Pretrivialization F proj) :
    f.target inter f.toPartialEquiv.symm ⁻¹' e.source = (e.baseSet inter f.baseSet) ×ˢ univ := by
  rw [inter_comm]; rw [f.target_eq]; rw [e.source_eq]; rw [f.preimage_symm_proj_inter]

/--
theorem `trans_source` / 定理 `trans_source`

English:
theorem trans_source
  given: (e f : Pretrivialization F proj)
  proof: by
  rw [PartialEquiv.trans_source]; rw [PartialEquiv.symm_source]; rw [e.target_inter_preimage_symm_source_eq]

中文:
定理 trans_source
  条件: (e f : Pretrivialization F proj)
  证明: by
  rw [PartialEquiv.trans_source]; rw [PartialEquiv.symm_source]; rw [e.target_inter_preimage_symm_source_eq]

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_source, PartialEquiv.trans_source, e.target_inter_preimage_symm_source_eq, symm_source, target_inter_preimage_symm_source_eq, trans_source
-/
theorem trans_source (e f : Pretrivialization F proj) :
    (f.toPartialEquiv.symm.trans e.toPartialEquiv).source = (e.baseSet inter f.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source]; rw [PartialEquiv.symm_source]; rw [e.target_inter_preimage_symm_source_eq]

/--
theorem `symm_trans_symm` / 定理 `symm_trans_symm`

English:
theorem symm_trans_symm
  given: (e e' : Pretrivialization F proj)
  proof: by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm]; rw [PartialEquiv.symm_symm]

中文:
定理 symm_trans_symm
  条件: (e e' : Pretrivialization F proj)
  证明: by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm]; rw [PartialEquiv.symm_symm]

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_symm, PartialEquiv.trans_symm_eq_symm_trans_symm, symm_symm, trans_symm_eq_symm_trans_symm
-/
theorem symm_trans_symm (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).symm
      = e'.toPartialEquiv.symm.trans e.toPartialEquiv := by
  rw [PartialEquiv.trans_symm_eq_symm_trans_symm]; rw [PartialEquiv.symm_symm]

/--
theorem `symm_trans_source_eq` / 定理 `symm_trans_source_eq`

English:
theorem symm_trans_source_eq
  given: (e e' : Pretrivialization F proj)
  proof: by
  rw [PartialEquiv.trans_source]; rw [e'.source_eq]; rw [PartialEquiv.symm_source]; rw [e.target_eq]; rw [inter_comm]; rw [e.preimage_symm_proj_inter]; rw [inter_comm]

中文:
定理 symm_trans_source_eq
  条件: (e e' : Pretrivialization F proj)
  证明: by
  rw [PartialEquiv.trans_source]; rw [e'.source_eq]; rw [PartialEquiv.symm_source]; rw [e.target_eq]; rw [inter_comm]; rw [e.preimage_symm_proj_inter]; rw [inter_comm]

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_source, PartialEquiv.trans_source, e.preimage_symm_proj_inter, e.target_eq, inter_comm, preimage_symm_proj_inter, source_eq, symm_source, target_eq, trans_source
-/
theorem symm_trans_source_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet inter e'.baseSet) ×ˢ univ := by
  rw [PartialEquiv.trans_source]; rw [e'.source_eq]; rw [PartialEquiv.symm_source]; rw [e.target_eq]; rw [inter_comm]; rw [e.preimage_symm_proj_inter]; rw [inter_comm]

/--
theorem `symm_trans_target_eq` / 定理 `symm_trans_target_eq`

English:
theorem symm_trans_target_eq
  given: (e e' : Pretrivialization F proj)
  proof: by
  rw [← PartialEquiv.symm_source]; rw [symm_trans_symm]; rw [symm_trans_source_eq]; rw [inter_comm]

中文:
定理 symm_trans_target_eq
  条件: (e e' : Pretrivialization F proj)
  证明: by
  rw [← PartialEquiv.symm_source]; rw [symm_trans_symm]; rw [symm_trans_source_eq]; rw [inter_comm]

Depends on / 依赖: PartialEquiv, PartialEquiv.symm_source, inter_comm, symm_source, symm_trans_source_eq, symm_trans_symm
-/
theorem symm_trans_target_eq (e e' : Pretrivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet inter e'.baseSet) ×ˢ univ := by
  rw [← PartialEquiv.symm_source]; rw [symm_trans_symm]; rw [symm_trans_source_eq]; rw [inter_comm]

variable (e' : Pretrivialization F (π F E)) {b : B} {y : E b}

@[simp]
/--
theorem `coe_mem_source` / 定理 `coe_mem_source`

English:
theorem coe_mem_source
  statement: ↑y in e'.source ↔ b in e'.baseSet
  proof: e'.mem_source

@[mfld_simps]

中文:
定理 coe_mem_source
  结论: ↑y in e'.source ↔ b in e'.baseSet
  证明: e'.mem_source

@[mfld_simps]

Depends on / 依赖: mem_source
-/
theorem coe_mem_source : ↑y in e'.source ↔ b in e'.baseSet :=
  e'.mem_source

@[mfld_simps]
/--
theorem `coe_coe_fst` / 定理 `coe_coe_fst`

English:
theorem coe_coe_fst
  given: (hb : b in e'.baseSet)
  statement: (e' y).1 = b
  proof: by
  simp [hb]

中文:
定理 coe_coe_fst
  条件: (hb : b in e'.baseSet)
  结论: (e' y).1 = b
  证明: by
  simp [hb]
-/
theorem coe_coe_fst (hb : b in e'.baseSet) : (e' y).1 = b := by
  simp [hb]

/--
theorem `mk_mem_target` / 定理 `mk_mem_target`

English:
theorem mk_mem_target
  given: {x : B} {y : F}
  statement: (x, y) in e'.target ↔ x in e'.baseSet
  proof: e'.mem_target

@[simp, mfld_simps]

中文:
定理 mk_mem_target
  条件: {x : B} {y : F}
  结论: (x, y) in e'.target ↔ x in e'.baseSet
  证明: e'.mem_target

@[simp, mfld_simps]

Depends on / 依赖: mem_target
-/
theorem mk_mem_target {x : B} {y : F} : (x, y) in e'.target ↔ x in e'.baseSet :=
  e'.mem_target

@[simp, mfld_simps]
/--
theorem `symm_coe_proj` / 定理 `symm_coe_proj`

English:
theorem symm_coe_proj
  given: {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x in e'.baseSet)
  proof: e'.proj_symm_apply' h

中文:
定理 symm_coe_proj
  条件: {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x in e'.baseSet)
  证明: e'.proj_symm_apply' h

Depends on / 依赖: proj_symm_apply
-/
theorem symm_coe_proj {x : B} {y : F} (e' : Pretrivialization F (π F E)) (h : x in e'.baseSet) :
    (e'.toPartialEquiv.symm (x, y)).1 = x :=
  e'.proj_symm_apply' h

section Nonempty

variable [forall x, Nonempty (E x)]

open scoped Classical in
/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def symm (e : Pretrivialization F (π F E)) (b : B) (y : F)
  body: if hb : b in e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else Classical.arbitrary _

中文:
定义 noncomputable
  签名: def symm (e : Pretrivialization F (π F E)) (b : B) (y : F)
  定义体: if hb : b in e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else Classical.arbitrary _
-/
protected noncomputable def symm (e : Pretrivialization F (π F E)) (b : B) (y : F) : E b :=
  if hb : b in e.baseSet then
    cast (congr_arg E (e.proj_symm_apply' hb)) (e.toPartialEquiv.symm (b, y)).2
  else Classical.arbitrary _

/--
theorem `symm_apply` / 定理 `symm_apply`

English:
theorem symm_apply
  given: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: dif_pos hb

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values.

中文:
定理 symm_apply
  条件: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: dif_pos hb

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values.

Depends on / 依赖: dif_pos
-/
theorem symm_apply (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    e.symm b y = cast (congr_arg E (e.symm_coe_proj hb)) (e.toPartialEquiv.symm (b, y)).2 :=
  dif_pos hb

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/--
theorem `symm_apply_of_notMem` / 定理 `symm_apply_of_notMem`

English:
theorem symm_apply_of_notMem
  statement: (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
  proof: by
  simp [Pretrivialization.symm, hb]

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still re

中文:
定理 symm_apply_of_notMem
  结论: (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
  证明: by
  simp [Pretrivialization.symm, hb]

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still re

Depends on / 依赖: Pretrivialization, Pretrivialization.symm
-/
theorem symm_apply_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
    (y : F) : e.symm b y = Classical.arbitrary _ := by
  simp [Pretrivialization.symm, hb]

@[deprecated "The junk values of `Pretrivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/--
theorem `coe_symm_of_notMem` / 定理 `coe_symm_of_notMem`

English:
theorem coe_symm_of_notMem
  given: (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
  proof: by
  ext; exact symm_apply_of_notMem e hb _

中文:
定理 coe_symm_of_notMem
  条件: (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet)
  证明: by
  ext; exact symm_apply_of_notMem e hb _

Depends on / 依赖: symm_apply_of_notMem
-/
theorem coe_symm_of_notMem (e : Pretrivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) :
    e.symm b = fun _ => Classical.arbitrary _ := by
  ext; exact symm_apply_of_notMem e hb _

/--
theorem `mk_symm` / 定理 `mk_symm`

English:
theorem mk_symm
  given: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]

@[simp, mfld_simps]

中文:
定理 mk_symm
  条件: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]

@[simp, mfld_simps]

Depends on / 依赖: TotalSpace, TotalSpace.eta, TotalSpace.mk_cast, e.proj_symm_apply, e.symm_apply, mk_cast, proj_symm_apply, symm_apply
-/
theorem mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toPartialEquiv.symm (b, y) := by
  simp only [e.symm_apply hb, TotalSpace.mk_cast (e.proj_symm_apply' hb), TotalSpace.eta]

@[simp, mfld_simps]
/--
theorem `symm_proj_apply` / 定理 `symm_proj_apply`

English:
theorem symm_proj_apply
  statement: (e : Pretrivialization F (π F E)) (z : TotalSpace F E)
  proof: by
  rw [e.symm_apply hz]; rw [cast_eq_iff_heq]; rw [e.mk_proj_snd' hz]; rw [e.symm_apply_apply (e.mem_source.mpr hz)]

@[simp, mfld_simps]

中文:
定理 symm_proj_apply
  结论: (e : Pretrivialization F (π F E)) (z : 全空间 F E)
  证明: by
  rw [e.symm_apply hz]; rw [cast_eq_iff_heq]; rw [e.mk_proj_snd' hz]; rw [e.symm_apply_apply (e.mem_source.mpr hz)]

@[simp, mfld_simps]

Depends on / 依赖: cast_eq_iff_heq, e.mem_source.mpr, e.mk_proj_snd, e.symm_apply, e.symm_apply_apply, mem_source, mk_proj_snd, symm_apply, symm_apply_apply
-/
theorem symm_proj_apply (e : Pretrivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj in e.baseSet) : e.symm z.proj (e z).2 = z.2 := by
  rw [e.symm_apply hz]; rw [cast_eq_iff_heq]; rw [e.mk_proj_snd' hz]; rw [e.symm_apply_apply (e.mem_source.mpr hz)]

@[simp, mfld_simps]
/--
theorem `symm_apply_apply_mk` / 定理 `symm_apply_apply_mk`

English:
theorem symm_apply_apply_mk
  statement: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet)
  proof: e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]

中文:
定理 symm_apply_apply_mk
  结论: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet)
  证明: e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]

Depends on / 依赖: e.symm_proj_apply, symm_proj_apply
-/
theorem symm_apply_apply_mk (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet)
    (y : E b) : e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]
/--
theorem `apply_mk_symm` / 定理 `apply_mk_symm`

English:
theorem apply_mk_symm
  given: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: by
  rw [e.mk_symm hb]; rw [e.apply_symm_apply (e.mk_mem_target.mpr hb)]

中文:
定理 apply_mk_symm
  条件: (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: by
  rw [e.mk_symm hb]; rw [e.apply_symm_apply (e.mk_mem_target.mpr hb)]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.mk_mem_target.mpr, e.mk_symm, mk_mem_target, mk_symm
-/
theorem apply_mk_symm (e : Pretrivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) := by
  rw [e.mk_symm hb]; rw [e.apply_symm_apply (e.mk_mem_target.mpr hb)]

end Nonempty

/-- The restriction of a pretrivialization to a subset of the base. -/
@[simps toFun source target baseSet]
/--
Definition of `restrictPreimage'` / `restrictPreimage'` 的定义

English:
definition restrictPreimage'
  signature: (e : Pretrivialization F proj) (s : Set B)
  body: (⟨proj z, z.2⟩, (e z).2)
  invFun x := by classical exact if h : (x.1.1, x.2) in e.target then ⟨e.invFun (x.1, x.2), by
      simpa only [mem_preimage, ← e.proj_toFun _ (e.map_target' h), e.right_inv' h] using! x.1.2⟩
    else Classical.arbitrary (s -> F -> _) x.1 x.2
  source := Subtype.val ⁻¹' e.s

中文:
定义 restrictPreimage'
  签名: (e : Pretrivialization F proj) (s : 集合 B)
  定义体: (⟨proj z, z.2⟩, (e z).2)
  invFun x := by classical exact if h : (x.1.1, x.2) in e.target then ⟨e.invFun (x.1, x.2), by
      simpa only [mem_preimage, ← e.proj_toFun _ (e.map_target' h), e.right_inv' h] using! x.1.2⟩
    else Classical.arbitrary (s -> F -> _) x.1 x.2
  source := Subtype.val ⁻¹' e.s
-/
noncomputable def restrictPreimage' (e : Pretrivialization F proj) (s : Set B)
    [Nonempty (s -> F -> proj ⁻¹' s)] : Pretrivialization F (s.restrictPreimage proj) where
  toFun z := (⟨proj z, z.2⟩, (e z).2)
  invFun x := by classical exact if h : (x.1.1, x.2) in e.target then ⟨e.invFun (x.1, x.2), by
      simpa only [mem_preimage, ← e.proj_toFun _ (e.map_target' h), e.right_inv' h] using! x.1.2⟩
    else Classical.arbitrary (s -> F -> _) x.1 x.2
  source := Subtype.val ⁻¹' e.source
  target := (Prod.map Subtype.val id) ⁻¹' e.target
  map_source' z hz := by
    simpa only [Prod.map_apply, ← e.proj_toFun _ hz] using! e.map_source' hz
  map_target' x hx := by
    simp only [mem_preimage, (Prod.map_apply), id_eq] at hx
    rw [dif_pos hx]; exact e.map_target' hx
  left_inv' z hz := by
    dsimp only; rw [dif_pos] <;> all_goals simp_rw [← e.proj_toFun _ hz]
    exacts [Subtype.ext (e.left_inv' hz), e.map_source' hz]
right_inv' x hx := Subtype.val_injective.prodMap injective_id by
    simp only [mem_preimage, (Prod.map_apply), id_eq] at hx
    simp_rw [Prod.map_apply]; rw [dif_pos hx]
    convert! ← e.right_inv' hx; exact e.proj_toFun _ (e.map_target' hx)
open_target := e.open_target.preimage by fun_prop
  baseSet := Subtype.val ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage continuous_subtype_val
  source_eq := Set.ext fun _ => Set.ext_iff.mp e.source_eq _
  target_eq := Set.ext fun _ => Set.ext_iff.mp e.target_eq _
  proj_toFun _ _ := rfl

/-- The restriction of a pretrivialization to a set with nonempty intersection with the base set. -/
@[simps! toFun source target baseSet]
/--
Definition of `restrictPreimage` / `restrictPreimage` 的定义

English:
definition restrictPreimage
  signature: (e : Pretrivialization F proj) {s : Set B}
  body: have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

中文:
定义 restrictPreimage
  签名: (e : Pretrivialization F proj) {s : 集合 B}
  定义体: have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

Depends on / 依赖: Nonempty, Nonempty.some, Set.mem_preimage.mpr, e.invFun, e.proj_symm_apply, e.restrictPreimage, invFun, mem_preimage, proj_symm_apply, restrictPreimage
-/
noncomputable def restrictPreimage (e : Pretrivialization F proj) {s : Set B}
    (hs : (s inter e.baseSet).Nonempty) : Pretrivialization F (s.restrictPreimage proj) :=
have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

/-- Extend the total space of a pretrivialization from the preimage of a set to the whole space. -/
@[simps invFun source target baseSet]
/--
Definition of `domExtend` / `domExtend` 的定义

English:
definition domExtend
  signature: {s : Set B} (e : Pretrivialization F fun z : proj ⁻¹' s => proj z)
  body: by classical exact if h : proj z in s then e ⟨z, h⟩
    else (proj z, Classical.arbitrary (Z -> F) z)
  invFun x := e.invFun x
  source := Subtype.val '' e.source
  target := e.target
  map_source' _ := by
    rintro ⟨⟨z, hzp : proj z in s⟩, hze, rfl⟩
    simpa [hzp, e.coe_fst hze] using e.map_sourc

中文:
定义 domExtend
  签名: {s : 集合 B} (e : Pretrivialization F fun z : proj ⁻¹' s => proj z)
  定义体: by classical exact if h : proj z in s then e ⟨z, h⟩
    else (proj z, Classical.arbitrary (Z -> F) z)
  invFun x := e.invFun x
  source := Subtype.val '' e.source
  target := e.target
  map_source' _ := by
    rintro ⟨⟨z, hzp : proj z in s⟩, hze, rfl⟩
    simpa [hzp, e.coe_fst hze] using e.map_sourc

Depends on / 依赖: Classical, Classical.arbitrary, Subtype, Subtype.val, arbitrary, classical, coe_fst, dif_pos, e.coe_fst, e.invFun, e.map_source, e.map_target, e.source, e.symm_apply_apply, e.target, invFun, left_inv, map_source, map_target, right_inv
-/
noncomputable def domExtend {s : Set B} (e : Pretrivialization F fun z : proj ⁻¹' s => proj z)
    [Nonempty (Z -> F)] : Pretrivialization F proj where
  toFun z := by classical exact if h : proj z in s then e ⟨z, h⟩
    else (proj z, Classical.arbitrary (Z -> F) z)
  invFun x := e.invFun x
  source := Subtype.val '' e.source
  target := e.target
  map_source' _ := by
    rintro ⟨⟨z, hzp : proj z in s⟩, hze, rfl⟩
    simpa [hzp, e.coe_fst hze] using e.map_source hze
  map_target' x hx := by simpa using ⟨(e.invFun x).2, e.map_target hx⟩
  left_inv' _ := by rintro ⟨⟨z, hzp : proj z in s⟩, hze, rfl⟩; simp [hzp, e.symm_apply_apply hze]
  right_inv' x hx := (dif_pos (e.invFun x).2).trans (e.right_inv hx)
  open_target := e.open_target
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by ext z; simpa [e.source_eq] using
    (e.proj_symm_apply' · ▸ (e.invFun (proj z, Classical.arbitrary (Z -> F) z)).2)
  target_eq := by ext; simp [e.target_eq]
  proj_toFun _ := by rintro ⟨⟨z, hzp : proj z in s⟩, hze, rfl⟩; simp [hzp, e.coe_fst hze]

/-- Extend the base of a pretrivialization from a set to the whole space. -/
@[simps toFun source target baseSet]
/--
Definition of `codExtend'` / `codExtend'` 的定义

English:
definition codExtend'
  signature: {s : Set B} (hs : IsOpen s) {proj : Z -> s}
  body: ⟨(e z).1, (e z).2⟩
  invFun x := by classical exact if h : x.1 in s then e.invFun (⟨x.1, h⟩, x.2)
    else Classical.arbitrary (B -> F -> Z) x.1 x.2
  source := e.source
  target := (Prod.map Subtype.val id) '' e.target
  map_source' z hz := by simpa using e.map_source hz
  map_target' _ := by rintr

中文:
定义 codExtend'
  签名: {s : 集合 B} (hs : 是开集 s) {proj : Z -> s}
  定义体: ⟨(e z).1, (e z).2⟩
  invFun x := by classical exact if h : x.1 in s then e.invFun (⟨x.1, h⟩, x.2)
    else Classical.arbitrary (B -> F -> Z) x.1 x.2
  source := e.source
  target := (Prod.map Subtype.val id) '' e.target
  map_source' z hz := by simpa using e.map_source hz
  map_target' _ := by rintr
-/
noncomputable def codExtend' {s : Set B} (hs : IsOpen s) {proj : Z -> s}
    (e : Pretrivialization F proj) [Nonempty (B -> F -> Z)] :
    Pretrivialization F (Subtype.val ∘ proj) where
  toFun z := ⟨(e z).1, (e z).2⟩
  invFun x := by classical exact if h : x.1 in s then e.invFun (⟨x.1, h⟩, x.2)
    else Classical.arbitrary (B -> F -> Z) x.1 x.2
  source := e.source
  target := (Prod.map Subtype.val id) '' e.target
  map_source' z hz := by simpa using e.map_source hz
  map_target' _ := by rintro ⟨x, hx, rfl⟩; simpa using e.map_target hx
  left_inv' z hz := by simpa using e.left_inv hz
  right_inv' _ := by rintro ⟨x, hx, rfl⟩; ext <;> simp [e.apply_symm_apply hx]
  open_target := hs.isOpenMap_subtype_val.prodMap .id _ e.open_target
  baseSet := Subtype.val '' e.baseSet
  open_baseSet := hs.isOpenMap_subtype_val _ e.open_baseSet
  source_eq := by ext; simp [e.source_eq]
  target_eq := by rw [e.target_eq, prodMap_image_prod, image_id]
  proj_toFun _ h := by simp [e.coe_fst h]

/-- Extend the base of a pretrivialization from a nonempty set to the whole space. -/
@[simps! toFun source target baseSet]
/--
Definition of `codExtend` / `codExtend` 的定义

English:
definition codExtend
  signature: {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z -> s}
  body: have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

中文:
定义 codExtend
  签名: {s : 集合 B} (hs : 是开集 s) (nonempty : s.非空) {proj : Z -> s}
  定义体: have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

Depends on / 依赖: Nonempty, codExtend, e.codExtend, e.invFun, invFun, nonempty, nonempty.some_mem, some_mem
-/
noncomputable def codExtend {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z -> s}
    (e : Pretrivialization F proj) : Pretrivialization F (Subtype.val ∘ proj) :=
  have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

end Pretrivialization

variable [TopologicalSpace Z] [TopologicalSpace (TotalSpace F E)]

/--
Definition of `Trivialization` / `Trivialization` 的定义

English:
structure Trivialization
  parameters: (proj : Z -> B)
  extends: OpenPartialHomeomorph Z (B × F)
  axioms and operations (5):
    - baseSet : Set B
    - open_baseSet : IsOpen baseSet
    - source_eq : source = proj ⁻¹' baseSet
    - target_eq : target = baseSet ×ˢ univ
    - proj_toFun : forall p in source, (toOpenPartialHomeomorph p).1 = proj p

中文:
结构 Trivialization
  参数: (proj : Z -> B)
  继承: OpenPartialHomeomorph Z (B × F)
  公理与运算 (5 个):
    - baseSet : 集合 B
    - open_baseSet : 是开集 baseSet
    - source_eq : source = proj ⁻¹' baseSet
    - target_eq : target = baseSet ×ˢ univ
    - proj_toFun : 对任意 p in source, (toOpenPartialHomeomorph p).1 = proj p
-/
structure Trivialization (proj : Z -> B) extends OpenPartialHomeomorph Z (B × F) where
  /-- The domain of the local trivialisation (i.e., a subset of the bundle `Z`'s base):
  outside of it, the pretrivialisation returns a junk value -/
  baseSet : Set B
  open_baseSet : IsOpen baseSet
  source_eq : source = proj ⁻¹' baseSet
  target_eq : target = baseSet ×ˢ univ
  proj_toFun : forall p in source, (toOpenPartialHomeomorph p).1 = proj p

namespace Trivialization

variable {F}
variable (e : Trivialization F proj) {x : Z}

@[ext]
/--
lemma `ext'` / 引理 `ext'`

English:
lemma ext'
  statement: (e e' : Trivialization F proj)
  proof: by
  cases e; cases e'; congr

中文:
引理 ext'
  结论: (e e' : Trivialization F proj)
  证明: by
  cases e; cases e'; congr
-/
lemma ext' (e e' : Trivialization F proj)
    (h₁ : e.toOpenPartialHomeomorph = e'.toOpenPartialHomeomorph) (h₂ : e.baseSet = e'.baseSet) :
    e = e' := by
  cases e; cases e'; congr

/--
Definition of `toFun'` / `toFun'` 的定义

English:
definition toFun'
  signature: : Z -> (B × F)
  body: e.toFun

中文:
定义 toFun'
  签名: : Z -> (B × F)
  定义体: e.toFun
-/
@[coe] def toFun' : Z -> (B × F) := e.toFun

/--
Definition of `toPretrivialization` / `toPretrivialization` 的定义

English:
definition toPretrivialization
  signature: : Pretrivialization F proj
  body: { e with }

中文:
定义 toPretrivialization
  签名: : Pretrivialization F proj
  定义体: { e with }
-/
def toPretrivialization : Pretrivialization F proj :=
  { e with }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Trivialization F proj) fun _ => Z -> B × F
  body: ⟨toFun'⟩

中文:
实例 :
  签名: CoeFun (Trivialization F proj) fun _ => Z -> B × F
  定义体: ⟨toFun'⟩
-/
instance : CoeFun (Trivialization F proj) fun _ => Z -> B × F := ⟨toFun'⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (Trivialization F proj) (Pretrivialization F proj)
  body: ⟨toPretrivialization⟩

中文:
实例 :
  签名: Coe (Trivialization F proj) (Pretrivialization F proj)
  定义体: ⟨toPretrivialization⟩

Depends on / 依赖: toPretrivialization
-/
instance : Coe (Trivialization F proj) (Pretrivialization F proj) :=
  ⟨toPretrivialization⟩

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (proj : Z -> B) (e : Trivialization F proj)
  body: e

中文:
定义 Simps.apply
  签名: (proj : Z -> B) (e : Trivialization F proj)
  定义体: e
-/
def Simps.apply (proj : Z -> B) (e : Trivialization F proj) : Z -> B × F := e

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (proj : Z -> B) (e : Trivialization F proj)
  body: e.toOpenPartialHomeomorph.symm

initialize_simps_projections Trivialization (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (proj : Z -> B) (e : Trivialization F proj)
  定义体: e.toOpenPartialHomeomorph.symm

initialize_simps_projections Trivialization (toFun -> apply, invFun -> symm_apply)
-/
noncomputable def Simps.symm_apply (proj : Z -> B) (e : Trivialization F proj) : B × F -> Z :=
  e.toOpenPartialHomeomorph.symm

initialize_simps_projections Trivialization (toFun -> apply, invFun -> symm_apply)

/--
theorem `toPretrivialization_injective` / 定理 `toPretrivialization_injective`

English:
theorem toPretrivialization_injective
  proof: fun e e' h => by
  ext1
  exacts [OpenPartialHomeomorph.toPartialEquiv_injective congr(Pretrivialization.toPartialEquiv $h),
    congr(Pretrivialization.baseSet $h)]

@[simp, mfld_simps]

中文:
定理 toPretrivialization_injective
  证明: fun e e' h => by
  ext1
  exacts [OpenPartialHomeomorph.toPartialEquiv_injective congr(Pretrivialization.toPartialEquiv $h),
    congr(Pretrivialization.baseSet $h)]

@[simp, mfld_simps]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.toPartialEquiv_injective, Pretrivialization, Pretrivialization.baseSet, Pretrivialization.toPartialEquiv, baseSet, exacts, toPartialEquiv, toPartialEquiv_injective
-/
theorem toPretrivialization_injective :
    Function.Injective fun e : Trivialization F proj => e.toPretrivialization := fun e e' h => by
  ext1
  exacts [OpenPartialHomeomorph.toPartialEquiv_injective congr(Pretrivialization.toPartialEquiv $h),
    congr(Pretrivialization.baseSet $h)]

@[simp, mfld_simps]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  statement: ⇑e.toOpenPartialHomeomorph = e
  proof: rfl

@[simp, mfld_simps]

中文:
定理 coe_coe
  结论: ⇑e.toOpenPartialHomeomorph = e
  证明: rfl

@[simp, mfld_simps]
-/
theorem coe_coe : ⇑e.toOpenPartialHomeomorph = e :=
  rfl

@[simp, mfld_simps]
/--
theorem `coe_fst` / 定理 `coe_fst`

English:
theorem coe_fst
  given: (ex : x in e.source)
  statement: (e x).1 = proj x
  proof: e.proj_toFun x ex

中文:
定理 coe_fst
  条件: (ex : x in e.source)
  结论: (e x).1 = proj x
  证明: e.proj_toFun x ex

Depends on / 依赖: e.proj_toFun, proj_toFun
-/
theorem coe_fst (ex : x in e.source) : (e x).1 = proj x :=
  e.proj_toFun x ex

/--
theorem `eqOn` / 定理 `eqOn`

English:
theorem eqOn
  statement: EqOn (Prod.fst ∘ e) proj e.source
  proof: fun _x hx => e.coe_fst hx

中文:
定理 eqOn
  结论: EqOn (积类型.fst ∘ e) proj e.source
  证明: fun _x hx => e.coe_fst hx
-/
protected theorem eqOn : EqOn (Prod.fst ∘ e) proj e.source := fun _x hx => e.coe_fst hx

/--
theorem `mem_source` / 定理 `mem_source`

English:
theorem mem_source
  statement: x in e.source ↔ proj x in e.baseSet
  proof: by rw [e.source_eq, mem_preimage]

@[simp, mfld_simps]

中文:
定理 mem_source
  结论: x in e.source ↔ proj x in e.baseSet
  证明: by rw [e.source_eq, mem_preimage]

@[simp, mfld_simps]

Depends on / 依赖: e.source_eq, mem_preimage, source_eq
-/
theorem mem_source : x in e.source ↔ proj x in e.baseSet := by rw [e.source_eq, mem_preimage]

@[simp, mfld_simps]
/--
theorem `coe_fst'` / 定理 `coe_fst'`

English:
theorem coe_fst'
  given: (ex : proj x in e.baseSet)
  statement: (e x).1 = proj x
  proof: e.coe_fst (e.mem_source.2 ex)

中文:
定理 coe_fst'
  条件: (ex : proj x in e.baseSet)
  结论: (e x).1 = proj x
  证明: e.coe_fst (e.mem_source.2 ex)

Depends on / 依赖: coe_fst, e.coe_fst, e.mem_source, mem_source
-/
theorem coe_fst' (ex : proj x in e.baseSet) : (e x).1 = proj x :=
  e.coe_fst (e.mem_source.2 ex)

/--
theorem `mk_proj_snd` / 定理 `mk_proj_snd`

English:
theorem mk_proj_snd
  given: (ex : x in e.source)
  statement: (proj x, (e x).2) = e x
  proof: Prod.ext (e.coe_fst ex).symm rfl

中文:
定理 mk_proj_snd
  条件: (ex : x in e.source)
  结论: (proj x, (e x).2) = e x
  证明: Prod.ext (e.coe_fst ex).symm rfl

Depends on / 依赖: Prod.ext, coe_fst, e.coe_fst
-/
theorem mk_proj_snd (ex : x in e.source) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst ex).symm rfl

/--
theorem `mk_proj_snd'` / 定理 `mk_proj_snd'`

English:
theorem mk_proj_snd'
  given: (ex : proj x in e.baseSet)
  statement: (proj x, (e x).2) = e x
  proof: Prod.ext (e.coe_fst' ex).symm rfl

中文:
定理 mk_proj_snd'
  条件: (ex : proj x in e.baseSet)
  结论: (proj x, (e x).2) = e x
  证明: Prod.ext (e.coe_fst' ex).symm rfl

Depends on / 依赖: Prod.ext, coe_fst, e.coe_fst
-/
theorem mk_proj_snd' (ex : proj x in e.baseSet) : (proj x, (e x).2) = e x :=
  Prod.ext (e.coe_fst' ex).symm rfl

/--
theorem `source_inter_preimage_target_inter` / 定理 `source_inter_preimage_target_inter`

English:
theorem source_inter_preimage_target_inter
  given: (s : Set (B × F))
  proof: e.toOpenPartialHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]

中文:
定理 source_inter_preimage_target_inter
  条件: (s : 集合 (B × F))
  证明: e.toOpenPartialHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]

Depends on / 依赖: e.toOpenPartialHomeomorph.source_inter_preimage_target_inter, source_inter_preimage_target_inter, toOpenPartialHomeomorph
-/
theorem source_inter_preimage_target_inter (s : Set (B × F)) :
    e.source inter e ⁻¹' (e.target inter s) = e.source inter e ⁻¹' s :=
  e.toOpenPartialHomeomorph.source_inter_preimage_target_inter s

@[simp, mfld_simps]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (e : OpenPartialHomeomorph Z (B × F)) (i j k l m) (x : Z)
  proof: rfl

中文:
定理 coe_mk
  条件: (e : OpenPartialHomeomorph Z (B × F)) (i j k l m) (x : Z)
  证明: rfl
-/
theorem coe_mk (e : OpenPartialHomeomorph Z (B × F)) (i j k l m) (x : Z) :
    (Trivialization.mk e i j k l m : Trivialization F proj) x = e x :=
  rfl

/--
theorem `mem_target` / 定理 `mem_target`

English:
theorem mem_target
  given: {x : B × F}
  statement: x in e.target ↔ x.1 in e.baseSet
  proof: e.toPretrivialization.mem_target

中文:
定理 mem_target
  条件: {x : B × F}
  结论: x in e.target ↔ x.1 in e.baseSet
  证明: e.toPretrivialization.mem_target

Depends on / 依赖: e.toPretrivialization.mem_target, mem_target, toPretrivialization
-/
theorem mem_target {x : B × F} : x in e.target ↔ x.1 in e.baseSet :=
  e.toPretrivialization.mem_target

/--
theorem `map_target` / 定理 `map_target`

English:
theorem map_target
  given: {x : B × F} (hx : x in e.target)
  statement: e.toOpenPartialHomeomorph.symm x in e.source
  proof: e.toOpenPartialHomeomorph.map_target hx

中文:
定理 map_target
  条件: {x : B × F} (hx : x in e.target)
  结论: e.toOpenPartialHomeomorph.symm x in e.source
  证明: e.toOpenPartialHomeomorph.map_target hx

Depends on / 依赖: e.toOpenPartialHomeomorph.map_target, map_target, toOpenPartialHomeomorph
-/
theorem map_target {x : B × F} (hx : x in e.target) : e.toOpenPartialHomeomorph.symm x in e.source :=
  e.toOpenPartialHomeomorph.map_target hx

/--
theorem `proj_symm_apply` / 定理 `proj_symm_apply`

English:
theorem proj_symm_apply
  given: {x : B × F} (hx : x in e.target)
  proof: e.toPretrivialization.proj_symm_apply hx

中文:
定理 proj_symm_apply
  条件: {x : B × F} (hx : x in e.target)
  证明: e.toPretrivialization.proj_symm_apply hx

Depends on / 依赖: e.toPretrivialization.proj_symm_apply, proj_symm_apply, toPretrivialization
-/
theorem proj_symm_apply {x : B × F} (hx : x in e.target) :
    proj (e.toOpenPartialHomeomorph.symm x) = x.1 :=
  e.toPretrivialization.proj_symm_apply hx

/--
theorem `proj_symm_apply'` / 定理 `proj_symm_apply'`

English:
theorem proj_symm_apply'
  given: {b : B} {x : F} (hx : b in e.baseSet)
  proof: e.toPretrivialization.proj_symm_apply' hx

中文:
定理 proj_symm_apply'
  条件: {b : B} {x : F} (hx : b in e.baseSet)
  证明: e.toPretrivialization.proj_symm_apply' hx

Depends on / 依赖: e.toPretrivialization.proj_symm_apply, proj_symm_apply, toPretrivialization
-/
theorem proj_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) :
    proj (e.toOpenPartialHomeomorph.symm (b, x)) = b :=
  e.toPretrivialization.proj_symm_apply' hx

/--
theorem `proj_surjOn_baseSet` / 定理 `proj_surjOn_baseSet`

English:
theorem proj_surjOn_baseSet
  given: [Nonempty F]
  statement: Set.SurjOn proj e.source e.baseSet
  proof: e.toPretrivialization.proj_surjOn_baseSet

@[simp, mfld_simps]

中文:
定理 proj_surjOn_baseSet
  条件: [非空 F]
  结论: 集合.满射限制 proj e.source e.baseSet
  证明: e.toPretrivialization.proj_surjOn_baseSet

@[simp, mfld_simps]

Depends on / 依赖: e.toPretrivialization.proj_surjOn_baseSet, proj_surjOn_baseSet, toPretrivialization
-/
theorem proj_surjOn_baseSet [Nonempty F] : Set.SurjOn proj e.source e.baseSet :=
  e.toPretrivialization.proj_surjOn_baseSet

@[simp, mfld_simps]
/--
theorem `apply_symm_apply` / 定理 `apply_symm_apply`

English:
theorem apply_symm_apply
  given: {x : B × F} (hx : x in e.target)
  proof: e.toOpenPartialHomeomorph.right_inv hx

@[simp, mfld_simps]

中文:
定理 apply_symm_apply
  条件: {x : B × F} (hx : x in e.target)
  证明: e.toOpenPartialHomeomorph.right_inv hx

@[simp, mfld_simps]

Depends on / 依赖: e.toOpenPartialHomeomorph.right_inv, right_inv, toOpenPartialHomeomorph
-/
theorem apply_symm_apply {x : B × F} (hx : x in e.target) :
    e (e.toOpenPartialHomeomorph.symm x) = x :=
  e.toOpenPartialHomeomorph.right_inv hx

@[simp, mfld_simps]
/--
theorem `apply_symm_apply'` / 定理 `apply_symm_apply'`

English:
theorem apply_symm_apply'
  given: {b : B} {x : F} (hx : b in e.baseSet)
  proof: e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]

中文:
定理 apply_symm_apply'
  条件: {b : B} {x : F} (hx : b in e.baseSet)
  证明: e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]

Depends on / 依赖: apply_symm_apply, e.toPretrivialization.apply_symm_apply, toPretrivialization
-/
theorem apply_symm_apply' {b : B} {x : F} (hx : b in e.baseSet) :
    e (e.toOpenPartialHomeomorph.symm (b, x)) = (b, x) :=
  e.toPretrivialization.apply_symm_apply' hx

@[simp, mfld_simps]
/--
theorem `symm_apply_mk_proj` / 定理 `symm_apply_mk_proj`

English:
theorem symm_apply_mk_proj
  given: (ex : x in e.source)
  proof: e.toPretrivialization.symm_apply_mk_proj ex

中文:
定理 symm_apply_mk_proj
  条件: (ex : x in e.source)
  证明: e.toPretrivialization.symm_apply_mk_proj ex

Depends on / 依赖: e.toPretrivialization.symm_apply_mk_proj, symm_apply_mk_proj, toPretrivialization
-/
theorem symm_apply_mk_proj (ex : x in e.source) :
    e.toOpenPartialHomeomorph.symm (proj x, (e x).2) = x :=
  e.toPretrivialization.symm_apply_mk_proj ex

/--
theorem `symm_trans_source_eq` / 定理 `symm_trans_source_eq`

English:
theorem symm_trans_source_eq
  given: (e e' : Trivialization F proj)
  proof: Pretrivialization.symm_trans_source_eq e.toPretrivialization e'

中文:
定理 symm_trans_source_eq
  条件: (e e' : Trivialization F proj)
  证明: Pretrivialization.symm_trans_source_eq e.toPretrivialization e'

Depends on / 依赖: Pretrivialization, Pretrivialization.symm_trans_source_eq, e.toPretrivialization, symm_trans_source_eq, toPretrivialization
-/
theorem symm_trans_source_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).source = (e.baseSet inter e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_source_eq e.toPretrivialization e'

/--
theorem `symm_trans_target_eq` / 定理 `symm_trans_target_eq`

English:
theorem symm_trans_target_eq
  given: (e e' : Trivialization F proj)
  proof: Pretrivialization.symm_trans_target_eq e.toPretrivialization e'

中文:
定理 symm_trans_target_eq
  条件: (e e' : Trivialization F proj)
  证明: Pretrivialization.symm_trans_target_eq e.toPretrivialization e'

Depends on / 依赖: Pretrivialization, Pretrivialization.symm_trans_target_eq, e.toPretrivialization, symm_trans_target_eq, toPretrivialization
-/
theorem symm_trans_target_eq (e e' : Trivialization F proj) :
    (e.toPartialEquiv.symm.trans e'.toPartialEquiv).target = (e.baseSet inter e'.baseSet) ×ˢ univ :=
  Pretrivialization.symm_trans_target_eq e.toPretrivialization e'

/--
theorem `coe_fst_eventuallyEq_proj` / 定理 `coe_fst_eventuallyEq_proj`

English:
theorem coe_fst_eventuallyEq_proj
  given: (ex : x in e.source)
  statement: Prod.fst ∘ e =ᶠ[𝓝 x] proj
  proof: mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩

中文:
定理 coe_fst_eventuallyEq_proj
  条件: (ex : x in e.source)
  结论: 积类型.fst ∘ e =ᶠ[𝓝 x] proj
  证明: mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩

Depends on / 依赖: coe_fst, e.coe_fst, e.open_source, e.source, mem_nhds_iff, open_source, source
-/
theorem coe_fst_eventuallyEq_proj (ex : x in e.source) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  mem_nhds_iff.2 ⟨e.source, fun _y hy => e.coe_fst hy, e.open_source, ex⟩

/--
theorem `coe_fst_eventuallyEq_proj'` / 定理 `coe_fst_eventuallyEq_proj'`

English:
theorem coe_fst_eventuallyEq_proj'
  given: (ex : proj x in e.baseSet)
  statement: Prod.fst ∘ e =ᶠ[𝓝 x] proj
  proof: e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)

中文:
定理 coe_fst_eventuallyEq_proj'
  条件: (ex : proj x in e.baseSet)
  结论: 积类型.fst ∘ e =ᶠ[𝓝 x] proj
  证明: e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)

Depends on / 依赖: coe_fst_eventuallyEq_proj, e.coe_fst_eventuallyEq_proj, e.mem_source, mem_source
-/
theorem coe_fst_eventuallyEq_proj' (ex : proj x in e.baseSet) : Prod.fst ∘ e =ᶠ[𝓝 x] proj :=
  e.coe_fst_eventuallyEq_proj (e.mem_source.2 ex)

/--
theorem `map_proj_nhds` / 定理 `map_proj_nhds`

English:
theorem map_proj_nhds
  given: (ex : x in e.source)
  statement: map proj (𝓝 x) = 𝓝 (proj x)
  proof: by
  rw [← e.coe_fst ex]; rw [← map_congr (e.coe_fst_eventuallyEq_proj ex)]; rw [← map_map]; rw [← e.coe_coe]; rw [e.map_nhds_eq ex]; rw [map_fst_nhds]

中文:
定理 map_proj_nhds
  条件: (ex : x in e.source)
  结论: map proj (𝓝 x) = 𝓝 (proj x)
  证明: by
  rw [← e.coe_fst ex]; rw [← map_congr (e.coe_fst_eventuallyEq_proj ex)]; rw [← map_map]; rw [← e.coe_coe]; rw [e.map_nhds_eq ex]; rw [map_fst_nhds]

Depends on / 依赖: coe_coe, coe_fst, coe_fst_eventuallyEq_proj, e.coe_coe, e.coe_fst, e.coe_fst_eventuallyEq_proj, e.map_nhds_eq, map_congr, map_fst_nhds, map_map, map_nhds_eq
-/
theorem map_proj_nhds (ex : x in e.source) : map proj (𝓝 x) = 𝓝 (proj x) := by
  rw [← e.coe_fst ex]; rw [← map_congr (e.coe_fst_eventuallyEq_proj ex)]; rw [← map_map]; rw [← e.coe_coe]; rw [e.map_nhds_eq ex]; rw [map_fst_nhds]

/--
theorem `preimage_subset_source` / 定理 `preimage_subset_source`

English:
theorem preimage_subset_source
  given: {s : Set B} (hb : s subseteq e.baseSet)
  statement: proj ⁻¹' s subseteq e.source
  proof: fun _p hp => e.mem_source.mpr (hb hp)

中文:
定理 preimage_subset_source
  条件: {s : 集合 B} (hb : s subseteq e.baseSet)
  结论: proj ⁻¹' s subseteq e.source
  证明: fun _p hp => e.mem_source.mpr (hb hp)

Depends on / 依赖: e.mem_source.mpr, mem_source
-/
theorem preimage_subset_source {s : Set B} (hb : s subseteq e.baseSet) : proj ⁻¹' s subseteq e.source :=
  fun _p hp => e.mem_source.mpr (hb hp)

/--
theorem `image_preimage_eq_prod_univ` / 定理 `image_preimage_eq_prod_univ`

English:
theorem image_preimage_eq_prod_univ
  given: {s : Set B} (hb : s subseteq e.baseSet)
  proof: Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p in e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp

中文:
定理 image_preimage_eq_prod_univ
  条件: {s : 集合 B} (hb : s subseteq e.baseSet)
  证明: Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p in e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp

Depends on / 依赖: Subset, Subset.antisymm, antisymm, apply_symm_apply, e.apply_symm_apply, e.invFun, e.mem_target.mpr, e.preimage_subset_source, e.proj_symm_apply, e.proj_toFun, e.target, image_subset_iff, image_subset_iff.mpr, invFun, mem_preimage, mem_preimage.mpr, mem_target, preimage_subset_source, proj_symm_apply, proj_toFun
-/
theorem image_preimage_eq_prod_univ {s : Set B} (hb : s subseteq e.baseSet) :
    e '' proj ⁻¹' s = s ×ˢ univ :=
  Subset.antisymm
    (image_subset_iff.mpr fun p hp =>
      ⟨(e.proj_toFun p (e.preimage_subset_source hb hp)).symm ▸ hp, trivial⟩)
    fun p hp =>
    let hp' : p in e.target := e.mem_target.mpr (hb hp.1)
    ⟨e.invFun p, mem_preimage.mpr ((e.proj_symm_apply hp').symm ▸ hp.1), e.apply_symm_apply hp'⟩

/--
theorem `tendsto_nhds_iff` / 定理 `tendsto_nhds_iff`

English:
theorem tendsto_nhds_iff
  given: {α : Type*} {l : Filter α} {f : α -> Z} {z : Z} (hz : z in e.source)
  proof: by
  rw [e.nhds_eq_comap_inf_principal hz]; rw [tendsto_inf]; rw [tendsto_comap_iff]; rw [Prod.tendsto_iff]; rw [coe_coe]; rw [tendsto_principal]; rw [coe_fst _ hz]
  by_cases hl : forallᶠ x in l, f x in e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mo

中文:
定理 tendsto_nhds_iff
  条件: {α : 类型} {l : 滤子 α} {f : α -> Z} {z : Z} (hz : z in e.source)
  证明: by
  rw [e.nhds_eq_comap_inf_principal hz]; rw [tendsto_inf]; rw [tendsto_comap_iff]; rw [Prod.tendsto_iff]; rw [coe_coe]; rw [tendsto_principal]; rw [coe_fst _ hz]
  by_cases hl : forallᶠ x in l, f x in e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mo

Depends on / 依赖: Iff.rfl, Prod.tendsto_iff, and_false, and_true, coe_coe, coe_fst, e.coe_fst, e.nhds_eq_comap_inf_principal, e.open_baseSet.mem_nhds, e.source, e.source_eq, false_iff, hl.mono, mem_nhds, nhds_eq_comap_inf_principal, not_and, open_baseSet, source, source_eq, tendsto_comap_iff
-/
theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α -> Z} {z : Z} (hz : z in e.source) :
    Tendsto f l (𝓝 z) ↔
      Tendsto (proj ∘ f) l (𝓝 (proj z)) ∧ Tendsto (fun x => (e (f x)).2) l (𝓝 (e z).2) := by
  rw [e.nhds_eq_comap_inf_principal hz]; rw [tendsto_inf]; rw [tendsto_comap_iff]; rw [Prod.tendsto_iff]; rw [coe_coe]; rw [tendsto_principal]; rw [coe_fst _ hz]
  by_cases hl : forallᶠ x in l, f x in e.source
  · simp only [hl, and_true]
    refine (tendsto_congr' ?_).and Iff.rfl
    exact hl.mono fun x => e.coe_fst
  · simp only [hl, and_false, false_iff, not_and]
    rw [e.source_eq] at hl hz
exact fun h _ => hl h e.open_baseSet.mem_nhds hz

/--
theorem `nhds_eq_inf_comap` / 定理 `nhds_eq_inf_comap`

English:
theorem nhds_eq_inf_comap
  given: {z : Z} (hz : z in e.source)
  proof: by
  refine eq_of_forall_le_iff fun l => ?_
  rw [le_inf_iff]; rw [← tendsto_iff_comap]; rw [← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz

中文:
定理 nhds_eq_inf_comap
  条件: {z : Z} (hz : z in e.source)
  证明: by
  refine eq_of_forall_le_iff fun l => ?_
  rw [le_inf_iff]; rw [← tendsto_iff_comap]; rw [← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz

Depends on / 依赖: e.tendsto_nhds_iff, eq_of_forall_le_iff, le_inf_iff, tendsto_iff_comap, tendsto_nhds_iff
-/
theorem nhds_eq_inf_comap {z : Z} (hz : z in e.source) :
    𝓝 z = comap proj (𝓝 (proj z)) ⊓ comap (Prod.snd ∘ e) (𝓝 (e z).2) := by
  refine eq_of_forall_le_iff fun l => ?_
  rw [le_inf_iff]; rw [← tendsto_iff_comap]; rw [← tendsto_iff_comap]
  exact e.tendsto_nhds_iff hz

/--
Definition of `preimageHomeomorph` / `preimageHomeomorph` 的定义

English:
definition preimageHomeomorph
  signature: {s : Set B} (hb : s subseteq e.baseSet)
  body: (e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))

@[simp]

中文:
定义 preimageHomeomorph
  签名: {s : 集合 B} (hb : s subseteq e.baseSet)
  定义体: (e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.Set.prod, Homeomorph.Set.univ, Homeomorph.refl, e.image_preimage_eq_prod_univ, e.preimage_subset_source, e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource, homeomorphOfImageSubsetSource, image_preimage_eq_prod_univ, preimage_subset_source, prodCongr, toOpenPartialHomeomorph
-/
def preimageHomeomorph {s : Set B} (hb : s subseteq e.baseSet) : proj ⁻¹' s ≃ₜ s × F :=
  (e.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource (e.preimage_subset_source hb)
        (e.image_preimage_eq_prod_univ hb)).trans
    ((Homeomorph.Set.prod s univ).trans ((Homeomorph.refl s).prodCongr (Homeomorph.Set.univ F)))

@[simp]
/--
theorem `preimageHomeomorph_apply` / 定理 `preimageHomeomorph_apply`

English:
theorem preimageHomeomorph_apply
  given: {s : Set B} (hb : s subseteq e.baseSet) (p : proj ⁻¹' s)
  proof: Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl

中文:
定理 preimageHomeomorph_apply
  条件: {s : 集合 B} (hb : s subseteq e.baseSet) (p : proj ⁻¹' s)
  证明: Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl

Depends on / 依赖: Prod.ext, Subtype, Subtype.ext, e.mem_source.mpr, e.proj_toFun, mem_source, proj_toFun
-/
theorem preimageHomeomorph_apply {s : Set B} (hb : s subseteq e.baseSet) (p : proj ⁻¹' s) :
    e.preimageHomeomorph hb p = (⟨proj p, p.2⟩, (e p).2) :=
  Prod.ext (Subtype.ext (e.proj_toFun p (e.mem_source.mpr (hb p.2)))) rfl

/--
Definition of `preimageHomeomorph_symm_apply.aux` / `preimageHomeomorph_symm_apply.aux` 的定义

English:
definition preimageHomeomorph_symm_apply.aux
  signature: {s : Set B} (hb : s subseteq e.baseSet)
  body: (e.preimageHomeomorph hb).symm

@[simp]

中文:
定义 preimageHomeomorph_symm_apply.aux
  签名: {s : 集合 B} (hb : s subseteq e.baseSet)
  定义体: (e.preimageHomeomorph hb).symm

@[simp]
-/
protected def preimageHomeomorph_symm_apply.aux {s : Set B} (hb : s subseteq e.baseSet) :=
  (e.preimageHomeomorph hb).symm

@[simp]
/--
theorem `preimageHomeomorph_symm_apply` / 定理 `preimageHomeomorph_symm_apply`

English:
theorem preimageHomeomorph_symm_apply
  given: {s : Set B} (hb : s subseteq e.baseSet) (p : s × F)
  proof: rfl

中文:
定理 preimageHomeomorph_symm_apply
  条件: {s : 集合 B} (hb : s subseteq e.baseSet) (p : s × F)
  证明: rfl
-/
theorem preimageHomeomorph_symm_apply {s : Set B} (hb : s subseteq e.baseSet) (p : s × F) :
    (e.preimageHomeomorph hb).symm p =
      ⟨e.symm (p.1, p.2), ((preimageHomeomorph_symm_apply.aux e hb) p).2⟩ :=
  rfl

/--
Definition of `sourceHomeomorphBaseSetProd` / `sourceHomeomorphBaseSetProd` 的定义

English:
definition sourceHomeomorphBaseSetProd
  signature: : e.source ≃ₜ e.baseSet × F
  body: (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)

@[simp]

中文:
定义 sourceHomeomorphBaseSetProd
  签名: : e.source ≃ₜ e.baseSet × F
  定义体: (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.setCongr, e.preimageHomeomorph, e.source_eq, preimageHomeomorph, setCongr, source_eq, subset_rfl
-/
def sourceHomeomorphBaseSetProd : e.source ≃ₜ e.baseSet × F :=
  (Homeomorph.setCongr e.source_eq).trans (e.preimageHomeomorph subset_rfl)

@[simp]
/--
theorem `sourceHomeomorphBaseSetProd_apply` / 定理 `sourceHomeomorphBaseSetProd_apply`

English:
theorem sourceHomeomorphBaseSetProd_apply
  given: (p : e.source)
  proof: e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

中文:
定理 sourceHomeomorphBaseSetProd_apply
  条件: (p : e.source)
  证明: e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

Depends on / 依赖: e.mem_source.mp, e.preimageHomeomorph_apply, mem_source, preimageHomeomorph_apply, subset_rfl
-/
theorem sourceHomeomorphBaseSetProd_apply (p : e.source) :
    e.sourceHomeomorphBaseSetProd p = (⟨proj p, e.mem_source.mp p.2⟩, (e p).2) :=
  e.preimageHomeomorph_apply subset_rfl ⟨p, e.mem_source.mp p.2⟩

/--
Definition of `sourceHomeomorphBaseSetProd_symm_apply.aux` / `sourceHomeomorphBaseSetProd_symm_apply.aux` 的定义

English:
definition sourceHomeomorphBaseSetProd_symm_apply.aux
  body: e.sourceHomeomorphBaseSetProd.symm

@[simp]

中文:
定义 sourceHomeomorphBaseSetProd_symm_apply.aux
  定义体: e.sourceHomeomorphBaseSetProd.symm

@[simp]
-/
protected def sourceHomeomorphBaseSetProd_symm_apply.aux := e.sourceHomeomorphBaseSetProd.symm

@[simp]
/--
theorem `sourceHomeomorphBaseSetProd_symm_apply` / 定理 `sourceHomeomorphBaseSetProd_symm_apply`

English:
theorem sourceHomeomorphBaseSetProd_symm_apply
  given: (p : e.baseSet × F)
  proof: rfl

中文:
定理 sourceHomeomorphBaseSetProd_symm_apply
  条件: (p : e.baseSet × F)
  证明: rfl
-/
theorem sourceHomeomorphBaseSetProd_symm_apply (p : e.baseSet × F) :
    e.sourceHomeomorphBaseSetProd.symm p =
      ⟨e.symm (p.1, p.2), (sourceHomeomorphBaseSetProd_symm_apply.aux e p).2⟩ :=
  rfl

/--
Definition of `preimageSingletonHomeomorph` / `preimageSingletonHomeomorph` 的定义

English:
definition preimageSingletonHomeomorph
  signature: {b : B} (hb : b in e.baseSet)
  body: .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb))
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)

@[simp]

中文:
定义 preimageSingletonHomeomorph
  签名: {b : B} (hb : b in e.baseSet)
  定义体: .trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb))
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.homeomorphOfUnique, Homeomorph.punitProd, Homeomorph.refl, Set.singleton_subset_iff.mpr, e.preimageHomeomorph, homeomorphOfUnique, preimageHomeomorph, prodCongr, punitProd, singleton_subset_iff
-/
def preimageSingletonHomeomorph {b : B} (hb : b in e.baseSet) : proj ⁻¹' {b} ≃ₜ F :=
.trans (e.preimageHomeomorph (Set.singleton_subset_iff.mpr hb))
    .trans (.prodCongr (Homeomorph.homeomorphOfUnique ({b} : Set B) PUnit.{1}) (Homeomorph.refl F))
      (Homeomorph.punitProd F)

@[simp]
/--
theorem `preimageSingletonHomeomorph_apply` / 定理 `preimageSingletonHomeomorph_apply`

English:
theorem preimageSingletonHomeomorph_apply
  given: {b : B} (hb : b in e.baseSet) (p : proj ⁻¹' {b})
  proof: rfl

@[simp]

中文:
定理 preimageSingletonHomeomorph_apply
  条件: {b : B} (hb : b in e.baseSet) (p : proj ⁻¹' {b})
  证明: rfl

@[simp]
-/
theorem preimageSingletonHomeomorph_apply {b : B} (hb : b in e.baseSet) (p : proj ⁻¹' {b}) :
    e.preimageSingletonHomeomorph hb p = (e p).2 :=
  rfl

@[simp]
/--
theorem `preimageSingletonHomeomorph_symm_apply` / 定理 `preimageSingletonHomeomorph_symm_apply`

English:
theorem preimageSingletonHomeomorph_symm_apply
  given: {b : B} (hb : b in e.baseSet) (p : F)
  proof: rfl

中文:
定理 preimageSingletonHomeomorph_symm_apply
  条件: {b : B} (hb : b in e.baseSet) (p : F)
  证明: rfl
-/
theorem preimageSingletonHomeomorph_symm_apply {b : B} (hb : b in e.baseSet) (p : F) :
    (e.preimageSingletonHomeomorph hb).symm p =
      ⟨e.symm (b, p), by rw [mem_preimage, e.proj_symm_apply' hb, mem_singleton_iff]⟩ :=
  rfl

/--
theorem `continuousAt_proj` / 定理 `continuousAt_proj`

English:
theorem continuousAt_proj
  given: (ex : x in e.source)
  statement: ContinuousAt proj x
  proof: (e.map_proj_nhds ex).le

中文:
定理 continuousAt_proj
  条件: (ex : x in e.source)
  结论: ContinuousAt proj x
  证明: (e.map_proj_nhds ex).le

Depends on / 依赖: e.map_proj_nhds, map_proj_nhds
-/
theorem continuousAt_proj (ex : x in e.source) : ContinuousAt proj x :=
  (e.map_proj_nhds ex).le

/--
theorem `continuousOn_proj` / 定理 `continuousOn_proj`

English:
theorem continuousOn_proj
  statement: ContinuousOn proj e.source
  proof: continuousOn_of_forall_continuousAt fun _ => e.continuousAt_proj

中文:
定理 continuousOn_proj
  结论: ContinuousOn proj e.source
  证明: continuousOn_of_forall_continuousAt fun _ => e.continuousAt_proj

Depends on / 依赖: continuousAt_proj, continuousOn_of_forall_continuousAt, e.continuousAt_proj
-/
theorem continuousOn_proj : ContinuousOn proj e.source :=
  continuousOn_of_forall_continuousAt fun _ => e.continuousAt_proj

/--
theorem `continuousAt_symm_prodMk_left` / 定理 `continuousAt_symm_prodMk_left`

English:
theorem continuousAt_symm_prodMk_left
  given: {b : B} {v : F} (hb : b in e.baseSet)
  proof: (e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hb)).comp (by fun_prop)

中文:
定理 continuousAt_symm_prodMk_left
  条件: {b : B} {v : F} (hb : b in e.baseSet)
  证明: (e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hb)).comp (by fun_prop)

Depends on / 依赖: continuousAt_symm, e.mem_target.mpr, e.toOpenPartialHomeomorph.continuousAt_symm, fun_prop, mem_target, toOpenPartialHomeomorph
-/
theorem continuousAt_symm_prodMk_left {b : B} {v : F} (hb : b in e.baseSet) :
    ContinuousAt (fun x => e.symm (x, v)) b :=
  (e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hb)).comp (by fun_prop)

/--
theorem `continuousOn_symm_prodMk_left` / 定理 `continuousOn_symm_prodMk_left`

English:
theorem continuousOn_symm_prodMk_left
  given: {v : F}
  statement: ContinuousOn (fun x => e.symm (x, v)) e.baseSet
  proof: fun _ hb => (e.continuousAt_symm_prodMk_left hb).continuousWithinAt

中文:
定理 continuousOn_symm_prodMk_left
  条件: {v : F}
  结论: ContinuousOn (fun x => e.symm (x, v)) e.baseSet
  证明: fun _ hb => (e.continuousAt_symm_prodMk_left hb).continuousWithinAt

Depends on / 依赖: continuousAt_symm_prodMk_left, continuousWithinAt, e.continuousAt_symm_prodMk_left
-/
theorem continuousOn_symm_prodMk_left {v : F} : ContinuousOn (fun x => e.symm (x, v)) e.baseSet :=
  fun _ hb => (e.continuousAt_symm_prodMk_left hb).continuousWithinAt

/--
Definition of `compHomeomorph` / `compHomeomorph` 的定义

English:
definition compHomeomorph
  signature: {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z)
  body: h.transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p in e.source := by simpa using hp
    si

中文:
定义 compHomeomorph
  签名: {Z' : 类型} [拓扑空间 Z'] (h : Z' ≃ₜ Z)
  定义体: h.transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p in e.source := by simpa using hp
    si
-/
protected def compHomeomorph {Z' : Type*} [TopologicalSpace Z'] (h : Z' ≃ₜ Z) :
    Trivialization F (proj ∘ h) where
  toOpenPartialHomeomorph := h.transOpenPartialHomeomorph e.toOpenPartialHomeomorph
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := by simp [source_eq, preimage_preimage, Function.comp_def]
  target_eq := by simp [target_eq]
  proj_toFun p hp := by
    have hp : h p in e.source := by simpa using hp
    simp [hp]

/--
Definition of `homeomorphComp` / `homeomorphComp` 的定义

English:
definition homeomorphComp
  signature: {B' : Type*} [TopologicalSpace B'] (h : B ≃ₜ B')
  body: e.toOpenPartialHomeomorph.transHomeomorph (h.prodCongr <| .refl _)
  baseSet := h.symm ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage h.continuous_symm
  source_eq := by ext; simp [e.mem_source]
  target_eq := by ext; simp [Prod.map, e.mem_target]
  proj_toFun p hp := by simpa using e.proj_

中文:
定义 homeomorphComp
  签名: {B' : 类型} [拓扑空间 B'] (h : B ≃ₜ B')
  定义体: e.toOpenPartialHomeomorph.transHomeomorph (h.prodCongr <| .refl _)
  baseSet := h.symm ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage h.continuous_symm
  source_eq := by ext; simp [e.mem_source]
  target_eq := by ext; simp [Prod.map, e.mem_target]
  proj_toFun p hp := by simpa using e.proj_
-/
protected def homeomorphComp {B' : Type*} [TopologicalSpace B'] (h : B ≃ₜ B') :
    Trivialization F (h ∘ proj) where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.transHomeomorph (h.prodCongr <| .refl _)
  baseSet := h.symm ⁻¹' e.baseSet
  open_baseSet := e.open_baseSet.preimage h.continuous_symm
  source_eq := by ext; simp [e.mem_source]
  target_eq := by ext; simp [Prod.map, e.mem_target]
  proj_toFun p hp := by simpa using e.proj_toFun p hp

/--
theorem `continuousAt_of_comp_right` / 定理 `continuousAt_of_comp_right`

English:
theorem continuousAt_of_comp_right
  statement: {X : Type*} [TopologicalSpace X] {f : Z -> X} {z : Z}
  proof: by
  have hez : z in e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target]; rw [e.mem_source]
    exact he
  rwa [e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    OpenPartialHomeomorph.symm_symm]

中文:
定理 continuousAt_of_comp_right
  结论: {X : 类型} [拓扑空间 X] {f : Z -> X} {z : Z}
  证明: by
  have hez : z in e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target]; rw [e.mem_source]
    exact he
  rwa [e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    OpenPartialHomeomorph.symm_symm]

Depends on / 依赖: OpenPartialHomeomorph, OpenPartialHomeomorph.symm_symm, PartialEquiv, PartialEquiv.symm_target, continuousAt_iff_continuousAt_comp_right, e.mem_source, e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right, e.toPartialEquiv.symm.target, mem_source, symm_symm, symm_target, target, toOpenPartialHomeomorph, toPartialEquiv
-/
theorem continuousAt_of_comp_right {X : Type*} [TopologicalSpace X] {f : Z -> X} {z : Z}
    (e : Trivialization F proj) (he : proj z in e.baseSet)
    (hf : ContinuousAt (f ∘ e.toPartialEquiv.symm) (e z)) : ContinuousAt f z := by
  have hez : z in e.toPartialEquiv.symm.target := by
    rw [PartialEquiv.symm_target]; rw [e.mem_source]
    exact he
  rwa [e.toOpenPartialHomeomorph.symm.continuousAt_iff_continuousAt_comp_right hez,
    OpenPartialHomeomorph.symm_symm]

/--
theorem `continuousAt_of_comp_left` / 定理 `continuousAt_of_comp_left`

English:
theorem continuousAt_of_comp_left
  statement: {X : Type*} [TopologicalSpace X] {f : X -> Z} {x : X}
  proof: by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq]; rw [← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)

中文:
定理 continuousAt_of_comp_left
  结论: {X : 类型} [拓扑空间 X] {f : X -> Z} {x : X}
  证明: by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq]; rw [← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)

Depends on / 依赖: continuousAt_iff_continuousAt_comp_left, e.continuousAt_iff_continuousAt_comp_left, e.open_baseSet.mem_nhds, e.source_eq, hf_proj, hf_proj.preimage_mem_nhds, mem_nhds, open_baseSet, preimage_comp, preimage_mem_nhds, source_eq
-/
theorem continuousAt_of_comp_left {X : Type*} [TopologicalSpace X] {f : X -> Z} {x : X}
    (e : Trivialization F proj) (hf_proj : ContinuousAt (proj ∘ f) x) (he : proj (f x) in e.baseSet)
    (hf : ContinuousAt (e ∘ f) x) : ContinuousAt f x := by
  rw [e.continuousAt_iff_continuousAt_comp_left]
  · exact hf
  rw [e.source_eq]; rw [← preimage_comp]
  exact hf_proj.preimage_mem_nhds (e.open_baseSet.mem_nhds he)

variable (e' : Trivialization F (π F E)) {b : B} {y : E b}

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  statement: ContinuousOn e' e'.source
  proof: e'.continuousOn_toFun

中文:
定理 continuousOn
  结论: ContinuousOn e' e'.source
  证明: e'.continuousOn_toFun
-/
protected theorem continuousOn : ContinuousOn e' e'.source :=
  e'.continuousOn_toFun

/--
theorem `coe_mem_source` / 定理 `coe_mem_source`

English:
theorem coe_mem_source
  statement: ↑y in e'.source ↔ b in e'.baseSet
  proof: e'.mem_source

中文:
定理 coe_mem_source
  结论: ↑y in e'.source ↔ b in e'.baseSet
  证明: e'.mem_source

Depends on / 依赖: mem_source
-/
theorem coe_mem_source : ↑y in e'.source ↔ b in e'.baseSet :=
  e'.mem_source

/--
theorem `coe_coe_fst` / 定理 `coe_coe_fst`

English:
theorem coe_coe_fst
  given: (hb : b in e'.baseSet)
  statement: (e' y).1 = b
  proof: e'.coe_fst (e'.mem_source.2 hb)

中文:
定理 coe_coe_fst
  条件: (hb : b in e'.baseSet)
  结论: (e' y).1 = b
  证明: e'.coe_fst (e'.mem_source.2 hb)

Depends on / 依赖: coe_fst, mem_source
-/
theorem coe_coe_fst (hb : b in e'.baseSet) : (e' y).1 = b :=
  e'.coe_fst (e'.mem_source.2 hb)

/--
theorem `mk_mem_target` / 定理 `mk_mem_target`

English:
theorem mk_mem_target
  given: {y : F}
  statement: (b, y) in e'.target ↔ b in e'.baseSet
  proof: e'.toPretrivialization.mem_target

@[simp, mfld_simps]

中文:
定理 mk_mem_target
  条件: {y : F}
  结论: (b, y) in e'.target ↔ b in e'.baseSet
  证明: e'.toPretrivialization.mem_target

@[simp, mfld_simps]

Depends on / 依赖: mem_target, toPretrivialization, toPretrivialization.mem_target
-/
theorem mk_mem_target {y : F} : (b, y) in e'.target ↔ b in e'.baseSet :=
  e'.toPretrivialization.mem_target

@[simp, mfld_simps]
/--
theorem `symm_apply_apply` / 定理 `symm_apply_apply`

English:
theorem symm_apply_apply
  given: {x : TotalSpace F E} (hx : x in e'.source)
  proof: e'.toPartialEquiv.left_inv hx

@[simp, mfld_simps]

中文:
定理 symm_apply_apply
  条件: {x : 全空间 F E} (hx : x in e'.source)
  证明: e'.toPartialEquiv.left_inv hx

@[simp, mfld_simps]

Depends on / 依赖: left_inv, toPartialEquiv, toPartialEquiv.left_inv
-/
theorem symm_apply_apply {x : TotalSpace F E} (hx : x in e'.source) :
    e'.toOpenPartialHomeomorph.symm (e' x) = x :=
  e'.toPartialEquiv.left_inv hx

@[simp, mfld_simps]
/--
theorem `symm_coe_proj` / 定理 `symm_coe_proj`

English:
theorem symm_coe_proj
  given: {x : B} {y : F} (e : Trivialization F (π F E)) (h : x in e.baseSet)
  proof: e.proj_symm_apply' h

中文:
定理 symm_coe_proj
  条件: {x : B} {y : F} (e : Trivialization F (π F E)) (h : x in e.baseSet)
  证明: e.proj_symm_apply' h

Depends on / 依赖: e.proj_symm_apply, proj_symm_apply
-/
theorem symm_coe_proj {x : B} {y : F} (e : Trivialization F (π F E)) (h : x in e.baseSet) :
    (e.toOpenPartialHomeomorph.symm (x, y)).1 = x :=
  e.proj_symm_apply' h

section Nonempty

variable [forall x, Nonempty (E x)]

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def symm (e : Trivialization F (π F E)) (b : B) (y : F)
  body: e.toPretrivialization.symm b y

中文:
定义 noncomputable
  签名: def symm (e : Trivialization F (π F E)) (b : B) (y : F)
  定义体: e.toPretrivialization.symm b y
-/
protected noncomputable def symm (e : Trivialization F (π F E)) (b : B) (y : F) : E b :=
  e.toPretrivialization.symm b y

/--
theorem `symm_apply` / 定理 `symm_apply`

English:
theorem symm_apply
  given: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: dif_pos hb

@[deprecated "The junk values of `Trivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (

中文:
定理 symm_apply
  条件: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: dif_pos hb

@[deprecated "The junk values of `Trivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (

Depends on / 依赖: dif_pos
-/
theorem symm_apply (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    e.symm b y =
      cast (congr_arg E (e.symm_coe_proj hb)) (e.toOpenPartialHomeomorph.symm (b, y)).2 :=
  dif_pos hb

@[deprecated "The junk values of `Trivialization.symm` were changed from `0` to
`Classical.arbitrary` and should not be relied on; this lemma will be removed soon. Note that this
change does not affect the linear versions `symmₗ` and `symmL`, which still retain `0` as the junk
values." (since := "2026-06-23")]
/--
theorem `symm_apply_of_notMem` / 定理 `symm_apply_of_notMem`

English:
theorem symm_apply_of_notMem
  given: (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F)
  proof: e.toPretrivialization.symm_apply_of_notMem hb y

中文:
定理 symm_apply_of_notMem
  条件: (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F)
  证明: e.toPretrivialization.symm_apply_of_notMem hb y

Depends on / 依赖: e.toPretrivialization.symm_apply_of_notMem, symm_apply_of_notMem, toPretrivialization
-/
theorem symm_apply_of_notMem (e : Trivialization F (π F E)) {b : B} (hb : b ∉ e.baseSet) (y : F) :
    e.symm b y = Classical.arbitrary _ :=
  e.toPretrivialization.symm_apply_of_notMem hb y

/--
theorem `mk_symm` / 定理 `mk_symm`

English:
theorem mk_symm
  given: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: e.toPretrivialization.mk_symm hb y

@[simp, mfld_simps]

中文:
定理 mk_symm
  条件: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: e.toPretrivialization.mk_symm hb y

@[simp, mfld_simps]

Depends on / 依赖: e.toPretrivialization.mk_symm, mk_symm, toPretrivialization
-/
theorem mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    TotalSpace.mk b (e.symm b y) = e.toOpenPartialHomeomorph.symm (b, y) :=
  e.toPretrivialization.mk_symm hb y

@[simp, mfld_simps]
/--
theorem `symm_proj_apply` / 定理 `symm_proj_apply`

English:
theorem symm_proj_apply
  statement: (e : Trivialization F (π F E)) (z : TotalSpace F E)
  proof: e.toPretrivialization.symm_proj_apply z hz

@[simp, mfld_simps]

中文:
定理 symm_proj_apply
  结论: (e : Trivialization F (π F E)) (z : 全空间 F E)
  证明: e.toPretrivialization.symm_proj_apply z hz

@[simp, mfld_simps]

Depends on / 依赖: e.toPretrivialization.symm_proj_apply, symm_proj_apply, toPretrivialization
-/
theorem symm_proj_apply (e : Trivialization F (π F E)) (z : TotalSpace F E)
    (hz : z.proj in e.baseSet) : e.symm z.proj (e z).2 = z.2 :=
  e.toPretrivialization.symm_proj_apply z hz

@[simp, mfld_simps]
/--
theorem `symm_apply_apply_mk` / 定理 `symm_apply_apply_mk`

English:
theorem symm_apply_apply_mk
  given: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : E b)
  proof: e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]

中文:
定理 symm_apply_apply_mk
  条件: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : E b)
  证明: e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]

Depends on / 依赖: e.symm_proj_apply, symm_proj_apply
-/
theorem symm_apply_apply_mk (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : E b) :
    e.symm b (e ⟨b, y⟩).2 = y :=
  e.symm_proj_apply ⟨b, y⟩ hb

@[simp, mfld_simps]
/--
theorem `apply_mk_symm` / 定理 `apply_mk_symm`

English:
theorem apply_mk_symm
  given: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  proof: e.toPretrivialization.apply_mk_symm hb y

中文:
定理 apply_mk_symm
  条件: (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F)
  证明: e.toPretrivialization.apply_mk_symm hb y

Depends on / 依赖: apply_mk_symm, e.toPretrivialization.apply_mk_symm, toPretrivialization
-/
theorem apply_mk_symm (e : Trivialization F (π F E)) {b : B} (hb : b in e.baseSet) (y : F) :
    e ⟨b, e.symm b y⟩ = (b, y) :=
  e.toPretrivialization.apply_mk_symm hb y

/--
theorem `continuousOn_symm` / 定理 `continuousOn_symm`

English:
theorem continuousOn_symm
  given: (e : Trivialization F (π F E))
  proof: by
  have : forall z in e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toOpenPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 in e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toOpenPartialHomeomorph.continuousOn

中文:
定理 continuousOn_symm
  条件: (e : Trivialization F (π F E))
  证明: by
  have : forall z in e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toOpenPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 in e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toOpenPartialHomeomorph.continuousOn

Depends on / 依赖: ContinuousOn, ContinuousOn.congr, TotalSpace, TotalSpace.mk, baseSet, continuousOn_symm, e.baseSet, e.mk_symm, e.symm, e.target_eq, e.toOpenPartialHomeomorph.continuousOn_symm, e.toOpenPartialHomeomorph.symm, mk_symm, target_eq, toOpenPartialHomeomorph
-/
theorem continuousOn_symm (e : Trivialization F (π F E)) :
    ContinuousOn (fun z : B × F => TotalSpace.mk' F z.1 (e.symm z.1 z.2)) (e.baseSet ×ˢ univ) := by
  have : forall z in e.baseSet ×ˢ (univ : Set F),
      TotalSpace.mk z.1 (e.symm z.1 z.2) = e.toOpenPartialHomeomorph.symm z := by
    rintro x ⟨hx : x.1 in e.baseSet, _⟩
    rw [e.mk_symm hx]
  refine ContinuousOn.congr ?_ this
  rw [← e.target_eq]
  exact e.toOpenPartialHomeomorph.continuousOn_symm

end Nonempty

/--
Definition of `transFiberHomeomorph` / `transFiberHomeomorph` 的定义

English:
definition transFiberHomeomorph
  signature: {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
  body: e.toOpenPartialHomeomorph.transHomeomorph (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun

@[simp]

中文:
定义 transFiberHomeomorph
  签名: {F' : 类型} [拓扑空间 F'] (e : Trivialization F proj)
  定义体: e.toOpenPartialHomeomorph.transHomeomorph (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun

@[simp]

Depends on / 依赖: Homeomorph, Homeomorph.refl, baseSet, e.baseSet, e.open_baseSet, e.proj_toFun, e.source_eq, e.toOpenPartialHomeomorph.transHomeomorph, open_baseSet, preimage_preimage, prodCongr, prod_univ, proj_toFun, source_eq, target_eq, toOpenPartialHomeomorph, transHomeomorph
-/
def transFiberHomeomorph {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') : Trivialization F' proj where
  toOpenPartialHomeomorph :=
e.toOpenPartialHomeomorph.transHomeomorph (Homeomorph.refl _).prodCongr h
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := by simp [target_eq, prod_univ, preimage_preimage]
  proj_toFun := e.proj_toFun

@[simp]
/--
theorem `transFiberHomeomorph_apply` / 定理 `transFiberHomeomorph_apply`

English:
theorem transFiberHomeomorph_apply
  statement: {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
  proof: rfl

中文:
定理 transFiberHomeomorph_apply
  结论: {F' : 类型} [拓扑空间 F'] (e : Trivialization F proj)
  证明: rfl
-/
theorem transFiberHomeomorph_apply {F' : Type*} [TopologicalSpace F'] (e : Trivialization F proj)
    (h : F ≃ₜ F') (x : Z) : e.transFiberHomeomorph h x = ((e x).1, h (e x).2) :=
  rfl

/--
Definition of `coordChange` / `coordChange` 的定义

English:
definition coordChange
  signature: (e₁ e₂ : Trivialization F proj) (b : B) (x : F)
  body: (e₂ <| e₁.toOpenPartialHomeomorph.symm (b, x)).2

中文:
定义 coordChange
  签名: (e₁ e₂ : Trivialization F proj) (b : B) (x : F)
  定义体: (e₂ <| e₁.toOpenPartialHomeomorph.symm (b, x)).2

Depends on / 依赖: toOpenPartialHomeomorph, toOpenPartialHomeomorph.symm
-/
def coordChange (e₁ e₂ : Trivialization F proj) (b : B) (x : F) : F :=
  (e₂ <| e₁.toOpenPartialHomeomorph.symm (b, x)).2

/--
theorem `mk_coordChange` / 定理 `mk_coordChange`

English:
theorem mk_coordChange
  statement: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  proof: by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst']; rw [← e₁.coe_fst']; rw [e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]

@[simp]

中文:
定理 mk_coordChange
  结论: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  证明: by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst']; rw [← e₁.coe_fst']; rw [e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]

@[simp]

Depends on / 依赖: Prod.ext, apply_symm_apply, coe_fst, proj_symm_apply
-/
theorem mk_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
    (h₂ : b in e₂.baseSet) (x : F) :
    (b, e₁.coordChange e₂ b x) = e₂ (e₁.toOpenPartialHomeomorph.symm (b, x)) := by
  refine Prod.ext ?_ rfl
  rw [e₂.coe_fst']; rw [← e₁.coe_fst']; rw [e₁.apply_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]
  · rwa [e₁.proj_symm_apply' h₁]

@[simp]
/--
theorem `coordChange_apply_snd` / 定理 `coordChange_apply_snd`

English:
theorem coordChange_apply_snd
  given: (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p in e₁.baseSet)
  proof: by
  rw [coordChange]; rw [e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

@[simp, mfld_simps]

中文:
定理 coordChange_apply_snd
  条件: (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p in e₁.baseSet)
  证明: by
  rw [coordChange]; rw [e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

@[simp, mfld_simps]

Depends on / 依赖: coordChange, mem_source, symm_apply_mk_proj
-/
theorem coordChange_apply_snd (e₁ e₂ : Trivialization F proj) {p : Z} (h : proj p in e₁.baseSet) :
    e₁.coordChange e₂ (proj p) (e₁ p).snd = (e₂ p).snd := by
  rw [coordChange]; rw [e₁.symm_apply_mk_proj (e₁.mem_source.2 h)]

@[simp, mfld_simps]
/--
theorem `coordChange_same_apply` / 定理 `coordChange_same_apply`

English:
theorem coordChange_same_apply
  given: (e : Trivialization F proj) {b : B} (h : b in e.baseSet) (x : F)
  proof: by rw [coordChange, e.apply_symm_apply' h]

中文:
定理 coordChange_same_apply
  条件: (e : Trivialization F proj) {b : B} (h : b in e.baseSet) (x : F)
  证明: by rw [coordChange, e.apply_symm_apply' h]

Depends on / 依赖: apply_symm_apply, coordChange, e.apply_symm_apply
-/
theorem coordChange_same_apply (e : Trivialization F proj) {b : B} (h : b in e.baseSet) (x : F) :
    e.coordChange e b x = x := by rw [coordChange, e.apply_symm_apply' h]

/--
theorem `coordChange_same` / 定理 `coordChange_same`

English:
theorem coordChange_same
  given: (e : Trivialization F proj) {b : B} (h : b in e.baseSet)
  proof: funext e.coordChange_same_apply h

中文:
定理 coordChange_same
  条件: (e : Trivialization F proj) {b : B} (h : b in e.baseSet)
  证明: funext e.coordChange_same_apply h

Depends on / 依赖: coordChange_same_apply, e.coordChange_same_apply
-/
theorem coordChange_same (e : Trivialization F proj) {b : B} (h : b in e.baseSet) :
    e.coordChange e b = id :=
funext e.coordChange_same_apply h

/--
theorem `coordChange_coordChange` / 定理 `coordChange_coordChange`

English:
theorem coordChange_coordChange
  statement: (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  proof: by
  rw [coordChange]; rw [e₁.mk_coordChange _ h₁ h₂]; rw [← e₂.coe_coe]; rw [e₂.left_inv]; rw [coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

中文:
定理 coordChange_coordChange
  结论: (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  证明: by
  rw [coordChange]; rw [e₁.mk_coordChange _ h₁ h₂]; rw [← e₂.coe_coe]; rw [e₂.left_inv]; rw [coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

Depends on / 依赖: coe_coe, coordChange, left_inv, mem_source, mk_coordChange, proj_symm_apply
-/
theorem coordChange_coordChange (e₁ e₂ e₃ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
    (h₂ : b in e₂.baseSet) (x : F) :
    e₂.coordChange e₃ b (e₁.coordChange e₂ b x) = e₁.coordChange e₃ b x := by
  rw [coordChange]; rw [e₁.mk_coordChange _ h₁ h₂]; rw [← e₂.coe_coe]; rw [e₂.left_inv]; rw [coordChange]
  rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

/--
theorem `continuous_coordChange` / 定理 `continuous_coordChange`

English:
theorem continuous_coordChange
  statement: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  proof: by
  refine continuous_snd.comp (e₂.toOpenPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · fun_prop
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

中文:
定理 continuous_coordChange
  结论: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  证明: by
  refine continuous_snd.comp (e₂.toOpenPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · fun_prop
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

Depends on / 依赖: comp_continuous, continuousOn, continuousOn_symm, continuous_snd, continuous_snd.comp, fun_prop, mem_source, mem_target, proj_symm_apply, toOpenPartialHomeomorph, toOpenPartialHomeomorph.continuousOn.comp_continuous, toOpenPartialHomeomorph.continuousOn_symm.comp_continuous
-/
theorem continuous_coordChange (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
    (h₂ : b in e₂.baseSet) : Continuous (e₁.coordChange e₂ b) := by
  refine continuous_snd.comp (e₂.toOpenPartialHomeomorph.continuousOn.comp_continuous
    (e₁.toOpenPartialHomeomorph.continuousOn_symm.comp_continuous ?_ ?_) ?_)
  · fun_prop
  · exact fun x => e₁.mem_target.2 h₁
  · intro x
    rwa [e₂.mem_source, e₁.proj_symm_apply' h₁]

/--
Definition of `coordChangeHomeomorph` / `coordChangeHomeomorph` 的定义

English:
definition coordChangeHomeomorph
  signature: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  body: e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.

中文:
定义 coordChangeHomeomorph
  签名: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  定义体: e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.
-/
protected def coordChangeHomeomorph (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
    (h₂ : b in e₂.baseSet) : F ≃ₜ F where
  toFun := e₁.coordChange e₂ b
  invFun := e₂.coordChange e₁ b
  left_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  right_inv x := by simp only [*, coordChange_coordChange, coordChange_same_apply]
  continuous_toFun := e₁.continuous_coordChange e₂ h₁ h₂
  continuous_invFun := e₂.continuous_coordChange e₁ h₂ h₁

@[simp]
/--
theorem `coordChangeHomeomorph_coe` / 定理 `coordChangeHomeomorph_coe`

English:
theorem coordChangeHomeomorph_coe
  statement: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  proof: rfl

中文:
定理 coordChangeHomeomorph_coe
  结论: (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
  证明: rfl
-/
theorem coordChangeHomeomorph_coe (e₁ e₂ : Trivialization F proj) {b : B} (h₁ : b in e₁.baseSet)
    (h₂ : b in e₂.baseSet) : ⇑(e₁.coordChangeHomeomorph e₂ h₁ h₂) = e₁.coordChange e₂ b :=
  rfl

/--
theorem `isImage_preimage_prod` / 定理 `isImage_preimage_prod`

English:
theorem isImage_preimage_prod
  given: (e : Trivialization F proj) (s : Set B)
  proof: fun x hx => by simp [hx]

中文:
定理 isImage_preimage_prod
  条件: (e : Trivialization F proj) (s : 集合 B)
  证明: fun x hx => by simp [hx]
-/
theorem isImage_preimage_prod (e : Trivialization F proj) (s : Set B) :
    e.toOpenPartialHomeomorph.IsImage (proj ⁻¹' s) (s ×ˢ univ) := fun x hx => by simp [hx]

/--
Definition of `restrOpen` / `restrOpen` 的定义

English:
definition restrOpen
  signature: (e : Trivialization F proj) (s : Set B) (hs : IsOpen s)
  body: ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet inter s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1

中文:
定义 restrOpen
  签名: (e : Trivialization F proj) (s : 集合 B) (hs : 是开集 s)
  定义体: ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet inter s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1
-/
protected def restrOpen (e : Trivialization F proj) (s : Set B) (hs : IsOpen s) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    ((e.isImage_preimage_prod s).symm.restr (IsOpen.inter e.open_target (hs.prod isOpen_univ))).symm
  baseSet := e.baseSet inter s
  open_baseSet := IsOpen.inter e.open_baseSet hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p hp := e.proj_toFun p hp.1

/-- The restriction of a trivialization to a subset of the base. -/
@[simps! apply source target baseSet]
/--
Definition of `restrictPreimage'` / `restrictPreimage'` 的定义

English:
definition restrictPreimage'
  signature: (e : Trivialization F proj) (s : Set B)
  body: e.toPretrivialization.restrictPreimage' s
open_source := e.open_source.preimage by fun_prop
continuousOn_toFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_iff.mpr
    (e.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ => id).congr
      fun z hz => by ext; exacts [

中文:
定义 restrictPreimage'
  签名: (e : Trivialization F proj) (s : 集合 B)
  定义体: e.toPretrivialization.restrictPreimage' s
open_source := e.open_source.preimage by fun_prop
continuousOn_toFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_iff.mpr
    (e.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ => id).congr
      fun z hz => by ext; exacts [

Depends on / 依赖: e.toPretrivialization.restrictPreimage, restrictPreimage, toPretrivialization
-/
noncomputable def restrictPreimage' (e : Trivialization F proj) (s : Set B)
    [Nonempty (s -> F -> proj ⁻¹' s)] : Trivialization F (s.restrictPreimage proj) where
  __ := e.toPretrivialization.restrictPreimage' s
open_source := e.open_source.preimage by fun_prop
continuousOn_toFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_iff.mpr
    (e.continuousOn_toFun.comp continuous_subtype_val.continuousOn fun _ => id).congr
      fun z hz => by ext; exacts [(e.proj_toFun _ hz).symm, rfl]
continuousOn_invFun := Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    (e.continuousOn_invFun.comp (continuous_subtype_val.prodMap continuous_id).continuousOn
      fun _ => id).congr fun x hx => congr_arg Subtype.val (dif_pos hx)

/-- The restriction of a trivialization to a set with nonempty intersection with the base set. -/
@[simps! apply source target baseSet]
/--
Definition of `restrictPreimage` / `restrictPreimage` 的定义

English:
definition restrictPreimage
  signature: (e : Trivialization F proj) {s : Set B}
  body: have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

中文:
定义 restrictPreimage
  签名: (e : Trivialization F proj) {s : 集合 B}
  定义体: have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

Depends on / 依赖: Nonempty, Nonempty.some, Set.mem_preimage.mpr, e.invFun, e.proj_symm_apply, e.restrictPreimage, invFun, mem_preimage, proj_symm_apply, restrictPreimage
-/
noncomputable def restrictPreimage (e : Trivialization F proj) {s : Set B}
    (hs : (s inter e.baseSet).Nonempty) : Trivialization F (s.restrictPreimage proj) :=
have : Nonempty (F -> proj ⁻¹' s) := .intro fun f => Nonempty.some have ⟨z, hzs, hzb⟩ := hs
⟨⟨e.invFun ⟨z, f⟩, Set.mem_preimage.mpr (e.proj_symm_apply' hzb).symm ▸ hzs⟩⟩
  e.restrictPreimage' s

/-- Extend the total space of a trivialization from the preimage of a set to the whole space. -/
@[simps! symm_apply source target baseSet]
/--
Definition of `domExtend` / `domExtend` 的定义

English:
definition domExtend
  signature: {s : Set B} (hps : IsOpen (proj ⁻¹' s))
  body: e.toPretrivialization.domExtend
  open_source := hps.isOpenMap_subtype_val _ e.open_source
continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr by
    convert! e.continuousOn_toFun
    ext1 ⟨x, (hx : proj x in s)⟩
    simpa [Pretrivialization.domExtend] using! dif_pos hx
c

中文:
定义 domExtend
  签名: {s : 集合 B} (hps : 是开集 (proj ⁻¹' s))
  定义体: e.toPretrivialization.domExtend
  open_source := hps.isOpenMap_subtype_val _ e.open_source
continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr by
    convert! e.continuousOn_toFun
    ext1 ⟨x, (hx : proj x in s)⟩
    simpa [Pretrivialization.domExtend] using! dif_pos hx
c

Depends on / 依赖: domExtend, e.toPretrivialization.domExtend, toPretrivialization
-/
noncomputable def domExtend {s : Set B} (hps : IsOpen (proj ⁻¹' s))
    (e : Trivialization F fun z : proj ⁻¹' s => proj z) [Nonempty (Z -> F)] :
    Trivialization F proj where
  __ := e.toPretrivialization.domExtend
  open_source := hps.isOpenMap_subtype_val _ e.open_source
continuousOn_toFun := Topology.IsInducing.subtypeVal.continuousOn_image_iff.mpr by
    convert! e.continuousOn_toFun
    ext1 ⟨x, (hx : proj x in s)⟩
    simpa [Pretrivialization.domExtend] using! dif_pos hx
continuousOn_invFun := continuous_subtype_val.comp_continuousOn by
    convert! e.continuousOn_invFun

/-- Extend the base of a trivialization from a set to the whole space. -/
@[simps! apply source target baseSet]
/--
Definition of `codExtend'` / `codExtend'` 的定义

English:
definition codExtend'
  signature: {s : Set B} (hs : IsOpen s) {proj : Z -> s} (e : Trivialization F proj)
  body: e.toPretrivialization.codExtend' hs
  open_source := e.open_source
  continuousOn_toFun :=
    (continuous_subtype_val.prodMap continuous_id).comp_continuousOn e.continuousOn_toFun
continuousOn_invFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_image_iff.2 by
    convert! e.continuo

中文:
定义 codExtend'
  签名: {s : 集合 B} (hs : 是开集 s) {proj : Z -> s} (e : Trivialization F proj)
  定义体: e.toPretrivialization.codExtend' hs
  open_source := e.open_source
  continuousOn_toFun :=
    (continuous_subtype_val.prodMap continuous_id).comp_continuousOn e.continuousOn_toFun
continuousOn_invFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_image_iff.2 by
    convert! e.continuo

Depends on / 依赖: codExtend, e.toPretrivialization.codExtend, toPretrivialization
-/
noncomputable def codExtend' {s : Set B} (hs : IsOpen s) {proj : Z -> s} (e : Trivialization F proj)
    [Nonempty (B -> F -> Z)] : Trivialization F (Subtype.val ∘ proj) where
  __ := e.toPretrivialization.codExtend' hs
  open_source := e.open_source
  continuousOn_toFun :=
    (continuous_subtype_val.prodMap continuous_id).comp_continuousOn e.continuousOn_toFun
continuousOn_invFun := (Topology.IsInducing.subtypeVal.prodMap .id).continuousOn_image_iff.2 by
    convert! e.continuousOn_invFun; ext; simp [Pretrivialization.codExtend']; rfl

/-- Extend the base of a pretrivialization from a nonempty set to the whole space. -/
@[simps! apply source target baseSet]
/--
Definition of `codExtend` / `codExtend` 的定义

English:
definition codExtend
  signature: {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z -> s}
  body: have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

中文:
定义 codExtend
  签名: {s : 集合 B} (hs : 是开集 s) (nonempty : s.非空) {proj : Z -> s}
  定义体: have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

Depends on / 依赖: Nonempty, codExtend, e.codExtend, e.invFun, invFun, nonempty, nonempty.some_mem, some_mem
-/
noncomputable def codExtend {s : Set B} (hs : IsOpen s) (nonempty : s.Nonempty) {proj : Z -> s}
    (e : Trivialization F proj) : Trivialization F (Subtype.val ∘ proj) :=
  have : Nonempty (F -> Z) := .intro fun f => e.invFun (⟨_, nonempty.some_mem⟩, f)
  e.codExtend' hs

section Piecewise

/--
theorem `frontier_preimage` / 定理 `frontier_preimage`

English:
theorem frontier_preimage
  given: (e : Trivialization F proj) (s : Set B)
  proof: by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq]; rw [frontier_prod_univ_eq]; rw [(e.isImage_preimage_prod _).preimage_eq]; rw [e.source_eq]; rw [preimage_inter]

中文:
定理 frontier_preimage
  条件: (e : Trivialization F proj) (s : 集合 B)
  证明: by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq]; rw [frontier_prod_univ_eq]; rw [(e.isImage_preimage_prod _).preimage_eq]; rw [e.source_eq]; rw [preimage_inter]

Depends on / 依赖: e.isImage_preimage_prod, e.source_eq, frontier, frontier.preimage_eq, frontier_prod_univ_eq, isImage_preimage_prod, preimage_eq, preimage_inter, source_eq
-/
theorem frontier_preimage (e : Trivialization F proj) (s : Set B) :
    e.source inter frontier (proj ⁻¹' s) = proj ⁻¹' (e.baseSet inter frontier s) := by
  rw [← (e.isImage_preimage_prod s).frontier.preimage_eq]; rw [frontier_prod_univ_eq]; rw [(e.isImage_preimage_prod _).preimage_eq]; rw [e.source_eq]; rw [preimage_inter]

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `piecewise` / `piecewise` 的定义

English:
definition piecewise
  signature: (e e' : Trivialization F proj) (s : Set B)
  body: e.toOpenPartialHomeomorph.piecewise e'.toOpenPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet :

中文:
定义 piecewise
  签名: (e e' : Trivialization F proj) (s : 集合 B)
  定义体: e.toOpenPartialHomeomorph.piecewise e'.toOpenPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet :

Depends on / 依赖: baseSet, e.baseSet, e.frontier_preimage, e.isImage_preimage_prod, e.open_baseSet.ite, e.toOpenPartialHomeomorph.piecewise, frontier_preimage, isImage_preimage_prod, open_baseSet, piecewise, prod_univ, proj_toFun, s.ite, source_eq, target_eq, toOpenPartialHomeomorph
-/
noncomputable def piecewise (e e' : Trivialization F proj) (s : Set B)
    (Hs : e.baseSet inter frontier s = e'.baseSet inter frontier s)
    (Heq : EqOn e e' <| proj ⁻¹' (e.baseSet inter frontier s)) : Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.piecewise e'.toOpenPartialHomeomorph (proj ⁻¹' s) (s ×ˢ univ)
      (e.isImage_preimage_prod s) (e'.isImage_preimage_prod s)
      (by rw [e.frontier_preimage, e'.frontier_preimage, Hs]) (by rwa [e.frontier_preimage])
  baseSet := s.ite e.baseSet e'.baseSet
  open_baseSet := e.open_baseSet.ite e'.open_baseSet Hs
  source_eq := by simp [source_eq]
  target_eq := by simp [target_eq, prod_univ]
  proj_toFun p := by
    rintro (⟨he, hs⟩ | ⟨he, hs⟩) <;> simp [*]

/--
Definition of `piecewiseLeOfEq` / `piecewiseLeOfEq` 的定义

English:
definition piecewiseLeOfEq
  signature: [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
  body: e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
fun p hp => Heq p frontier_Iic_subset _ hp.2

中文:
定义 piecewiseLeOfEq
  签名: [线性序 B] [Order拓扑 B] (e e' : Trivialization F proj)
  定义体: e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
fun p hp => Heq p frontier_Iic_subset _ hp.2

Depends on / 依赖: Set.ext, and_congr_left_iff, e.piecewise, frontier_Iic_subset, mem_singleton_iff, piecewise
-/
noncomputable def piecewiseLeOfEq [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a in e.baseSet) (He' : a in e'.baseSet) (Heq : forall p, proj p = a -> e p = e' p) :
    Trivialization F proj :=
  e.piecewise e' (Iic a)
    (Set.ext fun x => and_congr_left_iff.2 fun hx => by
      obtain rfl : x = a := mem_singleton_iff.1 (frontier_Iic_subset _ hx)
      simp [He, He'])
fun p hp => Heq p frontier_Iic_subset _ hp.2

/--
Definition of `piecewiseLe` / `piecewiseLe` 的定义

English:
definition piecewiseLe
  signature: [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
  body: e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' by
    rintro p rfl
    ext1
    · simp [*]
    · simp [*]

中文:
定义 piecewiseLe
  签名: [线性序 B] [Order拓扑 B] (e e' : Trivialization F proj)
  定义体: e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' by
    rintro p rfl
    ext1
    · simp [*]
    · simp [*]

Depends on / 依赖: coordChangeHomeomorph, e.piecewiseLeOfEq, piecewiseLeOfEq, transFiberHomeomorph
-/
noncomputable def piecewiseLe [LinearOrder B] [OrderTopology B] (e e' : Trivialization F proj)
    (a : B) (He : a in e.baseSet) (He' : a in e'.baseSet) : Trivialization F proj :=
e.piecewiseLeOfEq (e'.transFiberHomeomorph (e'.coordChangeHomeomorph e He' He)) a He He' by
    rintro p rfl
    ext1
    · simp [*]
    · simp [*]

open scoped Classical in
/--
Definition of `disjointUnion` / `disjointUnion` 的定义

English:
definition disjointUnion
  signature: (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet)
  body: e.toOpenPartialHomeomorph.disjointUnion e'.toOpenPartialHomeomorph
      (by
        rw [e.source_eq]; rw [e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq]; rw [e'.target_eq]; rw [disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet :

中文:
定义 disjointUnion
  签名: (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet)
  定义体: e.toOpenPartialHomeomorph.disjointUnion e'.toOpenPartialHomeomorph
      (by
        rw [e.source_eq]; rw [e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq]; rw [e'.target_eq]; rw [disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet :

Depends on / 依赖: H.le_bot, H.preimage, IsOpen, IsOpen.union, baseSet, disjointUnion, disjoint_iff_inf_le, e.baseSet, e.open_baseSet, e.source_eq, e.target_eq, e.toOpenPartialHomeomorph.disjointUnion, le_bot, open_baseSet, preimage, proj_toFun, source_eq, target_eq, toOpenPartialHomeomorph, union_prod
-/
noncomputable def disjointUnion (e e' : Trivialization F proj) (H : Disjoint e.baseSet e'.baseSet) :
    Trivialization F proj where
  toOpenPartialHomeomorph :=
    e.toOpenPartialHomeomorph.disjointUnion e'.toOpenPartialHomeomorph
      (by
        rw [e.source_eq]; rw [e'.source_eq]
        exact H.preimage _)
      (by
        rw [e.target_eq]; rw [e'.target_eq]; rw [disjoint_iff_inf_le]
        intro x hx
        exact H.le_bot ⟨hx.1.1, hx.2.1⟩)
  baseSet := e.baseSet union e'.baseSet
  open_baseSet := IsOpen.union e.open_baseSet e'.open_baseSet
  source_eq := congr_arg₂ (· union ·) e.source_eq e'.source_eq
  target_eq := (congr_arg₂ (· union ·) e.target_eq e'.target_eq).trans union_prod.symm
  proj_toFun := by
    rintro p (hp | hp')
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_mem]; rw [e.coe_fst] <;> exact hp
    · change (e.source.piecewise e e' p).1 = proj p
      rw [piecewise_eq_of_notMem]; rw [e'.coe_fst hp']
      simp only [source_eq] at hp' ⊢
      exact fun h => H.le_bot ⟨h, hp'⟩

end Piecewise

section Lift

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (T : Trivialization F proj) (z : Z) (b : B)
  body: T.invFun (b, (T z).2)

中文:
定义 lift
  签名: (T : Trivialization F proj) (z : Z) (b : B)
  定义体: T.invFun (b, (T z).2)

Depends on / 依赖: T.invFun, invFun
-/
def lift (T : Trivialization F proj) (z : Z) (b : B) : Z := T.invFun (b, (T z).2)

variable {T : Trivialization F proj} {z : Z} {b : B}

@[simp]
/--
theorem `lift_self` / 定理 `lift_self`

English:
theorem lift_self
  given: (he : proj z in T.baseSet)
  statement: T.lift z (proj z) = z
  proof: symm_apply_mk_proj _ T.mem_source.2 he

中文:
定理 lift_self
  条件: (he : proj z in T.baseSet)
  结论: T.lift z (proj z) = z
  证明: symm_apply_mk_proj _ T.mem_source.2 he

Depends on / 依赖: T.mem_source, mem_source, symm_apply_mk_proj
-/
theorem lift_self (he : proj z in T.baseSet) : T.lift z (proj z) = z :=
symm_apply_mk_proj _ T.mem_source.2 he

/--
theorem `proj_lift` / 定理 `proj_lift`

English:
theorem proj_lift
  given: (hx : b in T.baseSet)
  statement: proj (T.lift z b) = b
  proof: T.proj_symm_apply T.mem_target.2 hx

中文:
定理 proj_lift
  条件: (hx : b in T.baseSet)
  结论: proj (T.lift z b) = b
  证明: T.proj_symm_apply T.mem_target.2 hx

Depends on / 依赖: T.mem_target, T.proj_symm_apply, mem_target, proj_symm_apply
-/
theorem proj_lift (hx : b in T.baseSet) : proj (T.lift z b) = b :=
T.proj_symm_apply T.mem_target.2 hx

/--
Definition of `liftCM` / `liftCM` 的定义

English:
definition liftCM
  signature: (T : Trivialization F proj)
  body: ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    refine .prodMk (by fun_prop) (.snd ?_)
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp

中文:
定义 liftCM
  签名: (T : Trivialization F proj)
  定义体: ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    refine .prodMk (by fun_prop) (.snd ?_)
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp

Depends on / 依赖: T.lift, T.map_target, map_target, mem_target
-/
def liftCM (T : Trivialization F proj) : C(T.source × T.baseSet, T.source) where
  toFun ex := ⟨T.lift ex.1 ex.2, T.map_target (by simp [mem_target])⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine T.continuousOn_invFun.comp_continuous ?_ (by simp [mem_target])
    refine .prodMk (by fun_prop) (.snd ?_)
    exact T.continuousOn_toFun.comp_continuous (by fun_prop) (by simp)

variable {ι : Type*} [TopologicalSpace ι] [LocallyCompactPair ι T.baseSet]
  {γ : C(ι, T.baseSet)} {i : ι} {e : T.source}

/--
Definition of `clift` / `clift` 的定义

English:
definition clift
  signature: (T : Trivialization F proj) [LocallyCompactPair ι T.baseSet]
  body: by
  let Ψ : C((T.source × C(ι, T.baseSet)) × ι, C(ι, T.baseSet) × ι) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
refine ContinuousMap.curry T.liftCM.comp ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

@[simp]

中文:
定义 clift
  签名: (T : Trivialization F proj) [LocallyCompactPair ι T.baseSet]
  定义体: by
  let Ψ : C((T.source × C(ι, T.baseSet)) × ι, C(ι, T.baseSet) × ι) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
refine ContinuousMap.curry T.liftCM.comp ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

@[simp]

Depends on / 依赖: ContinuousEval, ContinuousEval.continuous_eval.comp, ContinuousMap, ContinuousMap.curry, T.baseSet, T.liftCM.comp, T.source, baseSet, continuous, continuous_eval, fun_prop, liftCM, source
-/
def clift (T : Trivialization F proj) [LocallyCompactPair ι T.baseSet] :
    C(T.source × C(ι, T.baseSet), C(ι, T.source)) := by
  let Ψ : C((T.source × C(ι, T.baseSet)) × ι, C(ι, T.baseSet) × ι) :=
    ⟨fun eγt => (eγt.1.2, eγt.2), by fun_prop⟩
refine ContinuousMap.curry T.liftCM.comp ⟨fun eγt => ⟨eγt.1.1, eγt.1.2 eγt.2⟩, ?_⟩
  simpa using ⟨by fun_prop, ContinuousEval.continuous_eval.comp Ψ.continuous⟩

@[simp]
/--
theorem `clift_self` / 定理 `clift_self`

English:
theorem clift_self
  given: (h : proj e.1 = γ i)
  proof: by
  have : proj e in T.baseSet := by simp [h]
  simp [clift, liftCM, ← h, lift_self, this]

中文:
定理 clift_self
  条件: (h : proj e.1 = γ i)
  证明: by
  have : proj e in T.baseSet := by simp [h]
  simp [clift, liftCM, ← h, lift_self, this]

Depends on / 依赖: T.baseSet, baseSet, liftCM, lift_self
-/
theorem clift_self (h : proj e.1 = γ i) :
    T.clift (e, γ) i = e := by
  have : proj e in T.baseSet := by simp [h]
  simp [clift, liftCM, ← h, lift_self, this]

/--
theorem `proj_clift` / 定理 `proj_clift`

English:
theorem proj_clift
  statement: proj (T.clift (e, γ) i) = γ i
  proof: by
  simp [clift, liftCM, proj_lift]

中文:
定理 proj_clift
  结论: proj (T.clift (e, γ) i) = γ i
  证明: by
  simp [clift, liftCM, proj_lift]

Depends on / 依赖: liftCM, proj_lift
-/
theorem proj_clift : proj (T.clift (e, γ) i) = γ i := by
  simp [clift, liftCM, proj_lift]

end Lift

end Bundle.Trivialization
