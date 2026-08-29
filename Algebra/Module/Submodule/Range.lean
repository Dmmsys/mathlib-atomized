/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Data.Set.Finite.Range

/-!
# Range of linear maps

The range `LinearMap.range` of a (semi)linear map `f : M → M₂` is a submodule of `M₂`.

More specifically, `LinearMap.range` applies to any `SemilinearMapClass` over a `RingHomSurjective`
ring homomorphism.

Note that this also means that dot notation (i.e. `f.range` for a linear map `f`) does not work.

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module, range
-/

@[expose] public section

open Function

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R ->+* R₂} {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

section

/--
Definition of `range` / `range` 的定义

English:
definition range
  signature: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  body: (map f ⊤).copy (Set.range f) Set.image_univ.symm

中文:
定义 range
  签名: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  定义体: (map f ⊤).copy (Set.range f) Set.image_univ.symm

Depends on / 依赖: Set.image_univ.symm, Set.range, image_univ
-/
def range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=
  (map f ⊤).copy (Set.range f) Set.image_univ.symm

/--
theorem `coe_range` / 定理 `coe_range`

English:
theorem coe_range
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  statement: (range f : Set M₂) = Set.range f
  proof: rfl

中文:
定理 coe_range
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  结论: (range f : 集合 M₂) = 集合.range f
  证明: rfl
-/
theorem coe_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : (range f : Set M₂) = Set.range f :=
  rfl

/--
theorem `range_toAddSubmonoid` / 定理 `range_toAddSubmonoid`

English:
theorem range_toAddSubmonoid
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  proof: rfl

@[simp]

中文:
定理 range_toAddSubmonoid
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  证明: rfl

@[simp]
-/
theorem range_toAddSubmonoid [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubmonoid = AddMonoidHom.mrange f :=
  rfl

@[simp]
/--
theorem `mem_range` / 定理 `mem_range`

English:
theorem mem_range
  given: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {x}
  statement: x in range f ↔ exists y, f y = x
  proof: Iff.rfl

中文:
定理 mem_range
  条件: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {x}
  结论: x in range f ↔ 存在 y, f y = x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {x} : x in range f ↔ exists y, f y = x :=
  Iff.rfl

/--
theorem `range_eq_map` / 定理 `range_eq_map`

English:
theorem range_eq_map
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  statement: range f = map f ⊤
  proof: by
  ext
  simp

中文:
定理 range_eq_map
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  结论: range f = map f ⊤
  证明: by
  ext
  simp
-/
theorem range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : range f = map f ⊤ := by
  ext
  simp

/--
theorem `mem_range_self` / 定理 `mem_range_self`

English:
theorem mem_range_self
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (x : M)
  statement: f x in range f
  proof: ⟨x, rfl⟩

@[simp]

中文:
定理 mem_range_self
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (x : M)
  结论: f x in range f
  证明: ⟨x, rfl⟩

@[simp]
-/
theorem mem_range_self [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f :=
  ⟨x, rfl⟩

@[simp]
/--
theorem `range_id` / 定理 `range_id`

English:
theorem range_id
  statement: range (LinearMap.id : M ->ₗ[R] M) = ⊤
  proof: SetLike.coe_injective Set.range_id

中文:
定理 range_id
  结论: range (线性映射.id : M ->ₗ[R] M) = ⊤
  证明: SetLike.coe_injective Set.range_id

Depends on / 依赖: Set.range_id, SetLike, SetLike.coe_injective, coe_injective, range_id
-/
theorem range_id : range (LinearMap.id : M ->ₗ[R] M) = ⊤ :=
  SetLike.coe_injective Set.range_id

/--
theorem `range_comp` / 定理 `range_comp`

English:
theorem range_comp
  statement: [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
  proof: SetLike.coe_injective (Set.range_comp g f)

中文:
定理 range_comp
  结论: [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
  证明: SetLike.coe_injective (Set.range_comp g f)

Depends on / 依赖: Set.range_comp, SetLike, SetLike.coe_injective, coe_injective, range_comp
-/
theorem range_comp [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃]
    (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g.comp f : M ->ₛₗ[τ₁₃] M₃) = map g (range f) :=
  SetLike.coe_injective (Set.range_comp g f)

/--
theorem `range_comp_le_range` / 定理 `range_comp_le_range`

English:
theorem range_comp_le_range
  statement: [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂)
  proof: SetLike.coe_mono (Set.range_comp_subset_range f g)

中文:
定理 range_comp_le_range
  结论: [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂)
  证明: SetLike.coe_mono (Set.range_comp_subset_range f g)

Depends on / 依赖: Set.range_comp_subset_range, SetLike, SetLike.coe_mono, coe_mono, range_comp_subset_range
-/
theorem range_comp_le_range [RingHomSurjective τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂)
    (g : M₂ ->ₛₗ[τ₂₃] M₃) : range (g.comp f : M ->ₛₗ[τ₁₃] M₃) <= range g :=
  SetLike.coe_mono (Set.range_comp_subset_range f g)

/--
theorem `range_eq_top` / 定理 `range_eq_top`

English:
theorem range_eq_top
  given: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [top_coe]; rw [Set.range_eq_univ]

中文:
定理 range_eq_top
  条件: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [top_coe]; rw [Set.range_eq_univ]

Depends on / 依赖: Set.range_eq_univ, SetLike, SetLike.ext, _iff, coe_range, range_eq_univ, top_coe
-/
theorem range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} :
    range f = ⊤ ↔ Surjective f := by
  rw [SetLike.ext'_iff]; rw [coe_range]; rw [top_coe]; rw [Set.range_eq_univ]

/--
theorem `range_eq_top_of_surjective` / 定理 `range_eq_top_of_surjective`

English:
theorem range_eq_top_of_surjective
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f)
  proof: range_eq_top.2 hf

中文:
定理 range_eq_top_of_surjective
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : 满射 f)
  证明: range_eq_top.2 hf

Depends on / 依赖: range_eq_top
-/
theorem range_eq_top_of_surjective [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) :
    range f = ⊤ := range_eq_top.2 hf

/--
theorem `range_add_le` / 定理 `range_add_le`

English:
theorem range_add_le
  given: [RingHomSurjective τ₁₂] (f g : M ->ₛₗ[τ₁₂] M₂)
  proof: by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [mem_range, exists_apply_eq_apply]

中文:
定理 range_add_le
  条件: [RingHomSurjective τ₁₂] (f g : M ->ₛₗ[τ₁₂] M₂)
  证明: by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [mem_range, exists_apply_eq_apply]

Depends on / 依赖: add_mem_sup, all_goals, exists_apply_eq_apply, mem_range
-/
theorem range_add_le [RingHomSurjective τ₁₂] (f g : M ->ₛₗ[τ₁₂] M₂) :
    range (f + g) <= range f ⊔ range g := by
  rintro - ⟨_, rfl⟩
  apply add_mem_sup
  all_goals simp only [mem_range, exists_apply_eq_apply]

/--
theorem `range_le_iff_comap` / 定理 `range_le_iff_comap`

English:
theorem range_le_iff_comap
  given: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂}
  proof: by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

中文:
定理 range_le_iff_comap
  条件: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R₂ M₂}
  证明: by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

Depends on / 依赖: eq_top_iff, map_le_iff_le_comap, range_eq_map
-/
theorem range_le_iff_comap [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} :
    range f <= p ↔ comap f p = ⊤ := by rw [range_eq_map, map_le_iff_le_comap, eq_top_iff]

/--
theorem `map_le_range` / 定理 `map_le_range`

English:
theorem map_le_range
  given: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  proof: SetLike.coe_mono (Set.image_subset_range f p)

@[simp]

中文:
定理 map_le_range
  条件: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R M}
  证明: SetLike.coe_mono (Set.image_subset_range f p)

@[simp]

Depends on / 依赖: Set.image_subset_range, SetLike, SetLike.coe_mono, coe_mono, image_subset_range
-/
theorem map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    map f p <= range f :=
  SetLike.coe_mono (Set.image_subset_range f p)

@[simp]
/--
theorem `range_neg` / 定理 `range_neg`

English:
theorem range_neg
  statement: {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
  proof: by
  change range ((-LinearMap.id : M₂ ->ₗ[R₂] M₂).comp f) = _
  rw [range_comp]; rw [Submodule.map_neg]; rw [Submodule.map_id]

中文:
定理 range_neg
  结论: {R : 类型} {R₂ : 类型} {M : 类型} {M₂ : 类型} [半环 R] [环 R₂]
  证明: by
  change range ((-LinearMap.id : M₂ ->ₗ[R₂] M₂).comp f) = _
  rw [range_comp]; rw [Submodule.map_neg]; rw [Submodule.map_id]

Depends on / 依赖: LinearMap, LinearMap.id, Submodule, Submodule.map_id, Submodule.map_neg, map_id, map_neg, range_comp
-/
theorem range_neg {R : Type*} {R₂ : Type*} {M : Type*} {M₂ : Type*} [Semiring R] [Ring R₂]
    [AddCommMonoid M] [AddCommGroup M₂] [Module R M] [Module R₂ M₂] {τ₁₂ : R ->+* R₂}
    [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : LinearMap.range (-f) = LinearMap.range f := by
  change range ((-LinearMap.id : M₂ ->ₗ[R₂] M₂).comp f) = _
  rw [range_comp]; rw [Submodule.map_neg]; rw [Submodule.map_id]

/--
lemma `range_domRestrict` / 引理 `range_domRestrict`

English:
lemma range_domRestrict
  given: [RingHomSurjective τ₁₂] (K : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂)
  proof: by ext; simp

中文:
引理 range_domRestrict
  条件: [RingHomSurjective τ₁₂] (K : 子模 R M) (f : M ->ₛₗ[τ₁₂] M₂)
  证明: by ext; simp
-/
@[simp] lemma range_domRestrict [RingHomSurjective τ₁₂] (K : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂) :
    range (domRestrict f K) = K.map f := by ext; simp

/--
lemma `range_domRestrict_le_range` / 引理 `range_domRestrict_le_range`

English:
lemma range_domRestrict_le_range
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (S : Submodule R M)
  proof: by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]

中文:
引理 range_domRestrict_le_range
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (S : 子模 R M)
  证明: by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, mem_range_self
-/
lemma range_domRestrict_le_range [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (S : Submodule R M) :
    LinearMap.range (f.domRestrict S) <= LinearMap.range f := by
  rintro x ⟨⟨y, hy⟩, rfl⟩
  exact LinearMap.mem_range_self f y

@[simp]
/--
theorem `_root_.AddMonoidHom.coe_toIntLinearMap_range` / 定理 `_root_.AddMonoidHom.coe_toIntLinearMap_range`

English:
theorem _root_.AddMonoidHom.coe_toIntLinearMap_range
  statement: {M M₂ : Type*} [AddCommGroup M]
  proof: rfl

中文:
定理 _root_.加法幺半群态射.coe_to整数LinearMap_range
  结论: {M M₂ : 类型} [加法交换群 M]
  证明: rfl
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_range {M M₂ : Type*} [AddCommGroup M]
    [AddCommGroup M₂] (f : M ->+ M₂) :
    LinearMap.range f.toIntLinearMap = AddSubgroup.toIntSubmodule f.range := rfl

/--
lemma `_root_.Submodule.map_comap_eq_of_le` / 引理 `_root_.Submodule.map_comap_eq_of_le`

English:
lemma _root_.Submodule.map_comap_eq_of_le
  statement: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  proof: SetLike.coe_injective Set.image_preimage_eq_of_subset h

中文:
引理 _root_.子模.map_comap_eq_of_le
  结论: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  证明: SetLike.coe_injective Set.image_preimage_eq_of_subset h

Depends on / 依赖: Set.image_preimage_eq_of_subset, SetLike, SetLike.coe_injective, coe_injective, image_preimage_eq_of_subset
-/
lemma _root_.Submodule.map_comap_eq_of_le [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
    {p : Submodule R₂ M₂} (h : p <= LinearMap.range f) : (p.comap f).map f = p :=
SetLike.coe_injective Set.image_preimage_eq_of_subset h

/--
lemma `range_restrictScalars` / 引理 `range_restrictScalars`

English:
lemma range_restrictScalars
  statement: [SMul R R₂] [Module R₂ M] [Module R M₂] [CompatibleSMul M M₂ R R₂]
  proof: rfl

中文:
引理 range_restrictScalars
  结论: [标量乘法 R R₂] [模 R₂ M] [模 R M₂] [余mpatibleSMul M M₂ R R₂]
  证明: rfl
-/
lemma range_restrictScalars [SMul R R₂] [Module R₂ M] [Module R M₂] [CompatibleSMul M M₂ R R₂]
    [IsScalarTower R R₂ M₂] (f : M ->ₗ[R₂] M₂) :
    LinearMap.range (f.restrictScalars R) = (LinearMap.range f).restrictScalars R := rfl

end

/-- The decreasing sequence of submodules consisting of the ranges of the iterates of a linear map.
-/
@[simps]
/--
Definition of `iterateRange` / `iterateRange` 的定义

English:
definition iterateRange
  signature: (f : M ->ₗ[R] M)
  body: LinearMap.range (f ^ n)
  monotone' := monotone_nat_of_le_succ fun | n, _, ⟨x, rfl⟩ => ⟨f x, rfl⟩

中文:
定义 iterateRange
  签名: (f : M ->ₗ[R] M)
  定义体: LinearMap.range (f ^ n)
  monotone' := monotone_nat_of_le_succ fun | n, _, ⟨x, rfl⟩ => ⟨f x, rfl⟩

Depends on / 依赖: LinearMap, LinearMap.range
-/
def iterateRange (f : M ->ₗ[R] M) : Nat ->o (Submodule R M)ᵒᵈ where
  toFun n := LinearMap.range (f ^ n)
  monotone' := monotone_nat_of_le_succ fun | n, _, ⟨x, rfl⟩ => ⟨f x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `iterateRange_succ` / 引理 `iterateRange_succ`

English:
lemma iterateRange_succ
  given: {f : M ->ₗ[R] M} {n : Nat}
  proof: by
  simp only [iterateRange_coe, range_eq_map, ← map_comp, Module.End.iterate_succ']

中文:
引理 iterateRange_succ
  条件: {f : M ->ₗ[R] M} {n : 自然数}
  证明: by
  simp only [iterateRange_coe, range_eq_map, ← map_comp, Module.End.iterate_succ']

Depends on / 依赖: Module, Module.End.iterate_succ, iterateRange_coe, iterate_succ, map_comp, range_eq_map
-/
lemma iterateRange_succ {f : M ->ₗ[R] M} {n : Nat} :
    iterateRange f (n + 1) = (iterateRange f n).map f := by
  simp only [iterateRange_coe, range_eq_map, ← map_comp, Module.End.iterate_succ']

/--
Definition of `rangeRestrict` / `rangeRestrict` 的定义

English:
abbreviation rangeRestrict
  signature: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  body: f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

中文:
缩写 rangeRestrict
  签名: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  定义体: f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

Depends on / 依赖: LinearMap, LinearMap.mem_range_self, LinearMap.range, codRestrict, f.codRestrict, mem_range_self
-/
abbrev rangeRestrict [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : M ->ₛₗ[τ₁₂] LinearMap.range f :=
  f.codRestrict (LinearMap.range f) (LinearMap.mem_range_self f)

/--
Instance `fintypeRange` / 实例 `fintypeRange`

English:
instance fintypeRange
  signature: [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  body: Set.fintypeRange f

中文:
实例 fintypeRange
  签名: [有限类型 M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  定义体: Set.fintypeRange f

Depends on / 依赖: Set.fintypeRange, fintypeRange
-/
instance fintypeRange [Fintype M] [DecidableEq M₂] [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) :
    Fintype (range f) :=
  Set.fintypeRange f

/--
theorem `range_codRestrict` / 定理 `range_codRestrict`

English:
theorem range_codRestrict
  statement: {τ₂₁ : R₂ ->+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
  proof: by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _

中文:
定理 range_codRestrict
  结论: {τ₂₁ : R₂ ->+* R} [RingHomSurjective τ₂₁] (p : 子模 R M)
  证明: by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _

Depends on / 依赖: map_codRestrict, range_eq_map
-/
theorem range_codRestrict {τ₂₁ : R₂ ->+* R} [RingHomSurjective τ₂₁] (p : Submodule R M)
    (f : M₂ ->ₛₗ[τ₂₁] M) (hf) :
    range (codRestrict p f hf) = comap p.subtype (LinearMap.range f) := by
  simpa only [range_eq_map] using map_codRestrict _ _ _ _

/--
theorem `_root_.Submodule.map_comap_eq` / 定理 `_root_.Submodule.map_comap_eq`

English:
theorem _root_.Submodule.map_comap_eq
  statement: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  proof: le_antisymm (le_inf map_le_range (map_comap_le _ _)) by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

中文:
定理 _root_.子模.map_comap_eq
  结论: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  证明: le_antisymm (le_inf map_le_range (map_comap_le _ _)) by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

Depends on / 依赖: le_antisymm, le_inf, map_comap_le, map_le_range
-/
theorem _root_.Submodule.map_comap_eq [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
    (q : Submodule R₂ M₂) :
    map f (comap f q) = range f ⊓ q :=
le_antisymm (le_inf map_le_range (map_comap_le _ _)) by
    rintro _ ⟨⟨x, _, rfl⟩, hx⟩; exact ⟨x, hx, rfl⟩

/--
theorem `_root_.Submodule.map_comap_eq_self` / 定理 `_root_.Submodule.map_comap_eq_self`

English:
theorem _root_.Submodule.map_comap_eq_self
  statement: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]

中文:
定理 _root_.子模.map_comap_eq_self
  结论: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]

Depends on / 依赖: Submodule, Submodule.map_comap_eq, inf_eq_right, map_comap_eq
-/
theorem _root_.Submodule.map_comap_eq_self [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂}
    {q : Submodule R₂ M₂} (h : q <= range f) :
    map f (comap f q) = q := by
  rwa [Submodule.map_comap_eq, inf_eq_right]

@[simp]
/--
theorem `range_zero` / 定理 `range_zero`

English:
theorem range_zero
  given: [RingHomSurjective τ₁₂]
  statement: range (0 : M ->ₛₗ[τ₁₂] M₂) = ⊥
  proof: by
  simpa only [range_eq_map] using Submodule.map_zero _

中文:
定理 range_zero
  条件: [RingHomSurjective τ₁₂]
  结论: range (0 : M ->ₛₗ[τ₁₂] M₂) = ⊥
  证明: by
  simpa only [range_eq_map] using Submodule.map_zero _

Depends on / 依赖: Submodule, Submodule.map_zero, map_zero, range_eq_map
-/
theorem range_zero [RingHomSurjective τ₁₂] : range (0 : M ->ₛₗ[τ₁₂] M₂) = ⊥ := by
  simpa only [range_eq_map] using Submodule.map_zero _

section

variable [RingHomSurjective τ₁₂]

/--
theorem `range_le_bot_iff` / 定理 `range_le_bot_iff`

English:
theorem range_le_bot_iff
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: range f <= ⊥ ↔ f = 0
  proof: by
  rw [range_le_iff_comap]; exact ker_eq_top

中文:
定理 range_le_bot_iff
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: range f <= ⊥ ↔ f = 0
  证明: by
  rw [range_le_iff_comap]; exact ker_eq_top

Depends on / 依赖: ker_eq_top, range_le_iff_comap
-/
theorem range_le_bot_iff (f : M ->ₛₗ[τ₁₂] M₂) : range f <= ⊥ ↔ f = 0 := by
  rw [range_le_iff_comap]; exact ker_eq_top

/--
theorem `range_eq_bot` / 定理 `range_eq_bot`

English:
theorem range_eq_bot
  given: {f : M ->ₛₗ[τ₁₂] M₂}
  statement: range f = ⊥ ↔ f = 0
  proof: by
  rw [← range_le_bot_iff]; rw [le_bot_iff]

中文:
定理 range_eq_bot
  条件: {f : M ->ₛₗ[τ₁₂] M₂}
  结论: range f = ⊥ ↔ f = 0
  证明: by
  rw [← range_le_bot_iff]; rw [le_bot_iff]

Depends on / 依赖: le_bot_iff, range_le_bot_iff
-/
theorem range_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : range f = ⊥ ↔ f = 0 := by
  rw [← range_le_bot_iff]; rw [le_bot_iff]

/--
theorem `range_le_ker_iff` / 定理 `range_le_ker_iff`

English:
theorem range_le_ker_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃}
  proof: ⟨fun h => ker_eq_top.1 eq_top_iff'.2 fun _ => h ⟨_, rfl⟩, fun h x hx =>
mem_ker.2 Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩

中文:
定理 range_le_ker_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃}
  证明: ⟨fun h => ker_eq_top.1 eq_top_iff'.2 fun _ => h ⟨_, rfl⟩, fun h x hx =>
mem_ker.2 Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩

Depends on / 依赖: Exists, Exists.elim, comp_apply, eq_top_iff, ker_eq_top, mem_ker, zero_apply
-/
theorem range_le_ker_iff {f : M ->ₛₗ[τ₁₂] M₂} {g : M₂ ->ₛₗ[τ₂₃] M₃} :
    range f <= ker g ↔ (g.comp f : M ->ₛₗ[τ₁₃] M₃) = 0 :=
⟨fun h => ker_eq_top.1 eq_top_iff'.2 fun _ => h ⟨_, rfl⟩, fun h x hx =>
mem_ker.2 Exists.elim hx fun y hy => by rw [← hy, ← comp_apply, h, zero_apply]⟩

/--
theorem `comap_le_comap_iff` / 定理 `comap_le_comap_iff`

English:
theorem comap_le_comap_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'}
  proof: ⟨fun H => by rwa [SetLike.le_def, (range_eq_top.1 hf).forall], comap_mono⟩

中文:
定理 comap_le_comap_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'}
  证明: ⟨fun H => by rwa [SetLike.le_def, (range_eq_top.1 hf).forall], comap_mono⟩

Depends on / 依赖: SetLike, SetLike.le_def, comap_mono, le_def, range_eq_top
-/
theorem comap_le_comap_iff {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) {p p'} :
    comap f p <= comap f p' ↔ p <= p' :=
  ⟨fun H => by rwa [SetLike.le_def, (range_eq_top.1 hf).forall], comap_mono⟩

/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤)
  statement: Injective (comap f)
  proof: fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

中文:
定理 comap_injective
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤)
  结论: 单射 (comap f)
  证明: fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))
-/
theorem comap_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : range f = ⊤) : Injective (comap f) := fun _ _ h =>
  le_antisymm ((comap_le_comap_iff hf).1 (le_of_eq h)) ((comap_le_comap_iff hf).1 (ge_of_eq h))

-- TODO (?): generalize the next two lemmas to semilinear maps with `f ∘ₗ g` bijective.

/--
theorem `ker_eq_range_of_comp_eq_id` / 定理 `ker_eq_range_of_comp_eq_id`

English:
theorem ker_eq_range_of_comp_eq_id
  statement: {M P} [AddCommGroup M] [Module R M]
  proof: le_antisymm (fun x hx => ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩)
range_le_ker_iff.mpr by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

中文:
定理 ker_eq_range_of_comp_eq_id
  结论: {M P} [加法交换群 M] [模 R M]
  证明: le_antisymm (fun x hx => ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩)
range_le_ker_iff.mpr by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

Depends on / 依赖: comp_assoc, comp_id, comp_sub, id_comp, le_antisymm, map_zero, range_le_ker_iff, range_le_ker_iff.mpr, sub_self, sub_zero
-/
theorem ker_eq_range_of_comp_eq_id {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M ->ₗ[R] P} {g : P ->ₗ[R] M} (h : f ∘ₗ g = .id) :
    ker f = range (LinearMap.id - g ∘ₗ f) :=
le_antisymm (fun x hx => ⟨x, show x - g (f x) = x by rw [hx, map_zero, sub_zero]⟩)
range_le_ker_iff.mpr by rw [comp_sub, comp_id, ← comp_assoc, h, id_comp, sub_self]

/--
lemma `range_eq_ker_of_leftInverse` / 引理 `range_eq_ker_of_leftInverse`

English:
lemma range_eq_ker_of_leftInverse
  statement: {M P} [AddCommGroup M] [Module R M]
  proof: -- If `y = f x ∈ range f`, we have `(f ∘ g) y = f (g (f x)) = f x = y` by hypothesis `h`.
  -- Conversely, f g z - z = 0 implies z = f (g z) ∈ range f.
  le_antisymm (by rintro y ⟨x, rfl⟩; simp [h x]) (fun x hx => ⟨g x, by simpa [sub_eq_zero] using hx⟩)

中文:
引理 range_eq_ker_of_leftInverse
  结论: {M P} [加法交换群 M] [模 R M]
  证明: -- If `y = f x ∈ range f`, we have `(f ∘ g) y = f (g (f x)) = f x = y` by hypothesis `h`.
  -- Conversely, f g z - z = 0 implies z = f (g z) ∈ range f.
  le_antisymm (by rintro y ⟨x, rfl⟩; simp [h x]) (fun x hx => ⟨g x, by simpa [sub_eq_zero] using hx⟩)
-/
lemma range_eq_ker_of_leftInverse {M P} [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] {f : M ->ₗ[R] P} {g : P ->ₗ[R] M}
    (h : LeftInverse g f) : f.range = ker ((f.comp g) - LinearMap.id) :=
  -- If `y = f x ∈ range f`, we have `(f ∘ g) y = f (g (f x)) = f x = y` by hypothesis `h`.
  -- Conversely, f g z - z = 0 implies z = f (g z) ∈ range f.
  le_antisymm (by rintro y ⟨x, rfl⟩; simp [h x]) (fun x hx => ⟨g x, by simpa [sub_eq_zero] using hx⟩)

end

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂}
variable {f : M ->ₛₗ[τ₁₂] M₂}

open Submodule

/--
theorem `range_toAddSubgroup` / 定理 `range_toAddSubgroup`

English:
theorem range_toAddSubgroup
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  proof: rfl

中文:
定理 range_toAddSubgroup
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  证明: rfl
-/
theorem range_toAddSubgroup [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) :
    (range f).toAddSubgroup = f.toAddMonoidHom.range :=
  rfl

/--
theorem `ker_le_iff` / 定理 `ker_le_iff`

English:
theorem ker_le_iff
  given: [RingHomSurjective τ₁₂] {p : Submodule R M}
  proof: by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe]; rw [coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe]; rw [coe_range]; rw [Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x in p := h₂ hx
    have hxz : z + x in p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x in p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

中文:
定理 ker_le_iff
  条件: [RingHomSurjective τ₁₂] {p : 子模 R M}
  证明: by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe]; rw [coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe]; rw [coe_range]; rw [Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x in p := h₂ hx
    have hxz : z + x in p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x in p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

Depends on / 依赖: Set.mem_range, SetLike, SetLike.le_def, SetLike.mem_coe, add_sub_cancel_right, coe_range, le_def, map_zero, mem_coe, mem_ker, mem_range, p.sub_mem, sub_mem
-/
theorem ker_le_iff [RingHomSurjective τ₁₂] {p : Submodule R M} :
    ker f <= p ↔ exists y in range f, f ⁻¹' {y} subseteq p := by
  constructor
  · intro h
    use 0
    rw [← SetLike.mem_coe]; rw [coe_range]
    exact ⟨⟨0, map_zero f⟩, h⟩
  · rintro ⟨y, h₁, h₂⟩
    rw [SetLike.le_def]
    intro z hz
    simp only [mem_ker] at hz
    rw [← SetLike.mem_coe]; rw [coe_range]; rw [Set.mem_range] at h₁
    obtain ⟨x, hx⟩ := h₁
    have hx' : x in p := h₂ hx
    have hxz : z + x in p := by
      apply h₂
      simp [hx, hz]
    suffices z + x - x in p by simpa only [this, add_sub_cancel_right]
    exact p.sub_mem hxz hx'

end Ring

section CommSemiring

variable [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} [RingHomSurjective τ₁₂]

/--
theorem `range_smul_le_range` / 定理 `range_smul_le_range`

English:
theorem range_smul_le_range
  given: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  statement: range (c • f) <= range f
  proof: by
  simpa only [range_eq_map] using Submodule.map_smul_le_map _ _ _

中文:
定理 range_smul_le_range
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  结论: range (c • f) <= range f
  证明: by
  simpa only [range_eq_map] using Submodule.map_smul_le_map _ _ _

Depends on / 依赖: Submodule, Submodule.map_smul_le_map, map_smul_le_map, range_eq_map
-/
theorem range_smul_le_range (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : range (c • f) <= range f := by
  simpa only [range_eq_map] using Submodule.map_smul_le_map _ _ _

end CommSemiring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/--
theorem `range_smul` / 定理 `range_smul`

English:
theorem range_smul
  given: (f : V ->ₗ[K] V₂) (a : K) (h : a != 0)
  statement: range (a • f) = range f
  proof: by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h

中文:
定理 range_smul
  条件: (f : V ->ₗ[K] V₂) (a : K) (h : a != 0)
  结论: range (a • f) = range f
  证明: by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h

Depends on / 依赖: Submodule, Submodule.map_smul, map_smul, range_eq_map
-/
theorem range_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : range (a • f) = range f := by
  simpa only [range_eq_map] using Submodule.map_smul f _ a h

/--
theorem `range_smul'` / 定理 `range_smul'`

English:
theorem range_smul'
  given: (f : V ->ₗ[K] V₂) (a : K)
  proof: by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a

中文:
定理 range_smul'
  条件: (f : V ->ₗ[K] V₂) (a : K)
  证明: by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a

Depends on / 依赖: Submodule, Submodule.map_smul, map_smul, range_eq_map
-/
theorem range_smul' (f : V ->ₗ[K] V₂) (a : K) :
    range (a • f) = ⨆ _ : a != 0, range f := by
  simpa only [range_eq_map] using Submodule.map_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R ->+* R₂}

open LinearMap

@[simp]
/--
theorem `map_top` / 定理 `map_top`

English:
theorem map_top
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  statement: map f ⊤ = range f
  proof: (range_eq_map f).symm

@[simp]

中文:
定理 map_top
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)
  结论: map f ⊤ = range f
  证明: (range_eq_map f).symm

@[simp]

Depends on / 依赖: range_eq_map
-/
theorem map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) : map f ⊤ = range f :=
  (range_eq_map f).symm

@[simp]
/--
theorem `range_subtype` / 定理 `range_subtype`

English:
theorem range_subtype
  statement: range p.subtype = p
  proof: by simpa using map_comap_subtype p ⊤

中文:
定理 range_subtype
  结论: range p.subtype = p
  证明: by simpa using map_comap_subtype p ⊤

Depends on / 依赖: map_comap_subtype
-/
theorem range_subtype : range p.subtype = p := by simpa using map_comap_subtype p ⊤

/--
theorem `map_subtype_le` / 定理 `map_subtype_le`

English:
theorem map_subtype_le
  given: (p' : Submodule R p)
  statement: map p.subtype p' <= p
  proof: by
  simpa using (map_le_range : map p.subtype p' <= range p.subtype)

中文:
定理 map_subtype_le
  条件: (p' : 子模 R p)
  结论: map p.subtype p' <= p
  证明: by
  simpa using (map_le_range : map p.subtype p' <= range p.subtype)

Depends on / 依赖: map_le_range, p.subtype, subtype
-/
theorem map_subtype_le (p' : Submodule R p) : map p.subtype p' <= p := by
  simpa using (map_le_range : map p.subtype p' <= range p.subtype)

/--
theorem `map_subtype_top` / 定理 `map_subtype_top`

English:
theorem map_subtype_top
  statement: map p.subtype (⊤ : Submodule R p) = p
  proof: by simp

@[simp]

中文:
定理 map_subtype_top
  结论: map p.subtype (⊤ : 子模 R p) = p
  证明: by simp

@[simp]
-/
theorem map_subtype_top : map p.subtype (⊤ : Submodule R p) = p := by simp

@[simp]
/--
theorem `comap_subtype_eq_top` / 定理 `comap_subtype_eq_top`

English:
theorem comap_subtype_eq_top
  given: {p p' : Submodule R M}
  statement: comap p.subtype p' = ⊤ ↔ p <= p'
  proof: eq_top_iff.trans map_le_iff_le_comap.symm.trans by rw [map_subtype_top]

中文:
定理 comap_subtype_eq_top
  条件: {p p' : 子模 R M}
  结论: comap p.subtype p' = ⊤ ↔ p <= p'
  证明: eq_top_iff.trans map_le_iff_le_comap.symm.trans by rw [map_subtype_top]

Depends on / 依赖: eq_top_iff, eq_top_iff.trans, map_le_iff_le_comap, map_le_iff_le_comap.symm.trans, map_subtype_top
-/
theorem comap_subtype_eq_top {p p' : Submodule R M} : comap p.subtype p' = ⊤ ↔ p <= p' :=
eq_top_iff.trans map_le_iff_le_comap.symm.trans by rw [map_subtype_top]

/--
lemma `submoduleOf_eq_top` / 引理 `submoduleOf_eq_top`

English:
lemma submoduleOf_eq_top
  given: {p q : Submodule R M}
  proof: by simp [submoduleOf]

@[simp]

中文:
引理 submoduleOf_eq_top
  条件: {p q : 子模 R M}
  证明: by simp [submoduleOf]

@[simp]
-/
@[simp] lemma submoduleOf_eq_top {p q : Submodule R M} :
    p.submoduleOf q = ⊤ ↔ q <= p := by simp [submoduleOf]

@[simp]
/--
theorem `comap_subtype_self` / 定理 `comap_subtype_self`

English:
theorem comap_subtype_self
  statement: comap p.subtype p = ⊤
  proof: comap_subtype_eq_top.2 le_rfl

中文:
定理 comap_subtype_self
  结论: comap p.subtype p = ⊤
  证明: comap_subtype_eq_top.2 le_rfl

Depends on / 依赖: comap_subtype_eq_top, le_rfl
-/
theorem comap_subtype_self : comap p.subtype p = ⊤ :=
  comap_subtype_eq_top.2 le_rfl

/--
theorem `submoduleOf_self` / 定理 `submoduleOf_self`

English:
theorem submoduleOf_self
  given: (N : Submodule R M)
  statement: N.submoduleOf N = ⊤
  proof: comap_subtype_self _

中文:
定理 submoduleOf_self
  条件: (N : 子模 R M)
  结论: N.submoduleOf N = ⊤
  证明: comap_subtype_self _

Depends on / 依赖: comap_subtype_self
-/
theorem submoduleOf_self (N : Submodule R M) : N.submoduleOf N = ⊤ := comap_subtype_self _

/--
theorem `submoduleOf_sup_of_le` / 定理 `submoduleOf_sup_of_le`

English:
theorem submoduleOf_sup_of_le
  given: {N₁ N₂ N : Submodule R M} (h₁ : N₁ <= N) (h₂ : N₂ <= N)
  proof: by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

@[simp]

中文:
定理 submoduleOf_sup_of_le
  条件: {N₁ N₂ N : 子模 R M} (h₁ : N₁ <= N) (h₂ : N₂ <= N)
  证明: by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

@[simp]

Depends on / 依赖: N.subtype_injective, Submodule, Submodule.map_injective_of_injective, map_comap_eq, map_injective_of_injective, submoduleOf, subtype_injective
-/
theorem submoduleOf_sup_of_le {N₁ N₂ N : Submodule R M} (h₁ : N₁ <= N) (h₂ : N₂ <= N) :
    (N₁ ⊔ N₂).submoduleOf N = N₁.submoduleOf N ⊔ N₂.submoduleOf N := by
  apply Submodule.map_injective_of_injective N.subtype_injective
  simp only [submoduleOf, map_comap_eq]
  simp_all

@[simp]
/--
lemma `comap_subtype_le_iff` / 引理 `comap_subtype_le_iff`

English:
lemma comap_subtype_le_iff
  given: {p q r : Submodule R M}
  proof: ⟨fun h => by simpa using map_mono (f := p.subtype) h,
   fun h => by simpa using comap_mono (f := p.subtype) h⟩

中文:
引理 comap_subtype_le_iff
  条件: {p q r : 子模 R M}
  证明: ⟨fun h => by simpa using map_mono (f := p.subtype) h,
   fun h => by simpa using comap_mono (f := p.subtype) h⟩

Depends on / 依赖: comap_mono, map_mono, p.subtype, subtype
-/
lemma comap_subtype_le_iff {p q r : Submodule R M} :
    q.comap p.subtype <= r.comap p.subtype ↔ p ⊓ q <= p ⊓ r :=
  ⟨fun h => by simpa using map_mono (f := p.subtype) h,
   fun h => by simpa using comap_mono (f := p.subtype) h⟩

/--
theorem `range_inclusion` / 定理 `range_inclusion`

English:
theorem range_inclusion
  given: (p q : Submodule R M) (h : p <= q)
  proof: by
  rw [← map_top]; rw [inclusion]; rw [LinearMap.map_codRestrict]; rw [map_top]; rw [range_subtype]

@[simp]

中文:
定理 range_inclusion
  条件: (p q : 子模 R M) (h : p <= q)
  证明: by
  rw [← map_top]; rw [inclusion]; rw [LinearMap.map_codRestrict]; rw [map_top]; rw [range_subtype]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.map_codRestrict, inclusion, map_codRestrict, map_top, range_subtype
-/
theorem range_inclusion (p q : Submodule R M) (h : p <= q) :
    range (inclusion h) = comap q.subtype p := by
  rw [← map_top]; rw [inclusion]; rw [LinearMap.map_codRestrict]; rw [map_top]; rw [range_subtype]

@[simp]
/--
theorem `map_subtype_range_inclusion` / 定理 `map_subtype_range_inclusion`

English:
theorem map_subtype_range_inclusion
  given: {p p' : Submodule R M} (h : p <= p')
  proof: by simp [range_inclusion, map_comap_eq, h]

中文:
定理 map_subtype_range_inclusion
  条件: {p p' : 子模 R M} (h : p <= p')
  证明: by simp [range_inclusion, map_comap_eq, h]

Depends on / 依赖: map_comap_eq, range_inclusion
-/
theorem map_subtype_range_inclusion {p p' : Submodule R M} (h : p <= p') :
    map p'.subtype (range <| inclusion h) = p := by simp [range_inclusion, map_comap_eq, h]

/--
lemma `restrictScalars_map` / 引理 `restrictScalars_map`

English:
lemma restrictScalars_map
  statement: [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower R R₂ M]
  proof: rfl

中文:
引理 restrictScalars_map
  结论: [标量乘法 R R₂] [模 R₂ M] [模 R M₂] [标量塔 R R₂ M]
  证明: rfl
-/
lemma restrictScalars_map [SMul R R₂] [Module R₂ M] [Module R M₂] [IsScalarTower R R₂ M]
    [IsScalarTower R R₂ M₂] (f : M ->ₗ[R₂] M₂) (M' : Submodule R₂ M) :
    (M'.map f).restrictScalars R = (M'.restrictScalars R).map (f.restrictScalars R) := rfl

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `MapSubtype.orderIso` / `MapSubtype.orderIso` 的定义

English:
definition MapSubtype.orderIso
  signature: : Submodule R p ≃o { p' : Submodule R M // p' <= p } where
  body: ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simp [map_comap_subtype p, inf_of_le_right hq]
map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans by
    dsimp
    rw [map_le_iff_le_comap]; rw [comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]

中文:
定义 MapSubtype.orderIso
  签名: : 子模 R p ≃o { p' : 子模 R M // p' <= p } where
  定义体: ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simp [map_comap_subtype p, inf_of_le_right hq]
map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans by
    dsimp
    rw [map_le_iff_le_comap]; rw [comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]
-/
def MapSubtype.orderIso : Submodule R p ≃o { p' : Submodule R M // p' <= p } where
  toFun p' := ⟨map p.subtype p', map_subtype_le p _⟩
  invFun q := comap p.subtype q
  left_inv p' := comap_map_eq_of_injective (by exact Subtype.val_injective) p'
right_inv := fun ⟨q, hq⟩ => Subtype.ext by simp [map_comap_subtype p, inf_of_le_right hq]
map_rel_iff' {p₁ p₂} := Subtype.coe_le_coe.symm.trans by
    dsimp
    rw [map_le_iff_le_comap]; rw [comap_map_eq_of_injective (show Injective p.subtype from Subtype.coe_injective) p₂]

/--
Definition of `MapSubtype.orderEmbedding` / `MapSubtype.orderEmbedding` 的定义

English:
definition MapSubtype.orderEmbedding
  signature: : Submodule R p ↪o Submodule R M
  body: (RelIso.toRelEmbedding <| MapSubtype.orderIso p).trans
    Subtype.relEmbedding (X := Submodule R M) (fun p p' => p <= p') _

@[simp]

中文:
定义 MapSubtype.orderEmbedding
  签名: : 子模 R p ↪o 子模 R M
  定义体: (RelIso.toRelEmbedding <| MapSubtype.orderIso p).trans
    Subtype.relEmbedding (X := Submodule R M) (fun p p' => p <= p') _

@[simp]

Depends on / 依赖: MapSubtype, MapSubtype.orderIso, RelIso, RelIso.toRelEmbedding, Submodule, Subtype, Subtype.relEmbedding, orderIso, relEmbedding, toRelEmbedding
-/
def MapSubtype.orderEmbedding : Submodule R p ↪o Submodule R M :=
(RelIso.toRelEmbedding <| MapSubtype.orderIso p).trans
    Subtype.relEmbedding (X := Submodule R M) (fun p p' => p <= p') _

@[simp]
/--
theorem `map_subtype_embedding_eq` / 定理 `map_subtype_embedding_eq`

English:
theorem map_subtype_embedding_eq
  given: (p' : Submodule R p)
  proof: rfl

中文:
定理 map_subtype_embedding_eq
  条件: (p' : 子模 R p)
  证明: rfl
-/
theorem map_subtype_embedding_eq (p' : Submodule R p) :
    MapSubtype.orderEmbedding p p' = map p.subtype p' :=
  rfl

/--
Definition of `mapIic` / `mapIic` 的定义

English:
definition mapIic
  signature: (p : Submodule R M)
  body: Submodule.MapSubtype.orderIso p

中文:
定义 mapIic
  签名: (p : 子模 R M)
  定义体: Submodule.MapSubtype.orderIso p

Depends on / 依赖: MapSubtype, Submodule, Submodule.MapSubtype.orderIso, orderIso
-/
def mapIic (p : Submodule R M) :
    Submodule R p ≃o Set.Iic p :=
  Submodule.MapSubtype.orderIso p

/--
lemma `coe_mapIic_apply` / 引理 `coe_mapIic_apply`

English:
lemma coe_mapIic_apply
  proof: rfl

中文:
引理 coe_mapIic_apply
  证明: rfl
-/
@[simp] lemma coe_mapIic_apply
    (p : Submodule R M) (q : Submodule R p) :
    (p.mapIic q : Submodule R M) = q.map p.subtype :=
  rfl

/--
lemma `codisjoint_map` / 引理 `codisjoint_map`

English:
lemma codisjoint_map
  statement: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} (hf : Function.Surjective f)
  proof: by
  rw [codisjoint_iff]; rw [← Submodule.map_sup]; rw [codisjoint_iff.mp hpq]; rw [map_top]; rw [LinearMap.range_eq_top_of_surjective f hf]

中文:
引理 codisjoint_map
  结论: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} (hf : 函数.满射 f)
  证明: by
  rw [codisjoint_iff]; rw [← Submodule.map_sup]; rw [codisjoint_iff.mp hpq]; rw [map_top]; rw [LinearMap.range_eq_top_of_surjective f hf]

Depends on / 依赖: LinearMap, LinearMap.range_eq_top_of_surjective, Submodule, Submodule.map_sup, codisjoint_iff, codisjoint_iff.mp, map_sup, map_top, range_eq_top_of_surjective
-/
lemma codisjoint_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} (hf : Function.Surjective f)
    {p q : Submodule R M} (hpq : Codisjoint p q) : Codisjoint (p.map f) (q.map f) := by
  rw [codisjoint_iff]; rw [← Submodule.map_sup]; rw [codisjoint_iff.mp hpq]; rw [map_top]; rw [LinearMap.range_eq_top_of_surjective f hf]

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R ->+* R₂} {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/--
theorem `ker_eq_bot_of_cancel` / 定理 `ker_eq_bot_of_cancel`

English:
theorem ker_eq_bot_of_cancel
  statement: {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  have h₁ : f.comp (0 : ker f ->ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f)]; rw [← h 0 (ker f).subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero

中文:
定理 ker_eq_bot_of_cancel
  结论: {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  have h₁ : f.comp (0 : ker f ->ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f)]; rw [← h 0 (ker f).subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero

Depends on / 依赖: Eq.trans, Submodule, Submodule.range_subtype, comp_ker_subtype, comp_zero, f.comp, range_subtype, range_zero, subtype
-/
theorem ker_eq_bot_of_cancel {f : M ->ₛₗ[τ₁₂] M₂}
    (h : forall u v : ker f ->ₗ[R] M, f.comp u = f.comp v -> u = v) : ker f = ⊥ := by
  have h₁ : f.comp (0 : ker f ->ₗ[R] M) = 0 := comp_zero _
  rw [← Submodule.range_subtype (ker f)]; rw [← h 0 (ker f).subtype (Eq.trans h₁ (comp_ker_subtype f).symm)]
  exact range_zero

/--
theorem `range_comp_of_range_eq_top` / 定理 `range_comp_of_range_eq_top`

English:
theorem range_comp_of_range_eq_top
  statement: [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
  proof: by rw [range_comp, hf, Submodule.map_top]

中文:
定理 range_comp_of_range_eq_top
  结论: [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
  证明: by rw [range_comp, hf, Submodule.map_top]

Depends on / 依赖: Submodule, Submodule.map_top, map_top, range_comp
-/
theorem range_comp_of_range_eq_top [RingHomSurjective τ₁₂] [RingHomSurjective τ₂₃]
    [RingHomSurjective τ₁₃] {f : M ->ₛₗ[τ₁₂] M₂} (g : M₂ ->ₛₗ[τ₂₃] M₃) (hf : range f = ⊤) :
    range (g.comp f : M ->ₛₗ[τ₁₃] M₃) = range g := by rw [range_comp, hf, Submodule.map_top]

section Image

/--
Definition of `submoduleImage` / `submoduleImage` 的定义

English:
definition submoduleImage
  signature: {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
  body: (N.comap O.subtype).map ϕ

@[simp]

中文:
定义 submoduleImage
  签名: {M' : 类型} [加法交换幺半群 M'] [模 R M'] {O : 子模 R M}
  定义体: (N.comap O.subtype).map ϕ

@[simp]

Depends on / 依赖: N.comap, Nonempty, O.subtype, One.instNonempty, instNonempty, subtype
-/
def submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    (ϕ : O ->ₗ[R] M') (N : Submodule R M) : Submodule R M' :=
  (N.comap O.subtype).map ϕ

@[simp]
/--
theorem `mem_submoduleImage` / 定理 `mem_submoduleImage`

English:
theorem mem_submoduleImage
  statement: {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
  proof: by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y in N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩

中文:
定理 mem_submoduleImage
  结论: {M' : 类型} [加法交换幺半群 M'] [模 R M'] {O : 子模 R M}
  证明: by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y in N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩

Depends on / 依赖: Submodule, Submodule.mem_comap, Submodule.mem_map.trans, mem_comap, mem_map, simp_rw
-/
theorem mem_submoduleImage {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O ->ₗ[R] M'} {N : Submodule R M} {x : M'} :
    x in ϕ.submoduleImage N ↔ exists (y : _) (yO : y in O), y in N ∧ ϕ ⟨y, yO⟩ = x := by
  refine Submodule.mem_map.trans ⟨?_, ?_⟩ <;> simp_rw [Submodule.mem_comap]
  · rintro ⟨⟨y, yO⟩, yN : y in N, h⟩
    exact ⟨y, yO, yN, h⟩
  · rintro ⟨y, yO, yN, h⟩
    exact ⟨⟨y, yO⟩, yN, h⟩

/--
theorem `mem_submoduleImage_of_le` / 定理 `mem_submoduleImage_of_le`

English:
theorem mem_submoduleImage_of_le
  statement: {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
  proof: by
  grind [mem_submoduleImage]

中文:
定理 mem_submoduleImage_of_le
  结论: {M' : 类型} [加法交换幺半群 M'] [模 R M'] {O : 子模 R M}
  证明: by
  grind [mem_submoduleImage]

Depends on / 依赖: mem_submoduleImage
-/
theorem mem_submoduleImage_of_le {M' : Type*} [AddCommMonoid M'] [Module R M'] {O : Submodule R M}
    {ϕ : O ->ₗ[R] M'} {N : Submodule R M} (hNO : N <= O) {x : M'} :
    x in ϕ.submoduleImage N ↔ exists (y : _) (yN : y in N), ϕ ⟨y, hNO yN⟩ = x := by
  grind [mem_submoduleImage]

/--
theorem `submoduleImage_apply_of_le` / 定理 `submoduleImage_apply_of_le`

English:
theorem submoduleImage_apply_of_le
  statement: {M' : Type*} [AddCommMonoid M'] [Module R M']
  proof: by
  rw [submoduleImage]; rw [range_comp]; rw [Submodule.range_inclusion]

中文:
定理 submoduleImage_apply_of_le
  结论: {M' : 类型} [加法交换幺半群 M'] [模 R M']
  证明: by
  rw [submoduleImage]; rw [range_comp]; rw [Submodule.range_inclusion]

Depends on / 依赖: Submodule, Submodule.range_inclusion, range_comp, range_inclusion, submoduleImage
-/
theorem submoduleImage_apply_of_le {M' : Type*} [AddCommMonoid M'] [Module R M']
    {O : Submodule R M} (ϕ : O ->ₗ[R] M') (N : Submodule R M) (hNO : N <= O) :
    ϕ.submoduleImage N = range (ϕ.comp (Submodule.inclusion hNO)) := by
  rw [submoduleImage]; rw [range_comp]; rw [Submodule.range_inclusion]

end Image

section rangeRestrict

variable [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂)

/--
theorem `range_rangeRestrict` / 定理 `range_rangeRestrict`

English:
theorem range_rangeRestrict
  statement: range f.rangeRestrict = ⊤
  proof: by simp [f.range_codRestrict _]

中文:
定理 range_rangeRestrict
  结论: range f.rangeRestrict = ⊤
  证明: by simp [f.range_codRestrict _]
-/
@[simp] theorem range_rangeRestrict : range f.rangeRestrict = ⊤ := by simp [f.range_codRestrict _]

/--
theorem `surjective_rangeRestrict` / 定理 `surjective_rangeRestrict`

English:
theorem surjective_rangeRestrict
  statement: Surjective f.rangeRestrict
  proof: by
  rw [← range_eq_top]; rw [range_rangeRestrict]

中文:
定理 surjective_rangeRestrict
  结论: 满射 f.rangeRestrict
  证明: by
  rw [← range_eq_top]; rw [range_rangeRestrict]

Depends on / 依赖: range_eq_top, range_rangeRestrict
-/
theorem surjective_rangeRestrict : Surjective f.rangeRestrict := by
  rw [← range_eq_top]; rw [range_rangeRestrict]

/--
theorem `ker_rangeRestrict` / 定理 `ker_rangeRestrict`

English:
theorem ker_rangeRestrict
  statement: ker f.rangeRestrict = ker f
  proof: LinearMap.ker_codRestrict _ _ _

中文:
定理 ker_rangeRestrict
  结论: ker f.rangeRestrict = ker f
  证明: LinearMap.ker_codRestrict _ _ _

Depends on / 依赖: LinearMap, LinearMap.ker_codRestrict, ker_codRestrict
-/
theorem ker_rangeRestrict : ker f.rangeRestrict = ker f := LinearMap.ker_codRestrict _ _ _

/--
theorem `injective_rangeRestrict_iff` / 定理 `injective_rangeRestrict_iff`

English:
theorem injective_rangeRestrict_iff
  statement: Injective f.rangeRestrict ↔ Injective f
  proof: Set.injective_codRestrict _

中文:
定理 injective_rangeRestrict_iff
  结论: 单射 f.rangeRestrict ↔ 单射 f
  证明: Set.injective_codRestrict _
-/
@[simp] theorem injective_rangeRestrict_iff : Injective f.rangeRestrict ↔ Injective f :=
  Set.injective_codRestrict _

end rangeRestrict

section restrict

open Submodule

variable [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) {p : Submodule R M} {q : Submodule R₂ M₂}

@[simp]
/--
theorem `range_restrict` / 定理 `range_restrict`

English:
theorem range_restrict
  given: (h : forall x in p, f x in q)
  proof: by
  rw [← Submodule.map_top]; rw [map_restrict]; rw [Submodule.map_top]; rw [p.range_subtype]

中文:
定理 range_restrict
  条件: (h : 对任意 x in p, f x in q)
  证明: by
  rw [← Submodule.map_top]; rw [map_restrict]; rw [Submodule.map_top]; rw [p.range_subtype]

Depends on / 依赖: Submodule, Submodule.map_top, map_restrict, map_top, p.range_subtype, range_subtype
-/
theorem range_restrict (h : forall x in p, f x in q) :
    range (f.restrict h) = comap q.subtype (map f p) := by
  rw [← Submodule.map_top]; rw [map_restrict]; rw [Submodule.map_top]; rw [p.range_subtype]

end restrict

end Semiring

end LinearMap
