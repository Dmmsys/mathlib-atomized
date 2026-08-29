/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Algebra.Module.Submodule.LinearMap

/-!
# `map` and `comap` for `Submodule`s

## Main declarations

* `Submodule.map`: The pushforward of a submodule `p ⊆ M` by `f : M → M₂`
* `Submodule.comap`: The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`
* `Submodule.giMapComap`: `map f` and `comap f` form a `GaloisInsertion` when `f` is surjective.
* `Submodule.gciMapComap`: `map f` and `comap f` form a `GaloisCoinsertion` when `f` is injective.

## Tags

submodule, subspace, linear map, pushforward, pullback
-/

@[expose] public section

open Function Pointwise Set

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃}
variable [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable (p p' : Submodule R M) (q q' : Submodule R₂ M₂)
variable {x : M}

section

variable [RingHomSurjective σ₁₂]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  body: { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]

中文:
定义 map
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  定义体: { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]

Depends on / 依赖: carrier, p.smul_mem, p.toAddSubmonoid.map, smul_mem, surjective, toAddSubmonoid
-/
def map (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=
  { p.toAddSubmonoid.map f with
    carrier := f '' p
    smul_mem' := by
      rintro c x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := σ₁₂.surjective c
      exact ⟨_, p.smul_mem a hy, map_smulₛₗ f _ _⟩ }

@[simp]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  statement: (map f p : Set M₂) = f '' p
  proof: rfl

中文:
定理 map_coe
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  结论: (map f p : 集合 M₂) = f '' p
  证明: rfl
-/
theorem map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (map f p : Set M₂) = f '' p :=
  rfl

/--
theorem `map_toAddSubmonoid` / 定理 `map_toAddSubmonoid`

English:
theorem map_toAddSubmonoid
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  proof: SetLike.coe_injective rfl

中文:
定理 map_toAddSubmonoid
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toAddSubmonoid (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map (f : M ->+ M₂) :=
  SetLike.coe_injective rfl

/--
theorem `map_toAddSubmonoid'` / 定理 `map_toAddSubmonoid'`

English:
theorem map_toAddSubmonoid'
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  proof: SetLike.coe_injective rfl

@[simp]

中文:
定理 map_toAddSubmonoid'
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  证明: SetLike.coe_injective rfl

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem map_toAddSubmonoid' (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    (p.map f).toAddSubmonoid = p.toAddSubmonoid.map f :=
  SetLike.coe_injective rfl

@[simp]
/--
theorem `_root_.AddMonoidHom.coe_toIntLinearMap_map` / 定理 `_root_.AddMonoidHom.coe_toIntLinearMap_map`

English:
theorem _root_.AddMonoidHom.coe_toIntLinearMap_map
  statement: {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
  proof: rfl

@[simp]

中文:
定理 _root_.加法幺半群态射.coe_to整数LinearMap_map
  结论: {A A₂ : 类型} [加法交换群 A] [加法交换群 A₂]
  证明: rfl

@[simp]
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_map {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A ->+ A₂) (s : AddSubgroup A) :
    (AddSubgroup.toIntSubmodule s).map f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.map f) := rfl

@[simp]
/--
theorem `_root_.MonoidHom.coe_toAdditive_map` / 定理 `_root_.MonoidHom.coe_toAdditive_map`

English:
theorem _root_.MonoidHom.coe_toAdditive_map
  statement: {G G₂ : Type*} [Group G] [Group G₂] (f : G ->* G₂)
  proof: rfl

@[simp]

中文:
定理 _root_.幺半群态射.coe_toAdditive_map
  结论: {G G₂ : 类型} [群 G] [群 G₂] (f : G ->* G₂)
  证明: rfl

@[simp]
-/
theorem _root_.MonoidHom.coe_toAdditive_map {G G₂ : Type*} [Group G] [Group G₂] (f : G ->* G₂)
    (s : Subgroup G) :
    s.toAddSubgroup.map (MonoidHom.toAdditive f) = Subgroup.toAddSubgroup (s.map f) := rfl

@[simp]
/--
theorem `_root_.AddMonoidHom.coe_toMultiplicative_map` / 定理 `_root_.AddMonoidHom.coe_toMultiplicative_map`

English:
theorem _root_.AddMonoidHom.coe_toMultiplicative_map
  statement: {G G₂ : Type*} [AddGroup G] [AddGroup G₂]
  proof: rfl

@[simp]

中文:
定理 _root_.加法幺半群态射.coe_toMultiplicative_map
  结论: {G G₂ : 类型} [加法群 G] [加法群 G₂]
  证明: rfl

@[simp]
-/
theorem _root_.AddMonoidHom.coe_toMultiplicative_map {G G₂ : Type*} [AddGroup G] [AddGroup G₂]
    (f : G ->+ G₂) (s : AddSubgroup G) :
    s.toSubgroup.map (AddMonoidHom.toMultiplicative f) = AddSubgroup.toSubgroup (s.map f) := rfl

@[simp]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  given: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂}
  proof: Iff.rfl

中文:
定理 mem_map
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {p : 子模 R M} {x : M₂}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x : M₂} :
    x in map f p ↔ exists y, y in p ∧ f y = x :=
  Iff.rfl

/--
theorem `mem_map_of_mem` / 定理 `mem_map_of_mem`

English:
theorem mem_map_of_mem
  given: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r in p)
  statement: f r in map f p
  proof: Set.mem_image_of_mem _ h

中文:
定理 mem_map_of_mem
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {p : 子模 R M} {r} (h : r in p)
  结论: f r in map f p
  证明: Set.mem_image_of_mem _ h

Depends on / 依赖: Set.mem_image_of_mem, mem_image_of_mem
-/
theorem mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {r} (h : r in p) : f r in map f p :=
  Set.mem_image_of_mem _ h

/--
theorem `apply_coe_mem_map` / 定理 `apply_coe_mem_map`

English:
theorem apply_coe_mem_map
  given: (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p)
  statement: f r in map f p
  proof: mem_map_of_mem r.prop

@[simp]

中文:
定理 apply_coe_mem_map
  条件: (f : M ->ₛₗ[σ₁₂] M₂) {p : 子模 R M} (r : p)
  结论: f r in map f p
  证明: mem_map_of_mem r.prop

@[simp]

Depends on / 依赖: mem_map_of_mem, r.prop
-/
theorem apply_coe_mem_map (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M} (r : p) : f r in map f p :=
  mem_map_of_mem r.prop

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (LinearMap.id : M ->ₗ[R] M) p = p
  proof: Submodule.ext fun a => by simp

中文:
定理 map_id
  结论: map (线性映射.id : M ->ₗ[R] M) p = p
  证明: Submodule.ext fun a => by simp

Depends on / 依赖: Submodule, Submodule.ext
-/
theorem map_id : map (LinearMap.id : M ->ₗ[R] M) p = p :=
  Submodule.ext fun a => by simp

/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂)
  proof: SetLike.coe_injective by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]

@[gcongr]

中文:
定理 map_comp
  结论: [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂)
  证明: SetLike.coe_injective by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]

@[gcongr]

Depends on / 依赖: LinearMap, LinearMap.coe_comp, SetLike, SetLike.coe_injective, coe_comp, coe_injective, comp_apply, image_comp, map_coe
-/
theorem map_comp [RingHomSurjective σ₂₃] [RingHomSurjective σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂)
    (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = map g (map f p) :=
SetLike.coe_injective by simp only [← image_comp, map_coe, LinearMap.coe_comp, comp_apply]

@[gcongr]
/--
theorem `map_mono` / 定理 `map_mono`

English:
theorem map_mono
  given: {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
  statement: p <= p' -> map f p <= map f p'
  proof: image_mono

@[simp]

中文:
定理 map_mono
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {p p' : 子模 R M}
  结论: p <= p' -> map f p <= map f p'
  证明: image_mono

@[simp]

Depends on / 依赖: image_mono
-/
theorem map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M} : p <= p' -> map f p <= map f p' :=
  image_mono

@[simp]
/--
theorem `map_zero` / 定理 `map_zero`

English:
theorem map_zero
  statement: map (0 : M ->ₛₗ[σ₁₂] M₂) p = ⊥
  proof: have : exists x : M, x in p := ⟨0, p.zero_mem⟩
ext by simp [this, eq_comm]

中文:
定理 map_zero
  结论: map (0 : M ->ₛₗ[σ₁₂] M₂) p = ⊥
  证明: have : exists x : M, x in p := ⟨0, p.zero_mem⟩
ext by simp [this, eq_comm]
-/
protected theorem map_zero : map (0 : M ->ₛₗ[σ₁₂] M₂) p = ⊥ :=
  have : exists x : M, x in p := ⟨0, p.zero_mem⟩
ext by simp [this, eq_comm]

/--
theorem `map_add_le` / 定理 `map_add_le`

English:
theorem map_add_le
  given: (f g : M ->ₛₗ[σ₁₂] M₂)
  statement: map (f + g) p <= map f p ⊔ map g p
  proof: by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)

中文:
定理 map_add_le
  条件: (f g : M ->ₛₗ[σ₁₂] M₂)
  结论: map (f + g) p <= map f p ⊔ map g p
  证明: by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)

Depends on / 依赖: add_mem_sup, mem_map_of_mem
-/
theorem map_add_le (f g : M ->ₛₗ[σ₁₂] M₂) : map (f + g) p <= map f p ⊔ map g p := by
  rintro x ⟨m, hm, rfl⟩
  exact add_mem_sup (mem_map_of_mem hm) (mem_map_of_mem hm)

/--
theorem `map_inf_le` / 定理 `map_inf_le`

English:
theorem map_inf_le
  given: (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M}
  proof: image_inter_subset f p q

中文:
定理 map_inf_le
  条件: (f : M ->ₛₗ[σ₁₂] M₂) {p q : 子模 R M}
  证明: image_inter_subset f p q

Depends on / 依赖: image_inter_subset
-/
theorem map_inf_le (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} :
    (p ⊓ q).map f <= p.map f ⊓ q.map f :=
  image_inter_subset f p q

/--
theorem `map_inf` / 定理 `map_inf`

English:
theorem map_inf
  given: (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (hf : Injective f)
  proof: SetLike.coe_injective Set.image_inter hf

中文:
定理 map_inf
  条件: (f : M ->ₛₗ[σ₁₂] M₂) {p q : 子模 R M} (hf : 单射 f)
  证明: SetLike.coe_injective Set.image_inter hf

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_injective, coe_injective, image_inter
-/
theorem map_inf (f : M ->ₛₗ[σ₁₂] M₂) {p q : Submodule R M} (hf : Injective f) :
    (p ⊓ q).map f = p.map f ⊓ q.map f :=
SetLike.coe_injective Set.image_inter hf

/--
lemma `map_iInf` / 引理 `map_iInf`

English:
lemma map_iInf
  statement: {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (f : M ->ₛₗ[σ₁₂] M₂)
  proof: SetLike.coe_injective by simpa only [map_coe, coe_iInf] using hf.injOn.image_iInter_eq

中文:
引理 map_iInf
  结论: {ι : 类型层*} [非空 ι] {p : ι -> 子模 R M} (f : M ->ₛₗ[σ₁₂] M₂)
  证明: SetLike.coe_injective by simpa only [map_coe, coe_iInf] using hf.injOn.image_iInter_eq

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_iInf, coe_injective, hf.injOn.image_iInter_eq, image_iInter_eq, map_coe
-/
lemma map_iInf {ι : Sort*} [Nonempty ι] {p : ι -> Submodule R M} (f : M ->ₛₗ[σ₁₂] M₂)
    (hf : Injective f) : (⨅ i, p i).map f = ⨅ i, (p i).map f :=
SetLike.coe_injective by simpa only [map_coe, coe_iInf] using hf.injOn.image_iInter_eq

/--
theorem `range_map_nonempty` / 定理 `range_map_nonempty`

English:
theorem range_map_nonempty
  given: (N : Submodule R M)
  proof: ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

中文:
定理 range_map_nonempty
  条件: (N : 子模 R M)
  证明: ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

Depends on / 依赖: Set.mem_range.mpr, mem_range
-/
theorem range_map_nonempty (N : Submodule R M) :
    (Set.range (fun ϕ => Submodule.map ϕ N : (M ->ₛₗ[σ₁₂] M₂) -> Submodule R₂ M₂)).Nonempty :=
  ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩

end

section SemilinearMap

variable {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/--
Definition of `equivMapOfInjective` / `equivMapOfInjective` 的定义

English:
definition equivMapOfInjective
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
  body: { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }

@[simp]

中文:
定义 equivMapOfInjective
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (i : 单射 f) (p : 子模 R M)
  定义体: { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }

@[simp]

Depends on / 依赖: Equiv.Set.image, Equiv.Set.image_apply, Equiv.toFun_as_coe, coe_add, image_apply, intros, map_add, map_smul, toFun_as_coe
-/
noncomputable def equivMapOfInjective (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M) :
    p ≃ₛₗ[σ₁₂] p.map f :=
  { Equiv.Set.image f p i with
    map_add' := by
      intros
      simp only [coe_add, map_add, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl
    map_smul' := by
      intros
      -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` into `map_smulₛₗ _`
      simp only [coe_smul_of_tower, map_smulₛₗ _, Equiv.toFun_as_coe, Equiv.Set.image_apply]
      rfl }

@[simp]
/--
theorem `coe_equivMapOfInjective_apply` / 定理 `coe_equivMapOfInjective_apply`

English:
theorem coe_equivMapOfInjective_apply
  statement: (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
  proof: rfl

@[simp]

中文:
定理 coe_equivMapOfInjective_apply
  结论: (f : M ->ₛₗ[σ₁₂] M₂) (i : 单射 f) (p : 子模 R M)
  证明: rfl

@[simp]
-/
theorem coe_equivMapOfInjective_apply (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p) : (equivMapOfInjective f i p x : M₂) = f x :=
  rfl

@[simp]
/--
theorem `map_equivMapOfInjective_symm_apply` / 定理 `map_equivMapOfInjective_symm_apply`

English:
theorem map_equivMapOfInjective_symm_apply
  statement: (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
  proof: by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x]; rw [coe_equivMapOfInjective_apply]; rw [i.eq_iff]; rw [LinearEquiv.apply_symm_apply]

中文:
定理 map_equivMapOfInjective_symm_apply
  结论: (f : M ->ₛₗ[σ₁₂] M₂) (i : 单射 f) (p : 子模 R M)
  证明: by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x]; rw [coe_equivMapOfInjective_apply]; rw [i.eq_iff]; rw [LinearEquiv.apply_symm_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.apply_symm_apply, apply_symm_apply, coe_equivMapOfInjective_apply, eq_iff, equivMapOfInjective, i.eq_iff
-/
theorem map_equivMapOfInjective_symm_apply (f : M ->ₛₗ[σ₁₂] M₂) (i : Injective f) (p : Submodule R M)
    (x : p.map f) : f ((equivMapOfInjective f i p).symm x) = x := by
  rw [← LinearEquiv.apply_symm_apply (equivMapOfInjective f i p) x]; rw [coe_equivMapOfInjective_apply]; rw [i.eq_iff]; rw [LinearEquiv.apply_symm_apply]

/-- The pullback of a submodule `p ⊆ M₂` along `f : M → M₂` -/
@[implicit_reducible]
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
  body: { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]

中文:
定义 comap
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R₂ M₂)
  定义体: { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]

Depends on / 依赖: carrier, p.toAddSubmonoid.comap, toAddSubmonoid
-/
def comap (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=
  { p.toAddSubmonoid.comap f with
    carrier := f ⁻¹' p
    -- Note: https://github.com/leanprover-community/mathlib4/pull/8386 added `map_smulₛₗ _`
    smul_mem' := fun a x h => by simp [p.smul_mem (σ₁₂ a) h, map_smulₛₗ _] }

@[simp]
/--
theorem `comap_coe` / 定理 `comap_coe`

English:
theorem comap_coe
  given: (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
  statement: (comap f p : Set M) = f ⁻¹' p
  proof: rfl

@[simp]

中文:
定理 comap_coe
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R₂ M₂)
  结论: (comap f p : 集合 M) = f ⁻¹' p
  证明: rfl

@[simp]
-/
theorem comap_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : (comap f p : Set M) = f ⁻¹' p :=
  rfl

@[simp]
/--
theorem `AddMonoidHom.coe_toIntLinearMap_comap` / 定理 `AddMonoidHom.coe_toIntLinearMap_comap`

English:
theorem AddMonoidHom.coe_toIntLinearMap_comap
  statement: {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
  proof: rfl

@[simp]

中文:
定理 加法幺半群态射.coe_to整数LinearMap_comap
  结论: {A A₂ : 类型} [加法交换群 A] [加法交换群 A₂]
  证明: rfl

@[simp]
-/
theorem AddMonoidHom.coe_toIntLinearMap_comap {A A₂ : Type*} [AddCommGroup A] [AddCommGroup A₂]
    (f : A ->+ A₂) (s : AddSubgroup A₂) :
    (AddSubgroup.toIntSubmodule s).comap f.toIntLinearMap =
      AddSubgroup.toIntSubmodule (s.comap f) := rfl

@[simp]
/--
theorem `mem_comap` / 定理 `mem_comap`

English:
theorem mem_comap
  given: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂}
  statement: x in comap f p ↔ f x in p
  proof: Iff.rfl

@[simp]

中文:
定理 mem_comap
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {p : 子模 R₂ M₂}
  结论: x in comap f p ↔ f x in p
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂} : x in comap f p ↔ f x in p :=
  Iff.rfl

@[simp]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  statement: comap (LinearMap.id : M ->ₗ[R] M) p = p
  proof: SetLike.coe_injective rfl

中文:
定理 comap_id
  结论: comap (线性映射.id : M ->ₗ[R] M) p = p
  证明: SetLike.coe_injective rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
theorem comap_id : comap (LinearMap.id : M ->ₗ[R] M) p = p :=
  SetLike.coe_injective rfl

/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃)
  proof: rfl

@[gcongr]

中文:
定理 comap_comp
  条件: (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : 子模 R₃ M₃)
  证明: rfl

@[gcongr]
-/
theorem comap_comp (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R₃ M₃) :
    comap (g.comp f : M ->ₛₗ[σ₁₃] M₃) p = comap f (comap g p) :=
  rfl

@[gcongr]
/--
theorem `comap_mono` / 定理 `comap_mono`

English:
theorem comap_mono
  given: {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂}
  statement: q <= q' -> comap f q <= comap f q'
  proof: preimage_mono

中文:
定理 comap_mono
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {q q' : 子模 R₂ M₂}
  结论: q <= q' -> comap f q <= comap f q'
  证明: preimage_mono

Depends on / 依赖: preimage_mono
-/
theorem comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule R₂ M₂} : q <= q' -> comap f q <= comap f q' :=
  preimage_mono

/--
theorem `le_comap_pow_of_le_comap` / 定理 `le_comap_pow_of_le_comap`

English:
theorem le_comap_pow_of_le_comap
  statement: (p : Submodule R M) {f : M ->ₗ[R] M}
  proof: by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, comap_comp, h.trans (comap_mono ih)]

中文:
定理 le_comap_pow_of_le_comap
  结论: (p : 子模 R M) {f : M ->ₗ[R] M}
  证明: by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, comap_comp, h.trans (comap_mono ih)]

Depends on / 依赖: Module, Module.End.iterate_succ, Module.End.one_eq_id, comap_comp, comap_mono, h.trans, iterate_succ, one_eq_id
-/
theorem le_comap_pow_of_le_comap (p : Submodule R M) {f : M ->ₗ[R] M}
    (h : p <= p.comap f) (k : Nat) : p <= p.comap (f ^ k) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ k ih => simp [Module.End.iterate_succ, comap_comp, h.trans (comap_mono ih)]

section

variable [RingHomSurjective σ₁₂]

/--
theorem `map_le_iff_le_comap` / 定理 `map_le_iff_le_comap`

English:
theorem map_le_iff_le_comap
  given: {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: image_subset_iff

中文:
定理 map_le_iff_le_comap
  条件: {f : M ->ₛₗ[σ₁₂] M₂} {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: image_subset_iff

Depends on / 依赖: image_subset_iff
-/
theorem map_le_iff_le_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {q : Submodule R₂ M₂} :
    map f p <= q ↔ p <= comap f q :=
  image_subset_iff

/--
theorem `gc_map_comap` / 定理 `gc_map_comap`

English:
theorem gc_map_comap
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: GaloisConnection (map f) (comap f)

中文:
定理 gc_map_comap
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: GaloisConnection (map f) (comap f)
-/
theorem gc_map_comap (f : M ->ₛₗ[σ₁₂] M₂) : GaloisConnection (map f) (comap f)
  | _, _ => map_le_iff_le_comap

@[simp]
/--
theorem `map_bot` / 定理 `map_bot`

English:
theorem map_bot
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: map f ⊥ = ⊥
  proof: (gc_map_comap f).l_bot

@[simp]

中文:
定理 map_bot
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: map f ⊥ = ⊥
  证明: (gc_map_comap f).l_bot

@[simp]

Depends on / 依赖: gc_map_comap, l_bot
-/
theorem map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥ :=
  (gc_map_comap f).l_bot

@[simp]
/--
theorem `map_sup` / 定理 `map_sup`

English:
theorem map_sup
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: map f (p ⊔ p') = map f p ⊔ map f p'
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[simp]

中文:
定理 map_sup
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: map f (p ⊔ p') = map f p ⊔ map f p'
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[simp]

Depends on / 依赖: GaloisConnection, gc_map_comap, l_sup
-/
theorem map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f p ⊔ map f p' :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_sup

@[simp]
/--
theorem `map_iSup` / 定理 `map_iSup`

English:
theorem map_iSup
  given: {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> Submodule R M)
  proof: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

中文:
定理 map_iSup
  条件: {ι : 类型层*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 子模 R M)
  证明: (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

Depends on / 依赖: GaloisConnection, gc_map_comap, l_iSup
-/
theorem map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> Submodule R M) :
    map f (⨆ i, p i) = ⨆ i, map f (p i) :=
  (gc_map_comap f : GaloisConnection (map f) (comap f)).l_iSup

/--
lemma `disjoint_map` / 引理 `disjoint_map`

English:
lemma disjoint_map
  statement: {f : M ->ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) {p q : Submodule R M}
  proof: by
  rw [disjoint_iff]; rw [← map_inf f hf]; rw [disjoint_iff.mp hpq]; rw [map_bot]

中文:
引理 disjoint_map
  结论: {f : M ->ₛₗ[σ₁₂] M₂} (hf : 函数.单射 f) {p q : 子模 R M}
  证明: by
  rw [disjoint_iff]; rw [← map_inf f hf]; rw [disjoint_iff.mp hpq]; rw [map_bot]

Depends on / 依赖: disjoint_iff, disjoint_iff.mp, map_bot, map_inf
-/
lemma disjoint_map {f : M ->ₛₗ[σ₁₂] M₂} (hf : Function.Injective f) {p q : Submodule R M}
    (hpq : Disjoint p q) : Disjoint (p.map f) (q.map f) := by
  rw [disjoint_iff]; rw [← map_inf f hf]; rw [disjoint_iff.mp hpq]; rw [map_bot]

end

@[simp]
/--
theorem `comap_top` / 定理 `comap_top`

English:
theorem comap_top
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: comap f ⊤ = ⊤
  proof: rfl

@[simp]

中文:
定理 comap_top
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: comap f ⊤ = ⊤
  证明: rfl

@[simp]
-/
theorem comap_top (f : M ->ₛₗ[σ₁₂] M₂) : comap f ⊤ = ⊤ :=
  rfl

@[simp]
/--
theorem `comap_inf` / 定理 `comap_inf`

English:
theorem comap_inf
  given: (f : M ->ₛₗ[σ₁₂] M₂)
  statement: comap f (q ⊓ q') = comap f q ⊓ comap f q'
  proof: rfl

@[simp]

中文:
定理 comap_inf
  条件: (f : M ->ₛₗ[σ₁₂] M₂)
  结论: comap f (q ⊓ q') = comap f q ⊓ comap f q'
  证明: rfl

@[simp]
-/
theorem comap_inf (f : M ->ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') = comap f q ⊓ comap f q' :=
  rfl

@[simp]
/--
theorem `comap_iInf` / 定理 `comap_iInf`

English:
theorem comap_iInf
  statement: {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂)
  proof: by
  ext
  simp

@[simp]

中文:
定理 comap_iInf
  结论: {ι : 类型层*} (f : M ->ₛₗ[σ₁₂] M₂)
  证明: by
  ext
  simp

@[simp]
-/
theorem comap_iInf {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂)
    (p : ι -> Submodule R₂ M₂) : comap f (⨅ i, p i) = ⨅ i, comap f (p i) := by
  ext
  simp

@[simp]
/--
theorem `comap_finsetInf` / 定理 `comap_finsetInf`

English:
theorem comap_finsetInf
  statement: {ι : Type*} (f : M ->ₛₗ[σ₁₂] M₂)
  proof: by
  simp [Finset.inf_eq_iInf]

@[simp]

中文:
定理 comap_finsetInf
  结论: {ι : 类型} (f : M ->ₛₗ[σ₁₂] M₂)
  证明: by
  simp [Finset.inf_eq_iInf]

@[simp]

Depends on / 依赖: Finset, Finset.inf_eq_iInf, inf_eq_iInf
-/
theorem comap_finsetInf {ι : Type*} (f : M ->ₛₗ[σ₁₂] M₂)
    (s : Finset ι) (p : ι -> Submodule R₂ M₂) : comap f (s.inf p) = s.inf fun i => comap f (p i) := by
  simp [Finset.inf_eq_iInf]

@[simp]
/--
theorem `comap_zero` / 定理 `comap_zero`

English:
theorem comap_zero
  statement: comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤
  proof: ext by simp

中文:
定理 comap_zero
  结论: comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤
  证明: ext by simp
-/
theorem comap_zero : comap (0 : M ->ₛₗ[σ₁₂] M₂) q = ⊤ :=
ext by simp

/--
theorem `map_comap_le` / 定理 `map_comap_le`

English:
theorem map_comap_le
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
  proof: (gc_map_comap f).l_u_le _

中文:
定理 map_comap_le
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (q : 子模 R₂ M₂)
  证明: (gc_map_comap f).l_u_le _

Depends on / 依赖: gc_map_comap, l_u_le
-/
theorem map_comap_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) :
    map f (comap f q) <= q :=
  (gc_map_comap f).l_u_le _

/--
theorem `le_comap_map` / 定理 `le_comap_map`

English:
theorem le_comap_map
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  proof: (gc_map_comap f).le_u_l _

中文:
定理 le_comap_map
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  证明: (gc_map_comap f).le_u_l _

Depends on / 依赖: gc_map_comap, le_u_l
-/
theorem le_comap_map [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p <= comap f (map f p) :=
  (gc_map_comap f).le_u_l _

section submoduleOf

/--
Definition of `submoduleOf` / `submoduleOf` 的定义

English:
definition submoduleOf
  signature: (p q : Submodule R M)
  body: Submodule.comap q.subtype p

中文:
定义 submoduleOf
  签名: (p q : 子模 R M)
  定义体: Submodule.comap q.subtype p

Depends on / 依赖: Submodule, Submodule.comap, q.subtype, subtype
-/
def submoduleOf (p q : Submodule R M) : Submodule R q :=
  Submodule.comap q.subtype p

/--
Definition of `submoduleOfEquivOfLe` / `submoduleOfEquivOfLe` 的定义

English:
definition submoduleOfEquivOfLe
  signature: {p q : Submodule R M} (h : p <= q)
  body: ⟨m.1, m.2⟩
  invFun m := ⟨⟨m.1, h m.2⟩, m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 submoduleOfEquivOfLe
  签名: {p q : 子模 R M} (h : p <= q)
  定义体: ⟨m.1, m.2⟩
  invFun m := ⟨⟨m.1, h m.2⟩, m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def submoduleOfEquivOfLe {p q : Submodule R M} (h : p <= q) : p.submoduleOf q ≃ₗ[R] p where
  toFun m := ⟨m.1, m.2⟩
  invFun m := ⟨⟨m.1, h m.2⟩, m.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end submoduleOf

section GaloisInsertion

variable [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂}

/--
Definition of `giMapComap` / `giMapComap` 的定义

English:
definition giMapComap
  signature: (hf : Surjective f)
  body: (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩

中文:
定义 giMapComap
  签名: (hf : 满射 f)
  定义体: (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩

Depends on / 依赖: gc_map_comap, mem_comap, mem_map, toGaloisInsertion
-/
def giMapComap (hf : Surjective f) : GaloisInsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisInsertion fun S x hx => by
    rcases hf x with ⟨y, rfl⟩
    simp only [mem_map, mem_comap]
    exact ⟨y, hx, rfl⟩

variable (hf : Surjective f)
include hf

/--
theorem `map_comap_eq_of_surjective` / 定理 `map_comap_eq_of_surjective`

English:
theorem map_comap_eq_of_surjective
  given: (p : Submodule R₂ M₂)
  statement: (p.comap f).map f = p
  proof: (giMapComap hf).l_u_eq _

中文:
定理 map_comap_eq_of_surjective
  条件: (p : 子模 R₂ M₂)
  结论: (p.comap f).map f = p
  证明: (giMapComap hf).l_u_eq _

Depends on / 依赖: giMapComap, l_u_eq
-/
theorem map_comap_eq_of_surjective (p : Submodule R₂ M₂) : (p.comap f).map f = p :=
  (giMapComap hf).l_u_eq _

/--
theorem `map_surjective_of_surjective` / 定理 `map_surjective_of_surjective`

English:
theorem map_surjective_of_surjective
  statement: Function.Surjective (map f)
  proof: (giMapComap hf).l_surjective

中文:
定理 map_surjective_of_surjective
  结论: 函数.满射 (map f)
  证明: (giMapComap hf).l_surjective

Depends on / 依赖: giMapComap, l_surjective
-/
theorem map_surjective_of_surjective : Function.Surjective (map f) :=
  (giMapComap hf).l_surjective

/--
theorem `comap_injective_of_surjective` / 定理 `comap_injective_of_surjective`

English:
theorem comap_injective_of_surjective
  statement: Function.Injective (comap f)
  proof: (giMapComap hf).u_injective

中文:
定理 comap_injective_of_surjective
  结论: 函数.单射 (comap f)
  证明: (giMapComap hf).u_injective

Depends on / 依赖: giMapComap, u_injective
-/
theorem comap_injective_of_surjective : Function.Injective (comap f) :=
  (giMapComap hf).u_injective

/--
theorem `map_sup_comap_of_surjective` / 定理 `map_sup_comap_of_surjective`

English:
theorem map_sup_comap_of_surjective
  given: (p q : Submodule R₂ M₂)
  proof: (giMapComap hf).l_sup_u _ _

中文:
定理 map_sup_comap_of_surjective
  条件: (p q : 子模 R₂ M₂)
  证明: (giMapComap hf).l_sup_u _ _

Depends on / 依赖: giMapComap, l_sup_u
-/
theorem map_sup_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊔ q.comap f).map f = p ⊔ q :=
  (giMapComap hf).l_sup_u _ _

/--
theorem `map_iSup_comap_of_surjective` / 定理 `map_iSup_comap_of_surjective`

English:
theorem map_iSup_comap_of_surjective
  given: {ι : Sort*} (S : ι -> Submodule R₂ M₂)
  proof: (giMapComap hf).l_iSup_u _

中文:
定理 map_iSup_comap_of_surjective
  条件: {ι : 类型层*} (S : ι -> 子模 R₂ M₂)
  证明: (giMapComap hf).l_iSup_u _

Depends on / 依赖: giMapComap, l_iSup_u
-/
theorem map_iSup_comap_of_surjective {ι : Sort*} (S : ι -> Submodule R₂ M₂) :
    (⨆ i, (S i).comap f).map f = iSup S :=
  (giMapComap hf).l_iSup_u _

/--
theorem `map_inf_comap_of_surjective` / 定理 `map_inf_comap_of_surjective`

English:
theorem map_inf_comap_of_surjective
  given: (p q : Submodule R₂ M₂)
  proof: (giMapComap hf).l_inf_u _ _

中文:
定理 map_inf_comap_of_surjective
  条件: (p q : 子模 R₂ M₂)
  证明: (giMapComap hf).l_inf_u _ _

Depends on / 依赖: giMapComap, l_inf_u
-/
theorem map_inf_comap_of_surjective (p q : Submodule R₂ M₂) :
    (p.comap f ⊓ q.comap f).map f = p ⊓ q :=
  (giMapComap hf).l_inf_u _ _

/--
theorem `map_iInf_comap_of_surjective` / 定理 `map_iInf_comap_of_surjective`

English:
theorem map_iInf_comap_of_surjective
  given: {ι : Sort*} (S : ι -> Submodule R₂ M₂)
  proof: (giMapComap hf).l_iInf_u _

中文:
定理 map_iInf_comap_of_surjective
  条件: {ι : 类型层*} (S : ι -> 子模 R₂ M₂)
  证明: (giMapComap hf).l_iInf_u _

Depends on / 依赖: giMapComap, l_iInf_u
-/
theorem map_iInf_comap_of_surjective {ι : Sort*} (S : ι -> Submodule R₂ M₂) :
    (⨅ i, (S i).comap f).map f = iInf S :=
  (giMapComap hf).l_iInf_u _

/--
theorem `comap_le_comap_iff_of_surjective` / 定理 `comap_le_comap_iff_of_surjective`

English:
theorem comap_le_comap_iff_of_surjective
  given: {p q : Submodule R₂ M₂}
  statement: p.comap f <= q.comap f ↔ p <= q
  proof: (giMapComap hf).u_le_u_iff

中文:
定理 comap_le_comap_iff_of_surjective
  条件: {p q : 子模 R₂ M₂}
  结论: p.comap f <= q.comap f ↔ p <= q
  证明: (giMapComap hf).u_le_u_iff

Depends on / 依赖: giMapComap, u_le_u_iff
-/
theorem comap_le_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f <= q.comap f ↔ p <= q :=
  (giMapComap hf).u_le_u_iff

/--
lemma `comap_lt_comap_iff_of_surjective` / 引理 `comap_lt_comap_iff_of_surjective`

English:
lemma comap_lt_comap_iff_of_surjective
  given: {p q : Submodule R₂ M₂}
  statement: p.comap f < q.comap f ↔ p < q
  proof: by
  apply lt_iff_lt_of_le_iff_le' <;> exact comap_le_comap_iff_of_surjective hf

中文:
引理 comap_lt_comap_iff_of_surjective
  条件: {p q : 子模 R₂ M₂}
  结论: p.comap f < q.comap f ↔ p < q
  证明: by
  apply lt_iff_lt_of_le_iff_le' <;> exact comap_le_comap_iff_of_surjective hf

Depends on / 依赖: comap_le_comap_iff_of_surjective, lt_iff_lt_of_le_iff_le
-/
lemma comap_lt_comap_iff_of_surjective {p q : Submodule R₂ M₂} : p.comap f < q.comap f ↔ p < q := by
  apply lt_iff_lt_of_le_iff_le' <;> exact comap_le_comap_iff_of_surjective hf

/--
theorem `comap_strictMono_of_surjective` / 定理 `comap_strictMono_of_surjective`

English:
theorem comap_strictMono_of_surjective
  statement: StrictMono (comap f)
  proof: (giMapComap hf).strictMono_u

中文:
定理 comap_strictMono_of_surjective
  结论: 严格递增 (comap f)
  证明: (giMapComap hf).strictMono_u

Depends on / 依赖: giMapComap, strictMono_u
-/
theorem comap_strictMono_of_surjective : StrictMono (comap f) :=
  (giMapComap hf).strictMono_u

variable {p q}

/--
theorem `le_map_of_comap_le_of_surjective` / 定理 `le_map_of_comap_le_of_surjective`

English:
theorem le_map_of_comap_le_of_surjective
  given: (h : q.comap f <= p)
  statement: q <= p.map f
  proof: map_comap_eq_of_surjective hf q ▸ map_mono h

中文:
定理 le_map_of_comap_le_of_surjective
  条件: (h : q.comap f <= p)
  结论: q <= p.map f
  证明: map_comap_eq_of_surjective hf q ▸ map_mono h

Depends on / 依赖: map_comap_eq_of_surjective, map_mono
-/
theorem le_map_of_comap_le_of_surjective (h : q.comap f <= p) : q <= p.map f :=
  map_comap_eq_of_surjective hf q ▸ map_mono h

/--
theorem `lt_map_of_comap_lt_of_surjective` / 定理 `lt_map_of_comap_lt_of_surjective`

English:
theorem lt_map_of_comap_lt_of_surjective
  given: (h : q.comap f < p)
  statement: q < p.map f
  proof: by
  rw [lt_iff_le_not_ge] at h ⊢; rw [map_le_iff_le_comap]
  exact h.imp_left (le_map_of_comap_le_of_surjective hf)

中文:
定理 lt_map_of_comap_lt_of_surjective
  条件: (h : q.comap f < p)
  结论: q < p.map f
  证明: by
  rw [lt_iff_le_not_ge] at h ⊢; rw [map_le_iff_le_comap]
  exact h.imp_left (le_map_of_comap_le_of_surjective hf)

Depends on / 依赖: h.imp_left, imp_left, le_map_of_comap_le_of_surjective, lt_iff_le_not_ge, map_le_iff_le_comap
-/
theorem lt_map_of_comap_lt_of_surjective (h : q.comap f < p) : q < p.map f := by
  rw [lt_iff_le_not_ge] at h ⊢; rw [map_le_iff_le_comap]
  exact h.imp_left (le_map_of_comap_le_of_surjective hf)

end GaloisInsertion

section GaloisCoinsertion

variable [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂}

/--
Definition of `gciMapComap` / `gciMapComap` 的定义

English:
definition gciMapComap
  signature: (hf : Injective f)
  body: (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp only [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]

中文:
定义 gciMapComap
  签名: (hf : 单射 f)
  定义体: (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp only [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]

Depends on / 依赖: and_imp, eq_iff, forall_exists_index, gc_map_comap, hf.eq_iff, mem_comap, mem_map, toGaloisCoinsertion
-/
def gciMapComap (hf : Injective f) : GaloisCoinsertion (map f) (comap f) :=
  (gc_map_comap f).toGaloisCoinsertion fun S x => by
    simp only [mem_comap, mem_map, forall_exists_index, and_imp]
    intro y hy hxy
    rw [hf.eq_iff] at hxy
    rwa [← hxy]

variable (hf : Injective f)
include hf

/--
theorem `comap_map_eq_of_injective` / 定理 `comap_map_eq_of_injective`

English:
theorem comap_map_eq_of_injective
  given: (p : Submodule R M)
  statement: (p.map f).comap f = p
  proof: (gciMapComap hf).u_l_eq _

中文:
定理 comap_map_eq_of_injective
  条件: (p : 子模 R M)
  结论: (p.map f).comap f = p
  证明: (gciMapComap hf).u_l_eq _

Depends on / 依赖: gciMapComap, u_l_eq
-/
theorem comap_map_eq_of_injective (p : Submodule R M) : (p.map f).comap f = p :=
  (gciMapComap hf).u_l_eq _

/--
theorem `comap_surjective_of_injective` / 定理 `comap_surjective_of_injective`

English:
theorem comap_surjective_of_injective
  statement: Function.Surjective (comap f)
  proof: (gciMapComap hf).u_surjective

中文:
定理 comap_surjective_of_injective
  结论: 函数.满射 (comap f)
  证明: (gciMapComap hf).u_surjective

Depends on / 依赖: gciMapComap, u_surjective
-/
theorem comap_surjective_of_injective : Function.Surjective (comap f) :=
  (gciMapComap hf).u_surjective

/--
theorem `map_injective_of_injective` / 定理 `map_injective_of_injective`

English:
theorem map_injective_of_injective
  statement: Function.Injective (map f)
  proof: (gciMapComap hf).l_injective

中文:
定理 map_injective_of_injective
  结论: 函数.单射 (map f)
  证明: (gciMapComap hf).l_injective

Depends on / 依赖: gciMapComap, l_injective
-/
theorem map_injective_of_injective : Function.Injective (map f) :=
  (gciMapComap hf).l_injective

/--
theorem `comap_inf_map_of_injective` / 定理 `comap_inf_map_of_injective`

English:
theorem comap_inf_map_of_injective
  given: (p q : Submodule R M)
  statement: (p.map f ⊓ q.map f).comap f = p ⊓ q
  proof: (gciMapComap hf).u_inf_l _ _

中文:
定理 comap_inf_map_of_injective
  条件: (p q : 子模 R M)
  结论: (p.map f ⊓ q.map f).comap f = p ⊓ q
  证明: (gciMapComap hf).u_inf_l _ _

Depends on / 依赖: gciMapComap, u_inf_l
-/
theorem comap_inf_map_of_injective (p q : Submodule R M) : (p.map f ⊓ q.map f).comap f = p ⊓ q :=
  (gciMapComap hf).u_inf_l _ _

/--
theorem `comap_iInf_map_of_injective` / 定理 `comap_iInf_map_of_injective`

English:
theorem comap_iInf_map_of_injective
  given: {ι : Sort*} (S : ι -> Submodule R M)
  proof: (gciMapComap hf).u_iInf_l _

中文:
定理 comap_iInf_map_of_injective
  条件: {ι : 类型层*} (S : ι -> 子模 R M)
  证明: (gciMapComap hf).u_iInf_l _

Depends on / 依赖: gciMapComap, u_iInf_l
-/
theorem comap_iInf_map_of_injective {ι : Sort*} (S : ι -> Submodule R M) :
    (⨅ i, (S i).map f).comap f = iInf S :=
  (gciMapComap hf).u_iInf_l _

/--
theorem `comap_sup_map_of_injective` / 定理 `comap_sup_map_of_injective`

English:
theorem comap_sup_map_of_injective
  given: (p q : Submodule R M)
  statement: (p.map f ⊔ q.map f).comap f = p ⊔ q
  proof: (gciMapComap hf).u_sup_l _ _

中文:
定理 comap_sup_map_of_injective
  条件: (p q : 子模 R M)
  结论: (p.map f ⊔ q.map f).comap f = p ⊔ q
  证明: (gciMapComap hf).u_sup_l _ _

Depends on / 依赖: gciMapComap, u_sup_l
-/
theorem comap_sup_map_of_injective (p q : Submodule R M) : (p.map f ⊔ q.map f).comap f = p ⊔ q :=
  (gciMapComap hf).u_sup_l _ _

/--
theorem `comap_iSup_map_of_injective` / 定理 `comap_iSup_map_of_injective`

English:
theorem comap_iSup_map_of_injective
  given: {ι : Sort*} (S : ι -> Submodule R M)
  proof: (gciMapComap hf).u_iSup_l _

中文:
定理 comap_iSup_map_of_injective
  条件: {ι : 类型层*} (S : ι -> 子模 R M)
  证明: (gciMapComap hf).u_iSup_l _

Depends on / 依赖: algebra_map, gciMapComap, u_iSup_l
-/
theorem comap_iSup_map_of_injective {ι : Sort*} (S : ι -> Submodule R M) :
    (⨆ i, (S i).map f).comap f = iSup S :=
  (gciMapComap hf).u_iSup_l _

/--
theorem `map_le_map_iff_of_injective` / 定理 `map_le_map_iff_of_injective`

English:
theorem map_le_map_iff_of_injective
  given: (p q : Submodule R M)
  statement: p.map f <= q.map f ↔ p <= q
  proof: (gciMapComap hf).l_le_l_iff

中文:
定理 map_le_map_iff_of_injective
  条件: (p q : 子模 R M)
  结论: p.map f <= q.map f ↔ p <= q
  证明: (gciMapComap hf).l_le_l_iff

Depends on / 依赖: gciMapComap, l_le_l_iff
-/
theorem map_le_map_iff_of_injective (p q : Submodule R M) : p.map f <= q.map f ↔ p <= q :=
  (gciMapComap hf).l_le_l_iff

/--
theorem `map_strictMono_of_injective` / 定理 `map_strictMono_of_injective`

English:
theorem map_strictMono_of_injective
  statement: StrictMono (map f)
  proof: (gciMapComap hf).strictMono_l

中文:
定理 map_strictMono_of_injective
  结论: 严格递增 (map f)
  证明: (gciMapComap hf).strictMono_l

Depends on / 依赖: gciMapComap, strictMono_l
-/
theorem map_strictMono_of_injective : StrictMono (map f) :=
  (gciMapComap hf).strictMono_l

/--
lemma `map_lt_map_iff_of_injective` / 引理 `map_lt_map_iff_of_injective`

English:
lemma map_lt_map_iff_of_injective
  given: {p q : Submodule R M}
  proof: by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [map_le_map_iff_of_injective hf]; rw [(map_injective_of_injective hf).ne_iff]

中文:
引理 map_lt_map_iff_of_injective
  条件: {p q : 子模 R M}
  证明: by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [map_le_map_iff_of_injective hf]; rw [(map_injective_of_injective hf).ne_iff]

Depends on / 依赖: lt_iff_le_and_ne, map_injective_of_injective, map_le_map_iff_of_injective, ne_iff
-/
lemma map_lt_map_iff_of_injective {p q : Submodule R M} :
    p.map f < q.map f ↔ p < q := by
  rw [lt_iff_le_and_ne]; rw [lt_iff_le_and_ne]; rw [map_le_map_iff_of_injective hf]; rw [(map_injective_of_injective hf).ne_iff]

/--
lemma `comap_lt_of_lt_map_of_injective` / 引理 `comap_lt_of_lt_map_of_injective`

English:
lemma comap_lt_of_lt_map_of_injective
  statement: {p : Submodule R M} {q : Submodule R₂ M₂}
  proof: by
  rw [← map_lt_map_iff_of_injective hf]
  exact (map_comap_le _ _).trans_lt h

中文:
引理 comap_lt_of_lt_map_of_injective
  结论: {p : 子模 R M} {q : 子模 R₂ M₂}
  证明: by
  rw [← map_lt_map_iff_of_injective hf]
  exact (map_comap_le _ _).trans_lt h

Depends on / 依赖: map_comap_le, map_lt_map_iff_of_injective, trans_lt
-/
lemma comap_lt_of_lt_map_of_injective {p : Submodule R M} {q : Submodule R₂ M₂}
    (h : q < p.map f) : q.comap f < p := by
  rw [← map_lt_map_iff_of_injective hf]
  exact (map_comap_le _ _).trans_lt h

/--
lemma `map_covBy_of_injective` / 引理 `map_covBy_of_injective`

English:
lemma map_covBy_of_injective
  given: {p q : Submodule R M} (h : p ⋖ q)
  proof: by
  refine ⟨lt_of_le_of_ne (map_mono h.1.le) ((map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

中文:
引理 map_covBy_of_injective
  条件: {p q : 子模 R M} (h : p ⋖ q)
  证明: by
  refine ⟨lt_of_le_of_ne (map_mono h.1.le) ((map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

Depends on / 依赖: Set.image_preimage_eq_of_subset, Set.image_subset_range, Submodule, Submodule.comap_lt_of_lt_map_of_injective, Submodule.map_lt_map_iff_of_injective, comap_lt_of_lt_map_of_injective, image_preimage_eq_of_subset, image_subset_range, lt_of_le_of_ne, map_injective_of_injective, map_lt_map_iff_of_injective, map_mono, superset, trans_le
-/
lemma map_covBy_of_injective {p q : Submodule R M} (h : p ⋖ q) :
    p.map f ⋖ q.map f := by
  refine ⟨lt_of_le_of_ne (map_mono h.1.le) ((map_injective_of_injective hf).ne h.1.ne), ?_⟩
  intro P h₁ h₂
  refine h.2 ?_ (Submodule.comap_lt_of_lt_map_of_injective hf h₂)
  rw [← Submodule.map_lt_map_iff_of_injective hf]
  refine h₁.trans_le ?_
  exact (Set.image_preimage_eq_of_subset (.trans h₂.le (Set.image_subset_range _ _))).superset

end GaloisCoinsertion

end SemilinearMap

section OrderIso

variable [RingHomSurjective σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps symm_apply apply]
/--
Definition of `orderIsoMapComapOfBijective` / `orderIsoMapComapOfBijective` 的定义

English:
definition orderIsoMapComapOfBijective
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (hf : Bijective f)
  body: map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

中文:
定义 orderIsoMapComapOfBijective
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (hf : 双射 f)
  定义体: map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _
-/
def orderIsoMapComapOfBijective (f : M ->ₛₗ[σ₁₂] M₂) (hf : Bijective f) :
    Submodule R M ≃o Submodule R₂ M₂ where
  toFun := map f
  invFun := comap f
  left_inv := comap_map_eq_of_injective hf.injective
  right_inv := map_comap_eq_of_surjective hf.surjective
  map_rel_iff' := map_le_map_iff_of_injective hf.injective _ _

variable {σ₂₁ : R₂ ->+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]

/-- A linear isomorphism induces an order isomorphism of submodules. -/
@[simps! apply]
/--
Definition of `orderIsoMapComap` / `orderIsoMapComap` 的定义

English:
definition orderIsoMapComap
  signature: (f : M ≃ₛₗ[σ₁₂] M₂)
  body: orderIsoMapComapOfBijective (f : M ->ₛₗ[σ₁₂] M₂) f.bijective

@[simp]

中文:
定义 orderIsoMapComap
  签名: (f : M ≃ₛₗ[σ₁₂] M₂)
  定义体: orderIsoMapComapOfBijective (f : M ->ₛₗ[σ₁₂] M₂) f.bijective

@[simp]

Depends on / 依赖: bijective, f.bijective, orderIsoMapComapOfBijective
-/
def orderIsoMapComap (f : M ≃ₛₗ[σ₁₂] M₂) :
    Submodule R M ≃o Submodule R₂ M₂ := orderIsoMapComapOfBijective (f : M ->ₛₗ[σ₁₂] M₂) f.bijective

@[simp]
/--
lemma `orderIsoMapComap_symm_apply` / 引理 `orderIsoMapComap_symm_apply`

English:
lemma orderIsoMapComap_symm_apply
  given: (f : M ≃ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂)
  proof: rfl

中文:
引理 orderIsoMapComap_symm_apply
  条件: (f : M ≃ₛₗ[σ₁₂] M₂) (p : 子模 R₂ M₂)
  证明: rfl
-/
lemma orderIsoMapComap_symm_apply (f : M ≃ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap f).symm p = comap (f : M ->ₛₗ[σ₁₂] M₂) p :=
  rfl

variable {e : M ≃ₛₗ[σ₁₂] M₂}
variable {p}

/--
lemma `map_eq_bot_iff` / 引理 `map_eq_bot_iff`

English:
lemma map_eq_bot_iff
  statement: p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊥ ↔ p = ⊥
  proof: map_eq_bot_iff (orderIsoMapComap e)

中文:
引理 map_eq_bot_iff
  结论: p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊥ ↔ p = ⊥
  证明: map_eq_bot_iff (orderIsoMapComap e)
-/
@[simp] protected lemma map_eq_bot_iff : p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊥ ↔ p = ⊥ :=
  map_eq_bot_iff (orderIsoMapComap e)

/--
lemma `map_eq_top_iff` / 引理 `map_eq_top_iff`

English:
lemma map_eq_top_iff
  statement: p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊤ ↔ p = ⊤
  proof: map_eq_top_iff (orderIsoMapComap e)

中文:
引理 map_eq_top_iff
  结论: p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊤ ↔ p = ⊤
  证明: map_eq_top_iff (orderIsoMapComap e)
-/
@[simp] protected lemma map_eq_top_iff : p.map (e : M ->ₛₗ[σ₁₂] M₂) = ⊤ ↔ p = ⊤ :=
  map_eq_top_iff (orderIsoMapComap e)

/--
lemma `map_ne_bot_iff` / 引理 `map_ne_bot_iff`

English:
lemma map_ne_bot_iff
  statement: p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊥ ↔ p != ⊥
  proof: by simp

中文:
引理 map_ne_bot_iff
  结论: p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊥ ↔ p != ⊥
  证明: by simp
-/
protected lemma map_ne_bot_iff : p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊥ ↔ p != ⊥ := by simp

/--
lemma `map_ne_top_iff` / 引理 `map_ne_top_iff`

English:
lemma map_ne_top_iff
  statement: p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊤ ↔ p != ⊤
  proof: by simp

中文:
引理 map_ne_top_iff
  结论: p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊤ ↔ p != ⊤
  证明: by simp
-/
protected lemma map_ne_top_iff : p.map (e : M ->ₛₗ[σ₁₂] M₂) != ⊤ ↔ p != ⊤ := by simp

end OrderIso

--TODO(Mario): is there a way to prove this from order properties?
/--
theorem `map_inf_eq_map_inf_comap` / 定理 `map_inf_eq_map_inf_comap`

English:
theorem map_inf_eq_map_inf_comap
  statement: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
  proof: .symm SetLike.coe_injective image_inter_preimage _ _ _

@[simp]

中文:
定理 map_inf_eq_map_inf_comap
  结论: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : 子模 R M}
  证明: .symm SetLike.coe_injective image_inter_preimage _ _ _

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, image_inter_preimage
-/
theorem map_inf_eq_map_inf_comap [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M}
    {p' : Submodule R₂ M₂} : map f p ⊓ p' = map f (p ⊓ comap f p') :=
.symm SetLike.coe_injective image_inter_preimage _ _ _

@[simp]
/--
theorem `map_comap_subtype` / 定理 `map_comap_subtype`

English:
theorem map_comap_subtype
  statement: map p.subtype (comap p.subtype p') = p ⊓ p'
  proof: ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

中文:
定理 map_comap_subtype
  结论: map p.subtype (comap p.subtype p') = p ⊓ p'
  证明: ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩
-/
theorem map_comap_subtype : map p.subtype (comap p.subtype p') = p ⊓ p' :=
  ext fun x => ⟨by rintro ⟨⟨_, h₁⟩, h₂, rfl⟩; exact ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨⟨_, h₁⟩, h₂, rfl⟩⟩

/--
theorem `eq_zero_of_bot_submodule` / 定理 `eq_zero_of_bot_submodule`

English:
theorem eq_zero_of_bot_submodule
  statement: forall b : (⊥ : Submodule R M), b = 0

中文:
定理 eq_zero_of_bot_submodule
  结论: 对任意 b : (⊥ : 子模 R M), b = 0
-/
theorem eq_zero_of_bot_submodule : forall b : (⊥ : Submodule R M), b = 0
| ⟨b', hb⟩ => Subtype.ext show b' = 0 from (mem_bot R).1 hb

/--
theorem `_root_.LinearMap.iInf_invariant` / 定理 `_root_.LinearMap.iInf_invariant`

English:
theorem _root_.LinearMap.iInf_invariant
  statement: {σ : R ->+* R} {ι : Sort*}
  proof: by
  simp only [mem_iInf]
  exact fun v a i => hf i v (a i)

中文:
定理 _root_.线性映射.iInf_invariant
  结论: {σ : R ->+* R} {ι : 类型层*}
  证明: by
  simp only [mem_iInf]
  exact fun v a i => hf i v (a i)

Depends on / 依赖: mem_iInf
-/
theorem _root_.LinearMap.iInf_invariant {σ : R ->+* R} {ι : Sort*}
    (f : M ->ₛₗ[σ] M) {p : ι -> Submodule R M} (hf : forall i, forall v in p i, f v in p i) :
    forall v in iInf p, f v in iInf p := by
  simp only [mem_iInf]
  exact fun v a i => hf i v (a i)

/--
theorem `disjoint_iff_comap_eq_bot` / 定理 `disjoint_iff_comap_eq_bot`

English:
theorem disjoint_iff_comap_eq_bot
  given: {p q : Submodule R M}
  statement: Disjoint p q ↔ comap p.subtype q = ⊥
  proof: by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff]; rw [map_comap_subtype]; rw [map_bot]; rw [disjoint_iff]

中文:
定理 disjoint_iff_comap_eq_bot
  条件: {p q : 子模 R M}
  结论: Disjoint p q ↔ comap p.subtype q = ⊥
  证明: by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff]; rw [map_comap_subtype]; rw [map_bot]; rw [disjoint_iff]

Depends on / 依赖: Injective, Subtype, Subtype.coe_injective, coe_injective, disjoint_iff, eq_iff, map_bot, map_comap_subtype, map_injective_of_injective, p.subtype, subtype
-/
theorem disjoint_iff_comap_eq_bot {p q : Submodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥ := by
  rw [← (map_injective_of_injective (show Injective p.subtype from Subtype.coe_injective)).eq_iff]; rw [map_comap_subtype]; rw [map_bot]; rw [disjoint_iff]

end AddCommMonoid

section AddCommGroup

variable [Ring R] [AddCommGroup M] [Module R M] (p : Submodule R M)
variable [AddCommGroup M₂] [Module R M₂]

@[simp]
/--
theorem `map_neg` / 定理 `map_neg`

English:
theorem map_neg
  given: (f : M ->ₗ[R] M₂)
  statement: map (-f) p = map f p
  proof: ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x in p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x in p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

@[simp]

中文:
定理 map_neg
  条件: (f : M ->ₗ[R] M₂)
  结论: map (-f) p = map f p
  证明: ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x in p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x in p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

@[simp]
-/
protected theorem map_neg (f : M ->ₗ[R] M₂) : map (-f) p = map f p :=
  ext fun _ =>
    ⟨fun ⟨x, hx, hy⟩ => hy ▸ ⟨-x, show -x in p from neg_mem hx, map_neg f x⟩, fun ⟨x, hx, hy⟩ =>
      hy ▸ ⟨-x, show -x in p from neg_mem hx, (map_neg (-f) _).trans (neg_neg (f x))⟩⟩

@[simp]
/--
lemma `comap_neg` / 引理 `comap_neg`

English:
lemma comap_neg
  given: {f : M ->ₗ[R] M₂} {p : Submodule R M₂}
  proof: by
  ext; simp

中文:
引理 comap_neg
  条件: {f : M ->ₗ[R] M₂} {p : 子模 R M₂}
  证明: by
  ext; simp
-/
lemma comap_neg {f : M ->ₗ[R] M₂} {p : Submodule R M₂} :
    p.comap (-f) = p.comap f := by
  ext; simp

/--
lemma `map_toAddSubgroup` / 引理 `map_toAddSubgroup`

English:
lemma map_toAddSubgroup
  given: (f : M ->ₗ[R] M₂) (p : Submodule R M)
  proof: rfl

中文:
引理 map_toAddSubgroup
  条件: (f : M ->ₗ[R] M₂) (p : 子模 R M)
  证明: rfl
-/
lemma map_toAddSubgroup (f : M ->ₗ[R] M₂) (p : Submodule R M) :
    (p.map f).toAddSubgroup = p.toAddSubgroup.map (f : M ->+ M₂) :=
  rfl

end AddCommGroup

end Submodule

namespace Submodule

variable {K : Type*} {V : Type*} {V₂ : Type*}
variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/--
theorem `comap_smul` / 定理 `comap_smul`

English:
theorem comap_smul
  given: (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a != 0)
  proof: by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]

中文:
定理 comap_smul
  条件: (f : V ->ₗ[K] V₂) (p : 子模 K V₂) (a : K) (h : a != 0)
  证明: by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]

Depends on / 依赖: LinearMap, LinearMap.smul_apply, Submodule, Submodule.mem_comap, mem_comap, p.smul_mem_iff, smul_apply, smul_mem_iff
-/
theorem comap_smul (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K) (h : a != 0) :
    p.comap (a • f) = p.comap f := by
  ext b; simp only [Submodule.mem_comap, p.smul_mem_iff h, LinearMap.smul_apply]

/--
theorem `map_smul` / 定理 `map_smul`

English:
theorem map_smul
  given: (f : V ->ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a != 0)
  proof: le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])

中文:
定理 map_smul
  条件: (f : V ->ₗ[K] V₂) (p : 子模 K V) (a : K) (h : a != 0)
  证明: le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])
-/
protected theorem map_smul (f : V ->ₗ[K] V₂) (p : Submodule K V) (a : K) (h : a != 0) :
    p.map (a • f) = p.map f :=
  le_antisymm (by rw [map_le_iff_le_comap, comap_smul f _ a h, ← map_le_iff_le_comap])
    (by rw [map_le_iff_le_comap, ← comap_smul f _ a h, ← map_le_iff_le_comap])

/--
theorem `comap_smul'` / 定理 `comap_smul'`

English:
theorem comap_smul'
  given: (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K)
  proof: by
  by_cases h : a = 0 <;> simp [h, comap_smul]

中文:
定理 comap_smul'
  条件: (f : V ->ₗ[K] V₂) (p : 子模 K V₂) (a : K)
  证明: by
  by_cases h : a = 0 <;> simp [h, comap_smul]

Depends on / 依赖: comap_smul
-/
theorem comap_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V₂) (a : K) :
    p.comap (a • f) = ⨅ _ : a != 0, p.comap f := by
  by_cases h : a = 0 <;> simp [h, comap_smul]

/--
theorem `map_smul'` / 定理 `map_smul'`

English:
theorem map_smul'
  given: (f : V ->ₗ[K] V₂) (p : Submodule K V) (a : K)
  proof: by
  by_cases h : a = 0 <;> simp [h, Submodule.map_smul]

中文:
定理 map_smul'
  条件: (f : V ->ₗ[K] V₂) (p : 子模 K V) (a : K)
  证明: by
  by_cases h : a = 0 <;> simp [h, Submodule.map_smul]

Depends on / 依赖: Submodule, Submodule.map_smul, map_smul
-/
theorem map_smul' (f : V ->ₗ[K] V₂) (p : Submodule K V) (a : K) :
    p.map (a • f) = ⨆ _ : a != 0, map f p := by
  by_cases h : a = 0 <;> simp [h, Submodule.map_smul]

end Submodule

namespace Submodule

section Module

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `s ≤ t`, then we can view `s` as a submodule of `t` by taking the comap
of `t.subtype`. -/
@[simps apply_coe symm_apply]
/--
Definition of `comapSubtypeEquivOfLe` / `comapSubtypeEquivOfLe` 的定义

English:
definition comapSubtypeEquivOfLe
  signature: {p q : Submodule R M} (hpq : p <= q)
  body: ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 comapSubtypeEquivOfLe
  签名: {p q : 子模 R M} (hpq : p <= q)
  定义体: ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
-/
def comapSubtypeEquivOfLe {p q : Submodule R M} (hpq : p <= q) : comap q.subtype p ≃ₗ[R] p where
  toFun x := ⟨x, x.2⟩
  invFun x := ⟨⟨x, hpq x.2⟩, x.2⟩
  left_inv x := by simp
  right_inv x := by simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Module

end Submodule

namespace Submodule

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂} {τ₂₁ : R₂ ->+* R}
variable [RingHomInvPair τ₁₂ τ₂₁] [RingHomInvPair τ₂₁ τ₁₂]
variable (p : Submodule R M) (q : Submodule R₂ M₂)

@[simp high]
/--
theorem `mem_map_equiv` / 定理 `mem_map_equiv`

English:
theorem mem_map_equiv
  given: {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂}
  proof: by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

中文:
定理 mem_map_equiv
  条件: {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂}
  证明: by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

Depends on / 依赖: Submodule, Submodule.mem_map, e.symm, mem_map
-/
theorem mem_map_equiv {e : M ≃ₛₗ[τ₁₂] M₂} {x : M₂} :
    x in p.map (e : M ->ₛₗ[τ₁₂] M₂) ↔ e.symm x in p := by
  rw [Submodule.mem_map]; constructor
  · rintro ⟨y, hy, hx⟩
    simp [← hx, hy]
  · intro hx
    exact ⟨e.symm x, hx, by simp⟩

/--
theorem `map_equiv_eq_comap_symm` / 定理 `map_equiv_eq_comap_symm`

English:
theorem map_equiv_eq_comap_symm
  given: (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M)
  proof: Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]

中文:
定理 map_equiv_eq_comap_symm
  条件: (e : M ≃ₛₗ[τ₁₂] M₂) (K : 子模 R M)
  证明: Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, Submodule, Submodule.ext, coe_coe, mem_comap, mem_map_equiv
-/
theorem map_equiv_eq_comap_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R M) :
    K.map (e : M ->ₛₗ[τ₁₂] M₂) = K.comap (e.symm : M₂ ->ₛₗ[τ₂₁] M) :=
  Submodule.ext fun _ => by rw [mem_map_equiv, mem_comap, LinearEquiv.coe_coe]

/--
theorem `comap_equiv_eq_map_symm` / 定理 `comap_equiv_eq_map_symm`

English:
theorem comap_equiv_eq_map_symm
  given: (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂)
  proof: (map_equiv_eq_comap_symm e.symm K).symm

中文:
定理 comap_equiv_eq_map_symm
  条件: (e : M ≃ₛₗ[τ₁₂] M₂) (K : 子模 R₂ M₂)
  证明: (map_equiv_eq_comap_symm e.symm K).symm

Depends on / 依赖: e.symm, map_equiv_eq_comap_symm
-/
theorem comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁₂] M₂) (K : Submodule R₂ M₂) :
    K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂ ->ₛₗ[τ₂₁] M) :=
  (map_equiv_eq_comap_symm e.symm K).symm

variable {p}

/--
theorem `map_symm_eq_iff` / 定理 `map_symm_eq_iff`

English:
theorem map_symm_eq_iff
  given: (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂}
  proof: by
  rw [map_equiv_eq_comap_symm]
  exact (orderIsoMapComap e).symm_apply_eq.trans eq_comm

中文:
定理 map_symm_eq_iff
  条件: (e : M ≃ₛₗ[τ₁₂] M₂) {K : 子模 R₂ M₂}
  证明: by
  rw [map_equiv_eq_comap_symm]
  exact (orderIsoMapComap e).symm_apply_eq.trans eq_comm

Depends on / 依赖: eq_comm, map_equiv_eq_comap_symm, orderIsoMapComap, symm_apply_eq, symm_apply_eq.trans
-/
theorem map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Submodule R₂ M₂} :
    K.map (e.symm : M₂ ->ₛₗ[τ₂₁] M) = p ↔ p.map (e : M ->ₛₗ[τ₁₂] M₂) = K := by
  rw [map_equiv_eq_comap_symm]
  exact (orderIsoMapComap e).symm_apply_eq.trans eq_comm

/--
theorem `orderIsoMapComap_apply'` / 定理 `orderIsoMapComap_apply'`

English:
theorem orderIsoMapComap_apply'
  given: (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M)
  proof: p.map_equiv_eq_comap_symm _

中文:
定理 orderIsoMapComap_apply'
  条件: (e : M ≃ₛₗ[τ₁₂] M₂) (p : 子模 R M)
  证明: p.map_equiv_eq_comap_symm _

Depends on / 依赖: map_equiv_eq_comap_symm, p.map_equiv_eq_comap_symm
-/
theorem orderIsoMapComap_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    orderIsoMapComap e p = comap (e.symm : M₂ ->ₛₗ[τ₂₁] M) p :=
  p.map_equiv_eq_comap_symm _

/--
theorem `orderIsoMapComap_symm_apply'` / 定理 `orderIsoMapComap_symm_apply'`

English:
theorem orderIsoMapComap_symm_apply'
  given: (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂)
  proof: p.comap_equiv_eq_map_symm _

中文:
定理 orderIsoMapComap_symm_apply'
  条件: (e : M ≃ₛₗ[τ₁₂] M₂) (p : 子模 R₂ M₂)
  证明: p.comap_equiv_eq_map_symm _

Depends on / 依赖: comap_equiv_eq_map_symm, p.comap_equiv_eq_map_symm
-/
theorem orderIsoMapComap_symm_apply' (e : M ≃ₛₗ[τ₁₂] M₂) (p : Submodule R₂ M₂) :
    (orderIsoMapComap e).symm p = map (e.symm : M₂ ->ₛₗ[τ₂₁] M) p :=
  p.comap_equiv_eq_map_symm _

/--
theorem `inf_comap_le_comap_add` / 定理 `inf_comap_le_comap_add`

English:
theorem inf_comap_le_comap_add
  given: (f₁ f₂ : M ->ₛₗ[τ₁₂] M₂)
  proof: by
  simp only [SetLike.le_def, mem_comap, mem_inf, LinearMap.add_apply]
  exact fun _ h => add_mem h.1 h.2

中文:
定理 inf_comap_le_comap_add
  条件: (f₁ f₂ : M ->ₛₗ[τ₁₂] M₂)
  证明: by
  simp only [SetLike.le_def, mem_comap, mem_inf, LinearMap.add_apply]
  exact fun _ h => add_mem h.1 h.2

Depends on / 依赖: LinearMap, LinearMap.add_apply, SetLike, SetLike.le_def, add_apply, add_mem, le_def, mem_comap, mem_inf
-/
theorem inf_comap_le_comap_add (f₁ f₂ : M ->ₛₗ[τ₁₂] M₂) :
    comap f₁ q ⊓ comap f₂ q <= comap (f₁ + f₂) q := by
  simp only [SetLike.le_def, mem_comap, mem_inf, LinearMap.add_apply]
  exact fun _ h => add_mem h.1 h.2

/--
lemma `surjOn_iff_le_map` / 引理 `surjOn_iff_le_map`

English:
lemma surjOn_iff_le_map
  statement: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  proof: Iff.rfl

中文:
引理 surjOn_iff_le_map
  结论: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : 子模 R M}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma surjOn_iff_le_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
    {q : Submodule R₂ M₂} : Set.SurjOn f p q ↔ q <= p.map f :=
  Iff.rfl

end Submodule

namespace Submodule

variable {S N N₂ : Type*}
variable [CommSemiring S] [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable [AddCommMonoid N] [AddCommMonoid N₂] [Module S N] [Module S N₂]
variable {τ₁₂ : R ->+* R₂}
variable (p : Submodule R M) (q : Submodule R₂ M₂)
variable (pₗ : Submodule S N) (qₗ : Submodule S N₂)

/--
theorem `comap_le_comap_smul` / 定理 `comap_le_comap_smul`

English:
theorem comap_le_comap_smul
  given: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  statement: comap f q <= comap (c • f) q
  proof: by
  simp only [SetLike.le_def, mem_comap, LinearMap.smul_apply]
  exact fun _ h => smul_mem _ _ h

中文:
定理 comap_le_comap_smul
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  结论: comap f q <= comap (c • f) q
  证明: by
  simp only [SetLike.le_def, mem_comap, LinearMap.smul_apply]
  exact fun _ h => smul_mem _ _ h

Depends on / 依赖: LinearMap, LinearMap.smul_apply, SetLike, SetLike.le_def, le_def, mem_comap, smul_apply, smul_mem
-/
theorem comap_le_comap_smul (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : comap f q <= comap (c • f) q := by
  simp only [SetLike.le_def, mem_comap, LinearMap.smul_apply]
  exact fun _ h => smul_mem _ _ h

/--
theorem `map_smul_le_map` / 定理 `map_smul_le_map`

English:
theorem map_smul_le_map
  given: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  proof: by
  grw [map_le_iff_le_comap, ← comap_le_comap_smul (map f p) f c, ← map_le_iff_le_comap]

中文:
定理 map_smul_le_map
  条件: [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  证明: by
  grw [map_le_iff_le_comap, ← comap_le_comap_smul (map f p) f c, ← map_le_iff_le_comap]

Depends on / 依赖: comap_le_comap_smul, map_le_iff_le_comap
-/
theorem map_smul_le_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) :
    map (c • f) p <= map f p := by
  grw [map_le_iff_le_comap, ← comap_le_comap_smul (map f p) f c, ← map_le_iff_le_comap]

/--
Definition of `compatibleMaps` / `compatibleMaps` 的定义

English:
definition compatibleMaps
  signature: : Submodule S (N ->ₗ[S] N₂) where
  body: { fₗ | pₗ <= comap fₗ qₗ }
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)

中文:
定义 compatibleMaps
  签名: : 子模 S (N ->ₗ[S] N₂) where
  定义体: { fₗ | pₗ <= comap fₗ qₗ }
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)
-/
def compatibleMaps : Submodule S (N ->ₗ[S] N₂) where
  carrier := { fₗ | pₗ <= comap fₗ qₗ }
  zero_mem' := by simp
  add_mem' {f₁ f₂} h₁ h₂ := by
    apply le_trans _ (inf_comap_le_comap_add qₗ f₁ f₂)
    rw [le_inf_iff]
    exact ⟨h₁, h₂⟩
  smul_mem' c fₗ h := by
    dsimp at h
    exact le_trans h (comap_le_comap_smul qₗ fₗ c)

end Submodule

namespace LinearMap

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}

/-- The `LinearMap` from the preimage of a submodule to itself.

This is the linear version of `AddMonoidHom.addSubmonoidComap`
and `AddMonoidHom.addSubgroupComap`. -/
@[simps!]
/--
Definition of `submoduleComap` / `submoduleComap` 的定义

English:
definition submoduleComap
  signature: (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
  body: f.restrict fun _ => Submodule.mem_comap.1

中文:
定义 submoduleComap
  签名: (f : M ->ₛₗ[σ₁₂] M₂) (q : 子模 R₂ M₂)
  定义体: f.restrict fun _ => Submodule.mem_comap.1

Depends on / 依赖: Submodule, Submodule.mem_comap, f.restrict, mem_comap, restrict
-/
def submoduleComap (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂) : q.comap f ->ₛₗ[σ₁₂] q :=
  f.restrict fun _ => Submodule.mem_comap.1

/--
theorem `submoduleComap_surjective_of_surjective` / 定理 `submoduleComap_surjective_of_surjective`

English:
theorem submoduleComap_surjective_of_surjective
  statement: (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
  proof: fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

中文:
定理 submoduleComap_surjective_of_surjective
  结论: (f : M ->ₛₗ[σ₁₂] M₂) (q : 子模 R₂ M₂)
  证明: fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

Depends on / 依赖: Submodule, Submodule.mem_comap.mpr, Subtype, Subtype.val_injective, mem_comap, val_injective
-/
theorem submoduleComap_surjective_of_surjective (f : M ->ₛₗ[σ₁₂] M₂) (q : Submodule R₂ M₂)
    (hf : Surjective f) : Surjective (f.submoduleComap q) := fun y => by
  obtain ⟨x, hx⟩ := hf y
  use ⟨x, Submodule.mem_comap.mpr (hx ▸ y.2)⟩
  apply Subtype.val_injective
  simp [hx]

/--
Definition of `submoduleMap` / `submoduleMap` 的定义

English:
definition submoduleMap
  signature: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  body: f.restrict fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]

中文:
定义 submoduleMap
  签名: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  定义体: f.restrict fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]

Depends on / 依赖: Submodule, Submodule.mem_map.mpr, f.restrict, mem_map, restrict
-/
def submoduleMap [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    p ->ₛₗ[σ₁₂] p.map f :=
  f.restrict fun x hx => Submodule.mem_map.mpr ⟨x, hx, rfl⟩

@[simp]
/--
theorem `submoduleMap_coe_apply` / 定理 `submoduleMap_coe_apply`

English:
theorem submoduleMap_coe_apply
  statement: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M}
  proof: rfl

中文:
定理 submoduleMap_coe_apply
  结论: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {p : 子模 R M}
  证明: rfl
-/
theorem submoduleMap_coe_apply [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) {p : Submodule R M}
    (x : p) : ↑(f.submoduleMap p x) = f x := rfl

/--
theorem `submoduleMap_surjective` / 定理 `submoduleMap_surjective`

English:
theorem submoduleMap_surjective
  given: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M)
  proof: f.toAddMonoidHom.addSubmonoidMap_surjective _

@[grind inj]

中文:
定理 submoduleMap_surjective
  条件: [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : 子模 R M)
  证明: f.toAddMonoidHom.addSubmonoidMap_surjective _

@[grind inj]

Depends on / 依赖: addSubmonoidMap_surjective, f.toAddMonoidHom.addSubmonoidMap_surjective, toAddMonoidHom
-/
theorem submoduleMap_surjective [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) :
    Function.Surjective (f.submoduleMap p) := f.toAddMonoidHom.addSubmonoidMap_surjective _

@[grind inj]
/--
theorem `submoduleMap_injective` / 定理 `submoduleMap_injective`

English:
theorem submoduleMap_injective
  statement: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f)
  proof: f.toAddMonoidHom.addSubmonoidMap_injective hf _

中文:
定理 submoduleMap_injective
  结论: [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : 单射 f)
  证明: f.toAddMonoidHom.addSubmonoidMap_injective hf _

Depends on / 依赖: addSubmonoidMap_injective, f.toAddMonoidHom.addSubmonoidMap_injective, toAddMonoidHom
-/
theorem submoduleMap_injective [RingHomSurjective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} (hf : Injective f)
    (p : Submodule R M) : Injective (f.submoduleMap p) :=
  f.toAddMonoidHom.addSubmonoidMap_injective hf _

/--
theorem `submoduleMap_injective_of_injOn` / 定理 `submoduleMap_injective_of_injOn`

English:
theorem submoduleMap_injective_of_injOn
  statement: [RingHomSurjective σ₁₂]
  proof: by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  replace hxy : f x = f y := by simpa [Subtype.ext_iff] using hxy
  aesop

中文:
定理 submoduleMap_injective_of_injOn
  结论: [RingHomSurjective σ₁₂]
  证明: by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  replace hxy : f x = f y := by simpa [Subtype.ext_iff] using hxy
  aesop

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff, replace
-/
theorem submoduleMap_injective_of_injOn [RingHomSurjective σ₁₂]
    {p : Submodule R M} {f : M ->ₛₗ[σ₁₂] M₂} (hf : Set.InjOn f p) :
    Injective (f.submoduleMap p) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  replace hxy : f x = f y := by simpa [Subtype.ext_iff] using hxy
  aesop

open Submodule

/--
theorem `map_codRestrict` / 定理 `map_codRestrict`

English:
theorem map_codRestrict
  given: [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p')
  proof: Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]

中文:
定理 map_codRestrict
  条件: [RingHomSurjective σ₂₁] (p : 子模 R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p')
  证明: Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]

Depends on / 依赖: Submodule, Submodule.ext, Subtype, Subtype.ext_iff, ext_iff
-/
theorem map_codRestrict [RingHomSurjective σ₂₁] (p : Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') :
    map (codRestrict p f h) p' = comap p.subtype (p'.map f) :=
  Submodule.ext fun ⟨x, hx⟩ => by simp [Subtype.ext_iff]

/--
theorem `comap_codRestrict` / 定理 `comap_codRestrict`

English:
theorem comap_codRestrict
  given: (p : Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (hf p')
  proof: Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

中文:
定理 comap_codRestrict
  条件: (p : 子模 R M) (f : M₂ ->ₛₗ[σ₂₁] M) (hf p')
  证明: Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

Depends on / 依赖: Submodule, Submodule.ext
-/
theorem comap_codRestrict (p : Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (hf p') :
    comap (codRestrict p f hf) p' = comap f (map p.subtype p') :=
  Submodule.ext fun x => ⟨fun h => ⟨⟨_, hf x⟩, h, rfl⟩, by rintro ⟨⟨_, _⟩, h, ⟨⟩⟩; exact h⟩

/--
theorem `map_domRestrict` / 定理 `map_domRestrict`

English:
theorem map_domRestrict
  given: [RingHomSurjective σ₂₁] (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p')
  proof: map_comp p.subtype f p'

中文:
定理 map_domRestrict
  条件: [RingHomSurjective σ₂₁] (p : 子模 R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p')
  证明: map_comp p.subtype f p'

Depends on / 依赖: map_comp, p.subtype, subtype
-/
theorem map_domRestrict [RingHomSurjective σ₂₁] (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p') :
    map (domRestrict f p) p' = map f (map p.subtype p') :=
  map_comp p.subtype f p'

/--
theorem `comap_domRestrict` / 定理 `comap_domRestrict`

English:
theorem comap_domRestrict
  given: (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p')
  proof: comap_comp p.subtype f p'

中文:
定理 comap_domRestrict
  条件: (p : 子模 R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p')
  证明: comap_comp p.subtype f p'

Depends on / 依赖: comap_comp, p.subtype, subtype
-/
theorem comap_domRestrict (p : Submodule R₂ M₂) (f : M₂ ->ₛₗ[σ₂₁] M) (p') :
    comap (domRestrict f p) p' = comap p.subtype (comap f p') :=
  comap_comp p.subtype f p'

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `map_restrict` / 定理 `map_restrict`

English:
theorem map_restrict
  statement: [RingHomSurjective σ₂₁] {p : Submodule R₂ M₂} {q : Submodule R M}
  proof: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [map_codRestrict]; rw [map_domRestrict]

中文:
定理 map_restrict
  结论: [RingHomSurjective σ₂₁] {p : 子模 R₂ M₂} {q : 子模 R M}
  证明: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [map_codRestrict]; rw [map_domRestrict]

Depends on / 依赖: map_codRestrict, map_domRestrict, restrict_eq_codRestrict_domRestrict
-/
theorem map_restrict [RingHomSurjective σ₂₁] {p : Submodule R₂ M₂} {q : Submodule R M}
    {f : M₂ ->ₛₗ[σ₂₁] M} (h : forall x in p, f x in q) (p') :
    map (f.restrict h) p' = comap q.subtype (map f (map p.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict]; rw [map_codRestrict]; rw [map_domRestrict]

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `comap_restrict` / 定理 `comap_restrict`

English:
theorem comap_restrict
  statement: {p : Submodule R₂ M₂} {q : Submodule R M} {f : M₂ ->ₛₗ[σ₂₁] M}
  proof: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [comap_codRestrict]; rw [comap_domRestrict]

中文:
定理 comap_restrict
  结论: {p : 子模 R₂ M₂} {q : 子模 R M} {f : M₂ ->ₛₗ[σ₂₁] M}
  证明: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [comap_codRestrict]; rw [comap_domRestrict]

Depends on / 依赖: comap_codRestrict, comap_domRestrict, restrict_eq_codRestrict_domRestrict
-/
theorem comap_restrict {p : Submodule R₂ M₂} {q : Submodule R M} {f : M₂ ->ₛₗ[σ₂₁] M}
    (h : forall x in p, f x in q) (p') :
    comap (f.restrict h) p' = comap p.subtype (comap f (map q.subtype p')) := by
  rw [restrict_eq_codRestrict_domRestrict]; rw [comap_codRestrict]; rw [comap_domRestrict]

end LinearMap

/-! ### Linear equivalences -/

namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂}
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable (e : M ≃ₛₗ[σ₁₂] M₂)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `submoduleMap` / `submoduleMap` 的定义

English:
definition submoduleMap
  signature: (p : Submodule R M)
  body: { ((e : M ->ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M ->ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, and_true, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ ->ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }

@[simp]

中文:
定义 submoduleMap
  签名: (p : 子模 R M)
  定义体: { ((e : M ->ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M ->ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, and_true, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ ->ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }

@[simp]

Depends on / 依赖: LinearEquiv, LinearMap, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply, LinearMap.toFun_eq_coe, SetLike, SetLike.coe_mem, SetLike.mem_coe, Submodule, Submodule.mem_map, and_true, codRestrict, codRestrict_apply, coe_coe, coe_mem, domRestrict, domRestrict_apply, e.symm, invFun, left_inv
-/
def submoduleMap (p : Submodule R M) : p ≃ₛₗ[σ₁₂] ↥(p.map (e : M ->ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂) :=
  { ((e : M ->ₛₗ[σ₁₂] M₂).domRestrict p).codRestrict (p.map (e : M ->ₛₗ[σ₁₂] M₂)) fun x =>
      ⟨x, by
        simp only [LinearMap.domRestrict_apply, and_true, SetLike.coe_mem,
          SetLike.mem_coe]⟩ with
    invFun := fun y =>
      ⟨(e.symm : M₂ ->ₛₗ[σ₂₁] M) y, by
        rcases y with ⟨y', hy⟩
        rw [Submodule.mem_map] at hy
        rcases hy with ⟨x, hx, hxy⟩
        subst hxy
        simp only [symm_apply_apply, coe_coe, hx]⟩
    left_inv := fun x => by
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, SetLike.eta]
    right_inv := fun y => by
      apply SetCoe.ext
      simp only [LinearMap.domRestrict_apply, LinearMap.codRestrict_apply, LinearMap.toFun_eq_coe,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] }

@[simp]
/--
theorem `submoduleMap_apply` / 定理 `submoduleMap_apply`

English:
theorem submoduleMap_apply
  given: (p : Submodule R M) (x : p)
  statement: ↑(e.submoduleMap p x) = e x
  proof: rfl

@[simp]

中文:
定理 submoduleMap_apply
  条件: (p : 子模 R M) (x : p)
  结论: ↑(e.submoduleMap p x) = e x
  证明: rfl

@[simp]
-/
theorem submoduleMap_apply (p : Submodule R M) (x : p) : ↑(e.submoduleMap p x) = e x :=
  rfl

@[simp]
/--
theorem `submoduleMap_symm_apply` / 定理 `submoduleMap_symm_apply`

English:
theorem submoduleMap_symm_apply
  statement: (p : Submodule R M)
  proof: rfl

中文:
定理 submoduleMap_symm_apply
  结论: (p : 子模 R M)
  证明: rfl
-/
theorem submoduleMap_symm_apply (p : Submodule R M)
    (x : (p.map (e : M ->ₛₗ[σ₁₂] M₂) : Submodule R₂ M₂)) : ↑((e.submoduleMap p).symm x) = e.symm x :=
  rfl

end

end AddCommMonoid

end LinearEquiv
