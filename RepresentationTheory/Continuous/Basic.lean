/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Topology.ContinuousMap.Algebra

/-!
## Continuous representations

This file defines continuous representations of a monoid `G` on a `R`-module `V` and
related basic results.

## Main Results

* `ContRepresentation R G V` is the type of continuous representations of a monoid `G` on a
  `R`-module `V` which is a topological addgroup (where the action of `G` on `V` is
  *not* assumed to be continuous). The reason for this more general definition is that it allows us
  to define the coinduced representation of a continuous representation as also a continuous
  representation without any restriction on the topology on `G`.

* `ContIntertwiningMap π₁ π₂` is the type of continuous intertwining maps between two continuous
  representations `π₁` and `π₂`.

* `ContRepresentation.coind₁ π` is the coinduced continuous representation on the space of
  continuous functions from `G` to `V` for a continuous representation `π`.

* `ContIntertwiningMap.mapInvariantsOfRes φ f` is the continuous linear map
  `π.invariants →L[R] π'.invariants` induced by a monoid homomorphism `φ : H →* G` and a
  continuous intertwining map `f : π.restrict φ →ⁱL π'`.

* `ContRepresentation.coind₁ResMap φ f` is the continuous intertwining map
  `π.coind₁.restrict φ →ⁱL π'.coind₁` induced by a continuous group homomorphism `φ : H →ₜ* G`
  and a continuous intertwining map `f : π.restrict φ →ⁱL π'`, given by `F ↦ f ∘ F ∘ φ`.

## Tags
continuous representation, algebra
-/

@[expose] public section

variable (R G V W U : Type*) [Monoid G] [Ring R] [AddCommGroup V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [Module R V] [AddCommGroup W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [Module R W] [AddCommGroup U] [Module R U] [TopologicalSpace U]
  [IsTopologicalAddGroup U]

/--
Definition of `ContRepresentation` / `ContRepresentation` 的定义

English:
structure ContRepresentation
  parameters: where
  axioms and operations (2):
    - ofMonoidHom : :
    - toMonoidHom : G ->* V ->L[R] V

中文:
结构 余ntRepresentation
  参数: where
  公理与运算 (2 个):
    - ofMonoidHom : :
    - toMonoidHom : G ->* V ->L[R] V
-/
structure ContRepresentation where
  ofMonoidHom ::
  /-- The underlying monoid homomorphism of a continuous representation. -/
  toMonoidHom : G ->* V ->L[R] V

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (ContRepresentation R G V) G (V ->L[R] V)
  body: π.toMonoidHom
  coe_injective π₁ π₂ _ := by cases π₁; cases π₂; simp_all

中文:
实例 :
  签名: 函数状 (余ntRepresentation R G V) G (V ->L[R] V)
  定义体: π.toMonoidHom
  coe_injective π₁ π₂ _ := by cases π₁; cases π₂; simp_all

Depends on / 依赖: toMonoidHom
-/
instance : FunLike (ContRepresentation R G V) G (V ->L[R] V) where
  coe π := π.toMonoidHom
  coe_injective π₁ π₂ _ := by cases π₁; cases π₂; simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidHomClass (ContRepresentation R G V) G (V ->L[R] V)
  body: π.toMonoidHom.map_one
  map_mul π := π.toMonoidHom.map_mul

中文:
实例 :
  签名: 幺半群态射类 (余ntRepresentation R G V) G (V ->L[R] V)
  定义体: π.toMonoidHom.map_one
  map_mul π := π.toMonoidHom.map_mul
-/
instance : MonoidHomClass (ContRepresentation R G V) G (V ->L[R] V) where
  map_one π := π.toMonoidHom.map_one
  map_mul π := π.toMonoidHom.map_mul

/--
lemma `ContRepresentation.toMonoidHom_apply` / 引理 `ContRepresentation.toMonoidHom_apply`

English:
lemma ContRepresentation.toMonoidHom_apply
  given: (π : ContRepresentation R G V) (g : G)
  proof: rfl

中文:
引理 余ntRepresentation.toMonoidHom_apply
  条件: (π : 余ntRepresentation R G V) (g : G)
  证明: rfl
-/
lemma ContRepresentation.toMonoidHom_apply (π : ContRepresentation R G V) (g : G) :
    π.toMonoidHom g = π g := rfl

/--
Definition of `ContRepresentation.toRepresentation` / `ContRepresentation.toRepresentation` 的定义

English:
abbreviation ContRepresentation.toRepresentation
  signature: (π : ContRepresentation R G V)
  body: .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π.toMonoidHom

中文:
缩写 余ntRepresentation.toRepresentation
  签名: (π : 余ntRepresentation R G V)
  定义体: .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π.toMonoidHom

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.toLinearMapRingHom.toMonoidHom, Multiset, Multiset.map_eq_map, Subtype, Subtype.coe_injective, associated_zero_iff_eq_zero, coe_injective, contrapose, eq_or_ne, factors_prod, factors_unique, h.symm, h.trans, irreducible_of_factor, map_eq_map, map_subtype_coe_factors, rel_associated_iff_map_eq_map, toLinearMapRingHom, toMonoidHom
-/
abbrev ContRepresentation.toRepresentation (π : ContRepresentation R G V) :
    Representation R G V :=
  .comp ContinuousLinearMap.toLinearMapRingHom.toMonoidHom π.toMonoidHom

variable {R G V W U}

/--
Definition of `ContIntertwiningMap` / `ContIntertwiningMap` 的定义

English:
structure ContIntertwiningMap
  parameters: (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
  extends: V ->L[R] W
  axioms and operations (1):
    - isIntertwining'((g : G)) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap

中文:
结构 余nt整数ertwining映射
  参数: (π₁ : 余ntRepresentation R G V) (π₂ : 余ntRepresentation R G W)
  继承: V ->L[R] W
  公理与运算 (1 个):
    - isIntertwining'((g : G)) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap
-/
structure ContIntertwiningMap (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
    extends V ->L[R] W where
  isIntertwining' (g : G) : toContinuousLinearMap ∘L π₁ g = π₂ g ∘L toContinuousLinearMap

/-- notation for continuous intertwining maps -/
scoped[ContRepresentation] notation:30 π₁ " ->ⁱL " π₂ =>
  ContIntertwiningMap π₁ π₂

namespace ContIntertwiningMap

open ContRepresentation

variable {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  {π₃ : ContRepresentation R G U}

/--
Definition of `toIntertwiningMap` / `toIntertwiningMap` 的定义

English:
abbreviation toIntertwiningMap
  signature: (f : π₁ ->ⁱL π₂)
  body: f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.2 g))

中文:
缩写 to整数ertwiningMap
  签名: (f : π₁ ->ⁱL π₂)
  定义体: f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.2 g))

Depends on / 依赖: f.toContinuousLinearMap.toLinearMap, toContinuousLinearMap, toLinearMap
-/
abbrev toIntertwiningMap (f : π₁ ->ⁱL π₂) :
    Representation.IntertwiningMap π₁.toRepresentation π₂.toRepresentation where
  __ := f.toContinuousLinearMap.toLinearMap
  isIntertwining' g := congr(ContinuousLinearMap.toLinearMap $(f.2 g))

/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: : π₁ ->ⁱL π₁ where
  body: ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[simp]

中文:
定义 id
  签名: : π₁ ->ⁱL π₁ where
  定义体: ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[simp]

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.id
-/
def id : π₁ ->ⁱL π₁ where
  __ := ContinuousLinearMap.id R V
  isIntertwining' g := by simp

@[simp]
/--
lemma `toContinuousLinearMap_id` / 引理 `toContinuousLinearMap_id`

English:
lemma toContinuousLinearMap_id
  proof: rfl

@[ext]

中文:
引理 toContinuousLinearMap_id
  证明: rfl

@[ext]
-/
lemma toContinuousLinearMap_id :
    (id : π₁ ->ⁱL π₁).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  proof: by
  cases f; cases g; congr

中文:
引理 ext
  结论: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W}
  证明: by
  cases f; cases g; congr
-/
lemma ext {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {f g : π₁ ->ⁱL π₂} (h : f.toContinuousLinearMap = g.toContinuousLinearMap) : f = g := by
  cases f; cases g; congr

/--
lemma `toContinuousLinearMap_injective` / 引理 `toContinuousLinearMap_injective`

English:
lemma toContinuousLinearMap_injective
  statement: {π₁ : ContRepresentation R G V}
  proof: fun _ _ => ext

中文:
引理 toContinuousLinearMap_injective
  结论: {π₁ : 余ntRepresentation R G V}
  证明: fun _ _ => ext
-/
lemma toContinuousLinearMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ ->ⁱL π₂ => f.toContinuousLinearMap :=
  fun _ _ => ext

/--
lemma `toIntertwiningMap_injective` / 引理 `toIntertwiningMap_injective`

English:
lemma toIntertwiningMap_injective
  statement: {π₁ : ContRepresentation R G V}
  proof: fun _ _ _ => by ext; simp_all

中文:
引理 to整数ertwiningMap_injective
  结论: {π₁ : 余ntRepresentation R G V}
  证明: fun _ _ _ => by ext; simp_all
-/
lemma toIntertwiningMap_injective {π₁ : ContRepresentation R G V}
    {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ ->ⁱL π₂ => f.toIntertwiningMap :=
  fun _ _ _ => by ext; simp_all

/--
lemma `toFun_injective` / 引理 `toFun_injective`

English:
lemma toFun_injective
  given: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  proof: fun f g h => by
  ext x; exact congr_fun h x

中文:
引理 toFun_injective
  条件: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W}
  证明: fun f g h => by
  ext x; exact congr_fun h x

Depends on / 依赖: congr_fun
-/
lemma toFun_injective {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    Function.Injective fun f : π₁ ->ⁱL π₂ => f.toFun := fun f g h => by
  ext x; exact congr_fun h x

instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    FunLike (π₁ ->ⁱL π₂) V W where
  coe f := f.toFun
  coe_injective := toFun_injective

/--
lemma `id_apply` / 引理 `id_apply`

English:
lemma id_apply
  given: (v : V)
  statement: (.id : π₁ ->ⁱL π₁) v = v
  proof: rfl

中文:
引理 id_apply
  条件: (v : V)
  结论: (.id : π₁ ->ⁱL π₁) v = v
  证明: rfl
-/
lemma id_apply (v : V) : (.id : π₁ ->ⁱL π₁) v = v := rfl

/--
lemma `toContinuousLinearMap_apply` / 引理 `toContinuousLinearMap_apply`

English:
lemma toContinuousLinearMap_apply
  given: (f : π₁ ->ⁱL π₂) (v : V)
  proof: rfl

中文:
引理 toContinuousLinearMap_apply
  条件: (f : π₁ ->ⁱL π₂) (v : V)
  证明: rfl
-/
lemma toContinuousLinearMap_apply (f : π₁ ->ⁱL π₂) (v : V) :
  f.toContinuousLinearMap v = f v := rfl

/--
lemma `isIntertwining` / 引理 `isIntertwining`

English:
lemma isIntertwining
  statement: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  proof: f.toIntertwiningMap.isIntertwining _ _ g v

中文:
引理 is整数ertwining
  结论: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W}
  证明: f.toIntertwiningMap.isIntertwining _ _ g v

Depends on / 依赖: f.toIntertwiningMap.isIntertwining, isIntertwining, toIntertwiningMap
-/
lemma isIntertwining {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    (f : π₁ ->ⁱL π₂) (g : G) (v : V) : f (π₁ g v) = π₂ g (f v) :=
  f.toIntertwiningMap.isIntertwining _ _ g v

instance {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} :
    ContinuousLinearMapClass (π₁ ->ⁱL π₂) R V W where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont

open ContinuousLinearMap in
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  body: f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by rw [comp_assoc, g.2, ← comp_assoc, f.2, comp_assoc]

@[simp]

中文:
定义 comp
  签名: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W}
  定义体: f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by rw [comp_assoc, g.2, ← comp_assoc, f.2, comp_assoc]

@[simp]

Depends on / 依赖: f.toContinuousLinearMap.comp, g.toContinuousLinearMap, toContinuousLinearMap
-/
def comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π₂) : π₁ ->ⁱL π₃ where
  __ := f.toContinuousLinearMap.comp g.toContinuousLinearMap
  isIntertwining' h := by rw [comp_assoc, g.2, ← comp_assoc, f.2, comp_assoc]

@[simp]
/--
lemma `toContinuousLinearMap_comp` / 引理 `toContinuousLinearMap_comp`

English:
lemma toContinuousLinearMap_comp
  statement: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
  proof: rfl

中文:
引理 toContinuousLinearMap_comp
  结论: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W}
  证明: rfl
-/
lemma toContinuousLinearMap_comp {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W}
    {π₃ : ContRepresentation R G U} (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π₂) :
    (f.comp g).toContinuousLinearMap = f.toContinuousLinearMap.comp g.toContinuousLinearMap := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (π₁ ->ⁱL π₂)
  body: ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]

中文:
实例 :
  签名: 加法 (π₁ ->ⁱL π₂)
  定义体: ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]

Depends on / 依赖: f.toContinuousLinearMap, g.toContinuousLinearMap, toContinuousLinearMap
-/
instance : Add (π₁ ->ⁱL π₂) where
  add f g := ⟨f.toContinuousLinearMap + g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]
/--
lemma `toContinuousLinearMap_add` / 引理 `toContinuousLinearMap_add`

English:
lemma toContinuousLinearMap_add
  given: (f g : π₁ ->ⁱL π₂)
  proof: rfl

中文:
引理 toContinuousLinearMap_add
  条件: (f g : π₁ ->ⁱL π₂)
  证明: rfl
-/
lemma toContinuousLinearMap_add (f g : π₁ ->ⁱL π₂) :
    (f + g).toContinuousLinearMap = f.toContinuousLinearMap + g.toContinuousLinearMap := rfl

/--
lemma `add_apply` / 引理 `add_apply`

English:
lemma add_apply
  given: (f g : π₁ ->ⁱL π₂) (v : V)
  statement: (f + g) v = f v + g v
  proof: rfl

中文:
引理 add_apply
  条件: (f g : π₁ ->ⁱL π₂) (v : V)
  结论: (f + g) v = f v + g v
  证明: rfl
-/
lemma add_apply (f g : π₁ ->ⁱL π₂) (v : V) : (f + g) v = f v + g v := rfl

/--
lemma `comp_add` / 引理 `comp_add`

English:
lemma comp_add
  given: (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂)
  proof: by ext; simp

中文:
引理 comp_add
  条件: (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂)
  证明: by ext; simp
-/
lemma comp_add (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂) :
    f.comp (g + h) = f.comp g + f.comp h := by ext; simp

/--
lemma `add_comp` / 引理 `add_comp`

English:
lemma add_comp
  given: (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂)
  proof: by ext; simp

中文:
引理 add_comp
  条件: (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂)
  证明: by ext; simp
-/
lemma add_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂) :
    (f + g).comp h = f.comp h + g.comp h := by ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (π₁ ->ⁱL π₁)
  body: .id

中文:
实例 :
  签名: 幺 (π₁ ->ⁱL π₁)
  定义体: .id
-/
instance : One (π₁ ->ⁱL π₁) where one := .id

/--
lemma `one_def` / 引理 `one_def`

English:
lemma one_def
  statement: (1 : π₁ ->ⁱL π₁) = .id
  proof: rfl

@[simp]

中文:
引理 one_def
  结论: (1 : π₁ ->ⁱL π₁) = .id
  证明: rfl

@[simp]
-/
lemma one_def : (1 : π₁ ->ⁱL π₁) = .id := rfl

@[simp]
/--
lemma `toContinuousLinearMap_one` / 引理 `toContinuousLinearMap_one`

English:
lemma toContinuousLinearMap_one
  statement: (1 : π₁ ->ⁱL π₁).toContinuousLinearMap = 1
  proof: rfl

中文:
引理 toContinuousLinearMap_one
  结论: (1 : π₁ ->ⁱL π₁).toContinuousLinearMap = 1
  证明: rfl
-/
lemma toContinuousLinearMap_one : (1 : π₁ ->ⁱL π₁).toContinuousLinearMap = 1 := rfl

/--
lemma `one_apply` / 引理 `one_apply`

English:
lemma one_apply
  given: (v : V)
  statement: (1 : π₁ ->ⁱL π₁) v = v
  proof: rfl

中文:
引理 one_apply
  条件: (v : V)
  结论: (1 : π₁ ->ⁱL π₁) v = v
  证明: rfl
-/
lemma one_apply (v : V) : (1 : π₁ ->ⁱL π₁) v = v := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (π₁ ->ⁱL π₂)
  body: ⟨0, by simp⟩

@[simp]

中文:
实例 :
  签名: 零 (π₁ ->ⁱL π₂)
  定义体: ⟨0, by simp⟩

@[simp]
-/
instance : Zero (π₁ ->ⁱL π₂) where zero := ⟨0, by simp⟩

@[simp]
/--
lemma `toContinuousLinearMap_zero` / 引理 `toContinuousLinearMap_zero`

English:
lemma toContinuousLinearMap_zero
  statement: (0 : π₁ ->ⁱL π₂).toContinuousLinearMap = 0
  proof: rfl

中文:
引理 toContinuousLinearMap_zero
  结论: (0 : π₁ ->ⁱL π₂).toContinuousLinearMap = 0
  证明: rfl

Depends on / 依赖: _of_dvd, dvd_of_mem_factors, mem_factors, mk_dvd_mk
-/
lemma toContinuousLinearMap_zero : (0 : π₁ ->ⁱL π₂).toContinuousLinearMap = 0 := rfl

/--
lemma `zero_apply` / 引理 `zero_apply`

English:
lemma zero_apply
  given: (v : V)
  statement: (0 : π₁ ->ⁱL π₂) v = 0
  proof: rfl

中文:
引理 zero_apply
  条件: (v : V)
  结论: (0 : π₁ ->ⁱL π₂) v = 0
  证明: rfl
-/
lemma zero_apply (v : V) : (0 : π₁ ->ⁱL π₂) v = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddZeroClass (π₁ ->ⁱL π₂)
  body: fast_instance% toContinuousLinearMap_injective.addZeroClass _
    toContinuousLinearMap_zero toContinuousLinearMap_add

中文:
实例 :
  签名: 加法零类 (π₁ ->ⁱL π₂)
  定义体: fast_instance% toContinuousLinearMap_injective.addZeroClass _
    toContinuousLinearMap_zero toContinuousLinearMap_add

Depends on / 依赖: addZeroClass, fast_instance, toContinuousLinearMap_add, toContinuousLinearMap_injective, toContinuousLinearMap_injective.addZeroClass, toContinuousLinearMap_zero
-/
instance : AddZeroClass (π₁ ->ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addZeroClass _
    toContinuousLinearMap_zero toContinuousLinearMap_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommSemigroup (π₁ ->ⁱL π₂)
  body: fast_instance% toContinuousLinearMap_injective.addCommSemigroup _
    toContinuousLinearMap_add

中文:
实例 :
  签名: 加法交换半群 (π₁ ->ⁱL π₂)
  定义体: fast_instance% toContinuousLinearMap_injective.addCommSemigroup _
    toContinuousLinearMap_add

Depends on / 依赖: addCommSemigroup, fast_instance, toContinuousLinearMap_add, toContinuousLinearMap_injective, toContinuousLinearMap_injective.addCommSemigroup
-/
instance : AddCommSemigroup (π₁ ->ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommSemigroup _
    toContinuousLinearMap_add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (π₁ ->ⁱL π₂)
  body: ⟨-f.toContinuousLinearMap, by simp [f.2]⟩

@[simp]

中文:
实例 :
  签名: 取负 (π₁ ->ⁱL π₂)
  定义体: ⟨-f.toContinuousLinearMap, by simp [f.2]⟩

@[simp]

Depends on / 依赖: f.toContinuousLinearMap, toContinuousLinearMap
-/
instance : Neg (π₁ ->ⁱL π₂) where
  neg f := ⟨-f.toContinuousLinearMap, by simp [f.2]⟩

@[simp]
/--
lemma `toContinuousLinearMap_neg` / 引理 `toContinuousLinearMap_neg`

English:
lemma toContinuousLinearMap_neg
  given: (f : π₁ ->ⁱL π₂)
  proof: rfl

中文:
引理 toContinuousLinearMap_neg
  条件: (f : π₁ ->ⁱL π₂)
  证明: rfl
-/
lemma toContinuousLinearMap_neg (f : π₁ ->ⁱL π₂) :
    (-f).toContinuousLinearMap = -f.toContinuousLinearMap := rfl

/--
lemma `neg_apply` / 引理 `neg_apply`

English:
lemma neg_apply
  given: (f : π₁ ->ⁱL π₂) (v : V)
  statement: (-f) v = -f v
  proof: rfl

中文:
引理 neg_apply
  条件: (f : π₁ ->ⁱL π₂) (v : V)
  结论: (-f) v = -f v
  证明: rfl
-/
lemma neg_apply (f : π₁ ->ⁱL π₂) (v : V) : (-f) v = -f v := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (π₁ ->ⁱL π₂)
  body: ⟨f.toContinuousLinearMap - g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]

中文:
实例 :
  签名: 减法 (π₁ ->ⁱL π₂)
  定义体: ⟨f.toContinuousLinearMap - g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]

Depends on / 依赖: f.toContinuousLinearMap, g.toContinuousLinearMap, toContinuousLinearMap
-/
instance : Sub (π₁ ->ⁱL π₂) where
  sub f g := ⟨f.toContinuousLinearMap - g.toContinuousLinearMap, by simp [g.2, f.2]⟩

@[simp]
/--
lemma `toContinuousLinearMap_sub` / 引理 `toContinuousLinearMap_sub`

English:
lemma toContinuousLinearMap_sub
  given: (f g : π₁ ->ⁱL π₂)
  proof: rfl

中文:
引理 toContinuousLinearMap_sub
  条件: (f g : π₁ ->ⁱL π₂)
  证明: rfl
-/
lemma toContinuousLinearMap_sub (f g : π₁ ->ⁱL π₂) :
    (f - g).toContinuousLinearMap = f.toContinuousLinearMap - g.toContinuousLinearMap := rfl

/--
lemma `sub_apply` / 引理 `sub_apply`

English:
lemma sub_apply
  given: (f g : π₁ ->ⁱL π₂) (v : V)
  statement: (f - g) v = f v - g v
  proof: rfl

中文:
引理 sub_apply
  条件: (f g : π₁ ->ⁱL π₂) (v : V)
  结论: (f - g) v = f v - g v
  证明: rfl
-/
lemma sub_apply (f g : π₁ ->ⁱL π₂) (v : V) : (f - g) v = f v - g v := rfl

/--
lemma `sub_comp` / 引理 `sub_comp`

English:
lemma sub_comp
  given: (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂)
  proof: by
  ext; simp

中文:
引理 sub_comp
  条件: (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂)
  证明: by
  ext; simp
-/
lemma sub_comp (f g : π₂ ->ⁱL π₃) (h : π₁ ->ⁱL π₂) :
    (f - g).comp h = f.comp h - g.comp h := by
  ext; simp

/--
lemma `comp_sub` / 引理 `comp_sub`

English:
lemma comp_sub
  given: (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂)
  proof: by
  ext; simp

中文:
引理 comp_sub
  条件: (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂)
  证明: by
  ext; simp
-/
lemma comp_sub (f : π₂ ->ⁱL π₃) (g h : π₁ ->ⁱL π₂) :
    f.comp (g - h) = f.comp g - f.comp h := by
  ext; simp

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
  body: ⟨s • f.toContinuousLinearMap, fun g => by
    rw [ContinuousLinearMap.smul_comp]; rw [f.2]; rw [ContinuousLinearMap.comp_smul]⟩

中文:
实例 instSMul
  签名: {S : 类型} [幺半群 S] [分配乘法作用 S W] [标量交换类 R S W]
  定义体: ⟨s • f.toContinuousLinearMap, fun g => by
    rw [ContinuousLinearMap.smul_comp]; rw [f.2]; rw [ContinuousLinearMap.comp_smul]⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, comp_smul, f.toContinuousLinearMap, smul_comp, toContinuousLinearMap
-/
instance instSMul {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] :
    SMul S (π₁ ->ⁱL π₂) where
  smul s f := ⟨s • f.toContinuousLinearMap, fun g => by
    rw [ContinuousLinearMap.smul_comp]; rw [f.2]; rw [ContinuousLinearMap.comp_smul]⟩

section addcommgroup

variable {S : Type*} [Monoid S] [DistribMulAction S W] [SMulCommClass R S W]
  [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R]

@[simp]
/--
lemma `toContinuousLinearMap_smul` / 引理 `toContinuousLinearMap_smul`

English:
lemma toContinuousLinearMap_smul
  given: (s : S) (f : π₁ ->ⁱL π₂)
  proof: rfl

中文:
引理 toContinuousLinearMap_smul
  条件: (s : S) (f : π₁ ->ⁱL π₂)
  证明: rfl
-/
lemma toContinuousLinearMap_smul (s : S) (f : π₁ ->ⁱL π₂) :
    (s • f).toContinuousLinearMap = s • f.toContinuousLinearMap := rfl

/--
lemma `smul_apply` / 引理 `smul_apply`

English:
lemma smul_apply
  given: (s : S) (f : π₁ ->ⁱL π₂) (v : V)
  statement: (s • f) v = s • f v
  proof: rfl

中文:
引理 smul_apply
  条件: (s : S) (f : π₁ ->ⁱL π₂) (v : V)
  结论: (s • f) v = s • f v
  证明: rfl
-/
lemma smul_apply (s : S) (f : π₁ ->ⁱL π₂) (v : V) : (s • f) v = s • f v := rfl

/--
lemma `smul_comp` / 引理 `smul_comp`

English:
lemma smul_comp
  statement: {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
  proof: by
  ext; simp

中文:
引理 smul_comp
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S U] [标量交换类 R S U]
  证明: by
  ext; simp
-/
lemma smul_comp {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    (s : S) (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π₂) : (s • f).comp g = s • (f.comp g) := by
  ext; simp

/--
lemma `comp_smul` / 引理 `comp_smul`

English:
lemma comp_smul
  statement: {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
  proof: by
  ext; simp

中文:
引理 comp_smul
  结论: {S : 类型} [幺半群 S] [分配乘法作用 S U] [标量交换类 R S U]
  证明: by
  ext; simp
-/
lemma comp_smul {S : Type*} [Monoid S] [DistribMulAction S U] [SMulCommClass R S U]
    [ContinuousConstSMul S U] [LinearMap.CompatibleSMul U U S R]
    [DistribMulAction S W] [SMulCommClass R S W] [ContinuousConstSMul S W]
    [LinearMap.CompatibleSMul W W S R] [LinearMap.CompatibleSMul W U S R]
    (s : S) (f : π₂ ->ⁱL π₃) (g : π₁ ->ⁱL π₂) : f.comp (s • g) = s • (f.comp g) := by
  ext; simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (π₁ ->ⁱL π₂)
  body: fast_instance% toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ => toContinuousLinearMap_smul _ _) (fun _ _ => toContinuousLinearMap_smul _ _)

中文:
实例 :
  签名: 加法交换群 (π₁ ->ⁱL π₂)
  定义体: fast_instance% toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ => toContinuousLinearMap_smul _ _) (fun _ _ => toContinuousLinearMap_smul _ _)

Depends on / 依赖: addCommGroup, fast_instance, toContinuousLinearMap_add, toContinuousLinearMap_injective, toContinuousLinearMap_injective.addCommGroup, toContinuousLinearMap_neg, toContinuousLinearMap_smul, toContinuousLinearMap_sub, toContinuousLinearMap_zero
-/
instance : AddCommGroup (π₁ ->ⁱL π₂) :=
  fast_instance% toContinuousLinearMap_injective.addCommGroup _ toContinuousLinearMap_zero
    toContinuousLinearMap_add toContinuousLinearMap_neg toContinuousLinearMap_sub
    (fun _ _ => toContinuousLinearMap_smul _ _) (fun _ _ => toContinuousLinearMap_smul _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction S (π₁ ->ⁱL π₂)
  body: by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [smul_add]

中文:
实例 :
  签名: 分配乘法作用 S (π₁ ->ⁱL π₂)
  定义体: by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [smul_add]

Depends on / 依赖: mul_smul, smul_add, smul_zero
-/
instance : DistribMulAction S (π₁ ->ⁱL π₂) where
  one_smul _ := by ext; simp
  mul_smul _ _ _ := by ext; simp [mul_smul]
  smul_zero _ := by ext; simp
  smul_add _ _ _ := by ext; simp [smul_add]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: {S : Type*} [Ring S] [Module S W] [SMulCommClass R S W]
  body: by ext; simp [add_smul]
  zero_smul _ := by ext; simp

中文:
实例 instModule
  签名: {S : 类型} [环 S] [模 S W] [标量交换类 R S W]
  定义体: by ext; simp [add_smul]
  zero_smul _ := by ext; simp

Depends on / 依赖: add_smul, zero_smul
-/
instance instModule {S : Type*} [Ring S] [Module S W] [SMulCommClass R S W]
    [ContinuousConstSMul S W] [LinearMap.CompatibleSMul W W S R] :
    Module S (π₁ ->ⁱL π₂) where
  add_smul _ _ _ := by ext; simp [add_smul]
  zero_smul _ := by ext; simp

end addcommgroup

end ContIntertwiningMap

namespace ContRepresentation

/--
Definition of `Equiv` / `Equiv` 的定义

English:
structure Equiv
  parameters: (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W)
  (no additional axioms)

中文:
结构 等价
  参数: (π₁ : 余ntRepresentation R G V) (π₂ : 余ntRepresentation R G W)
  (无附加公理)
-/
structure Equiv (π₁ : ContRepresentation R G V) (π₂ : ContRepresentation R G W) extends
    V ≃L[R] W, ContIntertwiningMap π₁ π₂ where mk'' ::

attribute [coe] Equiv.toContIntertwiningMap

/-- Underlying continuous linear isomorphism of an equivalence of continuous representations. -/
add_decl_doc Equiv.toContinuousLinearEquiv

/-- The continuous intertwining map underlying an equivalence of continuous representations. -/
add_decl_doc Equiv.toContIntertwiningMap

namespace Equiv

variable {ρ : ContRepresentation R G V} {σ : ContRepresentation R G W}
  {τ : ContRepresentation R G U} (φ : Equiv ρ σ)

/--
lemma `isIntertwining` / 引理 `isIntertwining`

English:
lemma isIntertwining
  given: (g : G)
  proof: φ.isIntertwining' g

中文:
引理 is整数ertwining
  条件: (g : G)
  证明: φ.isIntertwining' g

Depends on / 依赖: isIntertwining
-/
lemma isIntertwining (g : G) :
    φ.toContinuousLinearEquiv.toContinuousLinearMap ∘L (ρ g) =
      (σ g) ∘L φ.toContinuousLinearEquiv.toContinuousLinearMap :=
  φ.isIntertwining' g

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e)
  body: e
  cont := e.continuous
  isIntertwining' := he

中文:
定义 mk
  签名: (e : V ≃L[R] W) (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e)
  定义体: e
  cont := e.continuous
  isIntertwining' := he
-/
def mk (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) : ρ.Equiv σ where
  __ := e
  cont := e.continuous
  isIntertwining' := he

/--
lemma `toContinuousLinearEquiv_mk'` / 引理 `toContinuousLinearEquiv_mk'`

English:
lemma toContinuousLinearEquiv_mk'
  given: {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e)
  proof: rfl

中文:
引理 toContinuousLinearEquiv_mk'
  条件: {e : V ≃L[R] W} (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e)
  证明: rfl
-/
lemma toContinuousLinearEquiv_mk' {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearEquiv = e := rfl

/--
lemma `toContIntertwiningMap_mk'` / 引理 `toContIntertwiningMap_mk'`

English:
lemma toContIntertwiningMap_mk'
  given: (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e)
  proof: rfl

@[simp]

中文:
引理 toCont整数ertwiningMap_mk'
  条件: (e : V ≃L[R] W) (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e)
  证明: rfl

@[simp]
-/
lemma toContIntertwiningMap_mk' (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContIntertwiningMap = ⟨e.toContinuousLinearMap, he⟩ := rfl

@[simp]
/--
lemma `toContinuousLinearMap_mk'` / 引理 `toContinuousLinearMap_mk'`

English:
lemma toContinuousLinearMap_mk'
  given: (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e)
  proof: rfl

中文:
引理 toContinuousLinearMap_mk'
  条件: (e : V ≃L[R] W) (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e)
  证明: rfl
-/
lemma toContinuousLinearMap_mk' (e : V ≃L[R] W) (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).toContinuousLinearMap = e.toContinuousLinearMap := rfl

/--
lemma `toContinuousLinearEquiv_injective` / 引理 `toContinuousLinearEquiv_injective`

English:
lemma toContinuousLinearEquiv_injective
  proof: fun φ ψ h => by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h

中文:
引理 toContinuousLinearEquiv_injective
  证明: fun φ ψ h => by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h

Depends on / 依赖: ContIntertwiningMap, ContIntertwiningMap.ext_iff, ext_iff
-/
lemma toContinuousLinearEquiv_injective :
    Function.Injective (toContinuousLinearEquiv : (σ.Equiv ρ) -> _) :=
  fun φ ψ h => by cases φ; cases ψ; simpa [ContIntertwiningMap.ext_iff] using h

/--
lemma `toContinuousLinearEquiv_inj` / 引理 `toContinuousLinearEquiv_inj`

English:
lemma toContinuousLinearEquiv_inj
  given: (φ ψ : σ.Equiv ρ)
  proof: toContinuousLinearEquiv_injective.eq_iff

中文:
引理 toContinuousLinearEquiv_inj
  条件: (φ ψ : σ.等价 ρ)
  证明: toContinuousLinearEquiv_injective.eq_iff

Depends on / 依赖: eq_iff, toContinuousLinearEquiv_injective, toContinuousLinearEquiv_injective.eq_iff
-/
lemma toContinuousLinearEquiv_inj (φ ψ : σ.Equiv ρ) :
    φ.toContinuousLinearEquiv = ψ.toContinuousLinearEquiv ↔ φ = ψ :=
  toContinuousLinearEquiv_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (Equiv ρ σ) V W
  body: φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all

中文:
实例 :
  签名: 等价状 (等价 ρ σ) V W
  定义体: φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all

Depends on / 依赖: toContinuousLinearEquiv
-/
instance : EquivLike (Equiv ρ σ) V W where
  coe φ := φ.toContinuousLinearEquiv
  inv φ := φ.invFun
  left_inv e := e.left_inv
  right_inv e := e.right_inv
  coe_injective' φ ψ h1 h2 := by cases φ; cases ψ; simp_all

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousLinearEquivClass (σ.Equiv ρ) R W V
  body: f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]

中文:
实例 :
  签名: ContinuousLinearEquivClass (σ.等价 ρ) R W V
  定义体: f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]

Depends on / 依赖: f.map_add, map_add
-/
instance : ContinuousLinearEquivClass (σ.Equiv ρ) R W V where
  map_add f := f.map_add
  map_smulₛₗ f := f.map_smul
  map_continuous f := f.cont
  inv_continuous f := f.continuous_invFun

@[simp]
/--
lemma `mk_apply` / 引理 `mk_apply`

English:
lemma mk_apply
  given: {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) (v : V)
  proof: rfl

@[ext]

中文:
引理 mk_apply
  条件: {e : V ≃L[R] W} (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e) (v : V)
  证明: rfl

@[ext]
-/
lemma mk_apply {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) (v : V) :
    (mk e he) v = e v := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ)
  statement: φ = ψ
  proof: by
  cases φ; cases ψ
  simpa using h

中文:
引理 ext
  条件: {φ ψ : 等价 ρ σ} (h : (φ : V -> W) = ψ)
  结论: φ = ψ
  证明: by
  cases φ; cases ψ
  simpa using h
-/
lemma ext {φ ψ : Equiv ρ σ} (h : (φ : V -> W) = ψ) : φ = ψ := by
  cases φ; cases ψ
  simpa using h

variable (ρ) in
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: : Equiv ρ ρ
  body: mk (ContinuousLinearEquiv.refl R V) (by simp)

中文:
定义 refl
  签名: : 等价 ρ ρ
  定义体: mk (ContinuousLinearEquiv.refl R V) (by simp)

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.refl
-/
def refl : Equiv ρ ρ := mk (ContinuousLinearEquiv.refl R V) (by simp)

/--
lemma `toContIntertwiningMap_refl` / 引理 `toContIntertwiningMap_refl`

English:
lemma toContIntertwiningMap_refl
  statement: (refl ρ).toContIntertwiningMap = .id
  proof: rfl

中文:
引理 toCont整数ertwiningMap_refl
  结论: (refl ρ).toCont整数ertwiningMap = .id
  证明: rfl
-/
@[simp] lemma toContIntertwiningMap_refl : (refl ρ).toContIntertwiningMap = .id := rfl

/--
lemma `toContinuousLinearMap_refl` / 引理 `toContinuousLinearMap_refl`

English:
lemma toContinuousLinearMap_refl
  proof: rfl

中文:
引理 toContinuousLinearMap_refl
  证明: rfl
-/
@[simp] lemma toContinuousLinearMap_refl :
    (refl ρ).toContinuousLinearMap = ContinuousLinearMap.id R V := rfl

/--
lemma `refl_apply` / 引理 `refl_apply`

English:
lemma refl_apply
  given: (v : V)
  statement: refl ρ v = v
  proof: rfl

中文:
引理 refl_apply
  条件: (v : V)
  结论: refl ρ v = v
  证明: rfl
-/
@[simp] lemma refl_apply (v : V) : refl ρ v = v := rfl

/--
lemma `coe_toContIntertwiningMap` / 引理 `coe_toContIntertwiningMap`

English:
lemma coe_toContIntertwiningMap
  statement: ⇑φ.toContIntertwiningMap = φ
  proof: rfl

中文:
引理 coe_toCont整数ertwiningMap
  结论: ⇑φ.toCont整数ertwiningMap = φ
  证明: rfl
-/
@[simp] lemma coe_toContIntertwiningMap : ⇑φ.toContIntertwiningMap = φ := rfl

/--
lemma `coe_toContinuousLinearMap` / 引理 `coe_toContinuousLinearMap`

English:
lemma coe_toContinuousLinearMap
  statement: ⇑φ.toContinuousLinearMap = φ
  proof: rfl

中文:
引理 coe_toContinuousLinearMap
  结论: ⇑φ.toContinuousLinearMap = φ
  证明: rfl

Depends on / 依赖: CommMonoidWithZero, UniqueFactorizationMonoid
-/
lemma coe_toContinuousLinearMap : ⇑φ.toContinuousLinearMap = φ := rfl

/--
lemma `coe_invFun` / 引理 `coe_invFun`

English:
lemma coe_invFun
  statement: φ.invFun = φ.symm
  proof: rfl

中文:
引理 coe_invFun
  结论: φ.invFun = φ.symm
  证明: rfl
-/
lemma coe_invFun : φ.invFun = φ.symm := rfl

/--
theorem `toContinuousLinearEquiv_toContinuousLinearMap` / 定理 `toContinuousLinearEquiv_toContinuousLinearMap`

English:
theorem toContinuousLinearEquiv_toContinuousLinearMap
  proof: rfl

中文:
定理 toContinuousLinearEquiv_toContinuousLinearMap
  证明: rfl
-/
theorem toContinuousLinearEquiv_toContinuousLinearMap :
    φ.toContinuousLinearEquiv.toContinuousLinearMap =
      φ.toContIntertwiningMap.toContinuousLinearMap := rfl

/--
theorem `toContinuousLinearEquiv_apply` / 定理 `toContinuousLinearEquiv_apply`

English:
theorem toContinuousLinearEquiv_apply
  given: (v : V)
  proof: rfl

中文:
定理 toContinuousLinearEquiv_apply
  条件: (v : V)
  证明: rfl
-/
theorem toContinuousLinearEquiv_apply (v : V) :
    φ.toContinuousLinearEquiv v = φ.toContIntertwiningMap v := rfl

open ContinuousLinearMap in
/-- The equiv between continuous representations are symmetric. -/
@[symm]
/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: : Equiv σ ρ
  body: mk φ.toContinuousLinearEquiv.symm fun g => by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

中文:
定义 symm
  签名: : 等价 σ ρ
  定义体: mk φ.toContinuousLinearEquiv.symm fun g => by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

Depends on / 依赖: cancel_left, comp_assoc, injective, isIntertwining, toContinuousLinearEquiv, toContinuousLinearEquiv.injective, toContinuousLinearEquiv.symm, toContinuousLinearEquiv.toContinuousLinearMap, toContinuousLinearMap
-/
def symm : Equiv σ ρ := mk φ.toContinuousLinearEquiv.symm fun g => by
  rw [← cancel_left' (g := φ.toContinuousLinearEquiv.toContinuousLinearMap)
    φ.toContinuousLinearEquiv.injective]; rw [← comp_assoc]; rw [← comp_assoc]
  simp [φ.isIntertwining g, comp_assoc]

open ContinuousLinearMap

/--
lemma `_root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining` / 引理 `_root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining`

English:
lemma _root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining
  statement: {e : V ≃L[R] W}
  proof: (mk e he).symm.isIntertwining g

@[simp]

中文:
引理 _root_.连续线性等价.is整数ertwining_symm_is整数ertwining
  结论: {e : V ≃L[R] W}
  证明: (mk e he).symm.isIntertwining g

@[simp]

Depends on / 依赖: isIntertwining, symm.isIntertwining
-/
lemma _root_.ContinuousLinearEquiv.isIntertwining_symm_isIntertwining {e : V ≃L[R] W}
    (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) (g : G) :
    e.symm ∘L (σ g) = (ρ g) ∘L e.symm :=
  (mk e he).symm.isIntertwining g

@[simp]
/--
lemma `mk_symm` / 引理 `mk_symm`

English:
lemma mk_symm
  given: {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e)
  proof: rfl

中文:
引理 mk_symm
  条件: {e : V ≃L[R] W} (he : 对任意 g, e ∘L (ρ g) = (σ g) ∘L e)
  证明: rfl
-/
lemma mk_symm {e : V ≃L[R] W} (he : forall g, e ∘L (ρ g) = (σ g) ∘L e) :
    (mk e he).symm = mk e.symm (e.isIntertwining_symm_isIntertwining he) := rfl

/--
lemma `toLinearMap_symm` / 引理 `toLinearMap_symm`

English:
lemma toLinearMap_symm
  given: (φ : Equiv ρ σ)
  statement: (symm φ).toLinearMap = φ.toLinearEquiv.symm
  proof: rfl

中文:
引理 toLinearMap_symm
  条件: (φ : 等价 ρ σ)
  结论: (symm φ).toLinearMap = φ.toLinearEquiv.symm
  证明: rfl
-/
lemma toLinearMap_symm (φ : Equiv ρ σ) : (symm φ).toLinearMap = φ.toLinearEquiv.symm := rfl

/--
lemma `coe_symm` / 引理 `coe_symm`

English:
lemma coe_symm
  given: (φ : Equiv ρ σ)
  statement: ⇑φ.toLinearEquiv.symm = φ.symm
  proof: rfl

中文:
引理 coe_symm
  条件: (φ : 等价 ρ σ)
  结论: ⇑φ.toLinearEquiv.symm = φ.symm
  证明: rfl
-/
lemma coe_symm (φ : Equiv ρ σ) : ⇑φ.toLinearEquiv.symm = φ.symm := rfl

/-- Composition of two `Equiv`s. -/
@[trans]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  body: mk
(φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) fun g => by
  rw [← ContinuousLinearEquiv.comp_coe]; rw [comp_assoc]; rw [φ.isIntertwining]; rw [← comp_assoc]; rw [ψ.isIntertwining]; rw [comp_assoc]

@[simp]

中文:
定义 trans
  签名: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  定义体: mk
(φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) fun g => by
  rw [← ContinuousLinearEquiv.comp_coe]; rw [comp_assoc]; rw [φ.isIntertwining]; rw [← comp_assoc]; rw [ψ.isIntertwining]; rw [comp_assoc]

@[simp]
-/
def trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) : Equiv ρ τ := mk
(φ.toContinuousLinearEquiv.trans ψ.toContinuousLinearEquiv) fun g => by
  rw [← ContinuousLinearEquiv.comp_coe]; rw [comp_assoc]; rw [φ.isIntertwining]; rw [← comp_assoc]; rw [ψ.isIntertwining]; rw [comp_assoc]

@[simp]
/--
lemma `toContIntertwiningMap_trans` / 引理 `toContIntertwiningMap_trans`

English:
lemma toContIntertwiningMap_trans
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  proof: rfl

@[simp]

中文:
引理 toCont整数ertwiningMap_trans
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  证明: rfl

@[simp]
-/
lemma toContIntertwiningMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (φ.trans ψ).toContIntertwiningMap = ψ.toContIntertwiningMap.comp φ.toContIntertwiningMap := rfl

@[simp]
/--
lemma `toContinuousLinearMap_trans` / 引理 `toContinuousLinearMap_trans`

English:
lemma toContinuousLinearMap_trans
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ)
  proof: rfl

@[simp]

中文:
引理 toContinuousLinearMap_trans
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ)
  证明: rfl

@[simp]
-/
lemma toContinuousLinearMap_trans (φ : Equiv ρ σ) (ψ : Equiv σ τ) :
    (trans φ ψ).toContinuousLinearMap = ψ.toContinuousLinearMap.comp φ.toContinuousLinearMap := rfl

@[simp]
/--
lemma `trans_apply` / 引理 `trans_apply`

English:
lemma trans_apply
  given: (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V)
  proof: rfl

@[simp]

中文:
引理 trans_apply
  条件: (φ : 等价 ρ σ) (ψ : 等价 σ τ) (v : V)
  证明: rfl

@[simp]
-/
lemma trans_apply (φ : Equiv ρ σ) (ψ : Equiv σ τ) (v : V) :
    trans φ ψ v = ψ (φ v) := rfl

@[simp]
/--
lemma `apply_symm_apply` / 引理 `apply_symm_apply`

English:
lemma apply_symm_apply
  given: (φ : Equiv ρ σ) (v : W)
  statement: φ (φ.symm v) = v
  proof: φ.right_inv v

@[simp]

中文:
引理 apply_symm_apply
  条件: (φ : 等价 ρ σ) (v : W)
  结论: φ (φ.symm v) = v
  证明: φ.right_inv v

@[simp]

Depends on / 依赖: right_inv
-/
lemma apply_symm_apply (φ : Equiv ρ σ) (v : W) : φ (φ.symm v) = v := φ.right_inv v

@[simp]
/--
lemma `symm_apply_apply` / 引理 `symm_apply_apply`

English:
lemma symm_apply_apply
  given: (φ : Equiv ρ σ) (v : V)
  statement: φ.symm (φ v) = v
  proof: φ.left_inv v

@[simp]

中文:
引理 symm_apply_apply
  条件: (φ : 等价 ρ σ) (v : V)
  结论: φ.symm (φ v) = v
  证明: φ.left_inv v

@[simp]

Depends on / 依赖: left_inv
-/
lemma symm_apply_apply (φ : Equiv ρ σ) (v : V) : φ.symm (φ v) = v := φ.left_inv v

@[simp]
/--
lemma `trans_symm` / 引理 `trans_symm`

English:
lemma trans_symm
  given: (φ : Equiv ρ σ)
  statement: φ.trans φ.symm = .refl ρ
  proof: by ext; simp

@[simp]

中文:
引理 trans_symm
  条件: (φ : 等价 ρ σ)
  结论: φ.trans φ.symm = .refl ρ
  证明: by ext; simp

@[simp]
-/
lemma trans_symm (φ : Equiv ρ σ) : φ.trans φ.symm = .refl ρ := by ext; simp

@[simp]
/--
lemma `symm_trans` / 引理 `symm_trans`

English:
lemma symm_trans
  given: (φ : Equiv ρ σ)
  statement: φ.symm.trans φ = .refl σ
  proof: by ext; simp

中文:
引理 symm_trans
  条件: (φ : 等价 ρ σ)
  结论: φ.symm.trans φ = .refl σ
  证明: by ext; simp
-/
lemma symm_trans (φ : Equiv ρ σ) : φ.symm.trans φ = .refl σ := by ext; simp

end Equiv

variable (R G V) in
/--
Definition of `trivial` / `trivial` 的定义

English:
definition trivial
  signature: : ContRepresentation R G V
  body: ofMonoidHom 1

@[simp]

中文:
定义 trivial
  签名: : 余ntRepresentation R G V
  定义体: ofMonoidHom 1

@[simp]

Depends on / 依赖: ofMonoidHom
-/
def trivial : ContRepresentation R G V := ofMonoidHom 1

@[simp]
/--
lemma `trivial_apply` / 引理 `trivial_apply`

English:
lemma trivial_apply
  given: (g : G) (v : V)
  statement: trivial R G V g v = v
  proof: rfl

中文:
引理 trivial_apply
  条件: (g : G) (v : V)
  结论: trivial R G V g v = v
  证明: rfl
-/
lemma trivial_apply (g : G) (v : V) : trivial R G V g v = v := rfl

/-- The restriction of a continuous representation along a monoid homomorphism. -/
@[implicit_reducible]
/--
Definition of `restrict` / `restrict` 的定义

English:
definition restrict
  signature: {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G)
  body: ofMonoidHom (π.toMonoidHom.comp φ)

中文:
定义 restrict
  签名: {H : 类型} [幺半群 H] (π : 余ntRepresentation R G V) (φ : H ->* G)
  定义体: ofMonoidHom (π.toMonoidHom.comp φ)

Depends on / 依赖: ofMonoidHom, toMonoidHom, toMonoidHom.comp
-/
def restrict {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G) :
    ContRepresentation R H V := ofMonoidHom (π.toMonoidHom.comp φ)

/--
lemma `restrict_apply` / 引理 `restrict_apply`

English:
lemma restrict_apply
  statement: {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G)
  proof: rfl

@[simp]

中文:
引理 restrict_apply
  结论: {H : 类型} [幺半群 H] (π : 余ntRepresentation R G V) (φ : H ->* G)
  证明: rfl

@[simp]
-/
lemma restrict_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G)
    (h : H) : π.restrict φ h = π (φ h) := rfl

@[simp]
/--
lemma `restrict_apply_apply` / 引理 `restrict_apply_apply`

English:
lemma restrict_apply_apply
  statement: {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G)
  proof: rfl

中文:
引理 restrict_apply_apply
  结论: {H : 类型} [幺半群 H] (π : 余ntRepresentation R G V) (φ : H ->* G)
  证明: rfl
-/
lemma restrict_apply_apply {H : Type*} [Monoid H] (π : ContRepresentation R G V) (φ : H ->* G)
    (h : H) (v : V) : π.restrict φ h v = π (φ h) v := rfl

/--
Definition of `_root_.ContIntertwiningMap.restrict` / `_root_.ContIntertwiningMap.restrict` 的定义

English:
definition _root_.ContIntertwiningMap.restrict
  signature: {H : Type*} [Monoid H] {π : ContRepresentation R G V}
  body: f.toContinuousLinearMap
  isIntertwining' h := by
    ext; simp [f.toContinuousLinearMap_apply, f.isIntertwining]

中文:
定义 _root_.余nt整数ertwining映射.restrict
  签名: {H : 类型} [幺半群 H] {π : 余ntRepresentation R G V}
  定义体: f.toContinuousLinearMap
  isIntertwining' h := by
    ext; simp [f.toContinuousLinearMap_apply, f.isIntertwining]

Depends on / 依赖: f.toContinuousLinearMap, toContinuousLinearMap
-/
def _root_.ContIntertwiningMap.restrict {H : Type*} [Monoid H] {π : ContRepresentation R G V}
    {π' : ContRepresentation R G W} (φ : H ->* G) (f : π ->ⁱL π') :
    π.restrict φ ->ⁱL π'.restrict φ where
  __ := f.toContinuousLinearMap
  isIntertwining' h := by
    ext; simp [f.toContinuousLinearMap_apply, f.isIntertwining]

/--
lemma `_root_.ContIntertwiningMap.restrict_toContinuousLinearMap` / 引理 `_root_.ContIntertwiningMap.restrict_toContinuousLinearMap`

English:
lemma _root_.ContIntertwiningMap.restrict_toContinuousLinearMap
  statement: {H : Type*} [Monoid H]
  proof: rfl

中文:
引理 _root_.余nt整数ertwining映射.restrict_toContinuousLinearMap
  结论: {H : 类型} [幺半群 H]
  证明: rfl
-/
lemma _root_.ContIntertwiningMap.restrict_toContinuousLinearMap {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H ->* G) (f : π ->ⁱL π') :
    (f.restrict φ).toContinuousLinearMap = f.toContinuousLinearMap := rfl

/--
lemma `_root_.ContIntertwiningMap.restrict_apply` / 引理 `_root_.ContIntertwiningMap.restrict_apply`

English:
lemma _root_.ContIntertwiningMap.restrict_apply
  statement: {H : Type*} [Monoid H]
  proof: rfl

中文:
引理 _root_.余nt整数ertwining映射.restrict_apply
  结论: {H : 类型} [幺半群 H]
  证明: rfl
-/
@[simp] lemma _root_.ContIntertwiningMap.restrict_apply {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H ->* G)
    (f : π ->ⁱL π') (v : V) : f.restrict φ v = f v := rfl

/--
lemma `_root_.ContIntertwiningMap.restrict_sub` / 引理 `_root_.ContIntertwiningMap.restrict_sub`

English:
lemma _root_.ContIntertwiningMap.restrict_sub
  statement: {H : Type*} [Monoid H]
  proof: rfl

中文:
引理 _root_.余nt整数ertwining映射.restrict_sub
  结论: {H : 类型} [幺半群 H]
  证明: rfl
-/
lemma _root_.ContIntertwiningMap.restrict_sub {H : Type*} [Monoid H]
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W} (φ : H ->* G)
    (f g : π ->ⁱL π') : (f - g).restrict φ = f.restrict φ - g.restrict φ := rfl

/--
Definition of `invariants` / `invariants` 的定义

English:
definition invariants
  signature: (π : ContRepresentation R G V)
  body: {v | forall g, π g v = v}
  zero_mem' := by simp
  add_mem' _ _ := by simp_all
  smul_mem' _ _ hv g := by simp [hv g]

@[simp]

中文:
定义 invariants
  签名: (π : 余ntRepresentation R G V)
  定义体: {v | forall g, π g v = v}
  zero_mem' := by simp
  add_mem' _ _ := by simp_all
  smul_mem' _ _ hv g := by simp [hv g]

@[simp]
-/
def invariants (π : ContRepresentation R G V) : Submodule R V where
  carrier := {v | forall g, π g v = v}
  zero_mem' := by simp
  add_mem' _ _ := by simp_all
  smul_mem' _ _ hv g := by simp [hv g]

@[simp]
/--
lemma `mem_invariants` / 引理 `mem_invariants`

English:
lemma mem_invariants
  given: {π : ContRepresentation R G V} (v : V)
  proof: Iff.rfl

中文:
引理 mem_invariants
  条件: {π : 余ntRepresentation R G V} (v : V)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_invariants {π : ContRepresentation R G V} (v : V) :
    v in π.invariants ↔ forall g, π g v = v := Iff.rfl

/--
Definition of `_root_.ContIntertwiningMap.mapInvariants` / `_root_.ContIntertwiningMap.mapInvariants` 的定义

English:
definition _root_.ContIntertwiningMap.mapInvariants
  body: f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

中文:
定义 _root_.余nt整数ertwining映射.mapInvariants
  定义体: f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

Depends on / 依赖: contextual, f.isIntertwining, f.toContinuousLinearMap.restrict, f.toContinuousLinearMap_apply, isIntertwining, restrict, toContinuousLinearMap, toContinuousLinearMap_apply
-/
def _root_.ContIntertwiningMap.mapInvariants
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π ->ⁱL π') : π.invariants ->L[R] π'.invariants :=
f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewrite, this lemma should be used when `mapInvariants` is
-- applied to `(homogeneousCochains X).X 0`
/--
lemma `_root_.ContIntertwiningMap.mapInvariants_apply` / 引理 `_root_.ContIntertwiningMap.mapInvariants_apply`

English:
lemma _root_.ContIntertwiningMap.mapInvariants_apply
  proof: rfl

@[simp]

中文:
引理 _root_.余nt整数ertwining映射.mapInvariants_apply
  证明: rfl

@[simp]
-/
lemma _root_.ContIntertwiningMap.mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π ->ⁱL π') (v : π.invariants) :
    f.mapInvariants v = f v := rfl

@[simp]
/--
lemma `_root_.ContIntertwiningMap.mk_mapInvariants_apply` / 引理 `_root_.ContIntertwiningMap.mk_mapInvariants_apply`

English:
lemma _root_.ContIntertwiningMap.mk_mapInvariants_apply
  proof: rfl

中文:
引理 _root_.余nt整数ertwining映射.mk_mapInvariants_apply
  证明: rfl
-/
lemma _root_.ContIntertwiningMap.mk_mapInvariants_apply
    {π : ContRepresentation R G V} {π' : ContRepresentation R G W}
    (f : π ->ⁱL π') (v : V) (hv : v in π.invariants) :
    f.mapInvariants ⟨v, hv⟩ = f v := rfl

variable {H : Type*} [Monoid H]

/--
lemma `invariants_le_invariants_restrict` / 引理 `invariants_le_invariants_restrict`

English:
lemma invariants_le_invariants_restrict
  given: (π : ContRepresentation R G V) (φ : H ->* G)
  proof: fun _ hv h => hv (φ h)

中文:
引理 invariants_le_invariants_restrict
  条件: (π : 余ntRepresentation R G V) (φ : H ->* G)
  证明: fun _ hv h => hv (φ h)
-/
lemma invariants_le_invariants_restrict (π : ContRepresentation R G V) (φ : H ->* G) :
    π.invariants <= (π.restrict φ).invariants :=
  fun _ hv h => hv (φ h)

variable {π : ContRepresentation R G V} {π' : ContRepresentation R H W}

/--
Definition of `_root_.ContIntertwiningMap.mapInvariantsOfRes` / `_root_.ContIntertwiningMap.mapInvariantsOfRes` 的定义

English:
definition _root_.ContIntertwiningMap.mapInvariantsOfRes
  signature: (φ : H ->* G)
  body: f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

中文:
定义 _root_.余nt整数ertwining映射.mapInvariantsOfRes
  签名: (φ : H ->* G)
  定义体: f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

Depends on / 依赖: contextual, f.isIntertwining, f.toContinuousLinearMap.restrict, f.toContinuousLinearMap_apply, isIntertwining, restrict, toContinuousLinearMap, toContinuousLinearMap_apply
-/
def _root_.ContIntertwiningMap.mapInvariantsOfRes (φ : H ->* G)
    (f : π.restrict φ ->ⁱL π') : π.invariants ->L[R] π'.invariants :=
f.toContinuousLinearMap.restrict by
    simp +contextual [f.toContinuousLinearMap_apply, ← f.isIntertwining]

-- provided for rewriting
/--
lemma `_root_.ContIntertwiningMap.mapInvariantsOfRes_apply` / 引理 `_root_.ContIntertwiningMap.mapInvariantsOfRes_apply`

English:
lemma _root_.ContIntertwiningMap.mapInvariantsOfRes_apply
  statement: (φ : H ->* G)
  proof: rfl

@[simp]

中文:
引理 _root_.余nt整数ertwining映射.mapInvariantsOfRes_apply
  结论: (φ : H ->* G)
  证明: rfl

@[simp]
-/
lemma _root_.ContIntertwiningMap.mapInvariantsOfRes_apply (φ : H ->* G)
    (f : π.restrict φ ->ⁱL π') (v : π.invariants) :
    f.mapInvariantsOfRes φ v = f v := rfl

@[simp]
/--
lemma `_root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply` / 引理 `_root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply`

English:
lemma _root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply
  statement: (φ : H ->* G)
  proof: rfl

中文:
引理 _root_.余nt整数ertwining映射.mk_mapInvariantsOfRes_apply
  结论: (φ : H ->* G)
  证明: rfl
-/
lemma _root_.ContIntertwiningMap.mk_mapInvariantsOfRes_apply (φ : H ->* G)
    (f : π.restrict φ ->ⁱL π') (v : V) (hv : v in π.invariants) :
    f.mapInvariantsOfRes φ ⟨v, hv⟩ = f v := rfl

-- TODO : define `IsTopologicalMonoid` and then replace `Homeomorph.mulLeft g⁻¹` with the
-- `ContinuousMap.mulRight g` to make `coind₁` work for monoids.
variable {G H : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace R]
  [ContinuousSMul R V] [ContinuousSMul R W] [Group H] [TopologicalSpace H]
  (φ : G ->ₜ* H) (π : ContRepresentation R G V)

/-- The underlying module of the coinduced continuous representation. -/
@[simps]
/--
Definition of `coindV` / `coindV` 的定义

English:
definition coindV
  signature: : Submodule R C(H, V) where
  body: {f | forall g h, f (φ g * h) = π g (f h)}
  add_mem' := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]

中文:
定义 coindV
  签名: : 子模 R C(H, V) where
  定义体: {f | forall g h, f (φ g * h) = π g (f h)}
  add_mem' := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
-/
def coindV : Submodule R C(H, V) where
  carrier := {f | forall g h, f (φ g * h) = π g (f h)}
  add_mem' := by simp +contextual
  zero_mem' := by simp
  smul_mem' := by simp +contextual

@[simp]
/--
lemma `mem_coindV` / 引理 `mem_coindV`

English:
lemma mem_coindV
  given: (f : C(H, V))
  statement: f in π.coindV φ ↔ forall g h, f (φ g * h) = π g (f h)
  proof: Iff.rfl

中文:
引理 mem_coindV
  条件: (f : C(H, V))
  结论: f in π.coindV φ ↔ 对任意 g h, f (φ g * h) = π g (f h)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_coindV (f : C(H, V)) : f in π.coindV φ ↔ forall g h, f (φ g * h) = π g (f h) := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ContinuousSMul R (π.coindV φ)
  body: by continuity

中文:
实例 :
  签名: 连续标量乘法 R (π.coindV φ)
  定义体: by continuity

Depends on / 依赖: continuity
-/
instance : ContinuousSMul R (π.coindV φ) where
  continuous_smul := by continuity

variable [IsTopologicalGroup G] [IsTopologicalGroup H]

/-- The coinduced continuous representation where the action of `H` is defined by
  `h ↦ f ↦ f ∘ (· * h)`. -/
@[simps]
/--
Definition of `coind` / `coind` 的定义

English:
definition coind
  signature: (π : ContRepresentation R G V)
  body: {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
cont := continuous_induced_rng.2 by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

中文:
定义 coind
  签名: (π : 余ntRepresentation R G V)
  定义体: {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
cont := continuous_induced_rng.2 by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]
-/
def coind (π : ContRepresentation R G V) : ContRepresentation R H (π.coindV φ) where
  toMonoidHom.toFun h := {
    toFun | ⟨f, hf⟩ => ⟨f.comp (ContinuousMap.mulRight h), by simp [mul_assoc, hf _]⟩
    map_add' _ _ := by simp
    map_smul' _ _ := by simp
cont := continuous_induced_rng.2 by
      simpa using! (ContinuousMap.mulRight h).continuous_precomp.comp continuous_subtype_val}
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' h1 h2 := by ext; simp [ContinuousMap.mulRight_mul]

open ContinuousMap

/--
Definition of `coind₁` / `coind₁` 的定义

English:
definition coind₁
  signature: (π : ContRepresentation R G V)
  body: {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]

中文:
定义 coind₁
  签名: (π : 余ntRepresentation R G V)
  定义体: {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
-/
def coind₁ (π : ContRepresentation R G V) :
    ContRepresentation R G C(G, V) where
  toMonoidHom.toFun g := {
    toFun f := .comp (π g) (f.comp (ContinuousMap.mulLeft g⁻¹))
    map_add' _ _ := by ext; simp
    map_smul' _ _ := by ext; simp
    cont := (continuous_postcomp _).comp (continuous_precomp _)
  }
  toMonoidHom.map_one' := by ext; simp
  toMonoidHom.map_mul' _ _ := by ext; simp [mul_assoc]

@[simp]
/--
lemma `coind₁_apply_apply` / 引理 `coind₁_apply_apply`

English:
lemma coind₁_apply_apply
  given: (π : ContRepresentation R G V) (g : G) (f : C(G, V)) (x : G)
  proof: rfl

中文:
引理 coind₁_apply_apply
  条件: (π : 余ntRepresentation R G V) (g : G) (f : C(G, V)) (x : G)
  证明: rfl
-/
lemma coind₁_apply_apply (π : ContRepresentation R G V) (g : G) (f : C(G, V)) (x : G) :
    π.coind₁ g f x = π g (f (g⁻¹ * x)) := rfl

/-- The functoriality of `coind₁`. -/
@[simps]
/--
Definition of `coind₁Map` / `coind₁Map` 的定义

English:
definition coind₁Map
  signature: {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} (f : π₁ ->ⁱL π₂)
  body: (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

中文:
定义 coind₁Map
  签名: {π₁ : 余ntRepresentation R G V} {π₂ : 余ntRepresentation R G W} (f : π₁ ->ⁱL π₂)
  定义体: (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

Depends on / 依赖: ContinuousMap
-/
def coind₁Map {π₁ : ContRepresentation R G V} {π₂ : ContRepresentation R G W} (f : π₁ ->ⁱL π₂) :
    coind₁ π₁ ->ⁱL coind₁ π₂ where
  toFun := (f : ContinuousMap _ _).comp
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  isIntertwining' g := by ext; simp [f.isIntertwining]
  cont := continuous_postcomp _

/-- The naturality of the transformation from `𝟭 ⟶ coind₁`. -/
@[simps]
/--
Definition of `coind₁ι` / `coind₁ι` 的定义

English:
definition coind₁ι
  signature: (π : ContRepresentation R G V)
  body: ContinuousMap.const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

中文:
定义 coind₁ι
  签名: (π : 余ntRepresentation R G V)
  定义体: ContinuousMap.const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

Depends on / 依赖: ContinuousMap, ContinuousMap.const
-/
def coind₁ι (π : ContRepresentation R G V) : π ->ⁱL coind₁ π where
  toFun := ContinuousMap.const G
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' := by aesop
  cont := continuous_const'

/--
Definition of `coind₁Equivcoind` / `coind₁Equivcoind` 的定义

English:
definition coind₁Equivcoind
  signature: : (coind₁ (.trivial R (⊥ : Subgroup G) V)).Equiv
  body: .mk (Submodule.topContEquiv.symm.trans <|
    ContinuousLinearEquiv.ofEq _ _ (by simp [SetLike.ext_iff])) <| fun g => by
    simp [Subsingleton.elim g 1, ContinuousLinearMap.one_def]

中文:
定义 coind₁Equivcoind
  签名: : (coind₁ (.trivial R (⊥ : 子群 G) V)).等价
  定义体: .mk (Submodule.topContEquiv.symm.trans <|
    ContinuousLinearEquiv.ofEq _ _ (by simp [SetLike.ext_iff])) <| fun g => by
    simp [Subsingleton.elim g 1, ContinuousLinearMap.one_def]

Depends on / 依赖: Submodule, Submodule.topContEquiv.symm.trans, topContEquiv
-/
def coind₁Equivcoind : (coind₁ (.trivial R (⊥ : Subgroup G) V)).Equiv
  (coind 1 (.trivial R G V)) := .mk (Submodule.topContEquiv.symm.trans <|
    ContinuousLinearEquiv.ofEq _ _ (by simp [SetLike.ext_iff])) <| fun g => by
    simp [Subsingleton.elim g 1, ContinuousLinearMap.one_def]

section coind₁ResMap

variable [ContinuousSMul R U] {π' : ContRepresentation R H W} {π}

/--
Definition of `coind₁Res` / `coind₁Res` 的定义

English:
definition coind₁Res
  signature: (φ : H ->ₜ* G) (π : ContRepresentation R G V)
  body: ContinuousMap.compCLM R V φ.toContinuousMap
  isIntertwining' h := by
    ext F x
    simp [map_mul, map_inv]

@[simp]

中文:
定义 coind₁Res
  签名: (φ : H ->ₜ* G) (π : 余ntRepresentation R G V)
  定义体: ContinuousMap.compCLM R V φ.toContinuousMap
  isIntertwining' h := by
    ext F x
    simp [map_mul, map_inv]

@[simp]

Depends on / 依赖: ContinuousMap, ContinuousMap.compCLM, compCLM, toContinuousMap
-/
def coind₁Res (φ : H ->ₜ* G) (π : ContRepresentation R G V) :
    π.coind₁.restrict (φ : H ->* G) ->ⁱL (π.restrict (φ : H ->* G)).coind₁ where
  __ := ContinuousMap.compCLM R V φ.toContinuousMap
  isIntertwining' h := by
    ext F x
    simp [map_mul, map_inv]

@[simp]
/--
lemma `coind₁Res_apply` / 引理 `coind₁Res_apply`

English:
lemma coind₁Res_apply
  given: (φ : H ->ₜ* G) (π : ContRepresentation R G V) (F : C(G, V)) (x : H)
  proof: rfl

中文:
引理 coind₁Res_apply
  条件: (φ : H ->ₜ* G) (π : 余ntRepresentation R G V) (F : C(G, V)) (x : H)
  证明: rfl
-/
lemma coind₁Res_apply (φ : H ->ₜ* G) (π : ContRepresentation R G V) (F : C(G, V)) (x : H) :
    coind₁Res φ π F x = F (φ x) := rfl

/--
Definition of `coind₁ResMap` / `coind₁ResMap` 的定义

English:
definition coind₁ResMap
  signature: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π')
  body: (coind₁Map f).comp (coind₁Res φ π)

@[simp]

中文:
定义 coind₁ResMap
  签名: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π')
  定义体: (coind₁Map f).comp (coind₁Res φ π)

@[simp]
-/
def coind₁ResMap (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') :
    π.coind₁.restrict (φ : H ->* G) ->ⁱL π'.coind₁ :=
  (coind₁Map f).comp (coind₁Res φ π)

@[simp]
/--
lemma `coind₁ResMap_apply` / 引理 `coind₁ResMap_apply`

English:
lemma coind₁ResMap_apply
  statement: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') (F : C(G, V))
  proof: rfl

中文:
引理 coind₁ResMap_apply
  结论: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') (F : C(G, V))
  证明: rfl
-/
lemma coind₁ResMap_apply (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') (F : C(G, V))
    (x : H) : coind₁ResMap φ f F x = f (F (φ x)) := rfl

/--
lemma `coind₁ResMap_comp_coind₁ι_restrict` / 引理 `coind₁ResMap_comp_coind₁ι_restrict`

English:
lemma coind₁ResMap_comp_coind₁ι_restrict
  given: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π')
  proof: rfl

中文:
引理 coind₁ResMap_comp_coind₁ι_restrict
  条件: (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π')
  证明: rfl
-/
lemma coind₁ResMap_comp_coind₁ι_restrict (φ : H ->ₜ* G) (f : π.restrict (φ : H ->* G) ->ⁱL π') :
    (coind₁ResMap φ f).comp (π.coind₁ι.restrict (φ : H ->* G)) = π'.coind₁ι.comp f := rfl

/--
lemma `coind₁Map_comp_coind₁ResMap` / 引理 `coind₁Map_comp_coind₁ResMap`

English:
lemma coind₁Map_comp_coind₁ResMap
  statement: (φ : H ->ₜ* G) {σ : ContRepresentation R H U}
  proof: rfl

中文:
引理 coind₁Map_comp_coind₁ResMap
  结论: (φ : H ->ₜ* G) {σ : 余ntRepresentation R H U}
  证明: rfl
-/
lemma coind₁Map_comp_coind₁ResMap (φ : H ->ₜ* G) {σ : ContRepresentation R H U}
    (f : π.restrict φ ->ⁱL π') (g : π' ->ⁱL σ) :
    (coind₁Map g).comp (coind₁ResMap φ f) = coind₁ResMap φ (g.comp f) := rfl

/--
lemma `coind₁ResMap_comp_coind₁Map_restrict` / 引理 `coind₁ResMap_comp_coind₁Map_restrict`

English:
lemma coind₁ResMap_comp_coind₁Map_restrict
  statement: (φ : H ->ₜ* G) {ρ : ContRepresentation R G U}
  proof: rfl

中文:
引理 coind₁ResMap_comp_coind₁Map_restrict
  结论: (φ : H ->ₜ* G) {ρ : 余ntRepresentation R G U}
  证明: rfl
-/
lemma coind₁ResMap_comp_coind₁Map_restrict (φ : H ->ₜ* G) {ρ : ContRepresentation R G U}
    (g : ρ ->ⁱL π) (f : π.restrict (φ : H ->* G) ->ⁱL π') :
    (coind₁ResMap φ f).comp ((coind₁Map g).restrict (φ : H ->* G)) =
      coind₁ResMap φ (f.comp (g.restrict (φ : H ->* G))) := rfl

end coind₁ResMap

end ContRepresentation
