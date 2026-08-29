/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Symmetric
public import Mathlib.Data.Sigma.Basic
public import Mathlib.Data.Sum.Basic
public import Mathlib.Logic.Equiv.Sum
public import Mathlib.Tactic.Common

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `Quiver.Star u` is the type of all arrows with source `u`;
* `Quiver.Costar u` is the type of all arrows with target `u`;
* `Prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `Prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `Prefunctor.IsCovering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `Quiver.PathStar u` is the type of all paths with source `u`;
* `Prefunctor.pathStar u` is the obvious function `PathStar u → PathStar (φ.obj u)`.

## Main statements

* `Prefunctor.IsCovering.pathStar_bijective` states that if `φ` is a covering,
  then `φ.pathStar u` is a bijection for all `u`.
  In other words, every path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `Prefunctor` to `Quiver.Prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/

@[expose] public section


open Function Quiver

universe u v w

variable {U : Type _} [Quiver.{u} U] {V : Type _} [Quiver.{v} V] (φ : U ⥤q V) {W : Type _}
  [Quiver.{w} W] (ψ : V ⥤q W)

/--
Definition of `Quiver.Star` / `Quiver.Star` 的定义

English:
abbreviation Quiver.Star
  signature: (u : U)
  body: Σ v : U, u ⟶ v

中文:
缩写 箭图.对合
  签名: (u : U)
  定义体: Σ v : U, u ⟶ v
-/
abbrev Quiver.Star (u : U) :=
  Σ v : U, u ⟶ v

/--
Definition of `Quiver.Star.mk` / `Quiver.Star.mk` 的定义

English:
abbreviation Quiver.Star.mk
  signature: {u v : U} (f : u ⟶ v)
  body: ⟨_, f⟩

中文:
缩写 箭图.对合.mk
  签名: {u v : U} (f : u ⟶ v)
  定义体: ⟨_, f⟩
-/
protected abbrev Quiver.Star.mk {u v : U} (f : u ⟶ v) : Quiver.Star u :=
  ⟨_, f⟩

/--
Definition of `Quiver.Costar` / `Quiver.Costar` 的定义

English:
abbreviation Quiver.Costar
  signature: (v : U)
  body: Σ u : U, u ⟶ v

中文:
缩写 箭图.Costar
  签名: (v : U)
  定义体: Σ u : U, u ⟶ v
-/
abbrev Quiver.Costar (v : U) :=
  Σ u : U, u ⟶ v

/--
Definition of `Quiver.Costar.mk` / `Quiver.Costar.mk` 的定义

English:
abbreviation Quiver.Costar.mk
  signature: {u v : U} (f : u ⟶ v)
  body: ⟨_, f⟩

中文:
缩写 箭图.Costar.mk
  签名: {u v : U} (f : u ⟶ v)
  定义体: ⟨_, f⟩
-/
protected abbrev Quiver.Costar.mk {u v : U} (f : u ⟶ v) : Quiver.Costar v :=
  ⟨_, f⟩

/-- A prefunctor induces a map of `Quiver.Star` at every vertex. -/
@[simps]
/--
Definition of `Prefunctor.star` / `Prefunctor.star` 的定义

English:
definition Prefunctor.star
  signature: (u : U)
  body: fun F =>
  Quiver.Star.mk (φ.map F.2)

中文:
定义 预函子.star
  签名: (u : U)
  定义体: fun F =>
  Quiver.Star.mk (φ.map F.2)
-/
def Prefunctor.star (u : U) : Quiver.Star u -> Quiver.Star (φ.obj u) := fun F =>
  Quiver.Star.mk (φ.map F.2)

/-- A prefunctor induces a map of `Quiver.Costar` at every vertex. -/
@[simps]
/--
Definition of `Prefunctor.costar` / `Prefunctor.costar` 的定义

English:
definition Prefunctor.costar
  signature: (u : U)
  body: fun F =>
  Quiver.Costar.mk (φ.map F.2)

@[simp]

中文:
定义 预函子.costar
  签名: (u : U)
  定义体: fun F =>
  Quiver.Costar.mk (φ.map F.2)

@[simp]
-/
def Prefunctor.costar (u : U) : Quiver.Costar u -> Quiver.Costar (φ.obj u) := fun F =>
  Quiver.Costar.mk (φ.map F.2)

@[simp]
/--
theorem `Prefunctor.star_apply` / 定理 `Prefunctor.star_apply`

English:
theorem Prefunctor.star_apply
  given: {u v : U} (e : u ⟶ v)
  proof: rfl

@[simp]

中文:
定理 预函子.star_apply
  条件: {u v : U} (e : u ⟶ v)
  证明: rfl

@[simp]
-/
theorem Prefunctor.star_apply {u v : U} (e : u ⟶ v) :
    φ.star u (Quiver.Star.mk e) = Quiver.Star.mk (φ.map e) :=
  rfl

@[simp]
/--
theorem `Prefunctor.costar_apply` / 定理 `Prefunctor.costar_apply`

English:
theorem Prefunctor.costar_apply
  given: {u v : U} (e : u ⟶ v)
  proof: rfl

中文:
定理 预函子.costar_apply
  条件: {u v : U} (e : u ⟶ v)
  证明: rfl
-/
theorem Prefunctor.costar_apply {u v : U} (e : u ⟶ v) :
    φ.costar v (Quiver.Costar.mk e) = Quiver.Costar.mk (φ.map e) :=
  rfl

/--
theorem `Prefunctor.star_comp` / 定理 `Prefunctor.star_comp`

English:
theorem Prefunctor.star_comp
  given: (u : U)
  statement: (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star u
  proof: rfl

中文:
定理 预函子.star_comp
  条件: (u : U)
  结论: (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star u
  证明: rfl
-/
theorem Prefunctor.star_comp (u : U) : (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star u :=
  rfl

/--
theorem `Prefunctor.costar_comp` / 定理 `Prefunctor.costar_comp`

English:
theorem Prefunctor.costar_comp
  given: (u : U)
  statement: (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ φ.costar u
  proof: rfl

中文:
定理 预函子.costar_comp
  条件: (u : U)
  结论: (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ φ.costar u
  证明: rfl
-/
theorem Prefunctor.costar_comp (u : U) : (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ φ.costar u :=
  rfl

/--
Definition of `Prefunctor.IsCovering` / `Prefunctor.IsCovering` 的定义

English:
structure Prefunctor.IsCovering
  parameters: : Prop where
  axioms and operations (2):
    - star_bijective : forall u, Bijective (φ.star u)
    - costar_bijective : forall u, Bijective (φ.costar u)

中文:
结构 预函子.是余vering
  参数: : 命题 where
  公理与运算 (2 个):
    - star_bijective : 对任意 u, 双射 (φ.star u)
    - costar_bijective : 对任意 u, 双射 (φ.costar u)
-/
protected structure Prefunctor.IsCovering : Prop where
  star_bijective : forall u, Bijective (φ.star u)
  costar_bijective : forall u, Bijective (φ.costar u)

@[simp]
/--
theorem `Prefunctor.IsCovering.map_injective` / 定理 `Prefunctor.IsCovering.map_injective`

English:
theorem Prefunctor.IsCovering.map_injective
  given: (hφ : φ.IsCovering) {u v : U}
  proof: by
  rintro f g he
  have : φ.star u (Quiver.Star.mk f) = φ.star u (Quiver.Star.mk g) := by simpa using he
  simpa using (hφ.star_bijective u).left this

中文:
定理 预函子.是余vering.map_injective
  条件: (hφ : φ.是余vering) {u v : U}
  证明: by
  rintro f g he
  have : φ.star u (Quiver.Star.mk f) = φ.star u (Quiver.Star.mk g) := by simpa using he
  simpa using (hφ.star_bijective u).left this

Depends on / 依赖: Quiver, Quiver.Star.mk, star_bijective
-/
theorem Prefunctor.IsCovering.map_injective (hφ : φ.IsCovering) {u v : U} :
    Injective fun f : u ⟶ v => φ.map f := by
  rintro f g he
  have : φ.star u (Quiver.Star.mk f) = φ.star u (Quiver.Star.mk g) := by simpa using he
  simpa using (hφ.star_bijective u).left this

/--
theorem `Prefunctor.IsCovering.comp` / 定理 `Prefunctor.IsCovering.comp`

English:
theorem Prefunctor.IsCovering.comp
  given: (hφ : φ.IsCovering) (hψ : ψ.IsCovering)
  statement: (φ ⋙q ψ).IsCovering
  proof: ⟨fun _ => (hψ.star_bijective _).comp (hφ.star_bijective _),
   fun _ => (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩

中文:
定理 预函子.是余vering.comp
  条件: (hφ : φ.是余vering) (hψ : ψ.是余vering)
  结论: (φ ⋙q ψ).是余vering
  证明: ⟨fun _ => (hψ.star_bijective _).comp (hφ.star_bijective _),
   fun _ => (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩

Depends on / 依赖: costar_bijective, star_bijective
-/
theorem Prefunctor.IsCovering.comp (hφ : φ.IsCovering) (hψ : ψ.IsCovering) : (φ ⋙q ψ).IsCovering :=
  ⟨fun _ => (hψ.star_bijective _).comp (hφ.star_bijective _),
   fun _ => (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩

/--
theorem `Prefunctor.IsCovering.of_comp_right` / 定理 `Prefunctor.IsCovering.of_comp_right`

English:
theorem Prefunctor.IsCovering.of_comp_right
  given: (hψ : ψ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering)
  proof: ⟨fun _ => (Bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
   fun _ => (Bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩

中文:
定理 预函子.是余vering.of_comp_right
  条件: (hψ : ψ.是余vering) (hφψ : (φ ⋙q ψ).是余vering)
  证明: ⟨fun _ => (Bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
   fun _ => (Bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩

Depends on / 依赖: Bijective, Bijective.of_comp_iff, costar_bijective, of_comp_iff, star_bijective
-/
theorem Prefunctor.IsCovering.of_comp_right (hψ : ψ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering) :
    φ.IsCovering :=
  ⟨fun _ => (Bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
   fun _ => (Bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩

/--
theorem `Prefunctor.IsCovering.of_comp_left` / 定理 `Prefunctor.IsCovering.of_comp_left`

English:
theorem Prefunctor.IsCovering.of_comp_left
  statement: (hφ : φ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering)
  proof: by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;> obtain ⟨u, rfl⟩ := φsur v
  exacts [(Bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
    (Bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)]

中文:
定理 预函子.是余vering.of_comp_left
  结论: (hφ : φ.是余vering) (hφψ : (φ ⋙q ψ).是余vering)
  证明: by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;> obtain ⟨u, rfl⟩ := φsur v
  exacts [(Bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
    (Bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)]

Depends on / 依赖: Bijective, Bijective.of_comp_iff, costar_bijective, exacts, of_comp_iff, star_bijective
-/
theorem Prefunctor.IsCovering.of_comp_left (hφ : φ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering)
    (φsur : Surjective φ.obj) : ψ.IsCovering := by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;> obtain ⟨u, rfl⟩ := φsur v
  exacts [(Bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
    (Bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)]

/--
Definition of `Quiver.symmetrifyStar` / `Quiver.symmetrifyStar` 的定义

English:
definition Quiver.symmetrifyStar
  signature: (u : U)
  body: Equiv.sigmaSumDistrib _ _

中文:
定义 箭图.symmetrifyStar
  签名: (u : U)
  定义体: Equiv.sigmaSumDistrib _ _

Depends on / 依赖: Equiv.sigmaSumDistrib, sigmaSumDistrib
-/
def Quiver.symmetrifyStar (u : U) :
    Quiver.Star (Symmetrify.of.obj u) ≃ Quiver.Star u oplus Quiver.Costar u :=
  Equiv.sigmaSumDistrib _ _

/--
Definition of `Quiver.symmetrifyCostar` / `Quiver.symmetrifyCostar` 的定义

English:
definition Quiver.symmetrifyCostar
  signature: (u : U)
  body: Equiv.sigmaSumDistrib _ _

中文:
定义 箭图.symmetrifyCostar
  签名: (u : U)
  定义体: Equiv.sigmaSumDistrib _ _

Depends on / 依赖: Equiv.sigmaSumDistrib, sigmaSumDistrib
-/
def Quiver.symmetrifyCostar (u : U) :
    Quiver.Costar (Symmetrify.of.obj u) ≃ Quiver.Costar u oplus Quiver.Star u :=
  Equiv.sigmaSumDistrib _ _

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Prefunctor.symmetrifyStar` / 定理 `Prefunctor.symmetrifyStar`

English:
theorem Prefunctor.symmetrifyStar
  given: (u : U)
  proof: by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyStar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyStar]`
    simp only [Quiver.symmetrifyStar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistr

中文:
定理 预函子.symmetrifyStar
  条件: (u : U)
  证明: by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyStar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyStar]`
    simp only [Quiver.symmetrifyStar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistr

Depends on / 依赖: Equiv.eq_symm_comp, Quiver, Quiver.symmetrifyStar, eq_symm_comp, symmetrifyStar
-/
theorem Prefunctor.symmetrifyStar (u : U) :
    φ.symmetrify.star u =
      (Quiver.symmetrifyStar _).symm ∘ Sum.map (φ.star u) (φ.costar u) ∘
        Quiver.symmetrifyStar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyStar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyStar]`
    simp only [Quiver.symmetrifyStar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Prefunctor.symmetrifyCostar` / 定理 `Prefunctor.symmetrifyCostar`

English:
theorem Prefunctor.symmetrifyCostar
  given: (u : U)
  proof: by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyCostar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyCostar]`
    simp only [Quiver.symmetrifyCostar, Function.comp_apply] <;>
    erw [Equiv.sigmaSu

中文:
定理 预函子.symmetrifyCostar
  条件: (u : U)
  证明: by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyCostar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyCostar]`
    simp only [Quiver.symmetrifyCostar, Function.comp_apply] <;>
    erw [Equiv.sigmaSu
-/
protected theorem Prefunctor.symmetrifyCostar (u : U) :
    φ.symmetrify.costar u =
      (Quiver.symmetrifyCostar _).symm ∘
        Sum.map (φ.costar u) (φ.star u) ∘ Quiver.symmetrifyCostar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyCostar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyCostar]`
    simp only [Quiver.symmetrifyCostar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `Prefunctor.IsCovering.symmetrify` / 定理 `Prefunctor.IsCovering.symmetrify`

English:
theorem Prefunctor.IsCovering.symmetrify
  given: (hφ : φ.IsCovering)
  proof: by
  refine ⟨fun u => ?_, fun u => ?_⟩ <;>
  simp [φ.symmetrifyStar, φ.symmetrifyCostar, hφ.star_bijective u, hφ.costar_bijective u]

中文:
定理 预函子.是余vering.symmetrify
  条件: (hφ : φ.是余vering)
  证明: by
  refine ⟨fun u => ?_, fun u => ?_⟩ <;>
  simp [φ.symmetrifyStar, φ.symmetrifyCostar, hφ.star_bijective u, hφ.costar_bijective u]
-/
protected theorem Prefunctor.IsCovering.symmetrify (hφ : φ.IsCovering) :
    φ.symmetrify.IsCovering := by
  refine ⟨fun u => ?_, fun u => ?_⟩ <;>
  simp [φ.symmetrifyStar, φ.symmetrifyCostar, hφ.star_bijective u, hφ.costar_bijective u]

/--
Definition of `Quiver.PathStar` / `Quiver.PathStar` 的定义

English:
abbreviation Quiver.PathStar
  signature: (u : U)
  body: Σ v : U, Path u v

中文:
缩写 箭图.PathStar
  签名: (u : U)
  定义体: Σ v : U, Path u v
-/
abbrev Quiver.PathStar (u : U) :=
  Σ v : U, Path u v

/--
Definition of `Quiver.PathStar.mk` / `Quiver.PathStar.mk` 的定义

English:
abbreviation Quiver.PathStar.mk
  signature: {u v : U} (p : Path u v)
  body: ⟨_, p⟩

中文:
缩写 箭图.PathStar.mk
  签名: {u v : U} (p : 道路 u v)
  定义体: ⟨_, p⟩
-/
protected abbrev Quiver.PathStar.mk {u v : U} (p : Path u v) : Quiver.PathStar u :=
  ⟨_, p⟩

/--
Definition of `Prefunctor.pathStar` / `Prefunctor.pathStar` 的定义

English:
definition Prefunctor.pathStar
  signature: (u : U)
  body: fun p =>
  Quiver.PathStar.mk (φ.mapPath p.2)

@[simp]

中文:
定义 预函子.pathStar
  签名: (u : U)
  定义体: fun p =>
  Quiver.PathStar.mk (φ.mapPath p.2)

@[simp]
-/
def Prefunctor.pathStar (u : U) : Quiver.PathStar u -> Quiver.PathStar (φ.obj u) := fun p =>
  Quiver.PathStar.mk (φ.mapPath p.2)

@[simp]
/--
theorem `Prefunctor.pathStar_apply` / 定理 `Prefunctor.pathStar_apply`

English:
theorem Prefunctor.pathStar_apply
  given: {u v : U} (p : Path u v)
  proof: rfl

中文:
定理 预函子.pathStar_apply
  条件: {u v : U} (p : 道路 u v)
  证明: rfl
-/
theorem Prefunctor.pathStar_apply {u v : U} (p : Path u v) :
    φ.pathStar u (Quiver.PathStar.mk p) = Quiver.PathStar.mk (φ.mapPath p) :=
  rfl

/--
theorem `Prefunctor.pathStar_injective` / 定理 `Prefunctor.pathStar_injective`

English:
theorem Prefunctor.pathStar_injective
  given: (hφ : forall u, Injective (φ.star u)) (u : U)
  proof: by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v₁, p₁⟩
  induction p₁ with
  | nil =>
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro; rfl -- Porting note: goal not present in lean3.
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h

中文:
定理 预函子.pathStar_injective
  条件: (hφ : 对任意 u, 单射 (φ.star u)) (u : U)
  证明: by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v₁, p₁⟩
  induction p₁ with
  | nil =>
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro; rfl -- Porting note: goal not present in lean3.
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h

Depends on / 依赖: Path.cast_cons, Path.eq_cast_iff_heq, Path.nil_ne_cons, PathStar, Porting, Prefunctor, Prefunctor.pathStar, Quiver, Quiver.PathStar.mk, Sigma.mk.inj_iff, cast_cons, eq_cast_iff_heq, h.symm, inj_iff, mapPath_cons, nil_ne_cons, pathStar, present, rename_i, unfoldPartialApp
-/
theorem Prefunctor.pathStar_injective (hφ : forall u, Injective (φ.star u)) (u : U) :
    Injective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v₁, p₁⟩
  induction p₁ with
  | nil =>
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro; rfl -- Porting note: goal not present in lean3.
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.eq_cast_iff_heq rfl h.symm]; rw [Path.cast_cons] at h'
      exact (Path.nil_ne_cons _ _) h'
  | cons p₁ e₁ ih =>
    rename_i x₁ y₁
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl h]; rw [Path.cast_cons] at h'
      exact (Path.cons_ne_nil _ _) h'
    · rename_i x₂
      intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      obtain ⟨hφy, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl hφy]; rw [Path.cast_cons]; rw [Path.cast_rfl_rfl] at h'
      have hφx := Path.obj_eq_of_cons_eq_cons h'
      have hφp := Path.heq_of_cons_eq_cons h'
      have hφe := HEq.trans (Hom.cast_heq rfl hφy _).symm (Path.hom_heq_of_cons_eq_cons h')
      have h_path_star : φ.pathStar u ⟨x₁, p₁⟩ = φ.pathStar u ⟨x₂, p₂⟩ := by
        simp only [Prefunctor.pathStar_apply, Sigma.mk.inj_iff]; exact ⟨hφx, hφp⟩
      cases ih h_path_star
      have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩ := by
        simp only [Prefunctor.star_apply, Sigma.mk.inj_iff]; exact ⟨hφy, hφe⟩
      cases hφ x₁ h_star
      rfl

/--
theorem `Prefunctor.pathStar_surjective` / 定理 `Prefunctor.pathStar_surjective`

English:
theorem Prefunctor.pathStar_surjective
  given: (hφ : forall u, Surjective (φ.star u)) (u : U)
  proof: by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v, p⟩
  induction p with
  | nil =>
    use ⟨u, Path.nil⟩
    simp only [Prefunctor.mapPath_nil]
  | cons p' ev ih =>
    obtain ⟨⟨u', q'⟩, h⟩ := ih
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨u'', eu⟩, k

中文:
定理 预函子.pathStar_surjective
  条件: (hφ : 对任意 u, 满射 (φ.star u)) (u : U)
  证明: by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v, p⟩
  induction p with
  | nil =>
    use ⟨u, Path.nil⟩
    simp only [Prefunctor.mapPath_nil]
  | cons p' ev ih =>
    obtain ⟨⟨u', q'⟩, h⟩ := ih
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨u'', eu⟩, k

Depends on / 依赖: Path.nil, PathStar, Prefunctor, Prefunctor.mapPath_nil, Prefunctor.pathStar, Quiver, Quiver.PathStar.mk, Sigma.mk.inj_iff, inj_iff, mapPath_nil, pathStar, star_apply, unfoldPartialApp
-/
theorem Prefunctor.pathStar_surjective (hφ : forall u, Surjective (φ.star u)) (u : U) :
    Surjective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v, p⟩
  induction p with
  | nil =>
    use ⟨u, Path.nil⟩
    simp only [Prefunctor.mapPath_nil]
  | cons p' ev ih =>
    obtain ⟨⟨u', q'⟩, h⟩ := ih
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨u'', eu⟩, k⟩ := hφ u' ⟨_, ev⟩
    simp only [star_apply, Sigma.mk.inj_iff] at k
    -- Porting note: was `obtain ⟨rfl, rfl⟩ := k`
    obtain ⟨rfl, k⟩ := k
    simp only [heq_eq_eq] at k
    subst k
    use ⟨_, q'.cons eu⟩
    simp only [Prefunctor.mapPath_cons]

/--
theorem `Prefunctor.pathStar_bijective` / 定理 `Prefunctor.pathStar_bijective`

English:
theorem Prefunctor.pathStar_bijective
  given: (hφ : forall u, Bijective (φ.star u)) (u : U)
  proof: ⟨φ.pathStar_injective (fun u => (hφ u).1) _, φ.pathStar_surjective (fun u => (hφ u).2) _⟩

中文:
定理 预函子.pathStar_bijective
  条件: (hφ : 对任意 u, 双射 (φ.star u)) (u : U)
  证明: ⟨φ.pathStar_injective (fun u => (hφ u).1) _, φ.pathStar_surjective (fun u => (hφ u).2) _⟩

Depends on / 依赖: pathStar_injective, pathStar_surjective
-/
theorem Prefunctor.pathStar_bijective (hφ : forall u, Bijective (φ.star u)) (u : U) :
    Bijective (φ.pathStar u) :=
  ⟨φ.pathStar_injective (fun u => (hφ u).1) _, φ.pathStar_surjective (fun u => (hφ u).2) _⟩

namespace Prefunctor.IsCovering

variable {φ}

/--
theorem `pathStar_bijective` / 定理 `pathStar_bijective`

English:
theorem pathStar_bijective
  given: (hφ : φ.IsCovering) (u : U)
  statement: Bijective (φ.pathStar u)
  proof: φ.pathStar_bijective hφ.1 u

中文:
定理 pathStar_bijective
  条件: (hφ : φ.是余vering) (u : U)
  结论: 双射 (φ.pathStar u)
  证明: φ.pathStar_bijective hφ.1 u
-/
protected theorem pathStar_bijective (hφ : φ.IsCovering) (u : U) : Bijective (φ.pathStar u) :=
  φ.pathStar_bijective hφ.1 u

end Prefunctor.IsCovering

section HasInvolutiveReverse

variable [HasInvolutiveReverse U] [HasInvolutiveReverse V]

/-- In a quiver with involutive inverses, the star and costar at every vertex are equivalent.
This map is induced by `Quiver.reverse`. -/
@[simps]
/--
Definition of `Quiver.starEquivCostar` / `Quiver.starEquivCostar` 的定义

English:
definition Quiver.starEquivCostar
  signature: (u : U)
  body: ⟨e.1, reverse e.2⟩
  invFun e := ⟨e.1, reverse e.2⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp]

中文:
定义 箭图.starEquivCostar
  签名: (u : U)
  定义体: ⟨e.1, reverse e.2⟩
  invFun e := ⟨e.1, reverse e.2⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp]

Depends on / 依赖: reverse
-/
def Quiver.starEquivCostar (u : U) : Quiver.Star u ≃ Quiver.Costar u where
  toFun e := ⟨e.1, reverse e.2⟩
  invFun e := ⟨e.1, reverse e.2⟩
  left_inv e := by simp
  right_inv e := by simp

@[simp]
/--
theorem `Quiver.starEquivCostar_apply` / 定理 `Quiver.starEquivCostar_apply`

English:
theorem Quiver.starEquivCostar_apply
  given: {u v : U} (e : u ⟶ v)
  proof: rfl

@[simp]

中文:
定理 箭图.starEquivCostar_apply
  条件: {u v : U} (e : u ⟶ v)
  证明: rfl

@[simp]
-/
theorem Quiver.starEquivCostar_apply {u v : U} (e : u ⟶ v) :
    Quiver.starEquivCostar u (Quiver.Star.mk e) = Quiver.Costar.mk (reverse e) :=
  rfl

@[simp]
/--
theorem `Quiver.starEquivCostar_symm_apply` / 定理 `Quiver.starEquivCostar_symm_apply`

English:
theorem Quiver.starEquivCostar_symm_apply
  given: {u v : U} (e : u ⟶ v)
  proof: rfl

中文:
定理 箭图.starEquivCostar_symm_apply
  条件: {u v : U} (e : u ⟶ v)
  证明: rfl
-/
theorem Quiver.starEquivCostar_symm_apply {u v : U} (e : u ⟶ v) :
    (Quiver.starEquivCostar v).symm (Quiver.Costar.mk e) = Quiver.Star.mk (reverse e) :=
  rfl

variable [Prefunctor.MapReverse φ]

/--
theorem `Prefunctor.costar_conj_star` / 定理 `Prefunctor.costar_conj_star`

English:
theorem Prefunctor.costar_conj_star
  given: (u : U)
  proof: by
  ext ⟨v, f⟩ <;> simp

中文:
定理 预函子.costar_conj_star
  条件: (u : U)
  证明: by
  ext ⟨v, f⟩ <;> simp
-/
theorem Prefunctor.costar_conj_star (u : U) :
    φ.costar u = Quiver.starEquivCostar (φ.obj u) ∘ φ.star u ∘ (Quiver.starEquivCostar u).symm := by
  ext ⟨v, f⟩ <;> simp

/--
theorem `Prefunctor.bijective_costar_iff_bijective_star` / 定理 `Prefunctor.bijective_costar_iff_bijective_star`

English:
theorem Prefunctor.bijective_costar_iff_bijective_star
  given: (u : U)
  proof: by
  rw [Prefunctor.costar_conj_star φ]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]

中文:
定理 预函子.bijective_costar_iff_bijective_star
  条件: (u : U)
  证明: by
  rw [Prefunctor.costar_conj_star φ]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]

Depends on / 依赖: EquivLike, EquivLike.bijective_comp, EquivLike.comp_bijective, Prefunctor, Prefunctor.costar_conj_star, bijective_comp, comp_bijective, costar_conj_star
-/
theorem Prefunctor.bijective_costar_iff_bijective_star (u : U) :
    Bijective (φ.costar u) ↔ Bijective (φ.star u) := by
  rw [Prefunctor.costar_conj_star φ]; rw [EquivLike.comp_bijective]; rw [EquivLike.bijective_comp]

/--
theorem `Prefunctor.isCovering_of_bijective_star` / 定理 `Prefunctor.isCovering_of_bijective_star`

English:
theorem Prefunctor.isCovering_of_bijective_star
  given: (h : forall u, Bijective (φ.star u))
  statement: φ.IsCovering
  proof: ⟨h, fun u => (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

中文:
定理 预函子.isCovering_of_bijective_star
  条件: (h : 对任意 u, 双射 (φ.star u))
  结论: φ.是余vering
  证明: ⟨h, fun u => (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

Depends on / 依赖: bijective_costar_iff_bijective_star
-/
theorem Prefunctor.isCovering_of_bijective_star (h : forall u, Bijective (φ.star u)) : φ.IsCovering :=
  ⟨h, fun u => (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

/--
theorem `Prefunctor.isCovering_of_bijective_costar` / 定理 `Prefunctor.isCovering_of_bijective_costar`

English:
theorem Prefunctor.isCovering_of_bijective_costar
  given: (h : forall u, Bijective (φ.costar u))
  proof: ⟨fun u => (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

中文:
定理 预函子.isCovering_of_bijective_costar
  条件: (h : 对任意 u, 双射 (φ.costar u))
  证明: ⟨fun u => (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

Depends on / 依赖: bijective_costar_iff_bijective_star
-/
theorem Prefunctor.isCovering_of_bijective_costar (h : forall u, Bijective (φ.costar u)) :
    φ.IsCovering :=
  ⟨fun u => (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end HasInvolutiveReverse
