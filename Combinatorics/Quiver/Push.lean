/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli
-/
module

public import Mathlib.Combinatorics.Quiver.Prefunctor

/-!

# Pushing a quiver structure along a map

Given a map `σ : V → W` and a `Quiver` instance on `V`, this file defines a `Quiver` instance
on `W` by associating to each arrow `v ⟶ v'` in `V` an arrow `σ v ⟶ σ v'` in `W`.

-/

@[expose] public section

namespace Quiver

universe v v₁ v₂ u u₁ u₂

variable {V : Type*} [Quiver V] {W : Type*} (σ : V -> W)

/-- The `Quiver` instance obtained by pushing arrows of `V` along the map `σ : V → W` -/
@[nolint unusedArguments]
/--
Definition of `Push` / `Push` 的定义

English:
definition Push
  signature: (_ : V -> W)
  body: W

中文:
定义 Push
  签名: (_ : V -> W)
  定义体: W
-/
def Push (_ : V -> W) :=
  W

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : Nonempty W] : Nonempty (Push σ)
  body: h

中文:
实例 [h
  签名: : 非空 W] : 非空 (Push σ)
  定义体: h
-/
instance [h : Nonempty W] : Nonempty (Push σ) :=
  h

/--
Inductive type `PushQuiver` / 归纳类型 `PushQuiver`

English:
inductive PushQuiver
  parameters: {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V -> W)
  constructors (1):
    - arrow: {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)

中文:
归纳类型 PushQuiver
  参数: {V : 类型u} [箭图.{v} V] {W : 类型u₂} (σ : V -> W)
  构造子 (1 个):
    - arrow: {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)
-/
inductive PushQuiver {V : Type u} [Quiver.{v} V] {W : Type u₂} (σ : V -> W) : W -> W -> Type max u u₂ v
  | arrow {X Y : V} (f : X ⟶ Y) : PushQuiver σ (σ X) (σ Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Quiver (Push σ)
  body: ⟨PushQuiver σ⟩

中文:
实例 :
  签名: 箭图 (Push σ)
  定义体: ⟨PushQuiver σ⟩

Depends on / 依赖: PushQuiver
-/
instance : Quiver (Push σ) :=
  ⟨PushQuiver σ⟩

namespace Push

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : V ⥤q Push σ where
  body: σ
  map f := PushQuiver.arrow f

@[simp]

中文:
定义 of
  签名: : V ⥤q Push σ where
  定义体: σ
  map f := PushQuiver.arrow f

@[simp]
-/
def of : V ⥤q Push σ where
  obj := σ
  map f := PushQuiver.arrow f

@[simp]
/--
theorem `of_obj` / 定理 `of_obj`

English:
theorem of_obj
  statement: (of σ).obj = σ
  proof: rfl

中文:
定理 of_obj
  结论: (of σ).obj = σ
  证明: rfl
-/
theorem of_obj : (of σ).obj = σ :=
  rfl

variable {W' : Type*} [Quiver W'] (φ : V ⥤q W') (τ : W -> W') (h : forall x, φ.obj x = τ (σ x))

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : Push σ ⥤q W' where
  body: τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      rw [← h X]; rw [← h Y]
      exact φ.map f

中文:
定义 lift
  签名: : Push σ ⥤q W' where
  定义体: τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      rw [← h X]; rw [← h Y]
      exact φ.map f
-/
noncomputable def lift : Push σ ⥤q W' where
  obj := τ
  map :=
    @PushQuiver.rec V _ W σ (fun X Y _ => τ X ⟶ τ Y) @fun X Y f => by
      rw [← h X]; rw [← h Y]
      exact φ.map f

/--
theorem `lift_obj` / 定理 `lift_obj`

English:
theorem lift_obj
  statement: (lift σ φ τ h).obj = τ
  proof: rfl

中文:
定理 lift_obj
  结论: (lift σ φ τ h).obj = τ
  证明: rfl
-/
theorem lift_obj : (lift σ φ τ h).obj = τ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `lift_comp` / 定理 `lift_comp`

English:
theorem lift_comp
  statement: (of σ ⋙q lift σ φ τ h) = φ
  proof: by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    simp

中文:
定理 lift_comp
  结论: (of σ ⋙q lift σ φ τ h) = φ
  证明: by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    simp

Depends on / 依赖: Eq.symm, Prefunctor, Prefunctor.comp_map, Prefunctor.comp_obj, Prefunctor.ext, cast_heq, comp_map, comp_obj, eq_of_heq, fapply, iterate
-/
theorem lift_comp : (of σ ⋙q lift σ φ τ h) = φ := by
  fapply Prefunctor.ext
  · rintro X
    simp only [Prefunctor.comp_obj]
    apply Eq.symm
    exact h X
  · rintro X Y f
    simp only [Prefunctor.comp_map]
    apply eq_of_heq
    iterate 2 apply (cast_heq _ _).trans
    simp

/--
theorem `lift_unique` / 定理 `lift_unique`

English:
theorem lift_unique
  given: (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ)
  proof: by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map]
    rfl

中文:
定理 lift_unique
  条件: (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ)
  证明: by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map]
    rfl

Depends on / 依赖: Prefunctor, Prefunctor.comp_map, Prefunctor.ext, comp_map, fapply
-/
theorem lift_unique (Φ : Push σ ⥤q W') (Φ₀ : Φ.obj = τ) (Φcomp : (of σ ⋙q Φ) = φ) :
    Φ = lift σ φ τ h := by
  dsimp only [of, lift]
  fapply Prefunctor.ext
  · intro X
    simp only
    rw [Φ₀]
  · rintro _ _ ⟨⟩
    subst_vars
    simp only [Prefunctor.comp_map]
    rfl

end Push

end Quiver
