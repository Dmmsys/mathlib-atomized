/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Christian Merten
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Normal subgroup objects

In this file we define normal subgroups of group objects in a cartesian monoidal category as
a predicate on morphisms. A morphism `φ : H ⟶ G` of group objects is normal if it is mono, a
monoid morphism and the conjugation map `(g, h) ↦ g * h * g⁻¹` factors through `φ`.

This is applied in the study of group schemes.

## Main declarations

- `CategoryTheory.IsMonHom.Normal`: The predicate on morphisms to be a normal monoid morphism.
- `CategoryTheory.IsMonHom.normal_iff_normal_monoidHom`: A monoid morphism `H ⟶ G` that is mono
  is normal if and only if for every `X`, the image of `H(X)` in `G(X)` is a normal subgroup.

## References

- In the context of group schemes:
  [Görtz, Wedhorn, Algebraic Geometry II, Definition 27.3][goertz-wedhorn-2]
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

open MonObj GrpObj MonoidalCategory CartesianMonoidalCategory

/--
Definition of `IsAddMonHom.Normal` / `IsAddMonHom.Normal` 的定义

English:
class IsAddMonHom.Normal
  parameters: {G H : C} [AddGrpObj G] [AddGrpObj H] (φ : H ⟶ G)
  axioms and operations (3):
    - mono : Mono φ  [default: by infer_instance]
    - isAddMonHom : IsAddMonHom φ  [default: by infer_instance]
    - exists_comp_eq_addConj : exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ AddGrpObj.addConj G

中文:
类 是加法幺半群态射.正规
  参数: {G H : C} [加法GrpObj G] [加法GrpObj H] (φ : H ⟶ G)
  公理与运算 (3 个):
    - mono : 单态射 φ  [默认: by infer_instance]
    - isAddMonHom : 是加法幺半群态射 φ  [默认: by infer_instance]
    - exists_comp_eq_addConj : 存在 ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ 加法GrpObj.addConj G

Depends on / 依赖: AddGrpObj, AddGrpObj.addConj, IsAddMonHom, addConj, exists_comp_eq_addConj, infer_instance, isAddMonHom, otimes
-/
class IsAddMonHom.Normal {G H : C} [AddGrpObj G] [AddGrpObj H] (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isAddMonHom : IsAddMonHom φ := by infer_instance
  exists_comp_eq_addConj : exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ AddGrpObj.addConj G

attribute [instance] IsAddMonHom.Normal.mono IsAddMonHom.Normal.isAddMonHom

namespace IsMonHom

variable {G H K : C} [GrpObj G] [GrpObj H] [GrpObj K] {φ : H ⟶ G}

/-- A morphism `φ : H ⟶ G` of group objects is a normal monoid homomorphism if it is a
monoid homomorphism that is mono and such that the conjugation map `(g, h) ↦ g * h * g⁻¹`
factors through `φ`. -/
@[to_additive]
/--
Definition of `Normal` / `Normal` 的定义

English:
class Normal
  parameters: (φ : H ⟶ G)
  axioms and operations (3):
    - mono : Mono φ  [default: by infer_instance]
    - isMonHom : IsMonHom φ  [default: by infer_instance]
    - exists_comp_eq_conj((φ)) : exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G

中文:
类 正规
  参数: (φ : H ⟶ G)
  公理与运算 (3 个):
    - mono : 单态射 φ  [默认: by infer_instance]
    - isMonHom : 是幺半群态射 φ  [默认: by infer_instance]
    - exists_comp_eq_conj((φ)) : 存在 ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G

Depends on / 依赖: IsMonHom, exists_comp_eq_conj, infer_instance, isMonHom, otimes
-/
class Normal (φ : H ⟶ G) : Prop where
  mono : Mono φ := by infer_instance
  isMonHom : IsMonHom φ := by infer_instance
  exists_comp_eq_conj (φ) : exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G

attribute [instance] Normal.mono Normal.isMonHom

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Normal (𝟙 G)
  body: by cat_disch

@[to_additive]

中文:
实例 :
  签名: 正规 (𝟙 G)
  定义体: by cat_disch

@[to_additive]

Depends on / 依赖: cat_disch
-/
instance : Normal (𝟙 G) where
  exists_comp_eq_conj := by cat_disch

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Normal η[G]
  body: by
    use toUnit _
    simp [conj, comp_mul, comp_inv, toUnit_unique _ (toUnit _), ← Hom.one_def]

@[to_additive]

中文:
实例 :
  签名: 正规 η[G]
  定义体: by
    use toUnit _
    simp [conj, comp_mul, comp_inv, toUnit_unique _ (toUnit _), ← Hom.one_def]

@[to_additive]

Depends on / 依赖: Hom.one_def, comp_inv, comp_mul, one_def, toUnit, toUnit_unique
-/
instance : Normal η[G] where
  exists_comp_eq_conj := by
    use toUnit _
    simp [conj, comp_mul, comp_inv, toUnit_unique _ (toUnit _), ← Hom.one_def]

@[to_additive]
/--
lemma `isNormalHom_iff` / 引理 `isNormalHom_iff`

English:
lemma isNormalHom_iff
  given: [IsMonHom φ] [Mono φ]
  statement: Normal φ ↔ exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G
  proof: ⟨fun h => h.exists_comp_eq_conj, fun h => ⟨‹_›, ‹_›, h⟩⟩

中文:
引理 isNormalHom_iff
  条件: [是幺半群态射 φ] [单态射 φ]
  结论: 正规 φ ↔ 存在 ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G
  证明: ⟨fun h => h.exists_comp_eq_conj, fun h => ⟨‹_›, ‹_›, h⟩⟩

Depends on / 依赖: exists_comp_eq_conj, h.exists_comp_eq_conj
-/
lemma isNormalHom_iff [IsMonHom φ] [Mono φ] : Normal φ ↔ exists ψ : G otimes H ⟶ H, ψ ≫ φ = G ◁ φ ≫ conj G :=
  ⟨fun h => h.exists_comp_eq_conj, fun h => ⟨‹_›, ‹_›, h⟩⟩

/-- If `φ` is mono, it is a normal group homomorphism if and only if for all `X` the image of
`H(X)` in `G(X)` is a normal subgroup. -/
@[to_additive /-- If `φ` is mono, it is a normal additive group homomorphism if and only if for all
`X` the image of `H(X)` in `G(X)` is a normal additive subgroup. -/]
/--
theorem `normal_iff_normal_monoidHom` / 定理 `normal_iff_normal_monoidHom`

English:
theorem normal_iff_normal_monoidHom
  given: [IsMonHom φ] [Mono φ]
  proof: by
  rw [isNormalHom_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨ψ, hψ⟩ X
    constructor
    rintro - ⟨x, rfl⟩ z
    exact ⟨lift z x ≫ ψ, by simp [hψ]⟩
  · intro hnormal
    have (X : C) (g : X ⟶ G) (h : X ⟶ H) : exists (h' : X ⟶ H), h' ≫ φ = g * h ≫ φ * g⁻¹ :=
      (hnormal X).conj_mem (h ≫ φ) (by simp) g
    choose h' hh' using this
    refine ⟨Yoneda.fullyFaithful.preimage ?_, ?_⟩
    · refine ⟨fun X => ↾fun x => h' _ (x ≫ fst _ _) (x ≫ snd _ _), fun X Y f => ?_⟩
      ext
      simp [← cancel_mono φ, hh', comp_mul, comp_inv]
    · refine yoneda.map_injective ?_
      ext
      simp [hh', conj, comp_mul, comp_inv]

@[to_additive]

中文:
定理 normal_iff_normal_monoidHom
  条件: [是幺半群态射 φ] [单态射 φ]
  证明: by
  rw [isNormalHom_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨ψ, hψ⟩ X
    constructor
    rintro - ⟨x, rfl⟩ z
    exact ⟨lift z x ≫ ψ, by simp [hψ]⟩
  · intro hnormal
    have (X : C) (g : X ⟶ G) (h : X ⟶ H) : exists (h' : X ⟶ H), h' ≫ φ = g * h ≫ φ * g⁻¹ :=
      (hnormal X).conj_mem (h ≫ φ) (by simp) g
    choose h' hh' using this
    refine ⟨Yoneda.fullyFaithful.preimage ?_, ?_⟩
    · refine ⟨fun X => ↾fun x => h' _ (x ≫ fst _ _) (x ≫ snd _ _), fun X Y f => ?_⟩
      ext
      simp [← cancel_mono φ, hh', comp_mul, comp_inv]
    · refine yoneda.map_injective ?_
      ext
      simp [hh', conj, comp_mul, comp_inv]

@[to_additive]

Depends on / 依赖: Yoneda, Yoneda.fullyFaithful.preimage, cancel_mono, comp_inv, comp_mul, conj_mem, fullyFaithful, hnormal, isNormalHom_iff, map_injecti, preimage, yoneda, yoneda.map_injecti
-/
theorem normal_iff_normal_monoidHom [IsMonHom φ] [Mono φ] :
    Normal φ ↔ forall (X : C), (monoidHom φ X).range.Normal := by
  rw [isNormalHom_iff]
  refine ⟨?_, ?_⟩
  · intro ⟨ψ, hψ⟩ X
    constructor
    rintro - ⟨x, rfl⟩ z
    exact ⟨lift z x ≫ ψ, by simp [hψ]⟩
  · intro hnormal
    have (X : C) (g : X ⟶ G) (h : X ⟶ H) : exists (h' : X ⟶ H), h' ≫ φ = g * h ≫ φ * g⁻¹ :=
      (hnormal X).conj_mem (h ≫ φ) (by simp) g
    choose h' hh' using this
    refine ⟨Yoneda.fullyFaithful.preimage ?_, ?_⟩
    · refine ⟨fun X => ↾fun x => h' _ (x ≫ fst _ _) (x ≫ snd _ _), fun X Y f => ?_⟩
      ext
      simp [← cancel_mono φ, hh', comp_mul, comp_inv]
    · refine yoneda.map_injective ?_
      ext
      simp [hh', conj, comp_mul, comp_inv]

@[to_additive]
instance (priority := low) [BraidedCategory C] [IsCommMonObj G] [IsMonHom φ] [Mono φ] :
    Normal φ := by
  simp [isNormalHom_iff, conj_eq_snd_of_isCommMonObj]

@[to_additive]
/--
lemma `Normal.of_isPullback_η` / 引理 `Normal.of_isPullback_η`

English:
lemma Normal.of_isPullback_η
  statement: [IsMonHom φ] {P : C} (p : G ⟶ P) [GrpObj P] [IsMonHom p]
  proof: h.mono_fst_of_mono
  exists_comp_eq_conj := by
    refine ⟨h.lift (G ◁ φ ≫ conj G) (toUnit _) ?_, ?_⟩
    · simp [conj, comp_mul, inv_comp, mul_comp, h.w, comp_inv, ← Hom.one_def]
    · simp

中文:
引理 正规.of_isPullback_η
  结论: [是幺半群态射 φ] {P : C} (p : G ⟶ P) [GrpObj P] [是幺半群态射 p]
  证明: h.mono_fst_of_mono
  exists_comp_eq_conj := by
    refine ⟨h.lift (G ◁ φ ≫ conj G) (toUnit _) ?_, ?_⟩
    · simp [conj, comp_mul, inv_comp, mul_comp, h.w, comp_inv, ← Hom.one_def]
    · simp

Depends on / 依赖: h.mono_fst_of_mono, mono_fst_of_mono
-/
lemma Normal.of_isPullback_η [IsMonHom φ] {P : C} (p : G ⟶ P) [GrpObj P] [IsMonHom p]
    (h : IsPullback φ (toUnit _) p η) :
    Normal φ where
  mono := h.mono_fst_of_mono
  exists_comp_eq_conj := by
    refine ⟨h.lift (G ◁ φ ≫ conj G) (toUnit _) ?_, ?_⟩
    · simp [conj, comp_mul, inv_comp, mul_comp, h.w, comp_inv, ← Hom.one_def]
    · simp

end CategoryTheory.IsMonHom
