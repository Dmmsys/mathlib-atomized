/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Tactic.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Types.Coproducts

/-!
# Gluing data

We define `GlueData` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also state lemmas about its
interaction with a functor that preserves certain pullbacks.

-/

@[expose] public section


noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory

universe v u₁ u₂

variable (C : Type u₁) [Category.{v} C] {C' : Type u₂} [Category.{v} C']

/--
Definition of `GlueData` / `GlueData` 的定义

English:
structure GlueData
  parameters: where
  axioms and operations (12):
    - J : Type v
    - U : J -> C
    - V : J × J -> C
    - f : forall i j, V (i, j) ⟶ U i
    - f_mono : forall i j, Mono (f i j)  [default: by infer_instance]
    - f_hasPullback : forall i j k, HasPullback (f i j) (f i k)  [default: by infer_instance]
    - f_id : forall i, IsIso (f i i)  [default: by infer_instance]
    - t : forall i j, V (i, j) ⟶ V (j, i)
    - t_id : forall i, t i i = 𝟙 _
    - t' : forall i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
    - t_fac : forall i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
    - cocycle : forall i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

中文:
结构 GlueData
  参数: where
  公理与运算 (12 个):
    - J : 类型v
    - U : J -> C
    - V : J × J -> C
    - f : 对任意 i j, V (i, j) ⟶ U i
    - f_mono : 对任意 i j, Mono (f i j)  [默认: by infer_instance]
    - f_hasPullback : 对任意 i j k, HasPullback (f i j) (f i k)  [默认: by infer_instance]
    - f_id : 对任意 i, IsIso (f i i)  [默认: by infer_instance]
    - t : 对任意 i j, V (i, j) ⟶ V (j, i)
    - t_id : 对任意 i, t i i = 𝟙 _
    - t' : 对任意 i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
    - t_fac : 对任意 i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
    - cocycle : 对任意 i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

Depends on / 依赖: HasPullback, f_hasPullback, f_id, infer_instance
-/
structure GlueData where
  /-- The index type `J` of a gluing datum -/
  J : Type v
  /-- For each `i : J`, an object `U i` -/
  U : J -> C
  /-- For each `i j : J`, an object `V i j` -/
  V : J × J -> C
  /-- For each `i j : J`, a monomorphism `f i j : V i j ⟶ U i` -/
  f : forall i j, V (i, j) ⟶ U i
  f_mono : forall i j, Mono (f i j) := by infer_instance
  f_hasPullback : forall i j k, HasPullback (f i j) (f i k) := by infer_instance
  f_id : forall i, IsIso (f i i) := by infer_instance
  /-- For each `i j : J`, a transition map `t i j : V i j ⟶ V j i` -/
  t : forall i j, V (i, j) ⟶ V (j, i)
  t_id : forall i, t i i = 𝟙 _
  /-- The morphism via which `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through
  `V j k ×[U j] V j i ⟶ V j i` -/
  t' : forall i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
  t_fac : forall i j k, t' i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j
  cocycle : forall i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _

attribute [simp] GlueData.t_id

attribute [instance] GlueData.f_id GlueData.f_mono GlueData.f_hasPullback

attribute [reassoc] GlueData.t_fac GlueData.cocycle

namespace GlueData

variable {C}
variable (D : GlueData C)

@[simp]
/--
theorem `t'_iij` / 定理 `t'_iij`

English:
theorem t'_iij
  given: (i j : D.J)
  statement: D.t' i i j = (pullbackSymmetry _ _).hom
  proof: by
  have eq₁ := D.t_fac i i j
  have eq₂ := (IsIso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id]; rw [Category.comp_id]; rw [eq₂] at eq₁
  have eq₃ := (IsIso.eq_comp_inv (D.f i i)).mp eq₁
  rw [Category.assoc]; rw [← pullback.condition]; rw [← Category.assoc

中文:
定理 t'_iij
  条件: (i j : D.J)
  结论: D.t' i i j = (pullbackSymmetry _ _).hom
  证明: by
  have eq₁ := D.t_fac i i j
  have eq₂ := (IsIso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id]; rw [Category.comp_id]; rw [eq₂] at eq₁
  have eq₃ := (IsIso.eq_comp_inv (D.f i i)).mp eq₁
  rw [Category.assoc]; rw [← pullback.condition]; rw [← Category.assoc

Depends on / 依赖: Category, Category.assoc, Category.comp_id, D.t_fac, D.t_id, IsIso.eq_comp_inv, Mono.right_cancellation, comp_id, condition, eq_comp_inv, pullback, pullback.condition, pullbackSymmetry_hom_comp_fst, right_cancellation, t_fac, t_id
-/
theorem t'_iij (i j : D.J) : D.t' i i j = (pullbackSymmetry _ _).hom := by
  have eq₁ := D.t_fac i i j
  have eq₂ := (IsIso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _)
  rw [D.t_id]; rw [Category.comp_id]; rw [eq₂] at eq₁
  have eq₃ := (IsIso.eq_comp_inv (D.f i i)).mp eq₁
  rw [Category.assoc]; rw [← pullback.condition]; rw [← Category.assoc] at eq₃
  exact
    Mono.right_cancellation _ _
      ((Mono.right_cancellation _ _ eq₃).trans (pullbackSymmetry_hom_comp_fst _ _).symm)

/--
theorem `t'_jii` / 定理 `t'_jii`

English:
theorem t'_jii
  given: (i j : D.J)
  statement: D.t' j i i = pullback.fst _ _ ≫ D.t j i ≫ inv (pullback.snd _ _)
  proof: by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp

中文:
定理 t'_jii
  条件: (i j : D.J)
  结论: D.t' j i i = pullback.fst _ _ ≫ D.t j i ≫ inv (pullback.snd _ _)
  证明: by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp
-/
theorem t'_jii (i j : D.J) : D.t' j i i = pullback.fst _ _ ≫ D.t j i ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp

/--
theorem `t'_iji` / 定理 `t'_iji`

English:
theorem t'_iji
  given: (i j : D.J)
  statement: D.t' i j i = pullback.fst _ _ ≫ D.t i j ≫ inv (pullback.snd _ _)
  proof: by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp

@[reassoc, elementwise (attr := simp)]

中文:
定理 t'_iji
  条件: (i j : D.J)
  结论: D.t' i j i = pullback.fst _ _ ≫ D.t i j ≫ inv (pullback.snd _ _)
  证明: by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp

@[reassoc, elementwise (attr := simp)]
-/
theorem t'_iji (i j : D.J) : D.t' i j i = pullback.fst _ _ ≫ D.t i j ≫ inv (pullback.snd _ _) := by
  rw [← Category.assoc]; rw [← D.t_fac]
  simp

@[reassoc, elementwise (attr := simp)]
/--
theorem `t_inv` / 定理 `t_inv`

English:
theorem t_inv
  given: (i j : D.J)
  statement: D.t i j ≫ D.t j i = 𝟙 _
  proof: by
  have eq : (pullbackSymmetry (D.f i i) (D.f i j)).hom =
      pullback.snd _ _ ≫ inv (pullback.fst _ _) := by simp
  have := D.cocycle i j i
  rw [D.t'_iij]; rw [D.t'_jii]; rw [D.t'_iji]; rw [fst_eq_snd_of_mono_eq]; rw [eq] at this
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at this
  r

中文:
定理 t_inv
  条件: (i j : D.J)
  结论: D.t i j ≫ D.t j i = 𝟙 _
  证明: by
  have eq : (pullbackSymmetry (D.f i i) (D.f i j)).hom =
      pullback.snd _ _ ≫ inv (pullback.fst _ _) := by simp
  have := D.cocycle i j i
  rw [D.t'_iij]; rw [D.t'_jii]; rw [D.t'_iji]; rw [fst_eq_snd_of_mono_eq]; rw [eq] at this
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at this
  r

Depends on / 依赖: Category, Category.assoc, D.cocycle, IsIso.comp_inv_eq, IsIso.eq_inv_comp, IsIso.inv_hom_id_assoc, _iij, _iji, _jii, cocycle, comp_inv_eq, eq_inv_comp, fst_eq_snd_of_mono_eq, inv_hom_id_assoc, pullback, pullback.fst, pullback.snd, pullbackSymmetry
-/
theorem t_inv (i j : D.J) : D.t i j ≫ D.t j i = 𝟙 _ := by
  have eq : (pullbackSymmetry (D.f i i) (D.f i j)).hom =
      pullback.snd _ _ ≫ inv (pullback.fst _ _) := by simp
  have := D.cocycle i j i
  rw [D.t'_iij]; rw [D.t'_jii]; rw [D.t'_iji]; rw [fst_eq_snd_of_mono_eq]; rw [eq] at this
  simp only [Category.assoc, IsIso.inv_hom_id_assoc] at this
  rw [← IsIso.eq_inv_comp]; rw [← Category.assoc]; rw [IsIso.comp_inv_eq] at this
  simpa using this

/--
theorem `t'_inv` / 定理 `t'_inv`

English:
theorem t'_inv
  given: (i j k : D.J)
  proof: by
  rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
  simp [t_fac, t_fac_assoc]

中文:
定理 t'_inv
  条件: (i j k : D.J)
  证明: by
  rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
  simp [t_fac, t_fac_assoc]
-/
theorem t'_inv (i j k : D.J) :
    D.t' i j k ≫ (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom = 𝟙 _ := by
  rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
  simp [t_fac, t_fac_assoc]

/--
Instance `t_isIso` / 实例 `t_isIso`

English:
instance t_isIso
  signature: (i j : D.J)
  body: ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

中文:
实例 t_isIso
  签名: (i j : D.J)
  定义体: ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

Depends on / 依赖: D.t_inv, t_inv
-/
instance t_isIso (i j : D.J) : IsIso (D.t i j) :=
  ⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

/--
Instance `t'_isIso` / 实例 `t'_isIso`

English:
instance t'_isIso
  signature: (i j k : D.J)
  body: ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by simpa using D.cocycle _ _ _⟩⟩

@[reassoc]

中文:
实例 t'_isIso
  签名: (i j k : D.J)
  定义体: ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by simpa using D.cocycle _ _ _⟩⟩

@[reassoc]
-/
instance t'_isIso (i j k : D.J) : IsIso (D.t' i j k) :=
  ⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, by simpa using D.cocycle _ _ _⟩⟩

@[reassoc]
/--
theorem `t'_comp_eq_pullbackSymmetry` / 定理 `t'_comp_eq_pullbackSymmetry`

English:
theorem t'_comp_eq_pullbackSymmetry
  given: (i j k : D.J)
  proof: by
  trans inv (D.t' i j k)
  · exact IsIso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
  · rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
    simp [t_fac, t_fac_assoc]

中文:
定理 t'_comp_eq_pullbackSymmetry
  条件: (i j k : D.J)
  证明: by
  trans inv (D.t' i j k)
  · exact IsIso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
  · rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
    simp [t_fac, t_fac_assoc]

Depends on / 依赖: StrongEpi, strongEpi_of_isIso
-/
theorem t'_comp_eq_pullbackSymmetry (i j k : D.J) :
    D.t' j k i ≫ D.t' k i j =
      (pullbackSymmetry _ _).hom ≫ D.t' j i k ≫ (pullbackSymmetry _ _).hom := by
  trans inv (D.t' i j k)
  · exact IsIso.eq_inv_of_hom_inv_id (D.cocycle _ _ _)
  · rw [← cancel_mono (pullback.fst (D.f i j) (D.f i k))]
    simp [t_fac, t_fac_assoc]

/--
Definition of `sigmaOpens` / `sigmaOpens` 的定义

English:
definition sigmaOpens
  signature: [HasCoproduct D.U]
  body: ∐ D.U

中文:
定义 sigmaOpens
  签名: [HasCoproduct D.U]
  定义体: ∐ D.U
-/
def sigmaOpens [HasCoproduct D.U] : C :=
  ∐ D.U

/--
Definition of `diagram` / `diagram` 的定义

English:
definition diagram
  signature: : MultispanIndex (.prod D.J) C where
  body: D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]

中文:
定义 diagram
  签名: : MultispanIndex (.prod D.J) C where
  定义体: D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]
-/
def diagram : MultispanIndex (.prod D.J) C where
  left := D.V
  right := D.U
  fst := fun ⟨i, j⟩ => D.f i j
  snd := fun ⟨i, j⟩ => D.t i j ≫ D.f j i

@[simp]
/--
theorem `diagram_fst` / 定理 `diagram_fst`

English:
theorem diagram_fst
  given: (i j : D.J)
  statement: D.diagram.fst ⟨i, j⟩ = D.f i j
  proof: rfl

@[simp]

中文:
定理 diagram_fst
  条件: (i j : D.J)
  结论: D.diagram.fst ⟨i, j⟩ = D.f i j
  证明: rfl

@[simp]
-/
theorem diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j :=
  rfl

@[simp]
/--
theorem `diagram_snd` / 定理 `diagram_snd`

English:
theorem diagram_snd
  given: (i j : D.J)
  statement: D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i
  proof: rfl

@[simp]

中文:
定理 diagram_snd
  条件: (i j : D.J)
  结论: D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i
  证明: rfl

@[simp]
-/
theorem diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i :=
  rfl

@[simp]
/--
theorem `diagram_left` / 定理 `diagram_left`

English:
theorem diagram_left
  statement: D.diagram.left = D.V
  proof: rfl

@[simp]

中文:
定理 diagram_left
  结论: D.diagram.left = D.V
  证明: rfl

@[simp]

Depends on / 依赖: Balanced, StrongEpiCategory, balanced_of_strongEpiCategory
-/
theorem diagram_left : D.diagram.left = D.V :=
  rfl

@[simp]
/--
theorem `diagram_right` / 定理 `diagram_right`

English:
theorem diagram_right
  statement: D.diagram.right = D.U
  proof: rfl

中文:
定理 diagram_right
  结论: D.diagram.right = D.U
  证明: rfl
-/
theorem diagram_right : D.diagram.right = D.U :=
  rfl

section

variable [HasMulticoequalizer D.diagram]

/--
Definition of `glued` / `glued` 的定义

English:
definition glued
  signature: : C
  body: multicoequalizer D.diagram

中文:
定义 glued
  签名: : C
  定义体: multicoequalizer D.diagram

Depends on / 依赖: D.diagram, diagram, multicoequalizer
-/
def glued : C :=
  multicoequalizer D.diagram

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: (i : D.J)
  body: Multicoequalizer.π D.diagram i

@[elementwise (attr := simp)]

中文:
定义 ι
  签名: (i : D.J)
  定义体: Multicoequalizer.π D.diagram i

@[elementwise (attr := simp)]

Depends on / 依赖: D.diagram, Multicoequalizer, diagram
-/
def ι (i : D.J) : D.U i ⟶ D.glued :=
  Multicoequalizer.π D.diagram i

@[elementwise (attr := simp)]
/--
theorem `glue_condition` / 定理 `glue_condition`

English:
theorem glue_condition
  given: (i j : D.J)
  statement: D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
  proof: (Category.assoc _ _ _).symm.trans (Multicoequalizer.condition D.diagram ⟨i, j⟩).symm

中文:
定理 glue_condition
  条件: (i j : D.J)
  结论: D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i
  证明: (Category.assoc _ _ _).symm.trans (Multicoequalizer.condition D.diagram ⟨i, j⟩).symm

Depends on / 依赖: Category, Category.assoc, D.diagram, Multicoequalizer, Multicoequalizer.condition, condition, diagram, symm.trans
-/
theorem glue_condition (i j : D.J) : D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
  (Category.assoc _ _ _).symm.trans (Multicoequalizer.condition D.diagram ⟨i, j⟩).symm

/--
Definition of `vPullbackCone` / `vPullbackCone` 的定义

English:
definition vPullbackCone
  signature: (i j : D.J)
  body: PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

中文:
定义 vPullbackCone
  签名: (i j : D.J)
  定义体: PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

Depends on / 依赖: PullbackCone, PullbackCone.mk
-/
def vPullbackCone (i j : D.J) : PullbackCone (D.ι i) (D.ι j) :=
  PullbackCone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

variable [HasColimits C]

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : D.sigmaOpens ⟶ D.glued
  body: Multicoequalizer.sigmaπ D.diagram

中文:
定义 π
  签名: : D.sigmaOpens ⟶ D.glued
  定义体: Multicoequalizer.sigmaπ D.diagram

Depends on / 依赖: D.diagram, Multicoequalizer, Multicoequalizer.sigma, diagram
-/
def π : D.sigmaOpens ⟶ D.glued :=
  Multicoequalizer.sigmaπ D.diagram

/--
Instance `π_epi` / 实例 `π_epi`

English:
instance π_epi
  signature: : Epi D.π
  body: inferInstanceAs Epi (Multicoequalizer.sigmaπ D.diagram)

中文:
实例 π_epi
  签名: : Epi D.π
  定义体: inferInstanceAs Epi (Multicoequalizer.sigmaπ D.diagram)

Depends on / 依赖: D.diagram, Multicoequalizer, Multicoequalizer.sigma, diagram
-/
instance π_epi : Epi D.π := inferInstanceAs Epi (Multicoequalizer.sigmaπ D.diagram)

end

/--
theorem `types_π_surjective` / 定理 `types_π_surjective`

English:
theorem types_π_surjective
  given: (D : GlueData Type*)
  statement: Function.Surjective D.π
  proof: (epi_iff_surjective _).mp inferInstance

中文:
定理 types_π_surjective
  条件: (D : GlueData 类型)
  结论: Function.Surjective D.π
  证明: (epi_iff_surjective _).mp inferInstance

Depends on / 依赖: epi_iff_surjective
-/
theorem types_π_surjective (D : GlueData Type*) : Function.Surjective D.π :=
  (epi_iff_surjective _).mp inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `types_ι_jointly_surjective` / 定理 `types_ι_jointly_surjective`

English:
theorem types_ι_jointly_surjective
  given: (D : GlueData (Type v)) (x : D.glued)
  proof: by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  rw [← dsimp% ConcreteCategory.congr_hom
    (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom_inv_id x']
  rcases (colimit.isoColimitCocone (Types.cop

中文:
定理 types_ι_jointly_surjective
  条件: (D : GlueData (类型v)) (x : D.glued)
  证明: by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  rw [← dsimp% ConcreteCategory.congr_hom
    (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom_inv_id x']
  rcases (colimit.isoColimitCocone (Types.cop

Depends on / 依赖: CategoryTheory, CategoryTheory.GlueData, ConcreteCategory, ConcreteCategory.congr_hom, D.diagram, D.types_, GlueData, Multicoequalizer, Types.coproductColimitCocone, colimit, colimit.isoColimitCocone, congr_hom, coproductColimitCocone, diagram, hom_inv_id, isoColimitCocone, simp_rw
-/
theorem types_ι_jointly_surjective (D : GlueData (Type v)) (x : D.glued) :
    exists (i : _) (y : D.U i), D.ι i y = x := by
  delta CategoryTheory.GlueData.ι
  simp_rw [← Multicoequalizer.ι_sigmaπ D.diagram]
  rcases D.types_π_surjective x with ⟨x', rfl⟩
  rw [← dsimp% ConcreteCategory.congr_hom
    (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom_inv_id x']
  rcases (colimit.isoColimitCocone (Types.coproductColimitCocone _)).hom x' with ⟨i, y⟩
  refine ⟨i, y, ?_⟩
  simp
  rfl

variable (F : C ⥤ C')

section
variable [forall i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

instance (i j k : D.J) : HasPullback (F.map (D.f i j)) (F.map (D.f i k)) :=
  ⟨⟨⟨_, isLimitOfHasPullbackOfPreservesLimit F (D.f i j) (D.f i k)⟩⟩⟩

/-- A functor that preserves the pullbacks of `f i j` and `f i k` can map a family of glue data. -/
@[simps]
/--
Definition of `mapGlueData` / `mapGlueData` 的定义

English:
definition mapGlueData
  signature: : GlueData C' where
  body: D.J
  U i := F.obj (D.U i)
  V i := F.obj (D.V i)
  f i j := F.map (D.f i j)
  f_mono _ _ := preserves_mono_of_preservesLimit _ _
  f_id _ := inferInstance
  t i j := F.map (D.t i j)
  t_id i := by
    simp
  t' i j k :=
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k

中文:
定义 mapGlueData
  签名: : GlueData C' where
  定义体: D.J
  U i := F.obj (D.U i)
  V i := F.obj (D.V i)
  f i j := F.map (D.f i j)
  f_mono _ _ := preserves_mono_of_preservesLimit _ _
  f_id _ := inferInstance
  t i j := F.map (D.t i j)
  t_id i := by
    simp
  t' i j k :=
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k
-/
def mapGlueData : GlueData C' where
  J := D.J
  U i := F.obj (D.U i)
  V i := F.obj (D.V i)
  f i j := F.map (D.f i j)
  f_mono _ _ := preserves_mono_of_preservesLimit _ _
  f_id _ := inferInstance
  t i j := F.map (D.t i j)
  t_id i := by
    simp
  t' i j k :=
    (PreservesPullback.iso F (D.f i j) (D.f i k)).inv ≫
      F.map (D.t' i j k) ≫ (PreservesPullback.iso F (D.f j k) (D.f j i)).hom
  t_fac i j k := by simpa [Iso.inv_comp_eq] using congr_arg (fun f => F.map f) (D.t_fac i j k)
  cocycle i j k := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc, D.cocycle,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `diagramIso` / `diagramIso` 的定义

English:
definition diagramIso
  signature: : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan
  body: NatIso.ofComponents
    (fun x =>
      match x with
      | WalkingMultispan.left _ => Iso.refl _
      | WalkingMultispan.right _ => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _) <;> simp)

@[simp]

中文:
定义 diagramIso
  签名: : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan
  定义体: NatIso.ofComponents
    (fun x =>
      match x with
      | WalkingMultispan.left _ => Iso.refl _
      | WalkingMultispan.right _ => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _) <;> simp)

@[simp]

Depends on / 依赖: Iso.refl, NatIso, NatIso.ofComponents, WalkingMultispan, WalkingMultispan.left, WalkingMultispan.right, ofComponents
-/
def diagramIso : D.diagram.multispan ⋙ F ≅ (D.mapGlueData F).diagram.multispan :=
  NatIso.ofComponents
    (fun x =>
      match x with
      | WalkingMultispan.left _ => Iso.refl _
      | WalkingMultispan.right _ => Iso.refl _)
    (by
      rintro (⟨_, _⟩ | _) _ (_ | _ | _) <;> simp)

@[simp]
/--
theorem `diagramIso_app_left` / 定理 `diagramIso_app_left`

English:
theorem diagramIso_app_left
  given: (i : D.J × D.J)
  proof: rfl

@[simp]

中文:
定理 diagramIso_app_left
  条件: (i : D.J × D.J)
  证明: rfl

@[simp]
-/
theorem diagramIso_app_left (i : D.J × D.J) :
    (D.diagramIso F).app (WalkingMultispan.left i) = Iso.refl _ :=
  rfl

@[simp]
/--
theorem `diagramIso_app_right` / 定理 `diagramIso_app_right`

English:
theorem diagramIso_app_right
  given: (i : D.J)
  proof: rfl

@[simp]

中文:
定理 diagramIso_app_right
  条件: (i : D.J)
  证明: rfl

@[simp]
-/
theorem diagramIso_app_right (i : D.J) :
    (D.diagramIso F).app (WalkingMultispan.right i) = Iso.refl _ :=
  rfl

@[simp]
/--
theorem `diagramIso_hom_app_left` / 定理 `diagramIso_hom_app_left`

English:
theorem diagramIso_hom_app_left
  given: (i : D.J × D.J)
  proof: rfl

@[simp]

中文:
定理 diagramIso_hom_app_left
  条件: (i : D.J × D.J)
  证明: rfl

@[simp]
-/
theorem diagramIso_hom_app_left (i : D.J × D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `diagramIso_hom_app_right` / 定理 `diagramIso_hom_app_right`

English:
theorem diagramIso_hom_app_right
  given: (i : D.J)
  proof: rfl

@[simp]

中文:
定理 diagramIso_hom_app_right
  条件: (i : D.J)
  证明: rfl

@[simp]
-/
theorem diagramIso_hom_app_right (i : D.J) :
    (D.diagramIso F).hom.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `diagramIso_inv_app_left` / 定理 `diagramIso_inv_app_left`

English:
theorem diagramIso_inv_app_left
  given: (i : D.J × D.J)
  proof: rfl

@[simp]

中文:
定理 diagramIso_inv_app_left
  条件: (i : D.J × D.J)
  证明: rfl

@[simp]
-/
theorem diagramIso_inv_app_left (i : D.J × D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.left i) = 𝟙 _ :=
  rfl

@[simp]
/--
theorem `diagramIso_inv_app_right` / 定理 `diagramIso_inv_app_right`

English:
theorem diagramIso_inv_app_right
  given: (i : D.J)
  proof: rfl

中文:
定理 diagramIso_inv_app_right
  条件: (i : D.J)
  证明: rfl
-/
theorem diagramIso_inv_app_right (i : D.J) :
    (D.diagramIso F).inv.app (WalkingMultispan.right i) = 𝟙 _ :=
  rfl

end

variable [HasMulticoequalizer D.diagram] [PreservesColimit D.diagram.multispan F]

/--
theorem `hasColimit_multispan_comp` / 定理 `hasColimit_multispan_comp`

English:
theorem hasColimit_multispan_comp
  statement: HasColimit (D.diagram.multispan ⋙ F)
  proof: ⟨⟨⟨_, isColimitOfPreserves _ (colimit.isColimit _)⟩⟩⟩

中文:
定理 hasColimit_multispan_comp
  结论: HasColimit (D.diagram.multispan ⋙ F)
  证明: ⟨⟨⟨_, isColimitOfPreserves _ (colimit.isColimit _)⟩⟩⟩

Depends on / 依赖: colimit, colimit.isColimit, isColimit, isColimitOfPreserves
-/
theorem hasColimit_multispan_comp : HasColimit (D.diagram.multispan ⋙ F) :=
  ⟨⟨⟨_, isColimitOfPreserves _ (colimit.isColimit _)⟩⟩⟩

attribute [local instance] hasColimit_multispan_comp

variable [forall i j k, PreservesLimit (cospan (D.f i j) (D.f i k)) F]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `hasColimit_mapGlueData_diagram` / 定理 `hasColimit_mapGlueData_diagram`

English:
theorem hasColimit_mapGlueData_diagram
  statement: HasMulticoequalizer (D.mapGlueData F).diagram
  proof: hasColimit_of_iso (D.diagramIso F).symm

中文:
定理 hasColimit_mapGlueData_diagram
  结论: HasMulticoequalizer (D.mapGlueData F).diagram
  证明: hasColimit_of_iso (D.diagramIso F).symm

Depends on / 依赖: D.diagramIso, diagramIso, hasColimit_of_iso
-/
theorem hasColimit_mapGlueData_diagram : HasMulticoequalizer (D.mapGlueData F).diagram :=
  hasColimit_of_iso (D.diagramIso F).symm

attribute [local instance] hasColimit_mapGlueData_diagram

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `gluedIso` / `gluedIso` 的定义

English:
definition gluedIso
  signature: : F.obj D.glued ≅ (D.mapGlueData F).glued
  body: haveI : HasColimit (MultispanIndex.multispan (diagram (mapGlueData D F))) := inferInstance
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

中文:
定义 gluedIso
  签名: : F.obj D.glued ≅ (D.mapGlueData F).glued
  定义体: haveI : HasColimit (MultispanIndex.multispan (diagram (mapGlueData D F))) := inferInstance
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

Depends on / 依赖: D.diagram.multispan, D.diagramIso, HasColimit, Limits, Limits.HasColimit.isoOfNatIso, MultispanIndex, MultispanIndex.multispan, diagram, diagramIso, isoOfNatIso, mapGlueData, multispan, preservesColimitIso
-/
def gluedIso : F.obj D.glued ≅ (D.mapGlueData F).glued :=
  haveI : HasColimit (MultispanIndex.multispan (diagram (mapGlueData D F))) := inferInstance
  preservesColimitIso F D.diagram.multispan ≪≫ Limits.HasColimit.isoOfNatIso (D.diagramIso F)

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_gluedIso_hom` / 定理 `ι_gluedIso_hom`

English:
theorem ι_gluedIso_hom
  given: (i : D.J)
  statement: F.map (D.ι i) ≫ (D.gluedIso F).hom = (D.mapGlueData F).ι i
  proof: by
  simp [gluedIso, GlueData.ι]

中文:
定理 ι_gluedIso_hom
  条件: (i : D.J)
  结论: F.map (D.ι i) ≫ (D.gluedIso F).hom = (D.mapGlueData F).ι i
  证明: by
  simp [gluedIso, GlueData.ι]

Depends on / 依赖: GlueData, gluedIso
-/
theorem ι_gluedIso_hom (i : D.J) : F.map (D.ι i) ≫ (D.gluedIso F).hom = (D.mapGlueData F).ι i := by
  simp [gluedIso, GlueData.ι]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `ι_gluedIso_inv` / 定理 `ι_gluedIso_inv`

English:
theorem ι_gluedIso_inv
  given: (i : D.J)
  statement: (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i)
  proof: by
  rw [Iso.comp_inv_eq]; rw [ι_gluedIso_hom]

中文:
定理 ι_gluedIso_inv
  条件: (i : D.J)
  结论: (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i)
  证明: by
  rw [Iso.comp_inv_eq]; rw [ι_gluedIso_hom]

Depends on / 依赖: Iso.comp_inv_eq, comp_inv_eq
-/
theorem ι_gluedIso_inv (i : D.J) : (D.mapGlueData F).ι i ≫ (D.gluedIso F).inv = F.map (D.ι i) := by
  rw [Iso.comp_inv_eq]; rw [ι_gluedIso_hom]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `vPullbackConeIsLimitOfMap` / `vPullbackConeIsLimitOfMap` 的定义

English:
definition vPullbackConeIsLimitOfMap
  signature: (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
  body: by
  apply isLimitOfReflects F
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
      cospan ((D.mapGlueData F).ι i) ((D.mapGlueData F).ι j) :=
    NatIso.ofComponents
      (fun x => by
        cases x
        exacts [D.gluedIso F, Iso.refl _])

中文:
定义 vPullbackConeIsLimitOfMap
  签名: (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
  定义体: by
  apply isLimitOfReflects F
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
      cospan ((D.mapGlueData F).ι i) ((D.mapGlueData F).ι j) :=
    NatIso.ofComponents
      (fun x => by
        cases x
        exacts [D.gluedIso F, Iso.refl _])

Depends on / 依赖: Cone.ext, D.gluedIso, D.mapGlueData, F.map, IsLimit, IsLimit.postcomposeHomEquiv, Iso.refl, NatIso, NatIso.ofComponents, all_goals, cospan, exacts, gluedIso, hc.ofIsoLimit, isLimitMapConePullbackConeEquiv, isLimitOfReflects, mapGlueData, ofComponents, ofIsoLimit, postcomposeHomEquiv
-/
def vPullbackConeIsLimitOfMap (i j : D.J) [ReflectsLimit (cospan (D.ι i) (D.ι j)) F]
    (hc : IsLimit ((D.mapGlueData F).vPullbackCone i j)) : IsLimit (D.vPullbackCone i j) := by
  apply isLimitOfReflects F
  apply (isLimitMapConePullbackConeEquiv _ _).symm _
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
      cospan ((D.mapGlueData F).ι i) ((D.mapGlueData F).ι j) :=
    NatIso.ofComponents
      (fun x => by
        cases x
        exacts [D.gluedIso F, Iso.refl _])
      (by rintro (_ | _) (_ | _) (_ | _ | _) <;> simp)
  apply IsLimit.postcomposeHomEquiv e _ _
  apply hc.ofIsoLimit
  refine Cone.ext (Iso.refl _) ?_
  rintro (_ | _ | _)
  all_goals simp [e]; rfl

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `ι_jointly_surjective` / 定理 `ι_jointly_surjective`

English:
theorem ι_jointly_surjective
  statement: (F : C ⥤ Type v) [PreservesColimit D.diagram.multispan F]
  proof: by
  let e := D.gluedIso F
  obtain ⟨i, y, eq⟩ := (D.mapGlueData F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv eq
  change ((D.mapGlueData F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id]; rw [D.ι_gluedIso_inv] at eq
  exact ⟨i, y, eq⟩

中文:
定理 ι_jointly_surjective
  结论: (F : C ⥤ 类型v) [PreservesColimit D.diagram.multispan F]
  证明: by
  let e := D.gluedIso F
  obtain ⟨i, y, eq⟩ := (D.mapGlueData F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv eq
  change ((D.mapGlueData F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id]; rw [D.ι_gluedIso_inv] at eq
  exact ⟨i, y, eq⟩

Depends on / 依赖: D.gluedIso, D.mapGlueData, congr_arg, e.hom, e.hom_inv_id, e.inv, gluedIso, hom_inv_id, mapGlueData, replace
-/
theorem ι_jointly_surjective (F : C ⥤ Type v) [PreservesColimit D.diagram.multispan F]
    [forall i j k : D.J, PreservesLimit (cospan (D.f i j) (D.f i k)) F] (x : F.obj D.glued) :
    exists (i : _) (y : F.obj (D.U i)), F.map (D.ι i) y = x := by
  let e := D.gluedIso F
  obtain ⟨i, y, eq⟩ := (D.mapGlueData F).types_ι_jointly_surjective (e.hom x)
  replace eq := congr_arg e.inv eq
  change ((D.mapGlueData F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq
  rw [e.hom_inv_id]; rw [D.ι_gluedIso_inv] at eq
  exact ⟨i, y, eq⟩

end GlueData

section GlueData'

/--
Definition of `GlueData'` / `GlueData'` 的定义

English:
structure GlueData'
  parameters: where
  axioms and operations (11):
    - J : Type v
    - U : J -> C
    - V : forall (i j : J), i != j -> C
    - f : forall i j h, V i j h ⟶ U i
    - f_mono : forall i j h, Mono (f i j h)  [default: by infer_instance]
    - f_hasPullback : forall i j k hij hik, HasPullback (f i j hij) (f i k hik)  [default: by infer_instance]
    - t : forall i j h, V i j h ⟶ V j i h.symm
    - t' : forall i j k hij hik hjk, pullback (f i j hij) (f i k hik) ⟶ pullback (f j k hjk) (f j i hij.symm)
    - t_fac : forall i j k hij hik hjk, t' i j k hij hik hjk ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j hij
    - t_inv : forall i j hij, t i j hij ≫ t j i hij.symm = 𝟙 _
    - cocycle : forall i j k hij hik hjk, t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫ t' k i j hik.symm hjk.symm hij = 𝟙 _

中文:
结构 GlueData'
  参数: where
  公理与运算 (11 个):
    - J : 类型v
    - U : J -> C
    - V : 对任意 (i j : J), i != j -> C
    - f : 对任意 i j h, V i j h ⟶ U i
    - f_mono : 对任意 i j h, Mono (f i j h)  [默认: by infer_instance]
    - f_hasPullback : 对任意 i j k hij hik, HasPullback (f i j hij) (f i k hik)  [默认: by infer_instance]
    - t : 对任意 i j h, V i j h ⟶ V j i h.symm
    - t' : 对任意 i j k hij hik hjk, pullback (f i j hij) (f i k hik) ⟶ pullback (f j k hjk) (f j i hij.symm)
    - t_fac : 对任意 i j k hij hik hjk, t' i j k hij hik hjk ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j hij
    - t_inv : 对任意 i j hij, t i j hij ≫ t j i hij.symm = 𝟙 _
    - cocycle : 对任意 i j k hij hik hjk, t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫ t' k i j hik.symm hjk.symm hij = 𝟙 _

Depends on / 依赖: HasPullback, f_hasPullback, infer_instance
-/
structure GlueData' where
  /-- Indexing type of a glue data. -/
  J : Type v
  /-- Objects of a glue data to be glued. -/
  U : J -> C
  /-- Objects representing the intersections. -/
  V : forall (i j : J), i != j -> C
  /-- The inclusion maps of the intersection into the object. -/
  f : forall i j h, V i j h ⟶ U i
  f_mono : forall i j h, Mono (f i j h) := by infer_instance
  f_hasPullback : forall i j k hij hik, HasPullback (f i j hij) (f i k hik) := by infer_instance
  /-- The transition maps between the intersections. -/
  t : forall i j h, V i j h ⟶ V j i h.symm
  /-- The transition maps between the intersection of intersections. -/
  t' : forall i j k hij hik hjk,
    pullback (f i j hij) (f i k hik) ⟶ pullback (f j k hjk) (f j i hij.symm)
  t_fac : forall i j k hij hik hjk, t' i j k hij hik hjk ≫ pullback.snd _ _ =
    pullback.fst _ _ ≫ t i j hij
  t_inv : forall i j hij, t i j hij ≫ t j i hij.symm = 𝟙 _
  cocycle : forall i j k hij hik hjk, t' i j k hij hik hjk ≫
    t' j k i hjk hij.symm hik.symm ≫ t' k i j hik.symm hjk.symm hij = 𝟙 _

attribute [local instance] GlueData'.f_mono GlueData'.f_hasPullback

attribute [reassoc (attr := simp)] GlueData'.t_inv GlueData'.cocycle

variable {C}

open scoped Classical in
/--
Definition of `GlueData'.f'` / `GlueData'.f'` 的定义

English:
abbreviation GlueData'.f'
  signature: (D : GlueData' C) (i j : D.J)
  body: if h : i = j then eqToHom (dif_pos h) else eqToHom (dif_neg h) ≫ D.f i j h

中文:
缩写 GlueData'.f'
  签名: (D : GlueData' C) (i j : D.J)
  定义体: if h : i = j then eqToHom (dif_pos h) else eqToHom (dif_neg h) ≫ D.f i j h
-/
abbrev GlueData'.f' (D : GlueData' C) (i j : D.J) :
    (if h : i = j then D.U i else D.V i j h) ⟶ D.U i :=
  if h : i = j then eqToHom (dif_pos h) else eqToHom (dif_neg h) ≫ D.f i j h

instance (D : GlueData' C) (i j : D.J) :
    Mono (D.f' i j) := by dsimp [GlueData'.f']; split_ifs <;> infer_instance

instance (D : GlueData' C) (i : D.J) :
    IsIso (D.f' i i) := by simp only [GlueData'.f', ↓reduceDIte]; infer_instance

instance (D : GlueData' C) (i j k : D.J) :
    HasPullback (D.f' i j) (D.f' i k) := by
  if hij : i = j then
    apply +allowSynthFailures hasPullback_of_left_iso
    simp only [GlueData'.f', dif_pos hij]
    infer_instance
  else if hik : i = k then
    apply +allowSynthFailures hasPullback_of_right_iso
    simp only [GlueData'.f', dif_pos hik]
    infer_instance
  else
    have {X Y Z : C} (f : X ⟶ Y) (e : Z = X) : eqToHom e ≫ f ≍ f := by subst e; simp
    convert! D.f_hasPullback i j k hij hik <;> simp [GlueData'.f', hij, hik, this]

open scoped Classical in
/--
Definition of `GlueData'.t''` / `GlueData'.t''` 的定义

English:
definition GlueData'.t''
  signature: (D : GlueData' C) (i j k : D.J)
  body: if hij : i = j then
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by aesop))
        (by aesop) (by aesop)
  else if hik : i = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      subst hik; infer_instance
    pull

中文:
定义 GlueData'.t''
  签名: (D : GlueData' C) (i j k : D.J)
  定义体: if hij : i = j then
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by aesop))
        (by aesop) (by aesop)
  else if hik : i = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      subst hik; infer_instance
    pull
-/
def GlueData'.t'' (D : GlueData' C) (i j k : D.J) :
    pullback (D.f' i j) (D.f' i k) ⟶ pullback (D.f' j k) (D.f' j i) :=
  if hij : i = j then
    (pullbackSymmetry _ _).hom ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by aesop))
        (by aesop) (by aesop)
  else if hik : i = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      subst hik; infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else if hjk : j = k then
    have : IsIso (pullback.snd (D.f' j k) (D.f' j i)) := by
      apply +allowSynthFailures pullback_snd_iso_of_left_iso
      simp only [hjk, GlueData'.f', ↓reduceDIte]
      infer_instance
    pullback.fst _ _ ≫ eqToHom (dif_neg hij) ≫ D.t _ _ _ ≫
      eqToHom (dif_neg (Ne.symm hij)).symm ≫ inv (pullback.snd _ _)
  else
    haveI := Ne.symm hij
    pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by rw [dif_neg hik]))
        (eqToHom (by simp)) (by delta f'; aesop) (by delta f'; aesop) ≫
      D.t' i j k hij hik hjk ≫
      pullback.map _ _ _ _ (eqToHom (by aesop)) (eqToHom (by aesop)) (eqToHom (by simp))
        (by delta f'; aesop) (by delta f'; aesop)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
/--
Definition of `GlueData.ofGlueData'` / `GlueData.ofGlueData'` 的定义

English:
definition GlueData.ofGlueData'
  signature: (D : GlueData' C)
  body: D.J
  U := D.U
  V ij := if h : ij.1 = ij.2 then D.U ij.1 else D.V ij.1 ij.2 h
  f i j := D.f' i j
  f_id i := by simp only [↓reduceDIte, GlueData'.f']; infer_instance
  t i j := if h : i = j then eqToHom (by simp [h]) else
    eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm
  t

中文:
定义 GlueData.ofGlueData'
  签名: (D : GlueData' C)
  定义体: D.J
  U := D.U
  V ij := if h : ij.1 = ij.2 then D.U ij.1 else D.V ij.1 ij.2 h
  f i j := D.f' i j
  f_id i := by simp only [↓reduceDIte, GlueData'.f']; infer_instance
  t i j := if h : i = j then eqToHom (by simp [h]) else
    eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm
  t
-/
def GlueData.ofGlueData' (D : GlueData' C) : GlueData C where
  J := D.J
  U := D.U
  V ij := if h : ij.1 = ij.2 then D.U ij.1 else D.V ij.1 ij.2 h
  f i j := D.f' i j
  f_id i := by simp only [↓reduceDIte, GlueData'.f']; infer_instance
  t i j := if h : i = j then eqToHom (by simp [h]) else
    eqToHom (dif_neg h) ≫ D.t i j h ≫ eqToHom (dif_neg (Ne.symm h)).symm
  t_id i := by simp
  t' := D.t''
  t_fac i j k := by
    delta GlueData'.t''
    obtain rfl | _ := eq_or_ne i j
    · simp
    obtain rfl | _ := eq_or_ne i k
    · simp [*]
    obtain rfl | _ := eq_or_ne j k
    · simp [*]
    · simp [*, reassoc_of% D.t_fac]
  cocycle i j k := by
    delta GlueData'.t''
    if hij : i = j then
      subst hij
      if hik : i = k then
        subst hik
        ext <;> simp
      else
        simp [hik, Ne.symm hik, fst_eq_snd_of_mono_eq]
    else if hik : i = k then
      subst hik
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq, pullback.condition_assoc]
    else if hjk : j = k then
      subst hjk
      ext <;> simp [hij, Ne.symm hij, fst_eq_snd_of_mono_eq]
    else
      ext <;> simp [hij, Ne.symm hij, hik, Ne.symm hik, hjk, Ne.symm hjk,
        pullback.map_comp_assoc]

end GlueData'

end CategoryTheory
