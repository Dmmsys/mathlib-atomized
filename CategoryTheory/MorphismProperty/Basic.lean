/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Properties of morphisms

We provide the basic framework for talking about properties of morphisms.
The following meta-property is defined

* `RespectsLeft P Q`: `P` respects the property `Q` on the left if `P f → P (i ≫ f)` where
  `i` satisfies `Q`.
* `RespectsRight P Q`: `P` respects the property `Q` on the right if `P f → P (f ≫ i)` where
  `i` satisfies `Q`.
* `Respects`: `P` respects `Q` if `P` respects `Q` both on the left and on the right.

-/

@[expose] public section

universe w v v' u u'

open CategoryTheory Opposite

noncomputable section

namespace CategoryTheory

/--
Definition of `MorphismProperty` / `MorphismProperty` 的定义

English:
definition MorphismProperty
  signature: (C : Type u) [CategoryStruct.{v} C]
  body: forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

中文:
定义 MorphismProperty
  签名: (C : 类型u) [CategoryStruct.{v} C]
  定义体: forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop
-/
def MorphismProperty (C : Type u) [CategoryStruct.{v} C] :=
  forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop

namespace MorphismProperty

section

variable (C : Type u) [CategoryStruct.{v} C]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteBooleanAlgebra (MorphismProperty C)
  body: forall ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f -> P₂ f
  __ := (inferInstance : CompleteBooleanAlgebra (forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))

中文:
实例 :
  签名: 完备布尔代数 (MorphismProperty C)
  定义体: forall ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f -> P₂ f
  __ := (inferInstance : CompleteBooleanAlgebra (forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))
-/
instance : CompleteBooleanAlgebra (MorphismProperty C) where
  le P₁ P₂ := forall ⦃X Y : C⦄ (f : X ⟶ Y), P₁ f -> P₂ f
  __ := (inferInstance : CompleteBooleanAlgebra (forall ⦃X Y : C⦄ (_ : X ⟶ Y), Prop))

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  given: {P Q : MorphismProperty C}
  proof: Iff.rfl

中文:
引理 le_def
  条件: {P Q : MorphismProperty C}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma le_def {P Q : MorphismProperty C} :
    P <= Q ↔ forall {X Y : C} (f : X ⟶ Y), P f -> Q f := Iff.rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (MorphismProperty C)
  body: ⟨⊤⟩

中文:
实例 :
  签名: 可居 (MorphismProperty C)
  定义体: ⟨⊤⟩
-/
instance : Inhabited (MorphismProperty C) :=
  ⟨⊤⟩

/--
lemma `top_eq` / 引理 `top_eq`

English:
lemma top_eq
  statement: (⊤ : MorphismProperty C) = fun _ _ _ => True
  proof: rfl

中文:
引理 top_eq
  结论: (⊤ : MorphismProperty C) = fun _ _ _ => 真
  证明: rfl
-/
lemma top_eq : (⊤ : MorphismProperty C) = fun _ _ _ => True := rfl

variable {C}

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: (W W' : MorphismProperty C) (h : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f)
  proof: by
  funext X Y f
  rw [h]

@[simp]

中文:
引理 ext
  条件: (W W' : MorphismProperty C) (h : 对任意 ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f)
  证明: by
  funext X Y f
  rw [h]

@[simp]
-/
lemma ext (W W' : MorphismProperty C) (h : forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) :
    W = W' := by
  funext X Y f
  rw [h]

@[simp]
/--
lemma `top_apply` / 引理 `top_apply`

English:
lemma top_apply
  given: {X Y : C} (f : X ⟶ Y)
  statement: (⊤ : MorphismProperty C) f
  proof: by
  simp only [top_eq]

中文:
引理 top_apply
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (⊤ : MorphismProperty C) f
  证明: by
  simp only [top_eq]

Depends on / 依赖: top_eq
-/
lemma top_apply {X Y : C} (f : X ⟶ Y) : (⊤ : MorphismProperty C) f := by
  simp only [top_eq]

/--
lemma `of_eq_top` / 引理 `of_eq_top`

English:
lemma of_eq_top
  given: {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y)
  statement: P f
  proof: by
  simp [h]

@[simp]

中文:
引理 of_eq_top
  条件: {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y)
  结论: P f
  证明: by
  simp [h]

@[simp]
-/
lemma of_eq_top {P : MorphismProperty C} (h : P = ⊤) {X Y : C} (f : X ⟶ Y) : P f := by
  simp [h]

@[simp]
/--
lemma `sup_iff` / 引理 `sup_iff`

English:
lemma sup_iff
  given: (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  statement: (W ⊔ W') f ↔ W f ∨ W' f
  proof: Iff.rfl

中文:
引理 sup_iff
  条件: (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  结论: (W ⊔ W') f ↔ W f ∨ W' f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma sup_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊔ W') f ↔ W f ∨ W' f :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `sSup_iff` / 引理 `sSup_iff`

English:
lemma sSup_iff
  given: (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp +instances [MorphismProperty]

@[simp]

中文:
引理 sSup_iff
  条件: (S : 集合 (MorphismProperty C)) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp +instances [MorphismProperty]

@[simp]

Depends on / 依赖: MorphismProperty, instances
-/
lemma sSup_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sSup S f ↔ exists W in S, W f := by
  simp +instances [MorphismProperty]

@[simp]
/--
lemma `iSup_iff` / 引理 `iSup_iff`

English:
lemma iSup_iff
  given: {ι : Sort*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [← sSup_range]

@[simp]

中文:
引理 iSup_iff
  条件: {ι : 类型层*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [← sSup_range]

@[simp]

Depends on / 依赖: sSup_range
-/
lemma iSup_iff {ι : Sort*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    iSup W f ↔ exists i, W i f := by
  simp [← sSup_range]

@[simp]
/--
lemma `inf_iff` / 引理 `inf_iff`

English:
lemma inf_iff
  given: (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  statement: (W ⊓ W') f ↔ W f ∧ W' f
  proof: Iff.rfl

中文:
引理 inf_iff
  条件: (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  结论: (W ⊓ W') f ↔ W f ∧ W' f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma inf_iff (W W' : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : (W ⊓ W') f ↔ W f ∧ W' f :=
  Iff.rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `sInf_iff` / 引理 `sInf_iff`

English:
lemma sInf_iff
  given: (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp +instances [MorphismProperty]

@[simp]

中文:
引理 sInf_iff
  条件: (S : 集合 (MorphismProperty C)) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp +instances [MorphismProperty]

@[simp]

Depends on / 依赖: MorphismProperty, instances
-/
lemma sInf_iff (S : Set (MorphismProperty C)) {X Y : C} (f : X ⟶ Y) :
    sInf S f ↔ forall W in S, W f := by
  simp +instances [MorphismProperty]

@[simp]
/--
lemma `iInf_iff` / 引理 `iInf_iff`

English:
lemma iInf_iff
  given: {ι : Type*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  proof: by
  simp [← sInf_range]

中文:
引理 iInf_iff
  条件: {ι : 类型} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  证明: by
  simp [← sInf_range]

Depends on / 依赖: sInf_range
-/
lemma iInf_iff {ι : Type*} (W : ι -> MorphismProperty C) {X Y : C} (f : X ⟶ Y) :
    iInf W f ↔ forall i, W i f := by
  simp [← sInf_range]

/-- The morphism property in `Cᵒᵖ` associated to a morphism property in `C` -/
@[simp]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (P : MorphismProperty C)
  body: fun _ _ f => P f.unop

中文:
定义 op
  签名: (P : MorphismProperty C)
  定义体: fun _ _ f => P f.unop

Depends on / 依赖: f.unop
-/
def op (P : MorphismProperty C) : MorphismProperty Cᵒᵖ := fun _ _ f => P f.unop

/-- The morphism property in `C` associated to a morphism property in `Cᵒᵖ` -/
@[simp]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (P : MorphismProperty Cᵒᵖ)
  body: fun _ _ f => P f.op

中文:
定义 unop
  签名: (P : MorphismProperty Cᵒᵖ)
  定义体: fun _ _ f => P f.op

Depends on / 依赖: f.op
-/
def unop (P : MorphismProperty Cᵒᵖ) : MorphismProperty C := fun _ _ f => P f.op

/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (P : MorphismProperty C)
  statement: P.op.unop = P
  proof: rfl

中文:
定理 unop_op
  条件: (P : MorphismProperty C)
  结论: P.op.unop = P
  证明: rfl
-/
theorem unop_op (P : MorphismProperty C) : P.op.unop = P :=
  rfl

/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (P : MorphismProperty Cᵒᵖ)
  statement: P.unop.op = P
  proof: rfl

中文:
定理 op_unop
  条件: (P : MorphismProperty Cᵒᵖ)
  结论: P.unop.op = P
  证明: rfl
-/
theorem op_unop (P : MorphismProperty Cᵒᵖ) : P.unop.op = P :=
  rfl

end

section

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D] {E : Type*} [Category* E]

/--
Definition of `inverseImage` / `inverseImage` 的定义

English:
definition inverseImage
  signature: (P : MorphismProperty D) (F : C ⥤ D)
  body: fun _ _ f =>
  P (F.map f)

@[simp]

中文:
定义 inverseImage
  签名: (P : MorphismProperty D) (F : C ⥤ D)
  定义体: fun _ _ f =>
  P (F.map f)

@[simp]
-/
def inverseImage (P : MorphismProperty D) (F : C ⥤ D) : MorphismProperty C := fun _ _ f =>
  P (F.map f)

@[simp]
/--
lemma `inverseImage_iff` / 引理 `inverseImage_iff`

English:
lemma inverseImage_iff
  given: (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  proof: by rfl

@[simp]

中文:
引理 inverseImage_iff
  条件: (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)
  证明: by rfl

@[simp]
-/
lemma inverseImage_iff (P : MorphismProperty D) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) :
    P.inverseImage F f ↔ P (F.map f) := by rfl

@[simp]
/--
lemma `op_inverseImage` / 引理 `op_inverseImage`

English:
lemma op_inverseImage
  given: (P : MorphismProperty D) (F : C ⥤ D)
  proof: rfl

@[gcongr]

中文:
引理 op_inverseImage
  条件: (P : MorphismProperty D) (F : C ⥤ D)
  证明: rfl

@[gcongr]
-/
lemma op_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).op = P.op.inverseImage F.op := rfl

@[gcongr]
/--
lemma `monotone_inverseImage` / 引理 `monotone_inverseImage`

English:
lemma monotone_inverseImage
  given: (F : C ⥤ D)
  proof: fun _ _ h _ _ _ hf => h _ hf

@[simp]

中文:
引理 monotone_inverseImage
  条件: (F : C ⥤ D)
  证明: fun _ _ h _ _ _ hf => h _ hf

@[simp]
-/
lemma monotone_inverseImage (F : C ⥤ D) :
    Monotone (fun P : MorphismProperty D => P.inverseImage F) :=
  fun _ _ h _ _ _ hf => h _ hf

@[simp]
/--
lemma `inverseImage_id` / 引理 `inverseImage_id`

English:
lemma inverseImage_id
  given: (P : MorphismProperty C)
  statement: P.inverseImage (𝟭 C) = P
  proof: rfl

@[simp]

中文:
引理 inverseImage_id
  条件: (P : MorphismProperty C)
  结论: P.inverseImage (𝟭 C) = P
  证明: rfl

@[simp]
-/
lemma inverseImage_id (P : MorphismProperty C) : P.inverseImage (𝟭 C) = P :=
  rfl

@[simp]
/--
lemma `inverseImage_inverseImage` / 引理 `inverseImage_inverseImage`

English:
lemma inverseImage_inverseImage
  given: (P : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
  proof: rfl

中文:
引理 inverseImage_inverseImage
  条件: (P : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E)
  证明: rfl
-/
lemma inverseImage_inverseImage (P : MorphismProperty E) (F : C ⥤ D) (G : D ⥤ E) :
    (P.inverseImage G).inverseImage F = P.inverseImage (F ⋙ G) :=
  rfl

/--
Inductive type `strictMap` / 归纳类型 `strictMap`

English:
inductive strictMap
  parameters: (P : MorphismProperty C) (F : C ⥤ D)
  constructors (1):
    - map: {X Y : C} {f : X ⟶ Y} (hf : P f) : strictMap _ _ (F.map f)

中文:
归纳类型 strict映射
  参数: (P : MorphismProperty C) (F : C ⥤ D)
  构造子 (1 个):
    - map: {X Y : C} {f : X ⟶ Y} (hf : P f) : strict映射 _ _ (F.map f)
-/
inductive strictMap (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D where
  | map {X Y : C} {f : X ⟶ Y} (hf : P f) : strictMap _ _ (F.map f)

/--
lemma `map_mem_strictMap` / 引理 `map_mem_strictMap`

English:
lemma map_mem_strictMap
  given: (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f)
  proof: ⟨hf⟩

@[gcongr]

中文:
引理 map_mem_strictMap
  条件: (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f)
  证明: ⟨hf⟩

@[gcongr]
-/
lemma map_mem_strictMap (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.strictMap F) (F.map f) := ⟨hf⟩

@[gcongr]
/--
lemma `monotone_strictMap` / 引理 `monotone_strictMap`

English:
lemma monotone_strictMap
  given: (F : C ⥤ D)
  statement: Monotone (fun P : MorphismProperty C => P.strictMap F)
  proof: fun _ _ h _ _ _ ⟨hf⟩ => ⟨h _ hf⟩

@[simp]

中文:
引理 monotone_strictMap
  条件: (F : C ⥤ D)
  结论: 递增 (fun P : MorphismProperty C => P.strict映射 F)
  证明: fun _ _ h _ _ _ ⟨hf⟩ => ⟨h _ hf⟩

@[simp]
-/
lemma monotone_strictMap (F : C ⥤ D) : Monotone (fun P : MorphismProperty C => P.strictMap F) :=
  fun _ _ h _ _ _ ⟨hf⟩ => ⟨h _ hf⟩

@[simp]
/--
lemma `strictMap_id` / 引理 `strictMap_id`

English:
lemma strictMap_id
  given: (P : MorphismProperty C)
  proof: by
  ext
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]

中文:
引理 strictMap_id
  条件: (P : MorphismProperty C)
  证明: by
  ext
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]
-/
lemma strictMap_id (P : MorphismProperty C) :
    P.strictMap (𝟭 C) = P := by
  ext
  exact ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

@[simp]
/--
lemma `strictMap_strictMap` / 引理 `strictMap_strictMap`

English:
lemma strictMap_strictMap
  given: (P : MorphismProperty C) (F : C ⥤ D) (G : D ⥤ E)
  proof: by
  ext
  exact ⟨fun ⟨⟨h⟩⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨⟨h⟩⟩⟩

@[simp]

中文:
引理 strictMap_strictMap
  条件: (P : MorphismProperty C) (F : C ⥤ D) (G : D ⥤ E)
  证明: by
  ext
  exact ⟨fun ⟨⟨h⟩⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨⟨h⟩⟩⟩

@[simp]
-/
lemma strictMap_strictMap (P : MorphismProperty C) (F : C ⥤ D) (G : D ⥤ E) :
    (P.strictMap F).strictMap G = P.strictMap (F ⋙ G) := by
  ext
  exact ⟨fun ⟨⟨h⟩⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨⟨h⟩⟩⟩

@[simp]
/--
lemma `strictMap_le_iff_le_inverseImage` / 引理 `strictMap_le_iff_le_inverseImage`

English:
lemma strictMap_le_iff_le_inverseImage
  statement: (F : C ⥤ D) (P : MorphismProperty C)
  proof: ⟨fun h _ _ _ hf => h _ ⟨hf⟩, fun h _ _ _ ⟨hf⟩ => h _ hf⟩

中文:
引理 strictMap_le_iff_le_inverseImage
  结论: (F : C ⥤ D) (P : MorphismProperty C)
  证明: ⟨fun h _ _ _ hf => h _ ⟨hf⟩, fun h _ _ _ ⟨hf⟩ => h _ hf⟩
-/
lemma strictMap_le_iff_le_inverseImage (F : C ⥤ D) (P : MorphismProperty C)
    (P' : MorphismProperty D) : P.strictMap F <= P' ↔ P <= P'.inverseImage F :=
  ⟨fun h _ _ _ hf => h _ ⟨hf⟩, fun h _ _ _ ⟨hf⟩ => h _ hf⟩

/--
lemma `gc_strictMap` / 引理 `gc_strictMap`

English:
lemma gc_strictMap
  given: (F : C ⥤ D)
  statement: GaloisConnection (strictMap · F) (inverseImage · F)
  proof: strictMap_le_iff_le_inverseImage F

中文:
引理 gc_strictMap
  条件: (F : C ⥤ D)
  结论: GaloisConnection (strict映射 · F) (inverseImage · F)
  证明: strictMap_le_iff_le_inverseImage F

Depends on / 依赖: strictMap_le_iff_le_inverseImage
-/
lemma gc_strictMap (F : C ⥤ D) : GaloisConnection (strictMap · F) (inverseImage · F) :=
  strictMap_le_iff_le_inverseImage F

/--
lemma `le_inverseImage_strictMap` / 引理 `le_inverseImage_strictMap`

English:
lemma le_inverseImage_strictMap
  given: (P : MorphismProperty C) (F : C ⥤ D)
  proof: (gc_strictMap F).le_u_l P

中文:
引理 le_inverseImage_strictMap
  条件: (P : MorphismProperty C) (F : C ⥤ D)
  证明: (gc_strictMap F).le_u_l P

Depends on / 依赖: gc_strictMap, le_u_l
-/
lemma le_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) :
    P <= (P.strictMap F).inverseImage F :=
  (gc_strictMap F).le_u_l P

/--
lemma `strictMap_inverseImage_le` / 引理 `strictMap_inverseImage_le`

English:
lemma strictMap_inverseImage_le
  given: (P : MorphismProperty D) (F : C ⥤ D)
  proof: (gc_strictMap F).l_u_le P

@[simp]

中文:
引理 strictMap_inverseImage_le
  条件: (P : MorphismProperty D) (F : C ⥤ D)
  证明: (gc_strictMap F).l_u_le P

@[simp]

Depends on / 依赖: gc_strictMap, l_u_le
-/
lemma strictMap_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).strictMap F <= P :=
  (gc_strictMap F).l_u_le P

@[simp]
/--
lemma `strictMap_inverseImage_strictMap` / 引理 `strictMap_inverseImage_strictMap`

English:
lemma strictMap_inverseImage_strictMap
  given: (P : MorphismProperty C) (F : C ⥤ D)
  proof: (gc_strictMap F).l_u_l_eq_l P

@[simp]

中文:
引理 strictMap_inverseImage_strictMap
  条件: (P : MorphismProperty C) (F : C ⥤ D)
  证明: (gc_strictMap F).l_u_l_eq_l P

@[simp]

Depends on / 依赖: gc_strictMap, l_u_l_eq_l
-/
lemma strictMap_inverseImage_strictMap (P : MorphismProperty C) (F : C ⥤ D) :
    ((P.strictMap F).inverseImage F).strictMap F = P.strictMap F :=
  (gc_strictMap F).l_u_l_eq_l P

@[simp]
/--
lemma `inverseImage_strictMap_inverseImage` / 引理 `inverseImage_strictMap_inverseImage`

English:
lemma inverseImage_strictMap_inverseImage
  given: (P : MorphismProperty D) (F : C ⥤ D)
  proof: (gc_strictMap F).u_l_u_eq_u P

@[simp]

中文:
引理 inverseImage_strictMap_inverseImage
  条件: (P : MorphismProperty D) (F : C ⥤ D)
  证明: (gc_strictMap F).u_l_u_eq_u P

@[simp]

Depends on / 依赖: gc_strictMap, u_l_u_eq_u
-/
lemma inverseImage_strictMap_inverseImage (P : MorphismProperty D) (F : C ⥤ D) :
    ((P.inverseImage F).strictMap F).inverseImage F = P.inverseImage F :=
  (gc_strictMap F).u_l_u_eq_u P

@[simp]
/--
lemma `strictMap_bot` / 引理 `strictMap_bot`

English:
lemma strictMap_bot
  given: (F : C ⥤ D)
  proof: (gc_strictMap F).l_bot

@[simp]

中文:
引理 strictMap_bot
  条件: (F : C ⥤ D)
  证明: (gc_strictMap F).l_bot

@[simp]

Depends on / 依赖: gc_strictMap, l_bot
-/
lemma strictMap_bot (F : C ⥤ D) :
    strictMap ⊥ F = ⊥ :=
  (gc_strictMap F).l_bot

@[simp]
/--
lemma `inverseImage_strictMap_top` / 引理 `inverseImage_strictMap_top`

English:
lemma inverseImage_strictMap_top
  given: (F : C ⥤ D)
  proof: (gc_strictMap F).u_l_top

@[simp]

中文:
引理 inverseImage_strictMap_top
  条件: (F : C ⥤ D)
  证明: (gc_strictMap F).u_l_top

@[simp]

Depends on / 依赖: gc_strictMap, u_l_top
-/
lemma inverseImage_strictMap_top (F : C ⥤ D) :
    (strictMap ⊤ F).inverseImage F = ⊤ :=
  (gc_strictMap F).u_l_top

@[simp]
/--
lemma `inverseImage_bot` / 引理 `inverseImage_bot`

English:
lemma inverseImage_bot
  given: (F : C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 inverseImage_bot
  条件: (F : C ⥤ D)
  证明: rfl

@[simp]
-/
lemma inverseImage_bot (F : C ⥤ D) :
    inverseImage ⊥ F = ⊥ :=
  rfl

@[simp]
/--
lemma `inverseImage_top` / 引理 `inverseImage_top`

English:
lemma inverseImage_top
  given: (F : C ⥤ D)
  proof: rfl

@[simp]

中文:
引理 inverseImage_top
  条件: (F : C ⥤ D)
  证明: rfl

@[simp]
-/
lemma inverseImage_top (F : C ⥤ D) :
    inverseImage ⊤ F = ⊤ :=
  rfl

@[simp]
/--
lemma `strictMap_sup` / 引理 `strictMap_sup`

English:
lemma strictMap_sup
  given: (F : C ⥤ D) (P P' : MorphismProperty C)
  proof: (gc_strictMap F).l_sup

@[simp]

中文:
引理 strictMap_sup
  条件: (F : C ⥤ D) (P P' : MorphismProperty C)
  证明: (gc_strictMap F).l_sup

@[simp]

Depends on / 依赖: gc_strictMap, l_sup
-/
lemma strictMap_sup (F : C ⥤ D) (P P' : MorphismProperty C) :
    (P ⊔ P').strictMap F = P.strictMap F ⊔ P'.strictMap F :=
  (gc_strictMap F).l_sup

@[simp]
/--
lemma `strictMap_iSup` / 引理 `strictMap_iSup`

English:
lemma strictMap_iSup
  given: (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty C)
  proof: (gc_strictMap F).l_iSup

@[simp]

中文:
引理 strictMap_iSup
  条件: (F : C ⥤ D) {ι : 类型} (P : ι -> MorphismProperty C)
  证明: (gc_strictMap F).l_iSup

@[simp]

Depends on / 依赖: gc_strictMap, l_iSup
-/
lemma strictMap_iSup (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty C) :
    (⨆ i, P i).strictMap F = ⨆ i, (P i).strictMap F :=
  (gc_strictMap F).l_iSup

@[simp]
/--
lemma `strictMap_sSup` / 引理 `strictMap_sSup`

English:
lemma strictMap_sSup
  given: (F : C ⥤ D) (P : Set (MorphismProperty C))
  proof: (gc_strictMap F).l_sSup

@[simp]

中文:
引理 strictMap_sSup
  条件: (F : C ⥤ D) (P : 集合 (MorphismProperty C))
  证明: (gc_strictMap F).l_sSup

@[simp]

Depends on / 依赖: gc_strictMap, l_sSup
-/
lemma strictMap_sSup (F : C ⥤ D) (P : Set (MorphismProperty C)) :
    (sSup P).strictMap F = ⨆ P' in P, P'.strictMap F :=
  (gc_strictMap F).l_sSup

@[simp]
/--
lemma `inverseImage_inf` / 引理 `inverseImage_inf`

English:
lemma inverseImage_inf
  given: (F : C ⥤ D) (P P' : MorphismProperty D)
  proof: (gc_strictMap F).u_inf

@[simp]

中文:
引理 inverseImage_inf
  条件: (F : C ⥤ D) (P P' : MorphismProperty D)
  证明: (gc_strictMap F).u_inf

@[simp]

Depends on / 依赖: gc_strictMap, u_inf
-/
lemma inverseImage_inf (F : C ⥤ D) (P P' : MorphismProperty D) :
    (P ⊓ P').inverseImage F = P.inverseImage F ⊓ P'.inverseImage F :=
  (gc_strictMap F).u_inf

@[simp]
/--
lemma `inverseImage_iInf` / 引理 `inverseImage_iInf`

English:
lemma inverseImage_iInf
  given: (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D)
  proof: (gc_strictMap F).u_iInf

@[simp]

中文:
引理 inverseImage_iInf
  条件: (F : C ⥤ D) {ι : 类型} (P : ι -> MorphismProperty D)
  证明: (gc_strictMap F).u_iInf

@[simp]

Depends on / 依赖: gc_strictMap, u_iInf
-/
lemma inverseImage_iInf (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D) :
    (⨅ i, P i).inverseImage F = ⨅ i, (P i).inverseImage F :=
  (gc_strictMap F).u_iInf

@[simp]
/--
lemma `inverseImage_sInf` / 引理 `inverseImage_sInf`

English:
lemma inverseImage_sInf
  given: (F : C ⥤ D) (P : Set (MorphismProperty D))
  proof: (gc_strictMap F).u_sInf

@[simp]

中文:
引理 inverseImage_sInf
  条件: (F : C ⥤ D) (P : 集合 (MorphismProperty D))
  证明: (gc_strictMap F).u_sInf

@[simp]

Depends on / 依赖: gc_strictMap, u_sInf
-/
lemma inverseImage_sInf (F : C ⥤ D) (P : Set (MorphismProperty D)) :
    (sInf P).inverseImage F = ⨅ P' in P, P'.inverseImage F :=
  (gc_strictMap F).u_sInf

@[simp]
/--
lemma `inverseImage_sup` / 引理 `inverseImage_sup`

English:
lemma inverseImage_sup
  given: (F : C ⥤ D) (P P' : MorphismProperty D)
  proof: rfl

@[simp]

中文:
引理 inverseImage_sup
  条件: (F : C ⥤ D) (P P' : MorphismProperty D)
  证明: rfl

@[simp]
-/
lemma inverseImage_sup (F : C ⥤ D) (P P' : MorphismProperty D) :
    (P ⊔ P').inverseImage F = P.inverseImage F ⊔ P'.inverseImage F :=
  rfl

@[simp]
/--
lemma `inverseImage_iSup` / 引理 `inverseImage_iSup`

English:
lemma inverseImage_iSup
  given: (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D)
  proof: by
  ext; simp

@[simp]

中文:
引理 inverseImage_iSup
  条件: (F : C ⥤ D) {ι : 类型} (P : ι -> MorphismProperty D)
  证明: by
  ext; simp

@[simp]
-/
lemma inverseImage_iSup (F : C ⥤ D) {ι : Type*} (P : ι -> MorphismProperty D) :
    (⨆ i, P i).inverseImage F = ⨆ i, (P i).inverseImage F := by
  ext; simp

@[simp]
/--
lemma `inverseImage_sSup` / 引理 `inverseImage_sSup`

English:
lemma inverseImage_sSup
  given: (F : C ⥤ D) (P : Set (MorphismProperty D))
  proof: by
  ext; simp

中文:
引理 inverseImage_sSup
  条件: (F : C ⥤ D) (P : 集合 (MorphismProperty D))
  证明: by
  ext; simp
-/
lemma inverseImage_sSup (F : C ⥤ D) (P : Set (MorphismProperty D)) :
    (sSup P).inverseImage F = ⨆ P' in P, P'.inverseImage F := by
  ext; simp

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (P : MorphismProperty C) (F : C ⥤ D)
  body: fun _ _ f =>
  exists (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

中文:
定义 map
  签名: (P : MorphismProperty C) (F : C ⥤ D)
  定义体: fun _ _ f =>
  exists (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)
-/
def map (P : MorphismProperty C) (F : C ⥤ D) : MorphismProperty D := fun _ _ f =>
  exists (X' Y' : C) (f' : X' ⟶ Y') (_ : P f'), Nonempty (Arrow.mk (F.map f') ≅ Arrow.mk f)

/--
lemma `map_mem_map` / 引理 `map_mem_map`

English:
lemma map_mem_map
  given: (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f)
  proof: ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

@[gcongr]

中文:
引理 map_mem_map
  条件: (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f)
  证明: ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

@[gcongr]

Depends on / 依赖: Iso.refl
-/
lemma map_mem_map (P : MorphismProperty C) (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) (hf : P f) :
    (P.map F) (F.map f) := ⟨X, Y, f, hf, ⟨Iso.refl _⟩⟩

@[gcongr]
/--
lemma `monotone_map` / 引理 `monotone_map`

English:
lemma monotone_map
  given: (F : C ⥤ D)
  proof: by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

@[simp]

中文:
引理 monotone_map
  条件: (F : C ⥤ D)
  证明: by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

@[simp]
-/
lemma monotone_map (F : C ⥤ D) :
    Monotone (map · F) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

@[simp]
/--
lemma `map_top_eq_top_of_essSurj_of_full` / 引理 `map_top_eq_top_of_essSurj_of_full`

English:
lemma map_top_eq_top_of_essSurj_of_full
  given: (F : C ⥤ D) [F.EssSurj] [F.Full]
  proof: by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

中文:
引理 map_top_eq_top_of_essSurj_of_full
  条件: (F : C ⥤ D) [F.本质满射] [F.满]
  证明: by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

Depends on / 依赖: Arrow.isoMk, F.objPreimage, F.preimage, Functor, Functor.objObjPreimageIso, eq_top_iff, objObjPreimageIso, objPreimage, preimage
-/
lemma map_top_eq_top_of_essSurj_of_full (F : C ⥤ D) [F.EssSurj] [F.Full] :
    (⊤ : MorphismProperty C).map F = ⊤ := by
  rw [eq_top_iff]
  intro X Y f _
  refine ⟨F.objPreimage X, F.objPreimage Y, F.preimage ?_, ⟨⟨⟩, ⟨?_⟩⟩⟩
  · exact (Functor.objObjPreimageIso F X).hom ≫ f ≫ (Functor.objObjPreimageIso F Y).inv
  · exact Arrow.isoMk' _ _ (Functor.objObjPreimageIso F X) (Functor.objObjPreimageIso F Y)
      (by simp)

section

variable (P : MorphismProperty C)

/--
Definition of `toSet` / `toSet` 的定义

English:
definition toSet
  signature: : Set (Arrow C)
  body: Set.ofPred (fun f => P f.hom)

中文:
定义 toSet
  签名: : 集合 (箭头 C)
  定义体: Set.ofPred (fun f => P f.hom)

Depends on / 依赖: Set.ofPred, f.hom, f.mono, ofPred
-/
def toSet : Set (Arrow C) := Set.ofPred (fun f => P f.hom)

/--
lemma `mem_toSet_iff` / 引理 `mem_toSet_iff`

English:
lemma mem_toSet_iff
  given: (f : Arrow C)
  statement: f in P.toSet ↔ P f.hom
  proof: Iff.rfl

中文:
引理 mem_toSet_iff
  条件: (f : 箭头 C)
  结论: f in P.toSet ↔ P f.hom
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_toSet_iff (f : Arrow C) : f in P.toSet ↔ P f.hom := Iff.rfl

/--
lemma `toSet_iSup` / 引理 `toSet_iSup`

English:
lemma toSet_iSup
  given: {ι : Type*} (W : ι -> MorphismProperty C)
  proof: by
  ext
  simp [mem_toSet_iff]

中文:
引理 toSet_iSup
  条件: {ι : 类型} (W : ι -> MorphismProperty C)
  证明: by
  ext
  simp [mem_toSet_iff]

Depends on / 依赖: mem_toSet_iff
-/
lemma toSet_iSup {ι : Type*} (W : ι -> MorphismProperty C) :
    (⨆ i, W i).toSet = ⋃ i, (W i).toSet := by
  ext
  simp [mem_toSet_iff]

/--
lemma `toSet_max` / 引理 `toSet_max`

English:
lemma toSet_max
  given: (W₁ W₂ : MorphismProperty C)
  proof: rfl

中文:
引理 toSet_max
  条件: (W₁ W₂ : MorphismProperty C)
  证明: rfl
-/
lemma toSet_max (W₁ W₂ : MorphismProperty C) :
    (W₁ ⊔ W₂).toSet = W₁.toSet union W₂.toSet := rfl

/--
Definition of `homFamily` / `homFamily` 的定义

English:
definition homFamily
  signature: (f : P.toSet)
  body: f.1.hom

中文:
定义 homFamily
  签名: (f : P.toSet)
  定义体: f.1.hom
-/
def homFamily (f : P.toSet) : f.1.left ⟶ f.1.right := f.1.hom

/--
lemma `homFamily_apply` / 引理 `homFamily_apply`

English:
lemma homFamily_apply
  given: (f : P.toSet)
  statement: P.homFamily f = f.1.hom
  proof: rfl

@[simp]

中文:
引理 homFamily_apply
  条件: (f : P.toSet)
  结论: P.homFamily f = f.1.hom
  证明: rfl

@[simp]
-/
lemma homFamily_apply (f : P.toSet) : P.homFamily f = f.1.hom := rfl

@[simp]
/--
lemma `homFamily_arrow_mk` / 引理 `homFamily_arrow_mk`

English:
lemma homFamily_arrow_mk
  given: {X Y : C} (f : X ⟶ Y) (hf : P f)
  proof: rfl

@[simp]

中文:
引理 homFamily_arrow_mk
  条件: {X Y : C} (f : X ⟶ Y) (hf : P f)
  证明: rfl

@[simp]

Depends on / 依赖: MonoOver, MonoOver.forget, Over.forget, forget
-/
lemma homFamily_arrow_mk {X Y : C} (f : X ⟶ Y) (hf : P f) :
    P.homFamily ⟨Arrow.mk f, hf⟩ = f := rfl

@[simp]
/--
lemma `arrow_mk_mem_toSet_iff` / 引理 `arrow_mk_mem_toSet_iff`

English:
lemma arrow_mk_mem_toSet_iff
  given: {X Y : C} (f : X ⟶ Y)
  statement: Arrow.mk f in P.toSet ↔ P f
  proof: Iff.rfl

中文:
引理 arrow_mk_mem_toSet_iff
  条件: {X Y : C} (f : X ⟶ Y)
  结论: 箭头.mk f in P.toSet ↔ P f
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma arrow_mk_mem_toSet_iff {X Y : C} (f : X ⟶ Y) : Arrow.mk f in P.toSet ↔ P f := Iff.rfl

/--
lemma `of_eq` / 引理 `of_eq`

English:
lemma of_eq
  statement: {X Y : C} {f : X ⟶ Y} (hf : P f)
  proof: by
  rw [← P.arrow_mk_mem_toSet_iff] at hf ⊢
  rwa [(Arrow.mk_eq_mk_iff f' f).2 ⟨hX.symm, hY.symm, h⟩]

中文:
引理 of_eq
  结论: {X Y : C} {f : X ⟶ Y} (hf : P f)
  证明: by
  rw [← P.arrow_mk_mem_toSet_iff] at hf ⊢
  rwa [(Arrow.mk_eq_mk_iff f' f).2 ⟨hX.symm, hY.symm, h⟩]

Depends on / 依赖: Arrow.mk_eq_mk_iff, P.arrow_mk_mem_toSet_iff, arrow_mk_mem_toSet_iff, hX.symm, hY.symm, mk_eq_mk_iff
-/
lemma of_eq {X Y : C} {f : X ⟶ Y} (hf : P f)
    {X' Y' : C} {f' : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (h : f' = eqToHom hX.symm ≫ f ≫ eqToHom hY) :
    P f' := by
  rw [← P.arrow_mk_mem_toSet_iff] at hf ⊢
  rwa [(Arrow.mk_eq_mk_iff f' f).2 ⟨hX.symm, hY.symm, h⟩]

end

/--
Inductive type `ofHoms` / 归纳类型 `ofHoms`

English:
inductive ofHoms
  parameters: {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i)
  constructors (1):
    - mk: (i : ι) : ofHoms f (f i)

中文:
归纳类型 ofHoms
  参数: {ι : 类型} {X Y : ι -> C} (f : 对任意 i, X i ⟶ Y i)
  构造子 (1 个):
    - mk: (i : ι) : ofHoms f (f i)
-/
inductive ofHoms {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) : MorphismProperty C
  | mk (i : ι) : ofHoms f (f i)

/--
lemma `ofHoms_iff` / 引理 `ofHoms_iff`

English:
lemma ofHoms_iff
  given: {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B)
  proof: by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff]; rw [h]; rw [arrow_mk_mem_toSet_iff]
    constructor

@[simp]

中文:
引理 ofHoms_iff
  条件: {ι : 类型} {X Y : ι -> C} (f : 对任意 i, X i ⟶ Y i) {A B : C} (g : A ⟶ B)
  证明: by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff]; rw [h]; rw [arrow_mk_mem_toSet_iff]
    constructor

@[simp]

Depends on / 依赖: arrow_mk_mem_toSet_iff, ofHoms
-/
lemma ofHoms_iff {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) {A B : C} (g : A ⟶ B) :
    ofHoms f g ↔ exists i, Arrow.mk g = Arrow.mk (f i) := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, h⟩
    rw [← (ofHoms f).arrow_mk_mem_toSet_iff]; rw [h]; rw [arrow_mk_mem_toSet_iff]
    constructor

@[simp]
/--
lemma `ofHoms_homFamily` / 引理 `ofHoms_homFamily`

English:
lemma ofHoms_homFamily
  given: (P : MorphismProperty C)
  statement: ofHoms P.homFamily = P
  proof: by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : P.toSet)⟩

中文:
引理 ofHoms_homFamily
  条件: (P : MorphismProperty C)
  结论: ofHoms P.homFamily = P
  证明: by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : P.toSet)⟩

Depends on / 依赖: P.toSet, ofHoms_iff
-/
lemma ofHoms_homFamily (P : MorphismProperty C) : ofHoms P.homFamily = P := by
  ext _ _ f
  constructor
  · intro hf
    rw [ofHoms_iff] at hf
    obtain ⟨⟨f, hf⟩, ⟨_, _⟩⟩ := hf
    exact hf
  · intro hf
    exact ⟨(⟨f, hf⟩ : P.toSet)⟩

/--
lemma `iSup_ofHoms` / 引理 `iSup_ofHoms`

English:
lemma iSup_ofHoms
  statement: {α : Type*} {ι : α -> Type*} {A B : forall a, ι a -> C}
  proof: by
  ext f
  simp [ofHoms_iff]

@[simp]

中文:
引理 iSup_ofHoms
  结论: {α : 类型} {ι : α -> 类型} {A B : 对任意 a, ι a -> C}
  证明: by
  ext f
  simp [ofHoms_iff]

@[simp]

Depends on / 依赖: ofHoms_iff
-/
lemma iSup_ofHoms {α : Type*} {ι : α -> Type*} {A B : forall a, ι a -> C}
    (f : forall a, forall i, A a i ⟶ B a i) :
    ⨆ (a : α), ofHoms (f a) = ofHoms (fun (j : Σ (a : α), ι a) => f j.1 j.2) := by
  ext f
  simp [ofHoms_iff]

@[simp]
/--
lemma `ofHoms_le_iff` / 引理 `ofHoms_le_iff`

English:
lemma ofHoms_le_iff
  given: {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) (P : MorphismProperty C)
  proof: ⟨fun h i => h _ (ofHoms.mk i), fun h _ _ _⟨i⟩ => h i⟩

中文:
引理 ofHoms_le_iff
  条件: {ι : 类型} {X Y : ι -> C} (f : 对任意 i, X i ⟶ Y i) (P : MorphismProperty C)
  证明: ⟨fun h i => h _ (ofHoms.mk i), fun h _ _ _⟨i⟩ => h i⟩

Depends on / 依赖: ofHoms, ofHoms.mk
-/
lemma ofHoms_le_iff {ι : Type*} {X Y : ι -> C} (f : forall i, X i ⟶ Y i) (P : MorphismProperty C) :
    ofHoms f <= P ↔ forall i, P (f i) :=
  ⟨fun h i => h _ (ofHoms.mk i), fun h _ _ _⟨i⟩ => h i⟩

/--
Definition of `single` / `single` 的定义

English:
abbreviation single
  signature: {X Y : C} (f : X ⟶ Y)
  body: .ofHoms (fun (_ : Unit) => f)

中文:
缩写 single
  签名: {X Y : C} (f : X ⟶ Y)
  定义体: .ofHoms (fun (_ : Unit) => f)

Depends on / 依赖: ofHoms
-/
abbrev single {X Y : C} (f : X ⟶ Y) : MorphismProperty C := .ofHoms (fun (_ : Unit) => f)

/--
lemma `prop_single` / 引理 `prop_single`

English:
lemma prop_single
  given: {X Y : C} (f : X ⟶ Y)
  statement: (single f) f
  proof: by tauto

@[simp high]

中文:
引理 prop_single
  条件: {X Y : C} (f : X ⟶ Y)
  结论: (single f) f
  证明: by tauto

@[simp high]
-/
lemma prop_single {X Y : C} (f : X ⟶ Y) : (single f) f := by tauto

@[simp high]
/--
lemma `single_le_iff` / 引理 `single_le_iff`

English:
lemma single_le_iff
  given: (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  statement: single f <= W ↔ W f
  proof: by
  simp

中文:
引理 single_le_iff
  条件: (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y)
  结论: single f <= W ↔ W f
  证明: by
  simp
-/
lemma single_le_iff (W : MorphismProperty C) {X Y : C} (f : X ⟶ Y) : single f <= W ↔ W f := by
  simp

end

section

variable {C : Type u} [CategoryStruct.{v} C]

/--
Definition of `RespectsRight` / `RespectsRight` 的定义

English:
class RespectsRight
  parameters: (P Q : MorphismProperty C)
  axioms and operations (1):
    - postcomp({X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f)) : P (f ≫ i)

中文:
类 RespectsRight
  参数: (P Q : MorphismProperty C)
  公理与运算 (1 个):
    - postcomp({X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f)) : P (f ≫ i)
-/
class RespectsRight (P Q : MorphismProperty C) : Prop where
  postcomp {X Y Z : C} (i : Y ⟶ Z) (hi : Q i) (f : X ⟶ Y) (hf : P f) : P (f ≫ i)

/--
Definition of `RespectsLeft` / `RespectsLeft` 的定义

English:
class RespectsLeft
  parameters: (P Q : MorphismProperty C)
  axioms and operations (1):
    - precomp({X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f)) : P (i ≫ f)

中文:
类 RespectsLeft
  参数: (P Q : MorphismProperty C)
  公理与运算 (1 个):
    - precomp({X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f)) : P (i ≫ f)
-/
class RespectsLeft (P Q : MorphismProperty C) : Prop where
  precomp {X Y Z : C} (i : X ⟶ Y) (hi : Q i) (f : Y ⟶ Z) (hf : P f) : P (i ≫ f)

/--
Definition of `Respects` / `Respects` 的定义

English:
class Respects
  parameters: (P Q : MorphismProperty C)
  extends: P.RespectsLeft Q, P.RespectsRight Q
  (no additional axioms)

中文:
类 Respects
  参数: (P Q : MorphismProperty C)
  继承: P.RespectsLeft Q, P.RespectsRight Q
  (无附加公理)
-/
class Respects (P Q : MorphismProperty C) : Prop extends P.RespectsLeft Q, P.RespectsRight Q where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] [P.RespectsRight Q] : P.Respects Q where

instance (P Q : MorphismProperty C) [P.RespectsLeft Q] : P.op.RespectsRight Q.op where
  postcomp i hi f hf := RespectsLeft.precomp (Q := Q) i.unop hi f.unop hf

instance (P Q : MorphismProperty C) [P.RespectsRight Q] : P.op.RespectsLeft Q.op where
  precomp i hi f hf := RespectsRight.postcomp (Q := Q) i.unop hi f.unop hf

/--
Instance `RespectsLeft.inf` / 实例 `RespectsLeft.inf`

English:
instance RespectsLeft.inf
  signature: (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
  body: ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩

中文:
实例 RespectsLeft.下确界
  签名: (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
  定义体: ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩

Depends on / 依赖: hf.left, hf.right, precomp
-/
instance RespectsLeft.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsLeft Q]
    [P₂.RespectsLeft Q] : (P₁ ⊓ P₂).RespectsLeft Q where
  precomp i hi f hf := ⟨precomp i hi f hf.left, precomp i hi f hf.right⟩

/--
lemma `RespectsLeft.sInf` / 引理 `RespectsLeft.sInf`

English:
lemma RespectsLeft.sInf
  statement: {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
  proof: by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').precomp _ hi _ (hf _ hW')

中文:
引理 RespectsLeft.sInf
  结论: {W : 集合 (MorphismProperty C)} {Q : MorphismProperty C}
  证明: by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').precomp _ hi _ (hf _ hW')

Depends on / 依赖: precomp, sInf_iff
-/
lemma RespectsLeft.sInf {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
    (h : forall W' in W, W'.RespectsLeft Q) : (sInf W).RespectsLeft Q where
  precomp _ hi _ hf := by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').precomp _ hi _ (hf _ hW')

/--
Instance `RespectsLeft.iInf` / 实例 `RespectsLeft.iInf`

English:
instance RespectsLeft.iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 RespectsLeft.iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance RespectsLeft.iInf {ι : Type*} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
    [forall i, (W i).RespectsLeft Q] : (⨅ i, W i).RespectsLeft Q := by
  rw [← sInf_range]
  exact sInf (by simpa)

/--
Instance `RespectsRight.inf` / 实例 `RespectsRight.inf`

English:
instance RespectsRight.inf
  signature: (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
  body: ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩

中文:
实例 RespectsRight.下确界
  签名: (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
  定义体: ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩

Depends on / 依赖: hf.left, hf.right, postcomp
-/
instance RespectsRight.inf (P₁ P₂ Q : MorphismProperty C) [P₁.RespectsRight Q]
    [P₂.RespectsRight Q] : (P₁ ⊓ P₂).RespectsRight Q where
  postcomp i hi f hf := ⟨postcomp i hi f hf.left, postcomp i hi f hf.right⟩

/--
lemma `RespectsRight.sInf` / 引理 `RespectsRight.sInf`

English:
lemma RespectsRight.sInf
  statement: {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
  proof: by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').postcomp _ hi _ (hf _ hW')

中文:
引理 RespectsRight.sInf
  结论: {W : 集合 (MorphismProperty C)} {Q : MorphismProperty C}
  证明: by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').postcomp _ hi _ (hf _ hW')

Depends on / 依赖: postcomp, sInf_iff
-/
lemma RespectsRight.sInf {W : Set (MorphismProperty C)} {Q : MorphismProperty C}
    (h : forall W' in W, W'.RespectsRight Q) : (sInf W).RespectsRight Q where
  postcomp _ hi _ hf := by
    rw [sInf_iff] at hf ⊢
    exact fun _ hW' => (h _ hW').postcomp _ hi _ (hf _ hW')

/--
Instance `RespectsRight.iInf` / 实例 `RespectsRight.iInf`

English:
instance RespectsRight.iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 RespectsRight.iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance RespectsRight.iInf {ι : Type*} {W : ι -> MorphismProperty C} {Q : MorphismProperty C}
    [forall i, (W i).RespectsRight Q] : (⨅ i, W i).RespectsRight Q := by
  rw [← sInf_range]
  exact sInf (by simpa)

end

section

variable (C : Type u) [Category.{v} C]

/--
Definition of `isomorphisms` / `isomorphisms` 的定义

English:
abbreviation isomorphisms
  signature: : MorphismProperty C
  body: fun _ _ f => IsIso f

中文:
缩写 isomorphisms
  签名: : MorphismProperty C
  定义体: fun _ _ f => IsIso f
-/
abbrev isomorphisms : MorphismProperty C := fun _ _ f => IsIso f

/--
Definition of `monomorphisms` / `monomorphisms` 的定义

English:
abbreviation monomorphisms
  signature: : MorphismProperty C
  body: fun _ _ f => Mono f

中文:
缩写 monomorphisms
  签名: : MorphismProperty C
  定义体: fun _ _ f => Mono f
-/
abbrev monomorphisms : MorphismProperty C := fun _ _ f => Mono f

/--
Definition of `epimorphisms` / `epimorphisms` 的定义

English:
abbreviation epimorphisms
  signature: : MorphismProperty C
  body: fun _ _ f => Epi f

@[simp]

中文:
缩写 epimorphisms
  签名: : MorphismProperty C
  定义体: fun _ _ f => Epi f

@[simp]
-/
abbrev epimorphisms : MorphismProperty C := fun _ _ f => Epi f

@[simp]
/--
lemma `op_isomorphisms` / 引理 `op_isomorphisms`

English:
lemma op_isomorphisms
  statement: (isomorphisms C).op = isomorphisms Cᵒᵖ
  proof: by
  ext
  apply isIso_unop_iff

中文:
引理 op_isomorphisms
  结论: (isomorphisms C).op = isomorphisms Cᵒᵖ
  证明: by
  ext
  apply isIso_unop_iff

Depends on / 依赖: isIso_unop_iff
-/
lemma op_isomorphisms : (isomorphisms C).op = isomorphisms Cᵒᵖ := by
  ext
  apply isIso_unop_iff

section

variable {C}

/--
Definition of `RespectsIso` / `RespectsIso` 的定义

English:
abbreviation RespectsIso
  signature: (P : MorphismProperty C)
  body: P.Respects (isomorphisms C)

中文:
缩写 RespectsIso
  签名: (P : MorphismProperty C)
  定义体: P.Respects (isomorphisms C)

Depends on / 依赖: P.Respects, Respects, isomorphisms
-/
abbrev RespectsIso (P : MorphismProperty C) : Prop := P.Respects (isomorphisms C)

/--
Instance `RespectsIso.inf` / 实例 `RespectsIso.inf`

English:
instance RespectsIso.inf
  signature: (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso]
  body: RespectsIso.inf

中文:
实例 RespectsIso.下确界
  签名: (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso]
  定义体: RespectsIso.inf
-/
instance RespectsIso.inf (P Q : MorphismProperty C) [P.RespectsIso] [Q.RespectsIso] :
    (P ⊓ Q).RespectsIso where

@[deprecated (since := "2026-05-04")] alias inf := RespectsIso.inf

/--
lemma `RespectsIso.sInf` / 引理 `RespectsIso.sInf`

English:
lemma RespectsIso.sInf
  given: {W : Set (MorphismProperty C)} (h : forall W' in W, W'.RespectsIso)
  proof: RespectsLeft.sInf (fun W' hW' => (h W' hW').toRespectsLeft)
  toRespectsRight := RespectsRight.sInf (fun W' hW' => (h W' hW').toRespectsRight)

中文:
引理 RespectsIso.sInf
  条件: {W : 集合 (MorphismProperty C)} (h : 对任意 W' in W, W'.RespectsIso)
  证明: RespectsLeft.sInf (fun W' hW' => (h W' hW').toRespectsLeft)
  toRespectsRight := RespectsRight.sInf (fun W' hW' => (h W' hW').toRespectsRight)

Depends on / 依赖: RespectsLeft, RespectsLeft.sInf, toRespectsLeft
-/
lemma RespectsIso.sInf {W : Set (MorphismProperty C)} (h : forall W' in W, W'.RespectsIso) :
    (sInf W).RespectsIso where
  toRespectsLeft := RespectsLeft.sInf (fun W' hW' => (h W' hW').toRespectsLeft)
  toRespectsRight := RespectsRight.sInf (fun W' hW' => (h W' hW').toRespectsRight)

/--
Instance `RespectsIso.iInf` / 实例 `RespectsIso.iInf`

English:
instance RespectsIso.iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C} [forall i, (W i).RespectsIso]
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 RespectsIso.iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C} [对任意 i, (W i).RespectsIso]
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance RespectsIso.iInf {ι : Type*} {W : ι -> MorphismProperty C} [forall i, (W i).RespectsIso] :
    (⨅ i, W i).RespectsIso := by
  rw [← sInf_range]
  exact sInf (by simpa)

/--
lemma `RespectsIso.mk` / 引理 `RespectsIso.mk`

English:
lemma RespectsIso.mk
  statement: (P : MorphismProperty C)
  proof: hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf

中文:
引理 RespectsIso.mk
  结论: (P : MorphismProperty C)
  证明: hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf

Depends on / 依赖: hprecomp
-/
lemma RespectsIso.mk (P : MorphismProperty C)
    (hprecomp : forall {X Y Z : C} (e : X ≅ Y) (f : Y ⟶ Z) (_ : P f), P (e.hom ≫ f))
    (hpostcomp : forall {X Y Z : C} (e : Y ≅ Z) (f : X ⟶ Y) (_ : P f), P (f ≫ e.hom)) :
    P.RespectsIso where
  precomp e (_ : IsIso e) f hf := hprecomp (asIso e) f hf
  postcomp e (_ : IsIso e) f hf := hpostcomp (asIso e) f hf

/--
lemma `RespectsIso.precomp` / 引理 `RespectsIso.precomp`

English:
lemma RespectsIso.precomp
  statement: (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
  proof: RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf

中文:
引理 RespectsIso.precomp
  结论: (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
  证明: RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf

Depends on / 依赖: RespectsLeft, RespectsLeft.precomp, isomorphisms, precomp
-/
lemma RespectsIso.precomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : X ⟶ Y)
    [IsIso e] (f : Y ⟶ Z) (hf : P f) : P (e ≫ f) :=
  RespectsLeft.precomp (Q := isomorphisms C) e ‹IsIso e› f hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RespectsIso (⊤ : MorphismProperty C)
  body: trivial
  postcomp _ _ _ _ := trivial

中文:
实例 :
  签名: RespectsIso (⊤ : MorphismProperty C)
  定义体: trivial
  postcomp _ _ _ _ := trivial
-/
instance : RespectsIso (⊤ : MorphismProperty C) where
  precomp _ _ _ _ := trivial
  postcomp _ _ _ _ := trivial

/--
lemma `RespectsIso.postcomp` / 引理 `RespectsIso.postcomp`

English:
lemma RespectsIso.postcomp
  statement: (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
  proof: RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf

中文:
引理 RespectsIso.postcomp
  结论: (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
  证明: RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf

Depends on / 依赖: RespectsRight, RespectsRight.postcomp, isomorphisms, postcomp
-/
lemma RespectsIso.postcomp (P : MorphismProperty C) [P.RespectsIso] {X Y Z : C} (e : Y ⟶ Z)
    [IsIso e] (f : X ⟶ Y) (hf : P f) : P (f ≫ e) :=
  RespectsRight.postcomp (Q := isomorphisms C) e ‹IsIso e› f hf

/--
Instance `RespectsIso.op` / 实例 `RespectsIso.op`

English:
instance RespectsIso.op
  signature: (P : MorphismProperty C) [RespectsIso P]
  body: postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf

中文:
实例 RespectsIso.op
  签名: (P : MorphismProperty C) [RespectsIso P]
  定义体: postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf

Depends on / 依赖: e.unop, f.unop, postcomp
-/
instance RespectsIso.op (P : MorphismProperty C) [RespectsIso P] : RespectsIso P.op where
  precomp e (_ : IsIso e) f hf := postcomp P e.unop f.unop hf
  postcomp e (_ : IsIso e) f hf := precomp P e.unop f.unop hf

/--
Instance `RespectsIso.unop` / 实例 `RespectsIso.unop`

English:
instance RespectsIso.unop
  signature: (P : MorphismProperty Cᵒᵖ) [RespectsIso P]
  body: postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

中文:
实例 RespectsIso.unop
  签名: (P : MorphismProperty Cᵒᵖ) [RespectsIso P]
  定义体: postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

Depends on / 依赖: e.op, f.op, postcomp
-/
instance RespectsIso.unop (P : MorphismProperty Cᵒᵖ) [RespectsIso P] : RespectsIso P.unop where
  precomp e (_ : IsIso e) f hf := postcomp P e.op f.op hf
  postcomp e (_ : IsIso e) f hf := precomp P e.op f.op hf

/--
Definition of `isoClosure` / `isoClosure` 的定义

English:
definition isoClosure
  signature: (P : MorphismProperty C)
  body: fun _ _ f => exists (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

中文:
定义 isoClosure
  签名: (P : MorphismProperty C)
  定义体: fun _ _ f => exists (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

Depends on / 依赖: Arrow.mk, Nonempty
-/
def isoClosure (P : MorphismProperty C) : MorphismProperty C :=
  fun _ _ f => exists (Y₁ Y₂ : C) (f' : Y₁ ⟶ Y₂) (_ : P f'), Nonempty (Arrow.mk f' ≅ Arrow.mk f)

/--
lemma `le_isoClosure` / 引理 `le_isoClosure`

English:
lemma le_isoClosure
  given: (P : MorphismProperty C)
  statement: P <= P.isoClosure
  proof: fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

中文:
引理 le_isoClosure
  条件: (P : MorphismProperty C)
  结论: P <= P.isoClosure
  证明: fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

Depends on / 依赖: Iso.refl
-/
lemma le_isoClosure (P : MorphismProperty C) : P <= P.isoClosure :=
  fun _ _ f hf => ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Instance `isoClosure_respectsIso` / 实例 `isoClosure_respectsIso`

English:
instance isoClosure_respectsIso
  signature: (P : MorphismProperty C)
  body: fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩

中文:
实例 isoClosure_respectsIso
  签名: (P : MorphismProperty C)
  定义体: fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩
-/
instance isoClosure_respectsIso (P : MorphismProperty C) :
    RespectsIso P.isoClosure where
  precomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left ≪≫ asIso (inv e)) (asIso iso.hom.right) (by simp)⟩⟩
  postcomp := fun e (he : IsIso e) f ⟨_, _, f', hf', ⟨iso⟩⟩ => ⟨_, _, f', hf',
      ⟨Arrow.isoMk (asIso iso.hom.left) (asIso iso.hom.right ≪≫ asIso e) (by simp)⟩⟩

/--
lemma `monotone_isoClosure` / 引理 `monotone_isoClosure`

English:
lemma monotone_isoClosure
  statement: Monotone (isoClosure (C := C))
  proof: by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

中文:
引理 monotone_isoClosure
  结论: 递增 (isoClosure (C := C))
  证明: by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩
-/
lemma monotone_isoClosure : Monotone (isoClosure (C := C)) := by
  intro P Q h X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact ⟨X', Y', f', h _ hf', ⟨e⟩⟩

/--
theorem `cancel_left_of_respectsIso` / 定理 `cancel_left_of_respectsIso`

English:
theorem cancel_left_of_respectsIso
  statement: (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
  proof: ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩

中文:
定理 cancel_left_of_respectsIso
  结论: (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
  证明: ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩

Depends on / 依赖: RespectsIso, RespectsIso.precomp, precomp
-/
theorem cancel_left_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] : P (f ≫ g) ↔ P g :=
  ⟨fun h => by simpa using RespectsIso.precomp P (inv f) (f ≫ g) h, RespectsIso.precomp P f g⟩

/--
theorem `cancel_right_of_respectsIso` / 定理 `cancel_right_of_respectsIso`

English:
theorem cancel_right_of_respectsIso
  statement: (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
  proof: ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩

中文:
定理 cancel_right_of_respectsIso
  结论: (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
  证明: ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩

Depends on / 依赖: RespectsIso, RespectsIso.postcomp, postcomp
-/
theorem cancel_right_of_respectsIso (P : MorphismProperty C) [hP : RespectsIso P] {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] : P (f ≫ g) ↔ P f :=
  ⟨fun h => by simpa using RespectsIso.postcomp P (inv g) (f ≫ g) h, RespectsIso.postcomp P g f⟩

/--
lemma `comma_iso_iff` / 引理 `comma_iso_iff`

English:
lemma comma_iso_iff
  statement: (P : MorphismProperty C) [P.RespectsIso]
  proof: by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]

中文:
引理 comma_iso_iff
  结论: (P : MorphismProperty C) [P.RespectsIso]
  证明: by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]

Depends on / 依赖: Comma.inv_left_hom_right, cancel_left_of_respectsIso, cancel_right_of_respectsIso, e.hom, inv_left_hom_right
-/
lemma comma_iso_iff (P : MorphismProperty C) [P.RespectsIso]
    {A B : Type*} [Category* A] [Category* B]
    {L : A ⥤ C} {R : B ⥤ C} {f g : Comma L R} (e : f ≅ g) :
    P f.hom ↔ P g.hom := by
  simp [← Comma.inv_left_hom_right e.hom, cancel_left_of_respectsIso, cancel_right_of_respectsIso]

/--
theorem `arrow_iso_iff` / 定理 `arrow_iso_iff`

English:
theorem arrow_iso_iff
  statement: (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
  proof: P.comma_iso_iff e

中文:
定理 arrow_iso_iff
  结论: (P : MorphismProperty C) [RespectsIso P] {f g : 箭头 C}
  证明: P.comma_iso_iff e

Depends on / 依赖: P.comma_iso_iff, comma_iso_iff
-/
theorem arrow_iso_iff (P : MorphismProperty C) [RespectsIso P] {f g : Arrow C}
    (e : f ≅ g) : P f.hom ↔ P g.hom :=
  P.comma_iso_iff e

/--
theorem `arrow_mk_iso_iff` / 定理 `arrow_mk_iso_iff`

English:
theorem arrow_mk_iso_iff
  statement: (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
  proof: P.arrow_iso_iff e

中文:
定理 arrow_mk_iso_iff
  结论: (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
  证明: P.arrow_iso_iff e

Depends on / 依赖: P.arrow_iso_iff, arrow_iso_iff
-/
theorem arrow_mk_iso_iff (P : MorphismProperty C) [RespectsIso P] {W X Y Z : C}
    {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) : P f ↔ P g :=
  P.arrow_iso_iff e

set_option backward.isDefEq.respectTransparency false in
/--
theorem `RespectsIso.of_respects_arrow_iso` / 定理 `RespectsIso.of_respects_arrow_iso`

English:
theorem RespectsIso.of_respects_arrow_iso
  statement: (P : MorphismProperty C)
  proof: by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp

中文:
定理 RespectsIso.of_respects_arrow_iso
  结论: (P : MorphismProperty C)
  证明: by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp

Depends on / 依赖: Arrow.isoMk, Arrow.mk, Iso.refl, postcomp
-/
theorem RespectsIso.of_respects_arrow_iso (P : MorphismProperty C)
    (hP : forall (f g : Arrow C) (_ : f ≅ g) (_ : P f.hom), P g.hom) : RespectsIso P where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (e ≫ f)) (Arrow.isoMk (asIso (inv e)) (Iso.refl _) ?_) hf
    simp
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    refine hP (Arrow.mk f) (Arrow.mk (f ≫ e)) (Arrow.isoMk (Iso.refl _) (asIso e) ?_) hf
    simp

/--
lemma `isoClosure_eq_iff` / 引理 `isoClosure_eq_iff`

English:
lemma isoClosure_eq_iff
  given: (P : MorphismProperty C)
  proof: by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP => le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

中文:
引理 isoClosure_eq_iff
  条件: (P : MorphismProperty C)
  证明: by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP => le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

Depends on / 依赖: P.arrow_mk_iso_iff, P.isoClosure_respectsIso, P.le_isoClosure, arrow_mk_iso_iff, isoClosure_respectsIso, le_antisymm, le_isoClosure
-/
lemma isoClosure_eq_iff (P : MorphismProperty C) :
    P.isoClosure = P ↔ P.RespectsIso := by
  refine ⟨(· ▸ P.isoClosure_respectsIso), fun hP => le_antisymm ?_ (P.le_isoClosure)⟩
  intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
  exact (P.arrow_mk_iso_iff e).1 hf'

/--
lemma `isoClosure_eq_self` / 引理 `isoClosure_eq_self`

English:
lemma isoClosure_eq_self
  given: (P : MorphismProperty C) [P.RespectsIso]
  proof: by rwa [isoClosure_eq_iff]

@[simp]

中文:
引理 isoClosure_eq_self
  条件: (P : MorphismProperty C) [P.RespectsIso]
  证明: by rwa [isoClosure_eq_iff]

@[simp]

Depends on / 依赖: isoClosure_eq_iff
-/
lemma isoClosure_eq_self (P : MorphismProperty C) [P.RespectsIso] :
    P.isoClosure = P := by rwa [isoClosure_eq_iff]

@[simp]
/--
lemma `isoClosure_isoClosure` / 引理 `isoClosure_isoClosure`

English:
lemma isoClosure_isoClosure
  given: (P : MorphismProperty C)
  proof: P.isoClosure.isoClosure_eq_self

中文:
引理 isoClosure_isoClosure
  条件: (P : MorphismProperty C)
  证明: P.isoClosure.isoClosure_eq_self

Depends on / 依赖: P.isoClosure.isoClosure_eq_self, isoClosure, isoClosure_eq_self
-/
lemma isoClosure_isoClosure (P : MorphismProperty C) :
    P.isoClosure.isoClosure = P.isoClosure :=
  P.isoClosure.isoClosure_eq_self

/--
lemma `isoClosure_le_iff` / 引理 `isoClosure_le_iff`

English:
lemma isoClosure_le_iff
  given: (P Q : MorphismProperty C) [Q.RespectsIso]
  proof: by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

中文:
引理 isoClosure_le_iff
  条件: (P Q : MorphismProperty C) [Q.RespectsIso]
  证明: by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

Depends on / 依赖: P.le_isoClosure.trans, Q.isoClosure_eq_self, isoClosure_eq_self, le_isoClosure, monotone_isoClosure
-/
lemma isoClosure_le_iff (P Q : MorphismProperty C) [Q.RespectsIso] :
    P.isoClosure <= Q ↔ P <= Q := by
  constructor
  · exact P.le_isoClosure.trans
  · intro h
    exact (monotone_isoClosure h).trans (by rw [Q.isoClosure_eq_self])

section

variable {D : Type*} [Category* D]

/--
lemma `isoClosure_strictMap_le` / 引理 `isoClosure_strictMap_le`

English:
lemma isoClosure_strictMap_le
  given: (P : MorphismProperty C) (F : C ⥤ D)
  proof: fun _ _ _ ⟨⟨_, _, _, hf, ⟨i⟩⟩⟩ => ⟨_, _, _, ⟨hf⟩, ⟨F.mapArrow.mapIso i⟩⟩

中文:
引理 isoClosure_strictMap_le
  条件: (P : MorphismProperty C) (F : C ⥤ D)
  证明: fun _ _ _ ⟨⟨_, _, _, hf, ⟨i⟩⟩⟩ => ⟨_, _, _, ⟨hf⟩, ⟨F.mapArrow.mapIso i⟩⟩

Depends on / 依赖: F.mapArrow.mapIso, mapArrow, mapIso
-/
lemma isoClosure_strictMap_le (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.strictMap F <= (P.strictMap F).isoClosure :=
  fun _ _ _ ⟨⟨_, _, _, hf, ⟨i⟩⟩⟩ => ⟨_, _, _, ⟨hf⟩, ⟨F.mapArrow.mapIso i⟩⟩

/--
lemma `map_eq_isoClosure` / 引理 `map_eq_isoClosure`

English:
lemma map_eq_isoClosure
  given: (W : MorphismProperty C) (F : C ⥤ D)
  proof: by
  ext
  refine ⟨fun ⟨_, _, f, hf, hf'⟩ => ⟨_, _, _, ⟨hf⟩, hf'⟩, fun ⟨_, _, f, hf, hf'⟩ => ?_⟩
  obtain ⟨hf⟩ := hf
  exact ⟨_, _, _, hf, hf'⟩

中文:
引理 map_eq_isoClosure
  条件: (W : MorphismProperty C) (F : C ⥤ D)
  证明: by
  ext
  refine ⟨fun ⟨_, _, f, hf, hf'⟩ => ⟨_, _, _, ⟨hf⟩, hf'⟩, fun ⟨_, _, f, hf, hf'⟩ => ?_⟩
  obtain ⟨hf⟩ := hf
  exact ⟨_, _, _, hf, hf'⟩
-/
lemma map_eq_isoClosure (W : MorphismProperty C) (F : C ⥤ D) :
    W.map F = (W.strictMap F).isoClosure := by
  ext
  refine ⟨fun ⟨_, _, f, hf, hf'⟩ => ⟨_, _, _, ⟨hf⟩, hf'⟩, fun ⟨_, _, f, hf, hf'⟩ => ?_⟩
  obtain ⟨hf⟩ := hf
  exact ⟨_, _, _, hf, hf'⟩

/--
Instance `map_respectsIso` / 实例 `map_respectsIso`

English:
instance map_respectsIso
  signature: (P : MorphismProperty C) (F : C ⥤ D)
  body: by
  rw [map_eq_isoClosure]
  infer_instance

中文:
实例 map_respectsIso
  签名: (P : MorphismProperty C) (F : C ⥤ D)
  定义体: by
  rw [map_eq_isoClosure]
  infer_instance

Depends on / 依赖: infer_instance, map_eq_isoClosure
-/
instance map_respectsIso (P : MorphismProperty C) (F : C ⥤ D) :
    (P.map F).RespectsIso := by
  rw [map_eq_isoClosure]
  infer_instance

/--
lemma `map_le_iff` / 引理 `map_le_iff`

English:
lemma map_le_iff
  given: (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q]
  proof: by
  rw [map_eq_isoClosure]; rw [isoClosure_le_iff]; rw [strictMap_le_iff_le_inverseImage]

@[simp]

中文:
引理 map_le_iff
  条件: (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q]
  证明: by
  rw [map_eq_isoClosure]; rw [isoClosure_le_iff]; rw [strictMap_le_iff_le_inverseImage]

@[simp]

Depends on / 依赖: isoClosure_le_iff, map_eq_isoClosure, strictMap_le_iff_le_inverseImage
-/
lemma map_le_iff (P : MorphismProperty C) {F : C ⥤ D} (Q : MorphismProperty D) [RespectsIso Q] :
    P.map F <= Q ↔ P <= Q.inverseImage F := by
  rw [map_eq_isoClosure]; rw [isoClosure_le_iff]; rw [strictMap_le_iff_le_inverseImage]

@[simp]
/--
lemma `map_isoClosure` / 引理 `map_isoClosure`

English:
lemma map_isoClosure
  given: (P : MorphismProperty C) (F : C ⥤ D)
  proof: by
  apply le_antisymm
  · rw [map_eq_isoClosure, map_eq_isoClosure, isoClosure_le_iff]
    exact isoClosure_strictMap_le _ _
  · exact monotone_map _ (le_isoClosure P)

中文:
引理 map_isoClosure
  条件: (P : MorphismProperty C) (F : C ⥤ D)
  证明: by
  apply le_antisymm
  · rw [map_eq_isoClosure, map_eq_isoClosure, isoClosure_le_iff]
    exact isoClosure_strictMap_le _ _
  · exact monotone_map _ (le_isoClosure P)

Depends on / 依赖: isoClosure_le_iff, isoClosure_strictMap_le, le_antisymm, le_isoClosure, map_eq_isoClosure, monotone_map
-/
lemma map_isoClosure (P : MorphismProperty C) (F : C ⥤ D) :
    P.isoClosure.map F = P.map F := by
  apply le_antisymm
  · rw [map_eq_isoClosure, map_eq_isoClosure, isoClosure_le_iff]
    exact isoClosure_strictMap_le _ _
  · exact monotone_map _ (le_isoClosure P)

/--
lemma `map_id_eq_isoClosure` / 引理 `map_id_eq_isoClosure`

English:
lemma map_id_eq_isoClosure
  given: (P : MorphismProperty C)
  proof: rfl

中文:
引理 map_id_eq_isoClosure
  条件: (P : MorphismProperty C)
  证明: rfl
-/
lemma map_id_eq_isoClosure (P : MorphismProperty C) :
    P.map (𝟭 _) = P.isoClosure := rfl

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  given: (P : MorphismProperty C) [RespectsIso P]
  proof: by
  rw [map_id_eq_isoClosure]; rw [P.isoClosure_eq_self]

@[simp]

中文:
引理 map_id
  条件: (P : MorphismProperty C) [RespectsIso P]
  证明: by
  rw [map_id_eq_isoClosure]; rw [P.isoClosure_eq_self]

@[simp]

Depends on / 依赖: P.isoClosure_eq_self, isoClosure_eq_self, map_id_eq_isoClosure
-/
lemma map_id (P : MorphismProperty C) [RespectsIso P] :
    P.map (𝟭 _) = P := by
  rw [map_id_eq_isoClosure]; rw [P.isoClosure_eq_self]

@[simp]
/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E)
  proof: by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

中文:
引理 map_map
  条件: (P : MorphismProperty C) (F : C ⥤ D) {E : 类型} [范畴* E] (G : D ⥤ E)
  证明: by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

Depends on / 依赖: G.mapArrow.mapIso, le_antisymm, mapArrow, mapIso, map_le_iff, map_mem_map
-/
lemma map_map (P : MorphismProperty C) (F : C ⥤ D) {E : Type*} [Category* E] (G : D ⥤ E) :
    (P.map F).map G = P.map (F ⋙ G) := by
  apply le_antisymm
  · rw [map_le_iff]
    intro X Y f ⟨X', Y', f', hf', ⟨e⟩⟩
    exact ⟨X', Y', f', hf', ⟨G.mapArrow.mapIso e⟩⟩
  · rw [map_le_iff]
    intro X Y f hf
    exact map_mem_map _ _ _ (map_mem_map _ _ _ hf)

/--
Instance `RespectsIso.inverseImage` / 实例 `RespectsIso.inverseImage`

English:
instance RespectsIso.inverseImage
  signature: (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D)
  body: by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf

中文:
实例 RespectsIso.inverseImage
  签名: (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D)
  定义体: by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf

Depends on / 依赖: MorphismProperty, MorphismProperty.inverseImage, cancel_left_of_respectsIso, cancel_right_of_respectsIso, inverseImage, postcomp
-/
instance RespectsIso.inverseImage (P : MorphismProperty D) [RespectsIso P] (F : C ⥤ D) :
    RespectsIso (P.inverseImage F) where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_left_of_respectsIso] using hf
  postcomp {X Y Z} e (he : IsIso e) f hf := by
    simpa [MorphismProperty.inverseImage, cancel_right_of_respectsIso] using hf

/--
lemma `map_eq_of_iso` / 引理 `map_eq_of_iso`

English:
lemma map_eq_of_iso
  given: (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
  proof: by
  revert F G e
  suffices forall {F G : C ⥤ D} (_ : F ≅ G), P.map F <= P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

中文:
引理 map_eq_of_iso
  条件: (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G)
  证明: by
  revert F G e
  suffices forall {F G : C ⥤ D} (_ : F ≅ G), P.map F <= P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

Depends on / 依赖: Arrow.mk, Functor, Functor.mapArrowFunctor, P.map, e.symm, le_antisymm, mapArrowFunctor, mapIso, revert
-/
lemma map_eq_of_iso (P : MorphismProperty C) {F G : C ⥤ D} (e : F ≅ G) :
    P.map F = P.map G := by
  revert F G e
  suffices forall {F G : C ⥤ D} (_ : F ≅ G), P.map F <= P.map G from
    fun F G e => le_antisymm (this e) (this e.symm)
  intro F G e X Y f ⟨X', Y', f', hf', ⟨e'⟩⟩
  exact ⟨X', Y', f', hf', ⟨((Functor.mapArrowFunctor _ _).mapIso e.symm).app (Arrow.mk f') ≪≫ e'⟩⟩

/--
lemma `map_inverseImage_le` / 引理 `map_inverseImage_le`

English:
lemma map_inverseImage_le
  given: (P : MorphismProperty D) (F : C ⥤ D)
  proof: fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

中文:
引理 map_inverseImage_le
  条件: (P : MorphismProperty D) (F : C ⥤ D)
  证明: fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

Depends on / 依赖: F.map
-/
lemma map_inverseImage_le (P : MorphismProperty D) (F : C ⥤ D) :
    (P.inverseImage F).map F <= P.isoClosure :=
  fun _ _ _ ⟨_, _, f, hf, ⟨e⟩⟩ => ⟨_, _, F.map f, hf, ⟨e⟩⟩

/--
lemma `inverseImage_equivalence_inverse_eq_map_functor` / 引理 `inverseImage_equivalence_inverse_eq_map_functor`

English:
lemma inverseImage_equivalence_inverse_eq_map_functor
  proof: by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

中文:
引理 inverseImage_equivalence_inverse_eq_map_functor
  证明: by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

Depends on / 依赖: Arrow.mk, E.counitIso, E.unitIso.symm, Functor, Functor.mapArrowFunctor, P.arrow_mk_iso_iff, arrow_mk_iso_iff, counitIso, le_antisymm, mapArrowFunctor, mapIso, map_le_iff, unitIso
-/
lemma inverseImage_equivalence_inverse_eq_map_functor
    (P : MorphismProperty D) [RespectsIso P] (E : C ≌ D) :
    P.inverseImage E.functor = P.map E.inverse := by
  apply le_antisymm
  · intro X Y f hf
    refine ⟨_, _, _, hf, ⟨?_⟩⟩
    exact ((Functor.mapArrowFunctor _ _).mapIso E.unitIso.symm).app (Arrow.mk f)
  · rw [map_le_iff]
    intro X Y f hf
    exact (P.arrow_mk_iso_iff
      (((Functor.mapArrowFunctor _ _).mapIso E.counitIso).app (Arrow.mk f))).2 hf

/--
lemma `inverseImage_equivalence_functor_eq_map_inverse` / 引理 `inverseImage_equivalence_functor_eq_map_inverse`

English:
lemma inverseImage_equivalence_functor_eq_map_inverse
  proof: inverseImage_equivalence_inverse_eq_map_functor Q E.symm

中文:
引理 inverseImage_equivalence_functor_eq_map_inverse
  证明: inverseImage_equivalence_inverse_eq_map_functor Q E.symm

Depends on / 依赖: E.symm, inverseImage_equivalence_inverse_eq_map_functor
-/
lemma inverseImage_equivalence_functor_eq_map_inverse
    (Q : MorphismProperty C) [RespectsIso Q] (E : C ≌ D) :
    Q.inverseImage E.inverse = Q.map E.functor :=
  inverseImage_equivalence_inverse_eq_map_functor Q E.symm

/--
lemma `map_inverseImage_eq_of_isEquivalence` / 引理 `map_inverseImage_eq_of_isEquivalence`

English:
lemma map_inverseImage_eq_of_isEquivalence
  proof: by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

中文:
引理 map_inverseImage_eq_of_isEquivalence
  证明: by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

Depends on / 依赖: F.asEquivalence, F.asEquivalence.counitIso, P.inverseImage_equivalence_inverse_eq_map_functor, P.map_eq_of_iso, asEquivalence, counitIso, inverseImage_equivalence_inverse_eq_map_functor, map_eq_of_iso, map_id, map_map
-/
lemma map_inverseImage_eq_of_isEquivalence
    (P : MorphismProperty D) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.inverseImage F).map F = P := by
  erw [P.inverseImage_equivalence_inverse_eq_map_functor F.asEquivalence, map_map,
    P.map_eq_of_iso F.asEquivalence.counitIso, map_id]

/--
lemma `inverseImage_map_eq_of_isEquivalence` / 引理 `inverseImage_map_eq_of_isEquivalence`

English:
lemma inverseImage_map_eq_of_isEquivalence
  proof: by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

中文:
引理 inverseImage_map_eq_of_isEquivalence
  证明: by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

Depends on / 依赖: F.asEquivalence, F.asEquivalence.unitIso.symm, P.map, P.map_eq_of_iso, SmallCategory, asEquivalence, inverseImage_equivalence_inverse_eq_map_functor, map_eq_of_iso, map_id, map_map, unitIso, wellPowered_of_smallCategory
-/
lemma inverseImage_map_eq_of_isEquivalence
    (P : MorphismProperty C) [P.RespectsIso] (F : C ⥤ D) [F.IsEquivalence] :
    (P.map F).inverseImage F = P := by
  erw [((P.map F).inverseImage_equivalence_inverse_eq_map_functor (F.asEquivalence)), map_map,
    P.map_eq_of_iso F.asEquivalence.unitIso.symm, map_id]

end

end

section

variable {C}
variable {X Y : C} (f : X ⟶ Y)

@[simp]
/--
theorem `isomorphisms.iff` / 定理 `isomorphisms.iff`

English:
theorem isomorphisms.iff
  statement: (isomorphisms C) f ↔ IsIso f
  proof: by rfl

@[simp]

中文:
定理 isomorphisms.iff
  结论: (isomorphisms C) f ↔ 是同构 f
  证明: by rfl

@[simp]
-/
theorem isomorphisms.iff : (isomorphisms C) f ↔ IsIso f := by rfl

@[simp]
/--
theorem `monomorphisms.iff` / 定理 `monomorphisms.iff`

English:
theorem monomorphisms.iff
  statement: (monomorphisms C) f ↔ Mono f
  proof: by rfl

@[simp]

中文:
定理 monomorphisms.iff
  结论: (monomorphisms C) f ↔ 单态射 f
  证明: by rfl

@[simp]
-/
theorem monomorphisms.iff : (monomorphisms C) f ↔ Mono f := by rfl

@[simp]
/--
theorem `epimorphisms.iff` / 定理 `epimorphisms.iff`

English:
theorem epimorphisms.iff
  statement: (epimorphisms C) f ↔ Epi f
  proof: by rfl

中文:
定理 epimorphisms.iff
  结论: (epimorphisms C) f ↔ 满态射 f
  证明: by rfl
-/
theorem epimorphisms.iff : (epimorphisms C) f ↔ Epi f := by rfl

/--
theorem `isomorphisms.infer_property` / 定理 `isomorphisms.infer_property`

English:
theorem isomorphisms.infer_property
  given: [hf : IsIso f]
  statement: (isomorphisms C) f
  proof: hf

中文:
定理 isomorphisms.infer_property
  条件: [hf : 是同构 f]
  结论: (isomorphisms C) f
  证明: hf
-/
theorem isomorphisms.infer_property [hf : IsIso f] : (isomorphisms C) f :=
  hf

/--
theorem `monomorphisms.infer_property` / 定理 `monomorphisms.infer_property`

English:
theorem monomorphisms.infer_property
  given: [hf : Mono f]
  statement: (monomorphisms C) f
  proof: hf

中文:
定理 monomorphisms.infer_property
  条件: [hf : 单态射 f]
  结论: (monomorphisms C) f
  证明: hf
-/
theorem monomorphisms.infer_property [hf : Mono f] : (monomorphisms C) f :=
  hf

/--
theorem `epimorphisms.infer_property` / 定理 `epimorphisms.infer_property`

English:
theorem epimorphisms.infer_property
  given: [hf : Epi f]
  statement: (epimorphisms C) f
  proof: hf

中文:
定理 epimorphisms.infer_property
  条件: [hf : 满态射 f]
  结论: (epimorphisms C) f
  证明: hf
-/
theorem epimorphisms.infer_property [hf : Epi f] : (epimorphisms C) f :=
  hf

end

@[deprecated "Use `op_isomorphisms _` instead." (since := "2026-01-18")]
/--
lemma `isomorphisms_op` / 引理 `isomorphisms_op`

English:
lemma isomorphisms_op
  statement: (isomorphisms C).op = isomorphisms Cᵒᵖ
  proof: op_isomorphisms _

中文:
引理 isomorphisms_op
  结论: (isomorphisms C).op = isomorphisms Cᵒᵖ
  证明: op_isomorphisms _

Depends on / 依赖: op_isomorphisms
-/
lemma isomorphisms_op : (isomorphisms C).op = isomorphisms Cᵒᵖ := op_isomorphisms _

/--
Instance `RespectsIso.monomorphisms` / 实例 `RespectsIso.monomorphisms`

English:
instance RespectsIso.monomorphisms
  signature: : RespectsIso (monomorphisms C)
  body: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

中文:
实例 RespectsIso.monomorphisms
  签名: : RespectsIso (monomorphisms C)
  定义体: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

Depends on / 依赖: RespectsIso, RespectsIso.mk, mono_comp, monomorphisms, monomorphisms.iff
-/
instance RespectsIso.monomorphisms : RespectsIso (monomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [monomorphisms.iff]
      intro
      apply mono_comp

/--
Instance `RespectsIso.epimorphisms` / 实例 `RespectsIso.epimorphisms`

English:
instance RespectsIso.epimorphisms
  signature: : RespectsIso (epimorphisms C)
  body: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

中文:
实例 RespectsIso.epimorphisms
  签名: : RespectsIso (epimorphisms C)
  定义体: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

Depends on / 依赖: RespectsIso, RespectsIso.mk, epi_comp, epimorphisms, epimorphisms.iff
-/
instance RespectsIso.epimorphisms : RespectsIso (epimorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [epimorphisms.iff]
      intro
      apply epi_comp

/--
Instance `RespectsIso.isomorphisms` / 实例 `RespectsIso.isomorphisms`

English:
instance RespectsIso.isomorphisms
  signature: : RespectsIso (isomorphisms C)
  body: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

中文:
实例 RespectsIso.isomorphisms
  签名: : RespectsIso (isomorphisms C)
  定义体: by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

Depends on / 依赖: IsIso.comp_isIso, RespectsIso, RespectsIso.mk, comp_isIso, isomorphisms, isomorphisms.iff
-/
instance RespectsIso.isomorphisms : RespectsIso (isomorphisms C) := by
  apply RespectsIso.mk <;>
    · intro X Y Z e f
      simp only [isomorphisms.iff]
      intro
      exact IsIso.comp_isIso

end

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {C₁ C₂ : Type*} [CategoryStruct C₁] [CategoryStruct C₂]
  body: fun _ _ f => W₁ f.1 ∧ W₂ f.2

中文:
定义 乘积
  签名: {C₁ C₂ : 类型} [CategoryStruct C₁] [CategoryStruct C₂]
  定义体: fun _ _ f => W₁ f.1 ∧ W₂ f.2
-/
def prod {C₁ C₂ : Type*} [CategoryStruct C₁] [CategoryStruct C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂) :
    MorphismProperty (C₁ × C₂) :=
  fun _ _ f => W₁ f.1 ∧ W₂ f.2

/--
Definition of `pi` / `pi` 的定义

English:
definition pi
  signature: {J : Type w} {C : J -> Type u} [forall j, Category.{v} (C j)]
  body: fun _ _ f => forall j, (W j) (f j)

中文:
定义 pi
  签名: {J : 类型 w} {C : J -> 类型u} [对任意 j, 范畴.{v} (C j)]
  定义体: fun _ _ f => forall j, (W j) (f j)
-/
def pi {J : Type w} {C : J -> Type u} [forall j, Category.{v} (C j)]
    (W : forall j, MorphismProperty (C j)) : MorphismProperty (forall j, C j) :=
  fun _ _ f => forall j, (W j) (f j)

variable {C} [Category.{v} C]

/--
Definition of `functorCategory` / `functorCategory` 的定义

English:
definition functorCategory
  signature: (W : MorphismProperty C) (J : Type*) [Category* J]
  body: fun _ _ f => forall (j : J), W (f.app j)

中文:
定义 functorCategory
  签名: (W : MorphismProperty C) (J : 类型) [范畴* J]
  定义体: fun _ _ f => forall (j : J), W (f.app j)

Depends on / 依赖: f.app
-/
def functorCategory (W : MorphismProperty C) (J : Type*) [Category* J] :
    MorphismProperty (J ⥤ C) :=
  fun _ _ f => forall (j : J), W (f.app j)

/--
Definition of `arrow` / `arrow` 的定义

English:
definition arrow
  signature: (W : MorphismProperty C)
  body: fun _ _ f => W f.left ∧ W f.right

中文:
定义 arrow
  签名: (W : MorphismProperty C)
  定义体: fun _ _ f => W f.left ∧ W f.right

Depends on / 依赖: f.left, f.right
-/
def arrow (W : MorphismProperty C) :
    MorphismProperty (Arrow C) :=
  fun _ _ f => W f.left ∧ W f.right

instance (W : MorphismProperty C) [W.RespectsIso] : W.arrow.RespectsIso where
  precomp f (_ : IsIso f) _ h :=
    ⟨RespectsIso.precomp _ _ _ h.1, RespectsIso.precomp _ _ _ h.2⟩
  postcomp f (_ : IsIso f) _ h :=
    ⟨RespectsIso.postcomp _ _ _ h.1, RespectsIso.postcomp _ _ _ h.2⟩

end MorphismProperty

namespace NatTrans

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_app_iff_of_iso` / 引理 `isIso_app_iff_of_iso`

English:
lemma isIso_app_iff_of_iso
  given: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y)
  proof: (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

中文:
引理 isIso_app_iff_of_iso
  条件: {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y)
  证明: (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

Depends on / 依赖: Arrow.isoMk, F.mapIso, G.mapIso, MorphismProperty, MorphismProperty.isomorphisms, arrow_mk_iso_iff, isomorphisms, mapIso
-/
lemma isIso_app_iff_of_iso {F G : C ⥤ D} (α : F ⟶ G) {X Y : C} (e : X ≅ Y) :
    IsIso (α.app X) ↔ IsIso (α.app Y) :=
  (MorphismProperty.isomorphisms D).arrow_mk_iso_iff
    (Arrow.isoMk (F.mapIso e) (G.mapIso e) (by simp))

end NatTrans

end CategoryTheory
