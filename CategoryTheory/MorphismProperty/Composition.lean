/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou, Aras Ergus
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Compatibilities of properties of morphisms with respect to composition

Given `P : MorphismProperty C`, we define the predicate `P.IsStableUnderComposition`
which means that `P f → P g → P (f ≫ g)`. We also introduce the type classes
`W.ContainsIdentities`, `W.IsMultiplicative`, and `W.HasTwoOutOfThreeProperty`.

-/

@[expose] public section


universe w v v' u u'

namespace CategoryTheory

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

variable (C) in
/--
Definition of `identities` / `identities` 的定义

English:
abbreviation identities
  signature: : MorphismProperty C
  body: .ofHoms fun X => 𝟙 X

中文:
缩写 identities
  签名: : MorphismProperty C
  定义体: .ofHoms fun X => 𝟙 X

Depends on / 依赖: ofHoms
-/
abbrev identities : MorphismProperty C :=
  .ofHoms fun X => 𝟙 X

/--
lemma `identities_op_iff` / 引理 `identities_op_iff`

English:
lemma identities_op_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: by
  obtain ⟨X⟩ := X
  obtain ⟨f⟩ := f
  dsimp
  exact ⟨fun ⟨_⟩ => ⟨_⟩, fun ⟨_⟩ => ⟨_⟩⟩

中文:
引理 identities_op_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: by
  obtain ⟨X⟩ := X
  obtain ⟨f⟩ := f
  dsimp
  exact ⟨fun ⟨_⟩ => ⟨_⟩, fun ⟨_⟩ => ⟨_⟩⟩
-/
lemma identities_op_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    identities Cᵒᵖ f ↔ identities C f.unop := by
  obtain ⟨X⟩ := X
  obtain ⟨f⟩ := f
  dsimp
  exact ⟨fun ⟨_⟩ => ⟨_⟩, fun ⟨_⟩ => ⟨_⟩⟩

/--
Definition of `ContainsIdentities` / `ContainsIdentities` 的定义

English:
class ContainsIdentities
  parameters: (W : MorphismProperty C)
  axioms and operations (1):
    - id_mem : forall (X : C), W (𝟙 X)

中文:
类 余ntainsIdentities
  参数: (W : MorphismProperty C)
  公理与运算 (1 个):
    - id_mem : 对任意 (X : C), W (𝟙 X)
-/
class ContainsIdentities (W : MorphismProperty C) : Prop where
  /-- for all `X : C`, the identity of `X` satisfies the morphism property -/
  id_mem : forall (X : C), W (𝟙 X)

/--
lemma `id_mem` / 引理 `id_mem`

English:
lemma id_mem
  given: (W : MorphismProperty C) [W.ContainsIdentities] (X : C)
  proof: ContainsIdentities.id_mem X

中文:
引理 id_mem
  条件: (W : MorphismProperty C) [W.余ntainsIdentities] (X : C)
  证明: ContainsIdentities.id_mem X

Depends on / 依赖: ContainsIdentities, ContainsIdentities.id_mem, id_mem
-/
lemma id_mem (W : MorphismProperty C) [W.ContainsIdentities] (X : C) :
    W (𝟙 X) := ContainsIdentities.id_mem X

namespace ContainsIdentities

/--
Instance `op` / 实例 `op`

English:
instance op
  signature: (W : MorphismProperty C) [W.ContainsIdentities]
  body: ⟨fun X => W.id_mem X.unop⟩

中文:
实例 op
  签名: (W : MorphismProperty C) [W.余ntainsIdentities]
  定义体: ⟨fun X => W.id_mem X.unop⟩

Depends on / 依赖: W.id_mem, X.unop, id_mem
-/
instance op (W : MorphismProperty C) [W.ContainsIdentities] :
    W.op.ContainsIdentities := ⟨fun X => W.id_mem X.unop⟩

/--
Instance `unop` / 实例 `unop`

English:
instance unop
  signature: (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities]
  body: ⟨fun X => W.id_mem (Opposite.op X)⟩

中文:
实例 unop
  签名: (W : MorphismProperty Cᵒᵖ) [W.余ntainsIdentities]
  定义体: ⟨fun X => W.id_mem (Opposite.op X)⟩

Depends on / 依赖: Opposite, Opposite.op, W.id_mem, id_mem
-/
instance unop (W : MorphismProperty Cᵒᵖ) [W.ContainsIdentities] :
    W.unop.ContainsIdentities := ⟨fun X => W.id_mem (Opposite.op X)⟩

/--
lemma `of_op` / 引理 `of_op`

English:
lemma of_op
  given: (W : MorphismProperty C) [W.op.ContainsIdentities]
  proof: (inferInstance : W.op.unop.ContainsIdentities)

中文:
引理 of_op
  条件: (W : MorphismProperty C) [W.op.余ntainsIdentities]
  证明: (inferInstance : W.op.unop.ContainsIdentities)

Depends on / 依赖: ContainsIdentities, W.op.unop.ContainsIdentities
-/
lemma of_op (W : MorphismProperty C) [W.op.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.op.unop.ContainsIdentities)

/--
lemma `of_unop` / 引理 `of_unop`

English:
lemma of_unop
  given: (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities]
  proof: (inferInstance : W.unop.op.ContainsIdentities)

中文:
引理 of_unop
  条件: (W : MorphismProperty Cᵒᵖ) [W.unop.余ntainsIdentities]
  证明: (inferInstance : W.unop.op.ContainsIdentities)

Depends on / 依赖: ContainsIdentities, W.unop.op.ContainsIdentities
-/
lemma of_unop (W : MorphismProperty Cᵒᵖ) [W.unop.ContainsIdentities] :
    W.ContainsIdentities := (inferInstance : W.unop.op.ContainsIdentities)

/--
lemma `eqToHom` / 引理 `eqToHom`

English:
lemma eqToHom
  given: (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x = y)
  proof: by
  subst h
  rw [eqToHom_refl]
  exact id_mem x

中文:
引理 eqToHom
  条件: (W : MorphismProperty C) [W.余ntainsIdentities] {x y : C} (h : x = y)
  证明: by
  subst h
  rw [eqToHom_refl]
  exact id_mem x

Depends on / 依赖: eqToHom_refl, id_mem
-/
lemma eqToHom (W : MorphismProperty C) [W.ContainsIdentities] {x y : C} (h : x = y) :
    W (eqToHom h) := by
  subst h
  rw [eqToHom_refl]
  exact id_mem x

/--
Instance `inverseImage` / 实例 `inverseImage`

English:
instance inverseImage
  signature: {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D)
  body: by simpa only [← F.map_id] using! P.id_mem (F.obj X)

中文:
实例 inverseImage
  签名: {P : MorphismProperty D} [P.余ntainsIdentities] (F : C ⥤ D)
  定义体: by simpa only [← F.map_id] using! P.id_mem (F.obj X)

Depends on / 依赖: F.map_id, F.obj, P.id_mem, id_mem, map_id
-/
instance inverseImage {P : MorphismProperty D} [P.ContainsIdentities] (F : C ⥤ D) :
    (P.inverseImage F).ContainsIdentities where
  id_mem X := by simpa only [← F.map_id] using! P.id_mem (F.obj X)

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities]
  body: ⟨P.id_mem X, Q.id_mem X⟩

中文:
实例 下确界
  签名: {P Q : MorphismProperty C} [P.余ntainsIdentities] [Q.余ntainsIdentities]
  定义体: ⟨P.id_mem X, Q.id_mem X⟩

Depends on / 依赖: P.id_mem, Q.id_mem, id_mem
-/
instance inf {P Q : MorphismProperty C} [P.ContainsIdentities] [Q.ContainsIdentities] :
    (P ⊓ Q).ContainsIdentities where
  id_mem X := ⟨P.id_mem X, Q.id_mem X⟩

/--
lemma `sInf` / 引理 `sInf`

English:
lemma sInf
  given: {W : Set (MorphismProperty C)} (h : forall W' in W, W'.ContainsIdentities)
  proof: (sInf_iff _ _).2 fun _ hW' => (h _ hW').id_mem _

中文:
引理 sInf
  条件: {W : 集合 (MorphismProperty C)} (h : 对任意 W' in W, W'.余ntainsIdentities)
  证明: (sInf_iff _ _).2 fun _ hW' => (h _ hW').id_mem _

Depends on / 依赖: id_mem, sInf_iff
-/
lemma sInf {W : Set (MorphismProperty C)} (h : forall W' in W, W'.ContainsIdentities) :
    (sInf W).ContainsIdentities where
  id_mem _ := (sInf_iff _ _).2 fun _ hW' => (h _ hW').id_mem _

/--
Instance `iInf` / 实例 `iInf`

English:
instance iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C}
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C}
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance iInf {ι : Type*} {W : ι -> MorphismProperty C}
    [forall i, (W i).ContainsIdentities] : (⨅ i, W i).ContainsIdentities := by
  rw [← sInf_range]
  exact sInf (by simpa)

/--
lemma `iff_identities_le` / 引理 `iff_identities_le`

English:
lemma iff_identities_le
  given: {W : MorphismProperty C}
  proof: ⟨fun _ => by intro _ _ _ ⟨_⟩; exact id_mem _, fun h => ⟨fun _ => h _ ⟨_⟩⟩⟩

中文:
引理 iff_identities_le
  条件: {W : MorphismProperty C}
  证明: ⟨fun _ => by intro _ _ _ ⟨_⟩; exact id_mem _, fun h => ⟨fun _ => h _ ⟨_⟩⟩⟩

Depends on / 依赖: id_mem
-/
lemma iff_identities_le {W : MorphismProperty C} :
    W.ContainsIdentities ↔ identities C <= W :=
  ⟨fun _ => by intro _ _ _ ⟨_⟩; exact id_mem _, fun h => ⟨fun _ => h _ ⟨_⟩⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (identities C).ContainsIdentities
  body: iff_identities_le.2 (by rfl)

中文:
实例 :
  签名: (identities C).余ntainsIdentities
  定义体: iff_identities_le.2 (by rfl)

Depends on / 依赖: iff_identities_le
-/
instance : (identities C).ContainsIdentities :=
  iff_identities_le.2 (by rfl)

end ContainsIdentities

/--
Instance `Prod.containsIdentities` / 实例 `Prod.containsIdentities`

English:
instance Prod.containsIdentities
  signature: {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
  body: ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

中文:
实例 积类型.containsIdentities
  签名: {C₁ C₂ : 类型} [范畴* C₁] [范畴* C₂]
  定义体: ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

Depends on / 依赖: id_mem
-/
instance Prod.containsIdentities {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    (W₁ : MorphismProperty C₁) (W₂ : MorphismProperty C₂)
    [W₁.ContainsIdentities] [W₂.ContainsIdentities] : (prod W₁ W₂).ContainsIdentities :=
  ⟨fun _ => ⟨W₁.id_mem _, W₂.id_mem _⟩⟩

/--
Instance `Pi.containsIdentities` / 实例 `Pi.containsIdentities`

English:
instance Pi.containsIdentities
  signature: {J : Type w} {C : J -> Type u}
  body: ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

中文:
实例 依赖函数类型.containsIdentities
  签名: {J : 类型 w} {C : J -> 类型u}
  定义体: ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

Depends on / 依赖: MorphismProperty, MorphismProperty.id_mem, id_mem
-/
instance Pi.containsIdentities {J : Type w} {C : J -> Type u}
    [forall j, Category.{v} (C j)] (W : forall j, MorphismProperty (C j)) [forall j, (W j).ContainsIdentities] :
    (pi W).ContainsIdentities :=
  ⟨fun _ _ => MorphismProperty.id_mem _ _⟩

/--
lemma `of_isIso` / 引理 `of_isIso`

English:
lemma of_isIso
  statement: (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
  proof: Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)

中文:
引理 of_isIso
  结论: (P : MorphismProperty C) [P.余ntainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
  证明: Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)

Depends on / 依赖: Category, Category.id_comp, P.id_mem, RespectsIso, RespectsIso.postcomp, id_comp, id_mem, postcomp
-/
lemma of_isIso (P : MorphismProperty C) [P.ContainsIdentities] [P.RespectsIso] {X Y : C} (f : X ⟶ Y)
    [IsIso f] : P f :=
  Category.id_comp f ▸ RespectsIso.postcomp P f (𝟙 X) (P.id_mem X)

/--
lemma `isomorphisms_le_of_containsIdentities` / 引理 `isomorphisms_le_of_containsIdentities`

English:
lemma isomorphisms_le_of_containsIdentities
  statement: (P : MorphismProperty C) [P.ContainsIdentities]
  proof: fun _ _ f (_ : IsIso f) => P.of_isIso f

中文:
引理 isomorphisms_le_of_containsIdentities
  结论: (P : MorphismProperty C) [P.余ntainsIdentities]
  证明: fun _ _ f (_ : IsIso f) => P.of_isIso f

Depends on / 依赖: P.of_isIso, of_isIso
-/
lemma isomorphisms_le_of_containsIdentities (P : MorphismProperty C) [P.ContainsIdentities]
    [P.RespectsIso] :
    isomorphisms C <= P := fun _ _ f (_ : IsIso f) => P.of_isIso f

/--
Definition of `IsStableUnderComposition` / `IsStableUnderComposition` 的定义

English:
class IsStableUnderComposition
  parameters: (P : MorphismProperty C)
  axioms and operations (1):
    - comp_mem({X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z)) : P f -> P g -> P (f ≫ g)

中文:
类 是StableUnderComposition
  参数: (P : MorphismProperty C)
  公理与运算 (1 个):
    - comp_mem({X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z)) : P f -> P g -> P (f ≫ g)
-/
class IsStableUnderComposition (P : MorphismProperty C) : Prop where
  comp_mem {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) : P f -> P g -> P (f ≫ g)

/--
lemma `comp_mem` / 引理 `comp_mem`

English:
lemma comp_mem
  statement: (W : MorphismProperty C) [W.IsStableUnderComposition]
  proof: IsStableUnderComposition.comp_mem f g hf hg

中文:
引理 comp_mem
  结论: (W : MorphismProperty C) [W.是StableUnderComposition]
  证明: IsStableUnderComposition.comp_mem f g hf hg

Depends on / 依赖: IsStableUnderComposition, IsStableUnderComposition.comp_mem, comp_mem
-/
lemma comp_mem (W : MorphismProperty C) [W.IsStableUnderComposition]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) (hg : W g) : W (f ≫ g) :=
  IsStableUnderComposition.comp_mem f g hf hg

instance (priority := 900) (W : MorphismProperty C) [W.IsStableUnderComposition] :
    W.Respects W where
  precomp _ hi _ hf := W.comp_mem _ _ hi hf
  postcomp _ hi _ hf := W.comp_mem _ _ hf hi

/--
Instance `IsStableUnderComposition.op` / 实例 `IsStableUnderComposition.op`

English:
instance IsStableUnderComposition.op
  signature: {P : MorphismProperty C} [P.IsStableUnderComposition]
  body: P.comp_mem g.unop f.unop hg hf

中文:
实例 是StableUnderComposition.op
  签名: {P : MorphismProperty C} [P.是StableUnderComposition]
  定义体: P.comp_mem g.unop f.unop hg hf

Depends on / 依赖: P.comp_mem, comp_mem, f.unop, g.unop
-/
instance IsStableUnderComposition.op {P : MorphismProperty C} [P.IsStableUnderComposition] :
    P.op.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.unop f.unop hg hf

/--
Instance `IsStableUnderComposition.unop` / 实例 `IsStableUnderComposition.unop`

English:
instance IsStableUnderComposition.unop
  signature: {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition]
  body: P.comp_mem g.op f.op hg hf

中文:
实例 是StableUnderComposition.unop
  签名: {P : MorphismProperty Cᵒᵖ} [P.是StableUnderComposition]
  定义体: P.comp_mem g.op f.op hg hf

Depends on / 依赖: P.comp_mem, comp_mem, f.op, g.op
-/
instance IsStableUnderComposition.unop {P : MorphismProperty Cᵒᵖ} [P.IsStableUnderComposition] :
    P.unop.IsStableUnderComposition where
  comp_mem f g hf hg := P.comp_mem g.op f.op hg hf

/--
Instance `IsStableUnderComposition.inf` / 实例 `IsStableUnderComposition.inf`

English:
instance IsStableUnderComposition.inf
  signature: {P Q : MorphismProperty C} [P.IsStableUnderComposition]
  body: ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩

中文:
实例 是StableUnderComposition.下确界
  签名: {P Q : MorphismProperty C} [P.是StableUnderComposition]
  定义体: ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩

Depends on / 依赖: P.comp_mem, Q.comp_mem, comp_mem, hf.left, hf.right, hg.left, hg.right
-/
instance IsStableUnderComposition.inf {P Q : MorphismProperty C} [P.IsStableUnderComposition]
    [Q.IsStableUnderComposition] :
    (P ⊓ Q).IsStableUnderComposition where
  comp_mem f g hf hg := ⟨P.comp_mem f g hf.left hg.left, Q.comp_mem f g hf.right hg.right⟩

/--
lemma `IsStableUnderComposition.sInf` / 引理 `IsStableUnderComposition.sInf`

English:
lemma IsStableUnderComposition.sInf
  statement: {W : Set (MorphismProperty C)}
  proof: by
    rw [sInf_iff] at hf hg ⊢
    exact fun W' hW' => (h W' hW').comp_mem _ _ (hf _ hW') (hg _ hW')

中文:
引理 是StableUnderComposition.sInf
  结论: {W : 集合 (MorphismProperty C)}
  证明: by
    rw [sInf_iff] at hf hg ⊢
    exact fun W' hW' => (h W' hW').comp_mem _ _ (hf _ hW') (hg _ hW')

Depends on / 依赖: comp_mem, sInf_iff
-/
lemma IsStableUnderComposition.sInf {W : Set (MorphismProperty C)}
    (h : forall W' in W, W'.IsStableUnderComposition) : (sInf W).IsStableUnderComposition where
  comp_mem f g hf hg := by
    rw [sInf_iff] at hf hg ⊢
    exact fun W' hW' => (h W' hW').comp_mem _ _ (hf _ hW') (hg _ hW')

/--
Instance `IsStableUnderComposition.iInf` / 实例 `IsStableUnderComposition.iInf`

English:
instance IsStableUnderComposition.iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C}
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 是StableUnderComposition.iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C}
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance IsStableUnderComposition.iInf {ι : Type*} {W : ι -> MorphismProperty C}
    [forall i, (W i).IsStableUnderComposition] : (⨅ i, W i).IsStableUnderComposition := by
  rw [← sInf_range]
  exact sInf (by simpa)

/--
Definition of `StableUnderInverse` / `StableUnderInverse` 的定义

English:
definition StableUnderInverse
  signature: (P : MorphismProperty C)
  body: forall ⦃X Y⦄ (e : X ≅ Y), P e.hom -> P e.inv

中文:
定义 StableUnderInverse
  签名: (P : MorphismProperty C)
  定义体: forall ⦃X Y⦄ (e : X ≅ Y), P e.hom -> P e.inv

Depends on / 依赖: e.hom, e.inv
-/
def StableUnderInverse (P : MorphismProperty C) : Prop :=
  forall ⦃X Y⦄ (e : X ≅ Y), P e.hom -> P e.inv

/--
theorem `StableUnderInverse.op` / 定理 `StableUnderInverse.op`

English:
theorem StableUnderInverse.op
  given: {P : MorphismProperty C} (h : StableUnderInverse P)
  proof: fun _ _ e he => h e.unop he

中文:
定理 StableUnderInverse.op
  条件: {P : MorphismProperty C} (h : StableUnderInverse P)
  证明: fun _ _ e he => h e.unop he

Depends on / 依赖: e.unop
-/
theorem StableUnderInverse.op {P : MorphismProperty C} (h : StableUnderInverse P) :
    StableUnderInverse P.op := fun _ _ e he => h e.unop he

/--
theorem `StableUnderInverse.unop` / 定理 `StableUnderInverse.unop`

English:
theorem StableUnderInverse.unop
  given: {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P)
  proof: fun _ _ e he => h e.op he

中文:
定理 StableUnderInverse.unop
  条件: {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P)
  证明: fun _ _ e he => h e.op he

Depends on / 依赖: e.op
-/
theorem StableUnderInverse.unop {P : MorphismProperty Cᵒᵖ} (h : StableUnderInverse P) :
    StableUnderInverse P.unop := fun _ _ e he => h e.op he

/--
theorem `respectsIso_of_isStableUnderComposition` / 定理 `respectsIso_of_isStableUnderComposition`

English:
theorem respectsIso_of_isStableUnderComposition
  statement: {P : MorphismProperty C}
  proof: RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))

中文:
定理 respectsIso_of_isStableUnderComposition
  结论: {P : MorphismProperty C}
  证明: RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))

Depends on / 依赖: RespectsIso, RespectsIso.mk
-/
theorem respectsIso_of_isStableUnderComposition {P : MorphismProperty C}
    [P.IsStableUnderComposition] (hP : isomorphisms C <= P) :
    RespectsIso P := RespectsIso.mk _
  (fun _ _ hf => P.comp_mem _ _ (hP _ (isomorphisms.infer_property _)) hf)
    (fun _ _ hf => P.comp_mem _ _ hf (hP _ (isomorphisms.infer_property _)))

/--
Instance `IsStableUnderComposition.inverseImage` / 实例 `IsStableUnderComposition.inverseImage`

English:
instance IsStableUnderComposition.inverseImage
  signature: {P : MorphismProperty D} [P.IsStableUnderComposition]
  body: by simpa only [← F.map_comp] using! P.comp_mem _ _ hf hg

中文:
实例 是StableUnderComposition.inverseImage
  签名: {P : MorphismProperty D} [P.是StableUnderComposition]
  定义体: by simpa only [← F.map_comp] using! P.comp_mem _ _ hf hg

Depends on / 依赖: F.map_comp, P.comp_mem, comp_mem, map_comp
-/
instance IsStableUnderComposition.inverseImage {P : MorphismProperty D} [P.IsStableUnderComposition]
    (F : C ⥤ D) : (P.inverseImage F).IsStableUnderComposition where
  comp_mem f g hf hg := by simpa only [← F.map_comp] using! P.comp_mem _ _ hf hg

/-- Given `app : Π X, F₁.obj X ⟶ F₂.obj X` where `F₁` and `F₂` are two functors,
this is the `MorphismProperty C` satisfied by the morphisms in `C` with respect
to which `app` is natural. -/
@[simp]
/--
Definition of `naturalityProperty` / `naturalityProperty` 的定义

English:
definition naturalityProperty
  signature: {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X)
  body: fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

中文:
定义 naturalityProperty
  签名: {F₁ F₂ : C ⥤ D} (app : 对任意 X, F₁.obj X ⟶ F₂.obj X)
  定义体: fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f
-/
def naturalityProperty {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) : MorphismProperty C :=
  fun X Y f => F₁.map f ≫ app Y = app X ≫ F₂.map f

namespace naturalityProperty

/--
Instance `isStableUnderComposition` / 实例 `isStableUnderComposition`

English:
instance isStableUnderComposition
  signature: {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X)
  body: by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]

中文:
实例 isStableUnderComposition
  签名: {F₁ F₂ : C ⥤ D} (app : 对任意 X, F₁.obj X ⟶ F₂.obj X)
  定义体: by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]

Depends on / 依赖: Category, Category.assoc, Functor, Functor.map_comp, map_comp, naturalityProperty, slice_lhs
-/
instance isStableUnderComposition {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsStableUnderComposition where
  comp_mem f g hf hg := by
    simp only [naturalityProperty] at hf hg ⊢
    simp only [Functor.map_comp, Category.assoc, hg]
    slice_lhs 1 2 => rw [hf]
    rw [Category.assoc]

/--
theorem `stableUnderInverse` / 定理 `stableUnderInverse`

English:
theorem stableUnderInverse
  given: {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X)
  proof: fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

中文:
定理 stableUnderInverse
  条件: {F₁ F₂ : C ⥤ D} (app : 对任意 X, F₁.obj X ⟶ F₂.obj X)
  证明: fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Category.id_comp, Functor, Functor.map_id, cancel_epi, comp_id, e.hom, e.hom_inv_id, hom_inv_id, id_comp, map_comp, map_comp_assoc, map_id, naturalityProperty, slice_rhs
-/
theorem stableUnderInverse {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).StableUnderInverse := fun X Y e he => by
  simp only [naturalityProperty] at he ⊢
  rw [← cancel_epi (F₁.map e.hom)]
  slice_rhs 1 2 => rw [he]
  simp only [Category.assoc, ← F₁.map_comp_assoc, ← F₂.map_comp, e.hom_inv_id, Functor.map_id,
    Category.id_comp, Category.comp_id]

end naturalityProperty

/--
Definition of `IsMultiplicative` / `IsMultiplicative` 的定义

English:
class IsMultiplicative
  parameters: (W : MorphismProperty C)
  extends: W.ContainsIdentities, W.IsStableUnderComposition
  (no additional axioms)

中文:
类 是Multiplicative
  参数: (W : MorphismProperty C)
  继承: W.余ntainsIdentities, W.是StableUnderComposition
  (无附加公理)

Depends on / 依赖: triangleMorphismId
-/
class IsMultiplicative (W : MorphismProperty C) : Prop
    extends W.ContainsIdentities, W.IsStableUnderComposition

namespace IsMultiplicative

/--
Instance `op` / 实例 `op`

English:
instance op
  signature: (W : MorphismProperty C) [IsMultiplicative W]
  body: W.comp_mem g.unop f.unop hg hf

中文:
实例 op
  签名: (W : MorphismProperty C) [是Multiplicative W]
  定义体: W.comp_mem g.unop f.unop hg hf

Depends on / 依赖: W.comp_mem, comp_mem, f.unop, g.unop
-/
instance op (W : MorphismProperty C) [IsMultiplicative W] : IsMultiplicative W.op where
  comp_mem f g hf hg := W.comp_mem g.unop f.unop hg hf

/--
Instance `unop` / 实例 `unop`

English:
instance unop
  signature: (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W]
  body: W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

中文:
实例 unop
  签名: (W : MorphismProperty Cᵒᵖ) [是Multiplicative W]
  定义体: W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

Depends on / 依赖: W.id_mem, id_mem
-/
instance unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W] : IsMultiplicative W.unop where
  id_mem _ := W.id_mem _
  comp_mem f g hf hg := W.comp_mem g.op f.op hg hf

/--
lemma `of_op` / 引理 `of_op`

English:
lemma of_op
  given: (W : MorphismProperty C) [IsMultiplicative W.op]
  statement: IsMultiplicative W
  proof: inferInstanceAs IsMultiplicative W.op.unop

中文:
引理 of_op
  条件: (W : MorphismProperty C) [是Multiplicative W.op]
  结论: 是Multiplicative W
  证明: inferInstanceAs IsMultiplicative W.op.unop

Depends on / 依赖: IsMultiplicative, W.op.unop
-/
lemma of_op (W : MorphismProperty C) [IsMultiplicative W.op] : IsMultiplicative W :=
inferInstanceAs IsMultiplicative W.op.unop

/--
lemma `of_unop` / 引理 `of_unop`

English:
lemma of_unop
  given: (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop]
  statement: IsMultiplicative W
  proof: inferInstanceAs IsMultiplicative W.unop.op

中文:
引理 of_unop
  条件: (W : MorphismProperty Cᵒᵖ) [是Multiplicative W.unop]
  结论: 是Multiplicative W
  证明: inferInstanceAs IsMultiplicative W.unop.op

Depends on / 依赖: IsMultiplicative, W.unop.op
-/
lemma of_unop (W : MorphismProperty Cᵒᵖ) [IsMultiplicative W.unop] : IsMultiplicative W :=
inferInstanceAs IsMultiplicative W.unop.op

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MorphismProperty.IsMultiplicative (⊤ : MorphismProperty C)
  body: trivial
  id_mem _ := trivial

中文:
实例 :
  签名: MorphismProperty.是Multiplicative (⊤ : MorphismProperty C)
  定义体: trivial
  id_mem _ := trivial
-/
instance : MorphismProperty.IsMultiplicative (⊤ : MorphismProperty C) where
  comp_mem _ _ _ _ := trivial
  id_mem _ := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isomorphisms C).IsMultiplicative
  body: isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance

中文:
实例 :
  签名: (isomorphisms C).是Multiplicative
  定义体: isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance

Depends on / 依赖: infer_property, isomorphisms, isomorphisms.infer_property
-/
instance : (isomorphisms C).IsMultiplicative where
  id_mem _ := isomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [isomorphisms.iff] at hf hg ⊢
    infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (monomorphisms C).IsMultiplicative
  body: monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp

中文:
实例 :
  签名: (monomorphisms C).是Multiplicative
  定义体: monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp

Depends on / 依赖: infer_property, monomorphisms, monomorphisms.infer_property
-/
instance : (monomorphisms C).IsMultiplicative where
  id_mem _ := monomorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [monomorphisms.iff] at hf hg ⊢
    apply mono_comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (epimorphisms C).IsMultiplicative
  body: epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp

中文:
实例 :
  签名: (epimorphisms C).是Multiplicative
  定义体: epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp

Depends on / 依赖: epimorphisms, epimorphisms.infer_property, infer_property
-/
instance : (epimorphisms C).IsMultiplicative where
  id_mem _ := epimorphisms.infer_property _
  comp_mem f g hf hg := by
    rw [epimorphisms.iff] at hf hg ⊢
    apply epi_comp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (identities C).IsMultiplicative
  body: by
    rintro _ _ _ _ _ ⟨_⟩ ⟨_⟩
    simp only [Category.comp_id]
    constructor

中文:
实例 :
  签名: (identities C).是Multiplicative
  定义体: by
    rintro _ _ _ _ _ ⟨_⟩ ⟨_⟩
    simp only [Category.comp_id]
    constructor

Depends on / 依赖: Category, Category.comp_id, comp_id
-/
instance : (identities C).IsMultiplicative where
  comp_mem := by
    rintro _ _ _ _ _ ⟨_⟩ ⟨_⟩
    simp only [Category.comp_id]
    constructor

instance {P : MorphismProperty D} [P.IsMultiplicative] (F : C ⥤ D) :
    (P.inverseImage F).IsMultiplicative where

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: {P Q : MorphismProperty C} [P.IsMultiplicative] [Q.IsMultiplicative]

中文:
实例 下确界
  签名: {P Q : MorphismProperty C} [P.是Multiplicative] [Q.是Multiplicative]
-/
instance inf {P Q : MorphismProperty C} [P.IsMultiplicative] [Q.IsMultiplicative] :
    (P ⊓ Q).IsMultiplicative where

/--
lemma `sInf` / 引理 `sInf`

English:
lemma sInf
  given: {W : Set (MorphismProperty C)} (h : forall W' in W, W'.IsMultiplicative)
  proof: by
  have := ContainsIdentities.sInf (fun W' hW' => (h W' hW').toContainsIdentities)
  have := IsStableUnderComposition.sInf (fun W' hW' => (h W' hW').toIsStableUnderComposition)
  constructor

中文:
引理 sInf
  条件: {W : 集合 (MorphismProperty C)} (h : 对任意 W' in W, W'.是Multiplicative)
  证明: by
  have := ContainsIdentities.sInf (fun W' hW' => (h W' hW').toContainsIdentities)
  have := IsStableUnderComposition.sInf (fun W' hW' => (h W' hW').toIsStableUnderComposition)
  constructor

Depends on / 依赖: ContainsIdentities, ContainsIdentities.sInf, IsStableUnderComposition, IsStableUnderComposition.sInf, toContainsIdentities, toIsStableUnderComposition
-/
lemma sInf {W : Set (MorphismProperty C)} (h : forall W' in W, W'.IsMultiplicative) :
    (sInf W).IsMultiplicative := by
  have := ContainsIdentities.sInf (fun W' hW' => (h W' hW').toContainsIdentities)
  have := IsStableUnderComposition.sInf (fun W' hW' => (h W' hW').toIsStableUnderComposition)
  constructor

/--
Instance `iInf` / 实例 `iInf`

English:
instance iInf
  signature: {ι : Type*} {W : ι -> MorphismProperty C}
  body: by
  rw [← sInf_range]
  exact sInf (by simpa)

中文:
实例 iInf
  签名: {ι : 类型} {W : ι -> MorphismProperty C}
  定义体: by
  rw [← sInf_range]
  exact sInf (by simpa)

Depends on / 依赖: sInf_range
-/
instance iInf {ι : Type*} {W : ι -> MorphismProperty C}
    [forall i, (W i).IsMultiplicative] : (⨅ i, W i).IsMultiplicative := by
  rw [← sInf_range]
  exact sInf (by simpa)

/--
Instance `naturalityProperty` / 实例 `naturalityProperty`

English:
instance naturalityProperty
  signature: {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X)
  body: by simp

中文:
实例 naturalityProperty
  签名: {F₁ F₂ : C ⥤ D} (app : 对任意 X, F₁.obj X ⟶ F₂.obj X)
  定义体: by simp
-/
instance naturalityProperty {F₁ F₂ : C ⥤ D} (app : forall X, F₁.obj X ⟶ F₂.obj X) :
    (naturalityProperty app).IsMultiplicative where
  id_mem _ := by simp

end IsMultiplicative

/--
Inductive type `multiplicativeClosure` / 归纳类型 `multiplicativeClosure`

English:
inductive multiplicativeClosure
  parameters: (W : MorphismProperty C)
  constructors (3):
    - of: {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure W f
    - id: (x : C) : multiplicativeClosure W (𝟙 x)
    - comp_of: {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : multiplicativeClosure W f) (hg : W g) : multiplicativeClosure W (f ≫ g)

中文:
归纳类型 multiplicativeClosure
  参数: (W : MorphismProperty C)
  构造子 (3 个):
    - of: {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure W f
    - id: (x : C) : multiplicativeClosure W (𝟙 x)
    - comp_of: {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : multiplicativeClosure W f) (hg : W g) : multiplicativeClosure W (f ≫ g)
-/
inductive multiplicativeClosure (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure W f
  | id (x : C) : multiplicativeClosure W (𝟙 x)
  | comp_of {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : multiplicativeClosure W f) (hg : W g) :
    multiplicativeClosure W (f ≫ g)

/--
Inductive type `multiplicativeClosure'` / 归纳类型 `multiplicativeClosure'`

English:
inductive multiplicativeClosure'
  parameters: (W : MorphismProperty C)
  constructors (3):
    - of: {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure' W f
    - id: (x : C) : multiplicativeClosure' W (𝟙 x)
    - of_comp: {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : W f) (hg : multiplicativeClosure' W g) : multiplicativeClosure' W (f ≫ g)

中文:
归纳类型 multiplicativeClosure'
  参数: (W : MorphismProperty C)
  构造子 (3 个):
    - of: {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure' W f
    - id: (x : C) : multiplicativeClosure' W (𝟙 x)
    - of_comp: {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : W f) (hg : multiplicativeClosure' W g) : multiplicativeClosure' W (f ≫ g)
-/
inductive multiplicativeClosure' (W : MorphismProperty C) : MorphismProperty C
  | of {x y : C} (f : x ⟶ y) (hf : W f) : multiplicativeClosure' W f
  | id (x : C) : multiplicativeClosure' W (𝟙 x)
  | of_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) (hf : W f) (hg : multiplicativeClosure' W g) :
    multiplicativeClosure' W (f ≫ g)

variable (W : MorphismProperty C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative W.multiplicativeClosure
  body: .id x
  comp_mem f g hf hg := by
    induction hg with
    | of _ hf₀ => exact .comp_of f _ hf hf₀
    | id _ => rwa [Category.comp_id]
    | comp_of f' g hf' hg h_rec =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ f') g (h_rec f hf) hg

中文:
实例 :
  签名: 是Multiplicative W.multiplicativeClosure
  定义体: .id x
  comp_mem f g hf hg := by
    induction hg with
    | of _ hf₀ => exact .comp_of f _ hf hf₀
    | id _ => rwa [Category.comp_id]
    | comp_of f' g hf' hg h_rec =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ f') g (h_rec f hf) hg
-/
instance : IsMultiplicative W.multiplicativeClosure where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hg with
    | of _ hf₀ => exact .comp_of f _ hf hf₀
    | id _ => rwa [Category.comp_id]
    | comp_of f' g hf' hg h_rec =>
      rw [← Category.assoc]
      exact .comp_of (f ≫ f') g (h_rec f hf) hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMultiplicative W.multiplicativeClosure'
  body: .id x
  comp_mem f g hf hg := by
    induction hf with
    | of _ h => exact .of_comp _ g h hg
    | id _ => rwa [Category.id_comp]
    | of_comp g' f hg' hf h_rec =>
      rw [Category.assoc]
      exact .of_comp g' (f ≫ g) hg' (h_rec g hg)

中文:
实例 :
  签名: 是Multiplicative W.multiplicativeClosure'
  定义体: .id x
  comp_mem f g hf hg := by
    induction hf with
    | of _ h => exact .of_comp _ g h hg
    | id _ => rwa [Category.id_comp]
    | of_comp g' f hg' hf h_rec =>
      rw [Category.assoc]
      exact .of_comp g' (f ≫ g) hg' (h_rec g hg)
-/
instance : IsMultiplicative W.multiplicativeClosure' where
  id_mem x := .id x
  comp_mem f g hf hg := by
    induction hf with
    | of _ h => exact .of_comp _ g h hg
    | id _ => rwa [Category.id_comp]
    | of_comp g' f hg' hf h_rec =>
      rw [Category.assoc]
      exact .of_comp g' (f ≫ g) hg' (h_rec g hg)

/--
lemma `le_multiplicativeClosure` / 引理 `le_multiplicativeClosure`

English:
lemma le_multiplicativeClosure
  statement: W <= W.multiplicativeClosure
  proof: fun {_ _} _ hf => .of _ hf

中文:
引理 le_multiplicativeClosure
  结论: W <= W.multiplicativeClosure
  证明: fun {_ _} _ hf => .of _ hf
-/
lemma le_multiplicativeClosure : W <= W.multiplicativeClosure := fun {_ _} _ hf => .of _ hf

/-- The multiplicative closure of a multiplicative property is equal to itself. -/
@[simp]
/--
lemma `multiplicativeClosure_eq_self` / 引理 `multiplicativeClosure_eq_self`

English:
lemma multiplicativeClosure_eq_self
  given: [W.IsMultiplicative]
  statement: W.multiplicativeClosure = W
  proof: by
apply le_antisymm _ le_multiplicativeClosure W
  intro _ _ _ hf
  induction hf with
  | of _ hf₀ => exact hf₀
  | id x => exact W.id_mem x
  | comp_of _ _ _ hg hf => exact W.comp_mem _ _ hf hg

中文:
引理 multiplicativeClosure_eq_self
  条件: [W.是Multiplicative]
  结论: W.multiplicativeClosure = W
  证明: by
apply le_antisymm _ le_multiplicativeClosure W
  intro _ _ _ hf
  induction hf with
  | of _ hf₀ => exact hf₀
  | id x => exact W.id_mem x
  | comp_of _ _ _ hg hf => exact W.comp_mem _ _ hf hg

Depends on / 依赖: W.comp_mem, W.id_mem, comp_mem, comp_of, id_mem, le_antisymm, le_multiplicativeClosure
-/
lemma multiplicativeClosure_eq_self [W.IsMultiplicative] : W.multiplicativeClosure = W := by
apply le_antisymm _ le_multiplicativeClosure W
  intro _ _ _ hf
  induction hf with
  | of _ hf₀ => exact hf₀
  | id x => exact W.id_mem x
  | comp_of _ _ _ hg hf => exact W.comp_mem _ _ hf hg

/--
lemma `multiplicativeClosure_eq_self_iff` / 引理 `multiplicativeClosure_eq_self_iff`

English:
lemma multiplicativeClosure_eq_self_iff
  statement: W.multiplicativeClosure = W ↔ W.IsMultiplicative where
  proof: by
    rw [← h]
    infer_instance
  mpr h := multiplicativeClosure_eq_self W

中文:
引理 multiplicativeClosure_eq_self_iff
  结论: W.multiplicativeClosure = W ↔ W.是Multiplicative where
  证明: by
    rw [← h]
    infer_instance
  mpr h := multiplicativeClosure_eq_self W

Depends on / 依赖: infer_instance, multiplicativeClosure_eq_self
-/
lemma multiplicativeClosure_eq_self_iff : W.multiplicativeClosure = W ↔ W.IsMultiplicative where
  mp h := by
    rw [← h]
    infer_instance
  mpr h := multiplicativeClosure_eq_self W

/-- The multiplicative closure of `W` is the smallest multiplicative property greater than or equal
to `W`. -/
@[simp]
/--
lemma `multiplicativeClosure_le_iff` / 引理 `multiplicativeClosure_le_iff`

English:
lemma multiplicativeClosure_le_iff
  given: (W' : MorphismProperty C) [W'.IsMultiplicative]
  proof: le_multiplicativeClosure W
  mpr h := by
    intro _ _ _ hf
    induction hf with
    | of _ hf => exact h _ hf
    | id x => exact W'.id_mem _
    | comp_of _ _ _ hg hf => exact W'.comp_mem _ _ hf (h _ hg)

中文:
引理 multiplicativeClosure_le_iff
  条件: (W' : MorphismProperty C) [W'.是Multiplicative]
  证明: le_multiplicativeClosure W
  mpr h := by
    intro _ _ _ hf
    induction hf with
    | of _ hf => exact h _ hf
    | id x => exact W'.id_mem _
    | comp_of _ _ _ hg hf => exact W'.comp_mem _ _ hf (h _ hg)

Depends on / 依赖: le_multiplicativeClosure
-/
lemma multiplicativeClosure_le_iff (W' : MorphismProperty C) [W'.IsMultiplicative] :
    multiplicativeClosure W <= W' ↔ W <= W' where
.trans h mp h := le_multiplicativeClosure W
  mpr h := by
    intro _ _ _ hf
    induction hf with
    | of _ hf => exact h _ hf
    | id x => exact W'.id_mem _
    | comp_of _ _ _ hg hf => exact W'.comp_mem _ _ hf (h _ hg)

/--
lemma `multiplicativeClosure_monotone` / 引理 `multiplicativeClosure_monotone`

English:
lemma multiplicativeClosure_monotone
  proof: fun _ W' h => by simpa using h.trans W'.le_multiplicativeClosure

中文:
引理 multiplicativeClosure_monotone
  证明: fun _ W' h => by simpa using h.trans W'.le_multiplicativeClosure
-/
lemma multiplicativeClosure_monotone :
    Monotone (multiplicativeClosure (C := C)) :=
  fun _ W' h => by simpa using h.trans W'.le_multiplicativeClosure

/--
lemma `multiplicativeClosure_eq_multiplicativeClosure'` / 引理 `multiplicativeClosure_eq_multiplicativeClosure'`

English:
lemma multiplicativeClosure_eq_multiplicativeClosure'
  proof: le_antisymm
((multiplicativeClosure_le_iff _ _).mpr (fun _ _ f hf => .of f hf))
    fun x y f hf => by induction hf with
      | of _ h => exact .of _ h
      | id x => exact .id x
      | of_comp f g hf hg hr => exact W.multiplicativeClosure.comp_mem f g (.of f hf) hr

中文:
引理 multiplicativeClosure_eq_multiplicativeClosure'
  证明: le_antisymm
((multiplicativeClosure_le_iff _ _).mpr (fun _ _ f hf => .of f hf))
    fun x y f hf => by induction hf with
      | of _ h => exact .of _ h
      | id x => exact .id x
      | of_comp f g hf hg hr => exact W.multiplicativeClosure.comp_mem f g (.of f hf) hr

Depends on / 依赖: W.multiplicativeClosure.comp_mem, comp_mem, le_antisymm, multiplicativeClosure, multiplicativeClosure_le_iff, of_comp
-/
lemma multiplicativeClosure_eq_multiplicativeClosure' :
    W.multiplicativeClosure = W.multiplicativeClosure' :=
  le_antisymm
((multiplicativeClosure_le_iff _ _).mpr (fun _ _ f hf => .of f hf))
    fun x y f hf => by induction hf with
      | of _ h => exact .of _ h
      | id x => exact .id x
      | of_comp f g hf hg hr => exact W.multiplicativeClosure.comp_mem f g (.of f hf) hr

/--
lemma `strictMap_multiplicativeClosure_le` / 引理 `strictMap_multiplicativeClosure_le`

English:
lemma strictMap_multiplicativeClosure_le
  given: (F : C ⥤ D)
  proof: by
  intro _ _ f hf
  induction hf with | map hf
  induction hf with
  | of f hf => exact le_multiplicativeClosure _ _ ⟨hf⟩
  | id x => simpa using .id (F.obj x)
  | comp_of _ _ hf hg h =>
    simpa using multiplicativeClosure.comp_of _ _ h (strictMap.map hg)

中文:
引理 strictMap_multiplicativeClosure_le
  条件: (F : C ⥤ D)
  证明: by
  intro _ _ f hf
  induction hf with | map hf
  induction hf with
  | of f hf => exact le_multiplicativeClosure _ _ ⟨hf⟩
  | id x => simpa using .id (F.obj x)
  | comp_of _ _ hf hg h =>
    simpa using multiplicativeClosure.comp_of _ _ h (strictMap.map hg)

Depends on / 依赖: F.obj, comp_of, le_multiplicativeClosure, multiplicativeClosure, multiplicativeClosure.comp_of, strictMap, strictMap.map
-/
lemma strictMap_multiplicativeClosure_le (F : C ⥤ D) :
    W.multiplicativeClosure.strictMap F <= (W.strictMap F).multiplicativeClosure := by
  intro _ _ f hf
  induction hf with | map hf
  induction hf with
  | of f hf => exact le_multiplicativeClosure _ _ ⟨hf⟩
  | id x => simpa using .id (F.obj x)
  | comp_of _ _ hf hg h =>
    simpa using multiplicativeClosure.comp_of _ _ h (strictMap.map hg)

/--
Definition of `HasOfPostcompProperty` / `HasOfPostcompProperty` 的定义

English:
class HasOfPostcompProperty
  parameters: (W W' : MorphismProperty C)
  axioms and operations (1):
    - of_postcomp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : W' g -> W (f ≫ g) -> W f

中文:
类 有OfPostcompProperty
  参数: (W W' : MorphismProperty C)
  公理与运算 (1 个):
    - of_postcomp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : W' g -> W (f ≫ g) -> W f
-/
class HasOfPostcompProperty (W W' : MorphismProperty C) : Prop where
  of_postcomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' g -> W (f ≫ g) -> W f

/--
Definition of `HasOfPrecompProperty` / `HasOfPrecompProperty` 的定义

English:
class HasOfPrecompProperty
  parameters: (W W' : MorphismProperty C)
  axioms and operations (1):
    - of_precomp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : W' f -> W (f ≫ g) -> W g

中文:
类 有OfPrecompProperty
  参数: (W W' : MorphismProperty C)
  公理与运算 (1 个):
    - of_precomp({X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)) : W' f -> W (f ≫ g) -> W g
-/
class HasOfPrecompProperty (W W' : MorphismProperty C) : Prop where
  of_precomp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) : W' f -> W (f ≫ g) -> W g

/--
Definition of `HasTwoOutOfThreeProperty` / `HasTwoOutOfThreeProperty` 的定义

English:
class HasTwoOutOfThreeProperty
  parameters: (W : MorphismProperty C)
  extends: W.IsStableUnderComposition, W.HasOfPostcompProperty W, W.HasOfPrecompProperty W
  (no additional axioms)

中文:
类 有TwoOutOfThreeProperty
  参数: (W : MorphismProperty C)
  继承: W.是StableUnderComposition, W.有OfPostcompProperty W, W.有OfPrecompProperty W
  (无附加公理)
-/
class HasTwoOutOfThreeProperty (W : MorphismProperty C) : Prop
    extends W.IsStableUnderComposition, W.HasOfPostcompProperty W, W.HasOfPrecompProperty W where

section

variable (W W' : MorphismProperty C) {W'}

/--
lemma `of_postcomp` / 引理 `of_postcomp`

English:
lemma of_postcomp
  statement: [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
  proof: HasOfPostcompProperty.of_postcomp f g hg hfg

中文:
引理 of_postcomp
  结论: [W.有OfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
  证明: HasOfPostcompProperty.of_postcomp f g hg hfg

Depends on / 依赖: HasOfPostcompProperty, HasOfPostcompProperty.of_postcomp, of_postcomp
-/
lemma of_postcomp [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g)
    (hfg : W (f ≫ g)) : W f :=
  HasOfPostcompProperty.of_postcomp f g hg hfg

/--
lemma `of_precomp` / 引理 `of_precomp`

English:
lemma of_precomp
  statement: [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
  proof: HasOfPrecompProperty.of_precomp f g hf hfg

中文:
引理 of_precomp
  结论: [W.有OfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
  证明: HasOfPrecompProperty.of_precomp f g hf hfg

Depends on / 依赖: HasOfPrecompProperty, HasOfPrecompProperty.of_precomp, of_precomp
-/
lemma of_precomp [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
    (hfg : W (f ≫ g)) : W g :=
  HasOfPrecompProperty.of_precomp f g hf hfg

/--
lemma `postcomp_iff` / 引理 `postcomp_iff`

English:
lemma postcomp_iff
  statement: [W.RespectsRight W'] [W.HasOfPostcompProperty W']
  proof: ⟨W.of_postcomp f g hg, fun hf => RespectsRight.postcomp _ hg _ hf⟩

中文:
引理 postcomp_iff
  结论: [W.RespectsRight W'] [W.有OfPostcompProperty W']
  证明: ⟨W.of_postcomp f g hg, fun hf => RespectsRight.postcomp _ hg _ hf⟩

Depends on / 依赖: RespectsRight, RespectsRight.postcomp, W.of_postcomp, of_postcomp, postcomp
-/
lemma postcomp_iff [W.RespectsRight W'] [W.HasOfPostcompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W' g) : W (f ≫ g) ↔ W f :=
  ⟨W.of_postcomp f g hg, fun hf => RespectsRight.postcomp _ hg _ hf⟩

/--
lemma `precomp_iff` / 引理 `precomp_iff`

English:
lemma precomp_iff
  statement: [W.RespectsLeft W'] [W.HasOfPrecompProperty W']
  proof: ⟨W.of_precomp f g hf, fun hg => RespectsLeft.precomp _ hf _ hg⟩

中文:
引理 precomp_iff
  结论: [W.RespectsLeft W'] [W.有OfPrecompProperty W']
  证明: ⟨W.of_precomp f g hf, fun hg => RespectsLeft.precomp _ hf _ hg⟩

Depends on / 依赖: RespectsLeft, RespectsLeft.precomp, W.of_precomp, of_precomp, precomp
-/
lemma precomp_iff [W.RespectsLeft W'] [W.HasOfPrecompProperty W']
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f) :
    W (f ≫ g) ↔ W g :=
  ⟨W.of_precomp f g hf, fun hg => RespectsLeft.precomp _ hf _ hg⟩

/--
lemma `HasOfPostcompProperty.of_le` / 引理 `HasOfPostcompProperty.of_le`

English:
lemma HasOfPostcompProperty.of_le
  statement: (Q : MorphismProperty C) [W.HasOfPostcompProperty Q]
  proof: W.of_postcomp (W' := Q) f g (hle _ hg) hfg

中文:
引理 有OfPostcompProperty.of_le
  结论: (Q : MorphismProperty C) [W.有OfPostcompProperty Q]
  证明: W.of_postcomp (W' := Q) f g (hle _ hg) hfg

Depends on / 依赖: W.of_postcomp, of_postcomp
-/
lemma HasOfPostcompProperty.of_le (Q : MorphismProperty C) [W.HasOfPostcompProperty Q]
    (hle : W' <= Q) : W.HasOfPostcompProperty W' where
  of_postcomp f g hg hfg := W.of_postcomp (W' := Q) f g (hle _ hg) hfg

/--
lemma `HasOfPrecompProperty.of_le` / 引理 `HasOfPrecompProperty.of_le`

English:
lemma HasOfPrecompProperty.of_le
  statement: (Q : MorphismProperty C) [W.HasOfPrecompProperty Q]
  proof: W.of_precomp (W' := Q) f g (hle _ hg) hfg

中文:
引理 有OfPrecompProperty.of_le
  结论: (Q : MorphismProperty C) [W.有OfPrecompProperty Q]
  证明: W.of_precomp (W' := Q) f g (hle _ hg) hfg

Depends on / 依赖: W.of_precomp, of_precomp
-/
lemma HasOfPrecompProperty.of_le (Q : MorphismProperty C) [W.HasOfPrecompProperty Q]
    (hle : W' <= Q) : W.HasOfPrecompProperty W' where
  of_precomp f g hg hfg := W.of_precomp (W' := Q) f g (hle _ hg) hfg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.HasOfPostcompProperty
  signature: W'] : W.op.HasOfPrecompProperty W'.op where
  body: W.of_postcomp _ _ hf hfg

中文:
实例 [W.有OfPostcompProperty
  签名: W'] : W.op.有OfPrecompProperty W'.op where
  定义体: W.of_postcomp _ _ hf hfg

Depends on / 依赖: W.of_postcomp, of_postcomp
-/
instance [W.HasOfPostcompProperty W'] : W.op.HasOfPrecompProperty W'.op where
  of_precomp _ _ hf hfg := W.of_postcomp _ _ hf hfg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.HasOfPrecompProperty
  signature: W'] : W.op.HasOfPostcompProperty W'.op where
  body: W.of_precomp _ _ hg hfg

中文:
实例 [W.有OfPrecompProperty
  签名: W'] : W.op.有OfPostcompProperty W'.op where
  定义体: W.of_precomp _ _ hg hfg

Depends on / 依赖: W.of_precomp, of_precomp
-/
instance [W.HasOfPrecompProperty W'] : W.op.HasOfPostcompProperty W'.op where
  of_postcomp _ _ hg hfg := W.of_precomp _ _ hg hfg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.HasTwoOutOfThreeProperty]
  signature: : W.op.HasTwoOutOfThreeProperty where

中文:
实例 [W.有TwoOutOfThreeProperty]
  签名: : W.op.有TwoOutOfThreeProperty where
-/
instance [W.HasTwoOutOfThreeProperty] : W.op.HasTwoOutOfThreeProperty where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : MorphismProperty C).HasOfPostcompProperty W
  body: trivial

中文:
实例 :
  签名: (⊤ : MorphismProperty C).有OfPostcompProperty W
  定义体: trivial
-/
instance : (⊤ : MorphismProperty C).HasOfPostcompProperty W where
  of_postcomp _ _ _ _ := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : MorphismProperty C).HasOfPrecompProperty W
  body: trivial

中文:
实例 :
  签名: (⊤ : MorphismProperty C).有OfPrecompProperty W
  定义体: trivial
-/
instance : (⊤ : MorphismProperty C).HasOfPrecompProperty W where
  of_precomp _ _ _ _ := trivial

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (⊤ : MorphismProperty C).HasTwoOutOfThreeProperty

中文:
实例 :
  签名: (⊤ : MorphismProperty C).有TwoOutOfThreeProperty
-/
instance : (⊤ : MorphismProperty C).HasTwoOutOfThreeProperty where

variable (P Q : MorphismProperty C)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasOfPostcompProperty
  signature: W] [Q.HasOfPostcompProperty W] :
  body: ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩

中文:
实例 [P.有OfPostcompProperty
  签名: W] [Q.有OfPostcompProperty W] :
  定义体: ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩

Depends on / 依赖: P.of_postcomp, Q.of_postcomp, of_postcomp
-/
instance [P.HasOfPostcompProperty W] [Q.HasOfPostcompProperty W] :
    (P ⊓ Q).HasOfPostcompProperty W where
  of_postcomp f g hg hfg := ⟨P.of_postcomp f g hg hfg.1, Q.of_postcomp f g hg hfg.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasOfPrecompProperty
  signature: W] [Q.HasOfPrecompProperty W] :
  body: ⟨P.of_precomp f g hg hfg.1, Q.of_precomp f g hg hfg.2⟩

中文:
实例 [P.有OfPrecompProperty
  签名: W] [Q.有OfPrecompProperty W] :
  定义体: ⟨P.of_precomp f g hg hfg.1, Q.of_precomp f g hg hfg.2⟩

Depends on / 依赖: P.of_precomp, Q.of_precomp, of_precomp
-/
instance [P.HasOfPrecompProperty W] [Q.HasOfPrecompProperty W] :
    (P ⊓ Q).HasOfPrecompProperty W where
  of_precomp f g hg hfg := ⟨P.of_precomp f g hg hfg.1, Q.of_precomp f g hg hfg.2⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.HasTwoOutOfThreeProperty]
  signature: [Q.HasTwoOutOfThreeProperty]
  body: by
  have : P.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : P.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : Q.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  have : Q.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  constructor

中文:
实例 [P.有TwoOutOfThreeProperty]
  签名: [Q.有TwoOutOfThreeProperty]
  定义体: by
  have : P.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : P.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : Q.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  have : Q.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  constructor

Depends on / 依赖: HasOfPostcompProperty, HasOfPrecompProperty, P.HasOfPostcompProperty, P.HasOfPrecompProperty, Q.HasOfPostcompProperty, Q.HasOfPrecompProperty, inf_le_left, inf_le_right, of_le
-/
instance [P.HasTwoOutOfThreeProperty] [Q.HasTwoOutOfThreeProperty] :
    (P ⊓ Q).HasTwoOutOfThreeProperty := by
  have : P.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : P.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_left
  have : Q.HasOfPostcompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  have : Q.HasOfPrecompProperty (P ⊓ Q) := .of_le _ _ inf_le_right
  constructor

end

section

variable (W₁ W₂ : MorphismProperty Cᵒᵖ)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.HasOfPostcompProperty
  signature: W₂] : W₁.unop.HasOfPrecompProperty W₂.unop where
  body: W₁.of_postcomp _ _ hf hfg

中文:
实例 [W₁.有OfPostcompProperty
  签名: W₂] : W₁.unop.有OfPrecompProperty W₂.unop where
  定义体: W₁.of_postcomp _ _ hf hfg

Depends on / 依赖: of_postcomp
-/
instance [W₁.HasOfPostcompProperty W₂] : W₁.unop.HasOfPrecompProperty W₂.unop where
  of_precomp _ _ hf hfg := W₁.of_postcomp _ _ hf hfg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.HasOfPrecompProperty
  signature: W₂] : W₁.unop.HasOfPostcompProperty W₂.unop where
  body: W₁.of_precomp _ _ hg hfg

中文:
实例 [W₁.有OfPrecompProperty
  签名: W₂] : W₁.unop.有OfPostcompProperty W₂.unop where
  定义体: W₁.of_precomp _ _ hg hfg

Depends on / 依赖: of_precomp
-/
instance [W₁.HasOfPrecompProperty W₂] : W₁.unop.HasOfPostcompProperty W₂.unop where
  of_postcomp _ _ hg hfg := W₁.of_precomp _ _ hg hfg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W₁.HasTwoOutOfThreeProperty]
  signature: : W₁.unop.HasTwoOutOfThreeProperty where

中文:
实例 [W₁.有TwoOutOfThreeProperty]
  签名: : W₁.unop.有TwoOutOfThreeProperty where
-/
instance [W₁.HasTwoOutOfThreeProperty] : W₁.unop.HasTwoOutOfThreeProperty where

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (isomorphisms C).HasTwoOutOfThreeProperty
  body: fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))

中文:
实例 :
  签名: (isomorphisms C).有TwoOutOfThreeProperty
  定义体: fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))
-/
instance : (isomorphisms C).HasTwoOutOfThreeProperty where
  of_postcomp f g := fun (hg : IsIso g) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso ((f ≫ g) ≫ inv g))
  of_precomp f g := fun (hf : IsIso f) (hfg : IsIso (f ≫ g)) =>
    by simpa using (inferInstance : IsIso (inv f ≫ (f ≫ g)))

instance (F : C ⥤ D) (W : MorphismProperty D) [W.HasTwoOutOfThreeProperty] :
    (W.inverseImage F).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg := W.of_postcomp (F.map f) (F.map g) hg (by simpa using hfg)
  of_precomp f g hf hfg := W.of_precomp (F.map f) (F.map g) hf (by simpa using hfg)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : W.HasOfPrecompProperty (isomorphisms C) where
  body: (W.cancel_left_of_respectsIso _ _).mp

中文:
实例 [W.RespectsIso]
  签名: : W.有OfPrecompProperty (isomorphisms C) where
  定义体: (W.cancel_left_of_respectsIso _ _).mp

Depends on / 依赖: W.cancel_left_of_respectsIso, cancel_left_of_respectsIso
-/
instance [W.RespectsIso] : W.HasOfPrecompProperty (isomorphisms C) where
  of_precomp _ _ (_ : IsIso _) := (W.cancel_left_of_respectsIso _ _).mp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [W.RespectsIso]
  signature: : W.HasOfPostcompProperty (isomorphisms C) where
  body: (W.cancel_right_of_respectsIso _ _).mp

中文:
实例 [W.RespectsIso]
  签名: : W.有OfPostcompProperty (isomorphisms C) where
  定义体: (W.cancel_right_of_respectsIso _ _).mp

Depends on / 依赖: W.cancel_right_of_respectsIso, cancel_right_of_respectsIso
-/
instance [W.RespectsIso] : W.HasOfPostcompProperty (isomorphisms C) where
  of_postcomp _ _ (_ : IsIso _) := (W.cancel_right_of_respectsIso _ _).mp

end MorphismProperty

end CategoryTheory
