/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.CommSq

/-!
# Facts about epimorphisms and monomorphisms.

The definitions of `Epi` and `Mono` are in `CategoryTheory.Category`,
since they are used by some lemmas for `Iso`, which is used everywhere.
-/

@[expose] public section


universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

@[to_dual unop_mono_of_epi]
/--
Instance `unop_epi_of_mono` / 实例 `unop_epi_of_mono`

English:
instance unop_epi_of_mono
  signature: {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f]
  body: ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

@[to_dual op_mono_of_epi]

中文:
实例 unop_epi_of_mono
  签名: {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f]
  定义体: ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

@[to_dual op_mono_of_epi]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, cancel_mono, op_inj, unop_inj
-/
instance unop_epi_of_mono {A B : Cᵒᵖ} (f : A ⟶ B) [Mono f] : Epi f.unop :=
  ⟨fun _ _ eq => Quiver.Hom.op_inj ((cancel_mono f).1 (Quiver.Hom.unop_inj eq))⟩

@[to_dual op_mono_of_epi]
/--
Instance `op_epi_of_mono` / 实例 `op_epi_of_mono`

English:
instance op_epi_of_mono
  signature: {A B : C} (f : A ⟶ B) [Mono f]
  body: ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj eq))⟩

@[to_dual (attr := simp)]

中文:
实例 op_epi_of_mono
  签名: {A B : C} (f : A ⟶ B) [Mono f]
  定义体: ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj eq))⟩

@[to_dual (attr := simp)]

Depends on / 依赖: Quiver, Quiver.Hom.op_inj, Quiver.Hom.unop_inj, cancel_mono, op_inj, unop_inj
-/
instance op_epi_of_mono {A B : C} (f : A ⟶ B) [Mono f] : Epi f.op :=
  ⟨fun _ _ eq => Quiver.Hom.unop_inj ((cancel_mono f).1 (Quiver.Hom.op_inj eq))⟩

@[to_dual (attr := simp)]
/--
lemma `op_epi_iff` / 引理 `op_epi_iff`

English:
lemma op_epi_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: ⟨fun _ => unop_mono_of_epi f.op, fun _ => inferInstance⟩

@[to_dual (attr := simp)]

中文:
引理 op_epi_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: ⟨fun _ => unop_mono_of_epi f.op, fun _ => inferInstance⟩

@[to_dual (attr := simp)]

Depends on / 依赖: f.op, unop_mono_of_epi
-/
lemma op_epi_iff {X Y : C} (f : X ⟶ Y) :
    Epi f.op ↔ Mono f :=
  ⟨fun _ => unop_mono_of_epi f.op, fun _ => inferInstance⟩

@[to_dual (attr := simp)]
/--
lemma `unop_epi_iff` / 引理 `unop_epi_iff`

English:
lemma unop_epi_iff
  given: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  proof: ⟨fun _ => op_mono_of_epi f.unop, fun _ => inferInstance⟩

中文:
引理 unop_epi_iff
  条件: {X Y : Cᵒᵖ} (f : X ⟶ Y)
  证明: ⟨fun _ => op_mono_of_epi f.unop, fun _ => inferInstance⟩

Depends on / 依赖: f.unop, op_mono_of_epi
-/
lemma unop_epi_iff {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    Epi f.unop ↔ Mono f :=
  ⟨fun _ => op_mono_of_epi f.unop, fun _ => inferInstance⟩

/--
Definition of `SplitMono` / `SplitMono` 的定义

English:
structure SplitMono
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (2):
    - retraction : Y ⟶ X
    - id : f ≫ retraction = 𝟙 X  [default: by cat_disch]

中文:
结构 SplitMono
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (2 个):
    - retraction : Y ⟶ X
    - id : f ≫ retraction = 𝟙 X  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure SplitMono {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  retraction : Y ⟶ X
  /-- `f` composed with `retraction` is the identity -/
  id : f ≫ retraction = 𝟙 X := by cat_disch

/--
Definition of `IsSplitMono` / `IsSplitMono` 的定义

English:
class IsSplitMono
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - exists_splitMono : Nonempty (SplitMono f)

中文:
类 IsSplitMono
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - exists_splitMono : Nonempty (SplitMono f)
-/
class IsSplitMono {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitMono : Nonempty (SplitMono f)

/-- A split epimorphism is a morphism `f : X ⟶ Y` with a given section `section_ f : Y ⟶ X`
such that `section_ f ≫ f = 𝟙 Y`.
(Note that `section` is a reserved keyword, so we append an underscore.)

Every split epimorphism is an epimorphism.
-/
@[to_dual (attr := ext, aesop apply safe (rule_sets := [CategoryTheory]))]
/--
Definition of `SplitEpi` / `SplitEpi` 的定义

English:
structure SplitEpi
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (2):
    - section_ : Y ⟶ X
    - id : section_ ≫ f = 𝟙 Y  [default: by cat_disch]

中文:
结构 SplitEpi
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (2 个):
    - section_ : Y ⟶ X
    - id : section_ ≫ f = 𝟙 Y  [默认: by cat_disch]
-/
structure SplitEpi {X Y : C} (f : X ⟶ Y) where
  /-- The map splitting `f` -/
  section_ : Y ⟶ X
  /-- `section_` composed with `f` is the identity -/
  id : section_ ≫ f = 𝟙 Y := by cat_disch

-- TODO: `to_dual` should add these automatically:
attribute [to_dual existing] SplitEpi.ext SplitEpi.ext_iff

/-- `IsSplitEpi f` is the assertion that `f` admits a section -/
@[to_dual]
/--
Definition of `IsSplitEpi` / `IsSplitEpi` 的定义

English:
class IsSplitEpi
  parameters: {X Y : C} (f : X ⟶ Y)
  axioms and operations (1):
    - exists_splitEpi : Nonempty (SplitEpi f)

中文:
类 IsSplitEpi
  参数: {X Y : C} (f : X ⟶ Y)
  公理与运算 (1 个):
    - exists_splitEpi : Nonempty (SplitEpi f)

Depends on / 依赖: SplitEpi, SplitEpi.id, SplitMono, SplitMono.id
-/
class IsSplitEpi {X Y : C} (f : X ⟶ Y) : Prop where
  /-- There is a splitting -/
  exists_splitEpi : Nonempty (SplitEpi f)

attribute [reassoc (attr := simp)] SplitMono.id SplitEpi.id

/-- A composition of `SplitEpi` is a split `SplitEpi`. -/
@[to_dual (attr := simps) (reorder := X Z, f g, sef seg) (rename := f ↔ g, sef -> smg, seg -> smf)
/-- A composition of `SplitMono` is a `SplitMono`. -/]
/--
Definition of `SplitEpi.comp` / `SplitEpi.comp` 的定义

English:
definition SplitEpi.comp
  signature: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g)
  body: seg.section_ ≫ sef.section_

中文:
定义 SplitEpi.comp
  签名: {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g)
  定义体: seg.section_ ≫ sef.section_
-/
def SplitEpi.comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} (sef : SplitEpi f) (seg : SplitEpi g) :
    SplitEpi (f ≫ g) where
  section_ := seg.section_ ≫ sef.section_

/-- A constructor for `IsSplitEpi f` taking a `SplitEpi f` as an argument -/
@[to_dual /-- A constructor for `IsSplitMono f` taking a `SplitMono f` as an argument -/]
/--
theorem `IsSplitEpi.mk'` / 定理 `IsSplitEpi.mk'`

English:
theorem IsSplitEpi.mk'
  given: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  statement: IsSplitEpi f
  proof: ⟨Nonempty.intro se⟩

中文:
定理 IsSplitEpi.mk'
  条件: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  结论: IsSplitEpi f
  证明: ⟨Nonempty.intro se⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
theorem IsSplitEpi.mk' {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : IsSplitEpi f :=
  ⟨Nonempty.intro se⟩

/-- The chosen section of a split epimorphism.
(Note that `section` is a reserved keyword, so we append an underscore.)
-/
@[to_dual retraction /-- The chosen retraction of a split monomorphism. -/]
/--
Definition of `section_` / `section_` 的定义

English:
definition section_
  signature: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f]
  body: hf.exists_splitEpi.some.section_

@[to_dual (attr := reassoc (attr := simp))]

中文:
定义 section_
  签名: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f]
  定义体: hf.exists_splitEpi.some.section_

@[to_dual (attr := reassoc (attr := simp))]

Depends on / 依赖: exists_splitEpi, hf.exists_splitEpi.some.section_, section_
-/
noncomputable def section_ {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Y ⟶ X :=
  hf.exists_splitEpi.some.section_

@[to_dual (attr := reassoc (attr := simp))]
/--
theorem `IsSplitEpi.id` / 定理 `IsSplitEpi.id`

English:
theorem IsSplitEpi.id
  given: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f]
  statement: section_ f ≫ f = 𝟙 Y
  proof: hf.exists_splitEpi.some.id

中文:
定理 IsSplitEpi.id
  条件: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f]
  结论: section_ f ≫ f = 𝟙 Y
  证明: hf.exists_splitEpi.some.id

Depends on / 依赖: exists_splitEpi, hf.exists_splitEpi.some.id
-/
theorem IsSplitEpi.id {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : section_ f ≫ f = 𝟙 Y :=
  hf.exists_splitEpi.some.id

/-- The section of a split epimorphism has an obvious retraction. -/
@[to_dual splitEpi /-- The retraction of a split monomorphism has an obvious section. -/]
/--
Definition of `SplitEpi.splitMono` / `SplitEpi.splitMono` 的定义

English:
definition SplitEpi.splitMono
  signature: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  body: f

中文:
定义 SplitEpi.splitMono
  签名: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  定义体: f
-/
def SplitEpi.splitMono {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : SplitMono se.section_ where
  retraction := f

/-- The section of a split epimorphism is itself a split monomorphism. -/
@[to_dual retraction_isSplitEpi
/-- The retraction of a split monomorphism is itself a split epimorphism. -/]
/--
Instance `section_isSplitMono` / 实例 `section_isSplitMono`

English:
instance section_isSplitMono
  signature: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  body: IsSplitMono.mk' (SplitEpi.splitMono _)

中文:
实例 section_isSplitMono
  签名: {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]
  定义体: IsSplitMono.mk' (SplitEpi.splitMono _)

Depends on / 依赖: IsSplitMono, IsSplitMono.mk, SplitEpi, SplitEpi.splitMono, splitMono
-/
instance section_isSplitMono {X Y : C} (f : X ⟶ Y) [IsSplitEpi f] : IsSplitMono (section_ f) :=
  IsSplitMono.mk' (SplitEpi.splitMono _)

/-- A split epi which is mono is an iso. -/
@[to_dual isIso_of_epi_of_isSplitMono /-- A split mono which is epi is an iso. -/]
/--
theorem `isIso_of_mono_of_isSplitEpi` / 定理 `isIso_of_mono_of_isSplitEpi`

English:
theorem isIso_of_mono_of_isSplitEpi
  given: {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f]
  statement: IsIso f
  proof: ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

中文:
定理 isIso_of_mono_of_isSplitEpi
  条件: {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f]
  结论: IsIso f
  证明: ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

Depends on / 依赖: cancel_mono, section_
-/
theorem isIso_of_mono_of_isSplitEpi {X Y : C} (f : X ⟶ Y) [Mono f] [IsSplitEpi f] : IsIso f :=
  ⟨⟨section_ f, ⟨by simp [← cancel_mono f], by simp⟩⟩⟩

/-- Every iso is a split epi. -/
@[to_dual /-- Every iso is a split mono. -/]
instance (priority := 100) IsSplitEpi.of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] : IsSplitEpi f :=
  IsSplitEpi.mk' { section_ := inv f }

@[to_dual]
/--
theorem `SplitEpi.epi` / 定理 `SplitEpi.epi`

English:
theorem SplitEpi.epi
  given: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  statement: Epi f
  proof: { left_cancellation := fun g h w => by replace w := se.section_ ≫= w; simpa using w }

中文:
定理 SplitEpi.epi
  条件: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f)
  结论: Epi f
  证明: { left_cancellation := fun g h w => by replace w := se.section_ ≫= w; simpa using w }

Depends on / 依赖: left_cancellation, replace, se.section_, section_
-/
theorem SplitEpi.epi {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) : Epi f :=
  { left_cancellation := fun g h w => by replace w := se.section_ ≫= w; simpa using w }

/-- Every split epi is an epi. -/
@[to_dual /-- Every split mono is a mono. -/]
instance (priority := 100) IsSplitEpi.epi {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] : Epi f :=
  hf.exists_splitEpi.some.epi

@[to_dual]
instance {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} [hf : IsSplitEpi f] [hg : IsSplitEpi g] :
IsSplitEpi (f ≫ g) := IsSplitEpi.mk' hf.exists_splitEpi.some.comp hg.exists_splitEpi.some

/-- Every split epi whose section is epi is an iso. -/
@[to_dual /-- Every split mono whose retraction is mono is an iso. -/]
/--
theorem `IsIso.of_epi_section'` / 定理 `IsIso.of_epi_section'`

English:
theorem IsIso.of_epi_section'
  given: {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_]
  proof: ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩

中文:
定理 IsIso.of_epi_section'
  条件: {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_]
  证明: ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩

Depends on / 依赖: cancel_epi_id, hf.section_, section_
-/
theorem IsIso.of_epi_section' {X Y : C} {f : X ⟶ Y} (hf : SplitEpi f) [Epi <| hf.section_] :
    IsIso f :=
  ⟨⟨hf.section_, ⟨(cancel_epi_id <| hf.section_).mp (by simp), by simp⟩⟩⟩

/-- Every split epi whose section is epi is an iso. -/
@[to_dual /-- Every split mono whose retraction is mono is an iso. -/]
/--
theorem `IsIso.of_epi_section` / 定理 `IsIso.of_epi_section`

English:
theorem IsIso.of_epi_section
  given: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f]
  proof: @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'

中文:
定理 IsIso.of_epi_section
  条件: {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f]
  证明: @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'

Depends on / 依赖: IsIso.of_epi_section, exists_splitEpi, hf.exists_splitEpi.some, of_epi_section
-/
theorem IsIso.of_epi_section {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] [hf' : Epi <| section_ f] :
    IsIso f :=
  @IsIso.of_epi_section' _ _ _ _ _ hf.exists_splitEpi.some hf'

-- FIXME this has unnecessarily become noncomputable!
/-- A category where every morphism has a `Trunc` retraction is computably a groupoid. -/
@[instance_reducible]
/--
Definition of `Groupoid.ofTruncSplitMono` / `Groupoid.ofTruncSplitMono` 的定义

English:
definition Groupoid.ofTruncSplitMono
  body: by
  apply Groupoid.ofIsIso
  intro X Y f
have ⟨a,_⟩ := Trunc.exists_rep all_split_mono f
have ⟨b,_⟩ := Trunc.exists_rep all_split_mono retraction f
  apply IsIso.of_mono_retraction

中文:
定义 Groupoid.ofTruncSplitMono
  定义体: by
  apply Groupoid.ofIsIso
  intro X Y f
have ⟨a,_⟩ := Trunc.exists_rep all_split_mono f
have ⟨b,_⟩ := Trunc.exists_rep all_split_mono retraction f
  apply IsIso.of_mono_retraction

Depends on / 依赖: Groupoid, Groupoid.ofIsIso, IsIso.of_mono_retraction, Trunc.exists_rep, all_split_mono, exists_rep, ofIsIso, of_mono_retraction, retraction
-/
noncomputable def Groupoid.ofTruncSplitMono
    (all_split_mono : forall {X Y : C} (f : X ⟶ Y), Trunc (IsSplitMono f)) : Groupoid.{v₁} C := by
  apply Groupoid.ofIsIso
  intro X Y f
have ⟨a,_⟩ := Trunc.exists_rep all_split_mono f
have ⟨b,_⟩ := Trunc.exists_rep all_split_mono retraction f
  apply IsIso.of_mono_retraction

section

variable (C)

/--
Definition of `SplitMonoCategory` / `SplitMonoCategory` 的定义

English:
class SplitMonoCategory
  parameters: : Prop where
  axioms and operations (1):
    - isSplitMono_of_mono : forall {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

中文:
类 SplitMonoCategory
  参数: : 命题 where
  公理与运算 (1 个):
    - isSplitMono_of_mono : 对任意 {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f
-/
class SplitMonoCategory : Prop where
  /-- All monos are split -/
  isSplitMono_of_mono : forall {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

/-- A split epi category is a category in which every epimorphism is split. -/
@[to_dual]
/--
Definition of `SplitEpiCategory` / `SplitEpiCategory` 的定义

English:
class SplitEpiCategory
  parameters: : Prop where
  axioms and operations (1):
    - isSplitEpi_of_epi : forall {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

中文:
类 SplitEpiCategory
  参数: : 命题 where
  公理与运算 (1 个):
    - isSplitEpi_of_epi : 对任意 {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f
-/
class SplitEpiCategory : Prop where
  /-- All epis are split -/
  isSplitEpi_of_epi : forall {X Y : C} (f : X ⟶ Y) [Epi f], IsSplitEpi f

end

/-- In a category in which every epimorphism is split, every epimorphism splits. This is not an
instance because it would create an instance loop. -/
@[to_dual
/-- In a category in which every monomorphism is split, every monomorphism splits. This is not an
instance because it would create an instance loop. -/]
/--
theorem `isSplitEpi_of_epi` / 定理 `isSplitEpi_of_epi`

English:
theorem isSplitEpi_of_epi
  given: [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f]
  statement: IsSplitEpi f
  proof: SplitEpiCategory.isSplitEpi_of_epi _

中文:
定理 isSplitEpi_of_epi
  条件: [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f]
  结论: IsSplitEpi f
  证明: SplitEpiCategory.isSplitEpi_of_epi _

Depends on / 依赖: SplitEpiCategory, SplitEpiCategory.isSplitEpi_of_epi, isSplitEpi_of_epi
-/
theorem isSplitEpi_of_epi [SplitEpiCategory C] {X Y : C} (f : X ⟶ Y) [Epi f] : IsSplitEpi f :=
  SplitEpiCategory.isSplitEpi_of_epi _

section

variable {D : Type u₂} [Category.{v₂} D]

/-- Split epimorphisms are also absolute epimorphisms. -/
@[to_dual (attr := simps) /-- Split monomorphisms are also absolute monomorphisms. -/]
/--
Definition of `SplitEpi.map` / `SplitEpi.map` 的定义

English:
definition SplitEpi.map
  signature: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D)
  body: F.map se.section_
  id := by rw [← Functor.map_comp, SplitEpi.id, Functor.map_id]

@[to_dual]

中文:
定义 SplitEpi.map
  签名: {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D)
  定义体: F.map se.section_
  id := by rw [← Functor.map_comp, SplitEpi.id, Functor.map_id]

@[to_dual]
-/
def SplitEpi.map {X Y : C} {f : X ⟶ Y} (se : SplitEpi f) (F : C ⥤ D) : SplitEpi (F.map f) where
  section_ := F.map se.section_
  id := by rw [← Functor.map_comp, SplitEpi.id, Functor.map_id]

@[to_dual]
instance {X Y : C} (f : X ⟶ Y) [hf : IsSplitEpi f] (F : C ⥤ D) : IsSplitEpi (F.map f) :=
  IsSplitEpi.mk' (hf.exists_splitEpi.some.map F)

end

section

/-- When `f` is an epimorphism, `f ≫ g` is epic iff `g` is. -/
@[to_dual (attr := simp) (reorder := g f 7)
/-- When `g` is a monomorphism, `f ≫ g` is monic iff `f` is. -/]
/--
lemma `epi_comp_iff_of_epi` / 引理 `epi_comp_iff_of_epi`

English:
lemma epi_comp_iff_of_epi
  given: {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z)
  proof: ⟨fun _ => epi_of_epi f _, fun _ => inferInstance⟩

中文:
引理 epi_comp_iff_of_epi
  条件: {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z)
  证明: ⟨fun _ => epi_of_epi f _, fun _ => inferInstance⟩

Depends on / 依赖: epi_of_epi
-/
lemma epi_comp_iff_of_epi {X Y Z : C} (f : X ⟶ Y) [Epi f] (g : Y ⟶ Z) :
    Epi (f ≫ g) ↔ Epi g :=
  ⟨fun _ => epi_of_epi f _, fun _ => inferInstance⟩

/-- When `g` is an isomorphism, `f ≫ g` is epic iff `f` is. -/
@[to_dual (attr := simp) (reorder := g f 8)
/-- When `f` is an isomorphism, `f ≫ g` is monic iff `g` is. -/]
/--
lemma `epi_comp_iff_of_isIso` / 引理 `epi_comp_iff_of_isIso`

English:
lemma epi_comp_iff_of_isIso
  given: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  proof: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  simpa using (inferInstance : Epi ((f ≫ g) ≫ inv g))

中文:
引理 epi_comp_iff_of_isIso
  条件: {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g]
  证明: by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  simpa using (inferInstance : Epi ((f ≫ g) ≫ inv g))
-/
lemma epi_comp_iff_of_isIso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] :
    Epi (f ≫ g) ↔ Epi f := by
  refine ⟨fun h => ?_, fun h => inferInstance⟩
  simpa using (inferInstance : Epi ((f ≫ g) ≫ inv g))

end

section Opposite

variable {X Y : C} {f : X ⟶ Y}

/-- The opposite of a split epi is a split mono. -/
@[to_dual /-- The opposite of a split mono is a split epi. -/]
/--
Definition of `SplitEpi.op` / `SplitEpi.op` 的定义

English:
definition SplitEpi.op
  signature: (h : SplitEpi f)
  body: h.section_.op
  id := Quiver.Hom.unop_inj (by simp)

@[to_dual]

中文:
定义 SplitEpi.op
  签名: (h : SplitEpi f)
  定义体: h.section_.op
  id := Quiver.Hom.unop_inj (by simp)

@[to_dual]

Depends on / 依赖: h.section_.op, section_
-/
def SplitEpi.op (h : SplitEpi f) : SplitMono f.op where
  retraction := h.section_.op
  id := Quiver.Hom.unop_inj (by simp)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsSplitMono
  signature: f] : IsSplitEpi f.op
  body: .mk' IsSplitMono.exists_splitMono.some.op

中文:
实例 [IsSplitMono
  签名: f] : IsSplitEpi f.op
  定义体: .mk' IsSplitMono.exists_splitMono.some.op

Depends on / 依赖: IsSplitMono, IsSplitMono.exists_splitMono.some.op, exists_splitMono
-/
instance [IsSplitMono f] : IsSplitEpi f.op :=
  .mk' IsSplitMono.exists_splitMono.some.op

end Opposite


section cubeLemma

variable {M000 M001 M010 M011 M100 M101 M110 M111 : C}
  (f00x : M000 ⟶ M001) (f01x : M010 ⟶ M011) (f10x : M100 ⟶ M101) (f11x : M110 ⟶ M111)
  (f0x0 : M000 ⟶ M010) (f0x1 : M001 ⟶ M011) (f1x0 : M100 ⟶ M110) (f1x1 : M101 ⟶ M111)
  (fx00 : M000 ⟶ M100) (fx01 : M001 ⟶ M101) (fx10 : M010 ⟶ M110) (fx11 : M011 ⟶ M111)

/--
theorem `cube_lemma_of_epi` / 定理 `cube_lemma_of_epi`

English:
theorem cube_lemma_of_epi
  statement: (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
  proof: by
  rw [← cancel_epi f00x]
  grind

中文:
定理 cube_lemma_of_epi
  结论: (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
  证明: by
  rw [← cancel_epi f00x]
  grind

Depends on / 依赖: cancel_epi
-/
theorem cube_lemma_of_epi (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
    (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ fx11)
    (hxx0 : f0x0 ≫ fx10 = fx00 ≫ f1x0) [Epi f00x] : f0x1 ≫ fx11 = fx01 ≫ f1x1 := by
  rw [← cancel_epi f00x]
  grind

/--
theorem `cube_lemma_of_mono` / 定理 `cube_lemma_of_mono`

English:
theorem cube_lemma_of_mono
  statement: (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
  proof: by
  rw [← cancel_mono f11x]
  grind

中文:
定理 cube_lemma_of_mono
  结论: (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
  证明: by
  rw [← cancel_mono f11x]
  grind

Depends on / 依赖: cancel_mono
-/
theorem cube_lemma_of_mono (h0xx : f0x0 ≫ f01x = f00x ≫ f0x1) (h1xx : f1x0 ≫ f11x = f10x ≫ f1x1)
    (hx0x : fx00 ≫ f10x = f00x ≫ fx01) (hx1x : fx10 ≫ f11x = f01x ≫ fx11)
    (hxx1 : f0x1 ≫ fx11 = fx01 ≫ f1x1) [Mono f11x] : f0x0 ≫ fx10 = fx00 ≫ f1x0 := by
  rw [← cancel_mono f11x]
  grind

/--
theorem `CommSq.cube_lemma_of_epi` / 定理 `CommSq.cube_lemma_of_epi`

English:
theorem CommSq.cube_lemma_of_epi
  statement: (h0xx : CommSq f0x0 f00x f01x f0x1)
  proof: ⟨CategoryTheory.cube_lemma_of_epi f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx0.w⟩

中文:
定理 CommSq.cube_lemma_of_epi
  结论: (h0xx : CommSq f0x0 f00x f01x f0x1)
  证明: ⟨CategoryTheory.cube_lemma_of_epi f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx0.w⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.cube_lemma_of_epi, cube_lemma_of_epi, h0xx.w, h1xx.w, hx0x.w, hx1x.w, hxx0.w
-/
theorem CommSq.cube_lemma_of_epi (h0xx : CommSq f0x0 f00x f01x f0x1)
    (h1xx : CommSq f1x0 f10x f11x f1x1) (hx0x : CommSq fx00 f00x f10x fx01)
    (hx1x : CommSq fx10 f01x f11x fx11) (hxx0 : CommSq f0x0 fx00 fx10 f1x0) [Epi f00x] :
    CommSq f0x1 fx01 fx11 f1x1 :=
  ⟨CategoryTheory.cube_lemma_of_epi f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx0.w⟩

/--
theorem `CommSq.cube_lemma_of_mono` / 定理 `CommSq.cube_lemma_of_mono`

English:
theorem CommSq.cube_lemma_of_mono
  statement: (h0xx : CommSq f0x0 f00x f01x f0x1)
  proof: ⟨CategoryTheory.cube_lemma_of_mono f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx1.w⟩

中文:
定理 CommSq.cube_lemma_of_mono
  结论: (h0xx : CommSq f0x0 f00x f01x f0x1)
  证明: ⟨CategoryTheory.cube_lemma_of_mono f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx1.w⟩

Depends on / 依赖: CategoryTheory, CategoryTheory.cube_lemma_of_mono, IsLeftAdjoint, cube_lemma_of_mono, h0xx.w, h1xx.w, hx0x.w, hx1x.w, hxx1.w, preservesZeroMorphisms_of_isLeftAdjoint
-/
theorem CommSq.cube_lemma_of_mono (h0xx : CommSq f0x0 f00x f01x f0x1)
    (h1xx : CommSq f1x0 f10x f11x f1x1) (hx0x : CommSq fx00 f00x f10x fx01)
    (hx1x : CommSq fx10 f01x f11x fx11) (hxx1 : CommSq f0x1 fx01 fx11 f1x1) [Mono f11x] :
    CommSq f0x0 fx00 fx10 f1x0 :=
  ⟨CategoryTheory.cube_lemma_of_mono f00x f01x f10x f11x
      f0x0 f0x1 f1x0 f1x1 fx00 fx01 fx10 fx11 h0xx.w h1xx.w hx0x.w hx1x.w hxx1.w⟩

end cubeLemma

end CategoryTheory
