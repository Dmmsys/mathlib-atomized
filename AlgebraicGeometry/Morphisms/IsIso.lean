/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!

# Being an isomorphism is local at the target

-/

universe u

public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

/-
**AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective** 是 Mathlib 中的一个引理，
位于命名空间 `AlgebraicGeometry`。
形式化陈述：isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) : 
IsIso f ↔ IsOpenImmersion f ∧ Surjective f
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.surjective_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (f 
: X ⟶ Y), AlgebraicGeometry.Surjective f ↔ Function.Surjective ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.epi_iff_surjective`：epi_iff_surjective {X Y : TopCat.{u}} (f : X 
⟶ Y) : Epi f ↔ Function.Surjective f
· 使用定理 `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_epi_base`：∀ {X Y : Algeb
raicGeometry.Scheme} (f : X ⟶ Y),   CategoryTheory.IsIso f ↔ AlgebraicGeometry.I
sOpenImmersion f ∧ CategoryTheory.Epi f.base
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isIso_iff_isOpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Surjective f := by
  rw [surjective_iff, ← TopCat.epi_iff_surjective, isIso_iff_isOpenImmersion_and_epi_base]
/-
**AlgebraicGeometry.isomorphisms_eq_isOpenImmersion_inf_surjective** 是 Mathlib 中
的一个引理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isomorphisms_eq_isOpenImmersion_inf_surjective : isomorphisms Scheme = (@I
sOpenImmersion ⊓ @Surjective : MorphismProperty Scheme)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.iff`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Morph
ismProperty.isomorphisms C f ↔ Categor…
· 使用引理 `AlgebraicGeometry.isIso_iff_isOpenImmersion_and_surjective`：isIso_iff_is
OpenImmersion_and_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso f ↔ IsOpenIm
mersion f ∧ Surjective f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isomorphisms_eq_isOpenImmersion_inf_surjective :
    isomorphisms Scheme = (@IsOpenImmersion ⊓ @Surjective : MorphismProperty Scheme) := by
  ext
  rw [isomorphisms.iff, isIso_iff_isOpenImmersion_and_surjective]
  rfl
/-
**AlgebraicGeometry.isomorphisms_eq_stalkwise** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：isomorphisms_eq_stalkwise : isomorphisms Scheme = (isomorphisms TopCat).in
verseImage Scheme.forgetToTop ⊓ stalkwise (fun f => Function.Bijective f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.isomorphisms_eq_isOpenImmersion_inf_surjective`：isomor
phisms_eq_isOpenImmersion_inf_surjective : isomorphisms Scheme = (@IsOpenImmersi
on ⊓ @Surjective : MorphismProperty Scheme)
· 使用定理 `AlgebraicGeometry.isOpenImmersion_eq_inf`：isOpenImmersion_eq_inf : @IsOp
enImmersion = (topologically IsOpenEmbedding) ⊓ stalkwise (Function.Bijective ·)
· 使用引理 `AlgebraicGeometry.surjective_eq_topologically`：surjective_eq_topological
ly : @Surjective = topologically Function.Surjective
· 使用定理 `inf_right_comm`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a 
⊓ b ⊓ c = a ⊓ c ⊓ b
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Topology.IsOpenEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
[tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsOp
enEmbedding f → Topology.IsE…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Homeomorph.isOpenEmbedding`：isOpenEmbedding (h : X ≃ₜ Y) : IsOpenEmbeddi
ng h
· 使用定理 `Homeomorph.surjective`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] (h : X ≃ₜ Y),   Function.Surjective ⇑h
-/
lemma isomorphisms_eq_stalkwise :
    isomorphisms Scheme = (isomorphisms TopCat).inverseImage Scheme.forgetToTop ⊓
      stalkwise (fun f ↦ Function.Bijective f) := by
  rw [isomorphisms_eq_isOpenImmersion_inf_surjective, isOpenImmersion_eq_inf,
    surjective_eq_topologically, inf_right_comm]
  congr 1
  ext X Y f
  exact ⟨fun H ↦ inferInstanceAs (IsIso (TopCat.isoOfHomeo
    (H.1.1.toHomeomorphOfSurjective H.2)).hom), fun (_ : IsIso f.base) ↦
    let e := (TopCat.homeoOfIso <| asIso f.base); ⟨e.isOpenEmbedding, e.surjective⟩⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个示例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsZariskiLocalAtTarget (isomorphisms Scheme) := inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAffineProperty (isomorphisms Scheme) fun X _ f _ ↦ IsAffine X ∧ IsIso (f.appTop) := by
  convert! HasAffineProperty.of_isZariskiLocalAtTarget (isomorphisms Scheme) with X Y f hY
  exact ⟨fun ⟨_, _⟩ ↦ (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map (f.appTop)))),
    fun (_ : IsIso f) ↦ ⟨.of_isIso f, inferInstance⟩⟩
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZariskiLocalAtTarget (monomorphisms Scheme) :=
  diagonal_isomorphisms (C := Scheme).symm ▸ inferInstance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.isIso_SpecMap_iff** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} : IsIso (Spec.map f)
 ↔ Function.Bijective f.hom
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.ConcreteCategory.isIso_iff_bijective`：isIso_iff_bijective
 [(forget C).ReflectsIsomorphisms] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Function.Bi
jective f
· 使用定理 `CategoryTheory.MorphismProperty.isomorphisms.iff`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y),   CategoryTheory.Morph
ismProperty.isomorphisms C f ↔ Categor…
· 使用定理 `CategoryTheory.MorphismProperty.arrow_mk_iso_iff`：arrow_mk_iso_iff (P : 
MorphismProperty C) [RespectsIso P] {W X Y Z : C} {f : W ⟶ X} {g : Y ⟶ Z} (e : A
rrow.mk f ≅ Arrow.mk g) : P f ↔ P g
· 使用定理 `CategoryTheory.MorphismProperty.RespectsIso.isomorphisms`：∀ (C : Type u)
 [inst : CategoryTheory.Category.{v, u} C], (CategoryTheory.MorphismProperty.iso
morphisms C).RespectsIso
· 使用定理 `AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp`：∀ {X Y : Algebraic
Geometry.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f] (U : Y.Opens),   CategoryT
heory.IsIso (AlgebraicGeometry.Scheme.Hom.…
· 使用定理 `AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat`：∀ {R S : CommRingCat}
 (f : R ⟶ S) [CategoryTheory.IsIso f], CategoryTheory.IsIso (AlgebraicGeometry.S
pec.map f)
-/
lemma isIso_SpecMap_iff {R S : CommRingCat.{u}} {f : R ⟶ S} :
    IsIso (Spec.map f) ↔ Function.Bijective f.hom := by
  rw [← ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  rw [← isomorphisms.iff, (isomorphisms _).arrow_mk_iso_iff (arrowIsoΓSpecOfIsAffine f),
    isomorphisms.iff]
  infer_instance

end AlgebraicGeometry

