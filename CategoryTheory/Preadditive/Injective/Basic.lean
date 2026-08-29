/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
module

public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/

@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/--
Definition of `Injective` / `Injective` 的定义

English:
class Injective
  parameters: (J : C)
  axioms and operations (1):
    - factors : forall {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], exists h : Y ⟶ J, f ≫ h = g

中文:
类 单射
  参数: (J : C)
  公理与运算 (1 个):
    - factors : 对任意 {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [单态射 f], 存在 h : Y ⟶ J, f ≫ h = g
-/
class Injective (J : C) : Prop where
  factors : forall {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], exists h : Y ⟶ J, f ≫ h = g

attribute [inherit_doc Injective] Injective.factors

variable (C) in
/--
Definition of `isInjective` / `isInjective` 的定义

English:
abbreviation isInjective
  signature: : ObjectProperty C
  body: Injective

中文:
缩写 isInjective
  签名: : ObjectProperty C
  定义体: Injective

Depends on / 依赖: Injective
-/
abbrev isInjective : ObjectProperty C := Injective

/--
lemma `Limits.IsZero.injective` / 引理 `Limits.IsZero.injective`

English:
lemma Limits.IsZero.injective
  given: {X : C} (h : IsZero X)
  statement: Injective X where
  proof: ⟨h.from_ _, h.eq_of_tgt _ _⟩

中文:
引理 Limits.是零.injective
  条件: {X : C} (h : 是零 X)
  结论: 单射 X where
  证明: ⟨h.from_ _, h.eq_of_tgt _ _⟩

Depends on / 依赖: eq_of_tgt, from_, h.eq_of_tgt, h.from_
-/
lemma Limits.IsZero.injective {X : C} (h : IsZero X) : Injective X where
  factors _ _ _ := ⟨h.from_ _, h.eq_of_tgt _ _⟩

section

/--
Definition of `InjectivePresentation` / `InjectivePresentation` 的定义

English:
structure InjectivePresentation
  parameters: (X : C)
  axioms and operations (4):
    - J : C
    - injective : Injective J  [default: by infer_instance]
    - f : X ⟶ J
    - mono : Mono f  [default: by infer_instance]

中文:
结构 单射呈现
  参数: (X : C)
  公理与运算 (4 个):
    - J : C
    - injective : 单射 J  [默认: by infer_instance]
    - f : X ⟶ J
    - mono : 单态射 f  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
structure InjectivePresentation (X : C) where
  J : C
  injective : Injective J := by infer_instance
  f : X ⟶ J
  mono : Mono f := by infer_instance

open InjectivePresentation in
attribute [inherit_doc InjectivePresentation] J injective f mono

attribute [instance] InjectivePresentation.injective InjectivePresentation.mono

variable (C)

/--
Definition of `EnoughInjectives` / `EnoughInjectives` 的定义

English:
class EnoughInjectives
  parameters: : Prop where
  axioms and operations (1):
    - presentation : forall X : C, Nonempty (InjectivePresentation X)

中文:
类 有足够单射
  参数: : 命题 where
  公理与运算 (1 个):
    - presentation : 对任意 X : C, 非空 (单射呈现 X)
-/
class EnoughInjectives : Prop where
  presentation : forall X : C, Nonempty (InjectivePresentation X)

attribute [inherit_doc EnoughInjectives] EnoughInjectives.presentation

attribute [instance low] EnoughInjectives.presentation

end

namespace Injective

/--
Definition of `factorThru` / `factorThru` 的定义

English:
definition factorThru
  signature: {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f]
  body: (Injective.factors g f).choose

@[reassoc (attr := simp)]

中文:
定义 factorThru
  签名: {J X Y : C} [单射 J] (g : X ⟶ J) (f : X ⟶ Y) [单态射 f]
  定义体: (Injective.factors g f).choose

@[reassoc (attr := simp)]

Depends on / 依赖: Injective, Injective.factors, factors
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).choose

@[reassoc (attr := simp)]
/--
theorem `comp_factorThru` / 定理 `comp_factorThru`

English:
theorem comp_factorThru
  given: {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f]
  proof: (Injective.factors g f).choose_spec

中文:
定理 comp_factorThru
  条件: {J X Y : C} [单射 J] (g : X ⟶ J) (f : X ⟶ Y) [单态射 f]
  证明: (Injective.factors g f).choose_spec

Depends on / 依赖: Injective, Injective.factors, choose_spec, factors
-/
theorem comp_factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] :
    f ≫ factorThru g f = g :=
  (Injective.factors g f).choose_spec

section

open ZeroObject

/--
Instance `zero_injective` / 实例 `zero_injective`

English:
instance zero_injective
  signature: [HasZeroObject C]
  body: (isZero_zero C).injective

中文:
实例 zero_injective
  签名: [有ZeroObject C]
  定义体: (isZero_zero C).injective

Depends on / 依赖: injective, isZero_zero
-/
instance zero_injective [HasZeroObject C] : Injective (0 : C) :=
  (isZero_zero C).injective

end

/--
theorem `of_iso` / 定理 `of_iso`

English:
theorem of_iso
  given: {P Q : C} (i : P ≅ Q) (hP : Injective P)
  statement: Injective Q
  proof: {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine ⟨h ≫ i.hom, ?_⟩
      rw [← Category.assoc]; rw [h_eq]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id] }

中文:
定理 of_iso
  条件: {P Q : C} (i : P ≅ Q) (hP : 单射 P)
  结论: 单射 Q
  证明: {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine ⟨h ≫ i.hom, ?_⟩
      rw [← Category.assoc]; rw [h_eq]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id] }

Depends on / 依赖: Category, Category.assoc, Category.comp_id, Injective, Injective.factors, Iso.inv_hom_id, comp_id, factors, h_eq, i.hom, i.inv, inv_hom_id
-/
theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  {
    factors := fun g f mono => by
      obtain ⟨h, h_eq⟩ := @Injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine ⟨h ≫ i.hom, ?_⟩
      rw [← Category.assoc]; rw [h_eq]; rw [Category.assoc]; rw [Iso.inv_hom_id]; rw [Category.comp_id] }

/--
theorem `iso_iff` / 定理 `iso_iff`

English:
theorem iso_iff
  given: {P Q : C} (i : P ≅ Q)
  statement: Injective P ↔ Injective Q
  proof: ⟨of_iso i, of_iso i.symm⟩

中文:
定理 iso_iff
  条件: {P Q : C} (i : P ≅ Q)
  结论: 单射 P ↔ 单射 Q
  证明: ⟨of_iso i, of_iso i.symm⟩

Depends on / 依赖: i.symm, of_iso
-/
theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
instance (X : Type u₁) [Nonempty X] : Injective X where
  factors g f mono :=
    ⟨↾fun z => by
      classical
      exact
          if h : z in Set.range f then g (Classical.choose h) else Nonempty.some inferInstance, by
      ext y
      classical
      change dite (f y in Set.range f) (fun h => g (Classical.choose h)) _ = _
      split_ifs <;> rename_i h
      · rw [mono_iff_injective] at mono
        simp [mono (Classical.choose_spec h)]
      · exact False.elim (h ⟨y, rfl⟩)⟩

/--
Instance `Type.enoughInjectives` / 实例 `Type.enoughInjectives`

English:
instance Type.enoughInjectives
  signature: : EnoughInjectives (Type u₁) where
  body: Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := ↾WithBot.some
        mono := by
          rw [mono_iff_injective]
          exact WithBot.coe_injective }

中文:
实例 类型.enoughInjectives
  签名: : 有足够单射 (类型u₁) where
  定义体: Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := ↾WithBot.some
        mono := by
          rw [mono_iff_injective]
          exact WithBot.coe_injective }

Depends on / 依赖: Nonempty, Nonempty.intro, WithBot, WithBot.coe_injective, WithBot.some, coe_injective, injective, mono_iff_injective
-/
instance Type.enoughInjectives : EnoughInjectives (Type u₁) where
  presentation X :=
    Nonempty.intro
      { J := WithBot X
        injective := inferInstance
        f := ↾WithBot.some
        mono := by
          rw [mono_iff_injective]
          exact WithBot.coe_injective }

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] : Injective (P ⨯ Q) where
  factors g f mono := by
    use Limits.prod.lift (factorThru (g ≫ Limits.prod.fst) f) (factorThru (g ≫ Limits.prod.snd) f)
    simp only [prod.comp_lift, comp_factorThru]
    ext
    · simp only [prod.lift_fst]
    · simp only [prod.lift_snd]

set_option backward.isDefEq.respectTransparency false in
instance {β : Type v} (c : β -> C) [HasProduct c] [forall b, Injective (c b)] : Injective (∏ᶜ c) where
  factors g f mono := by
    refine ⟨Pi.lift fun b => factorThru (g ≫ Pi.π c _) f, ?_⟩
    ext b
    simp only [Category.assoc, limit.lift_π, Fan.mk_π_app, comp_factorThru]

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where
  factors g f mono := by
    refine ⟨biprod.lift (factorThru (g ≫ biprod.fst) f) (factorThru (g ≫ biprod.snd) f), ?_⟩
    ext
    · simp only [Category.assoc, biprod.lift_fst, comp_factorThru]
    · simp only [Category.assoc, biprod.lift_snd, comp_factorThru]

instance {β : Type v} (c : β -> C) [HasZeroMorphisms C] [HasBiproduct c] [forall b, Injective (c b)] :
    Injective (⨁ c) where
  factors g f mono := by
    refine ⟨biproduct.lift fun b => factorThru (g ≫ biproduct.π _ _) f, ?_⟩
    ext
    simp only [Category.assoc, biproduct.lift_π, comp_factorThru]

instance {P : Cᵒᵖ} [Projective P] : Injective no_index (unop P) where
  factors g f mono :=
    ⟨(@Projective.factorThru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : Cᵒᵖ} [Injective J] : Projective no_index (unop J) where
  factors f e he :=
    ⟨(@factorThru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : C} [Injective J] : Projective (op J) where
  factors f e epi :=
    ⟨(@factorThru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

instance {P : C} [Projective P] : Injective (op P) where
  factors g f mono :=
    ⟨(@Projective.factorThru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

/--
theorem `injective_iff_projective_op` / 定理 `injective_iff_projective_op`

English:
theorem injective_iff_projective_op
  given: {J : C}
  statement: Injective J ↔ Projective (op J)
  proof: ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩

中文:
定理 injective_iff_projective_op
  条件: {J : C}
  结论: 单射 J ↔ 投射 (op J)
  证明: ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩

Depends on / 依赖: Injective
-/
theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun _ => inferInstance, fun _ => show Injective (unop (op J)) from inferInstance⟩

/--
theorem `projective_iff_injective_op` / 定理 `projective_iff_injective_op`

English:
theorem projective_iff_injective_op
  given: {P : C}
  statement: Projective P ↔ Injective (op P)
  proof: ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩

中文:
定理 projective_iff_injective_op
  条件: {P : C}
  结论: 投射 P ↔ 单射 (op P)
  证明: ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩

Depends on / 依赖: Projective
-/
theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun _ => inferInstance, fun _ => show Projective (unop (op P)) from inferInstance⟩

/--
theorem `injective_iff_preservesEpimorphisms_yoneda_obj` / 定理 `injective_iff_preservesEpimorphisms_yoneda_obj`

English:
theorem injective_iff_preservesEpimorphisms_yoneda_obj
  given: (J : C)
  proof: by
  rw [injective_iff_projective_op]; rw [Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  exact Functor.PreservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)

中文:
定理 injective_iff_preservesEpimorphisms_yoneda_obj
  条件: (J : C)
  证明: by
  rw [injective_iff_projective_op]; rw [Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  exact Functor.PreservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)

Depends on / 依赖: Coyoneda, Coyoneda.objOpOp, Functor, Functor.PreservesEpimorphisms.iso_iff, PreservesEpimorphisms, Projective, Projective.projective_iff_preservesEpimorphisms_coyoneda_obj, injective_iff_projective_op, iso_iff, objOpOp, projective_iff_preservesEpimorphisms_coyoneda_obj
-/
theorem injective_iff_preservesEpimorphisms_yoneda_obj (J : C) :
    Injective J ↔ (yoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_projective_op]; rw [Projective.projective_iff_preservesEpimorphisms_coyoneda_obj]
  exact Functor.PreservesEpimorphisms.iso_iff (Coyoneda.objOpOp _)

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]
variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

set_option backward.defeqAttrib.useBackward true in
/--
theorem `injective_of_adjoint` / 定理 `injective_of_adjoint`

English:
theorem injective_of_adjoint
  given: (adj : L ⊣ R) (J : D) [Injective J]
  statement: Injective R.obj J
  proof: ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective
        (by simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit])⟩⟩

中文:
定理 injective_of_adjoint
  条件: (adj : L ⊣ R) (J : D) [单射 J]
  结论: 单射 R.obj J
  证明: ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective
        (by simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit])⟩⟩

Depends on / 依赖: Adjunction, Adjunction.homEquiv_counit, Adjunction.homEquiv_unit, L.map, adj.homEquiv, factorThru, homEquiv, homEquiv_counit, homEquiv_unit, injective, symm.injective
-/
theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : Injective R.obj J :=
  ⟨fun {A} {_} g f im =>
    ⟨adj.homEquiv _ _ (factorThru ((adj.homEquiv A J).symm g) (L.map f)),
      (adj.homEquiv _ _).symm.injective
        (by simp [Adjunction.homEquiv_unit, Adjunction.homEquiv_counit])⟩⟩

end Adjunction

section EnoughInjectives

variable [EnoughInjectives C]

/--
lemma `exists_presentation` / 引理 `exists_presentation`

English:
lemma exists_presentation
  given: (X : C)
  statement: exists (p : InjectivePresentation X), IsZero X -> IsZero p.J
  proof: by
  by_cases h : IsZero X
  · have := h.injective
    exact ⟨{ J := X, f := 𝟙 X}, by tauto⟩
  · exact ⟨(EnoughInjectives.presentation X).some, by tauto⟩

中文:
引理 存在_presentation
  条件: (X : C)
  结论: 存在 (p : 单射呈现 X), 是零 X -> 是零 p.J
  证明: by
  by_cases h : IsZero X
  · have := h.injective
    exact ⟨{ J := X, f := 𝟙 X}, by tauto⟩
  · exact ⟨(EnoughInjectives.presentation X).some, by tauto⟩

Depends on / 依赖: EnoughInjectives, EnoughInjectives.presentation, IsZero, h.injective, injective, presentation
-/
lemma exists_presentation (X : C) : exists (p : InjectivePresentation X), IsZero X -> IsZero p.J := by
  by_cases h : IsZero X
  · have := h.injective
    exact ⟨{ J := X, f := 𝟙 X}, by tauto⟩
  · exact ⟨(EnoughInjectives.presentation X).some, by tauto⟩

/--
Definition of `under` / `under` 的定义

English:
definition under
  signature: (X : C)
  body: (exists_presentation X).choose.J

中文:
定义 under
  签名: (X : C)
  定义体: (exists_presentation X).choose.J

Depends on / 依赖: choose.J, exists_presentation
-/
def under (X : C) : C :=
  (exists_presentation X).choose.J

/--
Instance `injective_under` / 实例 `injective_under`

English:
instance injective_under
  signature: (X : C)
  body: (exists_presentation X).choose.injective

中文:
实例 injective_under
  签名: (X : C)
  定义体: (exists_presentation X).choose.injective

Depends on / 依赖: choose.injective, exists_presentation, injective
-/
instance injective_under (X : C) : Injective (under X) :=
  (exists_presentation X).choose.injective

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: (X : C)
  body: (exists_presentation X).choose.f

中文:
定义 ι
  签名: (X : C)
  定义体: (exists_presentation X).choose.f

Depends on / 依赖: choose.f, exists_presentation
-/
def ι (X : C) : X ⟶ under X :=
  (exists_presentation X).choose.f

/--
Instance `ι_mono` / 实例 `ι_mono`

English:
instance ι_mono
  signature: (X : C)
  body: (exists_presentation X).choose.mono

中文:
实例 ι_mono
  签名: (X : C)
  定义体: (exists_presentation X).choose.mono

Depends on / 依赖: choose.mono, exists_presentation
-/
instance ι_mono (X : C) : Mono (ι X) :=
  (exists_presentation X).choose.mono

/--
lemma `isZero_under` / 引理 `isZero_under`

English:
lemma isZero_under
  given: (X : C) (hX : IsZero X)
  proof: (exists_presentation X).choose_spec hX

中文:
引理 isZero_under
  条件: (X : C) (hX : 是零 X)
  证明: (exists_presentation X).choose_spec hX

Depends on / 依赖: choose_spec, exists_presentation
-/
lemma isZero_under (X : C) (hX : IsZero X) :
    IsZero (under X) :=
  (exists_presentation X).choose_spec hX

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/--
Definition of `syzygies` / `syzygies` 的定义

English:
definition syzygies
  signature: : C
  body: under (cokernel f)
deriving Injective

中文:
定义 syzygies
  签名: : C
  定义体: under (cokernel f)
deriving Injective

Depends on / 依赖: cokernel
-/
def syzygies : C :=
  under (cokernel f)
deriving Injective

/--
Definition of `d` / `d` 的定义

English:
abbreviation d
  signature: : Y ⟶ syzygies f
  body: cokernel.π f ≫ ι (cokernel f)

中文:
缩写 d
  签名: : Y ⟶ syzygies f
  定义体: cokernel.π f ≫ ι (cokernel f)

Depends on / 依赖: cokernel
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)

end

end EnoughInjectives

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EnoughInjectives
  signature: C] : EnoughProjectives Cᵒᵖ
  body: ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩

中文:
实例 [有足够单射
  签名: C] : 有足够投射 Cᵒᵖ
  定义体: ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩

Depends on / 依赖: Injective
-/
instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (unop X)).op}⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [EnoughProjectives
  signature: C] : EnoughInjectives Cᵒᵖ
  body: ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

中文:
实例 [有足够投射
  签名: C] : 有足够单射 Cᵒᵖ
  定义体: ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

Depends on / 依赖: Projective
-/
instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

/--
theorem `enoughProjectives_of_enoughInjectives_op` / 定理 `enoughProjectives_of_enoughInjectives_op`

English:
theorem enoughProjectives_of_enoughInjectives_op
  given: [EnoughInjectives Cᵒᵖ]
  statement: EnoughProjectives C
  proof: ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩

中文:
定理 enoughProjectives_of_enoughInjectives_op
  条件: [有足够单射 Cᵒᵖ]
  结论: 有足够投射 C
  证明: ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩

Depends on / 依赖: Injective
-/
theorem enoughProjectives_of_enoughInjectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨{ p := _, f := (Injective.ι (op X)).unop} ⟩⟩

/--
theorem `enoughInjectives_of_enoughProjectives_op` / 定理 `enoughInjectives_of_enoughProjectives_op`

English:
theorem enoughInjectives_of_enoughProjectives_op
  given: [EnoughProjectives Cᵒᵖ]
  statement: EnoughInjectives C
  proof: ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

中文:
定理 enoughInjectives_of_enoughProjectives_op
  条件: [有足够投射 Cᵒᵖ]
  结论: 有足够单射 C
  证明: ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

Depends on / 依赖: Projective
-/
theorem enoughInjectives_of_enoughProjectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩

end Injective

namespace Adjunction

variable {D : Type*} [Category* D] {F : C ⥤ D} {G : D ⥤ C}

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  given: (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I)
  proof: ⟨fun {X} {Y} f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc]; rw [← G.map_comp]; rw [h]
    simp⟩

中文:
定理 map_injective
  条件: (adj : F ⊣ G) [F.保持Monomorphisms] (I : D) (hI : 单射 I)
  证明: ⟨fun {X} {Y} f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc]; rw [← G.map_comp]; rw [h]
    simp⟩

Depends on / 依赖: F.map, G.map, G.map_comp, adj.counit.app, adj.unit.app, counit, factors, hI.factors, map_comp, unit_naturality_assoc
-/
theorem map_injective (adj : F ⊣ G) [F.PreservesMonomorphisms] (I : D) (hI : Injective I) :
    Injective (G.obj I) :=
  ⟨fun {X} {Y} f g => by
    intro
    rcases hI.factors (F.map f ≫ adj.counit.app _) (F.map g) with ⟨w,h⟩
    use adj.unit.app Y ≫ G.map w
    rw [← unit_naturality_assoc]; rw [← G.map_comp]; rw [h]
    simp⟩

/--
theorem `injective_of_map_injective` / 定理 `injective_of_map_injective`

English:
theorem injective_of_map_injective
  statement: (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D)
  proof: ⟨fun {X} {Y} f g => by
    intro
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    exact G.map_injective (by simpa)⟩

中文:
定理 injective_of_map_injective
  结论: (adj : F ⊣ G) [G.满] [G.忠实] (I : D)
  证明: ⟨fun {X} {Y} f g => by
    intro
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    exact G.map_injective (by simpa)⟩

Depends on / 依赖: F.map, G.map, G.map_injective, PreservesLimitsOfSize, adj.counit.app, adj.rightAdjoint_preservesLimits, counit, factors, hI.factors, map_injective, rightAdjoint_preservesLimits
-/
theorem injective_of_map_injective (adj : F ⊣ G) [G.Full] [G.Faithful] (I : D)
    (hI : Injective (G.obj I)) : Injective I :=
  ⟨fun {X} {Y} f g => by
    intro
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits
    rcases hI.factors (G.map f) (G.map g) with ⟨w,h⟩
    use inv (adj.counit.app _) ≫ F.map w ≫ adj.counit.app _
    exact G.map_injective (by simpa)⟩

/--
Definition of `mapInjectivePresentation` / `mapInjectivePresentation` 的定义

English:
definition mapInjectivePresentation
  signature: (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
  body: G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits; infer_instance

中文:
定义 mapInjectivePresentation
  签名: (adj : F ⊣ G) [F.保持Monomorphisms] (X : D)
  定义体: G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits; infer_instance

Depends on / 依赖: G.obj
-/
def mapInjectivePresentation (adj : F ⊣ G) [F.PreservesMonomorphisms] (X : D)
    (I : InjectivePresentation X) : InjectivePresentation (G.obj X) where
  J := G.obj I.J
  injective := adj.map_injective _ I.injective
  f := G.map I.f
  mono := by
    have : PreservesLimitsOfSize.{0, 0} G := adj.rightAdjoint_preservesLimits; infer_instance

/--
Definition of `injectivePresentationOfMap` / `injectivePresentationOfMap` 的定义

English:
definition injectivePresentationOfMap
  signature: (adj : F ⊣ G)
  body: G.obj I.J
  injective := Injective.injective_of_adjoint adj _
  f := adj.homEquiv _ _ I.f

中文:
定义 injectivePresentationOfMap
  签名: (adj : F ⊣ G)
  定义体: G.obj I.J
  injective := Injective.injective_of_adjoint adj _
  f := adj.homEquiv _ _ I.f

Depends on / 依赖: G.obj
-/
def injectivePresentationOfMap (adj : F ⊣ G)
    [F.PreservesMonomorphisms] [F.ReflectsMonomorphisms] (X : C)
    (I : InjectivePresentation <| F.obj X) :
    InjectivePresentation X where
  J := G.obj I.J
  injective := Injective.injective_of_adjoint adj _
  f := adj.homEquiv _ _ I.f

end Adjunction

namespace Functor

variable {D : Type*} [Category* D] (F : C ⥤ D)

/--
theorem `injective_of_map_injective` / 定理 `injective_of_map_injective`

English:
theorem injective_of_map_injective
  statement: [F.Full] [F.Faithful]
  proof: by
    obtain ⟨h, fac⟩ := hI.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

中文:
定理 injective_of_map_injective
  结论: [F.满] [F.忠实]
  证明: by
    obtain ⟨h, fac⟩ := hI.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

Depends on / 依赖: F.map, F.map_injective, F.preimage, factors, hI.factors, map_injective, preimage
-/
theorem injective_of_map_injective [F.Full] [F.Faithful]
    [F.PreservesMonomorphisms] {I : C} (hI : Injective (F.obj I)) : Injective I where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hI.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

/--
lemma `EnoughInjectives.of_adjunction` / 引理 `EnoughInjectives.of_adjunction`

English:
lemma EnoughInjectives.of_adjunction
  statement: {C : Type u₁} {D : Type u₂}
  proof: ⟨adj.injectivePresentationOfMap _ (EnoughInjectives.presentation _).some⟩

中文:
引理 有足够单射.of_adjunction
  结论: {C : 类型u₁} {D : 类型u₂}
  证明: ⟨adj.injectivePresentationOfMap _ (EnoughInjectives.presentation _).some⟩

Depends on / 依赖: EnoughInjectives, EnoughInjectives.presentation, adj.injectivePresentationOfMap, injectivePresentationOfMap, presentation
-/
lemma EnoughInjectives.of_adjunction {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) [L.PreservesMonomorphisms] [L.ReflectsMonomorphisms]
    [EnoughInjectives D] : EnoughInjectives C where
  presentation _ :=
    ⟨adj.injectivePresentationOfMap _ (EnoughInjectives.presentation _).some⟩

/--
lemma `EnoughInjectives.of_equivalence` / 引理 `EnoughInjectives.of_equivalence`

English:
lemma EnoughInjectives.of_equivalence
  statement: {C : Type u₁} {D : Type u₂}
  proof: EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

中文:
引理 有足够单射.of_equivalence
  结论: {C : 类型u₁} {D : 类型u₂}
  证明: EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

Depends on / 依赖: EnoughInjectives, EnoughInjectives.of_adjunction, asEquivalence, e.asEquivalence.toAdjunction, of_adjunction, toAdjunction
-/
lemma EnoughInjectives.of_equivalence {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    (e : C ⥤ D) [e.IsEquivalence] [EnoughInjectives D] : EnoughInjectives C :=
  EnoughInjectives.of_adjunction (adj := e.asEquivalence.toAdjunction)

namespace Equivalence

variable {D : Type*} [Category* D] (F : C ≌ D)

/--
theorem `map_injective_iff` / 定理 `map_injective_iff`

English:
theorem map_injective_iff
  given: (P : C)
  statement: Injective (F.functor.obj P) ↔ Injective P
  proof: ⟨F.symm.toAdjunction.injective_of_map_injective P, F.symm.toAdjunction.map_injective P⟩

中文:
定理 map_injective_iff
  条件: (P : C)
  结论: 单射 (F.functor.obj P) ↔ 单射 P
  证明: ⟨F.symm.toAdjunction.injective_of_map_injective P, F.symm.toAdjunction.map_injective P⟩

Depends on / 依赖: F.symm.toAdjunction.injective_of_map_injective, F.symm.toAdjunction.map_injective, injective_of_map_injective, map_injective, toAdjunction
-/
theorem map_injective_iff (P : C) : Injective (F.functor.obj P) ↔ Injective P :=
  ⟨F.symm.toAdjunction.injective_of_map_injective P, F.symm.toAdjunction.map_injective P⟩

/--
Definition of `injectivePresentationOfMapInjectivePresentation` / `injectivePresentationOfMapInjectivePresentation` 的定义

English:
definition injectivePresentationOfMapInjectivePresentation
  signature: (X : C)
  body: F.toAdjunction.injectivePresentationOfMap _ I

中文:
定义 injectivePresentationOfMapInjectivePresentation
  签名: (X : C)
  定义体: F.toAdjunction.injectivePresentationOfMap _ I

Depends on / 依赖: F.toAdjunction.injectivePresentationOfMap, injectivePresentationOfMap, toAdjunction
-/
def injectivePresentationOfMapInjectivePresentation (X : C)
    (I : InjectivePresentation (F.functor.obj X)) : InjectivePresentation X :=
  F.toAdjunction.injectivePresentationOfMap _ I

/--
theorem `enoughInjectives_iff` / 定理 `enoughInjectives_iff`

English:
theorem enoughInjectives_iff
  given: (F : C ≌ D)
  statement: EnoughInjectives C ↔ EnoughInjectives D
  proof: ⟨fun h => h.of_adjunction F.symm.toAdjunction, fun h => h.of_adjunction F.toAdjunction⟩

中文:
定理 enoughInjectives_iff
  条件: (F : C ≌ D)
  结论: 有足够单射 C ↔ 有足够单射 D
  证明: ⟨fun h => h.of_adjunction F.symm.toAdjunction, fun h => h.of_adjunction F.toAdjunction⟩

Depends on / 依赖: F.symm.toAdjunction, F.toAdjunction, h.of_adjunction, of_adjunction, toAdjunction
-/
theorem enoughInjectives_iff (F : C ≌ D) : EnoughInjectives C ↔ EnoughInjectives D :=
  ⟨fun h => h.of_adjunction F.symm.toAdjunction, fun h => h.of_adjunction F.toAdjunction⟩

end Equivalence

/--
lemma `Retract.injective` / 引理 `Retract.injective`

English:
lemma Retract.injective
  given: {X Y : C} (h : Retract X Y) [i : Injective Y]
  statement: Injective X
  proof: by
  refine Injective.mk (fun {A B} f e _ => ?_)
  rcases i.factors (f ≫ h.i) e with ⟨g, hg⟩
  use g ≫ h.r
  simp [Category.assoc', hg]

中文:
引理 收缩.injective
  条件: {X Y : C} (h : 收缩 X Y) [i : 单射 Y]
  结论: 单射 X
  证明: by
  refine Injective.mk (fun {A B} f e _ => ?_)
  rcases i.factors (f ≫ h.i) e with ⟨g, hg⟩
  use g ≫ h.r
  simp [Category.assoc', hg]

Depends on / 依赖: Category, Category.assoc, Injective, Injective.mk, factors, i.factors
-/
lemma Retract.injective {X Y : C} (h : Retract X Y) [i : Injective Y] : Injective X := by
  refine Injective.mk (fun {A B} f e _ => ?_)
  rcases i.factors (f ≫ h.i) e with ⟨g, hg⟩
  use g ≫ h.r
  simp [Category.assoc', hg]

end CategoryTheory
