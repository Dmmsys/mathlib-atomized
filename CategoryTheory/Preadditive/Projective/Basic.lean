/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts

/-!
# Projective objects and categories with enough projectives

An object `P` is called *projective* if every morphism out of `P` factors through every epimorphism.

A category `C` *has enough projectives* if every object admits an epimorphism from some
projective object.

`CategoryTheory.Projective.over X` picks an arbitrary such projective object, and
`CategoryTheory.Projective.π X : CategoryTheory.Projective.over X ⟶ X` is the corresponding
epimorphism.

Given a morphism `f : X ⟶ Y`, `CategoryTheory.Projective.left f` is a projective object over
`CategoryTheory.Limits.kernel f`, and `Projective.d f : Projective.left f ⟶ X` is the morphism
`π (kernel f) ≫ kernel.ι f`.

-/

@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite

universe v u v' u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/--
Definition of `Projective` / `Projective` 的定义

English:
class Projective
  parameters: (P : C)
  axioms and operations (1):
    - factors : forall {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], exists f', f' ≫ e = f

中文:
类 投射
  参数: (P : C)
  公理与运算 (1 个):
    - factors : 对任意 {E X : C} (f : P ⟶ X) (e : E ⟶ X) [满态射 e], 存在 f', f' ≫ e = f
-/
class Projective (P : C) : Prop where
  factors : forall {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], exists f', f' ≫ e = f

variable (C) in
/--
Definition of `isProjective` / `isProjective` 的定义

English:
abbreviation isProjective
  signature: : ObjectProperty C
  body: Projective

中文:
缩写 isProjective
  签名: : ObjectProperty C
  定义体: Projective

Depends on / 依赖: Projective
-/
abbrev isProjective : ObjectProperty C := Projective

/--
lemma `Limits.IsZero.projective` / 引理 `Limits.IsZero.projective`

English:
lemma Limits.IsZero.projective
  given: {X : C} (h : IsZero X)
  statement: Projective X where
  proof: ⟨h.to_ _, h.eq_of_src _ _⟩

中文:
引理 Limits.是零.projective
  条件: {X : C} (h : 是零 X)
  结论: 投射 X where
  证明: ⟨h.to_ _, h.eq_of_src _ _⟩

Depends on / 依赖: eq_of_src, h.eq_of_src, h.to_
-/
lemma Limits.IsZero.projective {X : C} (h : IsZero X) : Projective X where
  factors _ _ _ := ⟨h.to_ _, h.eq_of_src _ _⟩

section

/--
Definition of `ProjectivePresentation` / `ProjectivePresentation` 的定义

English:
structure ProjectivePresentation
  parameters: (X : C)
  axioms and operations (4):
    - p : C
    - [projective : Projective p]
    - f : p ⟶ X
    - [epi : Epi f]

中文:
结构 投射呈现
  参数: (X : C)
  公理与运算 (4 个):
    - p : C
    - [projective : 投射 p]
    - f : p ⟶ X
    - [epi : 满态射 f]
-/
structure ProjectivePresentation (X : C) where
  /-- The projective object `p` of this presentation -/
  p : C
  [projective : Projective p]
  /-- The epimorphism from `p` of this presentation -/
  f : p ⟶ X
  [epi : Epi f]

attribute [instance] ProjectivePresentation.projective ProjectivePresentation.epi

variable (C)

/--
Definition of `EnoughProjectives` / `EnoughProjectives` 的定义

English:
class EnoughProjectives
  parameters: : Prop where
  axioms and operations (1):
    - presentation : forall X : C, Nonempty (ProjectivePresentation X)

中文:
类 有足够投射
  参数: : 命题 where
  公理与运算 (1 个):
    - presentation : 对任意 X : C, 非空 (投射呈现 X)
-/
class EnoughProjectives : Prop where
  presentation : forall X : C, Nonempty (ProjectivePresentation X)

attribute [instance low] EnoughProjectives.presentation

end

namespace Projective

/--
Definition of `factorThru` / `factorThru` 的定义

English:
definition factorThru
  signature: {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e]
  body: (Projective.factors f e).choose

@[reassoc (attr := simp)]

中文:
定义 factorThru
  签名: {P X E : C} [投射 P] (f : P ⟶ X) (e : E ⟶ X) [满态射 e]
  定义体: (Projective.factors f e).choose

@[reassoc (attr := simp)]

Depends on / 依赖: Projective, Projective.factors, factors
-/
def factorThru {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] : P ⟶ E :=
  (Projective.factors f e).choose

@[reassoc (attr := simp)]
/--
theorem `factorThru_comp` / 定理 `factorThru_comp`

English:
theorem factorThru_comp
  given: {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e]
  proof: (Projective.factors f e).choose_spec

中文:
定理 factorThru_comp
  条件: {P X E : C} [投射 P] (f : P ⟶ X) (e : E ⟶ X) [满态射 e]
  证明: (Projective.factors f e).choose_spec

Depends on / 依赖: Projective, Projective.factors, choose_spec, factors
-/
theorem factorThru_comp {P X E : C} [Projective P] (f : P ⟶ X) (e : E ⟶ X) [Epi e] :
    factorThru f e ≫ e = f :=
  (Projective.factors f e).choose_spec

section

open ZeroObject

/--
Instance `zero_projective` / 实例 `zero_projective`

English:
instance zero_projective
  signature: [HasZeroObject C]
  body: (isZero_zero C).projective

中文:
实例 zero_projective
  签名: [有ZeroObject C]
  定义体: (isZero_zero C).projective

Depends on / 依赖: isZero_zero, projective
-/
instance zero_projective [HasZeroObject C] : Projective (0 : C) :=
  (isZero_zero C).projective

end

/--
theorem `of_iso` / 定理 `of_iso`

English:
theorem of_iso
  given: {P Q : C} (i : P ≅ Q) (_ : Projective P)
  statement: Projective Q where
  proof: let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩

中文:
定理 of_iso
  条件: {P Q : C} (i : P ≅ Q) (_ : 投射 P)
  结论: 投射 Q where
  证明: let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩

Depends on / 依赖: Projective, Projective.factors, factors, i.hom, i.inv
-/
theorem of_iso {P Q : C} (i : P ≅ Q) (_ : Projective P) : Projective Q where
  factors f e _ :=
    let ⟨f', hf'⟩ := Projective.factors (i.hom ≫ f) e
    ⟨i.inv ≫ f', by simp [hf']⟩

/--
theorem `iso_iff` / 定理 `iso_iff`

English:
theorem iso_iff
  given: {P Q : C} (i : P ≅ Q)
  statement: Projective P ↔ Projective Q
  proof: ⟨of_iso i, of_iso i.symm⟩

中文:
定理 iso_iff
  条件: {P Q : C} (i : P ≅ Q)
  结论: 投射 P ↔ 投射 Q
  证明: ⟨of_iso i, of_iso i.symm⟩

Depends on / 依赖: i.symm, of_iso
-/
theorem iso_iff {P Q : C} (i : P ≅ Q) : Projective P ↔ Projective Q :=
  ⟨of_iso i, of_iso i.symm⟩

/-- The axiom of choice says that every type is a projective object in `Type`. -/
instance (X : Type u) : Projective X where
  factors f e _ :=
    have he : Function.Surjective e := surjective_of_epi e
    ⟨↾fun x => (he (f x)).choose, by ext x; exact (he (f x)).choose_spec⟩

/--
Instance `Type.enoughProjectives` / 实例 `Type.enoughProjectives`

English:
instance Type.enoughProjectives
  signature: : EnoughProjectives (Type u) where
  body: ⟨⟨X, 𝟙 X⟩⟩

中文:
实例 类型.enoughProjectives
  签名: : 有足够投射 (类型u) where
  定义体: ⟨⟨X, 𝟙 X⟩⟩
-/
instance Type.enoughProjectives : EnoughProjectives (Type u) where
  presentation X := ⟨⟨X, 𝟙 X⟩⟩

set_option backward.isDefEq.respectTransparency false in
instance {P Q : C} [HasBinaryCoproduct P Q] [Projective P] [Projective Q] : Projective (P ⨿ Q) where
  factors f e epi := ⟨coprod.desc (factorThru (coprod.inl ≫ f) e) (factorThru (coprod.inr ≫ f) e),
    by cat_disch⟩

set_option backward.isDefEq.respectTransparency false in
instance {β : Type v} (g : β -> C) [HasCoproduct g] [forall b, Projective (g b)] : Projective (∐ g) where
  factors f e epi := ⟨Sigma.desc fun b => factorThru (Sigma.ι g b ≫ f) e, by cat_disch⟩

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Projective P] [Projective Q] :
    Projective (P ⊞ Q) where
  factors f e epi := ⟨biprod.desc (factorThru (biprod.inl ≫ f) e) (factorThru (biprod.inr ≫ f) e),
    by cat_disch⟩

instance {β : Type v} (g : β -> C) [HasZeroMorphisms C] [HasBiproduct g] [forall b, Projective (g b)] :
    Projective (⨁ g) where
  factors f e epi := ⟨biproduct.desc fun b => factorThru (biproduct.ι g b ≫ f) e, by cat_disch⟩

/--
theorem `projective_iff_preservesEpimorphisms_coyoneda_obj` / 定理 `projective_iff_preservesEpimorphisms_coyoneda_obj`

English:
theorem projective_iff_preservesEpimorphisms_coyoneda_obj
  given: (P : C)
  proof: ⟨fun hP =>
    ⟨fun f _ =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factorThru g f, factorThru_comp _ _⟩⟩,
    fun _ =>
    ⟨fun f e _ =>
      (epi_iff_surjective _).1 (inferInstance : Epi ((coyoneda.obj (op P)).map e)) f⟩⟩

中文:
定理 projective_iff_preservesEpimorphisms_coyoneda_obj
  条件: (P : C)
  证明: ⟨fun hP =>
    ⟨fun f _ =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factorThru g f, factorThru_comp _ _⟩⟩,
    fun _ =>
    ⟨fun f e _ =>
      (epi_iff_surjective _).1 (inferInstance : Epi ((coyoneda.obj (op P)).map e)) f⟩⟩

Depends on / 依赖: Projective, coyoneda, coyoneda.obj, epi_iff_surjective, factorThru, factorThru_comp
-/
theorem projective_iff_preservesEpimorphisms_coyoneda_obj (P : C) :
    Projective P ↔ (coyoneda.obj (op P)).PreservesEpimorphisms :=
  ⟨fun hP =>
    ⟨fun f _ =>
      (epi_iff_surjective _).2 fun g =>
        have : Projective (unop (op P)) := hP
        ⟨factorThru g f, factorThru_comp _ _⟩⟩,
    fun _ =>
    ⟨fun f e _ =>
      (epi_iff_surjective _).1 (inferInstance : Epi ((coyoneda.obj (op P)).map e)) f⟩⟩

section EnoughProjectives

variable [EnoughProjectives C]

/--
Definition of `over` / `over` 的定义

English:
definition over
  signature: (X : C)
  body: (EnoughProjectives.presentation X).some.p

中文:
定义 over
  签名: (X : C)
  定义体: (EnoughProjectives.presentation X).some.p

Depends on / 依赖: EnoughProjectives, EnoughProjectives.presentation, presentation, some.p
-/
def over (X : C) : C :=
  (EnoughProjectives.presentation X).some.p

/--
Instance `projective_over` / 实例 `projective_over`

English:
instance projective_over
  signature: (X : C)
  body: (EnoughProjectives.presentation X).some.projective

中文:
实例 projective_over
  签名: (X : C)
  定义体: (EnoughProjectives.presentation X).some.projective

Depends on / 依赖: EnoughProjectives, EnoughProjectives.presentation, presentation, projective, some.projective
-/
instance projective_over (X : C) : Projective (over X) :=
  (EnoughProjectives.presentation X).some.projective

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: (X : C)
  body: (EnoughProjectives.presentation X).some.f

中文:
定义 π
  签名: (X : C)
  定义体: (EnoughProjectives.presentation X).some.f

Depends on / 依赖: EnoughProjectives, EnoughProjectives.presentation, presentation, some.f
-/
def π (X : C) : over X ⟶ X :=
  (EnoughProjectives.presentation X).some.f

/--
Instance `π_epi` / 实例 `π_epi`

English:
instance π_epi
  signature: (X : C)
  body: (EnoughProjectives.presentation X).some.epi

中文:
实例 π_epi
  签名: (X : C)
  定义体: (EnoughProjectives.presentation X).some.epi

Depends on / 依赖: EnoughProjectives, EnoughProjectives.presentation, presentation, some.epi
-/
instance π_epi (X : C) : Epi (π X) :=
  (EnoughProjectives.presentation X).some.epi

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasKernel f]

/--
Definition of `syzygies` / `syzygies` 的定义

English:
definition syzygies
  signature: : C
  body: over (kernel f)

中文:
定义 syzygies
  签名: : C
  定义体: over (kernel f)

Depends on / 依赖: kernel
-/
def syzygies : C := over (kernel f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Projective (syzygies f)
  body: inferInstanceAs (Projective (over _))

中文:
实例 :
  签名: 投射 (syzygies f)
  定义体: inferInstanceAs (Projective (over _))

Depends on / 依赖: Projective
-/
instance : Projective (syzygies f) := inferInstanceAs (Projective (over _))

/--
Definition of `d` / `d` 的定义

English:
abbreviation d
  signature: : syzygies f ⟶ X
  body: π (kernel f) ≫ kernel.ι f

中文:
缩写 d
  签名: : syzygies f ⟶ X
  定义体: π (kernel f) ≫ kernel.ι f

Depends on / 依赖: kernel
-/
abbrev d : syzygies f ⟶ X :=
  π (kernel f) ≫ kernel.ι f

end

end EnoughProjectives

end Projective

namespace Adjunction

variable {D : Type u'} [Category.{v'} D] {F : C ⥤ D} {G : D ⥤ C}

set_option backward.defeqAttrib.useBackward true in
/--
theorem `map_projective` / 定理 `map_projective`

English:
theorem map_projective
  given: (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P)
  proof: by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    use F.map f' ≫ adj.counit.app _
    rw [Category.assoc]; rw [← Adjunction.counit_naturality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [hf']
    simp

中文:
定理 map_projective
  条件: (adj : F ⊣ G) [G.保持Epimorphisms] (P : C) (hP : 投射 P)
  证明: by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    use F.map f' ≫ adj.counit.app _
    rw [Category.assoc]; rw [← Adjunction.counit_naturality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [hf']
    simp

Depends on / 依赖: Adjunction, Adjunction.counit_naturality, Category, Category.assoc, F.map, F.map_comp, G.map, adj.counit.app, adj.unit.app, counit, counit_naturality, factors, hP.factors, map_comp
-/
theorem map_projective (adj : F ⊣ G) [G.PreservesEpimorphisms] (P : C) (hP : Projective P) :
    Projective (F.obj P) where
  factors f g _ := by
    rcases hP.factors (adj.unit.app P ≫ G.map f) (G.map g) with ⟨f', hf'⟩
    use F.map f' ≫ adj.counit.app _
    rw [Category.assoc]; rw [← Adjunction.counit_naturality]; rw [← Category.assoc]; rw [← F.map_comp]; rw [hf']
    simp

/--
theorem `projective_of_map_projective` / 定理 `projective_of_map_projective`

English:
theorem projective_of_map_projective
  statement: (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C)
  proof: by
    have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    exact F.map_injective (by simpa)

中文:
定理 projective_of_map_projective
  结论: (adj : F ⊣ G) [F.满] [F.忠实] (P : C)
  证明: by
    have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    exact F.map_injective (by simpa)

Depends on / 依赖: Adjunction, Adjunction.leftAdjoint_preservesColimits, F.map, F.map_injective, G.map, adj.unit.app, leftAdjoint_preservesColimits, map_injective
-/
theorem projective_of_map_projective (adj : F ⊣ G) [F.Full] [F.Faithful] (P : C)
    (hP : Projective (F.obj P)) : Projective P where
  factors f g _ := by
    have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj
    rcases (@hP).1 (F.map f) (F.map g) with ⟨f', hf'⟩
    use adj.unit.app _ ≫ G.map f' ≫ (inv <| adj.unit.app _)
    exact F.map_injective (by simpa)

/--
Definition of `mapProjectivePresentation` / `mapProjectivePresentation` 的定义

English:
definition mapProjectivePresentation
  signature: (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
  body: F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj; inferInstance

中文:
定义 mapProjectivePresentation
  签名: (adj : F ⊣ G) [G.保持Epimorphisms] (X : C)
  定义体: F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj; inferInstance

Depends on / 依赖: F.obj
-/
def mapProjectivePresentation (adj : F ⊣ G) [G.PreservesEpimorphisms] (X : C)
    (Y : ProjectivePresentation X) : ProjectivePresentation (F.obj X) where
  p := F.obj Y.p
  projective := adj.map_projective _ Y.projective
  f := F.map Y.f
  epi := have := Adjunction.leftAdjoint_preservesColimits.{0, 0} adj; inferInstance

end Adjunction

namespace Functor

variable {D : Type*} [Category* D] (F : C ⥤ D)

/--
theorem `projective_of_map_projective` / 定理 `projective_of_map_projective`

English:
theorem projective_of_map_projective
  statement: [F.Full] [F.Faithful]
  proof: by
    obtain ⟨h, fac⟩ := hP.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

中文:
定理 projective_of_map_projective
  结论: [F.满] [F.忠实]
  证明: by
    obtain ⟨h, fac⟩ := hP.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

Depends on / 依赖: F.map, F.map_injective, F.preimage, factors, hP.factors, map_injective, preimage
-/
theorem projective_of_map_projective [F.Full] [F.Faithful]
    [F.PreservesEpimorphisms] {P : C} (hP : Projective (F.obj P)) : Projective P where
  factors g f _ := by
    obtain ⟨h, fac⟩ := hP.factors (F.map g) (F.map f)
    exact ⟨F.preimage h, F.map_injective (by simp [fac])⟩

end Functor

namespace Equivalence

variable {D : Type u'} [Category.{v'} D] (F : C ≌ D)

/--
theorem `map_projective_iff` / 定理 `map_projective_iff`

English:
theorem map_projective_iff
  given: (P : C)
  statement: Projective (F.functor.obj P) ↔ Projective P
  proof: ⟨F.toAdjunction.projective_of_map_projective P, F.toAdjunction.map_projective P⟩

中文:
定理 map_projective_iff
  条件: (P : C)
  结论: 投射 (F.functor.obj P) ↔ 投射 P
  证明: ⟨F.toAdjunction.projective_of_map_projective P, F.toAdjunction.map_projective P⟩

Depends on / 依赖: F.toAdjunction.map_projective, F.toAdjunction.projective_of_map_projective, map_projective, projective_of_map_projective, toAdjunction
-/
theorem map_projective_iff (P : C) : Projective (F.functor.obj P) ↔ Projective P :=
  ⟨F.toAdjunction.projective_of_map_projective P, F.toAdjunction.map_projective P⟩

/--
Definition of `projectivePresentationOfMapProjectivePresentation` / `projectivePresentationOfMapProjectivePresentation` 的定义

English:
definition projectivePresentationOfMapProjectivePresentation
  signature: (X : C)
  body: F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _

中文:
定义 projectivePresentationOfMapProjectivePresentation
  签名: (X : C)
  定义体: F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _

Depends on / 依赖: F.inverse.obj, inverse
-/
def projectivePresentationOfMapProjectivePresentation (X : C)
    (Y : ProjectivePresentation (F.functor.obj X)) : ProjectivePresentation X where
  p := F.inverse.obj Y.p
  projective := Adjunction.map_projective F.symm.toAdjunction Y.p Y.projective
  f := F.inverse.map Y.f ≫ F.unitInv.app _
  epi := epi_comp _ _

/--
theorem `enoughProjectives_iff` / 定理 `enoughProjectives_iff`

English:
theorem enoughProjectives_iff
  given: (F : C ≌ D)
  statement: EnoughProjectives C ↔ EnoughProjectives D
  proof: by
  constructor
  all_goals intro H; constructor; intro X; constructor
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
      (Nonempty.some (H.presentation (F.functor.obj X)))

中文:
定理 enoughProjectives_iff
  条件: (F : C ≌ D)
  结论: 有足够投射 C ↔ 有足够投射 D
  证明: by
  constructor
  all_goals intro H; constructor; intro X; constructor
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
      (Nonempty.some (H.presentation (F.functor.obj X)))

Depends on / 依赖: F.functor.obj, F.inverse.obj, F.projectivePresentationOfMapProjectivePresentation, F.symm.projectivePresentationOfMapProjectivePresentation, H.presentation, Nonempty, Nonempty.some, all_goals, functor, inverse, presentation, projectivePresentationOfMapProjectivePresentation
-/
theorem enoughProjectives_iff (F : C ≌ D) : EnoughProjectives C ↔ EnoughProjectives D := by
  constructor
  all_goals intro H; constructor; intro X; constructor
  · exact F.symm.projectivePresentationOfMapProjectivePresentation _
      (Nonempty.some (H.presentation (F.inverse.obj X)))
  · exact F.projectivePresentationOfMapProjectivePresentation X
      (Nonempty.some (H.presentation (F.functor.obj X)))

end Equivalence

/--
lemma `Retract.projective` / 引理 `Retract.projective`

English:
lemma Retract.projective
  given: {X Y : C} (h : Retract X Y) [p : Projective Y]
  statement: Projective X
  proof: by
  refine Projective.mk (fun {A B} f e _ => ?_)
  rcases p.factors (h.r ≫ f) e with ⟨g, hg⟩
  use h.i ≫ g
  simp [hg]

中文:
引理 收缩.projective
  条件: {X Y : C} (h : 收缩 X Y) [p : 投射 Y]
  结论: 投射 X
  证明: by
  refine Projective.mk (fun {A B} f e _ => ?_)
  rcases p.factors (h.r ≫ f) e with ⟨g, hg⟩
  use h.i ≫ g
  simp [hg]

Depends on / 依赖: Projective, Projective.mk, factors, p.factors
-/
lemma Retract.projective {X Y : C} (h : Retract X Y) [p : Projective Y] : Projective X := by
  refine Projective.mk (fun {A B} f e _ => ?_)
  rcases p.factors (h.r ≫ f) e with ⟨g, hg⟩
  use h.i ≫ g
  simp [hg]

end CategoryTheory
