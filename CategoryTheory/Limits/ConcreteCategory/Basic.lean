/-
Copyright (c) 2017 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Adam Topaz
-/
module

public import Mathlib.CategoryTheory.ConcreteCategory.Forget
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Images
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# Facts about (co)limits of functors into concrete categories
-/

public section


universe s t w v u r

open CategoryTheory

namespace CategoryTheory.Types

open Limits


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget <| Type u).Full
  body: Functor.Full.id

中文:
实例 :
  签名: (forget <| 类型u).Full
  定义体: Functor.Full.id

Depends on / 依赖: Functor, Functor.Full.id
-/
instance : (forget <| Type u).Full :=
  Functor.Full.id

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimitsOfSize (forget <| Type u)
  body: id_preservesLimitsOfSize

中文:
实例 :
  签名: PreservesLimitsOfSize (forget <| 类型u)
  定义体: id_preservesLimitsOfSize

Depends on / 依赖: id_preservesLimitsOfSize
-/
instance : PreservesLimitsOfSize (forget <| Type u) :=
  id_preservesLimitsOfSize
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesColimitsOfSize (forget <| Type u)
  body: id_preservesColimitsOfSize

中文:
实例 :
  签名: PreservesColimitsOfSize (forget <| 类型u)
  定义体: id_preservesColimitsOfSize

Depends on / 依赖: id_preservesColimitsOfSize
-/
instance : PreservesColimitsOfSize (forget <| Type u) :=
  id_preservesColimitsOfSize

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsLimitsOfSize (forget <| Type u)
  body: id_reflectsLimits

中文:
实例 :
  签名: ReflectsLimitsOfSize (forget <| 类型u)
  定义体: id_reflectsLimits

Depends on / 依赖: id_reflectsLimits
-/
instance : ReflectsLimitsOfSize (forget <| Type u) :=
  id_reflectsLimits
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: ReflectsColimitsOfSize (forget <| Type u)
  body: id_reflectsColimits

中文:
实例 :
  签名: ReflectsColimitsOfSize (forget <| 类型u)
  定义体: id_reflectsColimits

Depends on / 依赖: id_reflectsColimits
-/
instance : ReflectsColimitsOfSize (forget <| Type u) :=
  id_reflectsColimits

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget <| Type u).IsEquivalence
  body: Functor.isEquivalence_refl

中文:
实例 :
  签名: (forget <| 类型u).IsEquivalence
  定义体: Functor.isEquivalence_refl

Depends on / 依赖: Functor, Functor.isEquivalence_refl, isEquivalence_refl
-/
instance : (forget <| Type u).IsEquivalence :=
  Functor.isEquivalence_refl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (forget <| Type u).IsCorepresentable
  body: inferInstanceAs (𝟭 <| Type u).IsCorepresentable

中文:
实例 :
  签名: (forget <| 类型u).IsCorepresentable
  定义体: inferInstanceAs (𝟭 <| Type u).IsCorepresentable

Depends on / 依赖: IsCorepresentable
-/
instance : (forget <| Type u).IsCorepresentable :=
  inferInstanceAs (𝟭 <| Type u).IsCorepresentable

end CategoryTheory.Types

namespace CategoryTheory.Limits.Concrete

section Limits

/--
lemma `small_sections_of_hasLimit` / 引理 `small_sections_of_hasLimit`

English:
lemma small_sections_of_hasLimit
  proof: by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

中文:
引理 small_sections_of_hasLimit
  证明: by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

Depends on / 依赖: Types.hasLimit_iff_small_sections, hasLimit_iff_small_sections, infer_instance
-/
lemma small_sections_of_hasLimit
    {C : Type u} [Category.{v} C] {FC : outParam <| C -> C -> Type*} {CC : outParam <| C -> Type v}
    [outParam <| forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [(forget C).IsCorepresentable] {J : Type w} [Category.{t} J] (G : J ⥤ C) [HasLimit G] :
    Small.{v} (G ⋙ forget C).sections := by
  rw [← Types.hasLimit_iff_small_sections]
  infer_instance

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type r}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{r} C FC]
variable {J : Type w} [Category.{t} J] (F : J ⥤ C) [PreservesLimit F (forget C)]

/--
theorem `to_product_injective_of_isLimit` / 定理 `to_product_injective_of_isLimit`

English:
theorem to_product_injective_of_isLimit
  proof: by
  let E := (forget C).mapCone D
  intro (x : E.pt) y H
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  exact funext_iff.mp H j

中文:
定理 to_product_injective_of_isLimit
  证明: by
  let E := (forget C).mapCone D
  intro (x : E.pt) y H
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  exact funext_iff.mp H j

Depends on / 依赖: E.pt, Types.isLimitEquivSections, forget, funext_iff, funext_iff.mp, injective, isLimitEquivSections, isLimitOfPreserves, mapCone
-/
theorem to_product_injective_of_isLimit
    {D : Cone F} (hD : IsLimit D) :
    Function.Injective fun (x : ToType D.pt) (j : J) => D.π.app j x := by
  let E := (forget C).mapCone D
  intro (x : E.pt) y H
  apply (Types.isLimitEquivSections (isLimitOfPreserves _ hD)).injective
  ext j
  exact funext_iff.mp H j

/--
theorem `isLimit_ext` / 定理 `isLimit_ext`

English:
theorem isLimit_ext
  given: {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt)
  proof: fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)

中文:
定理 isLimit_ext
  条件: {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt)
  证明: fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)
-/
theorem isLimit_ext {D : Cone F} (hD : IsLimit D) (x y : ToType D.pt) :
    (forall j, D.π.app j x = D.π.app j y) -> x = y := fun h =>
  Concrete.to_product_injective_of_isLimit _ hD (funext h)

/--
theorem `limit_ext` / 定理 `limit_ext`

English:
theorem limit_ext
  given: [HasLimit F] (x y : ToType (limit F))
  proof: Concrete.isLimit_ext F (limit.isLimit _) _ _

中文:
定理 limit_ext
  条件: [HasLimit F] (x y : ToType (limit F))
  证明: Concrete.isLimit_ext F (limit.isLimit _) _ _

Depends on / 依赖: Concrete, Concrete.isLimit_ext, isLimit, isLimit_ext, limit.isLimit
-/
theorem limit_ext [HasLimit F] (x y : ToType (limit F)) :
    (forall j, limit.π F j x = limit.π F j y) -> x = y :=
  Concrete.isLimit_ext F (limit.isLimit _) _ _

section Surjective

/--
lemma `surjective_π_app_zero_of_surjective_map` / 引理 `surjective_π_app_zero_of_surjective_map`

English:
lemma surjective_π_app_zero_of_surjective_map
  statement: {C : Type u} [Category.{v} C] {FC : C -> C -> Type*}
  proof: Types.surjective_π_app_zero_of_surjective_map (isLimitOfPreserves (forget C) hc) hF

中文:
引理 surjective_π_app_zero_of_surjective_map
  结论: {C : 类型u} [Category.{v} C] {FC : C -> C -> 类型}
  证明: Types.surjective_π_app_zero_of_surjective_map (isLimitOfPreserves (forget C) hc) hF

Depends on / 依赖: Types.surjective_, forget, isLimitOfPreserves
-/
lemma surjective_π_app_zero_of_surjective_map {C : Type u} [Category.{v} C] {FC : C -> C -> Type*}
    {CC : C -> Type v} [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC]
    [PreservesLimitsOfShape Natᵒᵖ (forget C)] {F : Natᵒᵖ ⥤ C} {c : Cone F}
    (hc : IsLimit c) (hF : forall n, Function.Surjective (F.map (homOfLE (Nat.le_succ n)).op)) :
    Function.Surjective (c.π.app ⟨0⟩) :=
  Types.surjective_π_app_zero_of_surjective_map (isLimitOfPreserves (forget C) hc) hF

end Surjective

end Limits

section Colimits

section

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type t}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{t} C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C)

section
variable [PreservesColimit F (forget C)]

/--
theorem `from_union_surjective_of_isColimit` / 定理 `from_union_surjective_of_isColimit`

English:
theorem from_union_surjective_of_isColimit
  given: {D : Cocone F} (hD : IsColimit D)
  proof: fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩

中文:
定理 from_union_surjective_of_isColimit
  条件: {D : Cocone F} (hD : IsColimit D)
  证明: fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩
-/
theorem from_union_surjective_of_isColimit {D : Cocone F} (hD : IsColimit D) :
    let ff : (Σ j : J, ToType (F.obj j)) -> ToType D.pt := fun a => D.ι.app a.1 a.2
    Function.Surjective ff := by
  intro ff x
  let E : Cocone (F ⋙ forget C) := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves (forget C) hD
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective_of_isColimit hE x
  exact ⟨⟨j, y⟩, hy⟩

/--
theorem `isColimit_exists_rep` / 定理 `isColimit_exists_rep`

English:
theorem isColimit_exists_rep
  given: {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt)
  proof: by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩

中文:
定理 isColimit_exists_rep
  条件: {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt)
  证明: by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩

Depends on / 依赖: Concrete, Concrete.from_union_surjective_of_isColimit, from_union_surjective_of_isColimit
-/
theorem isColimit_exists_rep {D : Cocone F} (hD : IsColimit D) (x : ToType D.pt) :
    exists (j : J) (y : ToType (F.obj j)), D.ι.app j y = x := by
  obtain ⟨a, rfl⟩ := Concrete.from_union_surjective_of_isColimit F hD x
  exact ⟨a.1, a.2, rfl⟩

/--
theorem `colimit_exists_rep` / 定理 `colimit_exists_rep`

English:
theorem colimit_exists_rep
  given: [HasColimit F] (x : ToType (colimit F))
  proof: Concrete.isColimit_exists_rep F (colimit.isColimit _) x

中文:
定理 colimit_exists_rep
  条件: [HasColimit F] (x : ToType (colimit F))
  证明: Concrete.isColimit_exists_rep F (colimit.isColimit _) x

Depends on / 依赖: Concrete, Concrete.isColimit_exists_rep, colimit, colimit.isColimit, isColimit, isColimit_exists_rep
-/
theorem colimit_exists_rep [HasColimit F] (x : ToType (colimit F)) :
    exists (j : J) (y : ToType (F.obj j)), colimit.ι F j y = x :=
  Concrete.isColimit_exists_rep F (colimit.isColimit _) x

end

set_option backward.isDefEq.respectTransparency false in
/--
theorem `isColimit_rep_eq_of_exists` / 定理 `isColimit_rep_eq_of_exists`

English:
theorem isColimit_rep_eq_of_exists
  statement: {D : Cocone F} {i j : J} (x : ToType (F.obj i))
  proof: by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  change E.ι.app i x = E.ι.app j y
  rw [← 

中文:
定理 isColimit_rep_eq_of_exists
  结论: {D : Cocone F} {i j : J} (x : ToType (F.obj i))
  证明: by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  change E.ι.app i x = E.ι.app j y
  rw [← 

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, F.map, comp_apply, congr_hom, forget, mapCocone, naturality
-/
theorem isColimit_rep_eq_of_exists {D : Cocone F} {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    D.ι.app i x = D.ι.app j y := by
  let E := (forget C).mapCocone D
  obtain ⟨k, f, g, (hfg : (F ⋙ forget C).map f x = F.map g y)⟩ := h
  let h1 : (F ⋙ forget C).map f ≫ E.ι.app k = E.ι.app i := E.ι.naturality f
  let h2 : (F ⋙ forget C).map g ≫ E.ι.app k = E.ι.app j := E.ι.naturality g
  change E.ι.app i x = E.ι.app j y
  rw [← h1]; rw [comp_apply]; rw [hfg]
  exact ConcreteCategory.congr_hom h2 y

/--
theorem `colimit_rep_eq_of_exists` / 定理 `colimit_rep_eq_of_exists`

English:
theorem colimit_rep_eq_of_exists
  statement: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  proof: Concrete.isColimit_rep_eq_of_exists F x y h

中文:
定理 colimit_rep_eq_of_exists
  结论: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  证明: Concrete.isColimit_rep_eq_of_exists F x y h

Depends on / 依赖: Concrete, Concrete.isColimit_rep_eq_of_exists, isColimit_rep_eq_of_exists
-/
theorem colimit_rep_eq_of_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j))
    (h : exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y) :
    colimit.ι F i x = colimit.ι F j y :=
  Concrete.isColimit_rep_eq_of_exists F x y h

end

section FilteredColimits

variable {C : Type u} [Category.{v} C] {FC : C -> C -> Type*} {CC : C -> Type s}
variable [forall X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
variable {J : Type w} [Category.{r} J] (F : J ⥤ C) [PreservesColimit F (forget C)] [IsFiltered J]

/--
theorem `isColimit_exists_of_rep_eq` / 定理 `isColimit_exists_of_rep_eq`

English:
theorem isColimit_exists_of_rep_eq
  statement: {D : Cocone F} {i j : J} (hD : IsColimit D)
  proof: by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h

中文:
定理 isColimit_exists_of_rep_eq
  结论: {D : Cocone F} {i j : J} (hD : IsColimit D)
  证明: by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h

Depends on / 依赖: FilteredColimit, IsColimit, Types.FilteredColimit.isColimit_eq_iff, forget, isColimitOfPreserves, isColimit_eq_iff, mapCocone
-/
theorem isColimit_exists_of_rep_eq {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) (h : D.ι.app _ x = D.ι.app _ y) :
    exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y := by
  let E := (forget C).mapCocone D
  let hE : IsColimit E := isColimitOfPreserves _ hD
  exact (Types.FilteredColimit.isColimit_eq_iff (F ⋙ forget C) hE).mp h

/--
theorem `isColimit_rep_eq_iff_exists` / 定理 `isColimit_rep_eq_iff_exists`

English:
theorem isColimit_rep_eq_iff_exists
  statement: {D : Cocone F} {i j : J} (hD : IsColimit D)
  proof: ⟨Concrete.isColimit_exists_of_rep_eq.{s} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩

中文:
定理 isColimit_rep_eq_iff_exists
  结论: {D : Cocone F} {i j : J} (hD : IsColimit D)
  证明: ⟨Concrete.isColimit_exists_of_rep_eq.{s} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩

Depends on / 依赖: Concrete, Concrete.isColimit_exists_of_rep_eq, Concrete.isColimit_rep_eq_of_exists, isColimit_exists_of_rep_eq, isColimit_rep_eq_of_exists
-/
theorem isColimit_rep_eq_iff_exists {D : Cocone F} {i j : J} (hD : IsColimit D)
    (x : ToType (F.obj i)) (y : ToType (F.obj j)) :
    D.ι.app i x = D.ι.app j y ↔ exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.isColimit_exists_of_rep_eq.{s} _ hD _ _,
   Concrete.isColimit_rep_eq_of_exists _ _ _⟩

/--
theorem `colimit_exists_of_rep_eq` / 定理 `colimit_exists_of_rep_eq`

English:
theorem colimit_exists_of_rep_eq
  statement: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  proof: Concrete.isColimit_exists_of_rep_eq.{s} F (colimit.isColimit _) x y h

中文:
定理 colimit_exists_of_rep_eq
  结论: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  证明: Concrete.isColimit_exists_of_rep_eq.{s} F (colimit.isColimit _) x y h

Depends on / 依赖: Concrete, Concrete.isColimit_exists_of_rep_eq, colimit, colimit.isColimit, isColimit, isColimit_exists_of_rep_eq
-/
theorem colimit_exists_of_rep_eq [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) (h : colimit.ι F _ x = colimit.ι F _ y) :
    exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  Concrete.isColimit_exists_of_rep_eq.{s} F (colimit.isColimit _) x y h

/--
theorem `colimit_rep_eq_iff_exists` / 定理 `colimit_rep_eq_iff_exists`

English:
theorem colimit_rep_eq_iff_exists
  statement: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  proof: ⟨Concrete.colimit_exists_of_rep_eq.{s} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩

中文:
定理 colimit_rep_eq_iff_exists
  结论: [HasColimit F] {i j : J} (x : ToType (F.obj i))
  证明: ⟨Concrete.colimit_exists_of_rep_eq.{s} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩

Depends on / 依赖: Concrete, Concrete.colimit_exists_of_rep_eq, Concrete.colimit_rep_eq_of_exists, colimit_exists_of_rep_eq, colimit_rep_eq_of_exists
-/
theorem colimit_rep_eq_iff_exists [HasColimit F] {i j : J} (x : ToType (F.obj i))
    (y : ToType (F.obj j)) :
    colimit.ι F i x = colimit.ι F j y ↔ exists (k : _) (f : i ⟶ k) (g : j ⟶ k), F.map f x = F.map g y :=
  ⟨Concrete.colimit_exists_of_rep_eq.{s} _ _ _, Concrete.colimit_rep_eq_of_exists _ _ _⟩

set_option backward.defeqAttrib.useBackward true in
omit [IsFiltered J] in
/--
theorem `exists_hom_ι_eq_of_isColimit` / 定理 `exists_hom_ι_eq_of_isColimit`

English:
theorem exists_hom_ι_eq_of_isColimit
  statement: [IsFilteredOrEmpty J] {D : Cocone F} (hD : IsColimit D)
  proof: by
  obtain ⟨j, y, rfl⟩ := isColimit_exists_rep F hD x
  refine ⟨IsFiltered.max k j, IsFiltered.leftToMax _ _, F.map (IsFiltered.rightToMax _ _) y, ?_⟩
  rw [← ConcreteCategory.comp_apply]
  congr 1
  simp

中文:
定理 exists_hom_ι_eq_of_isColimit
  结论: [IsFilteredOrEmpty J] {D : Cocone F} (hD : IsColimit D)
  证明: by
  obtain ⟨j, y, rfl⟩ := isColimit_exists_rep F hD x
  refine ⟨IsFiltered.max k j, IsFiltered.leftToMax _ _, F.map (IsFiltered.rightToMax _ _) y, ?_⟩
  rw [← ConcreteCategory.comp_apply]
  congr 1
  simp

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, F.map, IsFiltered, IsFiltered.leftToMax, IsFiltered.max, IsFiltered.rightToMax, comp_apply, isColimit_exists_rep, leftToMax, rightToMax
-/
theorem exists_hom_ι_eq_of_isColimit [IsFilteredOrEmpty J] {D : Cocone F} (hD : IsColimit D)
    (x : ToType D.pt) (k : J) :
    exists (j : J) (_ : k ⟶ j) (y : ToType (F.obj j)), D.ι.app j y = x := by
  obtain ⟨j, y, rfl⟩ := isColimit_exists_rep F hD x
  refine ⟨IsFiltered.max k j, IsFiltered.leftToMax _ _, F.map (IsFiltered.rightToMax _ _) y, ?_⟩
  rw [← ConcreteCategory.comp_apply]
  congr 1
  simp

end FilteredColimits

end Colimits

end CategoryTheory.Limits.Concrete
