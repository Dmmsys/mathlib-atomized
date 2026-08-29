/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Wide equalizers and wide coequalizers

This file defines wide (co)equalizers as special cases of (co)limits.

A wide equalizer for the family of morphisms `X ⟶ Y` indexed by `J` is the categorical
generalization of the subobject `{a ∈ A | ∀ j₁ j₂, f(j₁, a) = f(j₂, a)}`. Note that if `J` has
fewer than two morphisms this condition is trivial, so some lemmas and definitions assume `J` is
nonempty.

## Main definitions

* `WalkingParallelFamily` is the indexing category used for wide (co)equalizer diagrams
* `parallelFamily` is a functor from `WalkingParallelFamily` to our category `C`.
* a `Trident` is a cone over a parallel family.
  * there is really only one interesting morphism in a trident: the arrow from the vertex of the
    trident to the domain of f and g. It is called `Trident.ι`.
* a `wideEqualizer` is now just a `limit (parallelFamily f)`

Each of these has a dual.

## Main statements

* `wideEqualizer.ι_mono` states that every wideEqualizer map is a monomorphism

## Implementation notes
As with the other special shapes in the limits library, all the definitions here are given as
`abbrev`s of the general statements for limits, so all the `simp` lemmas and theorems about
general limits can be used.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

@[expose] public section


noncomputable section

namespace CategoryTheory.Limits

open CategoryTheory

universe w v u u₂

variable {J : Type w}

/--
Inductive type `WalkingParallelFamily` / 归纳类型 `WalkingParallelFamily`

English:
inductive WalkingParallelFamily
  parameters: (J : Type w)
  constructors (2):
    - zero: WalkingParallelFamily J
    - one: WalkingParallelFamily J

中文:
归纳类型 WalkingParallelFamily
  参数: (J : 类型 w)
  构造子 (2 个):
    - zero: WalkingParallelFamily J
    - one: WalkingParallelFamily J
-/
inductive WalkingParallelFamily (J : Type w) : Type w
  | zero : WalkingParallelFamily J
  | one : WalkingParallelFamily J
deriving Inhabited

open WalkingParallelFamily

-- We do not use `deriving DecidableEq` here
-- because it generates an instance with unnecessary hypotheses.
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DecidableEq (WalkingParallelFamily J)

中文:
实例 :
  签名: DecidableEq (WalkingParallelFamily J)
-/
instance : DecidableEq (WalkingParallelFamily J)
  | zero, zero => isTrue rfl
  | zero, one => isFalse fun t => by grind
  | one, zero => isFalse fun t => by grind
  | one, one => isTrue rfl

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/--
Inductive type `WalkingParallelFamily.Hom` / 归纳类型 `WalkingParallelFamily.Hom`

English:
inductive WalkingParallelFamily.Hom
  parameters: (J : Type w)
  constructors (2):
    - id: forall X : WalkingParallelFamily.{w} J, WalkingParallelFamily.Hom J X X
    - line: J -> WalkingParallelFamily.Hom J zero one

中文:
归纳类型 WalkingParallelFamily.态射
  参数: (J : 类型 w)
  构造子 (2 个):
    - id: 对任意 X : WalkingParallelFamily.{w} J, WalkingParallelFamily.态射 J X X
    - line: J -> WalkingParallelFamily.态射 J zero one
-/
inductive WalkingParallelFamily.Hom (J : Type w) :
  WalkingParallelFamily J -> WalkingParallelFamily J -> Type w
  | id : forall X : WalkingParallelFamily.{w} J, WalkingParallelFamily.Hom J X X
  | line : J -> WalkingParallelFamily.Hom J zero one
  deriving DecidableEq

/-- Satisfying the inhabited linter -/
instance (J : Type v) : Inhabited (WalkingParallelFamily.Hom J zero zero) where default := Hom.id _

open WalkingParallelFamily.Hom

/--
Definition of `WalkingParallelFamily.Hom.comp` / `WalkingParallelFamily.Hom.comp` 的定义

English:
definition WalkingParallelFamily.Hom.comp
  signature: :

中文:
定义 WalkingParallelFamily.态射.comp
  签名: :

Depends on / 依赖: Functor, Functor.additive_of_comp_faithful, Functor.additive_of_iso, additive_of_comp_faithful, additive_of_iso, commShiftIso
-/
def WalkingParallelFamily.Hom.comp :
    forall {X Y Z : WalkingParallelFamily J} (_ : WalkingParallelFamily.Hom J X Y)
      (_ : WalkingParallelFamily.Hom J Y Z), WalkingParallelFamily.Hom J X Z
  | _, _, _, id _, h => h
  | _, _, _, line j, id one => line j

attribute [local aesop safe cases] WalkingParallelFamily.Hom

/--
Instance `WalkingParallelFamily.category` / 实例 `WalkingParallelFamily.category`

English:
instance WalkingParallelFamily.category
  signature: : SmallCategory (WalkingParallelFamily J) where
  body: WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp

@[simp]

中文:
实例 WalkingParallelFamily.category
  签名: : 小范畴 (WalkingParallelFamily J) where
  定义体: WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp

@[simp]

Depends on / 依赖: WalkingParallelFamily, WalkingParallelFamily.Hom
-/
instance WalkingParallelFamily.category : SmallCategory (WalkingParallelFamily J) where
  Hom := WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp

@[simp]
/--
theorem `WalkingParallelFamily.hom_id` / 定理 `WalkingParallelFamily.hom_id`

English:
theorem WalkingParallelFamily.hom_id
  given: (X : WalkingParallelFamily J)
  proof: rfl

中文:
定理 WalkingParallelFamily.hom_id
  条件: (X : WalkingParallelFamily J)
  证明: rfl
-/
theorem WalkingParallelFamily.hom_id (X : WalkingParallelFamily J) :
    WalkingParallelFamily.Hom.id X = 𝟙 X :=
  rfl

variable (J) in
/--
Definition of `WalkingParallelFamily.arrowEquiv` / `WalkingParallelFamily.arrowEquiv` 的定义

English:
definition WalkingParallelFamily.arrowEquiv
  signature: :
  body: match f.left, f.right, f.hom with
    | zero, _, .id _ => none
    | one, _, .id _ => some none
    | zero, one, .line t => some (some t)
  invFun x := match x with
    | none => Arrow.mk (𝟙 zero)
    | some none => Arrow.mk (𝟙 one)
    | some (some t) => Arrow.mk (.line t)
  left_inv := by rintro ⟨(_ | _), _, (_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

中文:
定义 WalkingParallelFamily.arrowEquiv
  签名: :
  定义体: match f.left, f.right, f.hom with
    | zero, _, .id _ => none
    | one, _, .id _ => some none
    | zero, one, .line t => some (some t)
  invFun x := match x with
    | none => Arrow.mk (𝟙 zero)
    | some none => Arrow.mk (𝟙 one)
    | some (some t) => Arrow.mk (.line t)
  left_inv := by rintro ⟨(_ | _), _, (_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

Depends on / 依赖: f.hom, f.left, f.right
-/
def WalkingParallelFamily.arrowEquiv :
    Arrow (WalkingParallelFamily J) ≃ Option (Option J) where
  toFun f := match f.left, f.right, f.hom with
    | zero, _, .id _ => none
    | one, _, .id _ => some none
    | zero, one, .line t => some (some t)
  invFun x := match x with
    | none => Arrow.mk (𝟙 zero)
    | some none => Arrow.mk (𝟙 one)
    | some (some t) => Arrow.mk (.line t)
  left_inv := by rintro ⟨(_ | _), _, (_ | _)⟩ <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

variable {C : Type u} [Category.{v} C]
variable {X Y : C} (f : J -> (X ⟶ Y))

/--
Definition of `parallelFamily` / `parallelFamily` 的定义

English:
definition parallelFamily
  signature: : WalkingParallelFamily J ⥤ C where
  body: WalkingParallelFamily.casesOn x X Y
  map {x y} h :=
    match x, y, h with
    | _, _, Hom.id _ => 𝟙 _
    | _, _, line j => f j
  map_comp := by
    rintro _ _ _ ⟨⟩ ⟨⟩ <;>
      · cat_disch

@[simp]

中文:
定义 parallelFamily
  签名: : WalkingParallelFamily J ⥤ C where
  定义体: WalkingParallelFamily.casesOn x X Y
  map {x y} h :=
    match x, y, h with
    | _, _, Hom.id _ => 𝟙 _
    | _, _, line j => f j
  map_comp := by
    rintro _ _ _ ⟨⟩ ⟨⟩ <;>
      · cat_disch

@[simp]

Depends on / 依赖: WalkingParallelFamily, WalkingParallelFamily.casesOn, casesOn
-/
def parallelFamily : WalkingParallelFamily J ⥤ C where
  obj x := WalkingParallelFamily.casesOn x X Y
  map {x y} h :=
    match x, y, h with
    | _, _, Hom.id _ => 𝟙 _
    | _, _, line j => f j
  map_comp := by
    rintro _ _ _ ⟨⟩ ⟨⟩ <;>
      · cat_disch

@[simp]
/--
theorem `parallelFamily_obj_zero` / 定理 `parallelFamily_obj_zero`

English:
theorem parallelFamily_obj_zero
  statement: (parallelFamily f).obj zero = X
  proof: rfl

@[simp]

中文:
定理 parallelFamily_obj_zero
  结论: (parallelFamily f).obj zero = X
  证明: rfl

@[simp]
-/
theorem parallelFamily_obj_zero : (parallelFamily f).obj zero = X :=
  rfl

@[simp]
/--
theorem `parallelFamily_obj_one` / 定理 `parallelFamily_obj_one`

English:
theorem parallelFamily_obj_one
  statement: (parallelFamily f).obj one = Y
  proof: rfl

@[simp]

中文:
定理 parallelFamily_obj_one
  结论: (parallelFamily f).obj one = Y
  证明: rfl

@[simp]
-/
theorem parallelFamily_obj_one : (parallelFamily f).obj one = Y :=
  rfl

@[simp]
/--
theorem `parallelFamily_map_left` / 定理 `parallelFamily_map_left`

English:
theorem parallelFamily_map_left
  given: {j : J}
  statement: (parallelFamily f).map (line j) = f j
  proof: rfl

中文:
定理 parallelFamily_map_left
  条件: {j : J}
  结论: (parallelFamily f).map (line j) = f j
  证明: rfl
-/
theorem parallelFamily_map_left {j : J} : (parallelFamily f).map (line j) = f j :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallelFamily` -/
@[simps!]
/--
Definition of `diagramIsoParallelFamily` / `diagramIsoParallelFamily` 的定义

English:
definition diagramIsoParallelFamily
  signature: (F : WalkingParallelFamily J ⥤ C)
  body: NatIso.ofComponents (fun j => eqToIso <| by cases j <;> cat_disch) by
    rintro _ _ (_ | _) <;> cat_disch

中文:
定义 diagramIsoParallelFamily
  签名: (F : WalkingParallelFamily J ⥤ C)
  定义体: NatIso.ofComponents (fun j => eqToIso <| by cases j <;> cat_disch) by
    rintro _ _ (_ | _) <;> cat_disch

Depends on / 依赖: NatIso, NatIso.ofComponents, Subtype, cat_disch, eqToIso, ofComponents, small_of_surjective
-/
def diagramIsoParallelFamily (F : WalkingParallelFamily J ⥤ C) :
    F ≅ parallelFamily fun j => F.map (line j) :=
NatIso.ofComponents (fun j => eqToIso <| by cases j <;> cat_disch) by
    rintro _ _ (_ | _) <;> cat_disch

set_option backward.defeqAttrib.useBackward true in
/-- `WalkingParallelPair` as a category is equivalent to a special case of
`WalkingParallelFamily`. -/
@[simps!]
/--
Definition of `walkingParallelFamilyEquivWalkingParallelPair` / `walkingParallelFamilyEquivWalkingParallelPair` 的定义

English:
definition walkingParallelFamilyEquivWalkingParallelPair
  signature: :
  body: parallelFamily fun p => cond p.down WalkingParallelPairHom.left WalkingParallelPairHom.right
  inverse := parallelPair (line (ULift.up true)) (line (ULift.up false))
  unitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | ⟨_ | _⟩) <;> cat_disch)
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | _ | _) <;> cat_disch)
  functor_unitIso_comp := by rintro (_ | _) <;> cat_disch

中文:
定义 walkingParallelFamilyEquivWalkingParallelPair
  签名: :
  定义体: parallelFamily fun p => cond p.down WalkingParallelPairHom.left WalkingParallelPairHom.right
  inverse := parallelPair (line (ULift.up true)) (line (ULift.up false))
  unitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | ⟨_ | _⟩) <;> cat_disch)
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | _ | _) <;> cat_disch)
  functor_unitIso_comp := by rintro (_ | _) <;> cat_disch

Depends on / 依赖: NatIso, NatIso.ofComponents, ULift.up, WalkingParallelPairHom, WalkingParallelPairHom.left, WalkingParallelPairHom.right, cat_disch, counitIso, eqToIso, functor_unitIso_comp, inverse, ofComponents, p.down, parallelFamily, parallelPair, unitIso
-/
def walkingParallelFamilyEquivWalkingParallelPair :
    WalkingParallelFamily.{w} (ULift Bool) ≌ WalkingParallelPair where
  functor :=
    parallelFamily fun p => cond p.down WalkingParallelPairHom.left WalkingParallelPairHom.right
  inverse := parallelPair (line (ULift.up true)) (line (ULift.up false))
  unitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | ⟨_ | _⟩) <;> cat_disch)
  counitIso := NatIso.ofComponents (fun X => eqToIso (by cases X <;> rfl)) (by
    rintro _ _ (_ | _ | _) <;> cat_disch)
  functor_unitIso_comp := by rintro (_ | _) <;> cat_disch

/--
Definition of `Trident` / `Trident` 的定义

English:
abbreviation Trident
  body: Cone (parallelFamily f)

中文:
缩写 Trident
  定义体: Cone (parallelFamily f)

Depends on / 依赖: P.subtypeOpEquiv.injective, injective, parallelFamily, small_of_injective, subtypeOpEquiv
-/
abbrev Trident :=
  Cone (parallelFamily f)

/--
Definition of `Cotrident` / `Cotrident` 的定义

English:
abbreviation Cotrident
  body: Cocone (parallelFamily f)

中文:
缩写 Cotrident
  定义体: Cocone (parallelFamily f)

Depends on / 依赖: Cocone, P.unop.subtypeOpEquiv, parallelFamily, small_congr, subtypeOpEquiv
-/
abbrev Cotrident :=
  Cocone (parallelFamily f)

variable {f}

/--
Definition of `Trident.ι` / `Trident.ι` 的定义

English:
abbreviation Trident.ι
  signature: (t : Trident f)
  body: t.π.app zero

中文:
缩写 Trident.ι
  签名: (t : Trident f)
  定义体: t.π.app zero

Depends on / 依赖: small_of_surjective
-/
abbrev Trident.ι (t : Trident f) :=
  t.π.app zero

/--
Definition of `Cotrident.π` / `Cotrident.π` 的定义

English:
abbreviation Cotrident.π
  signature: (t : Cotrident f)
  body: t.ι.app one

@[simp]

中文:
缩写 Cotrident.π
  签名: (t : Cotrident f)
  定义体: t.ι.app one

@[simp]

Depends on / 依赖: infer_instance
-/
abbrev Cotrident.π (t : Cotrident f) :=
  t.ι.app one

@[simp]
/--
theorem `Trident.ι_eq_app_zero` / 定理 `Trident.ι_eq_app_zero`

English:
theorem Trident.ι_eq_app_zero
  given: (t : Trident f)
  statement: t.ι = t.π.app zero
  proof: rfl

@[simp]

中文:
定理 Trident.ι_eq_app_zero
  条件: (t : Trident f)
  结论: t.ι = t.π.app zero
  证明: rfl

@[simp]

Depends on / 依赖: Small.of_le, inf_le_right, of_le
-/
theorem Trident.ι_eq_app_zero (t : Trident f) : t.ι = t.π.app zero :=
  rfl

@[simp]
/--
theorem `Cotrident.π_eq_app_one` / 定理 `Cotrident.π_eq_app_one`

English:
theorem Cotrident.π_eq_app_one
  given: (t : Cotrident f)
  statement: t.π = t.ι.app one
  proof: rfl

中文:
定理 Cotrident.π_eq_app_one
  条件: (t : Cotrident f)
  结论: t.π = t.ι.app one
  证明: rfl

Depends on / 依赖: Small.of_le, inf_le_left, of_le
-/
theorem Cotrident.π_eq_app_one (t : Cotrident f) : t.π = t.ι.app one :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `Trident.app_zero` / 定理 `Trident.app_zero`

English:
theorem Trident.app_zero
  given: (s : Trident f) (j : J)
  statement: s.π.app zero ≫ f j = s.π.app one
  proof: by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

中文:
定理 Trident.app_zero
  条件: (s : Trident f) (j : J)
  结论: s.π.app zero ≫ f j = s.π.app one
  证明: by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

Depends on / 依赖: Or.inl, Or.inr, Subtype, parallelFamily_map_left, small_of_surjective
-/
theorem Trident.app_zero (s : Trident f) (j : J) : s.π.app zero ≫ f j = s.π.app one := by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
theorem `Cotrident.app_one` / 定理 `Cotrident.app_one`

English:
theorem Cotrident.app_one
  given: (s : Cotrident f) (j : J)
  statement: f j ≫ s.ι.app one = s.ι.app zero
  proof: by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

中文:
定理 Cotrident.app_one
  条件: (s : Cotrident f) (j : J)
  结论: f j ≫ s.ι.app one = s.ι.app zero
  证明: by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

Depends on / 依赖: Subtype, parallelFamily_map_left, small_of_surjective
-/
theorem Cotrident.app_one (s : Cotrident f) (j : J) : f j ≫ s.ι.app one = s.ι.app zero := by
  rw [← s.w (line j)]; rw [parallelFamily_map_left]

set_option backward.defeqAttrib.useBackward true in
/-- A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfying
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
@[simps]
/--
Definition of `Trident.ofι` / `Trident.ofι` 的定义

English:
definition Trident.ofι
  signature: [Nonempty J] {P : C} (ι : P ⟶ X) (w : forall j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂)
  body: P
  π :=
    { app := fun X => WalkingParallelFamily.casesOn X ι (ι ≫ f (Classical.arbitrary J))
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }

中文:
定义 Trident.ofι
  签名: [非空 J] {P : C} (ι : P ⟶ X) (w : 对任意 j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂)
  定义体: P
  π :=
    { app := fun X => WalkingParallelFamily.casesOn X ι (ι ≫ f (Classical.arbitrary J))
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }
-/
def Trident.ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : forall j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
    Trident f where
  pt := P
  π :=
    { app := fun X => WalkingParallelFamily.casesOn X ι (ι ≫ f (Classical.arbitrary J))
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }

set_option backward.defeqAttrib.useBackward true in
/-- A cotrident on `f : J → (X ⟶ Y)` is determined by the morphism `π : Y ⟶ P` satisfying
`∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π`.
-/
@[simps]
/--
Definition of `Cotrident.ofπ` / `Cotrident.ofπ` 的定义

English:
definition Cotrident.ofπ
  signature: [Nonempty J] {P : C} (π : Y ⟶ P) (w : forall j₁ j₂, f j₁ ≫ π = f j₂ ≫ π)
  body: P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }

中文:
定义 Cotrident.ofπ
  签名: [非空 J] {P : C} (π : Y ⟶ P) (w : 对任意 j₁ j₂, f j₁ ≫ π = f j₂ ≫ π)
  定义体: P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }
-/
def Cotrident.ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : forall j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    Cotrident f where
  pt := P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }

/--
theorem `Trident.ι_ofι` / 定理 `Trident.ι_ofι`

English:
theorem Trident.ι_ofι
  given: [Nonempty J] {P : C} (ι : P ⟶ X) (w : forall j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂)
  proof: rfl

中文:
定理 Trident.ι_ofι
  条件: [非空 J] {P : C} (ι : P ⟶ X) (w : 对任意 j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂)
  证明: rfl
-/
theorem Trident.ι_ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : forall j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
    (Trident.ofι ι w).ι = ι :=
  rfl

/--
theorem `Cotrident.π_ofπ` / 定理 `Cotrident.π_ofπ`

English:
theorem Cotrident.π_ofπ
  given: [Nonempty J] {P : C} (π : Y ⟶ P) (w : forall j₁ j₂, f j₁ ≫ π = f j₂ ≫ π)
  proof: rfl

#adaptation_note

中文:
定理 Cotrident.π_ofπ
  条件: [非空 J] {P : C} (π : Y ⟶ P) (w : 对任意 j₁ j₂, f j₁ ≫ π = f j₂ ≫ π)
  证明: rfl

#adaptation_note
-/
theorem Cotrident.π_ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : forall j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    (Cotrident.ofπ π w).π = π :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
theorem `Trident.condition` / 定理 `Trident.condition`

English:
theorem Trident.condition
  given: (j₁ j₂ : J) (t : Trident f)
  statement: t.ι ≫ f j₁ = t.ι ≫ f j₂
  proof: by
  rw [t.app_zero]; rw [t.app_zero]

#adaptation_note

中文:
定理 Trident.condition
  条件: (j₁ j₂ : J) (t : Trident f)
  结论: t.ι ≫ f j₁ = t.ι ≫ f j₂
  证明: by
  rw [t.app_zero]; rw [t.app_zero]

#adaptation_note

Depends on / 依赖: app_zero, t.app_zero
-/
theorem Trident.condition (j₁ j₂ : J) (t : Trident f) : t.ι ≫ f j₁ = t.ι ≫ f j₂ := by
  rw [t.app_zero]; rw [t.app_zero]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/--
theorem `Cotrident.condition` / 定理 `Cotrident.condition`

English:
theorem Cotrident.condition
  given: (j₁ j₂ : J) (t : Cotrident f)
  statement: f j₁ ≫ t.π = f j₂ ≫ t.π
  proof: by
  rw [t.app_one]; rw [t.app_one]

中文:
定理 Cotrident.condition
  条件: (j₁ j₂ : J) (t : Cotrident f)
  结论: f j₁ ≫ t.π = f j₂ ≫ t.π
  证明: by
  rw [t.app_one]; rw [t.app_one]

Depends on / 依赖: app_one, le_isoClosure, t.app_one
-/
theorem Cotrident.condition (j₁ j₂ : J) (t : Cotrident f) : f j₁ ≫ t.π = f j₂ ≫ t.π := by
  rw [t.app_one]; rw [t.app_one]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Trident.equalizer_ext` / 定理 `Trident.equalizer_ext`

English:
theorem Trident.equalizer_ext
  statement: [Nonempty J] (s : Trident f) {W : C} {k l : W ⟶ s.pt}

中文:
定理 Trident.equalizer_ext
  结论: [非空 J] (s : Trident f) {W : C} {k l : W ⟶ s.pt}

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, exists_small_le, isoClosure_le_iff
-/
theorem Trident.equalizer_ext [Nonempty J] (s : Trident f) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ s.ι = l ≫ s.ι) : forall j : WalkingParallelFamily J, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by rw [← s.app_zero (Classical.arbitrary J), reassoc_of% h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Cotrident.coequalizer_ext` / 定理 `Cotrident.coequalizer_ext`

English:
theorem Cotrident.coequalizer_ext
  statement: [Nonempty J] (s : Cotrident f) {W : C} {k l : s.pt ⟶ W}

中文:
定理 Cotrident.coequalizer_ext
  结论: [非空 J] (s : Cotrident f) {W : C} {k l : s.pt ⟶ W}
-/
theorem Cotrident.coequalizer_ext [Nonempty J] (s : Cotrident f) {W : C} {k l : s.pt ⟶ W}
    (h : s.π ≫ k = s.π ≫ l) : forall j : WalkingParallelFamily J, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by rw [← s.app_one (Classical.arbitrary J), Category.assoc, Category.assoc, h]
  | one => h

/--
theorem `Trident.IsLimit.hom_ext` / 定理 `Trident.IsLimit.hom_ext`

English:
theorem Trident.IsLimit.hom_ext
  statement: [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C}
  proof: hs.hom_ext Trident.equalizer_ext _ h

中文:
定理 Trident.是极限.hom_ext
  结论: [非空 J] {s : Trident f} (hs : 是极限 s) {W : C}
  证明: hs.hom_ext Trident.equalizer_ext _ h

Depends on / 依赖: Trident, Trident.equalizer_ext, equalizer_ext, hom_ext, hs.hom_ext
-/
theorem Trident.IsLimit.hom_ext [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C}
    {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) : k = l :=
hs.hom_ext Trident.equalizer_ext _ h

/--
theorem `Cotrident.IsColimit.hom_ext` / 定理 `Cotrident.IsColimit.hom_ext`

English:
theorem Cotrident.IsColimit.hom_ext
  statement: [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C}
  proof: hs.hom_ext Cotrident.coequalizer_ext _ h

中文:
定理 Cotrident.是余极限.hom_ext
  结论: [非空 J] {s : Cotrident f} (hs : 是余极限 s) {W : C}
  证明: hs.hom_ext Cotrident.coequalizer_ext _ h

Depends on / 依赖: Cotrident, Cotrident.coequalizer_ext, EssentiallySmall, EssentiallySmall.exists_small_le, coequalizer_ext, exists_small_le, hom_ext, hs.hom_ext, le_sup_left, le_sup_right, monotone_isoClosure, sup_le_iff
-/
theorem Cotrident.IsColimit.hom_ext [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C}
    {k l : s.pt ⟶ W} (h : s.π ≫ k = s.π ≫ l) : k = l :=
hs.hom_ext Cotrident.coequalizer_ext _ h

/--
Definition of `Trident.IsLimit.lift'` / `Trident.IsLimit.lift'` 的定义

English:
definition Trident.IsLimit.lift'
  signature: [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
  body: ⟨hs.lift Trident.ofι _ h, hs.fac _ _⟩

中文:
定义 Trident.是极限.lift'
  签名: [非空 J] {s : Trident f} (hs : 是极限 s) {W : C} (k : W ⟶ X)
  定义体: ⟨hs.lift Trident.ofι _ h, hs.fac _ _⟩

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, Trident, Trident.of, exists_small_le, hs.fac, hs.lift, iSup_le_iff, le_iSup, monotone_isoClosure
-/
def Trident.IsLimit.lift' [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂) : { l : W ⟶ s.pt // l ≫ Trident.ι s = k } :=
⟨hs.lift Trident.ofι _ h, hs.fac _ _⟩

/--
Definition of `Cotrident.IsColimit.desc'` / `Cotrident.IsColimit.desc'` 的定义

English:
definition Cotrident.IsColimit.desc'
  signature: [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
  body: ⟨hs.desc Cotrident.ofπ _ h, hs.fac _ _⟩

中文:
定义 Cotrident.是余极限.desc'
  签名: [非空 J] {s : Cotrident f} (hs : 是余极限 s) {W : C} (k : Y ⟶ W)
  定义体: ⟨hs.desc Cotrident.ofπ _ h, hs.fac _ _⟩

Depends on / 依赖: Cotrident, Cotrident.of, hs.desc, hs.fac
-/
def Cotrident.IsColimit.desc' [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) : { l : s.pt ⟶ W // Cotrident.π s ≫ l = k } :=
⟨hs.desc Cotrident.ofπ _ h, hs.fac _ _⟩

/--
Definition of `Trident.IsLimit.mk` / `Trident.IsLimit.mk` 的定义

English:
definition Trident.IsLimit.mk
  signature: [Nonempty J] (t : Trident f) (lift : forall s : Trident f, s.pt ⟶ t.pt)
  body: { lift
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by rw [← t.w (line (Classical.arbitrary J)), reassoc_of% fac, s.w])
    uniq := uniq }

中文:
定义 Trident.是极限.mk
  签名: [非空 J] (t : Trident f) (lift : 对任意 s : Trident f, s.pt ⟶ t.pt)
  定义体: { lift
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by rw [← t.w (line (Classical.arbitrary J)), reassoc_of% fac, s.w])
    uniq := uniq }

Depends on / 依赖: Classical, Classical.arbitrary, WalkingParallelFamily, WalkingParallelFamily.casesOn, arbitrary, casesOn, reassoc_of
-/
def Trident.IsLimit.mk [Nonempty J] (t : Trident f) (lift : forall s : Trident f, s.pt ⟶ t.pt)
    (fac : forall s : Trident f, lift s ≫ t.ι = s.ι)
    (uniq :
      forall (s : Trident f) (m : s.pt ⟶ t.pt)
        (_ : forall j : WalkingParallelFamily J, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by rw [← t.w (line (Classical.arbitrary J)), reassoc_of% fac, s.w])
    uniq := uniq }

/--
Definition of `Trident.IsLimit.mk'` / `Trident.IsLimit.mk'` 的定义

English:
definition Trident.IsLimit.mk'
  signature: [Nonempty J] (t : Trident f)
  body: Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w zero)

中文:
定义 Trident.是极限.mk'
  签名: [非空 J] (t : Trident f)
  定义体: Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w zero)

Depends on / 依赖: IsLimit, Trident, Trident.IsLimit.mk, create
-/
def Trident.IsLimit.mk' [Nonempty J] (t : Trident f)
    (create : forall s : Trident f, { l // l ≫ t.ι = s.ι ∧ forall {m}, m ≫ t.ι = s.ι -> m = l }) :
    IsLimit t :=
  Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w zero)

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cotrident.IsColimit.mk` / `Cotrident.IsColimit.mk` 的定义

English:
definition Cotrident.IsColimit.mk
  signature: [Nonempty J] (t : Cotrident f) (desc : forall s : Cotrident f, t.pt ⟶ s.pt)
  body: { desc
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (by rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s)
    uniq := uniq }

中文:
定义 Cotrident.是余极限.mk
  签名: [非空 J] (t : Cotrident f) (desc : 对任意 s : Cotrident f, t.pt ⟶ s.pt)
  定义体: { desc
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (by rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s)
    uniq := uniq }

Depends on / 依赖: Classical, Classical.arbitrary, WalkingParallelFamily, WalkingParallelFamily.casesOn, arbitrary, casesOn, t.w_assoc, w_assoc
-/
def Cotrident.IsColimit.mk [Nonempty J] (t : Cotrident f) (desc : forall s : Cotrident f, t.pt ⟶ s.pt)
    (fac : forall s : Cotrident f, t.π ≫ desc s = s.π)
    (uniq :
      forall (s : Cotrident f) (m : t.pt ⟶ s.pt)
        (_ : forall j : WalkingParallelFamily J, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (by rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s)
    uniq := uniq }

/--
Definition of `Cotrident.IsColimit.mk'` / `Cotrident.IsColimit.mk'` 的定义

English:
definition Cotrident.IsColimit.mk'
  signature: [Nonempty J] (t : Cotrident f)
  body: Cotrident.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w one)

中文:
定义 Cotrident.是余极限.mk'
  签名: [非空 J] (t : Cotrident f)
  定义体: Cotrident.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w one)

Depends on / 依赖: Cotrident, Cotrident.IsColimit.mk, EssentiallySmall, EssentiallySmall.exists_small_le, IsColimit, asEquivalence, create, essentiallySmall_congr, essentiallySmall_of_small_of_locallySmall, exists_small_le
-/
def Cotrident.IsColimit.mk' [Nonempty J] (t : Cotrident f)
    (create :
      forall s : Cotrident f, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π ∧ forall {m}, t.π ≫ m = s.π -> m = l }) :
    IsColimit t :=
  Cotrident.IsColimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w one)

set_option backward.isDefEq.respectTransparency false in
/--
Given a limit cone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂`.
Further, this bijection is natural in `Z`: see `Trident.Limits.homIso_natural`.
-/
@[simps]
/--
Definition of `Trident.IsLimit.homIso` / `Trident.IsLimit.homIso` 的定义

English:
definition Trident.IsLimit.homIso
  signature: [Nonempty J] {t : Trident f} (ht : IsLimit t) (Z : C)
  body: ⟨k ≫ t.ι, by simp⟩
  invFun h := (Trident.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Trident.IsLimit.lift' ht _ _).prop

中文:
定义 Trident.是极限.homIso
  签名: [非空 J] {t : Trident f} (ht : 是极限 t) (Z : C)
  定义体: ⟨k ≫ t.ι, by simp⟩
  invFun h := (Trident.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Trident.IsLimit.lift' ht _ _).prop
-/
def Trident.IsLimit.homIso [Nonempty J] {t : Trident f} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // forall j₁ j₂, h ≫ f j₁ = h ≫ f j₂ } where
  toFun k := ⟨k ≫ t.ι, by simp⟩
  invFun h := (Trident.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Trident.IsLimit.lift' ht _ _).prop

/--
theorem `Trident.IsLimit.homIso_natural` / 定理 `Trident.IsLimit.homIso_natural`

English:
theorem Trident.IsLimit.homIso_natural
  statement: [Nonempty J] {t : Trident f} (ht : IsLimit t) {Z Z' : C}
  proof: Category.assoc _ _ _

中文:
定理 Trident.是极限.homIso_natural
  结论: [非空 J] {t : Trident f} (ht : 是极限 t) {Z Z' : C}
  证明: Category.assoc _ _ _

Depends on / 依赖: Category, Category.assoc, F.obj, Subtype, small_of_surjective
-/
theorem Trident.IsLimit.homIso_natural [Nonempty J] {t : Trident f} (ht : IsLimit t) {Z Z' : C}
    (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Trident.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) =
      q ≫ (Trident.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`. Further, this bijection is natural in `Z`: see
`Cotrident.IsColimit.homIso_natural`.
-/
@[simps]
/--
Definition of `Cotrident.IsColimit.homIso` / `Cotrident.IsColimit.homIso` 的定义

English:
definition Cotrident.IsColimit.homIso
  signature: [Nonempty J] {t : Cotrident f} (ht : IsColimit t) (Z : C)
  body: ⟨t.π ≫ k, by simp⟩
  invFun h := (Cotrident.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cotrident.IsColimit.desc' ht _ _).prop

中文:
定义 Cotrident.是余极限.homIso
  签名: [非空 J] {t : Cotrident f} (ht : 是余极限 t) (Z : C)
  定义体: ⟨t.π ≫ k, by simp⟩
  invFun h := (Cotrident.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cotrident.IsColimit.desc' ht _ _).prop

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, Q.strictMap, exists_small_le, map_monotone, strictMap
-/
def Cotrident.IsColimit.homIso [Nonempty J] {t : Cotrident f} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // forall j₁ j₂, f j₁ ≫ h = f j₂ ≫ h } where
  toFun k := ⟨t.π ≫ k, by simp⟩
  invFun h := (Cotrident.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cotrident.IsColimit.desc' ht _ _).prop

/--
theorem `Cotrident.IsColimit.homIso_natural` / 定理 `Cotrident.IsColimit.homIso_natural`

English:
theorem Cotrident.IsColimit.homIso_natural
  statement: [Nonempty J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z')
  proof: (Category.assoc _ _ _).symm

中文:
定理 Cotrident.是余极限.homIso_natural
  结论: [非空 J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z')
  证明: (Category.assoc _ _ _).symm

Depends on / 依赖: Category, Category.assoc
-/
theorem Cotrident.IsColimit.homIso_natural [Nonempty J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z')
    (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cotrident.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cotrident.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cone.ofTrident` / `Cone.ofTrident` 的定义

English:
definition Cone.ofTrident
  signature: {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
  body: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := fun j j' g => by cases g <;> cat_disch }

中文:
定义 锥.ofTrident
  签名: {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
  定义体: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := fun j j' g => by cases g <;> cat_disch }

Depends on / 依赖: EssentiallySmall, EssentiallySmall.exists_small_le, asEquivalence, essentiallySmall_congr, essentiallySmall_of_small_of_locallySmall, exists_small_le, t.pt
-/
def Cone.ofTrident {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j)) :
    Cone F where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := fun j j' g => by cases g <;> cat_disch }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cocone.ofCotrident` / `Cocone.ofCotrident` 的定义

English:
definition Cocone.ofCotrident
  signature: {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j))
  body: t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := fun j j' g => by cases g <;> simp [Cotrident.app_one t] }

@[simp]

中文:
定义 余锥.ofCotrident
  签名: {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j))
  定义体: t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := fun j j' g => by cases g <;> simp [Cotrident.app_one t] }

@[simp]

Depends on / 依赖: t.pt
-/
def Cocone.ofCotrident {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j)) :
    Cocone F where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := fun j j' g => by cases g <;> simp [Cotrident.app_one t] }

@[simp]
/--
theorem `Cone.ofTrident_π` / 定理 `Cone.ofTrident_π`

English:
theorem Cone.ofTrident_π
  statement: {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
  proof: rfl

@[simp]

中文:
定理 锥.ofTrident_π
  结论: {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
  证明: rfl

@[simp]
-/
theorem Cone.ofTrident_π {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
    (j) : (Cone.ofTrident t).π.app j = t.π.app j ≫ eqToHom (by cases j <;> cat_disch) :=
  rfl

@[simp]
/--
theorem `Cocone.ofCotrident_ι` / 定理 `Cocone.ofCotrident_ι`

English:
theorem Cocone.ofCotrident_ι
  statement: {F : WalkingParallelFamily J ⥤ C}
  proof: rfl

中文:
定理 余锥.ofCotrident_ι
  结论: {F : WalkingParallelFamily J ⥤ C}
  证明: rfl
-/
theorem Cocone.ofCotrident_ι {F : WalkingParallelFamily J ⥤ C}
    (t : Cotrident fun j => F.map (line j)) (j) :
    (Cocone.ofCotrident t).ι.app j = eqToHom (by cases j <;> cat_disch) ≫ t.ι.app j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Trident.ofCone` / `Trident.ofCone` 的定义

English:
definition Trident.ofCone
  signature: {F : WalkingParallelFamily J ⥤ C} (t : Cone F)
  body: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

中文:
定义 Trident.ofCone
  签名: {F : WalkingParallelFamily J ⥤ C} (t : 锥 F)
  定义体: t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

Depends on / 依赖: t.pt
-/
def Trident.ofCone {F : WalkingParallelFamily J ⥤ C} (t : Cone F) :
    Trident fun j => F.map (line j) where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `Cotrident.ofCocone` / `Cotrident.ofCocone` 的定义

English:
definition Cotrident.ofCocone
  signature: {F : WalkingParallelFamily J ⥤ C} (t : Cocone F)
  body: t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

@[simp]

中文:
定义 Cotrident.ofCocone
  签名: {F : WalkingParallelFamily J ⥤ C} (t : 余锥 F)
  定义体: t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

@[simp]

Depends on / 依赖: t.pt
-/
def Cotrident.ofCocone {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) :
    Cotrident fun j => F.map (line j) where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

@[simp]
/--
theorem `Trident.ofCone_π` / 定理 `Trident.ofCone_π`

English:
theorem Trident.ofCone_π
  given: {F : WalkingParallelFamily J ⥤ C} (t : Cone F) (j)
  proof: rfl

@[simp]

中文:
定理 Trident.ofCone_π
  条件: {F : WalkingParallelFamily J ⥤ C} (t : 锥 F) (j)
  证明: rfl

@[simp]

Depends on / 依赖: F.essImage, Functor, Functor.essImage, ObjectProperty, ObjectProperty.map, essImage, essentiallySmall_iff_objectPropertyEssentiallySmall, of_functor, of_le
-/
theorem Trident.ofCone_π {F : WalkingParallelFamily J ⥤ C} (t : Cone F) (j) :
    (Trident.ofCone t).π.app j = t.π.app j ≫ eqToHom (by cases j <;> cat_disch) :=
  rfl

@[simp]
/--
theorem `Cotrident.ofCocone_ι` / 定理 `Cotrident.ofCocone_ι`

English:
theorem Cotrident.ofCocone_ι
  given: {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) (j)
  proof: rfl

中文:
定理 Cotrident.ofCocone_ι
  条件: {F : WalkingParallelFamily J ⥤ C} (t : 余锥 F) (j)
  证明: rfl
-/
theorem Cotrident.ofCocone_ι {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) (j) :
    (Cotrident.ofCocone t).ι.app j = eqToHom (by cases j <;> cat_disch) ≫ t.ι.app j :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper function for constructing morphisms between wide equalizer tridents.
-/
@[simps]
/--
Definition of `Trident.mkHom` / `Trident.mkHom` 的定义

English:
definition Trident.mkHom
  signature: [Nonempty J] {s t : Trident f} (k : s.pt ⟶ t.pt)
  body: k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simpa using w =≫ f (Classical.arbitrary J)

中文:
定义 Trident.mkHom
  签名: [非空 J] {s t : Trident f} (k : s.pt ⟶ t.pt)
  定义体: k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simpa using w =≫ f (Classical.arbitrary J)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, cat_disch
-/
def Trident.mkHom [Nonempty J] {s t : Trident f} (k : s.pt ⟶ t.pt)
    (w : k ≫ t.ι = s.ι := by cat_disch) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · exact w
    · simpa using w =≫ f (Classical.arbitrary J)

/-- To construct an isomorphism between tridents,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
@[simps]
/--
Definition of `Trident.ext` / `Trident.ext` 的定义

English:
definition Trident.ext
  signature: [Nonempty J] {s t : Trident f} (i : s.pt ≅ t.pt)
  body: Trident.mkHom i.hom w
  inv := Trident.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

中文:
定义 Trident.ext
  签名: [非空 J] {s t : Trident f} (i : s.pt ≅ t.pt)
  定义体: Trident.mkHom i.hom w
  inv := Trident.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

Depends on / 依赖: Iso.inv_hom_id_assoc, Trident, Trident.mkHom, cat_disch, i.hom, i.inv, inv_hom_id_assoc
-/
def Trident.ext [Nonempty J] {s t : Trident f} (i : s.pt ≅ t.pt)
    (w : i.hom ≫ t.ι = s.ι := by cat_disch) : s ≅ t where
  hom := Trident.mkHom i.hom w
  inv := Trident.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Helper function for constructing morphisms between coequalizer cotridents.
-/
@[simps]
/--
Definition of `Cotrident.mkHom` / `Cotrident.mkHom` 的定义

English:
definition Cotrident.mkHom
  signature: [Nonempty J] {s t : Cotrident f} (k : s.pt ⟶ t.pt)
  body: k
  w := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
    · exact w

中文:
定义 Cotrident.mkHom
  签名: [非空 J] {s t : Cotrident f} (k : s.pt ⟶ t.pt)
  定义体: k
  w := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
    · exact w

Depends on / 依赖: Classical, Classical.arbitrary, IsClosedUnderIsomorphisms, arbitrary, cat_disch
-/
def Cotrident.mkHom [Nonempty J] {s t : Cotrident f} (k : s.pt ⟶ t.pt)
    (w : s.π ≫ k = t.π := by cat_disch) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
    · exact w

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `Cotrident.ext` / `Cotrident.ext` 的定义

English:
definition Cotrident.ext
  signature: [Nonempty J] {s t : Cotrident f} (i : s.pt ≅ t.pt)
  body: Cotrident.mkHom i.hom w
  inv := Cotrident.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

中文:
定义 Cotrident.ext
  签名: [非空 J] {s t : Cotrident f} (i : s.pt ≅ t.pt)
  定义体: Cotrident.mkHom i.hom w
  inv := Cotrident.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

Depends on / 依赖: Cotrident, Cotrident.mkHom, Iso.comp_inv_eq, cat_disch, comp_inv_eq, i.hom, i.inv
-/
def Cotrident.ext [Nonempty J] {s t : Cotrident f} (i : s.pt ≅ t.pt)
    (w : s.π ≫ i.hom = t.π := by cat_disch) : s ≅ t where
  hom := Cotrident.mkHom i.hom w
  inv := Cotrident.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

variable (f)

section

/--
Definition of `HasWideEqualizer` / `HasWideEqualizer` 的定义

English:
abbreviation HasWideEqualizer
  body: HasLimit (parallelFamily f)

中文:
缩写 HasWideEqualizer
  定义体: HasLimit (parallelFamily f)

Depends on / 依赖: HasLimit, parallelFamily
-/
abbrev HasWideEqualizer :=
  HasLimit (parallelFamily f)

variable [HasWideEqualizer f]

/--
Definition of `wideEqualizer` / `wideEqualizer` 的定义

English:
abbreviation wideEqualizer
  signature: : C
  body: limit (parallelFamily f)

中文:
缩写 wideEqualizer
  签名: : C
  定义体: limit (parallelFamily f)

Depends on / 依赖: parallelFamily
-/
abbrev wideEqualizer : C :=
  limit (parallelFamily f)

/--
Definition of `wideEqualizer.ι` / `wideEqualizer.ι` 的定义

English:
abbreviation wideEqualizer.ι
  signature: : wideEqualizer f ⟶ X
  body: limit.π (parallelFamily f) zero

中文:
缩写 wideEqualizer.ι
  签名: : wideEqualizer f ⟶ X
  定义体: limit.π (parallelFamily f) zero

Depends on / 依赖: IsClosedUnderIsomorphisms, parallelFamily
-/
abbrev wideEqualizer.ι : wideEqualizer f ⟶ X :=
  limit.π (parallelFamily f) zero

/--
Definition of `wideEqualizer.trident` / `wideEqualizer.trident` 的定义

English:
abbreviation wideEqualizer.trident
  signature: : Trident f
  body: limit.cone (parallelFamily f)

中文:
缩写 wideEqualizer.trident
  签名: : Trident f
  定义体: limit.cone (parallelFamily f)

Depends on / 依赖: limit.cone, parallelFamily
-/
abbrev wideEqualizer.trident : Trident f :=
  limit.cone (parallelFamily f)

/--
theorem `wideEqualizer.trident_ι` / 定理 `wideEqualizer.trident_ι`

English:
theorem wideEqualizer.trident_ι
  statement: (wideEqualizer.trident f).ι = wideEqualizer.ι f
  proof: rfl

中文:
定理 wideEqualizer.trident_ι
  结论: (wideEqualizer.trident f).ι = wideEqualizer.ι f
  证明: rfl
-/
theorem wideEqualizer.trident_ι : (wideEqualizer.trident f).ι = wideEqualizer.ι f :=
  rfl

/--
theorem `wideEqualizer.trident_π_app_zero` / 定理 `wideEqualizer.trident_π_app_zero`

English:
theorem wideEqualizer.trident_π_app_zero
  proof: rfl

@[reassoc]

中文:
定理 wideEqualizer.trident_π_app_zero
  证明: rfl

@[reassoc]
-/
theorem wideEqualizer.trident_π_app_zero :
    (wideEqualizer.trident f).π.app zero = wideEqualizer.ι f :=
  rfl

@[reassoc]
/--
theorem `wideEqualizer.condition` / 定理 `wideEqualizer.condition`

English:
theorem wideEqualizer.condition
  given: (j₁ j₂ : J)
  statement: wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂
  proof: Trident.condition j₁ j₂ limit.cone parallelFamily f

中文:
定理 wideEqualizer.condition
  条件: (j₁ j₂ : J)
  结论: wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂
  证明: Trident.condition j₁ j₂ limit.cone parallelFamily f

Depends on / 依赖: Trident, Trident.condition, condition, limit.cone, parallelFamily
-/
theorem wideEqualizer.condition (j₁ j₂ : J) : wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂ :=
Trident.condition j₁ j₂ limit.cone parallelFamily f

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `wideEqualizerIsWideEqualizer` / `wideEqualizerIsWideEqualizer` 的定义

English:
definition wideEqualizerIsWideEqualizer
  signature: [Nonempty J]
  body: IsLimit.ofIsoLimit (limit.isLimit _) (Trident.ext (Iso.refl _))

中文:
定义 wideEqualizerIsWideEqualizer
  签名: [非空 J]
  定义体: IsLimit.ofIsoLimit (limit.isLimit _) (Trident.ext (Iso.refl _))

Depends on / 依赖: IsLimit, IsLimit.ofIsoLimit, Iso.refl, Trident, Trident.ext, isLimit, limit.isLimit, ofIsoLimit
-/
def wideEqualizerIsWideEqualizer [Nonempty J] :
    IsLimit (Trident.ofι (wideEqualizer.ι f) (wideEqualizer.condition f)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Trident.ext (Iso.refl _))

variable {f}

/--
Definition of `wideEqualizer.lift` / `wideEqualizer.lift` 的定义

English:
abbreviation wideEqualizer.lift
  signature: [Nonempty J] {W : C} (k : W ⟶ X) (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂)
  body: limit.lift (parallelFamily f) (Trident.ofι k h)

中文:
缩写 wideEqualizer.lift
  签名: [非空 J] {W : C} (k : W ⟶ X) (h : 对任意 j₁ j₂, k ≫ f j₁ = k ≫ f j₂)
  定义体: limit.lift (parallelFamily f) (Trident.ofι k h)

Depends on / 依赖: Trident, Trident.of, limit.lift, parallelFamily
-/
abbrev wideEqualizer.lift [Nonempty J] {W : C} (k : W ⟶ X) (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    W ⟶ wideEqualizer f :=
  limit.lift (parallelFamily f) (Trident.ofι k h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `wideEqualizer.lift_ι` / 定理 `wideEqualizer.lift_ι`

English:
theorem wideEqualizer.lift_ι
  statement: [Nonempty J] {W : C} (k : W ⟶ X)
  proof: by
  simp

中文:
定理 wideEqualizer.lift_ι
  结论: [非空 J] {W : C} (k : W ⟶ X)
  证明: by
  simp
-/
theorem wideEqualizer.lift_ι [Nonempty J] {W : C} (k : W ⟶ X)
    (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    wideEqualizer.lift k h ≫ wideEqualizer.ι f = k := by
  simp

/--
Definition of `wideEqualizer.lift'` / `wideEqualizer.lift'` 的定义

English:
definition wideEqualizer.lift'
  signature: [Nonempty J] {W : C} (k : W ⟶ X) (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂)
  body: ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩

中文:
定义 wideEqualizer.lift'
  签名: [非空 J] {W : C} (k : W ⟶ X) (h : 对任意 j₁ j₂, k ≫ f j₁ = k ≫ f j₂)
  定义体: ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩

Depends on / 依赖: wideEqualizer, wideEqualizer.lift, wideEqualizer.lift_
-/
def wideEqualizer.lift' [Nonempty J] {W : C} (k : W ⟶ X) (h : forall j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    { l : W ⟶ wideEqualizer f // l ≫ wideEqualizer.ι f = k } :=
  ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩

/-- Two maps into a wide equalizer are equal if they are equal when composed with the wide
    equalizer map. -/
@[ext]
/--
theorem `wideEqualizer.hom_ext` / 定理 `wideEqualizer.hom_ext`

English:
theorem wideEqualizer.hom_ext
  statement: [Nonempty J] {W : C} {k l : W ⟶ wideEqualizer f}
  proof: Trident.IsLimit.hom_ext (limit.isLimit _) h

中文:
定理 wideEqualizer.hom_ext
  结论: [非空 J] {W : C} {k l : W ⟶ wideEqualizer f}
  证明: Trident.IsLimit.hom_ext (limit.isLimit _) h

Depends on / 依赖: IsLimit, Trident, Trident.IsLimit.hom_ext, hom_ext, isLimit, limit.isLimit
-/
theorem wideEqualizer.hom_ext [Nonempty J] {W : C} {k l : W ⟶ wideEqualizer f}
    (h : k ≫ wideEqualizer.ι f = l ≫ wideEqualizer.ι f) : k = l :=
  Trident.IsLimit.hom_ext (limit.isLimit _) h

/--
Instance `wideEqualizer.ι_mono` / 实例 `wideEqualizer.ι_mono`

English:
instance wideEqualizer.ι_mono
  signature: [Nonempty J]
  body: wideEqualizer.hom_ext w

中文:
实例 wideEqualizer.ι_mono
  签名: [非空 J]
  定义体: wideEqualizer.hom_ext w

Depends on / 依赖: hom_ext, wideEqualizer, wideEqualizer.hom_ext
-/
instance wideEqualizer.ι_mono [Nonempty J] : Mono (wideEqualizer.ι f) where
  right_cancellation _ _ w := wideEqualizer.hom_ext w

end

section

variable {f}

/--
theorem `mono_of_isLimit_parallelFamily` / 定理 `mono_of_isLimit_parallelFamily`

English:
theorem mono_of_isLimit_parallelFamily
  given: [Nonempty J] {c : Cone (parallelFamily f)} (i : IsLimit c)
  proof: Trident.IsLimit.hom_ext i w

中文:
定理 mono_of_isLimit_parallelFamily
  条件: [非空 J] {c : 锥 (parallelFamily f)} (i : 是极限 c)
  证明: Trident.IsLimit.hom_ext i w

Depends on / 依赖: IsLimit, Trident, Trident.IsLimit.hom_ext, hom_ext
-/
theorem mono_of_isLimit_parallelFamily [Nonempty J] {c : Cone (parallelFamily f)} (i : IsLimit c) :
    Mono (Trident.ι c) where
  right_cancellation _ _ w := Trident.IsLimit.hom_ext i w

end

section

/--
Definition of `HasWideCoequalizer` / `HasWideCoequalizer` 的定义

English:
abbreviation HasWideCoequalizer
  body: HasColimit (parallelFamily f)

中文:
缩写 HasWideCoequalizer
  定义体: HasColimit (parallelFamily f)

Depends on / 依赖: HasColimit, parallelFamily
-/
abbrev HasWideCoequalizer :=
  HasColimit (parallelFamily f)

variable [HasWideCoequalizer f]

/--
Definition of `wideCoequalizer` / `wideCoequalizer` 的定义

English:
abbreviation wideCoequalizer
  signature: : C
  body: colimit (parallelFamily f)

中文:
缩写 wideCoequalizer
  签名: : C
  定义体: colimit (parallelFamily f)

Depends on / 依赖: colimit, parallelFamily
-/
abbrev wideCoequalizer : C :=
  colimit (parallelFamily f)

/--
Definition of `wideCoequalizer.π` / `wideCoequalizer.π` 的定义

English:
abbreviation wideCoequalizer.π
  signature: : Y ⟶ wideCoequalizer f
  body: colimit.ι (parallelFamily f) one

中文:
缩写 wideCoequalizer.π
  签名: : Y ⟶ wideCoequalizer f
  定义体: colimit.ι (parallelFamily f) one

Depends on / 依赖: colimit, parallelFamily
-/
abbrev wideCoequalizer.π : Y ⟶ wideCoequalizer f :=
  colimit.ι (parallelFamily f) one

/--
Definition of `wideCoequalizer.cotrident` / `wideCoequalizer.cotrident` 的定义

English:
abbreviation wideCoequalizer.cotrident
  signature: : Cotrident f
  body: colimit.cocone (parallelFamily f)

中文:
缩写 wideCoequalizer.cotrident
  签名: : Cotrident f
  定义体: colimit.cocone (parallelFamily f)

Depends on / 依赖: cocone, colimit, colimit.cocone, parallelFamily
-/
abbrev wideCoequalizer.cotrident : Cotrident f :=
  colimit.cocone (parallelFamily f)

/--
theorem `wideCoequalizer.cotrident_π` / 定理 `wideCoequalizer.cotrident_π`

English:
theorem wideCoequalizer.cotrident_π
  statement: (wideCoequalizer.cotrident f).π = wideCoequalizer.π f
  proof: rfl

中文:
定理 wideCoequalizer.cotrident_π
  结论: (wideCoequalizer.cotrident f).π = wideCoequalizer.π f
  证明: rfl
-/
theorem wideCoequalizer.cotrident_π : (wideCoequalizer.cotrident f).π = wideCoequalizer.π f :=
  rfl

/--
theorem `wideCoequalizer.cotrident_ι_app_one` / 定理 `wideCoequalizer.cotrident_ι_app_one`

English:
theorem wideCoequalizer.cotrident_ι_app_one
  proof: rfl

@[reassoc]

中文:
定理 wideCoequalizer.cotrident_ι_app_one
  证明: rfl

@[reassoc]
-/
theorem wideCoequalizer.cotrident_ι_app_one :
    (wideCoequalizer.cotrident f).ι.app one = wideCoequalizer.π f :=
  rfl

@[reassoc]
/--
theorem `wideCoequalizer.condition` / 定理 `wideCoequalizer.condition`

English:
theorem wideCoequalizer.condition
  given: (j₁ j₂ : J)
  proof: Cotrident.condition j₁ j₂ colimit.cocone parallelFamily f

中文:
定理 wideCoequalizer.condition
  条件: (j₁ j₂ : J)
  证明: Cotrident.condition j₁ j₂ colimit.cocone parallelFamily f

Depends on / 依赖: Cotrident, Cotrident.condition, cocone, colimit, colimit.cocone, condition, parallelFamily
-/
theorem wideCoequalizer.condition (j₁ j₂ : J) :
    f j₁ ≫ wideCoequalizer.π f = f j₂ ≫ wideCoequalizer.π f :=
Cotrident.condition j₁ j₂ colimit.cocone parallelFamily f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `wideCoequalizerIsWideCoequalizer` / `wideCoequalizerIsWideCoequalizer` 的定义

English:
definition wideCoequalizerIsWideCoequalizer
  signature: [Nonempty J]
  body: IsColimit.ofIsoColimit (colimit.isColimit _) (Cotrident.ext (Iso.refl _))

中文:
定义 wideCoequalizerIsWideCoequalizer
  签名: [非空 J]
  定义体: IsColimit.ofIsoColimit (colimit.isColimit _) (Cotrident.ext (Iso.refl _))

Depends on / 依赖: Cotrident, Cotrident.ext, IsColimit, IsColimit.ofIsoColimit, Iso.refl, colimit, colimit.isColimit, isColimit, ofIsoColimit
-/
def wideCoequalizerIsWideCoequalizer [Nonempty J] :
    IsColimit (Cotrident.ofπ (wideCoequalizer.π f) (wideCoequalizer.condition f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cotrident.ext (Iso.refl _))

variable {f}

/--
Definition of `wideCoequalizer.desc` / `wideCoequalizer.desc` 的定义

English:
abbreviation wideCoequalizer.desc
  signature: [Nonempty J] {W : C} (k : Y ⟶ W) (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k)
  body: colimit.desc (parallelFamily f) (Cotrident.ofπ k h)

中文:
缩写 wideCoequalizer.desc
  签名: [非空 J] {W : C} (k : Y ⟶ W) (h : 对任意 j₁ j₂, f j₁ ≫ k = f j₂ ≫ k)
  定义体: colimit.desc (parallelFamily f) (Cotrident.ofπ k h)

Depends on / 依赖: Cotrident, Cotrident.of, colimit, colimit.desc, parallelFamily
-/
abbrev wideCoequalizer.desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer f ⟶ W :=
  colimit.desc (parallelFamily f) (Cotrident.ofπ k h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
theorem `wideCoequalizer.π_desc` / 定理 `wideCoequalizer.π_desc`

English:
theorem wideCoequalizer.π_desc
  statement: [Nonempty J] {W : C} (k : Y ⟶ W)
  proof: by
  simp

中文:
定理 wideCoequalizer.π_desc
  结论: [非空 J] {W : C} (k : Y ⟶ W)
  证明: by
  simp

Depends on / 依赖: Subsingleton, Subsingleton.elim
-/
theorem wideCoequalizer.π_desc [Nonempty J] {W : C} (k : Y ⟶ W)
    (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer.π f ≫ wideCoequalizer.desc k h = k := by
  simp

/--
Definition of `wideCoequalizer.desc'` / `wideCoequalizer.desc'` 的定义

English:
definition wideCoequalizer.desc'
  signature: [Nonempty J] {W : C} (k : Y ⟶ W) (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k)
  body: ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩

中文:
定义 wideCoequalizer.desc'
  签名: [非空 J] {W : C} (k : Y ⟶ W) (h : 对任意 j₁ j₂, f j₁ ≫ k = f j₂ ≫ k)
  定义体: ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩

Depends on / 依赖: wideCoequalizer, wideCoequalizer.desc
-/
def wideCoequalizer.desc' [Nonempty J] {W : C} (k : Y ⟶ W) (h : forall j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    { l : wideCoequalizer f ⟶ W // wideCoequalizer.π f ≫ l = k } :=
  ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩

/-- Two maps from a wide coequalizer are equal if they are equal when composed with the wide
    coequalizer map -/
@[ext]
/--
theorem `wideCoequalizer.hom_ext` / 定理 `wideCoequalizer.hom_ext`

English:
theorem wideCoequalizer.hom_ext
  statement: [Nonempty J] {W : C} {k l : wideCoequalizer f ⟶ W}
  proof: Cotrident.IsColimit.hom_ext (colimit.isColimit _) h

中文:
定理 wideCoequalizer.hom_ext
  结论: [非空 J] {W : C} {k l : wideCoequalizer f ⟶ W}
  证明: Cotrident.IsColimit.hom_ext (colimit.isColimit _) h

Depends on / 依赖: Cotrident, Cotrident.IsColimit.hom_ext, IsColimit, colimit, colimit.isColimit, hom_ext, isColimit
-/
theorem wideCoequalizer.hom_ext [Nonempty J] {W : C} {k l : wideCoequalizer f ⟶ W}
    (h : wideCoequalizer.π f ≫ k = wideCoequalizer.π f ≫ l) : k = l :=
  Cotrident.IsColimit.hom_ext (colimit.isColimit _) h

/--
Instance `wideCoequalizer.π_epi` / 实例 `wideCoequalizer.π_epi`

English:
instance wideCoequalizer.π_epi
  signature: [Nonempty J]
  body: wideCoequalizer.hom_ext w

中文:
实例 wideCoequalizer.π_epi
  签名: [非空 J]
  定义体: wideCoequalizer.hom_ext w

Depends on / 依赖: hom_ext, wideCoequalizer, wideCoequalizer.hom_ext
-/
instance wideCoequalizer.π_epi [Nonempty J] : Epi (wideCoequalizer.π f) where
  left_cancellation _ _ w := wideCoequalizer.hom_ext w

end

section

variable {f}

/--
theorem `epi_of_isColimit_parallelFamily` / 定理 `epi_of_isColimit_parallelFamily`

English:
theorem epi_of_isColimit_parallelFamily
  statement: [Nonempty J] {c : Cocone (parallelFamily f)}
  proof: Cotrident.IsColimit.hom_ext i w

中文:
定理 epi_of_isColimit_parallelFamily
  结论: [非空 J] {c : 余锥 (parallelFamily f)}
  证明: Cotrident.IsColimit.hom_ext i w

Depends on / 依赖: Cotrident, Cotrident.IsColimit.hom_ext, IsColimit, hom_ext
-/
theorem epi_of_isColimit_parallelFamily [Nonempty J] {c : Cocone (parallelFamily f)}
    (i : IsColimit c) : Epi (c.ι.app one) where
  left_cancellation _ _ w := Cotrident.IsColimit.hom_ext i w

end

variable (C)

/--
Definition of `HasWideEqualizers` / `HasWideEqualizers` 的定义

English:
abbreviation HasWideEqualizers
  body: forall J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C

中文:
缩写 HasWideEqualizers
  定义体: forall J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C

Depends on / 依赖: HasLimitsOfShape, WalkingParallelFamily
-/
abbrev HasWideEqualizers :=
  forall J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C

/--
Definition of `HasWideCoequalizers` / `HasWideCoequalizers` 的定义

English:
abbreviation HasWideCoequalizers
  body: forall J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C

中文:
缩写 HasWideCoequalizers
  定义体: forall J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C

Depends on / 依赖: HasColimitsOfShape, WalkingParallelFamily
-/
abbrev HasWideCoequalizers :=
  forall J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C

/--
theorem `hasWideEqualizers_of_hasLimit_parallelFamily` / 定理 `hasWideEqualizers_of_hasLimit_parallelFamily`

English:
theorem hasWideEqualizers_of_hasLimit_parallelFamily
  proof: fun _ =>
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelFamily F).symm }

中文:
定理 hasWideEqualizers_of_hasLimit_parallelFamily
  证明: fun _ =>
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelFamily F).symm }
-/
theorem hasWideEqualizers_of_hasLimit_parallelFamily
    [forall {J : Type w} {X Y : C} {f : J -> (X ⟶ Y)}, HasLimit (parallelFamily f)] :
    HasWideEqualizers.{w} C := fun _ =>
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelFamily F).symm }

/--
theorem `hasWideCoequalizers_of_hasColimit_parallelFamily` / 定理 `hasWideCoequalizers_of_hasColimit_parallelFamily`

English:
theorem hasWideCoequalizers_of_hasColimit_parallelFamily
  proof: fun _ =>
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelFamily F) }

中文:
定理 hasWideCoequalizers_of_hasColimit_parallelFamily
  证明: fun _ =>
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelFamily F) }
-/
theorem hasWideCoequalizers_of_hasColimit_parallelFamily
    [forall {J : Type w} {X Y : C} {f : J -> (X ⟶ Y)}, HasColimit (parallelFamily f)] :
    HasWideCoequalizers.{w} C := fun _ =>
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelFamily F) }

instance (priority := 10) hasEqualizers_of_hasWideEqualizers [HasWideEqualizers.{w} C] :
    HasEqualizers C :=
  hasLimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair

instance (priority := 10) hasCoequalizers_of_hasWideCoequalizers [HasWideCoequalizers.{w} C] :
    HasCoequalizers C :=
  hasColimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair

end CategoryTheory.Limits
