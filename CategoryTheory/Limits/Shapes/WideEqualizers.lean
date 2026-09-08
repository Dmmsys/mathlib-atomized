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

/-- The type of objects for the diagram indexing a wide (co)equalizer. -/
/-
**CategoryTheory.Limits.WalkingParallelFamily** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：Type w → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of objects for the diagram indexing a wide (co)equalizer.
-/
inductive WalkingParallelFamily (J : Type w) : Type w
  | zero : WalkingParallelFamily J
  | one : WalkingParallelFamily J
deriving Inhabited

open WalkingParallelFamily

-- We do not use `deriving DecidableEq` here
-- because it generates an instance with unnecessary hypotheses.
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DecidableEq (WalkingParallelFamily J)
  | zero, zero => isTrue rfl
  | zero, one => isFalse fun t => by grind
  | one, zero => isFalse fun t => by grind
  | one, one => isTrue rfl

-- Don't generate unnecessary `sizeOf_spec` lemma which the `simpNF` linter will complain about.
set_option genSizeOfSpec false in
/-- The type family of morphisms for the diagram indexing a wide (co)equalizer. -/
/-
**CategoryTheory.Limits.WalkingParallelFamily.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `C
ategoryTheory.Limits.WalkingParallelFamily`。
形式化陈述：(J : Type w) → CategoryTheory.Limits.WalkingParallelFamily J → CategoryThe
ory.Limits.WalkingParallelFamily J → Type w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type family of morphisms for the diagram indexing a wide (co)equalizer.
-/
inductive WalkingParallelFamily.Hom (J : Type w) :
  WalkingParallelFamily J → WalkingParallelFamily J → Type w
  | id : ∀ X : WalkingParallelFamily.{w} J, WalkingParallelFamily.Hom J X X
  | line : J → WalkingParallelFamily.Hom J zero one
  deriving DecidableEq

/-- Satisfying the inhabited linter -/
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Satisfying the inhabited linter
-/
instance (J : Type v) : Inhabited (WalkingParallelFamily.Hom J zero zero) where default := Hom.id _

open WalkingParallelFamily.Hom

/-- Composition of morphisms in the indexing diagram for wide (co)equalizers. -/
/-
**CategoryTheory.Limits.WalkingParallelFamily.Hom.comp** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.WalkingParallelFamily.Hom`。
形式化陈述：{J : Type w} →   {X Y Z : CategoryTheory.Limits.WalkingParallelFamily J} →
     CategoryTheory.Limits.WalkingParallelFamily.Hom J X Y →       CategoryTheor
y.Limits.WalkingParallelFamily.Hom J Y Z → CategoryTheory.Limits.WalkingParallel
Family.Hom J X Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of morphisms in the indexing diagram for wide (co)equalizers.
-/
def WalkingParallelFamily.Hom.comp :
    ∀ {X Y Z : WalkingParallelFamily J} (_ : WalkingParallelFamily.Hom J X Y)
      (_ : WalkingParallelFamily.Hom J Y Z), WalkingParallelFamily.Hom J X Z
  | _, _, _, id _, h => h
  | _, _, _, line j, id one => line j

attribute [local aesop safe cases] WalkingParallelFamily.Hom
/-
**CategoryTheory.Limits.WalkingParallelFamily.category** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits.WalkingParallelFamily`。
形式化陈述：{J : Type w} → CategoryTheory.SmallCategory (CategoryTheory.Limits.Walking
ParallelFamily J)
参数：CategoryTheory.Limits.WalkingParallelFamily J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance WalkingParallelFamily.category : SmallCategory (WalkingParallelFamily J) where
  Hom := WalkingParallelFamily.Hom J
  id := WalkingParallelFamily.Hom.id
  comp := WalkingParallelFamily.Hom.comp

@[simp]
/-
**CategoryTheory.Limits.WalkingParallelFamily.hom_id** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.Limits.WalkingParallelFamily`。
形式化陈述：∀ {J : Type w} (X : CategoryTheory.Limits.WalkingParallelFamily J),   Cate
goryTheory.Limits.WalkingParallelFamily.Hom.id X = CategoryTheory.CategoryStruct
.id X
参数：X : CategoryTheory.Limits.WalkingParallelFamily J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem WalkingParallelFamily.hom_id (X : WalkingParallelFamily J) :
    WalkingParallelFamily.Hom.id X = 𝟙 X :=
  rfl

variable (J) in
/-- `Arrow (WalkingParallelFamily J)` identifies to the type obtained
by adding two elements to `T`. -/
/-
**CategoryTheory.Limits.WalkingParallelFamily.arrowEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits.WalkingParallelFamily`。
形式化陈述：(J : Type w) → CategoryTheory.Arrow (CategoryTheory.Limits.WalkingParallel
Family J) ≃ Option (Option J)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Arrow (WalkingParallelFamily J)` identifies to the type obtained
by adding two elements to `T`.
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
variable {X Y : C} (f : J → (X ⟶ Y))

/-- `parallelFamily f` is the diagram in `C` consisting of the given family of morphisms, each with
common domain and codomain.
-/
/-
**CategoryTheory.Limits.parallelFamily** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits`。
形式化陈述：parallelFamily : WalkingParallelFamily J ⥤ C where obj x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`parallelFamily f` is the diagram in `C` consisting of the given family of morph
isms, each with
common domain and codomain.
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
/-
**CategoryTheory.Limits.parallelFamily_obj_zero** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：parallelFamily_obj_zero : (parallelFamily f).obj zero = X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelFamily_obj_zero : (parallelFamily f).obj zero = X :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.parallelFamily_obj_one** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：parallelFamily_obj_one : (parallelFamily f).obj one = Y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelFamily_obj_one : (parallelFamily f).obj one = Y :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.parallelFamily_map_left** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：parallelFamily_map_left {j : J} : (parallelFamily f).map (line j) = f j
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem parallelFamily_map_left {j : J} : (parallelFamily f).map (line j) = f j :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, equal) to a
    `parallelFamily` -/
@[simps!]
/-
**CategoryTheory.Limits.diagramIsoParallelFamily** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：diagramIsoParallelFamily (F : WalkingParallelFamily J ⥤ C) : F ≅ parallelF
amily fun j => F.map (line j)
参数：F : WalkingParallelFamily J ⥤ C。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every functor indexing a wide (co)equalizer is naturally isomorphic (actually, e
qual) to a
    `parallelFamily`
-/
def diagramIsoParallelFamily (F : WalkingParallelFamily J ⥤ C) :
    F ≅ parallelFamily fun j => F.map (line j) :=
  NatIso.ofComponents (fun j => eqToIso <| by cases j <;> cat_disch) <| by
    rintro _ _ (_ | _) <;> cat_disch

set_option backward.defeqAttrib.useBackward true in
/-- `WalkingParallelPair` as a category is equivalent to a special case of
`WalkingParallelFamily`. -/
@[simps!]
/-
**CategoryTheory.Limits.walkingParallelFamilyEquivWalkingParallelPair** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：walkingParallelFamilyEquivWalkingParallelPair : WalkingParallelFamily.{w} 
(ULift Bool) ≌ WalkingParallelPair where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`WalkingParallelPair` as a category is equivalent to a special case of
`WalkingParallelFamily`.
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

/-- A trident on `f` is just a `Cone (parallelFamily f)`. -/
/-
**CategoryTheory.Limits.Trident** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Limi
ts`。
形式化陈述：Trident
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trident on `f` is just a `Cone (parallelFamily f)`.
-/
abbrev Trident :=
  Cone (parallelFamily f)

/-- A cotrident on `f` and `g` is just a `Cocone (parallelFamily f)`. -/
/-
**CategoryTheory.Limits.Cotrident** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Li
mits`。
形式化陈述：Cotrident
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cotrident on `f` and `g` is just a `Cocone (parallelFamily f)`.
-/
abbrev Cotrident :=
  Cocone (parallelFamily f)

variable {f}

/-- A trident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.π.app zero : t.X ⟶ X` and `t.π.app one : t.X ⟶ Y`. Of these, only the first one is
    interesting, and we give it the shorter name `Trident.ι t`. -/
/-
**CategoryTheory.Limits.Trident.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.π.app zero : t.X ⟶ X` and `t.π.app one : t.X ⟶ Y`. Of these, only the fir
st one is
    interesting, and we give it the shorter name `Trident.ι t`.
-/
abbrev Trident.ι (t : Trident f) :=
  t.π.app zero

/-- A cotrident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphisms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the second one is
    interesting, and we give it the shorter name `Cotrident.π t`. -/
/-
**CategoryTheory.Limits.Cotrident.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cotrident `t` on the parallel family `f : J → (X ⟶ Y)` consists of two morphis
ms
    `t.ι.app zero : X ⟶ t.X` and `t.ι.app one : Y ⟶ t.X`. Of these, only the sec
ond one is
    interesting, and we give it the shorter name `Cotrident.π t`.
-/
abbrev Cotrident.π (t : Cotrident f) :=
  t.ι.app one

@[simp]
/-
**CategoryTheory.Limits.Trident.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Trident.ι_eq_app_zero (t : Trident f) : t.ι = t.π.app zero :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Cotrident.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cotrident.π_eq_app_one (t : Cotrident f) : t.π = t.ι.app one :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Trident.app_zero** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits.Trident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)}   (s : CategoryTheory.Limits.Trident f) (j : J),   Categ
oryTheory.CategoryStruct.comp (s.π.app CategoryTheory.Limits.WalkingParallelFami
ly.zero) (f j) =     s.π.app CategoryTheory.Limits.WalkingParallelFamily.one
参数：X ⟶ Y；s : CategoryTheory.Limits.Trident f；j : J；s.π.app CategoryTheory.Limits
.WalkingParallelFamily.zero；f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cone.w`：∀ {J : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C]   
{F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.parallelFamily_map_left`：parallelFamily_map_left {
j : J} : (parallelFamily f).map (line j) = f j
-/
theorem Trident.app_zero (s : Trident f) (j : J) : s.π.app zero ≫ f j = s.π.app one := by
  rw [← s.w (line j), parallelFamily_map_left]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.Cotrident.app_one** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Cotrident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)}   (s : CategoryTheory.Limits.Cotrident f) (j : J),   Cat
egoryTheory.CategoryStruct.comp (f j) (s.ι.app CategoryTheory.Limits.WalkingPara
llelFamily.one) =     s.ι.app CategoryTheory.Limits.WalkingParallelFamily.zero
参数：X ⟶ Y；s : CategoryTheory.Limits.Cotrident f；j : J；f j；s.ι.app CategoryTheory.
Limits.WalkingParallelFamily.one。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cocone.w`：∀ {J : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃, u₃} C] 
  {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.parallelFamily_map_left`：parallelFamily_map_left {
j : J} : (parallelFamily f).map (line j) = f j
-/
theorem Cotrident.app_one (s : Cotrident f) (j : J) : f j ≫ s.ι.app one = s.ι.app zero := by
  rw [← s.w (line j), parallelFamily_map_left]

set_option backward.defeqAttrib.useBackward true in
/-- A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfying
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
@[simps]
/-
**CategoryTheory.Limits.Trident.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A trident on `f : J → (X ⟶ Y)` is determined by the morphism `ι : P ⟶ X` satisfy
ing
`∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂`.
-/
def Trident.ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
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
/-
**CategoryTheory.Limits.Cotrident.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cotrident on `f : J → (X ⟶ Y)` is determined by the morphism `π : Y ⟶ P` satis
fying
`∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π`.
-/
def Cotrident.ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    Cotrident f where
  pt := P
  ι :=
    { app := fun X => WalkingParallelFamily.casesOn X (f (Classical.arbitrary J) ≫ π) π
      naturality := fun i j f => by
        obtain - | k := f
        · simp
        · simp [w (Classical.arbitrary J) k] }
/-
**CategoryTheory.Limits.Trident.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Limit
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Trident.ι_ofι [Nonempty J] {P : C} (ι : P ⟶ X) (w : ∀ j₁ j₂, ι ≫ f j₁ = ι ≫ f j₂) :
    (Trident.ofι ι w).ι = ι :=
  rfl
/-
**CategoryTheory.Limits.Cotrident.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Lim
its`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cotrident.π_ofπ [Nonempty J] {P : C} (π : Y ⟶ P) (w : ∀ j₁ j₂, f j₁ ≫ π = f j₂ ≫ π) :
    (Cotrident.ofπ π w).π = π :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Limits.Trident.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits.Trident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} (j₁ j₂ : J)   (t : CategoryTheory.Limits.Trident f),   C
ategoryTheory.CategoryStruct.comp t.ι (f j₁) = CategoryTheory.CategoryStruct.com
p t.ι (f j₂)
参数：X ⟶ Y；j₁ j₂ : J；t : CategoryTheory.Limits.Trident f；f j₁；f j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Trident.app_zero`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   (s : Categor
yTheory.Limits.Trident f) (j…

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem Trident.condition (j₁ j₂ : J) (t : Trident f) : t.ι ≫ f j₁ = t.ι ≫ f j₂ := by
  rw [t.app_zero, t.app_zero]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Limits.Cotrident.condition** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits.Cotrident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} (j₁ j₂ : J)   (t : CategoryTheory.Limits.Cotrident f),  
 CategoryTheory.CategoryStruct.comp (f j₁) t.π = CategoryTheory.CategoryStruct.c
omp (f j₂) t.π
参数：X ⟶ Y；j₁ j₂ : J；t : CategoryTheory.Limits.Cotrident f；f j₁；f j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.Cotrident.app_one`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   (s : Catego
ryTheory.Limits.Cotrident f) …

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem Cotrident.condition (j₁ j₂ : J) (t : Cotrident f) : f j₁ ≫ t.π = f j₂ ≫ t.π := by
  rw [t.app_one, t.app_one]

set_option backward.isDefEq.respectTransparency false in
/-- To check whether two maps are equalized by both maps of a trident, it suffices to check it for
the first map -/
/-
**CategoryTheory.Limits.Trident.equalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.Trident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [Nonempty J]   (s : CategoryTheory.Limits.Trident f) {W 
: C} {k l : W ⟶ s.pt},   CategoryTheory.CategoryStruct.comp k s.ι = CategoryTheo
ry.CategoryStruct.comp l s.ι →     ∀ (j : CategoryTheory.Limits.WalkingParallelF
amily J),       CategoryTheory.CategoryStruct.comp k (s.π.app j) = CategoryTheor
y.CategoryStruct.comp l (s.π.app j)
参数：X ⟶ Y；s : CategoryTheory.Limits.Trident f；j : CategoryTheory.Limits.WalkingPa
rallelFamily J；s.π.app j；s.π.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Trident.app_zero`：∀ {J : Type w} {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   (s : Categor
yTheory.Limits.Trident f) (j…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h

--- 原说明 ---
To check whether two maps are equalized by both maps of a trident, it suffices t
o check it for
the first map
-/
theorem Trident.equalizer_ext [Nonempty J] (s : Trident f) {W : C} {k l : W ⟶ s.pt}
    (h : k ≫ s.ι = l ≫ s.ι) : ∀ j : WalkingParallelFamily J, k ≫ s.π.app j = l ≫ s.π.app j
  | zero => h
  | one => by rw [← s.app_zero (Classical.arbitrary J), reassoc_of% h]

set_option backward.isDefEq.respectTransparency false in
/-- To check whether two maps are coequalized by both maps of a cotrident, it suffices to check it
for the second map -/
/-
**CategoryTheory.Limits.Cotrident.coequalizer_ext** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.Cotrident`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [Nonempty J]   (s : CategoryTheory.Limits.Cotrident f) {
W : C} {k l : s.pt ⟶ W},   CategoryTheory.CategoryStruct.comp s.π k = CategoryTh
eory.CategoryStruct.comp s.π l →     ∀ (j : CategoryTheory.Limits.WalkingParalle
lFamily J),       CategoryTheory.CategoryStruct.comp (s.ι.app j) k = CategoryThe
ory.CategoryStruct.comp (s.ι.app j) l
参数：X ⟶ Y；s : CategoryTheory.Limits.Cotrident f；j : CategoryTheory.Limits.Walking
ParallelFamily J；s.ι.app j；s.ι.app j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.Cotrident.app_one`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   (s : Catego
ryTheory.Limits.Cotrident f) …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
To check whether two maps are coequalized by both maps of a cotrident, it suffic
es to check it
for the second map
-/
theorem Cotrident.coequalizer_ext [Nonempty J] (s : Cotrident f) {W : C} {k l : s.pt ⟶ W}
    (h : s.π ≫ k = s.π ≫ l) : ∀ j : WalkingParallelFamily J, s.ι.app j ≫ k = s.ι.app j ≫ l
  | zero => by rw [← s.app_one (Classical.arbitrary J), Category.assoc, Category.assoc, h]
  | one => h
/-
**CategoryTheory.Limits.Trident.IsLimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.Trident.IsLimit`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [Nonempty J]   {s : CategoryTheory.Limits.Trident f} (hs
 : CategoryTheory.Limits.IsLimit s) {W : C} {k l : W ⟶ s.pt},   CategoryTheory.C
ategoryStruct.comp k s.ι = CategoryTheory.CategoryStruct.comp l s.ι → k = l
参数：X ⟶ Y；hs : CategoryTheory.Limits.IsLimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsLimit.hom_ext`：hom_ext (h : IsLimit t) {W : C} {
f f' : W ⟶ t.pt} (w : forall j, f ≫ t.π.app j = f' ≫ t.π.app j) : f = f'
· 使用定理 `CategoryTheory.Limits.Trident.equalizer_ext`：∀ {J : Type w} {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [Nonempty
 J]   (s : CategoryTheory.Limits.…
-/
theorem Trident.IsLimit.hom_ext [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C}
    {k l : W ⟶ s.pt} (h : k ≫ s.ι = l ≫ s.ι) : k = l :=
  hs.hom_ext <| Trident.equalizer_ext _ h
/-
**CategoryTheory.Limits.Cotrident.IsColimit.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `C
ategoryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [Nonempty J]   {s : CategoryTheory.Limits.Cotrident f} (
hs : CategoryTheory.Limits.IsColimit s) {W : C} {k l : s.pt ⟶ W},   CategoryTheo
ry.CategoryStruct.comp s.π k = CategoryTheory.CategoryStruct.comp s.π l → k = l
参数：X ⟶ Y；hs : CategoryTheory.Limits.IsColimit s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsColimit.hom_ext`：∀ {J : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{v₃
, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.Cotrident.coequalizer_ext`：∀ {J : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [None
mpty J]   (s : CategoryTheory.Limits.…
-/
theorem Cotrident.IsColimit.hom_ext [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C}
    {k l : s.pt ⟶ W} (h : s.π ≫ k = s.π ≫ l) : k = l :=
  hs.hom_ext <| Cotrident.coequalizer_ext _ h

/-- If `s` is a limit trident over `f`, then a morphism `k : W ⟶ X` satisfying
    `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism `l : W ⟶ s.X` such that
    `l ≫ Trident.ι s = k`. -/
/-
**CategoryTheory.Limits.Trident.IsLimit.lift'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.Trident.IsLimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s : CategoryTheory.Limits.Trident f} →               CategoryTheory.Li
mits.IsLimit s →                 {W : C} →                   (k : W ⟶ X) →      
               (∀ (j₁ j₂ : J),                         CategoryTheory.CategorySt
ruct.comp k (f j₁) = CategoryTheory.CategoryStruct.comp k (f j₂)) →             
          { l // CategoryTheory.CategoryStruct.comp l s.ι = k }
参数：X ⟶ Y；k : W ⟶ X；∀ (j₁ j₂ : J),                         CategoryTheory.Categor
yStruct.comp k (f j₁) = CategoryTheory.CategoryStruct.comp k (f j₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a limit trident over `f`, then a morphism `k : W ⟶ X` satisfying
    `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism `l : W ⟶ s.X` such that
    `l ≫ Trident.ι s = k`.
-/
def Trident.IsLimit.lift' [Nonempty J] {s : Trident f} (hs : IsLimit s) {W : C} (k : W ⟶ X)
    (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) : { l : W ⟶ s.pt // l ≫ Trident.ι s = k } :=
  ⟨hs.lift <| Trident.ofι _ h, hs.fac _ _⟩

/-- If `s` is a colimit cotrident over `f`, then a morphism `k : Y ⟶ W` satisfying
    `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism `l : s.X ⟶ W` such that
    `Cotrident.π s ≫ l = k`. -/
/-
**CategoryTheory.Limits.Cotrident.IsColimit.desc'** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s : CategoryTheory.Limits.Cotrident f} →               CategoryTheory.
Limits.IsColimit s →                 {W : C} →                   (k : Y ⟶ W) →  
                   (∀ (j₁ j₂ : J),                         CategoryTheory.Catego
ryStruct.comp (f j₁) k = CategoryTheory.CategoryStruct.comp (f j₂) k) →         
              { l // CategoryTheory.CategoryStruct.comp s.π l = k }
参数：X ⟶ Y；k : Y ⟶ W；∀ (j₁ j₂ : J),                         CategoryTheory.Categor
yStruct.comp (f j₁) k = CategoryTheory.CategoryStruct.comp (f j₂) k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s` is a colimit cotrident over `f`, then a morphism `k : Y ⟶ W` satisfying
    `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism `l : s.X ⟶ W` such that
    `Cotrident.π s ≫ l = k`.
-/
def Cotrident.IsColimit.desc' [Nonempty J] {s : Cotrident f} (hs : IsColimit s) {W : C} (k : Y ⟶ W)
    (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) : { l : s.pt ⟶ W // Cotrident.π s ≫ l = k } :=
  ⟨hs.desc <| Cotrident.ofπ _ h, hs.fac _ _⟩

/-- This is a slightly more convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.Trident.IsLimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Trident.IsLimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         (t : CategoryTheory.Limits.Trident f) →               (lift : (s : Cate
goryTheory.Limits.Trident f) → s.pt ⟶ t.pt) →                 (∀ (s : CategoryTh
eory.Limits.Trident f), CategoryTheory.CategoryStruct.comp (lift s) t.ι = s.ι) →
                   (∀ (s : CategoryTheory.Limits.Trident f) (m : s.pt ⟶ t.pt),  
                     (∀ (j : CategoryTheory.Limits.WalkingParallelFamily J),    
                       CategoryTheory.CategoryStruct.comp m (t.π.app j) = s.π.ap
p j) →                         m = lift s) →                     CategoryTheory.
Limits.IsLimit t
参数：X ⟶ Y；t : CategoryTheory.Limits.Trident f；lift : (s : CategoryTheory.Limits.T
rident f) → s.pt ⟶ t.pt；∀ (s : CategoryTheory.Limits.Trident f), CategoryTheory.
CategoryStruct.comp (lift s) t.ι = s.ι；∀ (s : CategoryTheory.Limits.Trident f) (
m : s.pt ⟶ t.pt),                       (∀ (j : CategoryTheory.Limits.WalkingPar
allelFamily J),                           CategoryTheory.CategoryStruct.comp m (
t.π.app j) = s.π.app j) →                         m = lift s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a trident is a limit co
ne. It
    only asks for a proof of facts that carry any mathematical content
-/
def Trident.IsLimit.mk [Nonempty J] (t : Trident f) (lift : ∀ s : Trident f, s.pt ⟶ t.pt)
    (fac : ∀ s : Trident f, lift s ≫ t.ι = s.ι)
    (uniq :
      ∀ (s : Trident f) (m : s.pt ⟶ t.pt)
        (_ : ∀ j : WalkingParallelFamily J, m ≫ t.π.app j = s.π.app j), m = lift s) :
    IsLimit t :=
  { lift
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (fac s)
        (by rw [← t.w (line (Classical.arbitrary J)), reassoc_of% fac, s.w])
    uniq := uniq }

/-- This is another convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
/-
**CategoryTheory.Limits.Trident.IsLimit.mk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.Trident.IsLimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         (t : CategoryTheory.Limits.Trident f) →               ((s : CategoryThe
ory.Limits.Trident f) →                   { l //                     CategoryThe
ory.CategoryStruct.comp l t.ι = s.ι ∧                       ∀                   
      {m :                           ((CategoryTheory.Functor.const (CategoryThe
ory.Limits.WalkingParallelFamily J)).obj s.pt).obj                              
 CategoryTheory.Limits.WalkingParallelFamily.zero ⟶                             
((CategoryTheory.Functor.const (CategoryTheory.Limits.WalkingParallelFamily J)).
obj                                   t.pt).obj                               Ca
tegoryTheory.Limits.WalkingParallelFamily.zero},                         Categor
yTheory.CategoryStruct.comp m t.ι = s.ι → m = l }) →                 CategoryThe
ory.Limits.IsLimit t
参数：X ⟶ Y；t : CategoryTheory.Limits.Trident f；(s : CategoryTheory.Limits.Trident 
f) →                   { l //                     CategoryTheory.CategoryStruct.
comp l t.ι = s.ι ∧                       ∀                         {m :         
                  ((CategoryTheory.Functor.const (CategoryTheory.Limits.WalkingP
arallelFamily J)).obj s.pt).obj                               CategoryTheory.Lim
its.WalkingParallelFamily.zero ⟶                             ((CategoryTheory.Fu
nctor.const (CategoryTheory.Limits.WalkingParallelFamily J)).obj                
                   t.pt).obj                               CategoryTheory.Limits
.WalkingParallelFamily.zero},                         CategoryTheory.CategoryStr
uct.comp m t.ι = s.ι → m = l }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a trident is a limit cone. It
    only asks for a proof of facts that carry any mathematical content, and allo
ws access to the
    same `s` for all parts.
-/
def Trident.IsLimit.mk' [Nonempty J] (t : Trident f)
    (create : ∀ s : Trident f, { l // l ≫ t.ι = s.ι ∧ ∀ {m}, m ≫ t.ι = s.ι → m = l }) :
    IsLimit t :=
  Trident.IsLimit.mk t (fun s => (create s).1) (fun s => (create s).2.1) fun s _ w =>
    (create s).2.2 (w zero)

set_option backward.isDefEq.respectTransparency false in
/-- This is a slightly more convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content -/
/-
**CategoryTheory.Limits.Cotrident.IsColimit.mk** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         (t : CategoryTheory.Limits.Cotrident f) →               (desc : (s : Ca
tegoryTheory.Limits.Cotrident f) → t.pt ⟶ s.pt) →                 (∀ (s : Catego
ryTheory.Limits.Cotrident f), CategoryTheory.CategoryStruct.comp t.π (desc s) = 
s.π) →                   (∀ (s : CategoryTheory.Limits.Cotrident f) (m : t.pt ⟶ 
s.pt),                       (∀ (j : CategoryTheory.Limits.WalkingParallelFamily
 J),                           CategoryTheory.CategoryStruct.comp (t.ι.app j) m 
= s.ι.app j) →                         m = desc s) →                     Categor
yTheory.Limits.IsColimit t
参数：X ⟶ Y；t : CategoryTheory.Limits.Cotrident f；desc : (s : CategoryTheory.Limits
.Cotrident f) → t.pt ⟶ s.pt；∀ (s : CategoryTheory.Limits.Cotrident f), CategoryT
heory.CategoryStruct.comp t.π (desc s) = s.π；∀ (s : CategoryTheory.Limits.Cotrid
ent f) (m : t.pt ⟶ s.pt),                       (∀ (j : CategoryTheory.Limits.Wa
lkingParallelFamily J),                           CategoryTheory.CategoryStruct.
comp (t.ι.app j) m = s.ι.app j) →                         m = desc s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a slightly more convenient method to verify that a cotrident is a colimi
t cocone. It
    only asks for a proof of facts that carry any mathematical content
-/
def Cotrident.IsColimit.mk [Nonempty J] (t : Cotrident f) (desc : ∀ s : Cotrident f, t.pt ⟶ s.pt)
    (fac : ∀ s : Cotrident f, t.π ≫ desc s = s.π)
    (uniq :
      ∀ (s : Cotrident f) (m : t.pt ⟶ s.pt)
        (_ : ∀ j : WalkingParallelFamily J, t.ι.app j ≫ m = s.ι.app j), m = desc s) :
    IsColimit t :=
  { desc
    fac := fun s j =>
      WalkingParallelFamily.casesOn j (by rw [← t.w_assoc (line (Classical.arbitrary J)), fac, s.w])
        (fac s)
    uniq := uniq }

/-- This is another convenient method to verify that a cotrident is a colimit cocone. It
    only asks for a proof of facts that carry any mathematical content, and allows access to the
    same `s` for all parts. -/
/-
**CategoryTheory.Limits.Cotrident.IsColimit.mk'** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         (t : CategoryTheory.Limits.Cotrident f) →               ((s : CategoryT
heory.Limits.Cotrident f) →                   { l //                     Categor
yTheory.CategoryStruct.comp t.π l = s.π ∧                       ∀               
          {m :                           ((CategoryTheory.Functor.const (Categor
yTheory.Limits.WalkingParallelFamily J)).obj t.pt).obj                          
     CategoryTheory.Limits.WalkingParallelFamily.one ⟶                          
   ((CategoryTheory.Functor.const (CategoryTheory.Limits.WalkingParallelFamily J
)).obj                                   s.pt).obj                              
 CategoryTheory.Limits.WalkingParallelFamily.one},                         Categ
oryTheory.CategoryStruct.comp t.π m = s.π → m = l }) →                 CategoryT
heory.Limits.IsColimit t
参数：X ⟶ Y；t : CategoryTheory.Limits.Cotrident f；(s : CategoryTheory.Limits.Cotrid
ent f) →                   { l //                     CategoryTheory.CategoryStr
uct.comp t.π l = s.π ∧                       ∀                         {m :     
                      ((CategoryTheory.Functor.const (CategoryTheory.Limits.Walk
ingParallelFamily J)).obj t.pt).obj                               CategoryTheory
.Limits.WalkingParallelFamily.one ⟶                             ((CategoryTheory
.Functor.const (CategoryTheory.Limits.WalkingParallelFamily J)).obj             
                      s.pt).obj                               CategoryTheory.Lim
its.WalkingParallelFamily.one},                         CategoryTheory.CategoryS
truct.comp t.π m = s.π → m = l }。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is another convenient method to verify that a cotrident is a colimit cocone
. It
    only asks for a proof of facts that carry any mathematical content, and allo
ws access to the
    same `s` for all parts.
-/
def Cotrident.IsColimit.mk' [Nonempty J] (t : Cotrident f)
    (create :
      ∀ s : Cotrident f, { l : t.pt ⟶ s.pt // t.π ≫ l = s.π ∧ ∀ {m}, t.π ≫ m = s.π → m = l }) :
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
/-
**CategoryTheory.Limits.Trident.IsLimit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Limits.Trident.IsLimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {t : CategoryTheory.Limits.Trident f} →               CategoryTheory.Li
mits.IsLimit t →                 (Z : C) →                   (Z ⟶ t.pt) ≃       
              { h //                       ∀ (j₁ j₂ : J),                       
  CategoryTheory.CategoryStruct.comp h (f j₁) = CategoryTheory.CategoryStruct.co
mp h (f j₂) }
参数：X ⟶ Y；Z : C；Z ⟶ t.pt；j₁ j₂ : J；f j₁；f j₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a limit cone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from
 `Z` to its point
are in bijection with morphisms `h : Z ⟶ X` such that `∀ j₁ j₂, h ≫ f j₁ = h ≫ f
 j₂`.
Further, this bijection is natural in `Z`: see `Trident.Limits.homIso_natural`.
-/
def Trident.IsLimit.homIso [Nonempty J] {t : Trident f} (ht : IsLimit t) (Z : C) :
    (Z ⟶ t.pt) ≃ { h : Z ⟶ X // ∀ j₁ j₂, h ≫ f j₁ = h ≫ f j₂ } where
  toFun k := ⟨k ≫ t.ι, by simp⟩
  invFun h := (Trident.IsLimit.lift' ht _ h.prop).1
  left_inv _ := Trident.IsLimit.hom_ext ht (Trident.IsLimit.lift' _ _ _).prop
  right_inv _ := Subtype.ext (Trident.IsLimit.lift' ht _ _).prop

/-- The bijection of `Trident.IsLimit.homIso` is natural in `Z`. -/
/-
**CategoryTheory.Limits.Trident.IsLimit.homIso_natural** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits.Trident.IsLimit`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [inst_1 : Nonempty J]   {t : CategoryTheory.Limits.Tride
nt f} (ht : CategoryTheory.Limits.IsLimit t) {Z Z' : C} (q : Z' ⟶ Z) (k : Z ⟶ t.
pt),   ↑((CategoryTheory.Limits.Trident.IsLimit.homIso ht Z') (CategoryTheory.Ca
tegoryStruct.comp q k)) =     CategoryTheory.CategoryStruct.comp q ↑((CategoryTh
eory.Limits.Trident.IsLimit.homIso ht Z) k)
参数：X ⟶ Y；ht : CategoryTheory.Limits.IsLimit t；q : Z' ⟶ Z；k : Z ⟶ t.pt；(CategoryT
heory.Limits.Trident.IsLimit.homIso ht Z') (CategoryTheory.CategoryStruct.comp q
 k)；(CategoryTheory.Limits.Trident.IsLimit.homIso ht Z) k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
The bijection of `Trident.IsLimit.homIso` is natural in `Z`.
-/
theorem Trident.IsLimit.homIso_natural [Nonempty J] {t : Trident f} (ht : IsLimit t) {Z Z' : C}
    (q : Z' ⟶ Z) (k : Z ⟶ t.pt) :
    (Trident.IsLimit.homIso ht _ (q ≫ k) : Z' ⟶ X) =
      q ≫ (Trident.IsLimit.homIso ht _ k : Z ⟶ X) :=
  Category.assoc _ _ _

/-- Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`.  Further, this bijection is natural in `Z`: see
`Cotrident.IsColimit.homIso_natural`.
-/
@[simps]
/-
**CategoryTheory.Limits.Cotrident.IsColimit.homIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {t : CategoryTheory.Limits.Cotrident f} →               CategoryTheory.
Limits.IsColimit t →                 (Z : C) →                   (t.pt ⟶ Z) ≃   
                  { h //                       ∀ (j₁ j₂ : J),                   
      CategoryTheory.CategoryStruct.comp (f j₁) h = CategoryTheory.CategoryStruc
t.comp (f j₂) h }
参数：X ⟶ Y；Z : C；t.pt ⟶ Z；j₁ j₂ : J；f j₁；f j₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a colimit cocone for the family `f : J → (X ⟶ Y)`, for any `Z`, morphisms 
from the cocone
point to `Z` are in bijection with morphisms `h : Z ⟶ X` such that
`∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h`.  Further, this bijection is natural in `Z`: see
`Cotrident.IsColimit.homIso_natural`.
-/
def Cotrident.IsColimit.homIso [Nonempty J] {t : Cotrident f} (ht : IsColimit t) (Z : C) :
    (t.pt ⟶ Z) ≃ { h : Y ⟶ Z // ∀ j₁ j₂, f j₁ ≫ h = f j₂ ≫ h } where
  toFun k := ⟨t.π ≫ k, by simp⟩
  invFun h := (Cotrident.IsColimit.desc' ht _ h.prop).1
  left_inv _ := Cotrident.IsColimit.hom_ext ht (Cotrident.IsColimit.desc' _ _ _).prop
  right_inv _ := Subtype.ext (Cotrident.IsColimit.desc' ht _ _).prop

/-- The bijection of `Cotrident.IsColimit.homIso` is natural in `Z`. -/
/-
**CategoryTheory.Limits.Cotrident.IsColimit.homIso_natural** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Limits.Cotrident.IsColimit`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)} [inst_1 : Nonempty J]   {t : CategoryTheory.Limits.Cotri
dent f} {Z Z' : C} (q : Z ⟶ Z') (ht : CategoryTheory.Limits.IsColimit t)   (k : 
t.pt ⟶ Z),   ↑((CategoryTheory.Limits.Cotrident.IsColimit.homIso ht Z') (Categor
yTheory.CategoryStruct.comp k q)) =     CategoryTheory.CategoryStruct.comp (↑((C
ategoryTheory.Limits.Cotrident.IsColimit.homIso ht Z) k)) q
参数：X ⟶ Y；q : Z ⟶ Z'；ht : CategoryTheory.Limits.IsColimit t；k : t.pt ⟶ Z；(Categor
yTheory.Limits.Cotrident.IsColimit.homIso ht Z') (CategoryTheory.CategoryStruct.
comp k q)；↑((CategoryTheory.Limits.Cotrident.IsColimit.homIso ht Z) k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…

--- 原说明 ---
The bijection of `Cotrident.IsColimit.homIso` is natural in `Z`.
-/
theorem Cotrident.IsColimit.homIso_natural [Nonempty J] {t : Cotrident f} {Z Z' : C} (q : Z ⟶ Z')
    (ht : IsColimit t) (k : t.pt ⟶ Z) :
    (Cotrident.IsColimit.homIso ht _ (k ≫ q) : Y ⟶ Z') =
      (Cotrident.IsColimit.homIso ht _ k : Y ⟶ Z) ≫ q :=
  (Category.assoc _ _ _).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is a helper construction that can be useful when verifying that a category has certain wide
    equalizers. Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (fun j ↦ F.map (line j))`, and a trident on `fun j ↦ F.map (line j)`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at
    `hasWideEqualizers_of_hasLimit_parallelFamily`, which you may find to be an easier way of
    achieving your goal. -/
/-
**CategoryTheory.Limits.Cone.ofTrident** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Cone`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : CategoryTheory.Functor (CategoryTheory.Limits.WalkingParallelFa
mily J) C} →         (CategoryTheory.Limits.Trident fun j => F.map (CategoryTheo
ry.Limits.WalkingParallelFamily.Hom.line j)) →           CategoryTheory.Limits.C
one F
参数：CategoryTheory.Limits.WalkingParallelFamily J；CategoryTheory.Limits.Trident f
un j => F.map (CategoryTheory.Limits.WalkingParallelFamily.Hom.line j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has certain wide
    equalizers. Given `F : WalkingParallelFamily ⥤ C`, which is really the same 
as
    `parallelFamily (fun j ↦ F.map (line j))`, and a trident on `fun j ↦ F.map (
line j)`,
    we get a cone on `F`.

    If you're thinking about using this, have a look at
    `hasWideEqualizers_of_hasLimit_parallelFamily`, which you may find to be an 
easier way of
    achieving your goal.
-/
def Cone.ofTrident {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j)) :
    Cone F where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := fun j j' g => by cases g <;> cat_disch }

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- This is a helper construction that can be useful when verifying that a category has all
    coequalizers. Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (fun j ↦ F.map (line j))`, and a cotrident on `fun j ↦ F.map (line j)` we get a
    cocone on `F`.

    If you're thinking about using this, have a look at
    `hasWideCoequalizers_of_hasColimit_parallelFamily`, which you may find to be an easier way
    of achieving your goal. -/
/-
**CategoryTheory.Limits.Cocone.ofCotrident** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cocone`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : CategoryTheory.Functor (CategoryTheory.Limits.WalkingParallelFa
mily J) C} →         (CategoryTheory.Limits.Cotrident fun j => F.map (CategoryTh
eory.Limits.WalkingParallelFamily.Hom.line j)) →           CategoryTheory.Limits
.Cocone F
参数：CategoryTheory.Limits.WalkingParallelFamily J；CategoryTheory.Limits.Cotrident
 fun j => F.map (CategoryTheory.Limits.WalkingParallelFamily.Hom.line j)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is a helper construction that can be useful when verifying that a category 
has all
    coequalizers. Given `F : WalkingParallelFamily ⥤ C`, which is really the sam
e as
    `parallelFamily (fun j ↦ F.map (line j))`, and a cotrident on `fun j ↦ F.map
 (line j)` we get a
    cocone on `F`.

    If you're thinking about using this, have a look at
    `hasWideCoequalizers_of_hasColimit_parallelFamily`, which you may find to be
 an easier way
    of achieving your goal.
-/
def Cocone.ofCotrident {F : WalkingParallelFamily J ⥤ C} (t : Cotrident fun j => F.map (line j)) :
    Cocone F where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := fun j j' g => by cases g <;> simp [Cotrident.app_one t] }

@[simp]
/-
**CategoryTheory.Limits.Cone.ofTrident_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cone.ofTrident_π {F : WalkingParallelFamily J ⥤ C} (t : Trident fun j => F.map (line j))
    (j) : (Cone.ofTrident t).π.app j = t.π.app j ≫ eqToHom (by cases j <;> cat_disch) :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Cocone.ofCotrident_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cocone.ofCotrident_ι {F : WalkingParallelFamily J ⥤ C}
    (t : Cotrident fun j => F.map (line j)) (j) :
    (Cocone.ofCotrident t).ι.app j = eqToHom (by cases j <;> cat_disch) ≫ t.ι.app j :=
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (fun j ↦ F.map (line j))` and a cone on `F`, we get a trident on
    `fun j ↦ F.map (line j)`. -/
/-
**CategoryTheory.Limits.Trident.ofCone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Limits.Trident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : CategoryTheory.Functor (CategoryTheory.Limits.WalkingParallelFa
mily J) C} →         CategoryTheory.Limits.Cone F →           CategoryTheory.Lim
its.Trident fun j => F.map (CategoryTheory.Limits.WalkingParallelFamily.Hom.line
 j)
参数：CategoryTheory.Limits.WalkingParallelFamily J；CategoryTheory.Limits.WalkingPa
rallelFamily.Hom.line j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (fun j ↦ F.map (line j))` and a cone on `F`, we get a triden
t on
    `fun j ↦ F.map (line j)`.
-/
def Trident.ofCone {F : WalkingParallelFamily J ⥤ C} (t : Cone F) :
    Trident fun j => F.map (line j) where
  pt := t.pt
  π :=
    { app := fun X => t.π.app X ≫ eqToHom (by cases X <;> cat_disch)
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (F.map left) (F.map right)` and a cocone on `F`, we get a cotrident on
    `fun j ↦ F.map (line j)`. -/
/-
**CategoryTheory.Limits.Cotrident.ofCocone** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.Cotrident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {F : CategoryTheory.Functor (CategoryTheory.Limits.WalkingParallelFa
mily J) C} →         CategoryTheory.Limits.Cocone F →           CategoryTheory.L
imits.Cotrident fun j => F.map (CategoryTheory.Limits.WalkingParallelFamily.Hom.
line j)
参数：CategoryTheory.Limits.WalkingParallelFamily J；CategoryTheory.Limits.WalkingPa
rallelFamily.Hom.line j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `F : WalkingParallelFamily ⥤ C`, which is really the same as
    `parallelFamily (F.map left) (F.map right)` and a cocone on `F`, we get a co
trident on
    `fun j ↦ F.map (line j)`.
-/
def Cotrident.ofCocone {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) :
    Cotrident fun j => F.map (line j) where
  pt := t.pt
  ι :=
    { app := fun X => eqToHom (by cases X <;> cat_disch) ≫ t.ι.app X
      naturality := by rintro _ _ (_ | _) <;> cat_disch }

@[simp]
/-
**CategoryTheory.Limits.Trident.ofCone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Trident.ofCone_π {F : WalkingParallelFamily J ⥤ C} (t : Cone F) (j) :
    (Trident.ofCone t).π.app j = t.π.app j ≫ eqToHom (by cases j <;> cat_disch) :=
  rfl

@[simp]
/-
**CategoryTheory.Limits.Cotrident.ofCocone_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Cotrident.ofCocone_ι {F : WalkingParallelFamily J ⥤ C} (t : Cocone F) (j) :
    (Cotrident.ofCocone t).ι.app j = eqToHom (by cases j <;> cat_disch) ≫ t.ι.app j :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Helper function for constructing morphisms between wide equalizer tridents.
-/
@[simps]
/-
**CategoryTheory.Limits.Trident.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Trident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s t : CategoryTheory.Limits.Trident f} →               (k : s.pt ⟶ t.p
t) →                 autoParam (CategoryTheory.CategoryStruct.comp k t.ι = s.ι) 
CategoryTheory.Limits.Trident.mkHom._auto_1 →                   (s ⟶ t)
参数：X ⟶ Y；k : s.pt ⟶ t.pt；CategoryTheory.CategoryStruct.comp k t.ι = s.ι；s ⟶ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for constructing morphisms between wide equalizer tridents.
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
/-
**CategoryTheory.Limits.Trident.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Li
mits.Trident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s t : CategoryTheory.Limits.Trident f} →               (i : s.pt ≅ t.p
t) →                 autoParam (CategoryTheory.CategoryStruct.comp i.hom t.ι = s
.ι)                     CategoryTheory.Limits.Trident.ext._auto_1 →             
      (s ≅ t)
参数：X ⟶ Y；i : s.pt ≅ t.pt；CategoryTheory.CategoryStruct.comp i.hom t.ι = s.ι；s ≅ 
t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism between tridents,
it suffices to give an isomorphism between the cone points
and check that it commutes with the `ι` morphisms.
-/
def Trident.ext [Nonempty J] {s t : Trident f} (i : s.pt ≅ t.pt)
    (w : i.hom ≫ t.ι = s.ι := by cat_disch) : s ≅ t where
  hom := Trident.mkHom i.hom w
  inv := Trident.mkHom i.inv (by rw [← w, Iso.inv_hom_id_assoc])

set_option backward.isDefEq.respectTransparency false in
/-- Helper function for constructing morphisms between coequalizer cotridents.
-/
@[simps]
/-
**CategoryTheory.Limits.Cotrident.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Limits.Cotrident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s t : CategoryTheory.Limits.Cotrident f} →               (k : s.pt ⟶ t
.pt) →                 autoParam (CategoryTheory.CategoryStruct.comp s.π k = t.π
)                     CategoryTheory.Limits.Cotrident.mkHom._auto_1 →           
        (s ⟶ t)
参数：X ⟶ Y；k : s.pt ⟶ t.pt；CategoryTheory.CategoryStruct.comp s.π k = t.π；s ⟶ t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Helper function for constructing morphisms between coequalizer cotridents.
-/
def Cotrident.mkHom [Nonempty J] {s t : Cotrident f} (k : s.pt ⟶ t.pt)
    (w : s.π ≫ k = t.π := by cat_disch) : s ⟶ t where
  hom := k
  w := by
    rintro ⟨_ | _⟩
    · simpa using f (Classical.arbitrary J) ≫= w
    · exact w

set_option backward.isDefEq.respectTransparency false in
/-- To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
/-
**CategoryTheory.Limits.Cotrident.ext** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits.Cotrident`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [Nonempty J] →    
         {s t : CategoryTheory.Limits.Cotrident f} →               (i : s.pt ≅ t
.pt) →                 autoParam (CategoryTheory.CategoryStruct.comp s.π i.hom =
 t.π)                     CategoryTheory.Limits.Cotrident.ext._auto_1 →         
          (s ≅ t)
参数：X ⟶ Y；i : s.pt ≅ t.pt；CategoryTheory.CategoryStruct.comp s.π i.hom = t.π；s ≅ 
t。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To construct an isomorphism between cotridents,
it suffices to give an isomorphism between the cocone points
and check that it commutes with the `π` morphisms.
-/
def Cotrident.ext [Nonempty J] {s t : Cotrident f} (i : s.pt ≅ t.pt)
    (w : s.π ≫ i.hom = t.π := by cat_disch) : s ≅ t where
  hom := Cotrident.mkHom i.hom w
  inv := Cotrident.mkHom i.inv (by rw [Iso.comp_inv_eq, w])

variable (f)

section

/-- A family `f` of parallel morphisms has a wide equalizer if the diagram `parallelFamily f` has a
limit. -/
/-
**CategoryTheory.Limits.HasWideEqualizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
形式化陈述：HasWideEqualizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `f` of parallel morphisms has a wide equalizer if the diagram `parallel
Family f` has a
limit.
-/
abbrev HasWideEqualizer :=
  HasLimit (parallelFamily f)

variable [HasWideEqualizer f]

/-- If a wide equalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wideEqualizer f`. -/
/-
**CategoryTheory.Limits.wideEqualizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.Limits`。
形式化陈述：wideEqualizer : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a wide equalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wideEqualizer f`.
-/
abbrev wideEqualizer : C :=
  limit (parallelFamily f)

/-- If a wide equalizer of `f` exists, we can access the inclusion `wideEqualizer f ⟶ X` by
    saying `wideEqualizer.ι f`. -/
/-
**CategoryTheory.Limits.wideEqualizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a wide equalizer of `f` exists, we can access the inclusion `wideEqualizer f 
⟶ X` by
    saying `wideEqualizer.ι f`.
-/
abbrev wideEqualizer.ι : wideEqualizer f ⟶ X :=
  limit.π (parallelFamily f) zero

/-- A wide equalizer cone for a parallel family `f`.
-/
/-
**CategoryTheory.Limits.wideEqualizer.trident** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.wideEqualizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} → (f : J → (X ⟶ Y)) → [CategoryTheory.Limits.HasWideEquali
zer f] → CategoryTheory.Limits.Trident f
参数：f : J → (X ⟶ Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide equalizer cone for a parallel family `f`.
-/
abbrev wideEqualizer.trident : Trident f :=
  limit.cone (parallelFamily f)
/-
**CategoryTheory.Limits.wideEqualizer.trident_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideEqualizer.trident_ι : (wideEqualizer.trident f).ι = wideEqualizer.ι f :=
  rfl
/-
**CategoryTheory.Limits.wideEqualizer.trident_** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideEqualizer.trident_π_app_zero :
    (wideEqualizer.trident f).π.app zero = wideEqualizer.ι f :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.wideEqualizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.wideEqualizer`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} (f : J → (X ⟶ Y))   [inst_1 : CategoryTheory.Limits.HasWideEqualizer f] (j
₁ j₂ : J),   CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.wideEqual
izer.ι f) (f j₁) =     CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits
.wideEqualizer.ι f) (f j₂)
参数：f : J → (X ⟶ Y)；j₁ j₂ : J；CategoryTheory.Limits.wideEqualizer.ι f；f j₁；Catego
ryTheory.Limits.wideEqualizer.ι f；f j₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Trident.condition`：∀ {J : Type w} {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} (j₁ j₂ : J)  
 (t : CategoryTheory.Limits.T…
-/
theorem wideEqualizer.condition (j₁ j₂ : J) : wideEqualizer.ι f ≫ f j₁ = wideEqualizer.ι f ≫ f j₂ :=
  Trident.condition j₁ j₂ <| limit.cone <| parallelFamily f

set_option backward.defeqAttrib.useBackward true in
/-- The wideEqualizer built from `wideEqualizer.ι f` is limiting. -/
/-
**CategoryTheory.Limits.wideEqualizerIsWideEqualizer** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：wideEqualizerIsWideEqualizer [Nonempty J] : IsLimit (Trident.ofι (wideEqua
lizer.ι f) (wideEqualizer.condition f))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.wideEqualizer.condition`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : J → (X ⟶ Y))   [inst
_1 : CategoryTheory.Limits.HasWideE…

--- 原说明 ---
The wideEqualizer built from `wideEqualizer.ι f` is limiting.
-/
def wideEqualizerIsWideEqualizer [Nonempty J] :
    IsLimit (Trident.ofι (wideEqualizer.ι f) (wideEqualizer.condition f)) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Trident.ext (Iso.refl _))

variable {f}

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` factors through the
    wide equalizer of `f` via `wideEqualizer.lift : W ⟶ wideEqualizer f`. -/
/-
**CategoryTheory.Limits.wideEqualizer.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Limits.wideEqualizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [inst_1 : Category
Theory.Limits.HasWideEqualizer f] →             [Nonempty J] →               {W 
: C} →                 (k : W ⟶ X) →                   (∀ (j₁ j₂ : J),          
             CategoryTheory.CategoryStruct.comp k (f j₁) = CategoryTheory.Catego
ryStruct.comp k (f j₂)) →                     (W ⟶ CategoryTheory.Limits.wideEqu
alizer f)
参数：X ⟶ Y；k : W ⟶ X；∀ (j₁ j₂ : J),                       CategoryTheory.CategoryS
truct.comp k (f j₁) = CategoryTheory.CategoryStruct.comp k (f j₂)；W ⟶ CategoryTh
eory.Limits.wideEqualizer f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` factors through
 the
    wide equalizer of `f` via `wideEqualizer.lift : W ⟶ wideEqualizer f`.
-/
abbrev wideEqualizer.lift [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    W ⟶ wideEqualizer f :=
  limit.lift (parallelFamily f) (Trident.ofι k h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.wideEqualizer.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideEqualizer.lift_ι [Nonempty J] {W : C} (k : W ⟶ X)
    (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    wideEqualizer.lift k h ≫ wideEqualizer.ι f = k := by
  simp

/-- A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morphism
    `l : W ⟶ wideEqualizer f` satisfying `l ≫ wideEqualizer.ι f = k`. -/
/-
**CategoryTheory.Limits.wideEqualizer.lift'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Limits.wideEqualizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [inst_1 : Category
Theory.Limits.HasWideEqualizer f] →             [Nonempty J] →               {W 
: C} →                 (k : W ⟶ X) →                   (∀ (j₁ j₂ : J),          
             CategoryTheory.CategoryStruct.comp k (f j₁) = CategoryTheory.Catego
ryStruct.comp k (f j₂)) →                     { l // CategoryTheory.CategoryStru
ct.comp l (CategoryTheory.Limits.wideEqualizer.ι f) = k }
参数：X ⟶ Y；k : W ⟶ X；∀ (j₁ j₂ : J),                       CategoryTheory.CategoryS
truct.comp k (f j₁) = CategoryTheory.CategoryStruct.comp k (f j₂)；CategoryTheory
.Limits.wideEqualizer.ι f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.wideEqualizer.lift_ι`：∀ {J : Type w} {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   [inst_1 
: CategoryTheory.Limits.HasWideE…

--- 原说明 ---
A morphism `k : W ⟶ X` satisfying `∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂` induces a morph
ism
    `l : W ⟶ wideEqualizer f` satisfying `l ≫ wideEqualizer.ι f = k`.
-/
def wideEqualizer.lift' [Nonempty J] {W : C} (k : W ⟶ X) (h : ∀ j₁ j₂, k ≫ f j₁ = k ≫ f j₂) :
    { l : W ⟶ wideEqualizer f // l ≫ wideEqualizer.ι f = k } :=
  ⟨wideEqualizer.lift k h, wideEqualizer.lift_ι _ _⟩

/-- Two maps into a wide equalizer are equal if they are equal when composed with the wide
    equalizer map. -/
@[ext]
/-
**CategoryTheory.Limits.wideEqualizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits.wideEqualizer`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)}   [inst_1 : CategoryTheory.Limits.HasWideEqualizer f] [N
onempty J] {W : C}   {k l : W ⟶ CategoryTheory.Limits.wideEqualizer f},   Catego
ryTheory.CategoryStruct.comp k (CategoryTheory.Limits.wideEqualizer.ι f) =      
 CategoryTheory.CategoryStruct.comp l (CategoryTheory.Limits.wideEqualizer.ι f) 
→     k = l
参数：X ⟶ Y；CategoryTheory.Limits.wideEqualizer.ι f；CategoryTheory.Limits.wideEqual
izer.ι f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Trident.IsLimit.hom_ext`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [Nonemp
ty J]   {s : CategoryTheory.Limits.…

--- 原说明 ---
Two maps into a wide equalizer are equal if they are equal when composed with th
e wide
    equalizer map.
-/
theorem wideEqualizer.hom_ext [Nonempty J] {W : C} {k l : W ⟶ wideEqualizer f}
    (h : k ≫ wideEqualizer.ι f = l ≫ wideEqualizer.ι f) : k = l :=
  Trident.IsLimit.hom_ext (limit.isLimit _) h

/-- A wide equalizer morphism is a monomorphism -/
/-
**CategoryTheory.Limits.wideEqualizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide equalizer morphism is a monomorphism
-/
instance wideEqualizer.ι_mono [Nonempty J] : Mono (wideEqualizer.ι f) where
  right_cancellation _ _ w := wideEqualizer.hom_ext w

end

section

variable {f}

/-- The wide equalizer morphism in any limit cone is a monomorphism. -/
/-
**CategoryTheory.Limits.mono_of_isLimit_parallelFamily** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：mono_of_isLimit_parallelFamily [Nonempty J] {c : Cone (parallelFamily f)} 
(i : IsLimit c) : Mono (Trident.ι c) where right_cancellation _ _ w
参数：parallelFamily f；i : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Trident.IsLimit.hom_ext`：∀ {J : Type w} {C : Type 
u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [Nonemp
ty J]   {s : CategoryTheory.Limits.…

--- 原说明 ---
The wide equalizer morphism in any limit cone is a monomorphism.
-/
theorem mono_of_isLimit_parallelFamily [Nonempty J] {c : Cone (parallelFamily f)} (i : IsLimit c) :
    Mono (Trident.ι c) where
  right_cancellation _ _ w := Trident.IsLimit.hom_ext i w

end

section

/-- A family `f` of parallel morphisms has a wide coequalizer if the diagram `parallelFamily f` has
a colimit. -/
/-
**CategoryTheory.Limits.HasWideCoequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `Category
Theory.Limits`。
形式化陈述：HasWideCoequalizer
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family `f` of parallel morphisms has a wide coequalizer if the diagram `parall
elFamily f` has
a colimit.
-/
abbrev HasWideCoequalizer :=
  HasColimit (parallelFamily f)

variable [HasWideCoequalizer f]

/-- If a wide coequalizer of `f` exists, we can access an arbitrary choice of such by
    saying `wideCoequalizer f`. -/
/-
**CategoryTheory.Limits.wideCoequalizer** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：wideCoequalizer : C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a wide coequalizer of `f` exists, we can access an arbitrary choice of such b
y
    saying `wideCoequalizer f`.
-/
abbrev wideCoequalizer : C :=
  colimit (parallelFamily f)

/-- If a wideCoequalizer of `f` exists, we can access the corresponding projection by
    saying `wideCoequalizer.π f`. -/
/-
**CategoryTheory.Limits.wideCoequalizer.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTh
eory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a wideCoequalizer of `f` exists, we can access the corresponding projection b
y
    saying `wideCoequalizer.π f`.
-/
abbrev wideCoequalizer.π : Y ⟶ wideCoequalizer f :=
  colimit.ι (parallelFamily f) one

/-- An arbitrary choice of coequalizer cocone for a parallel family `f`.
-/
/-
**CategoryTheory.Limits.wideCoequalizer.cotrident** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits.wideCoequalizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} → (f : J → (X ⟶ Y)) → [CategoryTheory.Limits.HasWideCoequa
lizer f] → CategoryTheory.Limits.Cotrident f
参数：f : J → (X ⟶ Y)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An arbitrary choice of coequalizer cocone for a parallel family `f`.
-/
abbrev wideCoequalizer.cotrident : Cotrident f :=
  colimit.cocone (parallelFamily f)
/-
**CategoryTheory.Limits.wideCoequalizer.cotrident_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideCoequalizer.cotrident_π : (wideCoequalizer.cotrident f).π = wideCoequalizer.π f :=
  rfl
/-
**CategoryTheory.Limits.wideCoequalizer.cotrident_** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideCoequalizer.cotrident_ι_app_one :
    (wideCoequalizer.cotrident f).ι.app one = wideCoequalizer.π f :=
  rfl

@[reassoc]
/-
**CategoryTheory.Limits.wideCoequalizer.condition** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits.wideCoequalizer`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} (f : J → (X ⟶ Y))   [inst_1 : CategoryTheory.Limits.HasWideCoequalizer f] 
(j₁ j₂ : J),   CategoryTheory.CategoryStruct.comp (f j₁) (CategoryTheory.Limits.
wideCoequalizer.π f) =     CategoryTheory.CategoryStruct.comp (f j₂) (CategoryTh
eory.Limits.wideCoequalizer.π f)
参数：f : J → (X ⟶ Y)；j₁ j₂ : J；f j₁；CategoryTheory.Limits.wideCoequalizer.π f；f j₂
；CategoryTheory.Limits.wideCoequalizer.π f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cotrident.condition`：∀ {J : Type w} {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} (j₁ j₂ : J)
   (t : CategoryTheory.Limits.C…
-/
theorem wideCoequalizer.condition (j₁ j₂ : J) :
    f j₁ ≫ wideCoequalizer.π f = f j₂ ≫ wideCoequalizer.π f :=
  Cotrident.condition j₁ j₂ <| colimit.cocone <| parallelFamily f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The cotrident built from `wideCoequalizer.π f` is colimiting. -/
/-
**CategoryTheory.Limits.wideCoequalizerIsWideCoequalizer** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.Limits`。
形式化陈述：wideCoequalizerIsWideCoequalizer [Nonempty J] : IsColimit (Cotrident.ofπ (
wideCoequalizer.π f) (wideCoequalizer.condition f))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.wideCoequalizer.condition`：∀ {J : Type w} {C : Typ
e u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} (f : J → (X ⟶ Y))   [in
st_1 : CategoryTheory.Limits.HasWideC…

--- 原说明 ---
The cotrident built from `wideCoequalizer.π f` is colimiting.
-/
def wideCoequalizerIsWideCoequalizer [Nonempty J] :
    IsColimit (Cotrident.ofπ (wideCoequalizer.π f) (wideCoequalizer.condition f)) :=
  IsColimit.ofIsoColimit (colimit.isColimit _) (Cotrident.ext (Iso.refl _))

variable {f}

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` factors through the
    wide coequalizer of `f` via `wideCoequalizer.desc : wideCoequalizer f ⟶ W`. -/
/-
**CategoryTheory.Limits.wideCoequalizer.desc** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Limits.wideCoequalizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [inst_1 : Category
Theory.Limits.HasWideCoequalizer f] →             [Nonempty J] →               {
W : C} →                 (k : Y ⟶ W) →                   (∀ (j₁ j₂ : J),        
               CategoryTheory.CategoryStruct.comp (f j₁) k = CategoryTheory.Cate
goryStruct.comp (f j₂) k) →                     (CategoryTheory.Limits.wideCoequ
alizer f ⟶ W)
参数：X ⟶ Y；k : Y ⟶ W；∀ (j₁ j₂ : J),                       CategoryTheory.CategoryS
truct.comp (f j₁) k = CategoryTheory.CategoryStruct.comp (f j₂) k；CategoryTheory
.Limits.wideCoequalizer f ⟶ W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` factors throu
gh the
    wide coequalizer of `f` via `wideCoequalizer.desc : wideCoequalizer f ⟶ W`.
-/
abbrev wideCoequalizer.desc [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer f ⟶ W :=
  colimit.desc (parallelFamily f) (Cotrident.ofπ k h)

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**CategoryTheory.Limits.wideCoequalizer.** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wideCoequalizer.π_desc [Nonempty J] {W : C} (k : Y ⟶ W)
    (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    wideCoequalizer.π f ≫ wideCoequalizer.desc k h = k := by
  simp

/-- Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a morphism
    `l : wideCoequalizer f ⟶ W` satisfying `wideCoequalizer.π ≫ g = l`. -/
/-
**CategoryTheory.Limits.wideCoequalizer.desc'** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits.wideCoequalizer`。
形式化陈述：{J : Type w} →   {C : Type u} →     [inst : CategoryTheory.Category.{v, u}
 C] →       {X Y : C} →         {f : J → (X ⟶ Y)} →           [inst_1 : Category
Theory.Limits.HasWideCoequalizer f] →             [Nonempty J] →               {
W : C} →                 (k : Y ⟶ W) →                   (∀ (j₁ j₂ : J),        
               CategoryTheory.CategoryStruct.comp (f j₁) k = CategoryTheory.Cate
goryStruct.comp (f j₂) k) →                     { l // CategoryTheory.CategorySt
ruct.comp (CategoryTheory.Limits.wideCoequalizer.π f) l = k }
参数：X ⟶ Y；k : Y ⟶ W；∀ (j₁ j₂ : J),                       CategoryTheory.CategoryS
truct.comp (f j₁) k = CategoryTheory.CategoryStruct.comp (f j₂) k；CategoryTheory
.Limits.wideCoequalizer.π f。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.wideCoequalizer.π_desc`：∀ {J : Type w} {C : Type u
} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)}   [inst_
1 : CategoryTheory.Limits.HasWideC…

--- 原说明 ---
Any morphism `k : Y ⟶ W` satisfying `∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k` induces a mor
phism
    `l : wideCoequalizer f ⟶ W` satisfying `wideCoequalizer.π ≫ g = l`.
-/
def wideCoequalizer.desc' [Nonempty J] {W : C} (k : Y ⟶ W) (h : ∀ j₁ j₂, f j₁ ≫ k = f j₂ ≫ k) :
    { l : wideCoequalizer f ⟶ W // wideCoequalizer.π f ≫ l = k } :=
  ⟨wideCoequalizer.desc k h, wideCoequalizer.π_desc _ _⟩

/-- Two maps from a wide coequalizer are equal if they are equal when composed with the wide
    coequalizer map -/
@[ext]
/-
**CategoryTheory.Limits.wideCoequalizer.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Limits.wideCoequalizer`。
形式化陈述：∀ {J : Type w} {C : Type u} [inst : CategoryTheory.Category.{v, u} C] {X Y
 : C} {f : J → (X ⟶ Y)}   [inst_1 : CategoryTheory.Limits.HasWideCoequalizer f] 
[Nonempty J] {W : C}   {k l : CategoryTheory.Limits.wideCoequalizer f ⟶ W},   Ca
tegoryTheory.CategoryStruct.comp (CategoryTheory.Limits.wideCoequalizer.π f) k =
       CategoryTheory.CategoryStruct.comp (CategoryTheory.Limits.wideCoequalizer
.π f) l →     k = l
参数：X ⟶ Y；CategoryTheory.Limits.wideCoequalizer.π f；CategoryTheory.Limits.wideCoe
qualizer.π f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cotrident.IsColimit.hom_ext`：∀ {J : Type w} {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [No
nempty J]   {s : CategoryTheory.Limits.…

--- 原说明 ---
Two maps from a wide coequalizer are equal if they are equal when composed with 
the wide
    coequalizer map
-/
theorem wideCoequalizer.hom_ext [Nonempty J] {W : C} {k l : wideCoequalizer f ⟶ W}
    (h : wideCoequalizer.π f ≫ k = wideCoequalizer.π f ≫ l) : k = l :=
  Cotrident.IsColimit.hom_ext (colimit.isColimit _) h

/-- A wide coequalizer morphism is an epimorphism -/
/-
**CategoryTheory.Limits.wideCoequalizer.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A wide coequalizer morphism is an epimorphism
-/
instance wideCoequalizer.π_epi [Nonempty J] : Epi (wideCoequalizer.π f) where
  left_cancellation _ _ w := wideCoequalizer.hom_ext w

end

section

variable {f}

/-- The wide coequalizer morphism in any colimit cocone is an epimorphism. -/
/-
**CategoryTheory.Limits.epi_of_isColimit_parallelFamily** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：epi_of_isColimit_parallelFamily [Nonempty J] {c : Cocone (parallelFamily f
)} (i : IsColimit c) : Epi (c.ι.app one) where left_cancellation _ _ w
参数：parallelFamily f；i : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Cotrident.IsColimit.hom_ext`：∀ {J : Type w} {C : T
ype u} [inst : CategoryTheory.Category.{v, u} C] {X Y : C} {f : J → (X ⟶ Y)} [No
nempty J]   {s : CategoryTheory.Limits.…

--- 原说明 ---
The wide coequalizer morphism in any colimit cocone is an epimorphism.
-/
theorem epi_of_isColimit_parallelFamily [Nonempty J] {c : Cocone (parallelFamily f)}
    (i : IsColimit c) : Epi (c.ι.app one) where
  left_cancellation _ _ w := Cotrident.IsColimit.hom_ext i w

end

variable (C)

/-- A category `HasWideEqualizers` if it has all limits of shape `WalkingParallelFamily J`, i.e.
if it has a wide equalizer for every family of parallel morphisms. -/
/-
**CategoryTheory.Limits.HasWideEqualizers** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryT
heory.Limits`。
形式化陈述：HasWideEqualizers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWideEqualizers` if it has all limits of shape `WalkingParallelFam
ily J`, i.e.
if it has a wide equalizer for every family of parallel morphisms.
-/
abbrev HasWideEqualizers :=
  ∀ J, HasLimitsOfShape (WalkingParallelFamily.{w} J) C

/-- A category `HasWideCoequalizers` if it has all colimits of shape `WalkingParallelFamily J`, i.e.
if it has a wide coequalizer for every family of parallel morphisms. -/
/-
**CategoryTheory.Limits.HasWideCoequalizers** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：HasWideCoequalizers
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A category `HasWideCoequalizers` if it has all colimits of shape `WalkingParalle
lFamily J`, i.e.
if it has a wide coequalizer for every family of parallel morphisms.
-/
abbrev HasWideCoequalizers :=
  ∀ J, HasColimitsOfShape (WalkingParallelFamily.{w} J) C

/-- If `C` has all limits of diagrams `parallelFamily f`, then it has all wide equalizers -/
/-
**CategoryTheory.Limits.hasWideEqualizers_of_hasLimit_parallelFamily** 是 Mathlib
 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasWideEqualizers_of_hasLimit_parallelFamily [forall {J : Type w} {X Y : C
} {f : J -> (X ⟶ Y)}, HasLimit (parallelFamily f)] : HasWideEqualizers.{w} C
参数：X ⟶ Y；parallelFamily f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasLimit_of_iso`：hasLimit_of_iso {F G : J ⥤ C} [Ha
sLimit F] (α : F ≅ G) : HasLimit G

--- 原说明 ---
If `C` has all limits of diagrams `parallelFamily f`, then it has all wide equal
izers
-/
theorem hasWideEqualizers_of_hasLimit_parallelFamily
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasLimit (parallelFamily f)] :
    HasWideEqualizers.{w} C := fun _ =>
  { has_limit := fun F => hasLimit_of_iso (diagramIsoParallelFamily F).symm }

/-- If `C` has all colimits of diagrams `parallelFamily f`, then it has all wide coequalizers -/
/-
**CategoryTheory.Limits.hasWideCoequalizers_of_hasColimit_parallelFamily** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Limits`。
形式化陈述：hasWideCoequalizers_of_hasColimit_parallelFamily [forall {J : Type w} {X Y
 : C} {f : J -> (X ⟶ Y)}, HasColimit (parallelFamily f)] : HasWideCoequalizers.{
w} C
参数：X ⟶ Y；parallelFamily f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasColimit_of_iso`：hasColimit_of_iso {F G : J ⥤ C}
 [HasColimit F] (α : G ≅ F) : HasColimit G

--- 原说明 ---
If `C` has all colimits of diagrams `parallelFamily f`, then it has all wide coe
qualizers
-/
theorem hasWideCoequalizers_of_hasColimit_parallelFamily
    [∀ {J : Type w} {X Y : C} {f : J → (X ⟶ Y)}, HasColimit (parallelFamily f)] :
    HasWideCoequalizers.{w} C := fun _ =>
  { has_colimit := fun F => hasColimit_of_iso (diagramIsoParallelFamily F) }
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) hasEqualizers_of_hasWideEqualizers [HasWideEqualizers.{w} C] :
    HasEqualizers C :=
  hasLimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair
/-
**CategoryTheory.Limits.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Limits`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) hasCoequalizers_of_hasWideCoequalizers [HasWideCoequalizers.{w} C] :
    HasCoequalizers C :=
  hasColimitsOfShape_of_equivalence.{w} walkingParallelFamilyEquivWalkingParallelPair

end CategoryTheory.Limits

