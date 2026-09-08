/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Functor.TwoSquare

/-!
# Guitart exact squares

Given four functors `T`, `L`, `R` and `B`, a 2-square `TwoSquare T L R B` consists of
a natural transformation `w : T ⋙ R ⟶ L ⋙ B`:
```
     T
  C₁ ⥤ C₂
L |     | R
  v     v
  C₃ ⥤ C₄
     B
```

In this file, we define a typeclass `w.GuitartExact` which expresses
that this square is exact in the sense of Guitart. This means that
for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final.
It is also equivalent to the fact that for any `X₂ : C₂`, the
induced functor `StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`
is initial.

Various categorical notions (fully faithful functors, adjunctions, etc.) can
be characterized in terms of Guitart exact squares. Their particular role
in pointwise Kan extensions shall also be used in the construction of
derived functors.

## TODO

* Define the notion of derivability structure from
  [the paper by Kahn and Maltsiniotis][KahnMaltsiniotis2008] using Guitart exact squares
  and construct (pointwise) derived functors using this notion

## References
* https://ncatlab.org/nlab/show/exact+square
* [René Guitart, *Relations et carrés exacts*][Guitart1980]
* [Bruno Kahn and Georges Maltsiniotis, *Structures de dérivabilité*][KahnMaltsiniotis2008]

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

open Category

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

namespace TwoSquare

variable {T L R B} (w : TwoSquare T L R B)

/-- Given `w : TwoSquare T L R B` and `X₃ : C₃`, this is the obvious functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)`. -/
@[simps! obj map]
/-
**CategoryTheory.TwoSquare.costructuredArrowRightwards** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.TwoSquare`。
形式化陈述：costructuredArrowRightwards (X₃ : C₃) : CostructuredArrow L X₃ ⥤ Costructu
redArrow R (B.obj X₃)
参数：X₃ : C₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and `X₃ : C₃`, this is the obvious functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)`.
-/
def costructuredArrowRightwards (X₃ : C₃) :
    CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃) :=
  CostructuredArrow.post L B X₃ ⋙ Comma.mapLeft _ w ⋙
    CostructuredArrow.pre T R (B.obj X₃)

/-- Given `w : TwoSquare T L R B` and `X₂ : C₂`, this is the obvious functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`. -/
@[simps! obj map]
/-
**CategoryTheory.TwoSquare.structuredArrowDownwards** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.TwoSquare`。
形式化陈述：structuredArrowDownwards (X₂ : C₂) : StructuredArrow X₂ T ⥤ StructuredArro
w (R.obj X₂) B
参数：X₂ : C₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and `X₂ : C₂`, this is the obvious functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B`.
-/
def structuredArrowDownwards (X₂ : C₂) :
    StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B :=
  StructuredArrow.post X₂ T R ⋙ Comma.mapRight _ w ⋙
    StructuredArrow.pre (R.obj X₂) L B

section

variable {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃)

/- In [the paper by Kahn and Maltsiniotis, §4.3][KahnMaltsiniotis2008], given
`w : TwoSquare T L R B` and `g : R.obj X₂ ⟶ B.obj X₃`, a category `J` is introduced
and it is observed that it is equivalent to the two categories
`w.StructuredArrowRightwards g` and `w.CostructuredArrowDownwards g`. We shall show below
that there is an equivalence
`w.equivalenceJ g : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is the
category `StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)`,
see the constructor `StructuredArrowRightwards.mk` for the data that is involved. -/
/-
**CategoryTheory.TwoSquare.StructuredArrowRightwards** 是 Mathlib 中的一个缩写定义，位于命名空间
 `CategoryTheory.TwoSquare`。
形式化陈述：StructuredArrowRightwards
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is 
the
category `StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightward
s X₃)`,
see the constructor `StructuredArrowRightwards.mk` for the data that is involved
.
-/
abbrev StructuredArrowRightwards :=
  StructuredArrow (CostructuredArrow.mk g) (w.costructuredArrowRightwards X₃)

/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is the
category `CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)`,
see the constructor `CostructuredArrowDownwards.mk` for the data that is involved. -/
/-
**CategoryTheory.TwoSquare.CostructuredArrowDownwards** 是 Mathlib 中的一个缩写定义，位于命名空
间 `CategoryTheory.TwoSquare`。
形式化陈述：CostructuredArrowDownwards
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is 
the
category `CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk 
g)`,
see the constructor `CostructuredArrowDownwards.mk` for the data that is involve
d.
-/
abbrev CostructuredArrowDownwards :=
  CostructuredArrow (w.structuredArrowDownwards X₂) (StructuredArrow.mk g)

section

variable (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)

/-- Constructor for objects in `w.StructuredArrowRightwards g`. -/
/-
**CategoryTheory.TwoSquare.StructuredArrowRightwards.mk** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.TwoSquare.StructuredArrowRightwards`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} →             
            (w : CategoryTheory.TwoSquare T L R B) →                           {
X₂ : C₂} →                             {X₃ : C₃} →                              
 (g : R.obj X₂ ⟶ B.obj X₃) →                                 (X₁ : C₁) →        
                           (a : X₂ ⟶ T.obj X₁) →                                
     (b : L.obj X₁ ⟶ X₃) →                                       CategoryTheory.
CategoryStruct.comp (R.map a)                                             (Categ
oryTheory.CategoryStruct.comp (w.app X₁) (B.map b)) =                           
                g →                                         w.StructuredArrowRig
htwards g
参数：w : CategoryTheory.TwoSquare T L R B；g : R.obj X₂ ⟶ B.obj X₃；X₁ : C₁；a : X₂ ⟶
 T.obj X₁；b : L.obj X₁ ⟶ X₃；R.map a；CategoryTheory.CategoryStruct.comp (w.app X₁
) (B.map b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in `w.StructuredArrowRightwards g`.
-/
abbrev StructuredArrowRightwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.StructuredArrowRightwards g :=
  StructuredArrow.mk (Y := CostructuredArrow.mk b) (CostructuredArrow.homMk a comm)

set_option backward.isDefEq.respectTransparency.types false in
/-- Constructor for objects in `w.CostructuredArrowDownwards g`. -/
/-
**CategoryTheory.TwoSquare.CostructuredArrowDownwards.mk** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.TwoSquare.CostructuredArrowDownwards`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} →             
            (w : CategoryTheory.TwoSquare T L R B) →                           {
X₂ : C₂} →                             {X₃ : C₃} →                              
 (g : R.obj X₂ ⟶ B.obj X₃) →                                 (X₁ : C₁) →        
                           (a : X₂ ⟶ T.obj X₁) →                                
     (b : L.obj X₁ ⟶ X₃) →                                       CategoryTheory.
CategoryStruct.comp (R.map a)                                             (Categ
oryTheory.CategoryStruct.comp (w.app X₁) (B.map b)) =                           
                g →                                         w.CostructuredArrowD
ownwards g
参数：w : CategoryTheory.TwoSquare T L R B；g : R.obj X₂ ⟶ B.obj X₃；X₁ : C₁；a : X₂ ⟶
 T.obj X₁；b : L.obj X₁ ⟶ X₃；R.map a；CategoryTheory.CategoryStruct.comp (w.app X₁
) (B.map b)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for objects in `w.CostructuredArrowDownwards g`.
-/
abbrev CostructuredArrowDownwards.mk (comm : R.map a ≫ w.app X₁ ≫ B.map b = g) :
    w.CostructuredArrowDownwards g :=
  CostructuredArrow.mk (Y := StructuredArrow.mk a)
    (StructuredArrow.homMk b (by simpa using comm))

variable {w g}

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.StructuredArrowRightwards.mk_surjective** 是 Mathlib 中
的一个定理，位于命名空间 `CategoryTheory.TwoSquare.StructuredArrowRightwards`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
] [inst_2 : CategoryTheory.Category.{v₃, u₃} C₃]   [inst_3 : CategoryTheory.Cate
gory.{v₄, u₄} C₄] {T : CategoryTheory.Functor C₁ C₂} {L : CategoryTheory.Functor
 C₁ C₃}   {R : CategoryTheory.Functor C₂ C₄} {B : CategoryTheory.Functor C₃ C₄} 
{w : CategoryTheory.TwoSquare T L R B} {X₂ : C₂}   {X₃ : C₃} {g : R.obj X₂ ⟶ B.o
bj X₃} (f : w.StructuredArrowRightwards g),   ∃ X₁ a b,     ∃ (comm :       Cate
goryTheory.CategoryStruct.comp (R.map a) (CategoryTheory.CategoryStruct.comp (w.
app X₁) (B.map b)) = g),       f = CategoryTheory.TwoSquare.StructuredArrowRight
wards.mk w g X₁ a b comm
参数：f : w.StructuredArrowRightwards g；comm :       CategoryTheory.CategoryStruct.
comp (R.map a) (CategoryTheory.CategoryStruct.comp (w.app X₁) (B.map b)) = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.StructuredArrow.mk_surjective`：mk_surjective (f : Structu
redArrow S T) : exists (Y : C) (g : S ⟶ T.obj Y), f = mk g
· 使用引理 `CategoryTheory.CostructuredArrow.mk_surjective`：mk_surjective (f : Costr
ucturedArrow S T) : exists (Y : C) (g : S.obj Y ⟶ T), f = mk g
· 使用定理 `CategoryTheory.CostructuredArrow.homMk_surjective`：homMk_surjective {f f
' : CostructuredArrow S T} (φ : f ⟶ f') : exists (ψ : f.left ⟶ f'.left) (hψ : S.
map ψ ≫ f'.hom = f.hom), φ = Costructur…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma StructuredArrowRightwards.mk_surjective
    (f : w.StructuredArrowRightwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := StructuredArrow.mk_surjective f
  obtain ⟨X₁, b, rfl⟩ := g.mk_surjective
  obtain ⟨a, ha, rfl⟩ := CostructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using ha, rfl⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.CostructuredArrowDownwards.mk_surjective** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.TwoSquare.CostructuredArrowDownwards`。
形式化陈述：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} [inst : Cate
goryTheory.Category.{v₁, u₁} C₁]   [inst_1 : CategoryTheory.Category.{v₂, u₂} C₂
] [inst_2 : CategoryTheory.Category.{v₃, u₃} C₃]   [inst_3 : CategoryTheory.Cate
gory.{v₄, u₄} C₄] {T : CategoryTheory.Functor C₁ C₂} {L : CategoryTheory.Functor
 C₁ C₃}   {R : CategoryTheory.Functor C₂ C₄} {B : CategoryTheory.Functor C₃ C₄} 
{w : CategoryTheory.TwoSquare T L R B} {X₂ : C₂}   {X₃ : C₃} {g : R.obj X₂ ⟶ B.o
bj X₃} (f : w.CostructuredArrowDownwards g),   ∃ X₁ a b,     ∃ (comm :       Cat
egoryTheory.CategoryStruct.comp (R.map a) (CategoryTheory.CategoryStruct.comp (w
.app X₁) (B.map b)) = g),       f = CategoryTheory.TwoSquare.CostructuredArrowDo
wnwards.mk w g X₁ a b comm
参数：f : w.CostructuredArrowDownwards g；comm :       CategoryTheory.CategoryStruct
.comp (R.map a) (CategoryTheory.CategoryStruct.comp (w.app X₁) (B.map b)) = g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.CostructuredArrow.mk_surjective`：mk_surjective (f : Costr
ucturedArrow S T) : exists (Y : C) (g : S.obj Y ⟶ T), f = mk g
· 使用引理 `CategoryTheory.StructuredArrow.mk_surjective`：mk_surjective (f : Structu
redArrow S T) : exists (Y : C) (g : S ⟶ T.obj Y), f = mk g
· 使用定理 `CategoryTheory.StructuredArrow.homMk_surjective`：homMk_surjective {f f' 
: StructuredArrow S T} (φ : f ⟶ f') : exists (ψ : f.right ⟶ f'.right) (hψ : f.ho
m ≫ T.map ψ = f'.hom), φ = Structured…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma CostructuredArrowDownwards.mk_surjective
    (f : w.CostructuredArrowDownwards g) :
    ∃ (X₁ : C₁) (a : X₂ ⟶ T.obj X₁) (b : L.obj X₁ ⟶ X₃)
      (comm : R.map a ≫ w.app X₁ ≫ B.map b = g), f = mk w g X₁ a b comm := by
  obtain ⟨g, φ, rfl⟩ := CostructuredArrow.mk_surjective f
  obtain ⟨X₁, a, rfl⟩ := g.mk_surjective
  obtain ⟨b, hb, rfl⟩ := StructuredArrow.homMk_surjective φ
  exact ⟨X₁, a, b, by simpa using hb, rfl⟩

end

namespace EquivalenceJ

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g`. -/
@[simps]
/-
**CategoryTheory.TwoSquare.EquivalenceJ.functor** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.TwoSquare.EquivalenceJ`。
形式化陈述：functor : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g w
here obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownward
s g`.
-/
def functor : w.StructuredArrowRightwards g ⥤ w.CostructuredArrowDownwards g where
  obj f := CostructuredArrow.mk (Y := StructuredArrow.mk f.hom.left)
      (StructuredArrow.homMk f.right.hom (by simpa using CostructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    CostructuredArrow.homMk (StructuredArrow.homMk φ.right.left
      (by dsimp; rw [← StructuredArrow.w φ]; rfl))
      (by ext; exact CostructuredArrow.w φ.right)
  map_id _ := rfl
  map_comp _ _ := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g`. -/
@[simps]
/-
**CategoryTheory.TwoSquare.EquivalenceJ.inverse** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.TwoSquare.EquivalenceJ`。
形式化陈述：inverse : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g w
here obj f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious functor `w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightward
s g`.
-/
def inverse : w.CostructuredArrowDownwards g ⥤ w.StructuredArrowRightwards g where
  obj f := StructuredArrow.mk (Y := CostructuredArrow.mk f.hom.right)
      (CostructuredArrow.homMk f.left.hom (by simpa using StructuredArrow.w f.hom))
  map {f₁ f₂} φ :=
    StructuredArrow.homMk (CostructuredArrow.homMk φ.left.right
      (by dsimp; rw [← CostructuredArrow.w φ]; rfl))
      (by ext; exact StructuredArrow.w φ.left)
  map_id _ := rfl
  map_comp _ _ := rfl

end EquivalenceJ

set_option backward.isDefEq.respectTransparency.types false in
/-- Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious equivalence of categories
`w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`. -/
@[simps functor inverse unitIso counitIso]
/-
**CategoryTheory.TwoSquare.equivalenceJ** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.TwoSquare`。
形式化陈述：equivalenceJ : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownward
s g where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `w : TwoSquare T L R B` and a morphism `g : R.obj X₂ ⟶ B.obj X₃`, this is
the obvious equivalence of categories
`w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g`.
-/
def equivalenceJ : w.StructuredArrowRightwards g ≌ w.CostructuredArrowDownwards g where
  functor := EquivalenceJ.functor w g
  inverse := EquivalenceJ.inverse w g
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**CategoryTheory.TwoSquare.isConnected_rightwards_iff_downwards** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：isConnected_rightwards_iff_downwards : IsConnected (w.StructuredArrowRight
wards g) ↔ IsConnected (w.CostructuredArrowDownwards g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.isConnected_iff_of_equivalence`：isConnected_iff_of_equiva
lence {K : Type u₂} [Category.{v₂} K] (e : J ≌ K) : IsConnected J ↔ IsConnected 
K
-/
lemma isConnected_rightwards_iff_downwards :
    IsConnected (w.StructuredArrowRightwards g) ↔ IsConnected (w.CostructuredArrowDownwards g) :=
  isConnected_iff_of_equivalence (w.equivalenceJ g)

end

section

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor `w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g'` induced
by a morphism `γ` such that `R.map γ ≫ g = g'`. -/
@[simps]
/-
**CategoryTheory.TwoSquare.costructuredArrowDownwardsPrecomp** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：costructuredArrowDownwardsPrecomp {X₂ X₂' : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ 
B.obj X₃) (g' : R.obj X₂' ⟶ B.obj X₃) (γ : X₂' ⟶ X₂) (hγ : R.map γ ≫ g = g') : w
.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g' where obj A
参数：g : R.obj X₂ ⟶ B.obj X₃；g' : R.obj X₂' ⟶ B.obj X₃；γ : X₂' ⟶ X₂；hγ : R.map γ ≫
 g = g'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g'` i
nduced
by a morphism `γ` such that `R.map γ ≫ g = g'`.
-/
def costructuredArrowDownwardsPrecomp
    {X₂ X₂' : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) (g' : R.obj X₂' ⟶ B.obj X₃)
    (γ : X₂' ⟶ X₂) (hγ : R.map γ ≫ g = g') :
    w.CostructuredArrowDownwards g ⥤ w.CostructuredArrowDownwards g' where
  obj A := CostructuredArrowDownwards.mk _ _ A.left.right (γ ≫ A.left.hom) A.hom.right
    (by simpa [← hγ] using R.map γ ≫= StructuredArrow.w A.hom)
  map {A A'} φ := CostructuredArrow.homMk (StructuredArrow.homMk φ.left.right (by
      dsimp
      rw [assoc, StructuredArrow.w])) (by
    ext
    dsimp
    rw [← CostructuredArrow.w φ, structuredArrowDownwards_map]
    rfl)
  map_id _ := rfl
  map_comp _ _ := rfl

end

/-- Condition on `w : TwoSquare T L R B` expressing that it is a Guitart exact square.
It is equivalent to saying that for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final (see `guitartExact_iff_final`)
or equivalently that for any `X₂ : C₂`, the induced functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B` is initial (see `guitartExact_iff_initial`).
See also  `guitartExact_iff_isConnected_rightwards`, `guitartExact_iff_isConnected_downwards`
for characterizations in terms of the connectedness of auxiliary categories. -/
/-
**CategoryTheory.TwoSquare.GuitartExact** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryThe
ory.TwoSquare`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} → CategoryTheo
ry.TwoSquare T L R B → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Condition on `w : TwoSquare T L R B` expressing that it is a Guitart exact squar
e.
It is equivalent to saying that for any `X₃ : C₃`, the induced functor
`CostructuredArrow L X₃ ⥤ CostructuredArrow R (B.obj X₃)` is final (see `guitart
Exact_iff_final`)
or equivalently that for any `X₂ : C₂`, the induced functor
`StructuredArrow X₂ T ⥤ StructuredArrow (R.obj X₂) B` is initial (see `guitartEx
act_iff_initial`).
See also  `guitartExact_iff_isConnected_rightwards`, `guitartExact_iff_isConnect
ed_downwards`
for characterizations in terms of the connectedness of auxiliary categories.
-/
class GuitartExact : Prop where
  isConnected_rightwards {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃) :
    IsConnected (w.StructuredArrowRightwards g)
/-
**CategoryTheory.TwoSquare.guitartExact_iff_isConnected_rightwards** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：guitartExact_iff_isConnected_rightwards : w.GuitartExact ↔ forall {X₂ : C₂
} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.StructuredArrowRightwards 
g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.TwoSquare.GuitartExact.isConnected_rightwards`：∀ {C₁ : Ty
pe u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {inst : CategoryTheory.Categ
ory.{v₁, u₁} C₁}   {inst_1 : CategoryTheory.Catego…
-/
lemma guitartExact_iff_isConnected_rightwards :
    w.GuitartExact ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.StructuredArrowRightwards g) :=
  ⟨fun h => h.isConnected_rightwards, fun h => ⟨h⟩⟩
/-
**CategoryTheory.TwoSquare.guitartExact_iff_isConnected_downwards** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：guitartExact_iff_isConnected_downwards : w.GuitartExact ↔ forall {X₂ : C₂}
 {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.CostructuredArrowDownwards 
g)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma guitartExact_iff_isConnected_downwards :
    w.GuitartExact ↔ ∀ {X₂ : C₂} {X₃ : C₃} (g : R.obj X₂ ⟶ B.obj X₃),
      IsConnected (w.CostructuredArrowDownwards g) := by
  simp only [guitartExact_iff_isConnected_rightwards,
    isConnected_rightwards_iff_downwards]
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hw : w.GuitartExact] {X₃ : C₃} (g : CostructuredArrow R (B.obj X₃)) :
    IsConnected (StructuredArrow g (w.costructuredArrowRightwards X₃)) := by
  rw [guitartExact_iff_isConnected_rightwards] at hw
  apply hw
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hw : w.GuitartExact] {X₂ : C₂} (g : StructuredArrow (R.obj X₂) B) :
    IsConnected (CostructuredArrow (w.structuredArrowDownwards X₂) g) := by
  rw [guitartExact_iff_isConnected_downwards] at hw
  apply hw

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.costructuredArrowRightwards_final_iff_of_iso** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：costructuredArrowRightwards_final_iff_of_iso {X₃ X₃' : C₃} (e : X₃ ≅ X₃') 
: (w.costructuredArrowRightwards X₃).Final ↔ (w.costructuredArrowRightwards X₃')
.Final
参数：e : X₃ ≅ X₃'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.final_iff_comp_equivalence`：final_iff_comp_equiva
lence [IsEquivalence G] : Final F ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.final_iff_equivalence_comp`：final_iff_equivalence
_comp [IsEquivalence F] : Final G ↔ Final (F ⋙ G)
· 使用定理 `CategoryTheory.Functor.final_natIso_iff`：final_natIso_iff {F F' : C ⥤ D}
 (i : F ≅ F') : Final F ↔ Final F'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma costructuredArrowRightwards_final_iff_of_iso {X₃ X₃' : C₃} (e : X₃ ≅ X₃') :
    (w.costructuredArrowRightwards X₃).Final ↔
      (w.costructuredArrowRightwards X₃').Final := by
  rw [Functor.final_iff_comp_equivalence _ (CostructuredArrow.mapIso (B.mapIso e)).functor,
    Functor.final_iff_equivalence_comp (CostructuredArrow.mapIso e).functor]
  exact Functor.final_natIso_iff
    (NatIso.ofComponents (fun _ ↦ CostructuredArrow.isoMk (Iso.refl _)))
/-
**CategoryTheory.TwoSquare.guitartExact_iff_final** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.TwoSquare`。
形式化陈述：guitartExact_iff_final : w.GuitartExact ↔ forall (X₃ : C₃), (w.costructure
dArrowRightwards X₃).Final
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.TwoSquare.instIsConnectedStructuredArrowCostructuredArrow
ObjCostructuredArrowRightwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C
₃ : Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst
_1 : CategoryTheory.Catego…
· 使用定理 `CategoryTheory.Functor.Final.out`：∀ {C : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D
}   {F : CategoryTheor…
-/
lemma guitartExact_iff_final :
    w.GuitartExact ↔ ∀ (X₃ : C₃), (w.costructuredArrowRightwards X₃).Final :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, fun _ => ⟨fun _ => inferInstance⟩⟩
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hw : w.GuitartExact] (X₃ : C₃) :
    (w.costructuredArrowRightwards X₃).Final := by
  rw [guitartExact_iff_final] at hw
  apply hw

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.TwoSquare.structuredArrowDownwards_initial_iff_of_iso** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.TwoSquare`。
形式化陈述：structuredArrowDownwards_initial_iff_of_iso {X₂ X₂' : C₂} (e : X₂ ≅ X₂') :
 (w.structuredArrowDownwards X₂).Initial ↔ (w.structuredArrowDownwards X₂').Init
ial
参数：e : X₂ ≅ X₂'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.initial_iff_comp_equivalence`：initial_iff_comp_eq
uivalence [IsEquivalence G] : Initial F ↔ Initial (F ⋙ G)
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
· 使用定理 `CategoryTheory.Functor.initial_iff_equivalence_comp`：initial_iff_equival
ence_comp [IsEquivalence F] : Initial G ↔ Initial (F ⋙ G)
· 使用定理 `CategoryTheory.Functor.initial_natIso_iff`：initial_natIso_iff {F F' : C 
⥤ D} (i : F ≅ F') : Initial F ↔ Initial F'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma structuredArrowDownwards_initial_iff_of_iso {X₂ X₂' : C₂} (e : X₂ ≅ X₂') :
    (w.structuredArrowDownwards X₂).Initial ↔
      (w.structuredArrowDownwards X₂').Initial := by
  rw [Functor.initial_iff_comp_equivalence _ (StructuredArrow.mapIso (R.mapIso e)).functor,
    Functor.initial_iff_equivalence_comp (StructuredArrow.mapIso e).functor]
  exact Functor.initial_natIso_iff
    (NatIso.ofComponents (fun _ ↦ StructuredArrow.isoMk (Iso.refl _)))
/-
**CategoryTheory.TwoSquare.guitartExact_iff_initial** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.TwoSquare`。
形式化陈述：guitartExact_iff_initial : w.GuitartExact ↔ forall (X₂ : C₂), (w.structure
dArrowDownwards X₂).Initial
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.TwoSquare.instIsConnectedCostructuredArrowStructuredArrow
ObjStructuredArrowDownwardsOfGuitartExact`：∀ {C₁ : Type u₁} {C₂ : Type u₂} {C₃ :
 Type u₃} {C₄ : Type u₄} [inst : CategoryTheory.Category.{v₁, u₁} C₁]   [inst_1 
: CategoryTheory.Catego…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_isConnected_downwards`：guitart
Exact_iff_isConnected_downwards : w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} (g
 : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.CostructuredA…
· 使用定理 `CategoryTheory.Functor.Initial.out`：∀ {C : Type u₁} {inst : CategoryTheo
ry.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂}
 D}   {F : CategoryTheor…
-/
lemma guitartExact_iff_initial :
    w.GuitartExact ↔ ∀ (X₂ : C₂), (w.structuredArrowDownwards X₂).Initial :=
  ⟨fun _ _ => ⟨fun _ => inferInstance⟩, by
    rw [guitartExact_iff_isConnected_downwards]
    intros
    infer_instance⟩
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [hw : w.GuitartExact] (X₂ : C₂) :
    (w.structuredArrowDownwards X₂).Initial := by
  rw [guitartExact_iff_initial] at hw
  apply hw

set_option backward.isDefEq.respectTransparency false in
/-- When the left and right functors of a 2-square are equivalences, and the natural
transformation of the 2-square is an isomorphism, then the 2-square is Guitart exact. -/
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When the left and right functors of a 2-square are equivalences, and the natural
transformation of the 2-square is an isomorphism, then the 2-square is Guitart e
xact.
-/
instance (priority := 100) guitartExact_of_isEquivalence_of_isIso
    [L.IsEquivalence] [R.IsEquivalence] [IsIso w.natTrans] : GuitartExact w := by
  rw [guitartExact_iff_initial]
  intro X₂
  have := StructuredArrow.isEquivalence_post X₂ T R
  have : (Comma.mapRight _ w : StructuredArrow (R.obj X₂) _ ⥤ _).IsEquivalence :=
    (Comma.mapRightIso _ (asIso w)).isEquivalence_functor
  have := StructuredArrow.isEquivalence_pre (R.obj X₂) L B
  dsimp only [structuredArrowDownwards]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.TwoSquare.guitartExact_id** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTh
eory.TwoSquare`。
形式化陈述：guitartExact_id (F : C₁ ⥤ C₂) : GuitartExact (TwoSquare.mk (𝟭 C₁) F F (𝟭 C
₂) (𝟙 F))
参数：F : C₁ ⥤ C₂。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.TwoSquare.guitartExact_iff_isConnected_rightwards`：guitar
tExact_iff_isConnected_rightwards : w.GuitartExact ↔ forall {X₂ : C₂} {X₃ : C₃} 
(g : R.obj X₂ ⟶ B.obj X₃), IsConnected (w.StructuredAr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.CostructuredArrow.w`：w (f : X ⟶ Y) : S.map f.left ≫ Y.hom
 = X.hom
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `CategoryTheory.Zigzag.of_inv_hom`：∀ {J : Type u₁} [inst : CategoryTheory
.Category.{v₁, u₁} J] {j₁ j₂ j₃ : J} (f₂₁ : j₂ ⟶ j₁) (f₂₃ : j₂ ⟶ j₃),   Category
Theory.Zigzag j₁ j₃
-/
instance guitartExact_id (F : C₁ ⥤ C₂) :
    GuitartExact (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) := by
  rw [guitartExact_iff_isConnected_rightwards]
  intro X₂ X₃ (g : F.obj X₂ ⟶ X₃)
  let Z := StructuredArrowRightwards (TwoSquare.mk (𝟭 C₁) F F (𝟭 C₂) (𝟙 F)) g
  let X₀ : Z := StructuredArrow.mk (Y := CostructuredArrow.mk g) (CostructuredArrow.homMk (𝟙 _))
  have φ : ∀ (X : Z), X₀ ⟶ X := fun X =>
    StructuredArrow.homMk (CostructuredArrow.homMk X.hom.left
      (by simpa using! CostructuredArrow.w X.hom))
  have : Nonempty Z := ⟨X₀⟩
  apply zigzag_isConnected
  intro X Y
  exact Zigzag.of_inv_hom (φ X) (φ Y)

end TwoSquare

end CategoryTheory

