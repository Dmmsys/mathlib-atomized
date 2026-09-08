/-
Copyright (c) 2025 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jakob von Raumer
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.Tactic.CategoryTheory.Slice

/-!
# 2-squares of functors

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

We define operations to paste such squares horizontally and vertically and prove the interchange
law of those two operations.

## TODO

Generalize all of this to double categories.

-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ v₉ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈ u₉

namespace CategoryTheory

open Category CategoryTheory.Functor

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  (T : C₁ ⥤ C₂) (L : C₁ ⥤ C₃) (R : C₂ ⥤ C₄) (B : C₃ ⥤ C₄)

/-- A `2`-square consists of a natural transformation `T ⋙ R ⟶ L ⋙ B`
involving fours functors `T`, `L`, `R`, `B` that are on the
top/left/right/bottom sides of a square of categories. -/
/-
**CategoryTheory.TwoSquare** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：TwoSquare
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `2`-square consists of a natural transformation `T ⋙ R ⟶ L ⋙ B`
involving fours functors `T`, `L`, `R`, `B` that are on the
top/left/right/bottom sides of a square of categories.
-/
def TwoSquare := T ⋙ R ⟶ L ⋙ B

namespace TwoSquare

/-- Constructor for `TwoSquare`. -/
/-
**CategoryTheory.TwoSquare.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.TwoSqu
are`。
形式化陈述：mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B
参数：α : T ⋙ R ⟶ L ⋙ B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `TwoSquare`.
-/
abbrev mk (α : T ⋙ R ⟶ L ⋙ B) : TwoSquare T L R B := α

variable {T} {L} {R} {B} in
/-- The natural transformation associated to a 2-square. -/
/-
**CategoryTheory.TwoSquare.natTrans** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.
TwoSquare`。
形式化陈述：natTrans (w : TwoSquare T L R B) : T ⋙ R ⟶ L ⋙ B
参数：w : TwoSquare T L R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation associated to a 2-square.
-/
abbrev natTrans (w : TwoSquare T L R B) : T ⋙ R ⟶ L ⋙ B := w

/-- The type of 2-squares on functors `T`, `L`, `R`, and `B` is trivially equivalent to
the type of natural transformations `T ⋙ R ⟶ L ⋙ B`. -/
@[simps]
/-
**CategoryTheory.TwoSquare.equivNatTrans** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.TwoSquare`。
形式化陈述：equivNatTrans : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of 2-squares on functors `T`, `L`, `R`, and `B` is trivially equivalent
 to
the type of natural transformations `T ⋙ R ⟶ L ⋙ B`.
-/
def equivNatTrans : TwoSquare T L R B ≃ (T ⋙ R ⟶ L ⋙ B) where
  toFun := natTrans
  invFun := mk T L R B

variable {T L R B}

/-- The opposite of a `2`-square. -/
/-
**CategoryTheory.TwoSquare.op** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSquar
e`。
形式化陈述：op (α : TwoSquare T L R B) : TwoSquare L.op T.op B.op R.op
参数：α : TwoSquare T L R B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The opposite of a `2`-square.
-/
def op (α : TwoSquare T L R B) : TwoSquare L.op T.op B.op R.op := NatTrans.op α

@[simp]
/-
**CategoryTheory.TwoSquare.natTrans_op** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.TwoSquare`。
形式化陈述：natTrans_op (α : TwoSquare T L R B) : α.op.natTrans = NatTrans.op α.natTra
ns
参数：α : TwoSquare T L R B。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTrans_op (α : TwoSquare T L R B) :
    α.op.natTrans = NatTrans.op α.natTrans := rfl
/-
**CategoryTheory.TwoSquare.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.TwoSquare`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α : TwoSquare T L R B) [IsIso α.natTrans] : IsIso α.op.natTrans :=
  inferInstanceAs (IsIso (NatTrans.op α.natTrans))

@[ext]
/-
**CategoryTheory.TwoSquare.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.TwoSqua
re`。
形式化陈述：ext (w w' : TwoSquare T L R B) (h : forall (X : C₁), w.natTrans.app X = w'
.natTrans.app X) : w = w'
参数：w w' : TwoSquare T L R B；h : forall (X : C₁), w.natTrans.app X = w'.natTrans.
app X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma ext (w w' : TwoSquare T L R B) (h : ∀ (X : C₁), w.natTrans.app X = w'.natTrans.app X) :
    w = w' :=
  NatTrans.ext (funext h)

/-- The horizontal identity 2-square. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.hId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSqua
re`。
形式化陈述：hId (L : C₁ ⥤ C₃) : TwoSquare (𝟭 _) L L (𝟭 _)
参数：L : C₁ ⥤ C₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal identity 2-square.
-/
def hId (L : C₁ ⥤ C₃) : TwoSquare (𝟭 _) L L (𝟭 _) :=
  (Functor.leftUnitor L).hom ≫ (Functor.rightUnitor L).inv

/-- Notation for the horizontal identity 2-square. -/
scoped notation "𝟙ₕ" => hId  -- type as \b1\_h

/-- The vertical identity 2-square. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.vId** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSqua
re`。
形式化陈述：vId (T : C₁ ⥤ C₂) : TwoSquare T (𝟭 _) (𝟭 _) T
参数：T : C₁ ⥤ C₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical identity 2-square.
-/
def vId (T : C₁ ⥤ C₂) : TwoSquare T (𝟭 _) (𝟭 _) T :=
  (Functor.rightUnitor T).hom ≫ (Functor.leftUnitor T).inv

/-- Notation for the vertical identity 2-square. -/
scoped notation "𝟙ᵥ" => vId  -- type as \b1\_v

/-- Whiskering a 2-square with a natural transformation at the top. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerTop** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
TwoSquare`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} →             
            {T' : CategoryTheory.Functor C₁ C₂} →                           Cate
goryTheory.TwoSquare T' L R B → (T ⟶ T') → CategoryTheory.TwoSquare T L R B
参数：T ⟶ T'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 2-square with a natural transformation at the top.
-/
protected def whiskerTop {T' : C₁ ⥤ C₂} (w : TwoSquare T' L R B) (α : T ⟶ T') : TwoSquare T L R B :=
  .mk _ _ _ _ <| whiskerRight α R ≫ w.natTrans

/-- Whiskering a 2-square with a natural transformation at the left side. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.TwoSquare`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} →             
            {L' : CategoryTheory.Functor C₁ C₃} →                           Cate
goryTheory.TwoSquare T L R B → (L ⟶ L') → CategoryTheory.TwoSquare T L' R B
参数：L ⟶ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 2-square with a natural transformation at the left side.
-/
protected def whiskerLeft {L' : C₁ ⥤ C₃} (w : TwoSquare T L R B) (α : L ⟶ L') :
    TwoSquare T L' R B :=
  .mk _ _ _ _ <| w.natTrans ≫ whiskerRight α B

/-- Whiskering a 2-square with a natural transformation at the right side. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.TwoSquare`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B : CategoryTheory.Functor C₃ C₄} →             
            {R' : CategoryTheory.Functor C₂ C₄} →                           Cate
goryTheory.TwoSquare T L R' B → (R ⟶ R') → CategoryTheory.TwoSquare T L R B
参数：R ⟶ R'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 2-square with a natural transformation at the right side.
-/
protected def whiskerRight {R' : C₂ ⥤ C₄} (w : TwoSquare T L R' B) (α : R ⟶ R') :
    TwoSquare T L R B :=
  .mk _ _ _ _ <| whiskerLeft T α ≫ w.natTrans

/-- Whiskering a 2-square with a natural transformation at the bottom. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.whiskerBottom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.TwoSquare`。
形式化陈述：{C₁ : Type u₁} →   {C₂ : Type u₂} →     {C₃ : Type u₃} →       {C₄ : Type 
u₄} →         [inst : CategoryTheory.Category.{v₁, u₁} C₁] →           [inst_1 :
 CategoryTheory.Category.{v₂, u₂} C₂] →             [inst_2 : CategoryTheory.Cat
egory.{v₃, u₃} C₃] →               [inst_3 : CategoryTheory.Category.{v₄, u₄} C₄
] →                 {T : CategoryTheory.Functor C₁ C₂} →                   {L : 
CategoryTheory.Functor C₁ C₃} →                     {R : CategoryTheory.Functor 
C₂ C₄} →                       {B B' : CategoryTheory.Functor C₃ C₄} →          
               CategoryTheory.TwoSquare T L R B → (B ⟶ B') → CategoryTheory.TwoS
quare T L R B'
参数：B ⟶ B'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Whiskering a 2-square with a natural transformation at the bottom.
-/
protected def whiskerBottom {B' : C₃ ⥤ C₄} (w : TwoSquare T L R B) (α : B ⟶ B') :
    TwoSquare T L R B' :=
  .mk _ _ _ _ <| w.natTrans ≫ whiskerLeft L α

variable {C₅ : Type u₅} {C₆ : Type u₆} {C₇ : Type u₇} {C₈ : Type u₈}
  [Category.{v₅} C₅] [Category.{v₆} C₆] [Category.{v₇} C₇] [Category.{v₈} C₈]
  {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆} {L' : C₃ ⥤ C₇} {R'' : C₄ ⥤ C₈} {B'' : C₇ ⥤ C₈}

/-- The horizontal composition of 2-squares. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.hComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSq
uare`。
形式化陈述：hComp (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') : TwoSquare (T ⋙
 T') L R' (B ⋙ B')
参数：w : TwoSquare T L R B；w' : TwoSquare T' R R' B'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The horizontal composition of 2-squares.
-/
def hComp (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') :
    TwoSquare (T ⋙ T') L R' (B ⋙ B') :=
  .mk _ _ _ _ <| (associator _ _ _).hom ≫ (whiskerLeft T w'.natTrans) ≫
    (associator _ _ _).inv ≫ (whiskerRight w.natTrans B') ≫ (associator _ _ _).hom

/-- Notation for the horizontal composition of 2-squares. -/
scoped infixr:80 " ≫ₕ " => hComp -- type as \gg\_h

/-- The vertical composition of 2-squares. -/
@[simps!]
/-
**CategoryTheory.TwoSquare.vComp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.TwoSq
uare`。
形式化陈述：vComp (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') : TwoSquare T 
(L ⋙ L') (R ⋙ R'') B''
参数：w : TwoSquare T L R B；w' : TwoSquare B L' R'' B''。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The vertical composition of 2-squares.
-/
def vComp (w : TwoSquare T L R B) (w' : TwoSquare B L' R'' B'') :
    TwoSquare T (L ⋙ L') (R ⋙ R'') B'' :=
  .mk _ _ _ _ <| (associator _ _ _).inv ≫ whiskerRight w.natTrans R'' ≫
    (associator _ _ _).hom ≫ whiskerLeft L w'.natTrans ≫ (associator _ _ _).inv

/-- Notation for the vertical composition of 2-squares. -/
scoped infixr:80 " ≫ᵥ " => vComp -- type as \gg\_v

section Interchange

variable {C₉ : Type u₉} [Category.{v₉} C₉] {R₃ : C₆ ⥤ C₉} {B₃ : C₈ ⥤ C₉}

set_option backward.defeqAttrib.useBackward true in
/-- When composing 2-squares which form a diagram of grid, composing horizontally first yields the
same result as composing vertically first. -/
/-
**CategoryTheory.TwoSquare.hCompVCompHComp** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.TwoSquare`。
形式化陈述：hCompVCompHComp (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B') (w₃ :
 TwoSquare B L' R'' B'') (w₄ : TwoSquare B' R'' R₃ B₃) : (w₁ ≫ₕ w₂) ≫ᵥ (w₃ ≫ₕ w₄
) = (w₁ ≫ᵥ w₃) ≫ₕ (w₂ ≫ᵥ w₄)
参数：w₁ : TwoSquare T L R B；w₂ : TwoSquare T' R R' B'；w₃ : TwoSquare B L' R'' B''；
w₄ : TwoSquare B' R'' R₃ B₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.TwoSquare.ext`：ext (w w' : TwoSquare T L R B) (h : forall
 (X : C₁), w.natTrans.app X = w'.natTrans.app X) : w = w'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.NatTrans.mk.congr_simp`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, 
u₂} D]   {F G : CategoryThe…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.comp_map`：comp_map (F : C ⥤ D) (G : D ⥤ E) {X Y :
 C} (f : X ⟶ Y) : (F ⋙ G).map f = G.map (F.map f)
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
When composing 2-squares which form a diagram of grid, composing horizontally fi
rst yields the
same result as composing vertically first.
-/
lemma hCompVCompHComp (w₁ : TwoSquare T L R B) (w₂ : TwoSquare T' R R' B')
    (w₃ : TwoSquare B L' R'' B'') (w₄ : TwoSquare B' R'' R₃ B₃) :
    (w₁ ≫ₕ w₂) ≫ᵥ (w₃ ≫ₕ w₄) = (w₁ ≫ᵥ w₃) ≫ₕ (w₂ ≫ᵥ w₄) := by
  unfold hComp vComp whiskerLeft whiskerRight
  ext c
  simp only [comp_obj, NatTrans.comp_app, associator_hom_app, associator_inv_app, comp_id, id_comp,
    map_comp, assoc]
  slice_rhs 2 3 =>
    rw [← Functor.comp_map _ B₃, ← w₄.naturality]
  simp

end Interchange

end TwoSquare

end CategoryTheory

