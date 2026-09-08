/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.CategoryTheory.Triangulated.Opposite.Triangulated

/-!
# Localizing subcategories

Let `C` be a pretriangulated category. If `A` and `B` are triangulated
subcategories of `C`, we define predicates (typeclasses
`IsVerdierRightLocalizing` and `IsVerdierLeftLocalizing`)
saying that `A` is right `B`-localizing (or left `B`-localizing).
When `B` is closed under isomorphisms, we show that this implies that
the functor from the Verdier quotient `A/(A ⊓ B)` to `C/B` is fully
faithful.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*,
  Proposition 2.3.5, Chapitre II][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Pretriangulated Opposite

namespace ObjectProperty

variable {C D D₁ D₂ : Type*} [Category* C] [Category* D] [Category* D₁] [Category* D₂]

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
right `B`-localizing if any morphism `X ⟶ Y` with `X` in `B` and
`Y` in `A` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierRightLocalizing_iff` for a characterization which
relies on it. -/
/-
**CategoryTheory.ObjectProperty.IsVerdierRightLocalizing** 是 Mathlib 中的一个归纳类型，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → CategoryTheory.ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
right `B`-localizing if any morphism `X ⟶ Y` with `X` in `B` and
`Y` in `A` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierRightLocalizing_iff` for a characterization which
relies on it.
-/
class IsVerdierRightLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : B X) (hY : A Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f

/-- If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
left `B`-localizing if any morphism `X ⟶ Y` with `X` in `A` and
`Y` in `B` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierLeftLocalizing_iff` for a characterization which
relies on it. -/
/-
**CategoryTheory.ObjectProperty.IsVerdierLeftLocalizing** 是 Mathlib 中的一个归纳类型，位于命
名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     Cat
egoryTheory.ObjectProperty C → CategoryTheory.ObjectProperty C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` and `B` are triangulated subcategories of a (pre)triangulated
category `C` (with `B` closed under isomorphisms), we say that `A` is
left `B`-localizing if any morphism `X ⟶ Y` with `X` in `A` and
`Y` in `B` factors through an object that is in `A` and `B`.
Note that the definition does not use the (pre)triangulated structure:
see `isVerdierLeftLocalizing_iff` for a characterization which
relies on it.
-/
class IsVerdierLeftLocalizing (A B : ObjectProperty C) : Prop where
  fac {X Y : C} (f : X ⟶ Y) (hX : A X) (hY : B Y) :
    ∃ (Z : C) (a : X ⟶ Z) (b : Z ⟶ Y), A Z ∧ B Z ∧ a ≫ b = f
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : ObjectProperty C) [A.IsVerdierLeftLocalizing B] :
    A.op.IsVerdierRightLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ :=
      IsVerdierLeftLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierLeftLocalizing B] :
    A.unop.IsVerdierRightLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierLeftLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : ObjectProperty C) [A.IsVerdierRightLocalizing B] :
    A.op.IsVerdierLeftLocalizing B.op where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.unop hY hX
    exact ⟨_, b.op, a.op, h₁, h₂, Quiver.Hom.unop_inj fac⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A B : ObjectProperty Cᵒᵖ) [A.IsVerdierRightLocalizing B] :
    A.unop.IsVerdierLeftLocalizing B.unop where
  fac f hX hY := by
    obtain ⟨Z, a, b, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac f.op hY hX
    exact ⟨_, b.unop, a.unop, h₁, h₂, Quiver.Hom.op_inj fac⟩

variable (A B : ObjectProperty C)
/-
**CategoryTheory.ObjectProperty.isVerdierLeftLocalizing_op_iff** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isVerdierLeftLocalizing_op_iff : A.op.IsVerdierLeftLocalizing B.op ↔ A.IsV
erdierRightLocalizing B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsVerdierLeftLocalizingOppositeOpOfIsV
erdierRightLocalizing`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_
1} C] (A B : CategoryTheory.ObjectProperty C)   [A.IsVerdierRightLocalizing B], 
A.o…
-/
lemma isVerdierLeftLocalizing_op_iff :
    A.op.IsVerdierLeftLocalizing B.op ↔ A.IsVerdierRightLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsVerdierRightLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩
/-
**CategoryTheory.ObjectProperty.isVerdierRightLocalizing_op_iff** 是 Mathlib 中的一个
引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isVerdierRightLocalizing_op_iff : A.op.IsVerdierRightLocalizing B.op ↔ A.I
sVerdierLeftLocalizing B
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.instIsVerdierRightLocalizingOppositeOpOfIs
VerdierLeftLocalizing`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_
1} C] (A B : CategoryTheory.ObjectProperty C)   [A.IsVerdierLeftLocalizing B], A
.op…
-/
lemma isVerdierRightLocalizing_op_iff :
    A.op.IsVerdierRightLocalizing B.op ↔ A.IsVerdierLeftLocalizing B :=
  ⟨fun _ ↦ inferInstanceAs (A.op.unop.IsVerdierLeftLocalizing B.op.unop),
    fun _ ↦ inferInstance⟩

variable [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.isVerdierRightLocalizing_iff** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isVerdierRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated] [B.IsCl
osedUnderIsomorphisms] : A.IsVerdierRightLocalizing B ↔ forall ⦃X Y : C⦄ (s : X 
⟶ Y) (_ : A X) (_ : B.trW s), exists (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A 
⊓ B).trW s' ∧ s ≫ b = s'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff'`：trW_iff' [P.IsStableUnderShift I
nt] {Y Z : C} (g : Y ⟶ Z) : P.trW g ↔ exists (X : C) (f : X ⟶ Y) (h : Z ⟶ X⟦(1 :
 Int)⟧) (_ : Triangle.mk f g…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsVerdierRightLocalizing.fac`：∀ {C : Type 
u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {A B : CategoryTheory.ObjectP
roperty C}   [self : A.IsVerdierRightLocalizing …
· 使用定理 `CategoryTheory.ObjectProperty.distinguished_cocone_triangle`：∀ {C : Type
 u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Lim
its.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedClosed₃OfIsTriangulated`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Catego
ryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism`
：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderShiftMin`：∀ {C : Type u_1
} [inst : CategoryTheory.Category.{v_1, u_1} C] (P Q : CategoryTheory.ObjectProp
erty C) {A : Type u_2}   [inst_1 : AddMonoid …
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Pretriangulated.distinguished_cocone_triangle`：∀ {C : Typ
e u} {inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.H
asZeroObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用定理 `CategoryTheory.ObjectProperty.distinguished_cocone_triangle₁`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedClosed₁OfIsTriangulated`
：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Catego
ryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.Pretriangulated.complete_distinguished_triangle_morphism₁
`：complete_distinguished_triangle_morphism₁ (T₁ T₂ : Triangle C) (hT₁ : T₁ in di
stTriang C) (hT₂ : T₂ in distTriang C) (b : T₁.obj₂ ⟶ T₂.obj₂)…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.trW_iff_of_distinguished'`：trW_iff_of_dist
inguished' [P.IsStableUnderShift Int] [P.IsClosedUnderIsomorphisms] (T : Triangl
e C) (hT : T in distTriang C) : P.trW T.mor₂ …
· 使用引理 `CategoryTheory.ObjectProperty.trW_monotone`：trW_monotone {Q : ObjectProp
erty C} (h : P <= Q) : P.trW <= Q.trW
-/
lemma isVerdierRightLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierRightLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A X) (_ : B.trW s),
        ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' := by
  refine ⟨fun _ X Y s hX hs ↦ ?_, fun hA ↦ ⟨fun {X Y} f hX hY ↦ ?_⟩⟩
  · rw [ObjectProperty.trW_iff'] at hs
    obtain ⟨W, a, b, hT, hW⟩ := hs
    obtain ⟨W', c, d, h₁, h₂, fac⟩ := IsVerdierRightLocalizing.fac a hW hX
    obtain ⟨U, hU, e, f, hT'⟩ := A.distinguished_cocone_triangle d h₁ hX
    obtain ⟨g, hg, _⟩ := Pretriangulated.complete_distinguished_triangle_morphism _ _ hT hT'
      c (𝟙 _) (by cat_disch)
    refine ⟨U, e, g, hU, ?_, by cat_disch⟩
    rw [ObjectProperty.trW_iff']
    exact ⟨_, _, _, hT', h₁, h₂⟩
  · obtain ⟨Z, s, b, hT⟩ := Pretriangulated.distinguished_cocone_triangle f
    have hs : B.trW s := by
      rw [trW_iff']
      exact ⟨_, _, _, hT, hX⟩
    obtain ⟨W, s', g, hW, hs', fac⟩ := hA s hY hs
    obtain ⟨U, hU, a, c, hT'⟩ := A.distinguished_cocone_triangle₁ s' hY hW
    obtain ⟨t, ht, ht'⟩ :=
      complete_distinguished_triangle_morphism₁ _ _ hT hT' (𝟙 Y) g (by cat_disch)
    exact ⟨U, t, a, hU, (B.trW_iff_of_distinguished' _ hT').1 (trW_monotone (by simp) _ hs'),
      by cat_disch⟩

variable {A B} in
/-
**CategoryTheory.ObjectProperty.IsVerdierRightLocalizing.fac'** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.ObjectProperty.IsVerdierRightLocalizing`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A B : Cate
goryTheory.ObjectProperty C}   [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
[inst_2 : CategoryTheory.HasShift C ℤ]   [inst_3 : CategoryTheory.Preadditive C]
 [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]   [inst_5 : Ca
tegoryTheory.Pretriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClose
dUnderIsomorphisms]   [A.IsVerdierRightLocalizing B] {X Y : C} (s : X ⟶ Y),   A 
X → B.trW s → ∃ Z s' b, A Z ∧ (A ⊓ B).trW s' ∧ CategoryTheory.CategoryStruct.com
p s b = s'
参数：n : ℤ；CategoryTheory.shiftFunctor C n；s : X ⟶ Y；A ⊓ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.isVerdierRightLocalizing_iff`：isVerdierRig
htLocalizing_iff [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphi
sms] : A.IsVerdierRightLocalizing B ↔ forall ⦃X …
-/
lemma IsVerdierRightLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierRightLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hX : A X) (hs : B.trW s) :
    ∃ (Z : C) (s' : X ⟶ Z) (b : Y ⟶ Z), A Z ∧ (A ⊓ B).trW s' ∧ s ≫ b = s' :=
  (isVerdierRightLocalizing_iff A B).1 inferInstance s hX hs
/-
**CategoryTheory.ObjectProperty.isVerdierLeftLocalizing_iff** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isVerdierLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated] [B.IsClo
sedUnderIsomorphisms] : A.IsVerdierLeftLocalizing B ↔ forall ⦃X Y : C⦄ (s : X ⟶ 
Y) (_ : A Y) (_ : B.trW s), exists (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ 
B).trW s' ∧ a ≫ s = s'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.isVerdierRightLocalizing_op_iff`：isVerdier
RightLocalizing_op_iff : A.op.IsVerdierRightLocalizing B.op ↔ A.IsVerdierLeftLoc
alizing B
· 使用定理 `CategoryTheory.Pretriangulated.Opposite.instAdditiveOppositeShiftFunctor
Int`：∀ (C : Type u_1) [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : Ca
tegoryTheory.HasShift C ℤ]   [inst_2 : CategoryTheory.Preadditive…
· 使用引理 `CategoryTheory.ObjectProperty.isVerdierRightLocalizing_iff`：isVerdierRig
htLocalizing_iff [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphi
sms] : A.IsVerdierRightLocalizing B ↔ forall ⦃X …
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedOppositeOp`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.HasS
hift C ℤ]   [inst_2 : CategoryTheory.Limits.HasZ…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderIsomorphismsOppositeOp`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C)   [P.IsClosedUnderIsomorphisms], P.op.IsClose…
· 使用引理 `CategoryTheory.ObjectProperty.trW_of_op`：trW_of_op (P : ObjectProperty C
) [P.IsTriangulated] {X Y : C} {f : X ⟶ Y} (hf : P.op.trW f.op) : P.trW f
· 使用定理 `CategoryTheory.ObjectProperty.instIsTriangulatedMinOfIsClosedUnderIsomor
phisms`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 :
 CategoryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.trW_of_unop`：trW_of_unop (P : ObjectProper
ty Cᵒᵖ) [P.IsTriangulated] {X Y : Cᵒᵖ} {f : X ⟶ Y} (hf : P.unop.trW f.unop) : P.
trW f
-/
lemma isVerdierLeftLocalizing_iff [A.IsTriangulated] [B.IsTriangulated]
    [B.IsClosedUnderIsomorphisms] :
    A.IsVerdierLeftLocalizing B ↔
      ∀ ⦃X Y : C⦄ (s : X ⟶ Y) (_ : A Y) (_ : B.trW s),
        ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' := by
  rw [← isVerdierRightLocalizing_op_iff, isVerdierRightLocalizing_iff]
  refine ⟨fun hA X Y s hY hs ↦ ?_, fun hA X Y s hX hs ↦ ?_⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.op hY (by simpa [trW_op_iff])
    exact ⟨Z'.unop, s'.unop, b.unop, hZ', trW_of_op _ hs', by cat_disch⟩
  · obtain ⟨Z', s', b, hZ', hs', fac⟩ := hA s.unop hX (trW_of_op _ hs)
    exact ⟨_, s'.op, b.op, hZ', trW_of_unop _ hs', by cat_disch⟩

variable {A B} in
/-
**CategoryTheory.ObjectProperty.IsVerdierLeftLocalizing.fac'** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ObjectProperty.IsVerdierLeftLocalizing`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {A B : Cate
goryTheory.ObjectProperty C}   [inst_1 : CategoryTheory.Limits.HasZeroObject C] 
[inst_2 : CategoryTheory.HasShift C ℤ]   [inst_3 : CategoryTheory.Preadditive C]
 [inst_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive]   [inst_5 : Ca
tegoryTheory.Pretriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClose
dUnderIsomorphisms]   [A.IsVerdierLeftLocalizing B] {X Y : C} (s : X ⟶ Y),   A Y
 → B.trW s → ∃ Z s' a, A Z ∧ (A ⊓ B).trW s' ∧ CategoryTheory.CategoryStruct.comp
 a s = s'
参数：n : ℤ；CategoryTheory.shiftFunctor C n；s : X ⟶ Y；A ⊓ B。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.isVerdierLeftLocalizing_iff`：isVerdierLeft
Localizing_iff [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphism
s] : A.IsVerdierLeftLocalizing B ↔ forall ⦃X Y …
-/
lemma IsVerdierLeftLocalizing.fac'
    [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]
    [A.IsVerdierLeftLocalizing B]
    {X Y : C} (s : X ⟶ Y) (hY : A Y) (hs : B.trW s) :
    ∃ (Z : C) (s' : Z ⟶ Y) (a : Z ⟶ X), A Z ∧ (A ⊓ B).trW s' ∧ a ≫ s = s' :=
  (isVerdierLeftLocalizing_iff A B).1 inferInstance s hY hs

/-- If `A` is a triangulated subcategory of a pretriangulated category `C`,
and `B : ObjectProperty C`, this is the inclusion functor
`A.ι : A.FullSubcategory ⥤ C`, considered as a localizer morphism,
where `C` is equipped with the property of morphisms `B.trW`
and `A.FullSubcategory` with the property of morphisms `(B.inverseImage A.ι).trW`. -/
@[instance_reducible]
/-
**CategoryTheory.ObjectProperty.triangulatedLocalizerMorphism** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangulatedLocalizerMorphism [A.IsTriangulated] : LocalizerMorphism (B.in
verseImage A.ι).trW B.trW where functor
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…

--- 原说明 ---
If `A` is a triangulated subcategory of a pretriangulated category `C`,
and `B : ObjectProperty C`, this is the inclusion functor
`A.ι : A.FullSubcategory ⥤ C`, considered as a localizer morphism,
where `C` is equipped with the property of morphisms `B.trW`
and `A.FullSubcategory` with the property of morphisms `(B.inverseImage A.ι).trW
`.
-/
def triangulatedLocalizerMorphism [A.IsTriangulated] :
    LocalizerMorphism (B.inverseImage A.ι).trW B.trW where
  functor := A.ι
  map X Y f hf := by
    simp only [MorphismProperty.inverseImage_iff, trW_iff] at hf ⊢
    obtain ⟨Z, a, b, hT, hZ⟩ := hf
    exact ⟨_, _, _, A.ι.map_distinguished _ hT, hZ⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.CommShift ℤ :=
  inferInstanceAs (A.ι.CommShift ℤ)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [A.IsTriangulated] :
    (triangulatedLocalizerMorphism A B).functor.IsTriangulated :=
  inferInstanceAs A.ι.IsTriangulated

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.trW_inverseImage_** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trW_inverseImage_ι_iff [A.IsTriangulated] {X Y : A.FullSubcategory} (f : X ⟶ Y) :
    (B.inverseImage A.ι).trW f ↔ (A ⊓ B).trW f.hom := by
  simp only [trW_iff]
  constructor
  · rintro ⟨Z, a, b, h, hZ⟩
    exact ⟨_, _, _, A.ι.map_distinguished _ h, Z.property, hZ⟩
  · rintro ⟨Z, a, b, h, hZ⟩
    refine ⟨⟨Z, hZ.1⟩, A.homMk a, A.homMk (b ≫ (A.ι.commShiftIso 1).inv.app _), ?_, hZ.2⟩
    rw [← A.ι.map_distinguished_iff]
    refine isomorphic_distinguished _ h _
      (Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_)
    · cat_disch
    · cat_disch
    · simp [dsimp% (A.ι.commShiftIso (1 : ℤ)).inv_hom_id_app X]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.inverseImage_opEquivalence_inverse_trW_inverseIm
age_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op [A.IsTriangulated]
    [B.IsTriangulated] [B.IsClosedUnderIsomorphisms] :
    (B.op.inverseImage A.op.ι).trW.inverseImage A.opEquivalence.inverse =
      (B.inverseImage A.ι).op.trW := by
  ext ⟨X₁⟩ ⟨X₂⟩ a
  simp [trW_op, trW_inverseImage_ι_iff, ← op_inf]

variable [IsTriangulated C] [A.IsTriangulated] [B.IsTriangulated] [B.IsClosedUnderIsomorphisms]

section

variable [A.IsVerdierRightLocalizing B]
  (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  have : L₁.EssSurj := Localization.essSurj L₁ (B.inverseImage A.ι).trW
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine F.full_of_comp_essSurj L₁ (fun X₁ X₂ φ ↦ ?_)
  obtain ⟨φ', hφ'⟩ : ∃ φ', φ = e.inv.app X₁ ≫ φ' ≫ e.hom.app X₂ :=
    ⟨e.hom.app X₁ ≫ φ ≫ e.inv.app X₂, by
      simp [dsimp% e.inv_hom_id_app_assoc, dsimp% e.inv_hom_id_app]⟩
  obtain ⟨f, hf⟩ := Localization.exists_leftFraction L₂ B.trW φ'
  obtain ⟨X₃, s', a, hX₃, hs', fac⟩ :=
    IsVerdierRightLocalizing.fac' f.s X₂.property f.hs
  let g : (B.inverseImage A.ι).trW.LeftFraction X₁ X₂ :=
    { Y' := ⟨X₃, hX₃⟩
      f := A.homMk (f.f ≫ a)
      s := A.homMk s'
      hs := by rwa [trW_inverseImage_ι_iff] }
  have := Localization.inverts L₁ _ _ g.hs
  refine ⟨g.map L₁ (Localization.inverts _ _), ?_⟩
  rw [← cancel_mono (F.map (L₁.map g.s)), ← Functor.map_comp,
    MorphismProperty.LeftFraction.map_comp_map_s]
  simp [g, ← fac, hφ', hf, ← dsimp% NatIso.naturality_1 e,
    dsimp% e.hom_inv_id_app_assoc]
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  let := Localization.preadditive L₁ (B.inverseImage A.ι).trW
  let := Localization.preadditive L₂ B.trW
  have := Localization.functor_additive L₁ (B.inverseImage A.ι).trW
  have := Localization.functor_additive L₂ B.trW
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F :=
    CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  refine Functor.faithful_of_comp_cancel_zero_of_hasLeftCalculusOfFractions L₁
    (B.inverseImage A.ι).trW F (fun X₁ X₂ f hf ↦ ?_)
  replace hf : L₂.map f.hom = L₂.map 0 := by
    simp [← dsimp% NatIso.naturality_2 e f, hf]
  rw [MorphismProperty.map_eq_iff_postcomp L₂ B.trW] at hf
  obtain ⟨X₃, s, hs, fac⟩ := hf
  obtain ⟨X₄, t, a, hX₄, ht, fac'⟩ :=
    IsVerdierRightLocalizing.fac' s X₂.property hs
  let t' : X₂ ⟶ ⟨X₄, hX₄⟩ := A.homMk t
  have := Localization.inverts L₁ (B.inverseImage A.ι).trW t'
    (by rwa [trW_inverseImage_ι_iff])
  rw [← cancel_mono (L₁.map t'), zero_comp, ← L₁.map_comp, ← L₁.map_zero]
  congr 1
  ext
  simp [t', ← fac', reassoc_of% fac]

end

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [A.IsVerdierRightLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful where
  nonempty_fullyFaithful := ⟨.ofFullyFaithful _⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [A.IsVerdierLeftLocalizing B] :
    (A.triangulatedLocalizerMorphism B).IsLocalizedFullyFaithful := by
  let L₁ := (B.inverseImage A.ι).trW.Q
  let L₂ := B.trW.Q
  let F : (B.inverseImage A.ι).trW.Localization ⥤ B.trW.Localization :=
    (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  let : CatCommSq (A.op.triangulatedLocalizerMorphism B.op).functor
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op :=
    ⟨Functor.isoWhiskerLeft A.opEquivalence.functor
      (NatIso.op (CatCommSq.iso (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F).symm)⟩
  have : L₂.op.IsLocalization B.op.trW := by rw [trW_op]; infer_instance
  have : (A.opEquivalence.functor ⋙ L₁.op).IsLocalization (B.op.inverseImage A.op.ι).trW := by
    refine Functor.IsLocalization.of_equivalence_source L₁.op (B.inverseImage A.ι).trW.op
      _ _ A.opEquivalence.symm ?_ ?_
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight A.opEquivalence.counitIso _ ≪≫ Functor.leftUnitor _)
    · rw [← trW_op, ← inverseImage_opEquivalence_inverse_trW_inverseImage_ι_op]
      intro _ _ f hf
      simp only [MorphismProperty.inverseImage_iff, Equivalence.symm_functor] at hf ⊢
      exact MorphismProperty.le_isoClosure _ _ hf
    · refine fun _ _ _ hf ↦ Localization.inverts L₁.op (B.inverseImage A.ι).trW.op _ ?_
      simpa [trW_inverseImage_ι_iff, ← op_inf, trW_op] using! hf
  exact LocalizerMorphism.IsLocalizedFullyFaithful.mk' (A.triangulatedLocalizerMorphism B)
    L₁ L₂ F (((A.op.triangulatedLocalizerMorphism B.op).fullyFaithful
    (A.opEquivalence.functor ⋙ L₁.op) L₂.op F.op).unop)

section

variable [A.IsVerdierLeftLocalizing B] (L₁ : A.FullSubcategory ⥤ D₁) (L₂ : C ⥤ D₂)
  [L₁.IsLocalization (B.inverseImage A.ι).trW]
  [L₂.IsLocalization B.trW]

/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Full := by
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Faithful := by
  infer_instance
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preadditive D₁] [Preadditive D₂] [L₁.Additive] [L₂.Additive] :
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂).Additive := by
  let F := (A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂
  rw [Localization.functor_additive_iff L₁ (B.inverseImage A.ι).trW]
  let e : A.ι ⋙ L₂ ≅ L₁ ⋙ F := CatCommSq.iso
    (A.triangulatedLocalizerMorphism B).functor L₁ L₂ F
  exact Functor.additive_of_iso e

/-- If `A` is a left `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
/-
**CategoryTheory.ObjectProperty.IsVerdierLeftLocalizing.fullyFaithful** 是 Mathli
b 中的一个定义，位于命名空间 `CategoryTheory.ObjectProperty.IsVerdierLeftLocalizing`。
形式化陈述：{C : Type u_1} →   {D₁ : Type u_3} →     {D₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category
.{v_3, u_3} D₁] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D₂] →  
           (A B : CategoryTheory.ObjectProperty C) →               [inst_3 : Cat
egoryTheory.Limits.HasZeroObject C] →                 [inst_4 : CategoryTheory.H
asShift C ℤ] →                   [inst_5 : CategoryTheory.Preadditive C] →      
               [inst_6 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] 
→                       [inst_7 : CategoryTheory.Pretriangulated C] →           
              [CategoryTheory.IsTriangulated C] →                           [ins
t_9 : A.IsTriangulated] →                             [B.IsTriangulated] →      
                         [B.IsClosedUnderIsomorphisms] →                        
         [A.IsVerdierLeftLocalizing B] →                                   {L₁ :
 CategoryTheory.Functor A.FullSubcategory D₁} →                                 
    {L₂ : CategoryTheory.Functor C D₂} →                                       {
F : CategoryTheory.Functor D₁ D₂} →                                         [L₁.
IsLocalization (B.inverseImage A.ι).trW] →                                      
     [L₂.IsLocalization B.trW] → (L₁.comp F ≅ A.ι.comp L₂) → F.FullyFaithful
参数：A B : CategoryTheory.ObjectProperty C；n : ℤ；CategoryTheory.shiftFunctor C n；B
.inverseImage A.ι；L₁.comp F ≅ A.ι.comp L₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…

--- 原说明 ---
If `A` is a left `B`-localizing triangulated subcategory in the sense of Verdier
,
then the induced functor between the localizations with respect to `(B.inverseIm
age A.ι).trW`
and `B.trW` is fully faithful.
-/
noncomputable def IsVerdierLeftLocalizing.fullyFaithful
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

/-- If `A` is a right `B`-localizing triangulated subcategory in the sense of Verdier,
then the induced functor between the localizations with respect to `(B.inverseImage A.ι).trW`
and `B.trW` is fully faithful. -/
@[no_expose]
/-
**CategoryTheory.ObjectProperty.IsVerdierRightLocalizing.fullyFaithful** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.ObjectProperty.IsVerdierRightLocalizing`。
形式化陈述：{C : Type u_1} →   {D₁ : Type u_3} →     {D₂ : Type u_4} →       [inst : C
ategoryTheory.Category.{v_1, u_1} C] →         [inst_1 : CategoryTheory.Category
.{v_3, u_3} D₁] →           [inst_2 : CategoryTheory.Category.{v_4, u_4} D₂] →  
           (A B : CategoryTheory.ObjectProperty C) →               [inst_3 : Cat
egoryTheory.Limits.HasZeroObject C] →                 [inst_4 : CategoryTheory.H
asShift C ℤ] →                   [inst_5 : CategoryTheory.Preadditive C] →      
               [inst_6 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] 
→                       [inst_7 : CategoryTheory.Pretriangulated C] →           
              [CategoryTheory.IsTriangulated C] →                           [ins
t_9 : A.IsTriangulated] →                             [B.IsTriangulated] →      
                         [B.IsClosedUnderIsomorphisms] →                        
         [A.IsVerdierRightLocalizing B] →                                   {L₁ 
: CategoryTheory.Functor A.FullSubcategory D₁} →                                
     {L₂ : CategoryTheory.Functor C D₂} →                                       
{F : CategoryTheory.Functor D₁ D₂} →                                         [L₁
.IsLocalization (B.inverseImage A.ι).trW] →                                     
      [L₂.IsLocalization B.trW] → (L₁.comp F ≅ A.ι.comp L₂) → F.FullyFaithful
参数：A B : CategoryTheory.ObjectProperty C；n : ℤ；CategoryTheory.shiftFunctor C n；B
.inverseImage A.ι；L₁.comp F ≅ A.ι.comp L₂。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instFullLocalizedFunctorFullSubcategoryTrW
InverseImageιTriangulatedLocalizerMorphism`：∀ {C : Type u_1} {D₁ : Type u_3} {D₂
 : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : CategoryT
heory.Category.{v_3, u_3…
· 使用定理 `CategoryTheory.ObjectProperty.instFaithfulLocalizedFunctorFullSubcategor
yTrWInverseImageιTriangulatedLocalizerMorphism`：∀ {C : Type u_1} {D₁ : Type u_3}
 {D₂ : Type u_4} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Categ
oryTheory.Category.{v_3, u_3…

--- 原说明 ---
If `A` is a right `B`-localizing triangulated subcategory in the sense of Verdie
r,
then the induced functor between the localizations with respect to `(B.inverseIm
age A.ι).trW`
and `B.trW` is fully faithful.
-/
noncomputable def IsVerdierRightLocalizing.fullyFaithful [A.IsVerdierRightLocalizing B]
    {L₁ : A.FullSubcategory ⥤ D₁} {L₂ : C ⥤ D₂} {F : D₁ ⥤ D₂}
    [L₁.IsLocalization (B.inverseImage A.ι).trW] [L₂.IsLocalization B.trW]
    (e : L₁ ⋙ F ≅ A.ι ⋙ L₂) :
    F.FullyFaithful :=
  Functor.FullyFaithful.ofIso (.ofFullyFaithful
    ((A.triangulatedLocalizerMorphism B).localizedFunctor L₁ L₂))
    (Localization.liftNatIso L₁ (B.inverseImage A.ι).trW
      ((A.triangulatedLocalizerMorphism B).functor ⋙ L₂) (L₁ ⋙ F) _ _ e.symm)

end

end ObjectProperty

end CategoryTheory

