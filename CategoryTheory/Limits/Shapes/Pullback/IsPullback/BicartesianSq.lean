/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Joël Riou, Calle Sönne
-/
module

public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Bi-Cartesian squares

`BicartesianSq f g h i` is the proposition that
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
is a pullback square *and* a pushout square.

We show that the pullback and pushout squares for a biproduct are bi-Cartesian.
-/

@[expose] public section

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- A *bi-Cartesian* square is a commutative square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
that is both a pullback square and a pushout square.
-/
/-
**CategoryTheory.BicartesianSq** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} →   [inst : CategoryTheory.Category.{v₁, u₁} C] → {W X Y Z :
 C} → (W ⟶ X) → (W ⟶ Y) → (X ⟶ Z) → (Y ⟶ Z) → Prop
参数：W ⟶ X；W ⟶ Y；X ⟶ Z；Y ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *bi-Cartesian* square is a commutative square
```
  W ---f---> X
  |          |
  g          h
  |          |
  v          v
  Y ---i---> Z

```
that is both a pullback square and a pushout square.
-/
structure BicartesianSq {W X Y Z : C} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) : Prop
    extends IsPullback f g h i, IsPushout f g h i


variable [HasZeroObject C] [HasZeroMorphisms C]
open ZeroObject

namespace IsPullback

variable {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-
**CategoryTheory.IsPullback.of_hasBinaryProduct** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.IsPullback`。
形式化陈述：of_hasBinaryProduct [HasBinaryProduct X Y] : IsPullback Limits.prod.fst Li
mits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.IsPullback.of_is_product`：of_is_product {c : BinaryFan X 
Y} (h : Limits.IsLimit c) (t : IsTerminal Z) : IsPullback c.fst c.snd (t.from _)
 (t.from _)
-/
theorem of_hasBinaryProduct [HasBinaryProduct X Y] :
    IsPullback Limits.prod.fst Limits.prod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! @of_is_product _ _ X Y 0 _ (limit.isLimit _) HasZeroObject.zeroIsTerminal
    <;> subsingleton

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback square. -/
@[simp]
/-
**CategoryTheory.IsPullback.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPullback`。
形式化陈述：zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 
⟶ X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CategoryTheory.Limits.PullbackCone.equalizer_ext`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   (t : Ca
tegoryTheory.Limits.PullbackCone f g) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.PullbackCone.condition`：condition (t : PullbackCon
e f g) : fst t ≫ f = snd t ≫ g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the left and `𝟙 X` on the right is a pullback squ
are.
-/
theorem zero_left (X : C) : IsPullback (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  { w := by simp
    isLimit' :=
      ⟨{  lift := fun _ => 0
          fac := fun s => by
            simpa [eq_iff_true_of_subsingleton] using
              @PullbackCone.equalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simpa using (PullbackCone.condition s).symm) }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback square. -/
@[simp]
/-
**CategoryTheory.IsPullback.zero_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：zero_top (X : C) : IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙
 X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.zero_left`：zero_left (X : C) : IsPullback (0 :
 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pullback squ
are.
-/
theorem zero_top (X : C) : IsPullback (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip

/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pullback square. -/
@[simp]
/-
**CategoryTheory.IsPullback.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.IsPullback`。
形式化陈述：zero_right (X : C) : IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X
 ⟶ 0)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_iso_pullback`：of_iso_pullback (h : CommSq f
st snd f g) [HasPullback f g] (i : P ≅ pullback f g) (w₁ : i.hom ≫ pullback.fst 
_ _ = fst) (w₂ : i.hom ≫ pullba…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullbackZeroZeroIso_inv_fst`：pullbackZeroZeroIso_i
nv_fst (X Y : C) [HasBinaryProduct X Y] : (pullbackZeroZeroIso X Y).inv ≫ pullba
ck.fst 0 0 = prod.fst
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.Limits.pullbackZeroZeroIso_inv_snd`：pullbackZeroZeroIso_i
nv_snd (X Y : C) [HasBinaryProduct X Y] : (pullbackZeroZeroIso X Y).inv ≫ pullba
ck.snd 0 0 = prod.snd
· 使用定理 `CategoryTheory.Limits.zeroProdIso_inv_snd`：zeroProdIso_inv_snd (X : C) :
 (zeroProdIso X).inv ≫ prod.snd = 𝟙 X

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pullback squ
are.
-/
theorem zero_right (X : C) : IsPullback (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  of_iso_pullback (by simp) ((zeroProdIso X).symm ≪≫ (pullbackZeroZeroIso _ _).symm)
    (by simp [eq_iff_true_of_subsingleton]) (by simp)

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pullback square. -/
@[simp]
/-
**CategoryTheory.IsPullback.zero_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：zero_bot (X : C) : IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶
 0)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.zero_right`：zero_right (X : C) : IsPullback (0
 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pullback squ
are.
-/
theorem zero_bot (X : C) : IsPullback (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip
/-
**CategoryTheory.IsPullback.of_isBilimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.IsPullback`。
形式化陈述：of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPullback b.fst b
.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.IsPullback.of_is_product'`：of_is_product' (h : Limits.IsL
imit (BinaryFan.mk fst snd)) (t : IsTerminal Z) : IsPullback fst snd (t.from _) 
(t.from _)
-/
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! IsPullback.of_is_product' h.isLimit HasZeroObject.zeroIsTerminal
    <;> subsingleton

@[simp]
/-
**CategoryTheory.IsPullback.of_has_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.IsPullback`。
形式化陈述：of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] : IsPullback biprod.fs
t biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_isBilimit`：of_isBilimit {b : BinaryBicone X
 Y} (h : b.IsBilimit) : IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
-/
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPullback.inl_snd'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPullback b.inl (0 : 
X ⟶ 0) b.snd (0 : 0 ⟶ Y)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.of_isBilimit`：of_isBilimit {b : BinaryBicone X
 Y} (h : b.IsBilimit) : IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
-/
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  refine of_right ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pullback square.
-/
@[simp]
/-
**CategoryTheory.IsPullback.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：inl_snd (X Y : C) [HasBinaryBiproduct X Y] : IsPullback biprod.inl (0 : X 
⟶ 0) biprod.snd (0 : 0 ⟶ Y)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.inl_snd'`：inl_snd' {b : BinaryBicone X Y} (h :
 b.IsBilimit) : IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y)

--- 原说明 ---
The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pullback square.
-/
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPullback.inr_fst'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPullback`。
形式化陈述：inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPullback b.inr (0 : 
Y ⟶ 0) b.fst (0 : 0 ⟶ X)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.of_isBilimit`：of_isBilimit {b : BinaryBicone X
 Y} (h : b.IsBilimit) : IsPullback b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
-/
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  apply flip
  refine of_bot ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pullback square.
-/
@[simp]
/-
**CategoryTheory.IsPullback.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pullback`。
形式化陈述：inr_fst (X Y : C) [HasBinaryBiproduct X Y] : IsPullback biprod.inr (0 : Y 
⟶ 0) biprod.fst (0 : 0 ⟶ X)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.inr_fst'`：inr_fst' {b : BinaryBicone X Y} (h :
 b.IsBilimit) : IsPullback b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X)

--- 原说明 ---
The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pullback square.
-/
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPullback.of_is_bilimit'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.IsPullback`。
形式化陈述：of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPullback (0 : 
0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_right`：of_right {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : 
C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ 
: X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.IsPullback.inl_snd'`：inl_snd' {b : BinaryBicone X Y} (h :
 b.IsBilimit) : IsPullback b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y)
-/
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.inl_snd' h).flip
  simp
/-
**CategoryTheory.IsPullback.of_hasBinaryBiproduct** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.IsPullback`。
形式化陈述：of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : IsPullback (0 :
 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_is_bilimit'`：of_is_bilimit' {b : BinaryBico
ne X Y} (h : b.IsBilimit) : IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr
-/
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPullback.hasPullback_biprod_fst_biprod_snd** 是 Mathlib 中的一个实例
，位于命名空间 `CategoryTheory.IsPullback`。
形式化陈述：hasPullback_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] : HasPullback (
biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasLimit.mk`：∀ {J : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C] 
  {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPullback.of_hasBinaryBiproduct`：of_hasBinaryBiproduct (
X Y : C) [HasBinaryBiproduct X Y] : IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.in
l biprod.inr
-/
instance hasPullback_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) :=
  HasLimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

/-- The pullback of `biprod.inl` and `biprod.inr` is the zero object. -/
/-
**CategoryTheory.IsPullback.pullbackBiprodInlBiprodInr** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.IsPullback`。
形式化陈述：pullbackBiprodInlBiprodInr [HasBinaryBiproduct X Y] : pullback (biprod.inl
 : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.of_hasBinaryBiproduct`：of_hasBinaryBiproduct (
X Y : C) [HasBinaryBiproduct X Y] : IsPullback (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.in
l biprod.inr

--- 原说明 ---
The pullback of `biprod.inl` and `biprod.inr` is the zero object.
-/
def pullbackBiprodInlBiprodInr [HasBinaryBiproduct X Y] :
    pullback (biprod.inl : X ⟶ _) (biprod.inr : Y ⟶ _) ≅ 0 :=
  limit.isoLimitCone ⟨_, (of_hasBinaryBiproduct X Y).isLimit⟩

end IsPullback

namespace IsPushout

variable {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P} {inr : Y ⟶ P}

/-
**CategoryTheory.IsPushout.of_hasBinaryCoproduct** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsPushout`。
形式化陈述：of_hasBinaryCoproduct [HasBinaryCoproduct X Y] : IsPushout (0 : 0 ⟶ X) (0 
: 0 ⟶ Y) coprod.inl coprod.inr
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.IsPushout.of_is_coproduct`：of_is_coproduct {c : BinaryCof
an X Y} (h : Limits.IsColimit c) (t : IsInitial Z) : IsPushout (t.to _) (t.to _)
 c.inl c.inr
-/
theorem of_hasBinaryCoproduct [HasBinaryCoproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) coprod.inl coprod.inr := by
  convert! @of_is_coproduct _ _ 0 X Y _ (colimit.isColimit _) HasZeroObject.zeroIsInitial
    <;> subsingleton

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout square. -/
@[simp]
/-
**CategoryTheory.IsPushout.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
IsPushout`。
形式化陈述：zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X 
⟶ 0)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Limits.PushoutCocone.coequalizer_ext`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   (t :
 CategoryTheory.Limits.PushoutCocone f g)…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.PushoutCocone.condition`：condition (t : PushoutCoc
one f g) : f ≫ inl t = g ≫ inr t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the right and `𝟙 X` on the left is a pushout squa
re.
-/
theorem zero_right (X : C) : IsPushout (0 : X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0) :=
  { w := by simp
    isColimit' :=
      ⟨{  desc := fun _ => 0
          fac := fun s => by
            have c :=
              @PushoutCocone.coequalizer_ext _ _ _ _ _ _ _ s _ 0 (𝟙 _)
                (by simp [eq_iff_true_of_subsingleton]) (by simpa using PushoutCocone.condition s)
            dsimp at c
            simpa using c }⟩ }

/-- The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout square. -/
@[simp]
/-
**CategoryTheory.IsPushout.zero_bot** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 
0)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.zero_right`：zero_right (X : C) : IsPushout (0 :
 X ⟶ 0) (𝟙 X) (0 : (0 : C) ⟶ 0) (0 : X ⟶ 0)

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the bottom and `𝟙 X` on the top is a pushout squa
re.
-/
theorem zero_bot (X : C) : IsPushout (𝟙 X) (0 : X ⟶ 0) (0 : X ⟶ 0) (0 : (0 : C) ⟶ 0) :=
  (zero_right X).flip

/-- The square with `0 : 0 ⟶ 0` on the right left `𝟙 X` on the right is a pushout square. -/
@[simp]
/-
**CategoryTheory.IsPushout.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.I
sPushout`。
形式化陈述：zero_left (X : C) : IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶
 X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_iso_pushout`：of_iso_pushout (h : CommSq f g 
inl inr) [HasPushout f g] (i : P ≅ pushout f g) (w₁ : inl ≫ i.hom = pushout.inl 
_ _) (w₂ : inr ≫ i.hom = push…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.inl_pushoutZeroZeroIso_inv`：inl_pushoutZeroZeroIso
_inv (X Y : C) [HasBinaryCoproduct X Y] : coprod.inl ≫ (pushoutZeroZeroIso X Y).
inv = pushout.inl _ _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the right left `𝟙 X` on the right is a pushout sq
uare.
-/
theorem zero_left (X : C) : IsPushout (0 : 0 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X) :=
  of_iso_pushout (by simp) ((coprodZeroIso X).symm ≪≫ (pushoutZeroZeroIso _ _).symm) (by simp)
    (by simp [eq_iff_true_of_subsingleton])

/-- The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pushout square. -/
@[simp]
/-
**CategoryTheory.IsPushout.zero_top** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：zero_top (X : C) : IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 
X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.zero_left`：zero_left (X : C) : IsPushout (0 : 0
 ⟶ X) (0 : (0 : C) ⟶ 0) (𝟙 X) (0 : 0 ⟶ X)

--- 原说明 ---
The square with `0 : 0 ⟶ 0` on the top and `𝟙 X` on the bottom is a pushout squa
re.
-/
theorem zero_top (X : C) : IsPushout (0 : (0 : C) ⟶ 0) (0 : 0 ⟶ X) (0 : 0 ⟶ X) (𝟙 X) :=
  (zero_left X).flip
/-
**CategoryTheory.IsPushout.of_isBilimit** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheor
y.IsPushout`。
形式化陈述：of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPushout (0 : 0 ⟶
 X) (0 : 0 ⟶ Y) b.inl b.inr
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `CategoryTheory.IsPushout.of_is_coproduct'`：of_is_coproduct' (h : Limits.
IsColimit (BinaryCofan.mk inl inr)) (t : IsInitial Z) : IsPushout (t.to _) (t.to
 _) inl inr
-/
theorem of_isBilimit {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr := by
  convert! IsPushout.of_is_coproduct' h.isColimit HasZeroObject.zeroIsInitial
    <;> subsingleton

@[simp]
/-
**CategoryTheory.IsPushout.of_has_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.IsPushout`。
形式化陈述：of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] : IsPushout (0 : 0 ⟶ X
) (0 : 0 ⟶ Y) biprod.inl biprod.inr
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_isBilimit`：of_isBilimit {b : BinaryBicone X 
Y} (h : b.IsBilimit) : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr
-/
theorem of_has_biproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr :=
  of_isBilimit (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPushout.inl_snd'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPushout b.inl (0 : X
 ⟶ 0) b.snd (0 : 0 ⟶ Y)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.IsPushout.of_left`：of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} 
{h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X
₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_snd`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPushout.of_isBilimit`：of_isBilimit {b : BinaryBicone X 
Y} (h : b.IsBilimit) : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr
-/
theorem inl_snd' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y) := by
  apply flip
  refine of_left ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pushout square.
-/
/-
**CategoryTheory.IsPushout.inl_snd** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：inl_snd (X Y : C) [HasBinaryBiproduct X Y] : IsPushout biprod.inl (0 : X ⟶
 0) biprod.snd (0 : 0 ⟶ Y)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.inl_snd'`：inl_snd' {b : BinaryBicone X Y} (h : 
b.IsBilimit) : IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y)

--- 原说明 ---
The square
```
  X --inl--> X ⊞ Y
  |            |
  0           snd
  |            |
  v            v
  0 ---0-----> Y
```
is a pushout square.
-/
theorem inl_snd (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inl (0 : X ⟶ 0) biprod.snd (0 : 0 ⟶ Y) :=
  inl_snd' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPushout.inr_fst'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Is
Pushout`。
形式化陈述：inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPushout b.inr (0 : Y
 ⟶ 0) b.fst (0 : 0 ⟶ X)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_top`：of_top {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {h
₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁₂
 ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inr_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPushout.of_isBilimit`：of_isBilimit {b : BinaryBicone X 
Y} (h : b.IsBilimit) : IsPushout (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr
-/
theorem inr_fst' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X) := by
  refine of_top ?_ (by simp) (of_isBilimit h)
  simp

/-- The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pushout square.
-/
/-
**CategoryTheory.IsPushout.inr_fst** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.IsP
ushout`。
形式化陈述：inr_fst (X Y : C) [HasBinaryBiproduct X Y] : IsPushout biprod.inr (0 : Y ⟶
 0) biprod.fst (0 : 0 ⟶ X)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.inr_fst'`：inr_fst' {b : BinaryBicone X Y} (h : 
b.IsBilimit) : IsPushout b.inr (0 : Y ⟶ 0) b.fst (0 : 0 ⟶ X)

--- 原说明 ---
The square
```
  Y --inr--> X ⊞ Y
  |            |
  0           fst
  |            |
  v            v
  0 ---0-----> X
```
is a pushout square.
-/
theorem inr_fst (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.inr (0 : Y ⟶ 0) biprod.fst (0 : 0 ⟶ X) :=
  inr_fst' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPushout.of_is_bilimit'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.IsPushout`。
形式化陈述：of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) : IsPushout b.fst 
b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
参数：h : b.IsBilimit。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_left`：of_left {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ X₂₃ : C} 
{h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃} {v₁₁ : X
₁₁ ⟶ X₂₁} {v₁₂ : X₁₂ ⟶…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.BinaryBicone.inl_fst`：∀ {C : Type uC} [inst : Cate
goryTheory.Category.{uC', uC} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C]   {P Q : C} (self : Categor…
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsPushout.inl_snd'`：inl_snd' {b : BinaryBicone X Y} (h : 
b.IsBilimit) : IsPushout b.inl (0 : X ⟶ 0) b.snd (0 : 0 ⟶ Y)
-/
theorem of_is_bilimit' {b : BinaryBicone X Y} (h : b.IsBilimit) :
    IsPushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  refine IsPushout.of_left ?_ (by simp) (IsPushout.inl_snd' h)
  simp
/-
**CategoryTheory.IsPushout.of_hasBinaryBiproduct** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.IsPushout`。
形式化陈述：of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] : IsPushout bipro
d.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
参数：X Y : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_is_bilimit'`：of_is_bilimit' {b : BinaryBicon
e X Y} (h : b.IsBilimit) : IsPushout b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0)
-/
theorem of_hasBinaryBiproduct (X Y : C) [HasBinaryBiproduct X Y] :
    IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_is_bilimit' (BinaryBiproduct.isBilimit X Y)
/-
**CategoryTheory.IsPushout.hasPushout_biprod_fst_biprod_snd** 是 Mathlib 中的一个实例，位
于命名空间 `CategoryTheory.IsPushout`。
形式化陈述：hasPushout_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] : HasPushout (bi
prod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.HasColimit.mk`：∀ {J : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C
]   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.IsPushout.of_hasBinaryBiproduct`：of_hasBinaryBiproduct (X
 Y : C) [HasBinaryBiproduct X Y] : IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (
0 : Y ⟶ 0)
-/
instance hasPushout_biprod_fst_biprod_snd [HasBinaryBiproduct X Y] :
    HasPushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) :=
  HasColimit.mk ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

/-- The pushout of `biprod.fst` and `biprod.snd` is the zero object. -/
/-
**CategoryTheory.IsPushout.pushoutBiprodFstBiprodSnd** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.IsPushout`。
形式化陈述：pushoutBiprodFstBiprodSnd [HasBinaryBiproduct X Y] : pushout (biprod.fst :
 _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.of_hasBinaryBiproduct`：of_hasBinaryBiproduct (X
 Y : C) [HasBinaryBiproduct X Y] : IsPushout biprod.fst biprod.snd (0 : X ⟶ 0) (
0 : Y ⟶ 0)

--- 原说明 ---
The pushout of `biprod.fst` and `biprod.snd` is the zero object.
-/
def pushoutBiprodFstBiprodSnd [HasBinaryBiproduct X Y] :
    pushout (biprod.fst : _ ⟶ X) (biprod.snd : _ ⟶ Y) ≅ 0 :=
  colimit.isoColimitCocone ⟨_, (of_hasBinaryBiproduct X Y).isColimit⟩

end IsPushout

namespace BicartesianSq

variable {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

omit [HasZeroObject C] [HasZeroMorphisms C] in
section

/-
**CategoryTheory.BicartesianSq.of_isPullback_isPushout** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.BicartesianSq`。
形式化陈述：of_isPullback_isPushout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i)
 : BicartesianSq f g h i
参数：p₁ : IsPullback f g h i；p₂ : IsPushout f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPushout.isColimit'`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {Z X Y P : C} {f : Z ⟶ X} {g : Z ⟶ Y} {inl : X ⟶ P}   {
inr : Y ⟶ P} (self : Cate…
-/
theorem of_isPullback_isPushout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i) :
    BicartesianSq f g h i :=
  BicartesianSq.mk p₁ p₂.isColimit'
/-
**CategoryTheory.BicartesianSq.flip** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Bi
cartesianSq`。
形式化陈述：flip (p : BicartesianSq f g h i) : BicartesianSq g f i h
参数：p : BicartesianSq f g h i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.BicartesianSq.of_isPullback_isPushout`：of_isPullback_isPu
shout (p₁ : IsPullback f g h i) (p₂ : IsPushout f g h i) : BicartesianSq f g h i
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用定理 `CategoryTheory.BicartesianSq.toIsPullback`：∀ {C : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}
   {i : Y ⟶ Z}, CategoryTheory.…
· 使用定理 `CategoryTheory.IsPushout.flip`：flip (h : IsPushout f g inl inr) : IsPush
out g f inr inl
· 使用定理 `CategoryTheory.BicartesianSq.toIsPushout`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} 
  {i : Y ⟶ Z}, CategoryTheory.…
-/
theorem flip (p : BicartesianSq f g h i) : BicartesianSq g f i h :=
  of_isPullback_isPushout p.toIsPullback.flip p.toIsPushout.flip

end


/-- ```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bi-Cartesian square.
-/
/-
**CategoryTheory.BicartesianSq.of_is_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.BicartesianSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bi-Cartesian square.
-/
theorem of_is_biproduct₁ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq b.fst b.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) :=
  of_isPullback_isPushout (IsPullback.of_isBilimit h) (IsPushout.of_is_bilimit' h)

/-- ```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bi-Cartesian square.
-/
/-
**CategoryTheory.BicartesianSq.of_is_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.BicartesianSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bi-Cartesian square.
-/
theorem of_is_biproduct₂ {b : BinaryBicone X Y} (h : b.IsBilimit) :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) b.inl b.inr :=
  of_isPullback_isPushout (IsPullback.of_is_bilimit' h) (IsPushout.of_isBilimit h)

/-- ```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bi-Cartesian square.
-/
@[simp]
/-
**CategoryTheory.BicartesianSq.of_has_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.BicartesianSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
 X ⊞ Y --fst--> X
   |            |
  snd           0
   |            |
   v            v
   Y -----0---> 0
```
is a bi-Cartesian square.
-/
theorem of_has_biproduct₁ [HasBinaryBiproduct X Y] :
    BicartesianSq biprod.fst biprod.snd (0 : X ⟶ 0) (0 : Y ⟶ 0) := by
  convert! of_is_biproduct₁ (BinaryBiproduct.isBilimit X Y)

/-- ```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bi-Cartesian square.
-/
@[simp]
/-
**CategoryTheory.BicartesianSq.of_has_biproduct** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.BicartesianSq`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
```
   0 -----0---> X
   |            |
   0           inl
   |            |
   v            v
   Y --inr--> X ⊞ Y
```
is a bi-Cartesian square.
-/
theorem of_has_biproduct₂ [HasBinaryBiproduct X Y] :
    BicartesianSq (0 : 0 ⟶ X) (0 : 0 ⟶ Y) biprod.inl biprod.inr := by
  convert! of_is_biproduct₂ (BinaryBiproduct.isBilimit X Y)

end BicartesianSq
end CategoryTheory

