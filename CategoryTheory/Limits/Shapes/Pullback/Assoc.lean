/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-!
# Associativity of pullbacks

This file shows that pullbacks (and pushouts) are associative up to natural isomorphism.

-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v₁ v₂ v u u₂

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

section PullbackAssoc

/-
The objects and morphisms are as follows:
```
           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁
```

where the two squares are pullbacks.

We can then construct the pullback squares

```
W  - l₂ -> Z₂ - g₄ -> X₃
|                     |
l₁                    f₄
∨                     ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
```

and

```
W' - l₂' -> Z₂
|           |
l₁'         g₃
∨           ∨
Z₁          X₂
|           |
g₁          f₂
∨           ∨
X₁ -  f₁ -> Y₁
```

We will show that both `W` and `W'` are pullbacks over `g₁, g₂`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₁) (f₃ : X₂ ⟶ Y₂)
variable (f₄ : X₃ ⟶ Y₂) [HasPullback f₁ f₂] [HasPullback f₃ f₄]

local notation "Z₁" => pullback f₁ f₂

local notation "Z₂" => pullback f₃ f₄

local notation "g₁" => (pullback.fst _ _ : Z₁ ⟶ X₁)

local notation "g₂" => (pullback.snd _ _ : Z₁ ⟶ X₂)

local notation "g₃" => (pullback.fst _ _ : Z₂ ⟶ X₂)

local notation "g₄" => (pullback.snd _ _ : Z₂ ⟶ X₃)

local notation "W" => pullback (g₂ ≫ f₃) f₄

local notation "W'" => pullback f₁ (g₃ ≫ f₂)

local notation "l₁" => (pullback.fst _ _ : W ⟶ Z₁)

local notation "l₂" =>
  (pullback.lift (pullback.fst _ _ ≫ g₂) (pullback.snd _ _)
      (Eq.trans (Category.assoc _ _ _) pullback.condition) :
    W ⟶ Z₂)

local notation "l₁'" =>
  (pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ g₃)
      (pullback.condition.trans (Eq.symm (Category.assoc _ _ _))) :
    W' ⟶ Z₁)

local notation "l₂'" => (pullback.snd f₁ (g₃ ≫ f₂))

set_option backward.isDefEq.respectTransparency false in
/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
/-
**CategoryTheory.Limits.pullbackPullbackLeftIsPullback** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Limits`。
形式化陈述：pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (Pullb
ackCone.mk l₁ l₂ (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm))
参数：g₂ ≫ f₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
`(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`.
-/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone.mk l₁ l₂
    (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply leftSquareIsPullback _ rfl (pullbackIsPullback f₃ f₄)
  simpa [PullbackCone.pasteHoriz] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ f₄)

/-- `(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
/-
**CategoryTheory.Limits.pullbackAssocIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.Limits`。
形式化陈述：pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone
.mk (l₁ ≫ g₁) l₂ (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by rw [pullback.lift_fst_as
soc]; rw [Category.assoc]; rw [Category.assoc]; rw [pullback.condition]))
参数：g₂ ≫ f₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
`(X₁ ×[Y₁] X₂) ×[Y₂] X₃` is the pullback `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`.
-/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  simpa using! pasteVertIsPullback rfl (pullbackIsPullback _ _)
    (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄)
/-
**CategoryTheory.Limits.hasPullback_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Limits`。
形式化陈述：hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂)
参数：g₂ ≫ f₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
-/
theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`. -/
/-
**CategoryTheory.Limits.pullbackPullbackRightIsPullback** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Limits`。
形式化陈述：pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] : IsLimit (Pull
backCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _))
参数：g₃ ≫ f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
`X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[X₂] (X₂ ×[Y₂] X₃)`.
-/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply topSquareIsPullback _ rfl (pullbackIsPullback f₁ f₂)
  simpa [PullbackCone.pasteVert] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ _)

/-- `X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`. -/
/-
**CategoryTheory.Limits.pullbackAssocSymmIsPullback** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] : IsLimit (Pullback
Cone.mk l₁' (l₂' ≫ g₄) (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by rw [pullback.lif
t_snd_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [pullback.condition])
)
参数：g₃ ≫ f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…

--- 原说明 ---
`X₁ ×[Y₁] (X₂ ×[Y₂] X₃)` is the pullback `(X₁ ×[Y₁] X₂) ×[Y₂] X₃`.
-/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc, Category.assoc, Category.assoc, pullback.condition])) := by
  simpa [PullbackCone.pasteHoriz] using! pasteHorizIsPullback rfl
    (pullbackIsPullback f₃ f₄) (pullbackPullbackRightIsPullback _ _ _ _)
/-
**CategoryTheory.Limits.hasPullback_assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Limits`。
形式化陈述：hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) 
f₄
参数：g₃ ≫ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

/-- The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`. -/
/-
**CategoryTheory.Limits.pullbackAssoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Limits`。
形式化陈述：pullbackAssoc [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPul
lback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : pullback (pullback.snd _ _ ≫ f₃ 
: pullback f₁ f₂ ⟶ _) f₄ ≅ pullback f₁ (pullback.fst _ _ ≫ f₂ : pullback f₃ f₄ ⟶
 _)
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(X₁ ×[Y₁] X₂) ×[Y₂] X₃ ≅ X₁ ×[Y₁] (X₂ ×[Y₂] X₃)`.
-/
noncomputable def pullbackAssoc [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    pullback (pullback.snd _ _ ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst _ _ ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_inv_fst_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackAssoc_inv_fst_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃)
 f₄] [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂
 f₃ f₄).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_inv_comp`：conePoint
UniqueUpToIso_inv_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).inv ≫ s.π.app j = t.π.…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackAssoc_inv_fst_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ := by
  trans l₁' ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_hom_fst** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：pullbackAssoc_hom_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
 [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂ f₃ 
f₄).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_inv_fst_fst`：pullbackAssoc_inv_fst_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
-/
theorem pullbackAssoc_hom_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [← Iso.eq_inv_comp, pullbackAssoc_inv_fst_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_hom_snd_fst** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackAssoc_hom_snd_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃)
 f₄] [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂
 f₃ f₄).hom ≫ pullback.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.
snd _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.pullback.lift_fst`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackAssoc_hom_snd_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫
    pullback.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.snd _ _ := by
  trans l₂ ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_hom_snd_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackAssoc_hom_snd_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃)
 f₄] [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂
 f₃ f₄).hom ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.IsLimit.conePointUniqueUpToIso_hom_comp`：conePoint
UniqueUpToIso_hom_comp {s t : Cone F} (P : IsLimit s) (Q : IsLimit t) (j : J) : 
(conePointUniqueUpToIso P Q).hom ≫ t.π.app j = s.π.…
· 使用定理 `CategoryTheory.Limits.pullback.lift_snd`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Cate
goryTheory.Limits.HasPullback…
-/
theorem pullbackAssoc_hom_snd_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _ := by
  trans l₂ ≫ pullback.snd _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_inv_fst_snd** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pullbackAssoc_inv_fst_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃)
 f₄] [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂
 f₃ f₄).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.
fst _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_fst`：pullbackAssoc_hom_snd_f
st [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
-/
theorem pullbackAssoc_inv_fst_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.fst _ _ := by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.pullbackAssoc_inv_snd** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：pullbackAssoc_inv_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
 [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullbackAssoc f₁ f₂ f₃ 
f₄).inv ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _
参数：(pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃；(pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `CategoryTheory.Limits.pullbackAssoc_hom_snd_snd`：pullbackAssoc_hom_snd_s
nd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄] [HasPullback f₁ ((pullba
ck.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] : (pullb…
-/
theorem pullbackAssoc_inv_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_snd]

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

```
           Z₂ - g₄ -> X₃
           |          |
           g₃         f₄
           ∨          ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|          |
g₁         f₂
∨          ∨
X₁ - f₁ -> Y₁
```

where the two squares are pushouts.

We can then construct the pushout squares

```
Z₁ - g₂ -> X₂ - f₃ -> Y₂
|                     |
g₁                    l₂
∨                     ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄  -> X₃
|           |
g₃          f₄
∨           ∨
X₂          Y₂
|           |
f₂          l₂'
∨           ∨
Y₁ - l₁' -> W'
```

We will show that both `W` and `W'` are pushouts over `f₂, f₃`, and thus we may construct a
canonical isomorphism between them. -/
variable {X₁ X₂ X₃ Z₁ Z₂ : C} (g₁ : Z₁ ⟶ X₁) (g₂ : Z₁ ⟶ X₂) (g₃ : Z₂ ⟶ X₂)
variable (g₄ : Z₂ ⟶ X₃) [HasPushout g₁ g₂] [HasPushout g₃ g₄]

local notation "Y₁" => pushout g₁ g₂

local notation "Y₂" => pushout g₃ g₄

local notation "f₁" => (pushout.inl _ _ : X₁ ⟶ Y₁)

local notation "f₂" => (pushout.inr _ _ : X₂ ⟶ Y₁)

local notation "f₃" => (pushout.inl _ _ : X₂ ⟶ Y₂)

local notation "f₄" => (pushout.inr _ _ : X₃ ⟶ Y₂)

local notation "W" => pushout g₁ (g₂ ≫ f₃)

local notation "W'" => pushout (g₃ ≫ f₂) g₄

local notation "l₁" =>
  (pushout.desc (pushout.inl _ _) (f₃ ≫ pushout.inr _ _)
    (pushout.condition.trans (Category.assoc _ _ _)) : Y₁ ⟶ W)

local notation "l₂" => (pushout.inr _ _ : Y₂ ⟶ W)

local notation "l₁'" => (pushout.inl _ _ : Y₁ ⟶ W')

local notation "l₂'" =>
  (pushout.desc (f₂ ≫ pushout.inl _ _) (pushout.inr _ _)
      (Eq.trans (Eq.symm (Category.assoc _ _ _)) pushout.condition) :
    Y₂ ⟶ W')

set_option backward.isDefEq.respectTransparency false in
/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
/-
**CategoryTheory.Limits.pushoutPushoutLeftIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Limits`。
形式化陈述：pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] : IsColimit (Pushout
Cocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm))
参数：g₃ ≫ f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
`(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`.
-/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) := by
  apply botSquareIsPushout _ rfl (pushoutIsPushout _ g₄)
  simpa [PushoutCocone.pasteVert] using
    PushoutCocone.mkSelfIsColimit (pushoutIsPushout (g₃ ≫ f₂) g₄)

/-- `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
/-
**CategoryTheory.Limits.pushoutAssocIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] : IsColimit (PushoutCocone
.mk (f₁ ≫ l₁') l₂' (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by rw [Category.assoc];
 rw [pushout.inl_desc]; rw [pushout.condition_assoc]))
参数：g₃ ≫ f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
`(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃` is the pushout `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`.
-/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [Category.assoc, pushout.inl_desc, pushout.condition_assoc])) := by
  simpa using! pasteHorizIsPushout rfl (pushoutIsPushout g₁ g₂)
    (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄)
/-
**CategoryTheory.Limits.hasPushout_assoc** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheo
ry.Limits`。
形式化陈述：hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃)
参数：g₃ ≫ f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
-/
theorem hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`. -/
/-
**CategoryTheory.Limits.pushoutPushoutRightIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Limits`。
形式化陈述：pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] : IsColimit (Pushou
tCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _))
参数：g₂ ≫ f₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
`X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ×[X₂] (X₂ ⨿[Z₂] X₃)`.
-/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) := by
  apply rightSquareIsPushout _ rfl (pushoutIsPushout _ _)
  simpa [PushoutCocone.pasteHoriz] using PushoutCocone.mkSelfIsColimit (pushoutIsPushout _ _)

/-- `X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`. -/
/-
**CategoryTheory.Limits.pushoutAssocSymmIsPushout** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Limits`。
形式化陈述：pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] : IsColimit (PushoutCo
cone.mk l₁ (f₄ ≫ l₂) (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by rw [Category.assoc];
 rw [pushout.inr_desc]; rw [pushout.condition_assoc]))
参数：g₂ ≫ f₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …

--- 原说明 ---
`X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)` is the pushout `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃`.
-/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [Category.assoc, pushout.inr_desc, pushout.condition_assoc])) := by
  simpa using! pasteVertIsPushout rfl (pushoutIsPushout _ _) (pushoutPushoutRightIsPushout _ _ _ _)
/-
**CategoryTheory.Limits.hasPushout_assoc_symm** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Limits`。
形式化陈述：hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄
参数：g₂ ≫ f₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

/-- The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`. -/
/-
**CategoryTheory.Limits.pushoutAssoc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.L
imits`。
形式化陈述：pushoutAssoc [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [HasPushou
t g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout (g₃ ≫ pushout.inr _ _ : _ ⟶ p
ushout g₁ g₂) g₄ ≅ pushout g₁ (g₂ ≫ pushout.inl _ _ : _ ⟶ pushout g₃ g₄)
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism `(X₁ ⨿[Z₁] X₂) ⨿[Z₂] X₃ ≅ X₁ ⨿[Z₁] (X₂ ⨿[Z₂] X₃)`.
-/
noncomputable def pushoutAssoc [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout (g₃ ≫ pushout.inr _ _ : _ ⟶ pushout g₁ g₂) g₄ ≅
      pushout g₁ (g₂ ≫ pushout.inl _ _ : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_inl_pushoutAssoc_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：inl_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄
] [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inl _ _ ≫ pushout
.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inl_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inl _ _ ≫ pushout.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl _ _ := by
  trans f₁ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_inl_pushoutAssoc_hom** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：inr_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄
] [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inr _ _ ≫ pushout
.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inl _ _ ≫ pushout.inr _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_hom`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inr_inl_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inr _ _ ≫ pushout.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom =
      pushout.inl _ _ ≫ pushout.inr _ _ := by
  trans f₂ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_inr_pushoutAssoc_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：inr_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄
] [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inr _ _ ≫ pushout
.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.pushout.condition`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Catego
ryTheory.Limits.HasPushout f …
· 使用定理 `CategoryTheory.Limits.IsColimit.comp_coconePointUniqueUpToIso_inv`：∀ {J 
: Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : C
ategoryTheory.Category.{v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.pushout.inl_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
· 使用定理 `CategoryTheory.Limits.pushout.inr_desc`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] {W X Y Z : C} {f : X ⟶ Y} {g : X ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPushout …
-/
theorem inr_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inr _ _ ≫ pushout.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr _ _ := by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄) WalkingCospan.right
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_pushoutAssoc_inv** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：inl_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [H
asPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inl _ _ ≫ (pushoutAss
oc g₁ g₂ g₃ g₄).inv = pushout.inl _ _ ≫ pushout.inl _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.inl_inl_pushoutAssoc_hom`：inl_inl_pushoutAssoc_hom
 [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [HasPushout g₁ (g₂ ≫ (pushou
t.inl _ _ : X₂ ⟶ Y₂))] : pushout.inl…
-/
theorem inl_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl _ _ ≫ pushout.inl _ _ := by
  rw [Iso.comp_inv_eq, Category.assoc, inl_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inl_inr_pushoutAssoc_inv** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Limits`。
形式化陈述：inl_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄
] [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inl _ _ ≫ pushout
.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inr _ _ ≫ pushout.inl _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `CategoryTheory.Limits.inr_inl_pushoutAssoc_hom`：inr_inl_pushoutAssoc_hom
 [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [HasPushout g₁ (g₂ ≫ (pushou
t.inl _ _ : X₂ ⟶ Y₂))] : pushout.inr…
-/
theorem inl_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inl _ _ ≫ pushout.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv =
      pushout.inr _ _ ≫ pushout.inl _ _ := by
  rw [← Category.assoc, Iso.comp_inv_eq, Category.assoc, inr_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]
/-
**CategoryTheory.Limits.inr_pushoutAssoc_hom** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Limits`。
形式化陈述：inr_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [H
asPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] : pushout.inr _ _ ≫ (pushoutAss
oc g₁ g₂ g₃ g₄).hom = pushout.inr _ _ ≫ pushout.inr _ _
参数：g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)；g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_comp_inv`：eq_comp_inv (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : g = f ≫ α.inv ↔ g ≫ α.hom = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.inr_inr_pushoutAssoc_inv`：inr_inr_pushoutAssoc_inv
 [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄] [HasPushout g₁ (g₂ ≫ (pushou
t.inl _ _ : X₂ ⟶ Y₂))] : pushout.inr…
-/
theorem inr_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inr _ _ ≫ pushout.inr _ _ := by
  rw [← Iso.eq_comp_inv, Category.assoc, inr_inr_pushoutAssoc_inv]

end PushoutAssoc

end CategoryTheory.Limits

