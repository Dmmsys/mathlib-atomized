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
           | |
           g₃ f₄
           ∨ ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
| |
g₁ f₂
∨ ∨
X₁ - f₁ -> Y₁
```

where the two squares are pullbacks.

We can then construct the pullback squares

```
W - l₂ -> Z₂ - g₄ -> X₃
| |
l₁ f₄
∨ ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
```

and

```
W' - l₂' -> Z₂
| |
l₁' g₃
∨ ∨
Z₁ X₂
| |
g₁ f₂
∨ ∨
X₁ - f₁ -> Y₁
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
/--
Definition of `pullbackPullbackLeftIsPullback` / `pullbackPullbackLeftIsPullback` 的定义

English:
definition pullbackPullbackLeftIsPullback
  signature: [HasPullback (g₂ ≫ f₃) f₄]
  body: by
  apply leftSquareIsPullback _ rfl (pullbackIsPullback f₃ f₄)
  simpa [PullbackCone.pasteHoriz] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ f₄)

中文:
定义 pullbackPullbackLeftIsPullback
  签名: [HasPullback (g₂ ≫ f₃) f₄]
  定义体: by
  apply leftSquareIsPullback _ rfl (pullbackIsPullback f₃ f₄)
  simpa [PullbackCone.pasteHoriz] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ f₄)

Depends on / 依赖: PullbackCone, PullbackCone.mkSelfIsLimit, PullbackCone.pasteHoriz, leftSquareIsPullback, mkSelfIsLimit, pasteHoriz, pullbackIsPullback
-/
def pullbackPullbackLeftIsPullback [HasPullback (g₂ ≫ f₃) f₄] : IsLimit (PullbackCone.mk l₁ l₂
    (show l₁ ≫ g₂ = l₂ ≫ g₃ from (pullback.lift_fst _ _ _).symm)) := by
  apply leftSquareIsPullback _ rfl (pullbackIsPullback f₃ f₄)
  simpa [PullbackCone.pasteHoriz] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ f₄)

/--
Definition of `pullbackAssocIsPullback` / `pullbackAssocIsPullback` 的定义

English:
definition pullbackAssocIsPullback
  signature: [HasPullback (g₂ ≫ f₃) f₄]
  body: by
  simpa using! pasteVertIsPullback rfl (pullbackIsPullback _ _)
    (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄)

中文:
定义 pullbackAssocIsPullback
  签名: [HasPullback (g₂ ≫ f₃) f₄]
  定义体: by
  simpa using! pasteVertIsPullback rfl (pullbackIsPullback _ _)
    (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄)

Depends on / 依赖: pasteVertIsPullback, pullbackIsPullback, pullbackPullbackLeftIsPullback
-/
def pullbackAssocIsPullback [HasPullback (g₂ ≫ f₃) f₄] :
    IsLimit
      (PullbackCone.mk (l₁ ≫ g₁) l₂
        (show (l₁ ≫ g₁) ≫ f₁ = l₂ ≫ g₃ ≫ f₂ by
          rw [pullback.lift_fst_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [pullback.condition])) := by
  simpa using! pasteVertIsPullback rfl (pullbackIsPullback _ _)
    (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄)

/--
theorem `hasPullback_assoc` / 定理 `hasPullback_assoc`

English:
theorem hasPullback_assoc
  given: [HasPullback (g₂ ≫ f₃) f₄]
  statement: HasPullback f₁ (g₃ ≫ f₂)
  proof: ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

中文:
定理 hasPullback_assoc
  条件: [HasPullback (g₂ ≫ f₃) f₄]
  结论: HasPullback f₁ (g₃ ≫ f₂)
  证明: ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

Depends on / 依赖: pullbackAssocIsPullback
-/
theorem hasPullback_assoc [HasPullback (g₂ ≫ f₃) f₄] : HasPullback f₁ (g₃ ≫ f₂) :=
  ⟨⟨⟨_, pullbackAssocIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pullbackPullbackRightIsPullback` / `pullbackPullbackRightIsPullback` 的定义

English:
definition pullbackPullbackRightIsPullback
  signature: [HasPullback f₁ (g₃ ≫ f₂)]
  body: by
  apply topSquareIsPullback _ rfl (pullbackIsPullback f₁ f₂)
  simpa [PullbackCone.pasteVert] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ _)

中文:
定义 pullbackPullbackRightIsPullback
  签名: [HasPullback f₁ (g₃ ≫ f₂)]
  定义体: by
  apply topSquareIsPullback _ rfl (pullbackIsPullback f₁ f₂)
  simpa [PullbackCone.pasteVert] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ _)

Depends on / 依赖: PullbackCone, PullbackCone.mkSelfIsLimit, PullbackCone.pasteVert, mkSelfIsLimit, pasteVert, pullbackIsPullback, topSquareIsPullback
-/
def pullbackPullbackRightIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit (PullbackCone.mk l₁' l₂' (show l₁' ≫ g₂ = l₂' ≫ g₃ from pullback.lift_snd _ _ _)) := by
  apply topSquareIsPullback _ rfl (pullbackIsPullback f₁ f₂)
  simpa [PullbackCone.pasteVert] using PullbackCone.mkSelfIsLimit (pullbackIsPullback _ _)

/--
Definition of `pullbackAssocSymmIsPullback` / `pullbackAssocSymmIsPullback` 的定义

English:
definition pullbackAssocSymmIsPullback
  signature: [HasPullback f₁ (g₃ ≫ f₂)]
  body: by
  simpa [PullbackCone.pasteHoriz] using! pasteHorizIsPullback rfl
    (pullbackIsPullback f₃ f₄) (pullbackPullbackRightIsPullback _ _ _ _)

中文:
定义 pullbackAssocSymmIsPullback
  签名: [HasPullback f₁ (g₃ ≫ f₂)]
  定义体: by
  simpa [PullbackCone.pasteHoriz] using! pasteHorizIsPullback rfl
    (pullbackIsPullback f₃ f₄) (pullbackPullbackRightIsPullback _ _ _ _)

Depends on / 依赖: PullbackCone, PullbackCone.pasteHoriz, pasteHoriz, pasteHorizIsPullback, pullbackIsPullback, pullbackPullbackRightIsPullback
-/
def pullbackAssocSymmIsPullback [HasPullback f₁ (g₃ ≫ f₂)] :
    IsLimit
      (PullbackCone.mk l₁' (l₂' ≫ g₄)
        (show l₁' ≫ g₂ ≫ f₃ = (l₂' ≫ g₄) ≫ f₄ by
          rw [pullback.lift_snd_assoc]; rw [Category.assoc]; rw [Category.assoc]; rw [pullback.condition])) := by
  simpa [PullbackCone.pasteHoriz] using! pasteHorizIsPullback rfl
    (pullbackIsPullback f₃ f₄) (pullbackPullbackRightIsPullback _ _ _ _)

/--
theorem `hasPullback_assoc_symm` / 定理 `hasPullback_assoc_symm`

English:
theorem hasPullback_assoc_symm
  given: [HasPullback f₁ (g₃ ≫ f₂)]
  statement: HasPullback (g₂ ≫ f₃) f₄
  proof: ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

中文:
定理 hasPullback_assoc_symm
  条件: [HasPullback f₁ (g₃ ≫ f₂)]
  结论: HasPullback (g₂ ≫ f₃) f₄
  证明: ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

Depends on / 依赖: pullbackAssocSymmIsPullback
-/
theorem hasPullback_assoc_symm [HasPullback f₁ (g₃ ≫ f₂)] : HasPullback (g₂ ≫ f₃) f₄ :=
  ⟨⟨⟨_, pullbackAssocSymmIsPullback f₁ f₂ f₃ f₄⟩⟩⟩

/--
Definition of `pullbackAssoc` / `pullbackAssoc` 的定义

English:
definition pullbackAssoc
  signature: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  body: (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)

@[reassoc (attr := simp)]

中文:
定义 pullbackAssoc
  签名: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  定义体: (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)

@[reassoc (attr := simp)]

Depends on / 依赖: conePointUniqueUpToIso, pullbackPullbackLeftIsPullback, pullbackPullbackRightIsPullback
-/
noncomputable def pullbackAssoc [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    pullback (pullback.snd _ _ ≫ f₃ : pullback f₁ f₂ ⟶ _) f₄ ≅
      pullback f₁ (pullback.fst _ _ ≫ f₂ : pullback f₃ f₄ ⟶ _) :=
  (pullbackPullbackLeftIsPullback f₁ f₂ f₃ f₄).conePointUniqueUpToIso
    (pullbackPullbackRightIsPullback f₁ f₂ f₃ f₄)

@[reassoc (attr := simp)]
/--
theorem `pullbackAssoc_inv_fst_fst` / 定理 `pullbackAssoc_inv_fst_fst`

English:
theorem pullbackAssoc_inv_fst_fst
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by
  trans l₁' ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
定理 pullbackAssoc_inv_fst_fst
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by
  trans l₁' ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingCospan.left
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingCospan, WalkingCospan.left, conePointUniqueUpToIso_inv_comp, lift_fst, pullback, pullback.fst, pullback.lift_fst
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
/--
theorem `pullbackAssoc_hom_fst` / 定理 `pullbackAssoc_hom_fst`

English:
theorem pullbackAssoc_hom_fst
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by
  rw [← Iso.eq_inv_comp]; rw [pullbackAssoc_inv_fst_fst]

@[reassoc (attr := simp)]

中文:
定理 pullbackAssoc_hom_fst
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by
  rw [← Iso.eq_inv_comp]; rw [pullbackAssoc_inv_fst_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.eq_inv_comp, eq_inv_comp, pullbackAssoc_inv_fst_fst
-/
theorem pullbackAssoc_hom_fst [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).hom ≫ pullback.fst _ _ = pullback.fst _ _ ≫ pullback.fst _ _ := by
  rw [← Iso.eq_inv_comp]; rw [pullbackAssoc_inv_fst_fst]

@[reassoc (attr := simp)]
/--
theorem `pullbackAssoc_hom_snd_fst` / 定理 `pullbackAssoc_hom_snd_fst`

English:
theorem pullbackAssoc_hom_snd_fst
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by
  trans l₂ ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

中文:
定理 pullbackAssoc_hom_snd_fst
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by
  trans l₂ ≫ pullback.fst _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_hom_comp, f.toCommaMorphism, lift_fst, pullback, pullback.fst, pullback.lift_fst, toCommaMorphism
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
/--
theorem `pullbackAssoc_hom_snd_snd` / 定理 `pullbackAssoc_hom_snd_snd`

English:
theorem pullbackAssoc_hom_snd_snd
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by
  trans l₂ ≫ pullback.snd _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]

中文:
定理 pullbackAssoc_hom_snd_snd
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by
  trans l₂ ≫ pullback.snd _ _
  · rw [← Category.assoc]
    congr 1
    exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingCospan.right
  · exact pullback.lift_snd _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, WalkingCospan, WalkingCospan.right, conePointUniqueUpToIso_hom_comp, lift_snd, pullback, pullback.lift_snd, pullback.snd
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
/--
theorem `pullbackAssoc_inv_fst_snd` / 定理 `pullbackAssoc_inv_fst_snd`

English:
theorem pullbackAssoc_inv_fst_snd
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]

@[reassoc (attr := simp)]

中文:
定理 pullbackAssoc_inv_fst_snd
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, pullbackAssoc_hom_snd_fst
-/
theorem pullbackAssoc_inv_fst_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
    pullback.snd _ _ ≫ pullback.fst _ _ := by rw [Iso.inv_comp_eq, pullbackAssoc_hom_snd_fst]

@[reassoc (attr := simp)]
/--
theorem `pullbackAssoc_inv_snd` / 定理 `pullbackAssoc_inv_snd`

English:
theorem pullbackAssoc_inv_snd
  statement: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  proof: by
  rw [Iso.inv_comp_eq]; rw [pullbackAssoc_hom_snd_snd]

中文:
定理 pullbackAssoc_inv_snd
  结论: [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
  证明: by
  rw [Iso.inv_comp_eq]; rw [pullbackAssoc_hom_snd_snd]

Depends on / 依赖: Iso.inv_comp_eq, inv_comp_eq, pullbackAssoc_hom_snd_snd
-/
theorem pullbackAssoc_inv_snd [HasPullback ((pullback.snd _ _ : Z₁ ⟶ X₂) ≫ f₃) f₄]
    [HasPullback f₁ ((pullback.fst _ _ : Z₂ ⟶ X₂) ≫ f₂)] :
    (pullbackAssoc f₁ f₂ f₃ f₄).inv ≫ pullback.snd _ _ = pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [Iso.inv_comp_eq]; rw [pullbackAssoc_hom_snd_snd]

end PullbackAssoc

section PushoutAssoc

/-
The objects and morphisms are as follows:

```
           Z₂ - g₄ -> X₃
           | |
           g₃ f₄
           ∨ ∨
Z₁ - g₂ -> X₂ - f₃ -> Y₂
| |
g₁ f₂
∨ ∨
X₁ - f₁ -> Y₁
```

where the two squares are pushouts.

We can then construct the pushout squares

```
Z₁ - g₂ -> X₂ - f₃ -> Y₂
| |
g₁ l₂
∨ ∨
X₁ - f₁ -> Y₁ - l₁ -> W

and

Z₂ - g₄ -> X₃
| |
g₃ f₄
∨ ∨
X₂ Y₂
| |
f₂ l₂'
∨ ∨
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
/--
Definition of `pushoutPushoutLeftIsPushout` / `pushoutPushoutLeftIsPushout` 的定义

English:
definition pushoutPushoutLeftIsPushout
  signature: [HasPushout (g₃ ≫ f₂) g₄]
  body: by
  apply botSquareIsPushout _ rfl (pushoutIsPushout _ g₄)
  simpa [PushoutCocone.pasteVert] using
    PushoutCocone.mkSelfIsColimit (pushoutIsPushout (g₃ ≫ f₂) g₄)

中文:
定义 pushoutPushoutLeftIsPushout
  签名: [HasPushout (g₃ ≫ f₂) g₄]
  定义体: by
  apply botSquareIsPushout _ rfl (pushoutIsPushout _ g₄)
  simpa [PushoutCocone.pasteVert] using
    PushoutCocone.mkSelfIsColimit (pushoutIsPushout (g₃ ≫ f₂) g₄)

Depends on / 依赖: PushoutCocone, PushoutCocone.mkSelfIsColimit, PushoutCocone.pasteVert, botSquareIsPushout, f.hom, mkSelfIsColimit, pasteVert, pushoutIsPushout
-/
def pushoutPushoutLeftIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk l₁' l₂' (show f₂ ≫ l₁' = f₃ ≫ l₂' from (pushout.inl_desc _ _ _).symm)) := by
  apply botSquareIsPushout _ rfl (pushoutIsPushout _ g₄)
  simpa [PushoutCocone.pasteVert] using
    PushoutCocone.mkSelfIsColimit (pushoutIsPushout (g₃ ≫ f₂) g₄)

/--
Definition of `pushoutAssocIsPushout` / `pushoutAssocIsPushout` 的定义

English:
definition pushoutAssocIsPushout
  signature: [HasPushout (g₃ ≫ f₂) g₄]
  body: by
  simpa using! pasteHorizIsPushout rfl (pushoutIsPushout g₁ g₂)
    (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄)

中文:
定义 pushoutAssocIsPushout
  签名: [HasPushout (g₃ ≫ f₂) g₄]
  定义体: by
  simpa using! pasteHorizIsPushout rfl (pushoutIsPushout g₁ g₂)
    (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄)

Depends on / 依赖: pasteHorizIsPushout, pushoutIsPushout, pushoutPushoutLeftIsPushout
-/
def pushoutAssocIsPushout [HasPushout (g₃ ≫ f₂) g₄] :
    IsColimit
      (PushoutCocone.mk (f₁ ≫ l₁') l₂'
        (show g₁ ≫ f₁ ≫ l₁' = (g₂ ≫ f₃) ≫ l₂' by
          rw [Category.assoc]; rw [pushout.inl_desc]; rw [pushout.condition_assoc])) := by
  simpa using! pasteHorizIsPushout rfl (pushoutIsPushout g₁ g₂)
    (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄)

/--
theorem `hasPushout_assoc` / 定理 `hasPushout_assoc`

English:
theorem hasPushout_assoc
  given: [HasPushout (g₃ ≫ f₂) g₄]
  statement: HasPushout g₁ (g₂ ≫ f₃)
  proof: ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

中文:
定理 hasPushout_assoc
  条件: [HasPushout (g₃ ≫ f₂) g₄]
  结论: HasPushout g₁ (g₂ ≫ f₃)
  证明: ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

Depends on / 依赖: f.left, g.left, pushoutAssocIsPushout
-/
theorem hasPushout_assoc [HasPushout (g₃ ≫ f₂) g₄] : HasPushout g₁ (g₂ ≫ f₃) :=
  ⟨⟨⟨_, pushoutAssocIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `pushoutPushoutRightIsPushout` / `pushoutPushoutRightIsPushout` 的定义

English:
definition pushoutPushoutRightIsPushout
  signature: [HasPushout g₁ (g₂ ≫ f₃)]
  body: by
  apply rightSquareIsPushout _ rfl (pushoutIsPushout _ _)
  simpa [PushoutCocone.pasteHoriz] using PushoutCocone.mkSelfIsColimit (pushoutIsPushout _ _)

中文:
定义 pushoutPushoutRightIsPushout
  签名: [HasPushout g₁ (g₂ ≫ f₃)]
  定义体: by
  apply rightSquareIsPushout _ rfl (pushoutIsPushout _ _)
  simpa [PushoutCocone.pasteHoriz] using PushoutCocone.mkSelfIsColimit (pushoutIsPushout _ _)

Depends on / 依赖: PushoutCocone, PushoutCocone.mkSelfIsColimit, PushoutCocone.pasteHoriz, mkSelfIsColimit, pasteHoriz, pushoutIsPushout, rightSquareIsPushout
-/
def pushoutPushoutRightIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit (PushoutCocone.mk l₁ l₂ (show f₂ ≫ l₁ = f₃ ≫ l₂ from pushout.inr_desc _ _ _)) := by
  apply rightSquareIsPushout _ rfl (pushoutIsPushout _ _)
  simpa [PushoutCocone.pasteHoriz] using PushoutCocone.mkSelfIsColimit (pushoutIsPushout _ _)

/--
Definition of `pushoutAssocSymmIsPushout` / `pushoutAssocSymmIsPushout` 的定义

English:
definition pushoutAssocSymmIsPushout
  signature: [HasPushout g₁ (g₂ ≫ f₃)]
  body: by
  simpa using! pasteVertIsPushout rfl (pushoutIsPushout _ _) (pushoutPushoutRightIsPushout _ _ _ _)

中文:
定义 pushoutAssocSymmIsPushout
  签名: [HasPushout g₁ (g₂ ≫ f₃)]
  定义体: by
  simpa using! pasteVertIsPushout rfl (pushoutIsPushout _ _) (pushoutPushoutRightIsPushout _ _ _ _)

Depends on / 依赖: pasteVertIsPushout, pushoutIsPushout, pushoutPushoutRightIsPushout
-/
def pushoutAssocSymmIsPushout [HasPushout g₁ (g₂ ≫ f₃)] :
    IsColimit
      (PushoutCocone.mk l₁ (f₄ ≫ l₂)
        (show (g₃ ≫ f₂) ≫ l₁ = g₄ ≫ f₄ ≫ l₂ by
          rw [Category.assoc]; rw [pushout.inr_desc]; rw [pushout.condition_assoc])) := by
  simpa using! pasteVertIsPushout rfl (pushoutIsPushout _ _) (pushoutPushoutRightIsPushout _ _ _ _)

/--
theorem `hasPushout_assoc_symm` / 定理 `hasPushout_assoc_symm`

English:
theorem hasPushout_assoc_symm
  given: [HasPushout g₁ (g₂ ≫ f₃)]
  statement: HasPushout (g₃ ≫ f₂) g₄
  proof: ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

中文:
定理 hasPushout_assoc_symm
  条件: [HasPushout g₁ (g₂ ≫ f₃)]
  结论: HasPushout (g₃ ≫ f₂) g₄
  证明: ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

Depends on / 依赖: Comma.Hom.ext, pushoutAssocSymmIsPushout
-/
theorem hasPushout_assoc_symm [HasPushout g₁ (g₂ ≫ f₃)] : HasPushout (g₃ ≫ f₂) g₄ :=
  ⟨⟨⟨_, pushoutAssocSymmIsPushout g₁ g₂ g₃ g₄⟩⟩⟩

/--
Definition of `pushoutAssoc` / `pushoutAssoc` 的定义

English:
definition pushoutAssoc
  signature: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  body: (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)

@[reassoc (attr := simp)]

中文:
定义 pushoutAssoc
  签名: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  定义体: (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)

@[reassoc (attr := simp)]

Depends on / 依赖: coconePointUniqueUpToIso, pushoutPushoutLeftIsPushout, pushoutPushoutRightIsPushout
-/
noncomputable def pushoutAssoc [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout (g₃ ≫ pushout.inr _ _ : _ ⟶ pushout g₁ g₂) g₄ ≅
      pushout g₁ (g₂ ≫ pushout.inl _ _ : _ ⟶ pushout g₃ g₄) :=
  (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).coconePointUniqueUpToIso
    (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄)

@[reassoc (attr := simp)]
/--
theorem `inl_inl_pushoutAssoc_hom` / 定理 `inl_inl_pushoutAssoc_hom`

English:
theorem inl_inl_pushoutAssoc_hom
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  trans f₁ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 inl_inl_pushoutAssoc_hom
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  trans f₁ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inl_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: WalkingCospan, WalkingCospan.left, comp_coconePointUniqueUpToIso_hom, inl_desc, pushout, pushout.inl_desc, pushoutPushoutLeftIsPushout
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
/--
theorem `inr_inl_pushoutAssoc_hom` / 定理 `inr_inl_pushoutAssoc_hom`

English:
theorem inr_inl_pushoutAssoc_hom
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  trans f₂ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 inr_inl_pushoutAssoc_hom
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  trans f₂ ≫ l₁
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_hom _
        WalkingCospan.left
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: WalkingCospan, WalkingCospan.left, comp_coconePointUniqueUpToIso_hom, inr_desc, pushout, pushout.inr_desc, pushoutPushoutLeftIsPushout
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
/--
theorem `inr_inr_pushoutAssoc_inv` / 定理 `inr_inr_pushoutAssoc_inv`

English:
theorem inr_inr_pushoutAssoc_inv
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄) WalkingCospan.right
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]

中文:
定理 inr_inr_pushoutAssoc_inv
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  trans f₄ ≫ l₂'
  · congr 1
    exact
      (pushoutPushoutLeftIsPushout g₁ g₂ g₃ g₄).comp_coconePointUniqueUpToIso_inv
        (pushoutPushoutRightIsPushout g₁ g₂ g₃ g₄) WalkingCospan.right
  · exact pushout.inr_desc _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: WalkingCospan, WalkingCospan.right, comp_coconePointUniqueUpToIso_inv, inr_desc, pushout, pushout.inr_desc, pushoutPushoutLeftIsPushout, pushoutPushoutRightIsPushout
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
/--
theorem `inl_pushoutAssoc_inv` / 定理 `inl_pushoutAssoc_inv`

English:
theorem inl_pushoutAssoc_inv
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inl_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]

中文:
定理 inl_pushoutAssoc_inv
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inl_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, inl_inl_pushoutAssoc_hom
-/
theorem inl_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inl _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv = pushout.inl _ _ ≫ pushout.inl _ _ := by
  rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inl_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]
/--
theorem `inl_inr_pushoutAssoc_inv` / 定理 `inl_inr_pushoutAssoc_inv`

English:
theorem inl_inr_pushoutAssoc_inv
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inr_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]

中文:
定理 inl_inr_pushoutAssoc_inv
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inr_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]

Depends on / 依赖: Category, Category.assoc, Iso.comp_inv_eq, comp_inv_eq, inr_inl_pushoutAssoc_hom
-/
theorem inl_inr_pushoutAssoc_inv [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inl _ _ ≫ pushout.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).inv =
      pushout.inr _ _ ≫ pushout.inl _ _ := by
  rw [← Category.assoc]; rw [Iso.comp_inv_eq]; rw [Category.assoc]; rw [inr_inl_pushoutAssoc_hom]

@[reassoc (attr := simp)]
/--
theorem `inr_pushoutAssoc_hom` / 定理 `inr_pushoutAssoc_hom`

English:
theorem inr_pushoutAssoc_hom
  statement: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  proof: by
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [inr_inr_pushoutAssoc_inv]

中文:
定理 inr_pushoutAssoc_hom
  结论: [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
  证明: by
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [inr_inr_pushoutAssoc_inv]

Depends on / 依赖: Category, Category.assoc, Iso.eq_comp_inv, eq_comp_inv, inr_inr_pushoutAssoc_inv
-/
theorem inr_pushoutAssoc_hom [HasPushout (g₃ ≫ (pushout.inr _ _ : X₂ ⟶ Y₁)) g₄]
    [HasPushout g₁ (g₂ ≫ (pushout.inl _ _ : X₂ ⟶ Y₂))] :
    pushout.inr _ _ ≫ (pushoutAssoc g₁ g₂ g₃ g₄).hom = pushout.inr _ _ ≫ pushout.inr _ _ := by
  rw [← Iso.eq_comp_inv]; rw [Category.assoc]; rw [inr_inr_pushoutAssoc_inv]

end PushoutAssoc

end CategoryTheory.Limits
