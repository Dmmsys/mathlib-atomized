/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.Limits.HasLimits

/-!
# Limits in the category of indexed families of objects.

Given a functor `F : J ⥤ Π i, C i` into a category of indexed families,
1. we can assemble a collection of cones over `F ⋙ Pi.eval C i` into a cone over `F`
2. if all those cones are limit cones, the assembled cone is a limit cone, and
3. if we have limits for each of `F ⋙ Pi.eval C i`, we can produce a
   `HasLimit F` instance
-/

@[expose] public section


open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory.pi

universe v₁ v₂ u₁ u₂

variable {I : Type v₁} {C : I -> Type u₁} [forall i, Category.{v₁} (C i)]
variable {J : Type v₁} [SmallCategory J]
variable {F : J ⥤ forall i, C i}

/--
Definition of `coneCompEval` / `coneCompEval` 的定义

English:
definition coneCompEval
  signature: (c : Cone F) (i : I)
  body: c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

中文:
定义 coneCompEval
  签名: (c : Cone F) (i : I)
  定义体: c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

Depends on / 依赖: c.pt
-/
def coneCompEval (c : Cone F) (i : I) : Cone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  π :=
    { app := fun j => c.π.app j i
      naturality := fun _ _ f => congr_fun (c.π.naturality f) i }

/--
Definition of `coconeCompEval` / `coconeCompEval` 的定义

English:
definition coconeCompEval
  signature: (c : Cocone F) (i : I)
  body: c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

中文:
定义 coconeCompEval
  签名: (c : Cocone F) (i : I)
  定义体: c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

Depends on / 依赖: c.pt
-/
def coconeCompEval (c : Cocone F) (i : I) : Cocone (F ⋙ Pi.eval C i) where
  pt := c.pt i
  ι :=
    { app := fun j => c.ι.app j i
      naturality := fun _ _ f => congr_fun (c.ι.naturality f) i }

/--
Definition of `coneOfConeCompEval` / `coneOfConeCompEval` 的定义

English:
definition coneOfConeCompEval
  signature: (c : forall i, Cone (F ⋙ Pi.eval C i))
  body: (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).π.naturality f }

中文:
定义 coneOfConeCompEval
  签名: (c : 对任意 i, Cone (F ⋙ Pi.eval C i))
  定义体: (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).π.naturality f }
-/
def coneOfConeCompEval (c : forall i, Cone (F ⋙ Pi.eval C i)) : Cone F where
  pt i := (c i).pt
  π :=
    { app := fun j i => (c i).π.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).π.naturality f }

/--
Definition of `coconeOfCoconeCompEval` / `coconeOfCoconeCompEval` 的定义

English:
definition coconeOfCoconeCompEval
  signature: (c : forall i, Cocone (F ⋙ Pi.eval C i))
  body: (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).ι.naturality f }

中文:
定义 coconeOfCoconeCompEval
  签名: (c : 对任意 i, Cocone (F ⋙ Pi.eval C i))
  定义体: (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).ι.naturality f }
-/
def coconeOfCoconeCompEval (c : forall i, Cocone (F ⋙ Pi.eval C i)) : Cocone F where
  pt i := (c i).pt
  ι :=
    { app := fun j i => (c i).ι.app j
      naturality := fun j j' f => by
        funext i
        exact (c i).ι.naturality f }

/--
Definition of `coneOfConeEvalIsLimit` / `coneOfConeEvalIsLimit` 的定义

English:
definition coneOfConeEvalIsLimit
  signature: {c : forall i, Cone (F ⋙ Pi.eval C i)} (P : forall i, IsLimit (c i))
  body: (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

中文:
定义 coneOfConeEvalIsLimit
  签名: {c : 对任意 i, Cone (F ⋙ Pi.eval C i)} (P : 对任意 i, IsLimit (c i))
  定义体: (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

Depends on / 依赖: coneCompEval
-/
def coneOfConeEvalIsLimit {c : forall i, Cone (F ⋙ Pi.eval C i)} (P : forall i, IsLimit (c i)) :
    IsLimit (coneOfConeCompEval c) where
  lift s i := (P i).lift (coneCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coneCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coneCompEval s i) (m i) fun j => congr_fun (w j) i

/--
Definition of `coconeOfCoconeEvalIsColimit` / `coconeOfCoconeEvalIsColimit` 的定义

English:
definition coconeOfCoconeEvalIsColimit
  signature: {c : forall i, Cocone (F ⋙ Pi.eval C i)} (P : forall i, IsColimit (c i))
  body: (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

中文:
定义 coconeOfCoconeEvalIsColimit
  签名: {c : 对任意 i, Cocone (F ⋙ Pi.eval C i)} (P : 对任意 i, IsColimit (c i))
  定义体: (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

Depends on / 依赖: coconeCompEval
-/
def coconeOfCoconeEvalIsColimit {c : forall i, Cocone (F ⋙ Pi.eval C i)} (P : forall i, IsColimit (c i)) :
    IsColimit (coconeOfCoconeCompEval c) where
  desc s i := (P i).desc (coconeCompEval s i)
  fac s j := by
    funext i
    exact (P i).fac (coconeCompEval s i) j
  uniq s m w := by
    funext i
    exact (P i).uniq (coconeCompEval s i) (m i) fun j => congr_fun (w j) i

section

variable [forall i, HasLimit (F ⋙ Pi.eval C i)]

/--
theorem `hasLimit_of_hasLimit_comp_eval` / 定理 `hasLimit_of_hasLimit_comp_eval`

English:
theorem hasLimit_of_hasLimit_comp_eval
  statement: HasLimit F
  proof: HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }

中文:
定理 hasLimit_of_hasLimit_comp_eval
  结论: HasLimit F
  证明: HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }

Depends on / 依赖: HasLimit, HasLimit.mk, coneOfConeCompEval, coneOfConeEvalIsLimit, isLimit, limit.cone, limit.isLimit
-/
theorem hasLimit_of_hasLimit_comp_eval : HasLimit F :=
  HasLimit.mk
    { cone := coneOfConeCompEval fun _ => limit.cone _
      isLimit := coneOfConeEvalIsLimit fun _ => limit.isLimit _ }

end

section

variable [forall i, HasColimit (F ⋙ Pi.eval C i)]

/--
theorem `hasColimit_of_hasColimit_comp_eval` / 定理 `hasColimit_of_hasColimit_comp_eval`

English:
theorem hasColimit_of_hasColimit_comp_eval
  statement: HasColimit F
  proof: HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }

中文:
定理 hasColimit_of_hasColimit_comp_eval
  结论: HasColimit F
  证明: HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }

Depends on / 依赖: HasColimit, HasColimit.mk, cocone, coconeOfCoconeCompEval, coconeOfCoconeEvalIsColimit, colimit, colimit.cocone, colimit.isColimit, isColimit
-/
theorem hasColimit_of_hasColimit_comp_eval : HasColimit F :=
  HasColimit.mk
    { cocone := coconeOfCoconeCompEval fun _ => colimit.cocone _
      isColimit := coconeOfCoconeEvalIsColimit fun _ => colimit.isColimit _ }

end

/-!
As an example, we can use this to construct particular shapes of limits
in a category of indexed families.

With the addition of
`import CategoryTheory.Limits.Types.Products`
we can use:
```
attribute [local instance] hasLimit_of_hasLimit_comp_eval
example : hasBinaryProducts (I → Type v₁) := ⟨by infer_instance⟩
```
-/


end CategoryTheory.pi
