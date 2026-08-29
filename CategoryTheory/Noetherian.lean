/-
Copyright (c) 2022 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.CategoryTheory.Subobject.ArtinianObject
public import Mathlib.CategoryTheory.Subobject.NoetherianObject

/-!
# Artinian and Noetherian categories

An Artinian category is a category in which objects do not
have infinite decreasing sequences of subobjects.

A Noetherian category is a category in which objects do not
have infinite increasing sequences of subobjects.

Note: In the file, `Mathlib/CategoryTheory/Subobject/ArtinianObject.lean`,
it is shown that any nonzero Artinian object has a simple subobject.

## Future work
The Jordan-Hölder theorem, following https://stacks.math.columbia.edu/tag/0FCK.
-/

public section


namespace CategoryTheory

open CategoryTheory.Limits

variable (C : Type*) [Category* C]

/--
Definition of `Noetherian` / `Noetherian` 的定义

English:
class Noetherian
  parameters: : Prop extends EssentiallySmall C where
  extends: EssentiallySmall C
  axioms and operations (1):
    - isNoetherianObject : forall X : C, IsNoetherianObject X

中文:
类 Noetherian
  参数: : 命题 extends EssentiallySmall C where
  继承: EssentiallySmall C
  公理与运算 (1 个):
    - isNoetherianObject : 对任意 X : C, IsNoetherianObject X
-/
class Noetherian : Prop extends EssentiallySmall C where
  isNoetherianObject : forall X : C, IsNoetherianObject X

attribute [instance] Noetherian.isNoetherianObject

/--
Definition of `Artinian` / `Artinian` 的定义

English:
class Artinian
  parameters: : Prop extends EssentiallySmall C where
  extends: EssentiallySmall C
  axioms and operations (1):
    - isArtinianObject : forall X : C, IsArtinianObject X

中文:
类 Artinian
  参数: : 命题 extends EssentiallySmall C where
  继承: EssentiallySmall C
  公理与运算 (1 个):
    - isArtinianObject : 对任意 X : C, IsArtinianObject X
-/
class Artinian : Prop extends EssentiallySmall C where
  isArtinianObject : forall X : C, IsArtinianObject X

attribute [instance] Artinian.isArtinianObject

end CategoryTheory
