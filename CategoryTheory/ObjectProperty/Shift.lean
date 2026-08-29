/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Properties of objects on categories equipped with shift

Given a predicate `P : ObjectProperty C` on objects of a category equipped with a shift
by `A`, we define shifted properties of objects `P.shift a` for all `a : A`.
We also introduce a typeclass `P.IsStableUnderShift A` to say that `P X`
implies `P (X⟦a⟧)` for all `a : A`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory

variable {C : Type*} [Category* C] (P Q : ObjectProperty C)
  {A : Type*} [AddMonoid A] [HasShift C A]
  {E : Type*} [Category* E] [HasShift E A]

namespace ObjectProperty

/--
Definition of `shift` / `shift` 的定义

English:
definition shift
  signature: (a : A)
  body: fun X => P (X⟦a⟧)

中文:
定义 shift
  签名: (a : A)
  定义体: fun X => P (X⟦a⟧)
-/
def shift (a : A) : ObjectProperty C := fun X => P (X⟦a⟧)

/--
lemma `prop_shift_iff` / 引理 `prop_shift_iff`

English:
lemma prop_shift_iff
  given: (a : A) (X : C)
  statement: P.shift a X ↔ P (X⟦a⟧)
  proof: Iff.rfl

中文:
引理 prop_shift_iff
  条件: (a : A) (X : C)
  结论: P.shift a X ↔ P (X⟦a⟧)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma prop_shift_iff (a : A) (X : C) : P.shift a X ↔ P (X⟦a⟧) := Iff.rfl

instance (a : A) [P.IsClosedUnderIsomorphisms] :
    (P.shift a).IsClosedUnderIsomorphisms where
  of_iso e hX := P.prop_of_iso ((shiftFunctor C a).mapIso e) hX

variable (A)

@[simp]
/--
lemma `shift_zero` / 引理 `shift_zero`

English:
lemma shift_zero
  given: [P.IsClosedUnderIsomorphisms]
  statement: P.shift (0 : A) = P
  proof: by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

中文:
引理 shift_zero
  条件: [P.IsClosedUnderIsomorphisms]
  结论: P.shift (0 : A) = P
  证明: by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

Depends on / 依赖: P.prop_iff_of_iso, prop_iff_of_iso, shiftFunctorZero
-/
lemma shift_zero [P.IsClosedUnderIsomorphisms] : P.shift (0 : A) = P := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorZero C A).app X)

variable {A}

/--
lemma `shift_shift` / 引理 `shift_shift`

English:
lemma shift_shift
  given: (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms]
  proof: by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)

中文:
引理 shift_shift
  条件: (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms]
  证明: by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)

Depends on / 依赖: P.prop_iff_of_iso, prop_iff_of_iso, shiftFunctorAdd, symm.app
-/
lemma shift_shift (a b c : A) (h : a + b = c) [P.IsClosedUnderIsomorphisms] :
    (P.shift b).shift a = P.shift c := by
  ext X
  exact P.prop_iff_of_iso ((shiftFunctorAdd' C a b c h).symm.app X)

/--
lemma `shift_sup` / 引理 `shift_sup`

English:
lemma shift_sup
  given: (a : A)
  statement: (P ⊔ Q).shift a = P.shift a ⊔ Q.shift a
  proof: by
  ext
  simp [prop_shift_iff]

中文:
引理 shift_sup
  条件: (a : A)
  结论: (P ⊔ Q).shift a = P.shift a ⊔ Q.shift a
  证明: by
  ext
  simp [prop_shift_iff]

Depends on / 依赖: prop_shift_iff
-/
lemma shift_sup (a : A) : (P ⊔ Q).shift a = P.shift a ⊔ Q.shift a := by
  ext
  simp [prop_shift_iff]

/--
lemma `shift_iSup` / 引理 `shift_iSup`

English:
lemma shift_iSup
  given: {ι : Sort*} (P : ι -> ObjectProperty C) (a : A)
  proof: by
  ext
  simp [prop_shift_iff]

中文:
引理 shift_iSup
  条件: {ι : Sort*} (P : ι -> Object命题erty C) (a : A)
  证明: by
  ext
  simp [prop_shift_iff]

Depends on / 依赖: prop_shift_iff
-/
lemma shift_iSup {ι : Sort*} (P : ι -> ObjectProperty C) (a : A) :
    (⨆ (i : ι), P i).shift a = ⨆ (i : ι), (P i).shift a := by
  ext
  simp [prop_shift_iff]

/--
Definition of `IsStableUnderShiftBy` / `IsStableUnderShiftBy` 的定义

English:
class IsStableUnderShiftBy
  parameters: (a : A)
  axioms and operations (1):
    - le_shift : P <= P.shift a

中文:
类 IsStableUnderShiftBy
  参数: (a : A)
  公理与运算 (1 个):
    - le_shift : P <= P.shift a
-/
class IsStableUnderShiftBy (a : A) : Prop where
  le_shift : P <= P.shift a

/--
lemma `le_shift` / 引理 `le_shift`

English:
lemma le_shift
  given: (a : A) [P.IsStableUnderShiftBy a]
  proof: IsStableUnderShiftBy.le_shift

中文:
引理 le_shift
  条件: (a : A) [P.IsStableUnderShiftBy a]
  证明: IsStableUnderShiftBy.le_shift

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.le_shift, le_shift
-/
lemma le_shift (a : A) [P.IsStableUnderShiftBy a] :
    P <= P.shift a := IsStableUnderShiftBy.le_shift

instance (a : A) [P.IsStableUnderShiftBy a] [P.Nonempty] : (P.shift a).Nonempty :=
  .mono (P.le_shift a)

instance (a : A) : IsStableUnderShiftBy (⊥ : ObjectProperty C) a where
  le_shift _ h := False.elim h

instance (a : A) : IsStableUnderShiftBy (⊤ : ObjectProperty C) a where
  le_shift _ _ := by trivial

instance (a : A) [P.IsStableUnderShiftBy a] :
    P.isoClosure.IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, hY, ⟨e⟩⟩
    exact ⟨Y⟦a⟧, P.le_shift a _ hY, ⟨(shiftFunctor C a).mapIso e⟩⟩

instance (a : A) [P.IsStableUnderShiftBy a]
    [Q.IsStableUnderShiftBy a] : (P ⊓ Q).IsStableUnderShiftBy a where
  le_shift _ hX :=
    ⟨P.le_shift a _ hX.1, Q.le_shift a _ hX.2⟩

variable (A) in
/--
Definition of `IsStableUnderShift` / `IsStableUnderShift` 的定义

English:
class IsStableUnderShift
  parameters: where
  axioms and operations (1):
    - isStableUnderShiftBy((a : A)) : P.IsStableUnderShiftBy a  [default: by infer_instance]

中文:
类 IsStableUnderShift
  参数: where
  公理与运算 (1 个):
    - isStableUnderShiftBy((a : A)) : P.IsStableUnderShiftBy a  [默认: by infer_instance]

Depends on / 依赖: infer_instance
-/
class IsStableUnderShift where
  isStableUnderShiftBy (a : A) : P.IsStableUnderShiftBy a := by infer_instance

attribute [instance] IsStableUnderShift.isStableUnderShiftBy

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: A] :

中文:
实例 [P.IsStableUnderShift
  签名: A] :
-/
instance [P.IsStableUnderShift A] :
    P.isoClosure.IsStableUnderShift A where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsStableUnderShift
  signature: A]

中文:
实例 [P.IsStableUnderShift
  签名: A]
-/
instance [P.IsStableUnderShift A]
    [Q.IsStableUnderShift A] : (P ⊓ Q).IsStableUnderShift A where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderShift (⊥ : ObjectProperty C) A

中文:
实例 :
  签名: IsStableUnderShift (⊥ : Object命题erty C) A
-/
instance : IsStableUnderShift (⊥ : ObjectProperty C) A where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsStableUnderShift (⊤ : ObjectProperty C) A

中文:
实例 :
  签名: IsStableUnderShift (⊤ : Object命题erty C) A
-/
instance : IsStableUnderShift (⊤ : ObjectProperty C) A where

/--
lemma `prop_shift_iff_of_isStableUnderShift` / 引理 `prop_shift_iff_of_isStableUnderShift`

English:
lemma prop_shift_iff_of_isStableUnderShift
  statement: {G : Type*} [AddGroup G] [HasShift C G]
  proof: by
  refine ⟨fun hX => ?_, P.le_shift g _⟩
  rw [← P.shift_zero G]; rw [← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

中文:
引理 prop_shift_iff_of_isStableUnderShift
  结论: {G : 类型} [AddGroup G] [HasShift C G]
  证明: by
  refine ⟨fun hX => ?_, P.le_shift g _⟩
  rw [← P.shift_zero G]; rw [← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

Depends on / 依赖: P.le_shift, P.shift_shift, P.shift_zero, le_shift, shift_shift, shift_zero
-/
lemma prop_shift_iff_of_isStableUnderShift {G : Type*} [AddGroup G] [HasShift C G]
    [P.IsStableUnderShift G] [P.IsClosedUnderIsomorphisms] (X : C) (g : G) :
    P (X⟦g⟧) ↔ P X := by
  refine ⟨fun hX => ?_, P.le_shift g _⟩
  rw [← P.shift_zero G]; rw [← P.shift_shift g (-g) 0 (by simp)]
  exact P.le_shift (-g) _ hX

variable (A) in
/--
Definition of `shiftClosure` / `shiftClosure` 的定义

English:
definition shiftClosure
  signature: : ObjectProperty C
  body: fun X => exists (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y

中文:
定义 shiftClosure
  签名: : Object命题erty C
  定义体: fun X => exists (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y
-/
def shiftClosure : ObjectProperty C := fun X => exists (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y

/--
lemma `prop_shiftClosure_iff` / 引理 `prop_shiftClosure_iff`

English:
lemma prop_shiftClosure_iff
  given: (X : C)
  proof: Iff.rfl

中文:
引理 prop_shiftClosure_iff
  条件: (X : C)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma prop_shiftClosure_iff (X : C) :
    shiftClosure P A X ↔ exists (Y : C) (a : A) (_ : X ≅ Y⟦a⟧), P Y := Iff.rfl

/--
lemma `le_shiftClosure` / 引理 `le_shiftClosure`

English:
lemma le_shiftClosure
  statement: P <= P.shiftClosure A
  proof: by
  intro X hX
  exact ⟨X, 0, (shiftFunctorZero C A).symm.app X, hX⟩

中文:
引理 le_shiftClosure
  结论: P <= P.shiftClosure A
  证明: by
  intro X hX
  exact ⟨X, 0, (shiftFunctorZero C A).symm.app X, hX⟩

Depends on / 依赖: shiftFunctorZero, symm.app
-/
lemma le_shiftClosure : P <= P.shiftClosure A := by
  intro X hX
  exact ⟨X, 0, (shiftFunctorZero C A).symm.app X, hX⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.Nonempty]
  signature: : (P.shiftClosure A).Nonempty
  body: .mono P.le_shiftClosure

中文:
实例 [P.Nonempty]
  签名: : (P.shiftClosure A).Nonempty
  定义体: .mono P.le_shiftClosure

Depends on / 依赖: P.le_shiftClosure, le_shiftClosure
-/
instance [P.Nonempty] : (P.shiftClosure A).Nonempty :=
  .mono P.le_shiftClosure

variable {P Q} in
/--
lemma `monotone_shiftClosure` / 引理 `monotone_shiftClosure`

English:
lemma monotone_shiftClosure
  given: (h : P <= Q)
  statement: P.shiftClosure A <= Q.shiftClosure A
  proof: by
  rintro X ⟨Y, a, i, hY⟩
  refine ⟨Y, a, i, h Y hY⟩

中文:
引理 monotone_shiftClosure
  条件: (h : P <= Q)
  结论: P.shiftClosure A <= Q.shiftClosure A
  证明: by
  rintro X ⟨Y, a, i, hY⟩
  refine ⟨Y, a, i, h Y hY⟩

Depends on / 依赖: diagonal
-/
lemma monotone_shiftClosure (h : P <= Q) : P.shiftClosure A <= Q.shiftClosure A := by
  rintro X ⟨Y, a, i, hY⟩
  refine ⟨Y, a, i, h Y hY⟩

/--
lemma `shiftClosure_eq_self` / 引理 `shiftClosure_eq_self`

English:
lemma shiftClosure_eq_self
  given: [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A]
  proof: by
  refine le_antisymm ?_ P.le_shiftClosure
  rintro X ⟨Y, a, i, hY⟩
  exact P.prop_of_iso i.symm (P.le_shift a Y hY)

@[simp]

中文:
引理 shiftClosure_eq_self
  条件: [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A]
  证明: by
  refine le_antisymm ?_ P.le_shiftClosure
  rintro X ⟨Y, a, i, hY⟩
  exact P.prop_of_iso i.symm (P.le_shift a Y hY)

@[simp]

Depends on / 依赖: P.le_shift, P.le_shiftClosure, P.prop_of_iso, has_color, i.symm, le_antisymm, le_shift, le_shiftClosure, prop_of_iso
-/
lemma shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] [P.IsStableUnderShift A] :
    P.shiftClosure A = P := by
  refine le_antisymm ?_ P.le_shiftClosure
  rintro X ⟨Y, a, i, hY⟩
  exact P.prop_of_iso i.symm (P.le_shift a Y hY)

@[simp]
/--
lemma `shiftClosure_bot` / 引理 `shiftClosure_bot`

English:
lemma shiftClosure_bot
  statement: shiftClosure (⊥ : ObjectProperty C) A = ⊥
  proof: shiftClosure_eq_self _

@[simp]

中文:
引理 shiftClosure_bot
  结论: shiftClosure (⊥ : Object命题erty C) A = ⊥
  证明: shiftClosure_eq_self _

@[simp]

Depends on / 依赖: IsEmpty, IsEmpty.forall_iff, Multiset, Multiset.nodup_zero, Multiset.notMem_zero, forall_iff, nodup_zero, notMem_zero, shiftClosure_eq_self
-/
lemma shiftClosure_bot : shiftClosure (⊥ : ObjectProperty C) A = ⊥ := shiftClosure_eq_self _

@[simp]
/--
lemma `shiftClosure_top` / 引理 `shiftClosure_top`

English:
lemma shiftClosure_top
  statement: shiftClosure (⊤ : ObjectProperty C) A = ⊤
  proof: shiftClosure_eq_self _

中文:
引理 shiftClosure_top
  结论: shiftClosure (⊤ : Object命题erty C) A = ⊤
  证明: shiftClosure_eq_self _

Depends on / 依赖: shiftClosure_eq_self
-/
lemma shiftClosure_top : shiftClosure (⊤ : ObjectProperty C) A = ⊤ := shiftClosure_eq_self _

/--
lemma `shiftClosure_le_iff` / 引理 `shiftClosure_le_iff`

English:
lemma shiftClosure_le_iff
  given: [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A]
  proof: ⟨(le_shiftClosure P).trans,
    fun h => (monotone_shiftClosure h).trans (by rw [shiftClosure_eq_self])⟩

中文:
引理 shiftClosure_le_iff
  条件: [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A]
  证明: ⟨(le_shiftClosure P).trans,
    fun h => (monotone_shiftClosure h).trans (by rw [shiftClosure_eq_self])⟩

Depends on / 依赖: le_shiftClosure, monotone_shiftClosure, shiftClosure_eq_self
-/
lemma shiftClosure_le_iff [IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A] :
    shiftClosure P A <= Q ↔ P <= Q :=
  ⟨(le_shiftClosure P).trans,
    fun h => (monotone_shiftClosure h).trans (by rw [shiftClosure_eq_self])⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.shiftClosure A).IsClosedUnderIsomorphisms
  body: by
    rintro X Y i ⟨Z, a, i', hZ⟩
    exact ⟨Z, a, i.symm.trans i', hZ⟩

中文:
实例 :
  签名: (P.shiftClosure A).IsClosedUnderIsomorphisms
  定义体: by
    rintro X Y i ⟨Z, a, i', hZ⟩
    exact ⟨Z, a, i.symm.trans i', hZ⟩

Depends on / 依赖: i.symm.trans
-/
instance : (P.shiftClosure A).IsClosedUnderIsomorphisms where
  of_iso := by
    rintro X Y i ⟨Z, a, i', hZ⟩
    exact ⟨Z, a, i.symm.trans i', hZ⟩

instance (a : A) : (P.shiftClosure A).IsStableUnderShiftBy a where
  le_shift := by
    rintro X ⟨Y, b, i, hY⟩
exact ⟨Y, b + a, ((shiftFunctor C a).mapIso i).trans
      (shiftFunctorAdd C b a).symm.app Y, hY⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (P.shiftClosure A).IsStableUnderShift A

中文:
实例 :
  签名: (P.shiftClosure A).IsStableUnderShift A
-/
instance : (P.shiftClosure A).IsStableUnderShift A where

/--
lemma `isStableUnderShift_iff_shiftClosure_eq_self` / 引理 `isStableUnderShift_iff_shiftClosure_eq_self`

English:
lemma isStableUnderShift_iff_shiftClosure_eq_self
  given: [P.IsClosedUnderIsomorphisms]
  proof: ⟨fun _ => shiftClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

中文:
引理 isStableUnderShift_iff_shiftClosure_eq_self
  条件: [P.IsClosedUnderIsomorphisms]
  证明: ⟨fun _ => shiftClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

Depends on / 依赖: infer_instance, shiftClosure_eq_self
-/
lemma isStableUnderShift_iff_shiftClosure_eq_self [P.IsClosedUnderIsomorphisms] :
    IsStableUnderShift P A ↔ shiftClosure P A = P :=
  ⟨fun _ => shiftClosure_eq_self _, fun h => by rw [← h]; infer_instance⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: (G : Type*) [AddGroup G]
  body: IsStableUnderShiftBy.mk by
    rw [shift_iSup]
    intro X hX
    rw [prop_iSup_iff] at hX ⊢
    obtain ⟨b, hb⟩ := hX
    exact ⟨-a + b, by rwa [P.shift_shift _ _ _ (add_neg_cancel_left a b)]⟩

中文:
实例 [P.IsClosedUnderIsomorphisms]
  签名: (G : 类型) [AddGroup G]
  定义体: IsStableUnderShiftBy.mk by
    rw [shift_iSup]
    intro X hX
    rw [prop_iSup_iff] at hX ⊢
    obtain ⟨b, hb⟩ := hX
    exact ⟨-a + b, by rwa [P.shift_shift _ _ _ (add_neg_cancel_left a b)]⟩

Depends on / 依赖: IsStableUnderShiftBy, IsStableUnderShiftBy.mk, P.shift_shift, add_neg_cancel_left, prop_iSup_iff, shift_iSup, shift_shift
-/
instance [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G]
    [HasShift C G] : (⨆ (a : G), P.shift a).IsStableUnderShift G where
isStableUnderShiftBy a := IsStableUnderShiftBy.mk by
    rw [shift_iSup]
    intro X hX
    rw [prop_iSup_iff] at hX ⊢
    obtain ⟨b, hb⟩ := hX
    exact ⟨-a + b, by rwa [P.shift_shift _ _ _ (add_neg_cancel_left a b)]⟩

/--
lemma `shiftClosure_eq_iSup` / 引理 `shiftClosure_eq_iSup`

English:
lemma shiftClosure_eq_iSup
  given: [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G] [HasShift C G]
  proof: by
  apply le_antisymm
  · rw [shiftClosure_le_iff]
    conv_lhs => rw [← P.shift_zero G]
    exact le_iSup P.shift (0 : G)
  · intro X hX
    obtain ⟨a, ha⟩ := (prop_iSup_iff _ _).mp hX
    exact ⟨X⟦a⟧, -a, (shiftShiftNeg X a).symm, ha⟩

中文:
引理 shiftClosure_eq_iSup
  条件: [P.IsClosedUnderIsomorphisms] (G : 类型) [AddGroup G] [HasShift C G]
  证明: by
  apply le_antisymm
  · rw [shiftClosure_le_iff]
    conv_lhs => rw [← P.shift_zero G]
    exact le_iSup P.shift (0 : G)
  · intro X hX
    obtain ⟨a, ha⟩ := (prop_iSup_iff _ _).mp hX
    exact ⟨X⟦a⟧, -a, (shiftShiftNeg X a).symm, ha⟩

Depends on / 依赖: P.shift, P.shift_zero, conv_lhs, le_antisymm, le_iSup, prop_iSup_iff, shiftClosure_le_iff, shiftShiftNeg, shift_zero
-/
lemma shiftClosure_eq_iSup [P.IsClosedUnderIsomorphisms] (G : Type*) [AddGroup G] [HasShift C G] :
    P.shiftClosure G = ⨆ (x : G), P.shift x := by
  apply le_antisymm
  · rw [shiftClosure_le_iff]
    conv_lhs => rw [← P.shift_zero G]
    exact le_iSup P.shift (0 : G)
  · intro X hX
    obtain ⟨a, ha⟩ := (prop_iSup_iff _ _).mp hX
    exact ⟨X⟦a⟧, -a, (shiftShiftNeg X a).symm, ha⟩

variable [P.IsStableUnderShift A]

/--
Instance `hasShift` / 实例 `hasShift`

English:
instance hasShift
  signature: :
  body: P.fullyFaithfulι.hasShift (fun n => ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X => P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)

中文:
实例 hasShift
  签名: :
  定义体: P.fullyFaithfulι.hasShift (fun n => ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X => P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)

Depends on / 依赖: ObjectProperty, ObjectProperty.lift, P.fullyFaithful, P.le_shift, P.liftComp, hasShift, le_shift, shiftFunctor
-/
noncomputable instance hasShift :
    HasShift P.FullSubcategory A :=
  P.fullyFaithfulι.hasShift (fun n => ObjectProperty.lift _ (P.ι ⋙ shiftFunctor C n)
    (fun X => P.le_shift n _ X.2)) (fun _ => P.liftCompιIso _ _)

/--
Instance `commShiftι` / 实例 `commShiftι`

English:
instance commShiftι
  signature: : P.ι.CommShift A
  body: Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

中文:
实例 commShiftι
  签名: : P.ι.CommShift A
  定义体: Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

Depends on / 依赖: CommShift, Functor, Functor.CommShift.ofHasShiftOfFullyFaithful, ofHasShiftOfFullyFaithful
-/
instance commShiftι : P.ι.CommShift A :=
  Functor.CommShift.ofHasShiftOfFullyFaithful _ _ _

-- these definitions are made irreducible to prevent any abuse of defeq
attribute [irreducible] hasShift commShiftι

section

variable (F : E ⥤ C) (hF : forall (X : E), P (F.obj X))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.CommShift
  signature: A] :
  body: Functor.CommShift.ofComp (P.liftCompιIso F hF) A

中文:
实例 [F.CommShift
  签名: A] :
  定义体: Functor.CommShift.ofComp (P.liftCompιIso F hF) A

Depends on / 依赖: CommShift, Functor, Functor.CommShift.ofComp, P.liftComp, ofComp
-/
noncomputable instance [F.CommShift A] :
    (P.lift F hF).CommShift A :=
  Functor.CommShift.ofComp (P.liftCompιIso F hF) A

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [F.CommShift
  signature: A] :
  body: Functor.CommShift.ofComp_compatibility _ _

中文:
实例 [F.CommShift
  签名: A] :
  定义体: Functor.CommShift.ofComp_compatibility _ _

Depends on / 依赖: CommShift, Functor, Functor.CommShift.ofComp_compatibility, ofComp_compatibility
-/
noncomputable instance [F.CommShift A] :
    NatTrans.CommShift (P.liftCompιIso F hF).hom A :=
  Functor.CommShift.ofComp_compatibility _ _

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [P.IsClosedUnderIsomorphisms]
  signature: (F : E ⥤ C) [F.CommShift A]
  body: { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }

中文:
实例 [P.IsClosedUnderIsomorphisms]
  签名: (F : E ⥤ C) [F.CommShift A]
  定义体: { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }

Depends on / 依赖: F.commShiftIso, P.le_shift, P.prop_of_iso, commShiftIso, le_shift, prop_of_iso, symm.app
-/
instance [P.IsClosedUnderIsomorphisms] (F : E ⥤ C) [F.CommShift A] :
    (P.inverseImage F).IsStableUnderShift A where
  isStableUnderShiftBy n :=
    { le_shift _ hY := P.prop_of_iso ((F.commShiftIso n).symm.app _) (P.le_shift n _ hY) }

end ObjectProperty

end CategoryTheory
