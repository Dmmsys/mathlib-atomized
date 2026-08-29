/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.CompleteLattice
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# t-structures on triangulated categories

This file introduces the notion of t-structure on (pre)triangulated categories.

The first example of t-structure shall be the canonical t-structure on the
derived category of an abelian category (TODO).

Given a t-structure `t : TStructure C`, we define typeclasses `t.IsLE X n`
and `t.IsGE X n` in order to say that an object `X : C` is `≤ n` or `≥ n` for `t`.

## Implementation notes

We introduce the type of t-structures rather than a type class saying that we
have fixed a t-structure on a certain category. The reason is that certain
triangulated categories have several t-structures which one may want to
use depending on the context.

## TODO

* show that the heart of `t` is an abelian category

## References
* [Beilinson, Bernstein, Deligne, Gabber, *Faisceaux pervers*][bbd-1982]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace CategoryTheory

open Limits

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C Int]
  [forall (n : Int), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

open Pretriangulated

/--
Definition of `TStructure` / `TStructure` 的定义

English:
structure TStructure
  parameters: where
  axioms and operations (10):
    - le((n : Int)) : ObjectProperty C
    - ge((n : Int)) : ObjectProperty C
    - le_isClosedUnderIsomorphisms((n : Int)) : (le n).IsClosedUnderIsomorphisms  [default: by infer_instance]
    - ge_isClosedUnderIsomorphisms((n : Int)) : (ge n).IsClosedUnderIsomorphisms  [default: by infer_instance]
    - le_shift((n a n' : Int) (h : a + n' = n) (X : C) (hX : le n X)) : le n' (X⟦a⟧)
    - ge_shift((n a n' : Int) (h : a + n' = n) (X : C) (hX : ge n X)) : ge n' (X⟦a⟧)
    - zero'(⦃X Y) : C⦄ (f : X ⟶ Y) (hX : le 0 X) (hY : ge 1 Y) : f = 0
    - le_zero_le : le 0 <= le 1
    - ge_one_le : ge 1 <= ge 0
    - exists_triangle_zero_one((A : C)) : exists (X Y : C) (_ : le 0 X) (_ : ge 1 Y) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in distTriang C

中文:
结构 TStructure
  参数: where
  公理与运算 (10 个):
    - le((n : 整数)) : Object命题erty C
    - ge((n : 整数)) : Object命题erty C
    - le_isClosedUnderIsomorphisms((n : 整数)) : (le n).IsClosedUnderIsomorphisms  [默认: by infer_instance]
    - ge_isClosedUnderIsomorphisms((n : 整数)) : (ge n).IsClosedUnderIsomorphisms  [默认: by infer_instance]
    - le_shift((n a n' : 整数) (h : a + n' = n) (X : C) (hX : le n X)) : le n' (X⟦a⟧)
    - ge_shift((n a n' : 整数) (h : a + n' = n) (X : C) (hX : ge n X)) : ge n' (X⟦a⟧)
    - zero'(⦃X Y) : C⦄ (f : X ⟶ Y) (hX : le 0 X) (hY : ge 1 Y) : f = 0
    - le_zero_le : le 0 <= le 1
    - ge_one_le : ge 1 <= ge 0
    - exists_triangle_zero_one((A : C)) : 存在 (X Y : C) (_ : le 0 X) (_ : ge 1 Y) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : 整数)⟧), Triangle.mk f g h in distTriang C

Depends on / 依赖: IsClosedUnderIsomorphisms, exists_triangle_zero_one, ge_isClosedUnderIsomorphisms, ge_one_le, ge_shift, infer_instance, le_shift, le_zero_le
-/
structure TStructure where
  /-- the predicate of objects that are `≤ n` for `n : ℤ`. -/
  le (n : Int) : ObjectProperty C
  /-- the predicate of objects that are `≥ n` for `n : ℤ`. -/
  ge (n : Int) : ObjectProperty C
  le_isClosedUnderIsomorphisms (n : Int) : (le n).IsClosedUnderIsomorphisms := by infer_instance
  ge_isClosedUnderIsomorphisms (n : Int) : (ge n).IsClosedUnderIsomorphisms := by infer_instance
  le_shift (n a n' : Int) (h : a + n' = n) (X : C) (hX : le n X) : le n' (X⟦a⟧)
  ge_shift (n a n' : Int) (h : a + n' = n) (X : C) (hX : ge n X) : ge n' (X⟦a⟧)
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : le 0 X) (hY : ge 1 Y) : f = 0
  le_zero_le : le 0 <= le 1
  ge_one_le : ge 1 <= ge 0
  exists_triangle_zero_one (A : C) : exists (X Y : C) (_ : le 0 X) (_ : ge 1 Y)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in distTriang C

namespace TStructure

attribute [instance] le_isClosedUnderIsomorphisms ge_isClosedUnderIsomorphisms

variable {C}
variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `exists_triangle` / 引理 `exists_triangle`

English:
lemma exists_triangle
  given: (A : C) (n₀ n₁ : Int) (h : n₀ + 1 = n₁)
  proof: by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ in distTriang C := by
    refine isomorp

中文:
引理 exists_triangle
  条件: (A : C) (n₀ n₁ : 整数) (h : n₀ + 1 = n₁)
  证明: by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ in distTriang C := by
    refine isomorp

Depends on / 依赖: Iso.refl, T.mor, Triangle, Triangle.isoMk, Triangle.mk, Triangle.shiftFunctor, Triangle.shift_distinguished, all_goals, distTriang, e.hom, e.inv, e.symm, exists_triangle_zero_one, isomorphic_distinguished, le_shift, neg_add_cancel, shiftEquiv, shiftFunctor, shift_distinguished, t.exists_triangle_zero_one
-/
lemma exists_triangle (A : C) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) :
    exists (X Y : C) (_ : t.le n₀ X) (_ : t.ge n₁ Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : Int)⟧), Triangle.mk f g h in distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ in distTriang C := by
    refine isomorphic_distinguished _ (Triangle.shift_distinguished _ mem (-n₀)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals simp [T]
  exact ⟨_, _, t.le_shift _ _ _ (neg_add_cancel n₀) _ hX,
    t.ge_shift _ _ _ (by lia) _ hY, _, _, _, hT'⟩

/--
lemma `shift_le` / 引理 `shift_le`

English:
lemma shift_le
  given: (a n n' : Int) (hn' : a + n = n')
  proof: by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX

中文:
引理 shift_le
  条件: (a n n' : 整数) (hn' : a + n = n')
  证明: by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX

Depends on / 依赖: le_shift, prop_iff_of_iso, shiftEquiv, t.le, t.le_shift, unitIso, unitIso.symm.app
-/
lemma shift_le (a n n' : Int) (hn' : a + n = n') :
    (t.le n).shift a = t.le n' := by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX

/--
lemma `shift_ge` / 引理 `shift_ge`

English:
lemma shift_ge
  given: (a n n' : Int) (hn' : a + n = n')
  proof: by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX

中文:
引理 shift_ge
  条件: (a n n' : 整数) (hn' : a + n = n')
  证明: by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX

Depends on / 依赖: ge_shift, prop_iff_of_iso, shiftEquiv, t.ge, t.ge_shift, unitIso, unitIso.symm.app
-/
lemma shift_ge (a n n' : Int) (hn' : a + n = n') :
    (t.ge n).shift a = t.ge n' := by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX

/--
lemma `le_monotone` / 引理 `le_monotone`

English:
lemma le_monotone
  statement: Monotone t.le
  proof: by
  let H := fun (a : Nat) => forall (n : Int), t.le n <= t.le (n + a)
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    

中文:
引理 le_monotone
  结论: Monotone t.le
  证明: by
  let H := fun (a : Nat) => forall (n : Int), t.le n <= t.le (n + a)
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    

Depends on / 依赖: H_one, H_zero, Int.nonneg_def, Nat.cast_zero, ObjectProperty, ObjectProperty.prop_shift_iff, add_zero, cast_zero, le_zero_le, nonneg_def, prop_shift_iff, shift_le, t.le, t.le_zero_le, t.shift_le
-/
lemma le_monotone : Monotone t.le := by
  let H := fun (a : Nat) => forall (n : Int), t.le n <= t.le (n + a)
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_le n 1 (n + (1 : Nat)) rfl]; rw [ObjectProperty.prop_shift_iff]
    rw [← t.shift_le n 0 n (add_zero n)]; rw [ObjectProperty.prop_shift_iff] at hX
    exact t.le_zero_le _ hX
  have H_add : forall (a b c : Nat) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h]; rw [Nat.cast_add]; rw [← add_assoc]
    exact (ha n).trans (hb (n + a))
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one

/--
lemma `ge_antitone` / 引理 `ge_antitone`

English:
lemma ge_antitone
  statement: Antitone t.ge
  proof: by
  let H := fun (a : Nat) => forall (n : Int), t.ge (n + a) <= t.ge n
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    

中文:
引理 ge_antitone
  结论: Antitone t.ge
  证明: by
  let H := fun (a : Nat) => forall (n : Int), t.ge (n + a) <= t.ge n
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    

Depends on / 依赖: H_add, H_one, H_zero, Int.nonneg_def, Nat.cast_zero, ObjectProperty, ObjectProperty.prop_shift_iff, add_zero, cast_zero, ge_one_le, nonneg_def, prop_shift_iff, shift_ge, t.ge, t.ge_one_le, t.shift_ge
-/
lemma ge_antitone : Antitone t.ge := by
  let H := fun (a : Nat) => forall (n : Int), t.ge (n + a) <= t.ge n
  suffices forall (a : Nat), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_ge n 1 (n + (1 : Nat)) (by simp)]; rw [ObjectProperty.prop_shift_iff] at hX
    rw [← t.shift_ge n 0 n (add_zero n)]
    exact t.ge_one_le _ hX
  have H_add : forall (a b c : Nat) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h]; rw [Nat.cast_add]; rw [← add_assoc]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one

/--
Definition of `IsLE` / `IsLE` 的定义

English:
class IsLE
  parameters: (X : C) (n : Int)
  axioms and operations (1):
    - le : t.le n X

中文:
类 IsLE
  参数: (X : C) (n : 整数)
  公理与运算 (1 个):
    - le : t.le n X
-/
class IsLE (X : C) (n : Int) : Prop where
  le : t.le n X

/--
Definition of `IsGE` / `IsGE` 的定义

English:
class IsGE
  parameters: (X : C) (n : Int)
  axioms and operations (1):
    - ge : t.ge n X

中文:
类 IsGE
  参数: (X : C) (n : 整数)
  公理与运算 (1 个):
    - ge : t.ge n X
-/
class IsGE (X : C) (n : Int) : Prop where
  ge : t.ge n X

/--
lemma `le_of_isLE` / 引理 `le_of_isLE`

English:
lemma le_of_isLE
  given: (X : C) (n : Int) [t.IsLE X n]
  statement: t.le n X
  proof: IsLE.le

中文:
引理 le_of_isLE
  条件: (X : C) (n : 整数) [t.IsLE X n]
  结论: t.le n X
  证明: IsLE.le

Depends on / 依赖: IsLE.le
-/
lemma le_of_isLE (X : C) (n : Int) [t.IsLE X n] : t.le n X := IsLE.le

/--
lemma `ge_of_isGE` / 引理 `ge_of_isGE`

English:
lemma ge_of_isGE
  given: (X : C) (n : Int) [t.IsGE X n]
  statement: t.ge n X
  proof: IsGE.ge

中文:
引理 ge_of_isGE
  条件: (X : C) (n : 整数) [t.IsGE X n]
  结论: t.ge n X
  证明: IsGE.ge

Depends on / 依赖: IsGE.ge
-/
lemma ge_of_isGE (X : C) (n : Int) [t.IsGE X n] : t.ge n X := IsGE.ge

/--
lemma `isLE_of_iso` / 引理 `isLE_of_iso`

English:
lemma isLE_of_iso
  given: {X Y : C} (e : X ≅ Y) (n : Int) [t.IsLE X n]
  statement: t.IsLE Y n where
  proof: (t.le n).prop_of_iso e (t.le_of_isLE X n)

中文:
引理 isLE_of_iso
  条件: {X Y : C} (e : X ≅ Y) (n : 整数) [t.IsLE X n]
  结论: t.IsLE Y n where
  证明: (t.le n).prop_of_iso e (t.le_of_isLE X n)

Depends on / 依赖: le_of_isLE, prop_of_iso, t.le, t.le_of_isLE
-/
lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : Int) [t.IsLE X n] : t.IsLE Y n where
  le := (t.le n).prop_of_iso e (t.le_of_isLE X n)

/--
lemma `isGE_of_iso` / 引理 `isGE_of_iso`

English:
lemma isGE_of_iso
  given: {X Y : C} (e : X ≅ Y) (n : Int) [t.IsGE X n]
  statement: t.IsGE Y n where
  proof: (t.ge n).prop_of_iso e (t.ge_of_isGE X n)

中文:
引理 isGE_of_iso
  条件: {X Y : C} (e : X ≅ Y) (n : 整数) [t.IsGE X n]
  结论: t.IsGE Y n where
  证明: (t.ge n).prop_of_iso e (t.ge_of_isGE X n)

Depends on / 依赖: ge_of_isGE, prop_of_iso, t.ge, t.ge_of_isGE
-/
lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : Int) [t.IsGE X n] : t.IsGE Y n where
  ge := (t.ge n).prop_of_iso e (t.ge_of_isGE X n)

/--
lemma `isLE_of_le` / 引理 `isLE_of_le`

English:
lemma isLE_of_le
  given: (X : C) (p q : Int) (hpq : p <= q := by lia) [t.IsLE X p]
  statement: t.IsLE X q where
  proof: le_monotone t hpq _ (t.le_of_isLE X p)

中文:
引理 isLE_of_le
  条件: (X : C) (p q : 整数) (hpq : p <= q := by lia) [t.IsLE X p]
  结论: t.IsLE X q where
  证明: le_monotone t hpq _ (t.le_of_isLE X p)

Depends on / 依赖: le_monotone, le_of_isLE, t.IsLE, t.le_of_isLE
-/
lemma isLE_of_le (X : C) (p q : Int) (hpq : p <= q := by lia) [t.IsLE X p] : t.IsLE X q where
  le := le_monotone t hpq _ (t.le_of_isLE X p)

/--
lemma `isGE_of_ge` / 引理 `isGE_of_ge`

English:
lemma isGE_of_ge
  given: (X : C) (p q : Int) (hpq : p <= q := by lia) [t.IsGE X q]
  statement: t.IsGE X p where
  proof: ge_antitone t hpq _ (t.ge_of_isGE X q)

@[deprecated (since := "2026-01-30")] alias isLE_of_LE := isLE_of_le
@[deprecated (since := "2026-01-30")] alias isGE_of_GE := isGE_of_ge

@[simp]

中文:
引理 isGE_of_ge
  条件: (X : C) (p q : 整数) (hpq : p <= q := by lia) [t.IsGE X q]
  结论: t.IsGE X p where
  证明: ge_antitone t hpq _ (t.ge_of_isGE X q)

@[deprecated (since := "2026-01-30")] alias isLE_of_LE := isLE_of_le
@[deprecated (since := "2026-01-30")] alias isGE_of_GE := isGE_of_ge

@[simp]

Depends on / 依赖: ge_antitone, ge_of_isGE, t.IsGE, t.ge_of_isGE
-/
lemma isGE_of_ge (X : C) (p q : Int) (hpq : p <= q := by lia) [t.IsGE X q] : t.IsGE X p where
  ge := ge_antitone t hpq _ (t.ge_of_isGE X q)

@[deprecated (since := "2026-01-30")] alias isLE_of_LE := isLE_of_le
@[deprecated (since := "2026-01-30")] alias isGE_of_GE := isGE_of_ge

@[simp]
/--
lemma `le_iff_isLE` / 引理 `le_iff_isLE`

English:
lemma le_iff_isLE
  given: (X : C) (n : Int)
  statement: t.le n X ↔ t.IsLE X n
  proof: ⟨fun h => ⟨h⟩, fun _ => t.le_of_isLE X n⟩

@[simp]

中文:
引理 le_iff_isLE
  条件: (X : C) (n : 整数)
  结论: t.le n X ↔ t.IsLE X n
  证明: ⟨fun h => ⟨h⟩, fun _ => t.le_of_isLE X n⟩

@[simp]

Depends on / 依赖: le_of_isLE, t.le_of_isLE
-/
lemma le_iff_isLE (X : C) (n : Int) : t.le n X ↔ t.IsLE X n :=
  ⟨fun h => ⟨h⟩, fun _ => t.le_of_isLE X n⟩

@[simp]
/--
lemma `ge_iff_isGE` / 引理 `ge_iff_isGE`

English:
lemma ge_iff_isGE
  given: (X : C) (n : Int)
  statement: t.ge n X ↔ t.IsGE X n
  proof: ⟨fun h => ⟨h⟩, fun _ => t.ge_of_isGE X n⟩

中文:
引理 ge_iff_isGE
  条件: (X : C) (n : 整数)
  结论: t.ge n X ↔ t.IsGE X n
  证明: ⟨fun h => ⟨h⟩, fun _ => t.ge_of_isGE X n⟩

Depends on / 依赖: ge_of_isGE, t.ge_of_isGE
-/
lemma ge_iff_isGE (X : C) (n : Int) : t.ge n X ↔ t.IsGE X n :=
  ⟨fun h => ⟨h⟩, fun _ => t.ge_of_isGE X n⟩

instance (n : Int) : (t.le n).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [le_iff_isLE] at h ⊢
    exact t.isLE_of_iso e _

instance (n : Int) : (t.ge n).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [ge_iff_isGE] at h ⊢
    exact t.isGE_of_iso e _

/--
lemma `isLE_shift` / 引理 `isLE_shift`

English:
lemma isLE_shift
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsLE X n]
  proof: ⟨t.le_shift n a n' hn' X (t.le_of_isLE X n)⟩

中文:
引理 isLE_shift
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia) [t.IsLE X n]
  证明: ⟨t.le_shift n a n' hn' X (t.le_of_isLE X n)⟩

Depends on / 依赖: le_of_isLE, le_shift, t.IsLE, t.le_of_isLE, t.le_shift
-/
lemma isLE_shift (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.le_shift n a n' hn' X (t.le_of_isLE X n)⟩

/--
lemma `isGE_shift` / 引理 `isGE_shift`

English:
lemma isGE_shift
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsGE X n]
  proof: ⟨t.ge_shift n a n' hn' X (t.ge_of_isGE X n)⟩

中文:
引理 isGE_shift
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia) [t.IsGE X n]
  证明: ⟨t.ge_shift n a n' hn' X (t.ge_of_isGE X n)⟩

Depends on / 依赖: ge_of_isGE, ge_shift, t.IsGE, t.ge_of_isGE, t.ge_shift
-/
lemma isGE_shift (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.ge_shift n a n' hn' X (t.ge_of_isGE X n)⟩

/--
lemma `isLE_of_shift` / 引理 `isLE_of_shift`

English:
lemma isLE_of_shift
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsLE (X⟦a⟧) n']
  proof: by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

中文:
引理 isLE_of_shift
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia) [t.IsLE (X⟦a⟧) n']
  证明: by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

Depends on / 依赖: isLE_of_iso, isLE_shift, shiftEquiv, t.IsLE, t.isLE_of_iso, t.isLE_shift, unitIso, unitIso.symm.app
-/
lemma isLE_of_shift (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

/--
lemma `isGE_of_shift` / 引理 `isGE_of_shift`

English:
lemma isGE_of_shift
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsGE (X⟦a⟧) n']
  proof: by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

中文:
引理 isGE_of_shift
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia) [t.IsGE (X⟦a⟧) n']
  证明: by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

Depends on / 依赖: isGE_of_iso, isGE_shift, shiftEquiv, t.IsGE, t.isGE_of_iso, t.isGE_shift, unitIso, unitIso.symm.app
-/
lemma isGE_of_shift (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n

/--
lemma `isLE_shift_iff` / 引理 `isLE_shift_iff`

English:
lemma isLE_shift_iff
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia)
  proof: by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

中文:
引理 isLE_shift_iff
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia)
  证明: by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

Depends on / 依赖: isLE_of_shift, isLE_shift, t.IsLE, t.isLE_of_shift, t.isLE_shift
-/
lemma isLE_shift_iff (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) :
    t.IsLE (X⟦a⟧) n' ↔ t.IsLE X n := by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'

/--
lemma `isGE_shift_iff` / 引理 `isGE_shift_iff`

English:
lemma isGE_shift_iff
  given: (X : C) (n a n' : Int) (hn' : a + n' = n := by lia)
  proof: by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

中文:
引理 isGE_shift_iff
  条件: (X : C) (n a n' : 整数) (hn' : a + n' = n := by lia)
  证明: by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

Depends on / 依赖: isGE_of_shift, isGE_shift, t.IsGE, t.isGE_of_shift, t.isGE_shift
-/
lemma isGE_shift_iff (X : C) (n a n' : Int) (hn' : a + n' = n := by lia) :
    t.IsGE (X⟦a⟧) n' ↔ t.IsGE X n := by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'

/--
lemma `zero` / 引理 `zero`

English:
lemma zero
  statement: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁ := by lia)
  proof: by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁ - n₀)
  have := t.isGE_of_ge (Y⟦n₀⟧) 1 (n₁ - n₀)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.le_of_isLE
  · apply t.ge_of_isGE

中文:
引理 zero
  结论: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : 整数) (h : n₀ < n₁ := by lia)
  证明: by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁ - n₀)
  have := t.isGE_of_ge (Y⟦n₀⟧) 1 (n₁ - n₀)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.le_of_isLE
  · apply t.ge_of_isGE

Depends on / 依赖: Functor, Functor.map_zero, add_zero, ge_of_isGE, isGE_of_ge, isGE_shift, isLE_shift, le_of_isLE, map_injective, map_zero, shiftFunctor, t.IsGE, t.IsLE, t.ge_of_isGE, t.isGE_of_ge, t.isGE_shift, t.isLE_shift, t.le_of_isLE, t.zero
-/
lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁ - n₀)
  have := t.isGE_of_ge (Y⟦n₀⟧) 1 (n₁ - n₀)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.le_of_isLE
  · apply t.ge_of_isGE

/--
lemma `zero_of_isLE_of_isGE` / 引理 `zero_of_isLE_of_isGE`

English:
lemma zero_of_isLE_of_isGE
  statement: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁)
  proof: t.zero f n₀ n₁ h

中文:
引理 zero_of_isLE_of_isGE
  结论: {X Y : C} (f : X ⟶ Y) (n₀ n₁ : 整数) (h : n₀ < n₁)
  证明: t.zero f n₀ n₁ h

Depends on / 依赖: t.zero
-/
lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h

/--
lemma `isZero` / 引理 `isZero`

English:
lemma isZero
  statement: (X : C) (n₀ n₁ : Int) (h : n₀ < n₁ := by lia)
  proof: by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

中文:
引理 isZero
  结论: (X : C) (n₀ n₁ : 整数) (h : n₀ < n₁ := by lia)
  证明: by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

Depends on / 依赖: IsZero, IsZero.iff_id_eq_zero, iff_id_eq_zero, t.IsGE, t.IsLE, t.zero
-/
lemma isZero (X : C) (n₀ n₁ : Int) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

/--
Definition of `minus` / `minus` 的定义

English:
definition minus
  signature: : ObjectProperty C
  body: fun X => exists (n : Int), t.IsLE X n

中文:
定义 minus
  签名: : Object命题erty C
  定义体: fun X => exists (n : Int), t.IsLE X n

Depends on / 依赖: t.IsLE
-/
def minus : ObjectProperty C := fun X => exists (n : Int), t.IsLE X n

/--
Definition of `plus` / `plus` 的定义

English:
definition plus
  signature: : ObjectProperty C
  body: fun X => exists (n : Int), t.IsGE X n

中文:
定义 plus
  签名: : Object命题erty C
  定义体: fun X => exists (n : Int), t.IsGE X n

Depends on / 依赖: t.IsGE
-/
def plus : ObjectProperty C := fun X => exists (n : Int), t.IsGE X n

/--
Definition of `bounded` / `bounded` 的定义

English:
definition bounded
  signature: : ObjectProperty C
  body: t.plus ⊓ t.minus

中文:
定义 bounded
  签名: : Object命题erty C
  定义体: t.plus ⊓ t.minus

Depends on / 依赖: t.minus, t.plus
-/
def bounded : ObjectProperty C := t.plus ⊓ t.minus

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.minus.IsClosedUnderIsomorphisms
  body: by rintro ⟨n, _⟩; exact ⟨_, t.isLE_of_iso e n⟩

中文:
实例 :
  签名: t.minus.IsClosedUnderIsomorphisms
  定义体: by rintro ⟨n, _⟩; exact ⟨_, t.isLE_of_iso e n⟩

Depends on / 依赖: isLE_of_iso, t.isLE_of_iso
-/
instance : t.minus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isLE_of_iso e n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.minus.IsStableUnderShift Int
  body: { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isLE_shift _ i _ _ (by omega)⟩ }

中文:
实例 :
  签名: t.minus.IsStableUnderShift 整数
  定义体: { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isLE_shift _ i _ _ (by omega)⟩ }

Depends on / 依赖: isLE_shift, le_shift, t.isLE_shift
-/
instance : t.minus.IsStableUnderShift Int where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isLE_shift _ i _ _ (by omega)⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.plus.IsClosedUnderIsomorphisms
  body: by rintro ⟨n, _⟩; exact ⟨_, t.isGE_of_iso e n⟩

中文:
实例 :
  签名: t.plus.IsClosedUnderIsomorphisms
  定义体: by rintro ⟨n, _⟩; exact ⟨_, t.isGE_of_iso e n⟩

Depends on / 依赖: isGE_of_iso, t.isGE_of_iso
-/
instance : t.plus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isGE_of_iso e n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.plus.IsStableUnderShift Int
  body: { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isGE_shift _ i _ _ (by omega)⟩ }

中文:
实例 :
  签名: t.plus.IsStableUnderShift 整数
  定义体: { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isGE_shift _ i _ _ (by omega)⟩ }

Depends on / 依赖: isGE_shift, le_shift, t.isGE_shift
-/
instance : t.plus.IsStableUnderShift Int where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isGE_shift _ i _ _ (by omega)⟩ }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.bounded.IsClosedUnderIsomorphisms
  body: by
  dsimp [bounded]
  infer_instance

中文:
实例 :
  签名: t.bounded.IsClosedUnderIsomorphisms
  定义体: by
  dsimp [bounded]
  infer_instance

Depends on / 依赖: bounded, infer_instance
-/
instance : t.bounded.IsClosedUnderIsomorphisms := by
  dsimp [bounded]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: t.bounded.IsStableUnderShift Int
  body: by
  dsimp [bounded]
  infer_instance

中文:
实例 :
  签名: t.bounded.IsStableUnderShift 整数
  定义体: by
  dsimp [bounded]
  infer_instance

Depends on / 依赖: bounded, infer_instance
-/
instance : t.bounded.IsStableUnderShift Int := by
  dsimp [bounded]
  infer_instance

end TStructure

end Triangulated

end CategoryTheory
