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

variable (C : Type*) [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

open Pretriangulated

/-- `TStructure C` is the type of t-structures on the (pre)triangulated category `C`. -/
/-
**CategoryTheory.Triangulated.TStructure** 是 Mathlib 中的一个结构，位于命名空间 `CategoryTheo
ry.Triangulated`。
形式化陈述：TStructure where /-- the predicate of objects that are `≤ n` for `n : ℤ`. 
-/ le (n : Int) : ObjectProperty C /-- the predicate of objects that are `≥ n` f
or `n : ℤ`. -/ ge (n : Int) : ObjectProperty C le_isClosedUnderIsomorphisms (n :
 Int) : (le n).IsClosedUnderIsomorphisms
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`TStructure C` is the type of t-structures on the (pre)triangulated category `C`
.
-/
structure TStructure where
  /-- the predicate of objects that are `≤ n` for `n : ℤ`. -/
  le (n : ℤ) : ObjectProperty C
  /-- the predicate of objects that are `≥ n` for `n : ℤ`. -/
  ge (n : ℤ) : ObjectProperty C
  le_isClosedUnderIsomorphisms (n : ℤ) : (le n).IsClosedUnderIsomorphisms := by infer_instance
  ge_isClosedUnderIsomorphisms (n : ℤ) : (ge n).IsClosedUnderIsomorphisms := by infer_instance
  le_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : le n X) : le n' (X⟦a⟧)
  ge_shift (n a n' : ℤ) (h : a + n' = n) (X : C) (hX : ge n X) : ge n' (X⟦a⟧)
  zero' ⦃X Y : C⦄ (f : X ⟶ Y) (hX : le 0 X) (hY : ge 1 Y) : f = 0
  le_zero_le : le 0 ≤ le 1
  ge_one_le : ge 1 ≤ ge 0
  exists_triangle_zero_one (A : C) : ∃ (X Y : C) (_ : le 0 X) (_ : ge 1 Y)
    (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C

namespace TStructure

attribute [instance] le_isClosedUnderIsomorphisms ge_isClosedUnderIsomorphisms

variable {C}
variable (t : TStructure C)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Triangulated.TStructure.exists_triangle** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：exists_triangle (A : C) (n₀ n₁ : Int) (h : n₀ + 1 = n₁) : exists (X Y : C)
 (_ : t.le n₀ X) (_ : t.ge n₁ Y) (f : X ⟶ A) (g : A ⟶ Y) (h : Y ⟶ X⟦(1 : Int)⟧),
 Triangle.mk f g h in distTriang C
参数：A : C；n₀ n₁ : Int；h : n₀ + 1 = n₁。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.exists_triangle_zero_one`：∀ {C : 
Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory
.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Pretriangulated.isomorphic_distinguished`：∀ {C : Type u} 
{inst : CategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZer
oObject C}   {inst_2 : CategoryTheory.HasShif…
· 使用引理 `CategoryTheory.Pretriangulated.Triangle.shift_distinguished`：shift_disti
nguished (n : Int) : (CategoryTheory.shiftFunctor (Triangle C) n).obj T in distT
riang C
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Int.negOnePow_neg`：negOnePow_neg (n : Int) : (-n).negOnePow = n.negOnePo
w
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
-/
lemma exists_triangle (A : C) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    ∃ (X Y : C) (_ : t.le n₀ X) (_ : t.ge n₁ Y) (f : X ⟶ A) (g : A ⟶ Y)
      (h : Y ⟶ X⟦(1 : ℤ)⟧), Triangle.mk f g h ∈ distTriang C := by
  obtain ⟨X, Y, hX, hY, f, g, h, mem⟩ := t.exists_triangle_zero_one (A⟦n₀⟧)
  let T := (Triangle.shiftFunctor C (-n₀)).obj (Triangle.mk f g h)
  let e := (shiftEquiv C n₀).unitIso.symm.app A
  have hT' : Triangle.mk (T.mor₁ ≫ e.hom) (e.inv ≫ T.mor₂) T.mor₃ ∈ distTriang C := by
    refine isomorphic_distinguished _ (Triangle.shift_distinguished _ mem (-n₀)) _ ?_
    refine Triangle.isoMk _ _ (Iso.refl _) e.symm (Iso.refl _) ?_ ?_ ?_
    all_goals simp [T]
  exact ⟨_, _, t.le_shift _ _ _ (neg_add_cancel n₀) _ hX,
    t.ge_shift _ _ _ (by lia) _ hY, _, _, _, hT'⟩
/-
**CategoryTheory.Triangulated.TStructure.shift_le** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：shift_le (a n n' : Int) (hn' : a + n = n') : (t.le n).shift a = t.le n'
参数：a n n' : Int；hn' : a + n = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_isClosedUnderIsomorphisms`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
-/
lemma shift_le (a n n' : ℤ) (hn' : a + n = n') :
    (t.le n).shift a = t.le n' := by
  ext X
  constructor
  · intro hX
    exact ((t.le n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.le_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.le_shift _ _ _ hn' X hX
/-
**CategoryTheory.Triangulated.TStructure.shift_ge** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.Triangulated.TStructure`。
形式化陈述：shift_ge (a n n' : Int) (hn' : a + n = n') : (t.ge n).shift a = t.ge n'
参数：a n n' : Int；hn' : a + n = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.ObjectProperty.prop_iff_of_iso`：prop_iff_of_iso [IsClosed
UnderIsomorphisms P] {X Y : C} (e : X ≅ Y) : P X ↔ P Y
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_isClosedUnderIsomorphisms`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
-/
lemma shift_ge (a n n' : ℤ) (hn' : a + n = n') :
    (t.ge n).shift a = t.ge n' := by
  ext X
  constructor
  · intro hX
    exact ((t.ge n').prop_iff_of_iso ((shiftEquiv C a).unitIso.symm.app X)).1
      (t.ge_shift n (-a) n' (by lia) _ hX)
  · intro hX
    exact t.ge_shift _ _ _ hn' X hX
/-
**CategoryTheory.Triangulated.TStructure.le_monotone** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：le_monotone : Monotone t.le
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Triangulated.TStructure.shift_le`：shift_le (a n n' : Int)
 (hn' : a + n = n') : (t.le n).shift a = t.le n'
· 使用引理 `CategoryTheory.ObjectProperty.prop_shift_iff`：prop_shift_iff (a : A) (X 
: C) : P.shift a X ↔ P (X⟦a⟧)
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_zero_le`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C
]   [inst_2 : CategoryTheory.Limits.Has…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.nonneg_def`：∀ {a : ℤ}, a.NonNeg ↔ ∃ n, a = ↑n
-/
lemma le_monotone : Monotone t.le := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.le n ≤ t.le (n + a)
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_le n 1 (n + (1 : ℕ)) rfl, ObjectProperty.prop_shift_iff]
    rw [← t.shift_le n 0 n (add_zero n), ObjectProperty.prop_shift_iff] at hX
    exact t.le_zero_le _ hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (ha n).trans (hb (n + a))
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one
/-
**CategoryTheory.Triangulated.TStructure.ge_antitone** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：ge_antitone : Antitone t.ge
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Triangulated.TStructure.shift_ge`：shift_ge (a n n' : Int)
 (hn' : a + n = n') : (t.ge n).shift a = t.ge n'
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_one_le`：∀ {C : Type u_1} [inst
 : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]
   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.ObjectProperty.prop_shift_iff`：prop_shift_iff (a : A) (X 
: C) : P.shift a X ↔ P (X⟦a⟧)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.nonneg_def`：∀ {a : ℤ}, a.NonNeg ↔ ∃ n, a = ↑n
-/
lemma ge_antitone : Antitone t.ge := by
  let H := fun (a : ℕ) => ∀ (n : ℤ), t.ge (n + a) ≤ t.ge n
  suffices ∀ (a : ℕ), H a by
    intro n₀ n₁ h
    obtain ⟨a, ha⟩ := Int.nonneg_def.1 h
    obtain rfl : n₁ = n₀ + a := by lia
    apply this
  have H_zero : H 0 := fun n => by
    simp only [Nat.cast_zero, add_zero]
    rfl
  have H_one : H 1 := fun n X hX => by
    rw [← t.shift_ge n 1 (n + (1 : ℕ)) (by simp), ObjectProperty.prop_shift_iff] at hX
    rw [← t.shift_ge n 0 n (add_zero n)]
    exact t.ge_one_le _ hX
  have H_add : ∀ (a b c : ℕ) (_ : a + b = c) (_ : H a) (_ : H b), H c := by
    intro a b c h ha hb n
    rw [← h, Nat.cast_add, ← add_assoc]
    exact (hb (n + a)).trans (ha n)
  intro a
  induction a with
  | zero => exact H_zero
  | succ a ha => exact H_add a 1 _ rfl ha H_one

/-- Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsLE X n`
holds if `X : C` is `≤ n` for the t-structure. -/
/-
**CategoryTheory.Triangulated.TStructure.IsLE** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Triangulated.TStructure`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] → CategoryTheory.Triangulated.TStructure C
 → C → ℤ → Prop
参数：n : ℤ；CategoryTheory.shiftFunctor C n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsLE 
X n`
holds if `X : C` is `≤ n` for the t-structure.
-/
class IsLE (X : C) (n : ℤ) : Prop where
  le : t.le n X

/-- Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsGE X n`
holds if `X : C` is `≥ n` for the t-structure. -/
/-
**CategoryTheory.Triangulated.TStructure.IsGE** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.Triangulated.TStructure`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     [in
st_1 : CategoryTheory.Preadditive C] →       [inst_2 : CategoryTheory.Limits.Has
ZeroObject C] →         [inst_3 : CategoryTheory.HasShift C ℤ] →           [inst
_4 : ∀ (n : ℤ), (CategoryTheory.shiftFunctor C n).Additive] →             [inst_
5 : CategoryTheory.Pretriangulated C] → CategoryTheory.Triangulated.TStructure C
 → C → ℤ → Prop
参数：n : ℤ；CategoryTheory.shiftFunctor C n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a t-structure `t` on a pretriangulated category `C`, the property `t.IsGE 
X n`
holds if `X : C` is `≥ n` for the t-structure.
-/
class IsGE (X : C) (n : ℤ) : Prop where
  ge : t.ge n X
/-
**CategoryTheory.Triangulated.TStructure.le_of_isLE** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：le_of_isLE (X : C) (n : Int) [t.IsLE X n] : t.le n X
参数：X : C；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.IsLE.le`：∀ {C : Type u_1} {inst :
 CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive C}  
 {inst_2 : CategoryTheory.Limits.Has…
-/
lemma le_of_isLE (X : C) (n : ℤ) [t.IsLE X n] : t.le n X := IsLE.le
/-
**CategoryTheory.Triangulated.TStructure.ge_of_isGE** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：ge_of_isGE (X : C) (n : Int) [t.IsGE X n] : t.ge n X
参数：X : C；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.IsGE.ge`：∀ {C : Type u_1} {inst :
 CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Preadditive C}  
 {inst_2 : CategoryTheory.Limits.Has…
-/
lemma ge_of_isGE (X : C) (n : ℤ) [t.IsGE X n] : t.ge n X := IsGE.ge
/-
**CategoryTheory.Triangulated.TStructure.isLE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_of_iso {X Y : C} (e : X ≅ Y) (n : Int) [t.IsLE X n] : t.IsLE Y n wher
e le
参数：e : X ≅ Y；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_isClosedUnderIsomorphisms`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_of_isLE`：le_of_isLE (X : C) (n
 : Int) [t.IsLE X n] : t.le n X
-/
lemma isLE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsLE X n] : t.IsLE Y n where
  le := (t.le n).prop_of_iso e (t.le_of_isLE X n)
/-
**CategoryTheory.Triangulated.TStructure.isGE_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_of_iso {X Y : C} (e : X ≅ Y) (n : Int) [t.IsGE X n] : t.IsGE Y n wher
e ge
参数：e : X ≅ Y；n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.prop_of_iso`：prop_of_iso [IsClosedUnderIso
morphisms P] {X Y : C} (e : X ≅ Y) (hX : P X) : P Y
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_isClosedUnderIsomorphisms`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTh
eory.Preadditive C]   [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_of_isGE`：ge_of_isGE (X : C) (n
 : Int) [t.IsGE X n] : t.ge n X
-/
lemma isGE_of_iso {X Y : C} (e : X ≅ Y) (n : ℤ) [t.IsGE X n] : t.IsGE Y n where
  ge := (t.ge n).prop_of_iso e (t.ge_of_isGE X n)
/-
**CategoryTheory.Triangulated.TStructure.isLE_of_le** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_of_le (X : C) (p q : Int) (hpq : p <= q
参数：X : C；p q : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_monotone`：le_monotone : Monoto
ne t.le
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_of_isLE`：le_of_isLE (X : C) (n
 : Int) [t.IsLE X n] : t.le n X
-/
lemma isLE_of_le (X : C) (p q : ℤ) (hpq : p ≤ q := by lia) [t.IsLE X p] : t.IsLE X q where
  le := le_monotone t hpq _ (t.le_of_isLE X p)
/-
**CategoryTheory.Triangulated.TStructure.isGE_of_ge** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_of_ge (X : C) (p q : Int) (hpq : p <= q
参数：X : C；p q : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_antitone`：ge_antitone : Antito
ne t.ge
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_of_isGE`：ge_of_isGE (X : C) (n
 : Int) [t.IsGE X n] : t.ge n X
-/
lemma isGE_of_ge (X : C) (p q : ℤ) (hpq : p ≤ q := by lia) [t.IsGE X q] : t.IsGE X p where
  ge := ge_antitone t hpq _ (t.ge_of_isGE X q)

@[deprecated (since := "2026-01-30")] alias isLE_of_LE := isLE_of_le
@[deprecated (since := "2026-01-30")] alias isGE_of_GE := isGE_of_ge

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.le_iff_isLE** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：le_iff_isLE (X : C) (n : Int) : t.le n X ↔ t.IsLE X n
参数：X : C；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_of_isLE`：le_of_isLE (X : C) (n
 : Int) [t.IsLE X n] : t.le n X
-/
lemma le_iff_isLE (X : C) (n : ℤ) : t.le n X ↔ t.IsLE X n :=
  ⟨fun h ↦ ⟨h⟩, fun _ ↦ t.le_of_isLE X n⟩

@[simp]
/-
**CategoryTheory.Triangulated.TStructure.ge_iff_isGE** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Triangulated.TStructure`。
形式化陈述：ge_iff_isGE (X : C) (n : Int) : t.ge n X ↔ t.IsGE X n
参数：X : C；n : Int。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_of_isGE`：ge_of_isGE (X : C) (n
 : Int) [t.IsGE X n] : t.ge n X
-/
lemma ge_iff_isGE (X : C) (n : ℤ) : t.ge n X ↔ t.IsGE X n :=
  ⟨fun h ↦ ⟨h⟩, fun _ ↦ t.ge_of_isGE X n⟩
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (t.le n).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [le_iff_isLE] at h ⊢
    exact t.isLE_of_iso e _
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (n : ℤ) : (t.ge n).IsClosedUnderIsomorphisms where
  of_iso e h := by
    simp only [ge_iff_isGE] at h ⊢
    exact t.isGE_of_iso e _
/-
**CategoryTheory.Triangulated.TStructure.isLE_shift** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_shift (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.le_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_of_isLE`：le_of_isLE (X : C) (n
 : Int) [t.IsLE X n] : t.le n X
-/
lemma isLE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsLE X n] :
    t.IsLE (X⟦a⟧) n' :=
  ⟨t.le_shift n a n' hn' X (t.le_of_isLE X n)⟩
/-
**CategoryTheory.Triangulated.TStructure.isGE_shift** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_shift (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Triangulated.TStructure.ge_shift`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C] 
  [inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_of_isGE`：ge_of_isGE (X : C) (n
 : Int) [t.IsGE X n] : t.ge n X
-/
lemma isGE_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsGE X n] :
    t.IsGE (X⟦a⟧) n' :=
  ⟨t.ge_shift n a n' hn' X (t.ge_of_isGE X n)⟩
/-
**CategoryTheory.Triangulated.TStructure.isLE_of_shift** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_of_shift (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_shift`：isLE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_iso`：isLE_of_iso {X Y : C
} (e : X ≅ Y) (n : Int) [t.IsLE X n] : t.IsLE Y n where le
-/
lemma isLE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsLE (X⟦a⟧) n'] :
    t.IsLE X n := by
  have h := t.isLE_shift (X⟦a⟧) n' (-a) n
  exact t.isLE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n
/-
**CategoryTheory.Triangulated.TStructure.isGE_of_shift** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_of_shift (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_shift`：isGE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_iso`：isGE_of_iso {X Y : C
} (e : X ≅ Y) (n : Int) [t.IsGE X n] : t.IsGE Y n where ge
-/
lemma isGE_of_shift (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) [t.IsGE (X⟦a⟧) n'] :
    t.IsGE X n := by
  have h := t.isGE_shift (X⟦a⟧) n' (-a) n
  exact t.isGE_of_iso (show X⟦a⟧⟦-a⟧ ≅ X from (shiftEquiv C a).unitIso.symm.app X) n
/-
**CategoryTheory.Triangulated.TStructure.isLE_shift_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isLE_shift_iff (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_of_shift`：isLE_of_shift (X :
 C) (n a n' : Int) (hn' : a + n' = n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_shift`：isLE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
-/
lemma isLE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) :
    t.IsLE (X⟦a⟧) n' ↔ t.IsLE X n := by
  constructor
  · intro
    exact t.isLE_of_shift X n a n' hn'
  · intro
    exact t.isLE_shift X n a n' hn'
/-
**CategoryTheory.Triangulated.TStructure.isGE_shift_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：isGE_shift_iff (X : C) (n a n' : Int) (hn' : a + n' = n
参数：X : C；n a n' : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_shift`：isGE_of_shift (X :
 C) (n a n' : Int) (hn' : a + n' = n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_shift`：isGE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
-/
lemma isGE_shift_iff (X : C) (n a n' : ℤ) (hn' : a + n' = n := by lia) :
    t.IsGE (X⟦a⟧) n' ↔ t.IsGE X n := by
  constructor
  · intro
    exact t.isGE_of_shift X n a n' hn'
  · intro
    exact t.isGE_shift X n a n' hn'
/-
**CategoryTheory.Triangulated.TStructure.zero** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Triangulated.TStructure`。
形式化陈述：zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁
参数：f : X ⟶ Y；n₀ n₁ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.isLE_shift`：isLE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_shift`：isGE_shift (X : C) (n
 a n' : Int) (hn' : a + n' = n
· 使用引理 `CategoryTheory.Triangulated.TStructure.isGE_of_ge`：isGE_of_ge (X : C) (p
 q : Int) (hpq : p <= q
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.Functor.IsEquivalence.faithful`：∀ {C : Type u₁} {inst : C
ategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D}   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instIsEquivalenceShiftFunctor`：∀ (C : Type u) {A : Type u
_1} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : AddGroup A]   [inst_2 : 
CategoryTheory.HasShift C A] (i : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_zero`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   [inst_2 : Category…
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `CategoryTheory.Triangulated.TStructure.zero'`：∀ {C : Type u_1} [inst : C
ategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.Has…
· 使用引理 `CategoryTheory.Triangulated.TStructure.le_of_isLE`：le_of_isLE (X : C) (n
 : Int) [t.IsLE X n] : t.le n X
· 使用引理 `CategoryTheory.Triangulated.TStructure.ge_of_isGE`：ge_of_isGE (X : C) (n
 : Int) [t.IsGE X n] : t.ge n X
-/
lemma zero {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE Y n₁] : f = 0 := by
  have := t.isLE_shift X n₀ n₀ 0 (add_zero n₀)
  have := t.isGE_shift Y n₁ n₀ (n₁ - n₀)
  have := t.isGE_of_ge (Y⟦n₀⟧) 1 (n₁ - n₀)
  apply (shiftFunctor C n₀).map_injective
  simp only [Functor.map_zero]
  apply t.zero'
  · apply t.le_of_isLE
  · apply t.ge_of_isGE
/-
**CategoryTheory.Triangulated.TStructure.zero_of_isLE_of_isGE** 是 Mathlib 中的一个引理
，位于命名空间 `CategoryTheory.Triangulated.TStructure`。
形式化陈述：zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : Int) (h : n₀ < n₁) (_ 
: t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0
参数：f : X ⟶ Y；n₀ n₁ : Int；h : n₀ < n₁；_ : t.IsLE X n₀；_ : t.IsGE Y n₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero`：zero {X Y : C} (f : X ⟶ Y) 
(n₀ n₁ : Int) (h : n₀ < n₁
-/
lemma zero_of_isLE_of_isGE {X Y : C} (f : X ⟶ Y) (n₀ n₁ : ℤ) (h : n₀ < n₁)
    (_ : t.IsLE X n₀) (_ : t.IsGE Y n₁) : f = 0 :=
  t.zero f n₀ n₁ h
/-
**CategoryTheory.Triangulated.TStructure.isZero** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Triangulated.TStructure`。
形式化陈述：isZero (X : C) (n₀ n₁ : Int) (h : n₀ < n₁
参数：X : C；n₀ n₁ : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.IsZero.iff_id_eq_zero`：iff_id_eq_zero (X : C) : Is
Zero X ↔ 𝟙 X = 0
· 使用引理 `CategoryTheory.Triangulated.TStructure.zero`：zero {X Y : C} (f : X ⟶ Y) 
(n₀ n₁ : Int) (h : n₀ < n₁
-/
lemma isZero (X : C) (n₀ n₁ : ℤ) (h : n₀ < n₁ := by lia)
    [t.IsLE X n₀] [t.IsGE X n₁] : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  exact t.zero _ n₀ n₁ h

/-- The full subcategory consisting of `t`-bounded above objects. -/
/-
**CategoryTheory.Triangulated.TStructure.minus** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Triangulated.TStructure`。
形式化陈述：minus : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory consisting of `t`-bounded above objects.
-/
def minus : ObjectProperty C := fun X ↦ ∃ (n : ℤ), t.IsLE X n

/-- The full subcategory consisting of `t`-bounded below objects. -/
/-
**CategoryTheory.Triangulated.TStructure.plus** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Triangulated.TStructure`。
形式化陈述：plus : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory consisting of `t`-bounded below objects.
-/
def plus : ObjectProperty C := fun X ↦ ∃ (n : ℤ), t.IsGE X n

/-- The full subcategory consisting of `t`-bounded objects. -/
/-
**CategoryTheory.Triangulated.TStructure.bounded** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.Triangulated.TStructure`。
形式化陈述：bounded : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory consisting of `t`-bounded objects.
-/
def bounded : ObjectProperty C := t.plus ⊓ t.minus
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.minus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isLE_of_iso e n⟩
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.minus.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isLE_shift _ i _ _ (by omega)⟩ }
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.plus.IsClosedUnderIsomorphisms where
  of_iso e := by rintro ⟨n, _⟩; exact ⟨_, t.isGE_of_iso e n⟩
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.plus.IsStableUnderShift ℤ where
  isStableUnderShiftBy n :=
    { le_shift := by
        rintro X ⟨i, _⟩
        exact ⟨i - n, t.isGE_shift _ i _ _ (by omega)⟩ }
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.bounded.IsClosedUnderIsomorphisms := by
  dsimp [bounded]
  infer_instance
/-
**CategoryTheory.Triangulated.TStructure.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Triangulated.TStructure`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : t.bounded.IsStableUnderShift ℤ := by
  dsimp [bounded]
  infer_instance

end TStructure

end Triangulated

end CategoryTheory

