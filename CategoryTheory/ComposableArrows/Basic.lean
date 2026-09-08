/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SuppressCompilation

/-!
# Composable arrows

If `C` is a category, the type of `n`-simplices in the nerve of `C` identifies
to the type of functors `Fin (n + 1) ⥤ C`, which can be thought of as families of `n` composable
arrows in `C`. In this file, we introduce and study this category `ComposableArrows C n`
of `n` composable arrows in `C`.

If `F : ComposableArrows C n`, we define `F.left` as the leftmost object, `F.right` as the
rightmost object, and `F.hom : F.left ⟶ F.right` is the canonical map.

The most significant definition in this file is the constructor
`F.precomp f : ComposableArrows C (n + 1)` for `F : ComposableArrows C n` and `f : X ⟶ F.left`:
"it shifts `F` towards the right and inserts `f` on the left". This `precomp` has
good definitional properties.

In the namespace `CategoryTheory.ComposableArrows`, we provide constructors
like `mk₁ f`, `mk₂ f g`, `mk₃ f g h` for `ComposableArrows C n` for small `n`.

TODO (@joelriou):
* construct some elements in `ComposableArrows m (Fin (n + 1))` for small `n`
  the precomposition with which shall induce functors
  `ComposableArrows C n ⥤ ComposableArrows C m` which correspond to simplicial operations
  (specifically faces) with good definitional properties (this might be necessary for
  up to `n = 7` in order to formalize spectral sequences following Verdier)

-/

set_option backward.defeqAttrib.useBackward true

@[expose] public section

/-!
New `simprocs` that run even in `dsimp` have caused breakages in this file.

(e.g. `dsimp` can now simplify `2 + 3` to `5`)

For now, we just turn off the offending simprocs in this file.

*However*, hopefully it is possible to refactor the material here so that no disabling of
simprocs is needed.

See issue https://github.com/leanprover-community/mathlib4/issues/27382.
-/
attribute [-simp] Fin.reduceFinMk

namespace CategoryTheory

open Category

variable (C : Type*) [Category* C]

/-- `ComposableArrows C n` is the type of functors `Fin (n + 1) ⥤ C`. -/
/-
**CategoryTheory.ComposableArrows** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory`。
形式化陈述：ComposableArrows (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ComposableArrows C n` is the type of functors `Fin (n + 1) ⥤ C`.
-/
abbrev ComposableArrows (n : ℕ) := Fin (n + 1) ⥤ C

namespace ComposableArrows

variable {C} {n m : ℕ}
variable (F G : ComposableArrows C n)

-- We do not yet replace `omega` with `lia` here, as it is measurably slower.
/-- A wrapper for `omega` which prefaces it with some quick and useful attempts -/
macro "valid" : tactic =>
  `(tactic| first | assumption | apply zero_le | apply le_rfl | transitivity <;> assumption | omega)

/-- The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`. -/
@[simp]
/-
**CategoryTheory.ComposableArrows.obj'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
形式化陈述：obj' (i : Nat) (hi : i <= n
参数：i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th object (with `i : ℕ` such that `i ≤ n`) of `F : ComposableArrows C n`.
-/
abbrev obj' (i : ℕ) (hi : i ≤ n := by valid) : C := F.obj ⟨i, by lia⟩

/-- The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`. -/
@[simp]
/-
**CategoryTheory.ComposableArrows.map'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
形式化陈述：map' (i j : Nat) (hij : i <= j
参数：i j : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `F.obj' i ⟶ F.obj' j` when `F : ComposableArrows C n`, and `i` and `j`
are natural numbers such that `i ≤ j ≤ n`.
-/
abbrev map' (i j : ℕ) (hij : i ≤ j := by valid) (hjn : j ≤ n := by valid) :
    F.obj ⟨i, by lia⟩ ⟶ F.obj ⟨j, by lia⟩ :=
  F.map (homOfLE (by simp only [Fin.mk_le_mk]; valid))
/-
**CategoryTheory.ComposableArrows.map'_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F 
: CategoryTheory.ComposableArrows C n) (i : ℕ)   (hi : autoParam (i ≤ n) Categor
yTheory.ComposableArrows.map'_self._auto_1),   F.map' i i ⋯ hi = CategoryTheory.
CategoryStruct.id (F.obj ⟨i, ⋯⟩)
参数：F : CategoryTheory.ComposableArrows C n；i : ℕ；hi : autoParam (i ≤ n) Category
Theory.ComposableArrows.map'_self._auto_1；F.obj ⟨i, ⋯⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma map'_self (i : ℕ) (hi : i ≤ n := by valid) : F.map' i i = 𝟙 _ := F.map_id _
/-
**CategoryTheory.ComposableArrows.map'_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {n : ℕ} (F 
: CategoryTheory.ComposableArrows C n)   (i j k : ℕ) (hij : autoParam (i ≤ j) Ca
tegoryTheory.ComposableArrows.map'_comp._auto_1)   (hjk : autoParam (j ≤ k) Cate
goryTheory.ComposableArrows.map'_comp._auto_3)   (hk : autoParam (k ≤ n) Categor
yTheory.ComposableArrows.map'_comp._auto_5),   F.map' i k ⋯ hk = CategoryTheory.
CategoryStruct.comp (F.map' i j hij ⋯) (F.map' j k hjk hk)
参数：F : CategoryTheory.ComposableArrows C n；i j k : ℕ；hij : autoParam (i ≤ j) Cat
egoryTheory.ComposableArrows.map'_comp._auto_1；hjk : autoParam (j ≤ k) CategoryT
heory.ComposableArrows.map'_comp._auto_3；hk : autoParam (k ≤ n) CategoryTheory.C
omposableArrows.map'_comp._auto_5；F.map' i j hij ⋯；F.map' j k hjk hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma map'_comp (i j k : ℕ) (hij : i ≤ j := by valid)
    (hjk : j ≤ k := by valid) (hk : k ≤ n := by valid) :
    F.map' i k = F.map' i j ≫ F.map' j k :=
  F.map_comp _ _

/-- The leftmost object of `F : ComposableArrows C n`. -/
/-
**CategoryTheory.ComposableArrows.left** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
形式化陈述：left
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The leftmost object of `F : ComposableArrows C n`.
-/
abbrev left := obj' F 0

/-- The rightmost object of `F : ComposableArrows C n`. -/
/-
**CategoryTheory.ComposableArrows.right** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryThe
ory.ComposableArrows`。
形式化陈述：right
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The rightmost object of `F : ComposableArrows C n`.
-/
abbrev right := obj' F n

/-- The canonical map `F.left ⟶ F.right` for `F : ComposableArrows C n`. -/
/-
**CategoryTheory.ComposableArrows.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：hom : F.left ⟶ F.right
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map `F.left ⟶ F.right` for `F : ComposableArrows C n`.
-/
abbrev hom : F.left ⟶ F.right := map' F 0 n

variable {F G}

/-- The map `F.obj' i ⟶ G.obj' i` induced on `i`th objects by a morphism `F ⟶ G`
in `ComposableArrows C n` when `i` is a natural number such that `i ≤ n`. -/
@[simp]
/-
**CategoryTheory.ComposableArrows.app'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheo
ry.ComposableArrows`。
形式化陈述：app' (φ : F ⟶ G) (i : Nat) (hi : i <= n
参数：φ : F ⟶ G；i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `F.obj' i ⟶ G.obj' i` induced on `i`th objects by a morphism `F ⟶ G`
in `ComposableArrows C n` when `i` is a natural number such that `i ≤ n`.
-/
abbrev app' (φ : F ⟶ G) (i : ℕ) (hi : i ≤ n := by valid) :
    F.obj' i ⟶ G.obj' i := φ.app _

@[reassoc]
/-
**CategoryTheory.ComposableArrows.naturality'** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ComposableArrows`。
形式化陈述：naturality' (φ : F ⟶ G) (i j : Nat) (hij : i <= j
参数：φ : F ⟶ G；i j : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
-/
lemma naturality' (φ : F ⟶ G) (i j : ℕ) (hij : i ≤ j := by valid)
    (hj : j ≤ n := by valid) :
    F.map' i j ≫ app' φ j = app' φ i ≫ G.map' i j :=
  φ.naturality _

/-- Constructor for `ComposableArrows C 0`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 0`.
-/
def mk₀ (X : C) : ComposableArrows C 0 := (Functor.const (Fin 1)).obj X

namespace Mk₁

variable (X₀ X₁ : C)

/-- The map which sends `0 : Fin 2` to `X₀` and `1` to `X₁`. -/
@[simp]
/-
**CategoryTheory.ComposableArrows.Mk₁.obj** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ComposableArrows.Mk₁`。
形式化陈述：{C : Type u_1} → C → C → Fin 2 → C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map which sends `0 : Fin 2` to `X₀` and `1` to `X₁`.
-/
def obj : Fin 2 → C
  | ⟨0, _⟩ => X₀
  | ⟨1, _⟩  => X₁

variable {X₀ X₁}
variable (f : X₀ ⟶ X₁)

/-- The obvious map `obj X₀ X₁ i ⟶ obj X₀ X₁ j` whenever `i j : Fin 2` satisfy `i ≤ j`. -/
@[simp]
/-
**CategoryTheory.ComposableArrows.Mk₁.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ComposableArrows.Mk₁`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X₀
 X₁ : C} →       (X₀ ⟶ X₁) →         (i j : Fin 2) →           i ≤ j → (Category
Theory.ComposableArrows.Mk₁.obj X₀ X₁ i ⟶ CategoryTheory.ComposableArrows.Mk₁.ob
j X₀ X₁ j)
参数：X₀ ⟶ X₁；i j : Fin 2；CategoryTheory.ComposableArrows.Mk₁.obj X₀ X₁ i ⟶ Categor
yTheory.ComposableArrows.Mk₁.obj X₀ X₁ j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map `obj X₀ X₁ i ⟶ obj X₀ X₁ j` whenever `i j : Fin 2` satisfy `i ≤ 
j`.
-/
def map : ∀ (i j : Fin 2) (_ : i ≤ j), obj X₀ X₁ i ⟶ obj X₀ X₁ j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨1, _⟩, ⟨1, _⟩, _ => 𝟙 _
/-
**CategoryTheory.ComposableArrows.Mk₁.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.ComposableArrows.Mk₁`。
形式化陈述：map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _
参数：i : Fin 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_id (i : Fin 2) : map f i i (by simp) = 𝟙 _ :=
  match i with
    | 0 => rfl
    | 1 => rfl
/-
**CategoryTheory.ComposableArrows.Mk₁.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ComposableArrows.Mk₁`。
形式化陈述：map_comp {i j k : Fin 2} (hij : i <= j) (hjk : j <= k) : map f i k (hij.tr
ans hjk) = map f i j hij ≫ map f j k hjk
参数：hij : i <= j；hjk : j <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ComposableArrows.Mk₁.map_id`：map_id (i : Fin 2) : map f i
 i (by simp) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma map_comp {i j k : Fin 2} (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  obtain rfl | rfl : i = j ∨ j = k := by lia
  · rw [map_id, id_comp]
  · rw [map_id, comp_id]

end Mk₁

/-- Constructor for `ComposableArrows C 1`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 1`.
-/
def mk₁ {X₀ X₁ : C} (f : X₀ ⟶ X₁) : ComposableArrows C 1 where
  obj := Mk₁.obj X₀ X₁
  map g := Mk₁.map f _ _ (leOfHom g)
  map_id := Mk₁.map_id f
  map_comp g g' := Mk₁.map_comp f (leOfHom g) (leOfHom g')

/-- Constructor for morphisms `F ⟶ G` in `ComposableArrows C n` which takes as inputs
a family of morphisms `F.obj i ⟶ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms `F ⟶ G` in `ComposableArrows C n` which takes as input
s
a family of morphisms `F.obj i ⟶ G.obj i` and the naturality condition only for 
the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`.
-/
def homMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ⟶ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)) :
    F ⟶ G where
  app := app
  naturality := by
    suffices ∀ (k i j : ℕ) (hj : i + k = j) (hj' : j ≤ n),
        F.map' i j ≫ app _ = app _ ≫ G.map' i j by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have hij' := leOfHom hij
      simp only [Fin.mk_le_mk] at hij'
      obtain ⟨k, hk⟩ := Nat.le.dest hij'
      exact this k i j hk (by valid)
    intro k
    induction k with intro i j hj hj'
    | zero =>
      simp only [add_zero] at hj
      obtain rfl := hj
      rw [F.map'_self i, G.map'_self i, id_comp, comp_id]
    | succ k hk =>
      rw [← add_assoc] at hj
      subst hj
      rw [F.map'_comp i (i + k) (i + k + 1), G.map'_comp i (i + k) (i + k + 1), assoc,
        w (i + k) (by valid), reassoc_of% (hk i (i + k) rfl (by valid))]

/-- Constructor for isomorphisms `F ≅ G` in `ComposableArrows C n` which takes as inputs
a family of isomorphisms `F.obj i ≅ G.obj i` and the naturality condition only for the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms `F ≅ G` in `ComposableArrows C n` which takes as in
puts
a family of isomorphisms `F.obj i ≅ G.obj i` and the naturality condition only f
or the
maps in `Fin (n + 1)` given by inequalities of the form `i ≤ i + 1`.
-/
def isoMk {F G : ComposableArrows C n} (app : ∀ i, F.obj i ≅ G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n),
      F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)) :
    F ≅ G where
  hom := homMk (fun i => (app i).hom) w
  inv := homMk (fun i => (app i).inv) (fun i hi => by
    rw [← cancel_epi ((app _).hom), ← reassoc_of% (w i hi), Iso.hom_inv_id, comp_id,
      Iso.hom_inv_id_assoc])
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext {F G : ComposableArrows C n} (h : ∀ i, F.obj i = G.obj i)
    (w : ∀ (i : ℕ) (hi : i < n), F.map' i (i + 1) =
      eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm) : F = G :=
  Functor.ext_of_iso
    (isoMk (fun i => eqToIso (h i)) (fun i hi => by simp [w i hi])) h

/-- Constructor for morphisms in `ComposableArrows C 0`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 0`.
-/
def homMk₀ {F G : ComposableArrows C 0} (f : F.obj' 0 ⟶ G.obj' 0) : F ⟶ G :=
  homMk (fun i => match i with
    | ⟨0, _⟩ => f) (fun i hi => by simp at hi)

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₀ {F G : ComposableArrows C 0} {φ φ' : F ⟶ G}
    (h : app' φ 0 = app' φ' 0) :
    φ = φ' := by
  ext i
  fin_cases i
  exact h

/-- Constructor for isomorphisms in `ComposableArrows C 0`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 0`.
-/
def isoMk₀ {F G : ComposableArrows C 0} (e : F.obj' 0 ≅ G.obj' 0) : F ≅ G where
  hom := homMk₀ e.hom
  inv := homMk₀ e.inv
/-
**CategoryTheory.ComposableArrows.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_iff₀ {F G : ComposableArrows C 0} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ h 0, fun _ i ↦ by fin_cases i; assumption⟩
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₀ {F G : ComposableArrows C 0} (h : F.obj' 0 = G.obj 0) : F = G :=
  ext (fun i => match i with
    | ⟨0, _⟩ => h) (fun i hi => by simp at hi)
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₀_surjective (F : ComposableArrows C 0) : ∃ (X : C), F = mk₀ X :=
  ⟨F.obj' 0, ext₀ rfl⟩

/-- Constructor for morphisms in `ComposableArrows C 1`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 1`.
-/
def homMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ⟶ G.obj' 0) (right : F.obj' 1 ⟶ G.obj' 1)
    (w : F.map' 0 1 ≫ right = left ≫ G.map' 0 1 := by cat_disch) :
    F ⟶ G :=
  homMk (fun i => match i with
      | ⟨0, _⟩ => left
      | ⟨1, _⟩ => right) (by
          intro i hi
          obtain rfl : i = 0 := by simpa using hi
          exact w)

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₁ {F G : ComposableArrows C 1} {φ φ' : F ⟶ G}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) :
    φ = φ' := by
  ext i
  match i with
    | 0 => exact h₀
    | 1 => exact h₁

/-- Constructor for isomorphisms in `ComposableArrows C 1`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 1`.
-/
def isoMk₁ {F G : ComposableArrows C 1}
    (left : F.obj' 0 ≅ G.obj' 0) (right : F.obj' 1 ≅ G.obj' 1)
    (w : F.map' 0 1 ≫ right.hom = left.hom ≫ G.map' 0 1 := by cat_disch) :
    F ≅ G where
  hom := homMk₁ left.hom right.hom w
  inv := homMk₁ left.inv right.inv (by
    rw [← cancel_mono right.hom, assoc, assoc, w, right.inv_hom_id, left.inv_hom_id_assoc]
    apply comp_id)
/-
**CategoryTheory.ComposableArrows.map'_eq_hom** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map'_eq_hom₁ (F : ComposableArrows C 1) : F.map' 0 1 = F.hom := rfl
/-
**CategoryTheory.ComposableArrows.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_iff₁ {F G : ComposableArrows C 1} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1⟩, fun _ i ↦ by fin_cases i <;> tauto⟩

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₁ {F G : ComposableArrows C 1}
    (left : F.left = G.left) (right : F.right = G.right)
    (w : F.hom = eqToHom left ≫ G.hom ≫ eqToHom right.symm) : F = G :=
  Functor.ext_of_iso (isoMk₁ (eqToIso left) (eqToIso right) (by simp [map'_eq_hom₁, w]))
    (fun i => by fin_cases i <;> assumption)
    (fun i => by fin_cases i <;> rfl)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₁_surjective (X : ComposableArrows C 1) : ∃ (X₀ X₁ : C) (f : X₀ ⟶ X₁), X = mk₁ f :=
  ⟨_, _, X.map' 0 1, ext₁ rfl rfl (by simp)⟩
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₁_eqToHom_comp {X₀' X₀ X₁ : C} (h : X₀' = X₀) (f : X₀ ⟶ X₁) :
    ComposableArrows.mk₁ (eqToHom h ≫ f) = ComposableArrows.mk₁ f := by
  cat_disch
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₁_comp_eqToHom {X₀ X₁ X₁' : C} (f : X₀ ⟶ X₁) (h : X₁ = X₁') :
    ComposableArrows.mk₁ (f ≫ eqToHom h) = ComposableArrows.mk₁ f := by
  cat_disch

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₁_hom (X : ComposableArrows C 1) :
    mk₁ X.hom = X :=
  ext₁ rfl rfl (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The bijection between `ComposableArrows C 1` and `Arrow C`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.arrowEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.ComposableArrows`。
形式化陈述：arrowEquiv : ComposableArrows C 1 ≃ Arrow C where toFun F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection between `ComposableArrows C 1` and `Arrow C`.
-/
def arrowEquiv : ComposableArrows C 1 ≃ Arrow C where
  toFun F := Arrow.mk F.hom
  invFun f := mk₁ f.hom
  left_inv F := ComposableArrows.ext₁ rfl rfl (by simp)
  right_inv _ := rfl

variable (F)

namespace Precomp

variable (X : C)

/-- The map `Fin (n + 1 + 1) → C` which "shifts" `F.obj'` to the right and inserts `X` in
the zeroth position. -/
/-
**CategoryTheory.ComposableArrows.Precomp.obj** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ComposableArrows.Precomp`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {n 
: ℕ} → CategoryTheory.ComposableArrows C n → C → Fin (n + 1 + 1) → C
参数：n + 1 + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Fin (n + 1 + 1) → C` which "shifts" `F.obj'` to the right and inserts `
X` in
the zeroth position.
-/
def obj : Fin (n + 1 + 1) → C
  | ⟨0, _⟩ => X
  | ⟨i + 1, hi⟩ => F.obj' i

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.obj_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ComposableArrows.Precomp`。
形式化陈述：obj_zero : obj F X 0 = X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma obj_zero : obj F X 0 = X := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.obj_one** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ComposableArrows.Precomp`。
形式化陈述：obj_one : obj F X 1 = F.obj' 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma obj_one : obj F X 1 = F.obj' 0 := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.obj_succ** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ComposableArrows.Precomp`。
形式化陈述：obj_succ (i : Nat) (hi : i + 1 < n + 1 + 1) : obj F X ⟨i + 1, hi⟩ = F.obj'
 i
参数：i : Nat；hi : i + 1 < n + 1 + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma obj_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) : obj F X ⟨i + 1, hi⟩ = F.obj' i := rfl

variable {X} (f : X ⟶ F.left)

/-- Auxiliary definition for the action on maps of the functor `F.precomp f`.
It sends `0 ≤ 1` to `f` and `i + 1 ≤ j + 1` to `F.map' i j`. -/
/-
**CategoryTheory.ComposableArrows.Precomp.map** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ComposableArrows.Precomp`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {n 
: ℕ} →       (F : CategoryTheory.ComposableArrows C n) →         {X : C} →      
     (X ⟶ F.left) →             (i j : Fin (n + 1 + 1)) →               i ≤ j → 
                (CategoryTheory.ComposableArrows.Precomp.obj F X i ⟶ CategoryThe
ory.ComposableArrows.Precomp.obj F X j)
参数：F : CategoryTheory.ComposableArrows C n；X ⟶ F.left；i j : Fin (n + 1 + 1)；Cate
goryTheory.ComposableArrows.Precomp.obj F X i ⟶ CategoryTheory.ComposableArrows.
Precomp.obj F X j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the action on maps of the functor `F.precomp f`.
It sends `0 ≤ 1` to `f` and `i + 1 ≤ j + 1` to `F.map' i j`.
-/
def map : ∀ (i j : Fin (n + 1 + 1)) (_ : i ≤ j), obj F X i ⟶ obj F X j
  | ⟨0, _⟩, ⟨0, _⟩, _ => 𝟙 X
  | ⟨0, _⟩, ⟨1, _⟩, _ => f
  | ⟨0, _⟩, ⟨j + 2, hj⟩, _ => f ≫ F.map' 0 (j + 1)
  | ⟨i + 1, hi⟩, ⟨j + 1, hj⟩, hij => F.map' i j (by simpa using hij)

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_zero_zero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_zero_zero : map F f 0 0 (by simp) = 𝟙 X
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_zero_zero : map F f 0 0 (by simp) = 𝟙 X := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_one_one** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_one_one : map F f 1 1 (by simp) = F.map (𝟙 _) := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_zero_one** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_zero_one : map F f 0 1 (by simp) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_zero_one : map F f 0 1 (by simp) = f := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_zero_one'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_zero_one' : map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_zero_one' : map F f 0 ⟨0 + 1, by simp⟩ (by simp) = f := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_zero_succ_succ** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_zero_succ_succ (j : Nat) (hj : j + 2 < n + 1 + 1) : map F f 0 ⟨j + 2, 
hj⟩ (by simp) = f ≫ F.map' 0 (j + 1)
参数：j : Nat；hj : j + 2 < n + 1 + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_zero_succ_succ (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    map F f 0 ⟨j + 2, hj⟩ (by simp) = f ≫ F.map' 0 (j + 1) := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_succ_succ** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_succ_succ (i j : Nat) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1
) (hij : i + 1 <= j + 1) : map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j
参数：i j : Nat；hi : i + 1 < n + 1 + 1；hj : j + 1 < n + 1 + 1；hij : i + 1 <= j + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_succ_succ (i j : ℕ) (hi : i + 1 < n + 1 + 1) (hj : j + 1 < n + 1 + 1)
    (hij : i + 1 ≤ j + 1) :
    map F f ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ hij = F.map' i j := rfl

@[simp]
/-
**CategoryTheory.ComposableArrows.Precomp.map_one_succ** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_one_succ (j : Nat) (hj : j + 1 < n + 1 + 1) : map F f 1 ⟨j + 1, hj⟩ (b
y simp [Fin.le_def]) = F.map' 0 j
参数：j : Nat；hj : j + 1 < n + 1 + 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma map_one_succ (j : ℕ) (hj : j + 1 < n + 1 + 1) :
    map F f 1 ⟨j + 1, hj⟩ (by simp [Fin.le_def]) = F.map' 0 j := rfl
/-
**CategoryTheory.ComposableArrows.Precomp.map_id** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ComposableArrows.Precomp`。
形式化陈述：map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _
参数：i : Fin (n + 1 + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma map_id (i : Fin (n + 1 + 1)) : map F f i i (by simp) = 𝟙 _ := by
  obtain ⟨_ | _, hi⟩ := i <;> simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.Precomp.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ComposableArrows.Precomp`。
形式化陈述：map_comp {i j k : Fin (n + 1 + 1)} (hij : i <= j) (hjk : j <= k) : map F f
 i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk
参数：n + 1 + 1；hij : i <= j；hjk : j <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.mk.congr_simp`：∀ {n : ℕ} (val val_1 : ℕ) (e_val : val = val_1) (isLt
 : val < n), ⟨val, isLt⟩ = ⟨val_1, ⋯⟩
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.instIsBotZeroClass`：∀ {n : ℕ} [inst : NeZero n], IsBotZeroClass (Fin
 n)
· 使用定理 `Fin.instNeZeroHAddNatOfNat_mathlib`：∀ {n m : ℕ} [NeZero n] [inst : NeZer
o (OfNat.ofNat m)], NeZero (OfNat.ofNat m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.one_mod`：∀ (n : ℕ), 1 % (n + 2) = 1
· 使用定理 `Nat.Simproc.add_le_gt`：∀ (a : ℕ) {b c : ℕ}, b > c → (a + b ≤ c) = False
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.homOfLE_comp`：homOfLE_comp {x y z : X} (h : x <= y) (k : 
y <= z) : homOfLE h ≫ homOfLE k = homOfLE (h.trans k)
-/
lemma map_comp {i j k : Fin (n + 1 + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    map F f i k (hij.trans hjk) = map F f i j hij ≫ map F f j k hjk := by
  obtain ⟨i, hi⟩ := i
  obtain ⟨j, hj⟩ := j
  obtain ⟨k, hk⟩ := k
  cases i
  · obtain _ | _ | j := j
    · dsimp
      rw [id_comp]
    · obtain _ | _ | k := k
      · simp at hjk
      · simp
      · rfl
    · obtain _ | _ | k := k
      · simp [Fin.ext_iff] at hjk
      · simp [Fin.le_def] at hjk
      · dsimp
        rw [assoc, ← F.map_comp, homOfLE_comp]
  · obtain _ | j := j
    · simp [Fin.ext_iff] at hij
    · obtain _ | k := k
      · simp [Fin.ext_iff] at hjk
      · dsimp
        rw [← F.map_comp, homOfLE_comp]

end Precomp

/-- "Precomposition" of `F : ComposableArrows C n` by a morphism `f : X ⟶ F.left`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.precomp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ComposableArrows`。
形式化陈述：precomp {X : C} (f : X ⟶ F.left) : ComposableArrows C (n + 1) where obj
参数：f : X ⟶ F.left。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.Precomp.map_id`：map_id (i : Fin (n + 1 +
 1)) : map F f i i (by simp) = 𝟙 _

--- 原说明 ---
"Precomposition" of `F : ComposableArrows C n` by a morphism `f : X ⟶ F.left`.
-/
def precomp {X : C} (f : X ⟶ F.left) : ComposableArrows C (n + 1) where
  obj := Precomp.obj F X
  map g := Precomp.map F f _ _ (leOfHom g)
  map_id := Precomp.map_id F f
  map_comp g g' := Precomp.map_comp F f (leOfHom g) (leOfHom g')

/-- Constructor for `ComposableArrows C 2`. -/
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 2`.
-/
abbrev mk₂ {X₀ X₁ X₂ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) : ComposableArrows C 2 :=
  (mk₁ g).precomp f

/-- Constructor for `ComposableArrows C 3`. -/
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 3`.
-/
abbrev mk₃ {X₀ X₁ X₂ X₃ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) : ComposableArrows C 3 :=
  (mk₂ g h).precomp f

/-- Constructor for `ComposableArrows C 4`. -/
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 4`.
-/
abbrev mk₄ {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄) :
    ComposableArrows C 4 :=
  (mk₃ g h i).precomp f

/-- Constructor for `ComposableArrows C 5`. -/
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory
.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ComposableArrows C 5`.
-/
abbrev mk₅ {X₀ X₁ X₂ X₃ X₄ X₅ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃)
    (i : X₃ ⟶ X₄) (j : X₄ ⟶ X₅) :
    ComposableArrows C 5 :=
  (mk₄ g h i j).precomp f

section

variable {X₀ X₁ X₂ X₃ X₄ : C} (f : X₀ ⟶ X₁) (g : X₁ ⟶ X₂) (h : X₂ ⟶ X₃) (i : X₃ ⟶ X₄)

/-! These examples are meant to test the good definitional properties of `precomp`,
and that `dsimp` can see through. -/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These examples are meant to test the good definitional properties of `precomp`,
and that `dsimp` can see through.
-/
example : map' (mk₂ f g) 0 1 = f := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₂ f g) 1 2 = g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₂ f g) 0 2 = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (mk₂ f g).hom = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₂ f g) 0 0 = 𝟙 _ := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₂ f g) 1 1 = 𝟙 _ := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₂ f g) 2 2 = 𝟙 _ := by dsimp

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 0 1 = f := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 1 2 = g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 2 3 = h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 0 3 = f ≫ g ≫ h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (mk₃ f g h).hom = f ≫ g ≫ h := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 0 2 = f ≫ g := by dsimp
set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map' (mk₃ f g h) 1 3 = g ≫ h := by dsimp

end

/-- The map `ComposableArrows C m → ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.whiskerLeft** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.ComposableArrows`。
形式化陈述：whiskerLeft (F : ComposableArrows C m) (Φ : Fin (n + 1) ⥤ Fin (m + 1)) : C
omposableArrows C n
参数：F : ComposableArrows C m；Φ : Fin (n + 1) ⥤ Fin (m + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ComposableArrows C m → ComposableArrows C n` obtained by precomposition
 with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`.
-/
def whiskerLeft (F : ComposableArrows C m) (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C n := Φ ⋙ F

/-- The functor `ComposableArrows C m ⥤ ComposableArrows C n` obtained by precomposition with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.whiskerLeftFunctor** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.ComposableArrows`。
形式化陈述：whiskerLeftFunctor (Φ : Fin (n + 1) ⥤ Fin (m + 1)) : ComposableArrows C m 
⥤ ComposableArrows C n where obj F
参数：Φ : Fin (n + 1) ⥤ Fin (m + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C m ⥤ ComposableArrows C n` obtained by precomposi
tion with
a functor `Fin (n + 1) ⥤ Fin (m + 1)`.
-/
def whiskerLeftFunctor (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    ComposableArrows C m ⥤ ComposableArrows C n where
  obj F := F.whiskerLeft Φ
  map f := Functor.whiskerLeft Φ f

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.succ`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows._root_.Fin.succFunctor** 是 Mathlib 中的一个定义，位于命名
空间 `CategoryTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.succ`.
-/
def _root_.Fin.succFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.succ
  map {_ _} hij := homOfLE (Fin.succ_le_succ_iff.2 (leOfHom hij))

/-- The functor `Fin (l + 1) ⥤ Fin (n + 1)` which sends `i` to `k + i` -/
@[simps!]
/-
**CategoryTheory.ComposableArrows._root_.Fin.natAddLEFunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Fin (l + 1) ⥤ Fin (n + 1)` which sends `i` to `k + i`
-/
def _root_.Fin.natAddLEFunctor {n k l : ℕ} (h : k + l ≤ n) : Fin (l + 1) ⥤ Fin (n + 1) where
  obj := fun ⟨i, _⟩ => ⟨k + i , by lia⟩
  map {_ _} hij := homOfLE (by rw [Fin.le_iff_val_le_val]; simpa using (leOfHom hij))

/-- The functor `ComposableArrows C n ⥤ ComposableArrows C l` obtained by precomposition with
the functor `Fin.natAddLEFunctor`. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.natAddLEFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.ComposableArrows`。
形式化陈述：natAddLEFunctor {n k l : Nat} (h : k + l <= n) : ComposableArrows C n ⥤ Co
mposableArrows C l
参数：h : k + l <= n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C n ⥤ ComposableArrows C l` obtained by precomposi
tion with
the functor `Fin.natAddLEFunctor`.
-/
def natAddLEFunctor {n k l : ℕ} (h : k + l ≤ n) :
    ComposableArrows C n ⥤ ComposableArrows C l :=
  whiskerLeftFunctor (Fin.natAddLEFunctor h)
/-
**CategoryTheory.ComposableArrows.natAddLEFunctor_obj'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows`。
形式化陈述：natAddLEFunctor_obj' {n k l i : Nat} (h : k + l <= n) (R : ComposableArrow
s C n) (_ : i <= l
参数：h : k + l <= n；R : ComposableArrows C n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natAddLEFunctor_obj' {n k l i : ℕ} (h : k + l ≤ n) (R : ComposableArrows C n)
    (_ : i ≤ l := by lia) :
    ((natAddLEFunctor h).obj R).obj' i = R.obj' (k + i) := rfl
/-
**CategoryTheory.ComposableArrows.natAddLEFunctor_app'** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows`。
形式化陈述：natAddLEFunctor_app' {n k l i : Nat} (h : k + l <= n) {R₁ R₂ : ComposableA
rrows C n} (φ : R₁ ⟶ R₂) (_ : i <= l
参数：h : k + l <= n；φ : R₁ ⟶ R₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natAddLEFunctor_app' {n k l i : ℕ} (h : k + l ≤ n) {R₁ R₂ : ComposableArrows C n}
    (φ : R₁ ⟶ R₂) (_ : i ≤ l := by lia) :
    app' ((natAddLEFunctor h).map φ) i = app' φ (k + i) := rfl

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the first arrow. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the first arrow.
-/
def δ₀Functor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.succFunctor (n + 1))

/-- The `ComposableArrows C n` obtained by forgetting the first arrow. -/
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ComposableArrows C n` obtained by forgetting the first arrow.
-/
abbrev δ₀ (F : ComposableArrows C (n + 1)) := δ₀Functor.obj F

@[simp]
/-
**CategoryTheory.ComposableArrows.precomp_** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma precomp_δ₀ {X : C} (f : X ⟶ F.left) : (F.precomp f).δ₀ = F := rfl

/-- The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.castSucc`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows._root_.Fin.castSuccFunctor** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `Fin n ⥤ Fin (n + 1)` which sends `i` to `i.castSucc`.
-/
def _root_.Fin.castSuccFunctor (n : ℕ) : Fin n ⥤ Fin (n + 1) where
  obj i := i.castSucc
  map hij := hij

/-- The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the last arrow. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Com
posableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C (n + 1) ⥤ ComposableArrows C n` which forgets
the last arrow.
-/
def δlastFunctor : ComposableArrows C (n + 1) ⥤ ComposableArrows C n :=
  whiskerLeftFunctor (Fin.castSuccFunctor (n + 1))

/-- The `ComposableArrows C n` obtained by forgetting the first arrow. -/
/-
**CategoryTheory.ComposableArrows.** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ComposableArrows C n` obtained by forgetting the first arrow.
-/
abbrev δlast (F : ComposableArrows C (n + 1)) := δlastFunctor.obj F

section

variable {F G : ComposableArrows C (n + 1)}


/-- Inductive construction of morphisms in `ComposableArrows C (n + 1)`: in order to construct
a morphism `F ⟶ G`, it suffices to provide `α : F.obj' 0 ⟶ G.obj' 0` and `β : F.δ₀ ⟶ G.δ₀`
such that `F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1`. -/
/-
**CategoryTheory.ComposableArrows.homMkSucc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：homMkSucc (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀) (w : F.map' 0 1 ≫ ap
p' β 0 = α ≫ G.map' 0 1) : F ⟶ G
参数：α : F.obj' 0 ⟶ G.obj' 0；β : F.δ₀ ⟶ G.δ₀；w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map
' 0 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductive construction of morphisms in `ComposableArrows C (n + 1)`: in order to
 construct
a morphism `F ⟶ G`, it suffices to provide `α : F.obj' 0 ⟶ G.obj' 0` and `β : F.
δ₀ ⟶ G.δ₀`
such that `F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1`.
-/
def homMkSucc (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
    (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1) : F ⟶ G :=
  homMk
    (fun i => match i with
      | ⟨0, _⟩ => α
      | ⟨i + 1, hi⟩ => app' β i)
    (fun i hi => by
      obtain _ | i := i
      · exact w
      · exact naturality' β i (i + 1))

variable (α : F.obj' 0 ⟶ G.obj' 0) (β : F.δ₀ ⟶ G.δ₀)
  (w : F.map' 0 1 ≫ app' β 0 = α ≫ G.map' 0 1 := by cat_disch)

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMkSucc_app_zero** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ComposableArrows`。
形式化陈述：homMkSucc_app_zero : (homMkSucc α β w).app 0 = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma homMkSucc_app_zero : (homMkSucc α β w).app 0 = α := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMkSucc_app_succ** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ComposableArrows`。
形式化陈述：homMkSucc_app_succ (i : Nat) (hi : i + 1 < n + 1 + 1) : (homMkSucc α β w).
app ⟨i + 1, hi⟩ = app' β i
参数：i : Nat；hi : i + 1 < n + 1 + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMkSucc_app_succ (i : ℕ) (hi : i + 1 < n + 1 + 1) :
    (homMkSucc α β w).app ⟨i + 1, hi⟩ = app' β i := rfl

end

/-
**CategoryTheory.ComposableArrows.hom_ext_succ** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ComposableArrows`。
形式化陈述：hom_ext_succ {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G} (h₀ : app' f
 0 = app' g 0) (h₁ : δ₀Functor.map f = δ₀Functor.map g) : f = g
参数：n + 1；h₀ : app' f 0 = app' g 0；h₁ : δ₀Functor.map f = δ₀Functor.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.congr_app`：congr_app {F G : C ⥤ D} {α β : NatTrans F G} (
h : α = β) (X : C) : α.app X = β.app X
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma hom_ext_succ {F G : ComposableArrows C (n + 1)} {f g : F ⟶ G}
    (h₀ : app' f 0 = app' g 0) (h₁ : δ₀Functor.map f = δ₀Functor.map g) : f = g := by
  ext ⟨i, hi⟩
  obtain _ | i := i
  · exact h₀
  · exact congr_app h₁ ⟨i, by valid⟩

set_option backward.isDefEq.respectTransparency false in
/-- Inductive construction of isomorphisms in `ComposableArrows C (n + 1)`: in order to
construct an isomorphism `F ≅ G`, it suffices to provide `α : F.obj' 0 ≅ G.obj' 0` and
`β : F.δ₀ ≅ G.δ₀` such that `F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMkSucc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.ComposableArrows`。
形式化陈述：isoMkSucc {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0) (β 
: F.δ₀ ≅ G.δ₀) (w : F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1) : F ≅ G wher
e hom
参数：n + 1；α : F.obj' 0 ≅ G.obj' 0；β : F.δ₀ ≅ G.δ₀；w : F.map' 0 1 ≫ app' β.hom 0 =
 α.hom ≫ G.map' 0 1。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inductive construction of isomorphisms in `ComposableArrows C (n + 1)`: in order
 to
construct an isomorphism `F ≅ G`, it suffices to provide `α : F.obj' 0 ≅ G.obj' 
0` and
`β : F.δ₀ ≅ G.δ₀` such that `F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1`.
-/
def isoMkSucc {F G : ComposableArrows C (n + 1)} (α : F.obj' 0 ≅ G.obj' 0)
    (β : F.δ₀ ≅ G.δ₀) (w : F.map' 0 1 ≫ app' β.hom 0 = α.hom ≫ G.map' 0 1) : F ≅ G where
  hom := homMkSucc α.hom β.hom w
  inv := homMkSucc α.inv β.inv (by
    rw [← cancel_epi α.hom, ← reassoc_of% w, α.hom_inv_id_assoc, β.hom_inv_id_app]
    dsimp
    rw [comp_id])
  hom_inv_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp
  inv_hom_id := by
    apply hom_ext_succ
    · simp
    · ext ⟨i, hi⟩
      simp

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.ext_succ** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.ComposableArrows`。
形式化陈述：ext_succ {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0) (h 
: F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫ eqToHom (Functor.cong
r_obj h.symm 0)) : F = G
参数：n + 1；h₀ : F.obj' 0 = G.obj' 0；h : F.δ₀ = G.δ₀；w : F.map' 0 1 = eqToHom h₀ ≫ 
G.map' 0 1 ≫ eqToHom (Functor.congr_obj h.symm 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_app`：eqToHom_app {F G : C ⥤ D} (h : F = G) (X : C
) : (eqToHom h : F ⟶ G).app X = eqToHom (Functor.congr_obj h X)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma ext_succ {F G : ComposableArrows C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0)
    (h : F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqToHom h₀ ≫ G.map' 0 1 ≫
      eqToHom (Functor.congr_obj h.symm 0)) : F = G := by
  have : ∀ i, F.obj i = G.obj i := by
    intro ⟨i, hi⟩
    rcases i with - | i
    · exact h₀
    · exact Functor.congr_obj h ⟨i, by valid⟩
  exact Functor.ext_of_iso (isoMkSucc (eqToIso h₀) (eqToIso h) (by
      rw [w]
      dsimp [app']
      rw [eqToHom_app, assoc, assoc, eqToHom_trans, eqToHom_refl, comp_id])) this
    (by rintro ⟨_ | _, hi⟩ <;> simp)

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.precomp_surjective** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ComposableArrows`。
形式化陈述：precomp_surjective (F : ComposableArrows C (n + 1)) : exists (F₀ : Composa
bleArrows C n) (X₀ : C) (f₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀
参数：F : ComposableArrows C (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `CategoryTheory.ComposableArrows.ext_succ`：ext_succ {F G : ComposableArro
ws C (n + 1)} (h₀ : F.obj' 0 = G.obj' 0) (h : F.δ₀ = G.δ₀) (w : F.map' 0 1 = eqT
oHom h₀ ≫ G.map' 0 1 ≫ eqToHom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `CategoryTheory.Functor.congr_obj`：congr_obj {F G : C ⥤ D} (h : F = G) (X
) : F.obj X = G.obj X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma precomp_surjective (F : ComposableArrows C (n + 1)) :
    ∃ (F₀ : ComposableArrows C n) (X₀ : C) (f₀ : X₀ ⟶ F₀.left), F = F₀.precomp f₀ :=
  ⟨F.δ₀, _, F.map' 0 1, ext_succ rfl (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for morphisms in `ComposableArrows C 2`. -/
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 2`.
-/
def homMk₂ : f ⟶ g := homMkSucc app₀ (homMk₁ app₁ app₂ w₁) w₀

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₂_app_zero : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₂_app_one : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₂_app_two : (homMk₂ app₀ app₁ app₂ w₀ w₁).app 2 = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₂_app_two' : (homMk₂ app₀ app₁ app₂ w₀ w₁).app ⟨2, by valid⟩ = app₂ := rfl

end

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₂ {f g : ComposableArrows C 2} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₁ h₁ h₂)

/-- Constructor for isomorphisms in `ComposableArrows C 2`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 2`.
-/
def isoMk₂ {f g : ComposableArrows C 2}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1 := by cat_disch)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2 := by cat_disch) : f ≅ g where
  hom := homMk₂ app₀.hom app₁.hom app₂.hom w₀ w₁
  inv := homMk₂ app₀.inv app₁.inv app₂.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
/-
**CategoryTheory.ComposableArrows.isIso_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isIso_iff₂ {F G : ComposableArrows C 2} (f : F ⟶ G) :
    IsIso f ↔ IsIso (f.app 0) ∧ IsIso (f.app 1) ∧ IsIso (f.app 2) := by
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h ↦ ⟨h 0, h 1, h 2⟩, fun _ i ↦ by fin_cases i <;> tauto⟩
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₂ {f g : ComposableArrows C 2}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm) : f = g :=
  ext_succ h₀ (ext₁ h₁ h₂ w₁) w₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₂_surjective (X : ComposableArrows C 2) :
    ∃ (X₀ X₁ X₂ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂), X = mk₂ f₀ f₁ :=
  ⟨_, _, _, X.map' 0 1, X.map' 1 2, ext₂ rfl rfl rfl (by simp) (by simp)⟩
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₂_of_arrow {f g : ComposableArrows C 2}
    (h₀₁ : Arrow.mk (f.map' 0 1) = Arrow.mk (g.map' 0 1))
    (h₁₂ : Arrow.mk (f.map' 1 2) = Arrow.mk (g.map' 1 2)) : f = g := by
  obtain ⟨x₀, x₁, x₂, f, f', rfl⟩ := mk₂_surjective f
  obtain ⟨y₀, y₁, y₂, g, g', rfl⟩ := mk₂_surjective g
  obtain rfl : x₀ = y₀ := congr_arg Arrow.leftFunc.obj h₀₁
  obtain rfl : x₁ = y₁ := congr_arg Arrow.rightFunc.obj h₀₁
  obtain rfl : x₂ = y₂ := congr_arg Arrow.rightFunc.obj h₁₂
  obtain rfl : f = g := by rwa [← Arrow.mk_inj]
  obtain rfl : f' = g' := by rwa [← Arrow.mk_inj]
  rfl

section

variable
  {f g : ComposableArrows C 3}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for morphisms in `ComposableArrows C 3`. -/
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 3`.
-/
def homMk₃ : f ⟶ g := homMkSucc app₀ (homMk₂ app₁ app₂ app₃ w₁ w₂) w₀

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₃_app_zero : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₃_app_one : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₃_app_two : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨2, by valid⟩ = app₂ :=
  rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₃_app_three : (homMk₃ app₀ app₁ app₂ app₃ w₀ w₁ w₂).app ⟨3, by valid⟩ = app₃ :=
  rfl

end

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₃ {f g : ComposableArrows C 3} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₂ h₁ h₂ h₃)

/-- Constructor for isomorphisms in `ComposableArrows C 3`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 3`.
-/
def isoMk₃ {f g : ComposableArrows C 3}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3) : f ≅ g where
  hom := homMk₃ app₀.hom app₁.hom app₂.hom app₃.hom w₀ w₁ w₂
  inv := homMk₃ app₀.inv app₁.inv app₂.inv app₃.inv
    (by rw [← cancel_epi app₀.hom, ← reassoc_of% w₀, app₁.hom_inv_id,
      comp_id, app₀.hom_inv_id_assoc])
    (by rw [← cancel_epi app₁.hom, ← reassoc_of% w₁, app₂.hom_inv_id,
      comp_id, app₁.hom_inv_id_assoc])
    (by rw [← cancel_epi app₂.hom, ← reassoc_of% w₂, app₃.hom_inv_id,
      comp_id, app₂.hom_inv_id_assoc])
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₃ {f g : ComposableArrows C 3}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm) : f = g :=
  ext_succ h₀ (ext₂ h₁ h₂ h₃ w₁ w₂) w₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₃_surjective (X : ComposableArrows C 3) :
    ∃ (X₀ X₁ X₂ X₃ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃), X = mk₃ f₀ f₁ f₂ :=
  ⟨_, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3,
    ext₃ rfl rfl rfl rfl (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 4}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for morphisms in `ComposableArrows C 4`. -/
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 4`.
-/
def homMk₄ : f ⟶ g := homMkSucc app₀ (homMk₃ app₁ app₂ app₃ app₄ w₁ w₂ w₃) w₀

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₄_app_zero : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₄_app_one : (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₄_app_two :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨2, by valid⟩ = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₄_app_three :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨3, by valid⟩ = app₃ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₄_app_four :
    (homMk₄ app₀ app₁ app₂ app₃ app₄ w₀ w₁ w₂ w₃).app ⟨4, by valid⟩ = app₄ := rfl

end

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₄ {f g : ComposableArrows C 4} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₃ h₁ h₂ h₃ h₄)
/-
**CategoryTheory.ComposableArrows.map'_inv_eq_inv_map'** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ComposableArrows`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {n m : ℕ} (
h : n + 1 ≤ m)   {f g : CategoryTheory.ComposableArrows C m} (app : f.obj' n ⋯ ≅
 g.obj' n ⋯)   (app' : f.obj' (n + 1) h ≅ g.obj' (n + 1) h),   CategoryTheory.Ca
tegoryStruct.comp (f.map' n (n + 1) ⋯ h) app'.hom =       CategoryTheory.Categor
yStruct.comp app.hom (g.map' n (n + 1) ⋯ h) →     CategoryTheory.CategoryStruct.
comp (g.map' n (n + 1) ⋯ h) app'.inv =       CategoryTheory.CategoryStruct.comp 
app.inv (f.map' n (n + 1) ⋯ h)
参数：h : n + 1 ≤ m；app : f.obj' n ⋯ ≅ g.obj' n ⋯；app' : f.obj' (n + 1) h ≅ g.obj' 
(n + 1) h；f.map' n (n + 1) ⋯ h；g.map' n (n + 1) ⋯ h；g.map' n (n + 1) ⋯ h；f.map' 
n (n + 1) ⋯ h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.IsIso.epi_of_iso`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],   CategoryTheo
ry.Epi f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma map'_inv_eq_inv_map' {n m : ℕ} (h : n + 1 ≤ m) {f g : ComposableArrows C m}
    (app : f.obj' n ≅ g.obj' n) (app' : f.obj' (n + 1) ≅ g.obj' (n + 1))
    (w : f.map' n (n + 1) ≫ app'.hom = app.hom ≫ g.map' n (n + 1)) :
    map' g n (n + 1) ≫ app'.inv = app.inv ≫ map' f n (n + 1) := by
  rw [← cancel_epi app.hom, ← reassoc_of% w, app'.hom_inv_id, comp_id, app.hom_inv_id_assoc]

/-- Constructor for isomorphisms in `ComposableArrows C 4`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 4`.
-/
def isoMk₄ {f g : ComposableArrows C 4}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4) :
    f ≅ g where
  hom := homMk₄ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom w₀ w₁ w₂ w₃
  inv := homMk₄ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₄ {f g : ComposableArrows C 4}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm) :
    f = g :=
  ext_succ h₀ (ext₃ h₁ h₂ h₃ h₄ w₁ w₂ w₃) w₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₄_surjective (X : ComposableArrows C 4) :
    ∃ (X₀ X₁ X₂ X₃ X₄ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) (f₃ : X₃ ⟶ X₄),
      X = mk₄ f₀ f₁ f₂ f₃ :=
  ⟨_, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4,
    ext₄ rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp)⟩

section

variable
  {f g : ComposableArrows C 5}
  (app₀ : f.obj' 0 ⟶ g.obj' 0) (app₁ : f.obj' 1 ⟶ g.obj' 1) (app₂ : f.obj' 2 ⟶ g.obj' 2)
  (app₃ : f.obj' 3 ⟶ g.obj' 3) (app₄ : f.obj' 4 ⟶ g.obj' 4) (app₅ : f.obj' 5 ⟶ g.obj' 5)
  (w₀ : f.map' 0 1 ≫ app₁ = app₀ ≫ g.map' 0 1 := by cat_disch)
  (w₁ : f.map' 1 2 ≫ app₂ = app₁ ≫ g.map' 1 2 := by cat_disch)
  (w₂ : f.map' 2 3 ≫ app₃ = app₂ ≫ g.map' 2 3 := by cat_disch)
  (w₃ : f.map' 3 4 ≫ app₄ = app₃ ≫ g.map' 3 4 := by cat_disch)
  (w₄ : f.map' 4 5 ≫ app₅ = app₄ ≫ g.map' 4 5 := by cat_disch)

set_option backward.privateInPublic true in
/-- Constructor for morphisms in `ComposableArrows C 5`. -/
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for morphisms in `ComposableArrows C 5`.
-/
def homMk₅ : f ⟶ g := homMkSucc app₀ (homMk₄ app₁ app₂ app₃ app₄ app₅ w₁ w₂ w₃ w₄) w₀

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_zero : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 0 = app₀ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_one : (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app 1 = app₁ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_two :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨2, by valid⟩ = app₂ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_three :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨3, by valid⟩ = app₃ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_four :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨4, by valid⟩ = app₄ := rfl

set_option backward.privateInPublic true in
@[simp]
/-
**CategoryTheory.ComposableArrows.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：homMk {F G : ComposableArrows C n} (app : forall i, F.obj i ⟶ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ app _ = app _ ≫ G.map' i (i 
+ 1)) : F ⟶ G where app
参数：app : forall i, F.obj i ⟶ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ app _ = app _ ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homMk₅_app_five :
    (homMk₅ app₀ app₁ app₂ app₃ app₄ app₅ w₀ w₁ w₂ w₃ w₄).app ⟨5, by valid⟩ = app₅ := rfl

end

@[ext]
/-
**CategoryTheory.ComposableArrows.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.ComposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_ext₅ {f g : ComposableArrows C 5} {φ φ' : f ⟶ g}
    (h₀ : app' φ 0 = app' φ' 0) (h₁ : app' φ 1 = app' φ' 1) (h₂ : app' φ 2 = app' φ' 2)
    (h₃ : app' φ 3 = app' φ' 3) (h₄ : app' φ 4 = app' φ' 4) (h₅ : app' φ 5 = app' φ' 5) :
    φ = φ' :=
  hom_ext_succ h₀ (hom_ext₄ h₁ h₂ h₃ h₄ h₅)

/-- Constructor for isomorphisms in `ComposableArrows C 5`. -/
@[simps]
/-
**CategoryTheory.ComposableArrows.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：isoMk {F G : ComposableArrows C n} (app : forall i, F.obj i ≅ G.obj i) (w 
: forall (i : Nat) (hi : i < n), F.map' i (i + 1) ≫ (app _).hom = (app _).hom ≫ 
G.map' i (i + 1)) : F ≅ G where hom
参数：app : forall i, F.obj i ≅ G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i
 (i + 1) ≫ (app _).hom = (app _).hom ≫ G.map' i (i + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for isomorphisms in `ComposableArrows C 5`.
-/
def isoMk₅ {f g : ComposableArrows C 5}
    (app₀ : f.obj' 0 ≅ g.obj' 0) (app₁ : f.obj' 1 ≅ g.obj' 1) (app₂ : f.obj' 2 ≅ g.obj' 2)
    (app₃ : f.obj' 3 ≅ g.obj' 3) (app₄ : f.obj' 4 ≅ g.obj' 4) (app₅ : f.obj' 5 ≅ g.obj' 5)
    (w₀ : f.map' 0 1 ≫ app₁.hom = app₀.hom ≫ g.map' 0 1)
    (w₁ : f.map' 1 2 ≫ app₂.hom = app₁.hom ≫ g.map' 1 2)
    (w₂ : f.map' 2 3 ≫ app₃.hom = app₂.hom ≫ g.map' 2 3)
    (w₃ : f.map' 3 4 ≫ app₄.hom = app₃.hom ≫ g.map' 3 4)
    (w₄ : f.map' 4 5 ≫ app₅.hom = app₄.hom ≫ g.map' 4 5) :
    f ≅ g where
  hom := homMk₅ app₀.hom app₁.hom app₂.hom app₃.hom app₄.hom app₅.hom w₀ w₁ w₂ w₃ w₄
  inv := homMk₅ app₀.inv app₁.inv app₂.inv app₃.inv app₄.inv app₅.inv
    (by rw [map'_inv_eq_inv_map' (by valid) app₀ app₁ w₀])
    (by rw [map'_inv_eq_inv_map' (by valid) app₁ app₂ w₁])
    (by rw [map'_inv_eq_inv_map' (by valid) app₂ app₃ w₂])
    (by rw [map'_inv_eq_inv_map' (by valid) app₃ app₄ w₃])
    (by rw [map'_inv_eq_inv_map' (by valid) app₄ app₅ w₄])
/-
**CategoryTheory.ComposableArrows.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
ComposableArrows`。
形式化陈述：ext {F G : ComposableArrows C n} (h : forall i, F.obj i = G.obj i) (w : fo
rall (i : Nat) (hi : i < n), F.map' i (i + 1) = eqToHom (h _) ≫ G.map' i (i + 1)
 ≫ eqToHom (h _).symm) : F = G
参数：h : forall i, F.obj i = G.obj i；w : forall (i : Nat) (hi : i < n), F.map' i (
i + 1) = eqToHom (h _) ≫ G.map' i (i + 1) ≫ eqToHom (h _).symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.ext_of_iso`：ext_of_iso {F G : C ⥤ D} (e : F ≅ G) 
(hobj : forall X, F.obj X = G.obj X) (happ : forall X, e.hom.app X = eqToHom (ho
bj X)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ext₅ {f g : ComposableArrows C 5}
    (h₀ : f.obj' 0 = g.obj' 0) (h₁ : f.obj' 1 = g.obj' 1) (h₂ : f.obj' 2 = g.obj' 2)
    (h₃ : f.obj' 3 = g.obj' 3) (h₄ : f.obj' 4 = g.obj' 4) (h₅ : f.obj' 5 = g.obj' 5)
    (w₀ : f.map' 0 1 = eqToHom h₀ ≫ g.map' 0 1 ≫ eqToHom h₁.symm)
    (w₁ : f.map' 1 2 = eqToHom h₁ ≫ g.map' 1 2 ≫ eqToHom h₂.symm)
    (w₂ : f.map' 2 3 = eqToHom h₂ ≫ g.map' 2 3 ≫ eqToHom h₃.symm)
    (w₃ : f.map' 3 4 = eqToHom h₃ ≫ g.map' 3 4 ≫ eqToHom h₄.symm)
    (w₄ : f.map' 4 5 = eqToHom h₄ ≫ g.map' 4 5 ≫ eqToHom h₅.symm) :
    f = g :=
  ext_succ h₀ (ext₄ h₁ h₂ h₃ h₄ h₅ w₁ w₂ w₃ w₄) w₀

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ComposableArrows.mk** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.C
omposableArrows`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk₅_surjective (X : ComposableArrows C 5) :
    ∃ (X₀ X₁ X₂ X₃ X₄ X₅ : C) (f₀ : X₀ ⟶ X₁) (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃)
      (f₃ : X₃ ⟶ X₄) (f₄ : X₄ ⟶ X₅), X = mk₅ f₀ f₁ f₂ f₃ f₄ :=
  ⟨_, _, _, _, _, _, X.map' 0 1, X.map' 1 2, X.map' 2 3, X.map' 3 4, X.map' 4 5,
    ext₅ rfl rfl rfl rfl rfl rfl (by simp) (by simp) (by simp) (by simp) (by simp)⟩

/-- The `i`th arrow of `F : ComposableArrows C n`. -/
/-
**CategoryTheory.ComposableArrows.arrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ComposableArrows`。
形式化陈述：arrow (i : Nat) (hi : i < n
参数：i : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `i`th arrow of `F : ComposableArrows C n`.
-/
def arrow (i : ℕ) (hi : i < n := by valid) :
    ComposableArrows C 1 := mk₁ (F.map' i (i + 1))

section mkOfObjOfMapSucc

variable (obj : Fin (n + 1) → C) (mapSucc : ∀ (i : Fin n), obj i.castSucc ⟶ obj i.succ)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_exists** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.ComposableArrows`。
形式化陈述：mkOfObjOfMapSucc_exists : exists (F : ComposableArrows C n) (e : forall i,
 F.obj i ≅ obj i), forall (i : Nat) (hi : i < n), mapSucc ⟨i, hi⟩ = (e ⟨i, _⟩).i
nv ≫ F.map' i (i + 1) ≫ (e ⟨i + 1, _⟩).hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
-/
lemma mkOfObjOfMapSucc_exists : ∃ (F : ComposableArrows C n) (e : ∀ i, F.obj i ≅ obj i),
    ∀ (i : ℕ) (hi : i < n), mapSucc ⟨i, hi⟩ =
      (e ⟨i, _⟩).inv ≫ F.map' i (i + 1) ≫ (e ⟨i + 1, _⟩).hom := by
  induction n with
  | zero => exact ⟨mk₀ (obj 0), fun 0 => Iso.refl _, fun i hi => by simp at hi⟩
  | succ n hn =>
    obtain ⟨F, e, h⟩ := hn (fun i => obj i.succ) (fun i => mapSucc i.succ)
    refine ⟨F.precomp (mapSucc 0 ≫ (e 0).inv), fun i => match i with
      | 0 => Iso.refl _
      | ⟨i + 1, hi⟩ => e _, fun i hi => ?_⟩
    obtain _ | i := i
    · simp
    · exact h i (by valid)

/-- Given `obj : Fin (n + 1) → C` and `mapSucc i : obj i.castSucc ⟶ obj i.succ`
for all `i : Fin n`, this is `F : ComposableArrows C n` such that `F.obj i` is
definitionally equal to `obj i` and such that `F.map' i (i + 1) = mapSucc ⟨i, hi⟩`. -/
/-
**CategoryTheory.ComposableArrows.mkOfObjOfMapSucc** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ComposableArrows`。
形式化陈述：mkOfObjOfMapSucc : ComposableArrows C n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_exists`：mkOfObjOfMapSuc
c_exists : exists (F : ComposableArrows C n) (e : forall i, F.obj i ≅ obj i), fo
rall (i : Nat) (hi : i < n), mapSucc ⟨i, hi⟩ …

--- 原说明 ---
Given `obj : Fin (n + 1) → C` and `mapSucc i : obj i.castSucc ⟶ obj i.succ`
for all `i : Fin n`, this is `F : ComposableArrows C n` such that `F.obj i` is
definitionally equal to `obj i` and such that `F.map' i (i + 1) = mapSucc ⟨i, hi
⟩`.
-/
noncomputable def mkOfObjOfMapSucc : ComposableArrows C n :=
  (mkOfObjOfMapSucc_exists obj mapSucc).choose.copyObj obj
    (mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose

@[simp]
/-
**CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_obj** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ComposableArrows`。
形式化陈述：mkOfObjOfMapSucc_obj (i : Fin (n + 1)) : (mkOfObjOfMapSucc obj mapSucc).ob
j i = obj i
参数：i : Fin (n + 1)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mkOfObjOfMapSucc_obj (i : Fin (n + 1)) :
    (mkOfObjOfMapSucc obj mapSucc).obj i = obj i := rfl
/-
**CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_map_succ** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ComposableArrows`。
形式化陈述：mkOfObjOfMapSucc_map_succ (i : Nat) (hi : i < n
参数：i : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_exists`：mkOfObjOfMapSuc
c_exists : exists (F : ComposableArrows C n) (e : forall i, F.obj i ≅ obj i), fo
rall (i : Nat) (hi : i < n), mapSucc ⟨i, hi⟩ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma mkOfObjOfMapSucc_map_succ (i : ℕ) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).map' i (i + 1) = mapSucc ⟨i, hi⟩ :=
  ((mkOfObjOfMapSucc_exists obj mapSucc).choose_spec.choose_spec i hi).symm

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_arrow** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ComposableArrows`。
形式化陈述：mkOfObjOfMapSucc_arrow (i : Nat) (hi : i < n
参数：i : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ComposableArrows.ext₁`：ext₁ {F G : ComposableArrows C 1} 
(left : F.left = G.left) (right : F.right = G.right) (w : F.hom = eqToHom left ≫
 G.hom ≫ eqToHom right.sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_succ_of_lt`：∀ {a b : ℕ}, a < b → a < b.succ
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Nat.succ_lt_succ`：∀ {n m : ℕ}, n < m → n.succ < m.succ
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `CategoryTheory.ComposableArrows.mkOfObjOfMapSucc_map_succ`：mkOfObjOfMapS
ucc_map_succ (i : Nat) (hi : i < n
-/
lemma mkOfObjOfMapSucc_arrow (i : ℕ) (hi : i < n := by valid) :
    (mkOfObjOfMapSucc obj mapSucc).arrow i = mk₁ (mapSucc ⟨i, hi⟩) :=
  ext₁ rfl rfl (by simpa using! mkOfObjOfMapSucc_map_succ obj mapSucc i hi)

end mkOfObjOfMapSucc

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
suppress_compilation in
variable (C n) in
/-- The equivalence `(ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n` obtained
by reversing the arrows. -/
@[simps!]
/-
**CategoryTheory.ComposableArrows.opEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Categ
oryTheory.ComposableArrows`。
形式化陈述：opEquivalence : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `(ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n` obtained
by reversing the arrows.
-/
def opEquivalence : (ComposableArrows C n)ᵒᵖ ≌ ComposableArrows Cᵒᵖ n :=
  ((orderDualEquivalence (Fin (n + 1))).symm.trans
      Fin.revOrderIso.equivalence).symm.congrLeft.op.trans
    (Functor.leftOpRightOpEquiv (Fin (n + 1)) C)

end ComposableArrows

section

open ComposableArrows

variable {C} {D : Type*} [Category* D] (G : C ⥤ D) (n : ℕ)

/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` obtained by postcomposition
with a functor `C ⥤ D`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapComposableArrows** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D →           (n : ℕ) → CategoryTheory.Functor (CategoryT
heory.ComposableArrows C n) (CategoryTheory.ComposableArrows D n)
参数：n : ℕ；CategoryTheory.ComposableArrows C n；CategoryTheory.ComposableArrows D n
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C n ⥤ ComposableArrows D n` obtained by postcompos
ition
with a functor `C ⥤ D`.
-/
def Functor.mapComposableArrows :
    ComposableArrows C n ⥤ ComposableArrows D n :=
  (whiskeringRight _ _ _).obj G

/-- The isomorphism between `(G.mapComposableArrows 1).obj (.mk₁ f)` and
`.mk₁ (G.map f)`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapComposableArrowsObjMk** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `(G.mapComposableArrows 1).obj (.mk₁ f)` and
`.mk₁ (G.map f)`.
-/
def Functor.mapComposableArrowsObjMk₁Iso {X Y : C} (f : X ⟶ Y) :
    (G.mapComposableArrows 1).obj (.mk₁ f) ≅ .mk₁ (G.map f) :=
  isoMk₁ (Iso.refl _) (Iso.refl _)

set_option backward.isDefEq.respectTransparency.types false in
/-- The isomorphism between `(G.mapComposableArrows 2).obj (.mk₂ f g)` and
`.mk₂ (G.map f) (G.map g)`. -/
@[simps!]
/-
**CategoryTheory.Functor.mapComposableArrowsObjMk** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between `(G.mapComposableArrows 2).obj (.mk₂ f g)` and
`.mk₂ (G.map f) (G.map g)`.
-/
def Functor.mapComposableArrowsObjMk₂Iso {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (G.mapComposableArrows 2).obj (.mk₂ f g) ≅ .mk₂ (G.map f) (G.map g) :=
  isoMk₂ (Iso.refl _) (Iso.refl _) (Iso.refl _)

suppress_compilation in
/-- The functor `ComposableArrows C n ⥤ ComposableArrows D n` induced by `G : C ⥤ D`
commutes with `opEquivalence`. -/
/-
**CategoryTheory.Functor.mapComposableArrowsOpIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         (G
 : CategoryTheory.Functor C D) →           (n : ℕ) →             (G.mapComposabl
eArrows n).comp (CategoryTheory.ComposableArrows.opEquivalence D n).functor.righ
tOp ≅               (CategoryTheory.ComposableArrows.opEquivalence C n).functor.
rightOp.comp (G.op.mapComposableArrows n).op
参数：G : CategoryTheory.Functor C D；n : ℕ；G.mapComposableArrows n；CategoryTheory.C
omposableArrows.opEquivalence D n；CategoryTheory.ComposableArrows.opEquivalence 
C n；G.op.mapComposableArrows n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ComposableArrows C n ⥤ ComposableArrows D n` induced by `G : C ⥤ D`
commutes with `opEquivalence`.
-/
def Functor.mapComposableArrowsOpIso :
    G.mapComposableArrows n ⋙ (opEquivalence D n).functor.rightOp ≅
      (opEquivalence C n).functor.rightOp ⋙ (G.op.mapComposableArrows n).op :=
  Iso.refl _

end

end CategoryTheory

