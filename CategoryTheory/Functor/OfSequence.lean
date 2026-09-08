/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.EqToHom

/-!
# Functors from the category of the ordered set `ℕ`

In this file, we provide a constructor `Functor.ofSequence`
for functors `ℕ ⥤ C` which takes as an input a sequence
of morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.

We also provide a constructor `NatTrans.ofSequence` for natural
transformations between functors `ℕ ⥤ C` which allows to check
the naturality condition only for morphisms `n ⟶ n + 1`.

The duals of the above for functors `ℕᵒᵖ ⥤ C` are given by `Functor.ofOpSequence` and
`NatTrans.ofOpSequence`.

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C : Type*} [Category* C]

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X n ⟶ X (n + 1))

namespace OfSequence

/-
**CategoryTheory.Functor.OfSequence.congr_f** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor.OfSequence`。
形式化陈述：congr_f (i j : Nat) (h : i = j) : f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHo
m (by rw [h])
参数：i j : Nat；h : i = j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma congr_f (i j : ℕ) (h : i = j) :
    f i = eqToHom (by rw [h]) ≫ f j ≫ eqToHom (by rw [h]) := by
  subst h
  simp

/-- The morphism `X i ⟶ X j` obtained by composing morphisms of
the form `X n ⟶ X (n + 1)` when `i ≤ j`. -/
/-
**CategoryTheory.Functor.OfSequence.map** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.Functor.OfSequence`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {X 
: ℕ → C} → ((n : ℕ) → X n ⟶ X (n + 1)) → (i j : ℕ) → i ≤ j → (X i ⟶ X j)
参数：(n : ℕ) → X n ⟶ X (n + 1)；i j : ℕ；X i ⟶ X j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism `X i ⟶ X j` obtained by composing morphisms of
the form `X n ⟶ X (n + 1)` when `i ≤ j`.
-/
def map : ∀ {X : ℕ → C} (_ : ∀ n, X n ⟶ X (n + 1)) (i j : ℕ), i ≤ j → (X i ⟶ X j)
  | _, _, 0, 0 => fun _ ↦ 𝟙 _
  | _, f, 0, 1 => fun _ ↦ f 0
  | _, f, 0, l + 1 => fun _ ↦ f 0 ≫ map (fun n ↦ f (n + 1)) 0 l (by lia)
  | _, _, _ + 1, 0 => nofun
  | _, f, k + 1, l + 1 => fun _ ↦ map (fun n ↦ f (n + 1)) k l (by lia)
/-
**CategoryTheory.Functor.OfSequence.map_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Functor.OfSequence`。
形式化陈述：map_id (i : Nat) : map f i i (by lia) = 𝟙 _
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_id (i : ℕ) : map f i i (by lia) = 𝟙 _ := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi
/-
**CategoryTheory.Functor.OfSequence.map_le_succ** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor.OfSequence`。
形式化陈述：map_le_succ (i : Nat) : map f i (i + 1) (by lia) = f i
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_le_succ (i : ℕ) : map f i (i + 1) (by lia) = f i := by
  revert X f
  induction i with
  | zero => intros; rfl
  | succ _ hi =>
      intro X f
      apply hi

@[reassoc]
/-
**CategoryTheory.Functor.OfSequence.map_comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Functor.OfSequence`。
形式化陈述：map_comp (i j k : Nat) (hij : i <= j) (hjk : j <= k) : map f i k (hij.tran
s hjk) = map f i j hij ≫ map f j k hjk
参数：i j k : Nat；hij : i <= j；hjk : j <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.OfSequence.map_id`：map_id (i : Nat) : map f i i (
by lia) = 𝟙 _
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.OfSequence.map.eq_3`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] (x : ℕ → C) (x_1 : (n : ℕ) → x n ⟶ x (n + 1))
 (l : ℕ),   (l = 0 → False) →   …
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.OfSequence.map.eq_2`：∀ {C : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} C] (x : ℕ → C) (x_1 : (n : ℕ) → x n ⟶ x (n + 1))
,   CategoryTheory.Functor.OfSeq…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma map_comp (i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    map f i k (hij.trans hjk) = map f i j hij ≫ map f j k hjk := by
  induction i generalizing X j k with
  | zero =>
      induction j generalizing X k with
      | zero =>
          rw [map_id, id_comp]
      | succ j hj =>
          obtain (_ | _ | k) := k
          · lia
          · obtain rfl : j = 0 := by lia
            rw [map_id, comp_id]
          · simp only [map, Nat.reduceAdd]
            rw [hj (fun n ↦ f (n + 1)) (k + 1) (by lia) (by lia)]
            obtain _ | j := j
            all_goals simp [map]
  | succ i hi =>
      rcases j, k with ⟨(_ | j), (_ | k)⟩
      · lia
      · lia
      · lia
      · exact hi _ j k (by lia) (by lia)

-- `map` has good definitional properties when applied to explicit natural numbers
/-
**CategoryTheory.Functor.OfSequence.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.F
unctor.OfSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map f 5 5 (by lia) = 𝟙 _ := rfl
/-
**CategoryTheory.Functor.OfSequence.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.F
unctor.OfSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map f 0 3 (by lia) = f 0 ≫ f 1 ≫ f 2 := rfl
/-
**CategoryTheory.Functor.OfSequence.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.F
unctor.OfSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : map f 3 7 (by lia) = f 3 ≫ f 4 ≫ f 5 ≫ f 6 := rfl

end OfSequence

/-- The functor `ℕ ⥤ C` constructed from a sequence of
morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`. -/
@[simps obj]
/-
**CategoryTheory.Functor.ofSequence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：ofSequence : Nat ⥤ C where obj
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.leOfHom`：leOfHom {x y : X} (h : x ⟶ y) : x <= y
· 使用引理 `CategoryTheory.Functor.OfSequence.map_id`：map_id (i : Nat) : map f i i (
by lia) = 𝟙 _

--- 原说明 ---
The functor `ℕ ⥤ C` constructed from a sequence of
morphisms `f : X n ⟶ X (n + 1)` for all `n : ℕ`.
-/
def ofSequence : ℕ ⥤ C where
  obj := X
  map {i j} φ := OfSequence.map f i j (leOfHom φ)
  map_id i := OfSequence.map_id f i
  map_comp {i j k} α β := OfSequence.map_comp f i j k (leOfHom α) (leOfHom β)

@[simp]
/-
**CategoryTheory.Functor.ofSequence_map_homOfLE_succ** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor`。
形式化陈述：ofSequence_map_homOfLE_succ (n : Nat) : (ofSequence f).map (homOfLE (Nat.l
e_add_right n 1)) = f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.OfSequence.map_le_succ`：map_le_succ (i : Nat) : m
ap f i (i + 1) (by lia) = f i
-/
lemma ofSequence_map_homOfLE_succ (n : ℕ) :
    (ofSequence f).map (homOfLE (Nat.le_add_right n 1)) = f n :=
  OfSequence.map_le_succ f n

end Functor

namespace NatTrans

variable {F G : ℕ ⥤ C} (app : ∀ (n : ℕ), F.obj n ⟶ G.obj n)
  (naturality : ∀ (n : ℕ), F.map (homOfLE (n.le_add_right 1)) ≫ app (n + 1) =
      app n ≫ G.map (homOfLE (n.le_add_right 1)))

/-- Constructor for natural transformations `F ⟶ G` in `ℕ ⥤ C` which takes as inputs
the morphisms `F.obj n ⟶ G.obj n` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps app]
/-
**CategoryTheory.NatTrans.ofSequence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.N
atTrans`。
形式化陈述：ofSequence : F ⟶ G where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations `F ⟶ G` in `ℕ ⥤ C` which takes as inputs
the morphisms `F.obj n ⟶ G.obj n` for all `n : ℕ` and the naturality condition o
nly
for morphisms of the form `n ⟶ n + 1`.
-/
def ofSequence : F ⟶ G where
  app := app
  naturality := by
    intro i j φ
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (leOfHom φ)
    obtain rfl := Subsingleton.elim φ (homOfLE (by lia))
    revert i j
    induction k with
    | zero =>
        intro i j hk
        obtain rfl : j = i := by lia
        simp
    | succ k hk =>
        intro i j hk'
        obtain rfl : j = i + k + 1 := by lia
        simp only [← homOfLE_comp (show i ≤ i + k by lia) (show i + k ≤ i + k + 1 by lia),
          Functor.map_comp, assoc, naturality, reassoc_of% (hk rfl)]

end NatTrans

namespace Functor

variable {X : ℕ → C} (f : ∀ n, X (n + 1) ⟶ X n)

/-- The functor `ℕᵒᵖ ⥤ C` constructed from a sequence of
morphisms `f : X (n + 1) ⟶ X n` for all `n : ℕ`. -/
@[simps! obj]
/-
**CategoryTheory.Functor.ofOpSequence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Functor`。
形式化陈述：ofOpSequence : Natᵒᵖ ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `ℕᵒᵖ ⥤ C` constructed from a sequence of
morphisms `f : X (n + 1) ⟶ X n` for all `n : ℕ`.
-/
def ofOpSequence : ℕᵒᵖ ⥤ C := (ofSequence (fun n ↦ (f n).op)).leftOp

-- `ofOpSequence` has good definitional properties when applied to explicit natural numbers
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (ofOpSequence f).map (homOfLE (show 5 ≤ 5 by lia)).op = 𝟙 _ := rfl
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (ofOpSequence f).map (homOfLE (show 0 ≤ 3 by lia)).op = (f 2 ≫ f 1) ≫ f 0 := rfl
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个示例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (ofOpSequence f).map (homOfLE (show 3 ≤ 7 by lia)).op =
    ((f 6 ≫ f 5) ≫ f 4) ≫ f 3 := rfl

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Functor.ofOpSequence_map_homOfLE_succ** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：ofOpSequence_map_homOfLE_succ (n : Nat) : (ofOpSequence f).map (homOfLE (N
at.le_add_right n 1)).op = f n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.ofSequence_map_homOfLE_succ`：ofSequence_map_homOf
LE_succ (n : Nat) : (ofSequence f).map (homOfLE (Nat.le_add_right n 1)) = f n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ofOpSequence_map_homOfLE_succ (n : ℕ) :
    (ofOpSequence f).map (homOfLE (Nat.le_add_right n 1)).op = f n := by
  simp [ofOpSequence]

end Functor

namespace NatTrans

variable {F G : ℕᵒᵖ ⥤ C} (app : ∀ (n : ℕ), F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩)
  (naturality : ∀ (n : ℕ), F.map (homOfLE (n.le_add_right 1)).op ≫ app n =
      app (n + 1) ≫ G.map (homOfLE (n.le_add_right 1)).op)

/-- Constructor for natural transformations `F ⟶ G` in `ℕᵒᵖ ⥤ C` which takes as inputs
the morphisms `F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩` for all `n : ℕ` and the naturality condition only
for morphisms of the form `n ⟶ n + 1`. -/
@[simps!]
/-
**CategoryTheory.NatTrans.ofOpSequence** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.NatTrans`。
形式化陈述：ofOpSequence : F ⟶ G where app n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for natural transformations `F ⟶ G` in `ℕᵒᵖ ⥤ C` which takes as inpu
ts
the morphisms `F.obj ⟨n⟩ ⟶ G.obj ⟨n⟩` for all `n : ℕ` and the naturality conditi
on only
for morphisms of the form `n ⟶ n + 1`.
-/
def ofOpSequence : F ⟶ G where
  app n := app n.unop
  naturality _ _ f := by
    let φ : G.rightOp ⟶ F.rightOp := ofSequence (fun n ↦ (app n).op)
      (fun n ↦ Quiver.Hom.unop_inj (naturality n).symm)
    exact Quiver.Hom.op_inj (φ.naturality f.unop).symm

end NatTrans

end CategoryTheory

