/-
Copyright (c) 2021 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Quotient

/-!
# The category paths on a quiver.

When `C` is a quiver, `paths C` is the category of paths.

## When the quiver is itself a category
We provide `path_composition : paths C ⥤ C`.

We check that the quotient of the path category of a category by the canonical relation
(paths are related if they compose to the same path) is equivalent to the original category.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

/-- A type synonym for the category of paths in a quiver.
-/
/-
**CategoryTheory.Paths** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Paths (V : Type u₁) : Type u₁
参数：V : Type u₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for the category of paths in a quiver.
-/
def Paths (V : Type u₁) : Type u₁ := V
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type u₁) [Inhabited V] : Inhabited (Paths V) := ⟨(default : V)⟩
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (V : Type u₁) [Unique V] : Unique (Paths V) where
  uniq _ := Subsingleton.elim (α := V) _ _

variable (V : Type u₁) [Quiver.{v₁} V]

namespace Paths

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Paths.categoryPaths** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.P
aths`。
形式化陈述：categoryPaths : Category.{max u₁ v₁} (Paths V) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance categoryPaths : Category.{max u₁ v₁} (Paths V) where
  Hom := fun X Y : V => Quiver.Path X Y
  id _ := Quiver.Path.nil
  comp f g := Quiver.Path.comp f g

set_option backward.isDefEq.respectTransparency.types false in
/-- The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
@[simps]
/-
**CategoryTheory.Paths.of** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Paths`。
形式化陈述：of : V ⥤q Paths V where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a quiver `V` into its path category, as a prefunctor.
-/
def of : V ⥤q Paths V where
  obj X := X
  map f := f.toPath

variable {V}

set_option backward.isDefEq.respectTransparency.types false in
/-- To prove a property on morphisms of a path category with given source `a`, it suffices to
prove it for the identity and prove that the property is preserved under composition on the right
with length 1 paths. -/
/-
**CategoryTheory.Paths.induction_fixed_source** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Paths`。
形式化陈述：induction_fixed_source {a : Paths V} (P : forall {b : Paths V}, (a ⟶ b) ->
 Prop) (id : P (𝟙 a)) (comp : forall {u v : V} (p : a ⟶ (of V).obj u) (q : u ⟶ v
), P p -> P (p ≫ (of V).map q)) : forall {b : Paths V} (f : a ⟶ b), P f
参数：P : forall {b : Paths V}, (a ⟶ b) -> Prop；id : P (𝟙 a)；comp : forall {u v : V
} (p : a ⟶ (of V).obj u) (q : u ⟶ v), P p -> P (p ≫ (of V).map q)。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To prove a property on morphisms of a path category with given source `a`, it su
ffices to
prove it for the identity and prove that the property is preserved under composi
tion on the right
with length 1 paths.
-/
lemma induction_fixed_source {a : Paths V} (P : ∀ {b : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 a))
    (comp : ∀ {u v : V} (p : a ⟶ (of V).obj u) (q : u ⟶ v), P p → P (p ≫ (of V).map q)) :
    ∀ {b : Paths V} (f : a ⟶ b), P f := by
  intro _ f
  induction f with
  | nil => exact id
  | cons _ w h => exact comp _ w h

set_option backward.isDefEq.respectTransparency false in
/-- To prove a property on morphisms of a path category with given target `b`, it suffices to prove
it for the identity and prove that the property is preserved under composition on the left
with length 1 paths. -/
/-
**CategoryTheory.Paths.induction_fixed_target** 是 Mathlib 中的一个引理，位于命名空间 `Categor
yTheory.Paths`。
形式化陈述：induction_fixed_target {b : Paths V} (P : forall {a : Paths V}, (a ⟶ b) ->
 Prop) (id : P (𝟙 b)) (comp : forall {u v : V} (p : (of V).obj v ⟶ b) (q : u ⟶ v
), P p -> P ((of V).map q ≫ p)) : forall {a : Paths V} (f : a ⟶ b), P f
参数：P : forall {a : Paths V}, (a ⟶ b) -> Prop；id : P (𝟙 b)；comp : forall {u v : V
} (p : (of V).obj v ⟶ b) (q : u ⟶ v), P p -> P ((of V).map q ≫ p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用引理 `Quiver.Path.eq_toPath_comp_of_length_eq_succ`：eq_toPath_comp_of_length_e
q_succ (p : Path a b) {n : Nat} (hp : p.length = n + 1) : exists (c : V) (f : a 
⟶ c) (q : Quiver.Path c b) (_ : q.…

--- 原说明 ---
To prove a property on morphisms of a path category with given target `b`, it su
ffices to prove
it for the identity and prove that the property is preserved under composition o
n the left
with length 1 paths.
-/
lemma induction_fixed_target {b : Paths V} (P : ∀ {a : Paths V}, (a ⟶ b) → Prop)
    (id : P (𝟙 b))
    (comp : ∀ {u v : V} (p : (of V).obj v ⟶ b) (q : u ⟶ v), P p → P ((of V).map q ≫ p)) :
    ∀ {a : Paths V} (f : a ⟶ b), P f := by
  intro a f
  generalize h : f.length = k
  induction k generalizing f a with
  | zero => cases f with
    | nil => exact id
    | cons _ _ => simp at h
  | succ k h' =>
    obtain ⟨c, f, q, hq, rfl⟩ := f.eq_toPath_comp_of_length_eq_succ h
    exact comp _ _ (h' _ hq)

set_option backward.isDefEq.respectTransparency.types false in
/-- To prove a property on morphisms of a path category, it suffices to prove it for the identity
and prove that the property is preserved under composition on the right with length 1 paths. -/
/-
**CategoryTheory.Paths.induction** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Paths
`。
形式化陈述：induction (P : forall {a b : Paths V}, (a ⟶ b) -> Prop) (id : forall {v : 
V}, P (𝟙 ((of V).obj v))) (comp : forall {u v w : V} (p : (of V).obj u ⟶ (of V).
obj v) (q : v ⟶ w), P p -> P (p ≫ (of V).map q)) : forall {a b : Paths V} (f : a
 ⟶ b), P f
参数：P : forall {a b : Paths V}, (a ⟶ b) -> Prop；id : forall {v : V}, P (𝟙 ((of V)
.obj v))；comp : forall {u v w : V} (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w)
, P p -> P (p ≫ (of V).map q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Paths.induction_fixed_source`：induction_fixed_source {a :
 Paths V} (P : forall {b : Paths V}, (a ⟶ b) -> Prop) (id : P (𝟙 a)) (comp : for
all {u v : V} (p : a ⟶ (of V).obj…

--- 原说明 ---
To prove a property on morphisms of a path category, it suffices to prove it for
 the identity
and prove that the property is preserved under composition on the right with len
gth 1 paths.
-/
lemma induction (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V}
      (p : (of V).obj u ⟶ (of V).obj v) (q : v ⟶ w), P p → P (p ≫ (of V).map q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f :=
  fun {_} ↦ induction_fixed_source _ id comp

set_option backward.isDefEq.respectTransparency.types false in
/-- To prove a property on morphisms of a path category, it suffices to prove it for the identity
and prove that the property is preserved under composition on the left with length 1 paths. -/
/-
**CategoryTheory.Paths.induction'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Path
s`。
形式化陈述：induction' (P : forall {a b : Paths V}, (a ⟶ b) -> Prop) (id : forall {v :
 V}, P (𝟙 ((of V).obj v))) (comp : forall {u v w : V} (p : u ⟶ v) (q : (of V).ob
j v ⟶ (of V).obj w), P q -> P ((of V).map p ≫ q)) : forall {a b : Paths V} (f : 
a ⟶ b), P f
参数：P : forall {a b : Paths V}, (a ⟶ b) -> Prop；id : forall {v : V}, P (𝟙 ((of V)
.obj v))；comp : forall {u v w : V} (p : u ⟶ v) (q : (of V).obj v ⟶ (of V).obj w)
, P q -> P ((of V).map p ≫ q)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Paths.induction_fixed_target`：induction_fixed_target {b :
 Paths V} (P : forall {a : Paths V}, (a ⟶ b) -> Prop) (id : P (𝟙 b)) (comp : for
all {u v : V} (p : (of V).obj v ⟶…

--- 原说明 ---
To prove a property on morphisms of a path category, it suffices to prove it for
 the identity
and prove that the property is preserved under composition on the left with leng
th 1 paths.
-/
lemma induction' (P : ∀ {a b : Paths V}, (a ⟶ b) → Prop)
    (id : ∀ {v : V}, P (𝟙 ((of V).obj v)))
    (comp : ∀ {u v w : V} (p : u ⟶ v)
      (q : (of V).obj v ⟶ (of V).obj w), P q → P ((of V).map p ≫ q)) :
    ∀ {a b : Paths V} (f : a ⟶ b), P f := by
  intro a b
  revert a
  exact induction_fixed_target (P := fun f ↦ P f) id (fun _ _ ↦ comp _ _)

attribute [local ext (iff := false)] Functor.ext

set_option backward.isDefEq.respectTransparency false in
/-- Any prefunctor from `V` lifts to a functor from `paths V` -/
/-
**CategoryTheory.Paths.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Paths`。
形式化陈述：lift {C} [Category* C] (φ : V ⥤q C) : Paths V ⥤ C where obj
参数：φ : V ⥤q C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any prefunctor from `V` lifts to a functor from `paths V`
-/
def lift {C} [Category* C] (φ : V ⥤q C) : Paths V ⥤ C where
  obj := φ.obj
  map {X} {Y} f :=
    @Quiver.Path.rec V _ X (fun Y _ => φ.obj X ⟶ φ.obj Y) (𝟙 <| φ.obj X)
      (fun _ f ihp => ihp ≫ φ.map f) Y f
  map_id _ := rfl
  map_comp f g := by
    induction g with
    | nil =>
      rw [Category.comp_id]
      rfl
    | cons g' p ih =>
      have : f ≫ Quiver.Path.cons g' p = (f ≫ g').cons p := by apply Quiver.Path.comp_cons
      rw [this]
      simp only at ih ⊢
      rw [ih, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Paths.lift_nil** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Paths`
。
形式化陈述：lift_nil {C} [Category* C] (φ : V ⥤q C) (X : V) : (lift φ).map Quiver.Path
.nil = 𝟙 (φ.obj X)
参数：φ : V ⥤q C；X : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_nil {C} [Category* C] (φ : V ⥤q C) (X : V) :
    (lift φ).map Quiver.Path.nil = 𝟙 (φ.obj X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Paths.lift_cons** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Paths
`。
形式化陈述：lift_cons {C} [Category* C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y)
 (f : Y ⟶ Z) : (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f
参数：φ : V ⥤q C；p : Quiver.Path X Y；f : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_cons {C} [Category* C] (φ : V ⥤q C) {X Y Z : V} (p : Quiver.Path X Y) (f : Y ⟶ Z) :
    (lift φ).map (p.cons f) = (lift φ).map p ≫ φ.map f := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Paths.lift_toPath** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pat
hs`。
形式化陈述：lift_toPath {C} [Category* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) : (lift φ
).map f.toPath = φ.map f
参数：φ : V ⥤q C；f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_toPath {C} [Category* C] (φ : V ⥤q C) {X Y : V} (f : X ⟶ Y) :
    (lift φ).map f.toPath = φ.map f := by
  dsimp [Quiver.Hom.toPath, lift]
  simp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Paths.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Paths
`。
形式化陈述：lift_spec {C} [Category* C] (φ : V ⥤q C) : of V ⋙q (lift φ).toPrefunctor =
 φ
参数：φ : V ⥤q C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.ext`：ext {V : Type u} [Quiver.{v₁} V] {W : Type u₂} [Quiver.{
v₂} W] {F G : Prefunctor V W} (h_obj : forall X, F.obj X = G.obj X) (h_map : for
all …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_spec {C} [Category* C] (φ : V ⥤q C) : of V ⋙q (lift φ).toPrefunctor = φ := by
  fapply Prefunctor.ext
  · rintro X
    rfl
  · rintro X Y f
    rcases φ with ⟨φo, φm⟩
    dsimp [lift, Quiver.Hom.toPath]
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Paths.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pat
hs`。
形式化陈述：lift_unique {C} [Category* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C) (hΦ : of V ⋙q
 Φ.toPrefunctor = φ) : Φ = lift φ
参数：φ : V ⥤q C；Φ : Paths V ⥤ C；hΦ : of V ⋙q Φ.toPrefunctor = φ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
theorem lift_unique {C} [Category* C] (φ : V ⥤q C) (Φ : Paths V ⥤ C)
    (hΦ : of V ⋙q Φ.toPrefunctor = φ) : Φ = lift φ := by
  subst_vars
  fapply Functor.ext
  · rintro X
    rfl
  · rintro X Y f
    dsimp [lift]
    induction f with
    | nil =>
      simp only [Category.comp_id]
      apply Functor.map_id
    | cons p f' ih =>
      simp only [Category.comp_id, Category.id_comp] at ih ⊢
      -- Porting note: Had to do substitute `p.cons f'` and `f'.toPath` by their fully qualified
      -- versions in this `have` clause (elsewhere too).
      have : Φ.map (Quiver.Path.cons p f') = Φ.map p ≫ Φ.map (Quiver.Hom.toPath f') := by
        convert! Functor.map_comp Φ p (Quiver.Hom.toPath f')
      rw [this, ih]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two functors out of a path category are equal when they agree on singleton paths. -/
@[ext (iff := false)]
/-
**CategoryTheory.Paths.ext_functor** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pat
hs`。
形式化陈述：ext_functor {C} [Category* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj) 
(h : forall (a b : V) (e : a ⟶ b), F.map e.toPath = eqToHom (congr_fun h_obj a) 
≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)) : F = G
参数：h_obj : F.obj = G.obj；h : forall (a b : V) (e : a ⟶ b), F.map e.toPath = eqTo
Hom (congr_fun h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.eqToHom_trans`：eqToHom_trans {X Y Z : C} (p : X = Y) (q :
 Y = Z) : eqToHom p ≫ eqToHom q = eqToHom (p.trans q)
· 使用定理 `CategoryTheory.eqToHom_refl`：eqToHom_refl {C : Type u₁} [CategoryStruct.
{v₁} C] (X : C) (p : X = X) : eqToHom p = 𝟙 X
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.eqToHom_trans_assoc`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {X Y Z : C} (p : X = Y) (q : Y = Z) {Z_1 : C} (h : Z ⟶ Z
_1),   CategoryTheory.Ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two functors out of a path category are equal when they agree on singleton paths
.
-/
theorem ext_functor {C} [Category* C] {F G : Paths V ⥤ C} (h_obj : F.obj = G.obj)
    (h : ∀ (a b : V) (e : a ⟶ b), F.map e.toPath =
        eqToHom (congr_fun h_obj a) ≫ G.map e.toPath ≫ eqToHom (congr_fun h_obj.symm b)) :
    F = G := by
  fapply Functor.ext
  · intro X
    rw [h_obj]
  · intro X Y f
    induction f with
    | nil => erw [F.map_id, G.map_id, Category.id_comp, eqToHom_trans, eqToHom_refl]
    | cons g e ih =>
      erw [F.map_comp g (Quiver.Hom.toPath e), G.map_comp g (Quiver.Hom.toPath e), ih, h]
      simp only [Category.id_comp, eqToHom_refl, eqToHom_trans_assoc, Category.assoc]

end Paths

variable (W : Type u₂) [Quiver.{v₂} W]

-- A restatement of `Prefunctor.mapPath_comp` using `f ≫ g` instead of `f.comp g`.
set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.Prefunctor.mapPath_comp'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Prefunctor`。
形式化陈述：∀ (V : Type u₁) [inst : Quiver V] (W : Type u₂) [inst_1 : Quiver W] (F : V
 ⥤q W) {X Y Z : CategoryTheory.Paths V}   (f : X ⟶ Y) (g : Y ⟶ Z), F.mapPath (Ca
tegoryTheory.CategoryStruct.comp f g) = (F.mapPath f).comp (F.mapPath g)
参数：V : Type u₁；W : Type u₂；F : V ⥤q W；f : X ⟶ Y；g : Y ⟶ Z；CategoryTheory.Categor
yStruct.comp f g；F.mapPath f；F.mapPath g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prefunctor.mapPath_comp`：∀ {V : Type u₁} [inst : Quiver V] {W : Type u₂}
 [inst_1 : Quiver W] (F : V ⥤q W) {a b : V} (p : Quiver.Path a b) {c : V}   (q :
 Quiver.Path …
-/
theorem Prefunctor.mapPath_comp' (F : V ⥤q W) {X Y Z : Paths V} (f : X ⟶ Y) (g : Y ⟶ Z) :
    F.mapPath (f ≫ g) = (F.mapPath f).comp (F.mapPath g) :=
  Prefunctor.mapPath_comp _ _ _

end

section

variable {C : Type u₁} [Category.{v₁} C]

open Quiver

/-- A path in a category can be composed to a single morphism. -/
@[simp]
/-
**CategoryTheory.composePath** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{v₁, u₁} C] → {X Y : C} → 
Quiver.Path X Y → (X ⟶ Y)
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A path in a category can be composed to a single morphism.
-/
def composePath {X : C} : ∀ {Y : C} (_ : Path X Y), X ⟶ Y
  | _, .nil => 𝟙 X
  | _, .cons p e => composePath p ≫ e

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
/-
**CategoryTheory.composePath_nil** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma composePath_nil {X : C} : composePath (Path.nil : Path X X) = 𝟙 X := rfl

-- This lemma was marked as `@[simp]` but it is generated by `@[simp]` on `composePath`.
/-
**CategoryTheory.composePath_cons** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) : composePath (p.c
ons e) = composePath p ≫ e
参数：p : Path X Y；e : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma composePath_cons {X Y Z : C} (p : Path X Y) (e : Y ⟶ Z) :
    composePath (p.cons e) = composePath p ≫ e := rfl

@[simp]
/-
**CategoryTheory.composePath_toPath** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem composePath_toPath {X Y : C} (f : X ⟶ Y) : composePath f.toPath = f := Category.id_comp _

@[simp]
/-
**CategoryTheory.composePath_comp** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) : composePath (
f.comp g) = composePath f ≫ composePath g
参数：f : Path X Y；g : Path Y Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.composePath.eq_2`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X : C} (x b : C) (p : Quiver.Path X b) (e : b ⟶ x),   Cate
goryTheory.composePat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
theorem composePath_comp {X Y Z : C} (f : Path X Y) (g : Path Y Z) :
    composePath (f.comp g) = composePath f ≫ composePath g := by
  induction g with
  | nil => simp
  | cons g e ih => simp [ih]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
-- TODO get rid of `(id X : C)` somehow?
/-
**CategoryTheory.composePath_id** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 (show C from X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem composePath_id {X : Paths C} : composePath (𝟙 X) = 𝟙 (show C from X) := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.composePath_comp'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory`。
形式化陈述：composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) : composePath 
(f ≫ g) = composePath f ≫ composePath g
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.composePath_comp`：composePath_comp {X Y Z : C} (f : Path 
X Y) (g : Path Y Z) : composePath (f.comp g) = composePath f ≫ composePath g
-/
theorem composePath_comp' {X Y Z : Paths C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    composePath (f ≫ g) = composePath f ≫ composePath g :=
  composePath_comp f g

variable (C)

set_option backward.isDefEq.respectTransparency.types false in
/-- Composition of paths as functor from the path category of a category to the category. -/
@[simps]
/-
**CategoryTheory.pathComposition** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：pathComposition : Paths C ⥤ C where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of paths as functor from the path category of a category to the cate
gory.
-/
def pathComposition : Paths C ⥤ C where
  obj X := X
  map f := composePath f

-- TODO: This, and what follows, should be generalized to
-- the `HomRel` for the kernel of any functor.
-- Indeed, this should be part of an equivalence between congruence relations on a category `C`
-- and full, essentially surjective functors out of `C`.
/-- The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism. -/
@[simp]
/-
**CategoryTheory.pathsHomRel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：pathsHomRel : HomRel (Paths C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical relation on the path category of a category:
two paths are related if they compose to the same morphism.
-/
def pathsHomRel : HomRel (Paths C) := fun _ _ p q =>
  (pathComposition C).map p = (pathComposition C).map q

#adaptation_note /-- As of nightly-2026-04-29, the simpNF linter is failing here.
Assistance investigating this would be appreciated. -/
attribute [nolint simpNF] pathsHomRel.eq_1

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from a category to the canonical quotient of its path category. -/
@[simps]
/-
**CategoryTheory.toQuotientPaths** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from a category to the canonical quotient of its path category.
-/
def toQuotientPaths : C ⥤ Quotient (pathsHomRel C) where
  obj X := Quotient.mk X
  map f := Quot.mk _ f.toPath
  map_id X := Quot.sound (HomRel.CompClosure.of (by simp))
  map_comp f g := Quot.sound (HomRel.CompClosure.of (by simp))

set_option backward.isDefEq.respectTransparency.types false in
/-- The functor from the canonical quotient of a path category of a category
to the original category. -/
@[simps!]
/-
**CategoryTheory.quotientPathsTo** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：quotientPathsTo : Quotient (pathsHomRel C) ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from the canonical quotient of a path category of a category
to the original category.
-/
def quotientPathsTo : Quotient (pathsHomRel C) ⥤ C :=
  Quotient.lift _ (pathComposition C) fun _ _ _ _ w => w

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The canonical quotient of the path category of a category
is equivalent to the original category. -/
/-
**CategoryTheory.quotientPathsEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where functor
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical quotient of the path category of a category
is equivalent to the original category.
-/
def quotientPathsEquiv : Quotient (pathsHomRel C) ≌ C where
  functor := quotientPathsTo C
  inverse := toQuotientPaths C
  unitIso :=
    NatIso.ofComponents
      (fun X => by cases X; rfl)
      (Quot.ind fun f => by exact Quot.sound (HomRel.CompClosure.of (by simp)))
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (fun f => by simp)
  functor_unitIso_comp X := by
    cases X
    simp only [Functor.id_obj,
               quotientPathsTo_obj, Functor.comp_obj, toQuotientPaths_obj_as,
               NatIso.ofComponents_hom_app, Iso.refl_hom, quotientPathsTo_map, Category.comp_id]
    rfl

end

end CategoryTheory

