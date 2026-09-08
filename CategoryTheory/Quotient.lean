/-
Copyright (c) 2020 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
module

public import Mathlib.CategoryTheory.Groupoid

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/

@[expose] public section


/-- A `HomRel` on `C` consists of a relation on every hom-set. -/
/-
**HomRel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HomRel (C) [Quiver C]
参数：C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomRel` on `C` consists of a relation on every hom-set.
-/
def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop
deriving Inhabited

namespace CategoryTheory

open CategoryTheory.Functor

section

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

/-- A functor induces a `HomRel` on its domain, relating those maps that have the same image. -/
/-
**CategoryTheory.Functor.homRel** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functo
r`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → HomRel C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor induces a `HomRel` on its domain, relating those maps that have the sa
me image.
-/
def Functor.homRel : HomRel C :=
  fun _ _ f g ↦ F.map f = F.map g

@[simp]
/-
**CategoryTheory.Functor.homRel_iff** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Fu
nctor`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : CategoryTheory.Functo
r C D) {X Y : C} (f g : X ⟶ Y),   F.homRel f g ↔ F.map f = F.map g
参数：F : CategoryTheory.Functor C D；f g : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Functor.homRel_iff {X Y : C} (f g : X ⟶ Y) :
    F.homRel f g ↔ F.map f = F.map g := Iff.rfl

end

variable {C : Type*} [Category* C] (r : HomRel C)

namespace HomRel

/-- The condition that a `HomRel` is stable under precomposition. -/
/-
**CategoryTheory.HomRel.IsStableUnderPrecomp** 是 Mathlib 中的一个归纳类型，位于命名空间 `Catego
ryTheory.HomRel`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → HomRel C 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a `HomRel` is stable under precomposition.
-/
class IsStableUnderPrecomp : Prop where
  comp_left {X Y Z} (f : X ⟶ Y) {g g' : Y ⟶ Z} : r g g' → r (f ≫ g) (f ≫ g')

/-- The condition that a `HomRel` is stable under postcomposition. -/
/-
**CategoryTheory.HomRel.IsStableUnderPostcomp** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categ
oryTheory.HomRel`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → HomRel C 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that a `HomRel` is stable under postcomposition.
-/
class IsStableUnderPostcomp : Prop where
  comp_right {X Y Z} {f f' : X ⟶ Y} (g : Y ⟶ Z) : r f f' → r (f ≫ g) (f' ≫ g)

export IsStableUnderPrecomp (comp_left)
export IsStableUnderPostcomp (comp_right)

/-- Generates the closure of a family of relations w.r.t. composition from left and right. -/
/-
**CategoryTheory.HomRel.CompClosure** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory.
HomRel`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → HomRel C 
→ HomRel C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Generates the closure of a family of relations w.r.t. composition from left and 
right.
-/
inductive CompClosure (r : HomRel C) : HomRel C
  | intro {s t : C} (a b : C) (f : s ⟶ a) (m₁ m₂ : a ⟶ b) (g : b ⟶ t) (h : r m₁ m₂) :
    CompClosure r (f ≫ m₁ ≫ g) (f ≫ m₂ ≫ g)

variable {r} in
/-
**CategoryTheory.HomRel.CompClosure.of** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory
.HomRel.CompClosure`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {r : HomRel
 C} {a b : C} {m₁ m₂ : a ⟶ b},   r m₁ m₂ → CategoryTheory.HomRel.CompClosure r m
₁ m₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
theorem CompClosure.of {a b : C} {m₁ m₂ : a ⟶ b} (h : r m₁ m₂) : CompClosure r m₁ m₂ := by
  simpa using CompClosure.intro _ _ (𝟙 _) m₁ m₂ (𝟙 _) h
/-
**CategoryTheory.HomRel.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.HomRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderPrecomp (CompClosure r) where
  comp_left := by
    rintro a b e f _ _ ⟨c, d, g, h₁, h₂, i, h⟩
    simpa using CompClosure.intro _ _ (f ≫ g) _ _ i h
/-
**CategoryTheory.HomRel.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.HomRel`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsStableUnderPostcomp (CompClosure r) where
  comp_right := by
    rintro a d e _ _ g ⟨b, c, f, g₁, g₂, i, h⟩
    simpa using CompClosure.intro _ _ f _ _ (i ≫ g) h

section

variable [IsStableUnderPrecomp r] [IsStableUnderPostcomp r]

/-
**CategoryTheory.HomRel.compClosure_iff_self** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.HomRel`。
形式化陈述：compClosure_iff_self {X Y : C} (f g : X ⟶ Y) : CompClosure r f g ↔ r f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.HomRel.IsStableUnderPrecomp.comp_left`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {r : HomRel C}   [self : CategoryTh
eory.HomRel.IsStableUnderPrecomp r] {X Y Z…
· 使用定理 `CategoryTheory.HomRel.IsStableUnderPostcomp.comp_right`：∀ {C : Type u_1}
 {inst : CategoryTheory.Category.{v_1, u_1} C} {r : HomRel C}   [self : Category
Theory.HomRel.IsStableUnderPostcomp r] {X Y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `CategoryTheory.HomRel.CompClosure.of`：∀ {C : Type u_1} [inst : CategoryT
heory.Category.{v_1, u_1} C] {r : HomRel C} {a b : C} {m₁ m₂ : a ⟶ b},   r m₁ m₂
 → CategoryTheory.HomRel.C…
-/
lemma compClosure_iff_self {X Y : C} (f g : X ⟶ Y) :
    CompClosure r f g ↔ r f g := by
  refine ⟨?_, CompClosure.of⟩
  rintro ⟨_, _, _, _, _, _, h⟩
  exact HomRel.comp_left _ (HomRel.comp_right _ h)

@[simp]
/-
**CategoryTheory.HomRel.compClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.HomRel`。
形式化陈述：compClosure_eq_self : CompClosure r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compClosure_eq_self :
    CompClosure r = r := by
  dsimp [HomRel]
  ext
  simp only [compClosure_iff_self]

end

end HomRel

/-- A `HomRel` is a congruence when it's an equivalence on every hom-set, and it can be composed
from left and right. -/
/-
**CategoryTheory.Congruence** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → HomRel C 
→ Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `HomRel` is a congruence when it's an equivalence on every hom-set, and it can
 be composed
from left and right.
-/
class Congruence : Prop
    extends HomRel.IsStableUnderPrecomp r, HomRel.IsStableUnderPostcomp r where
  /-- `r` is an equivalence on every hom-set. -/
  equivalence : ∀ {X Y}, _root_.Equivalence (@r X Y)

/-- For `F : C ⥤ D`, `F.homRel` is a congruence. -/
/-
**CategoryTheory.Functor.congruence_homRel** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Functor`。
形式化陈述：∀ {C : Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2}
 C]   [inst_1 : CategoryTheory.Category.{v_3, u_3} D] (F : CategoryTheory.Functo
r C D), CategoryTheory.Congruence F.homRel
参数：F : CategoryTheory.Functor C D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
For `F : C ⥤ D`, `F.homRel` is a congruence.
-/
instance Functor.congruence_homRel {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) :
    Congruence F.homRel where
  equivalence :=
    { refl := fun _ ↦ rfl
      symm := by aesop
      trans := by aesop }
  comp_left := by aesop
  comp_right := by aesop

/-- A type synonym for `C`, thought of as the objects of the quotient category. -/
@[ext]
/-
**CategoryTheory.Quotient** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u_1} → [inst : CategoryTheory.Category.{v_1, u_1} C] → HomRel C 
→ Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type synonym for `C`, thought of as the objects of the quotient category.
-/
structure Quotient (r : HomRel C) where
  /-- The object of `C`. -/
  as : C
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited C] : Inhabited (Quotient r) :=
  ⟨{ as := default }⟩

namespace Quotient

/-- Hom-sets of the quotient category. -/
/-
**CategoryTheory.Quotient.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotient
`。
形式化陈述：Hom (s t : Quotient r) : Type _
参数：s t : Quotient r。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Hom-sets of the quotient category.
-/
def Hom (s t : Quotient r) : Type _ :=
  Quot <| @HomRel.CompClosure C _ r s.as t.as
/-
**CategoryTheory.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (a : Quotient r) : Inhabited (Hom r a a) :=
  ⟨Quot.mk _ (𝟙 a.as)⟩

/-- Composition in the quotient category. -/
/-
**CategoryTheory.Quotient.comp** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotien
t`。
形式化陈述：comp ⦃a b c : Quotient r⦄ : Hom r a b -> Hom r b c -> Hom r a c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition in the quotient category.
-/
def comp ⦃a b c : Quotient r⦄ : Hom r a b → Hom r b c → Hom r a c := fun hf hg ↦
  Quot.liftOn hf
    (fun f ↦
      Quot.liftOn hg (fun g ↦ Quot.mk _ (f ≫ g)) fun _ _ h ↦
        Quot.sound (HomRel.comp_left f h))
    fun _ _ h ↦ Quot.inductionOn hg fun _ ↦ Quot.sound (HomRel.comp_right _ h)

@[simp]
/-
**CategoryTheory.Quotient.comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Quot
ient`。
形式化陈述：comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) : comp r 
(Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g)
参数：f : a.as ⟶ b.as；g : b.as ⟶ c.as。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_mk {a b c : Quotient r} (f : a.as ⟶ b.as) (g : b.as ⟶ c.as) :
    comp r (Quot.mk _ f) (Quot.mk _ g) = Quot.mk _ (f ≫ g) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Quotient.category** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quo
tient`。
形式化陈述：category : Category (Quotient r) where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance category : Category (Quotient r) where
  Hom := Hom r
  id a := Quot.mk _ (𝟙 a.as)
  comp := @comp _ _ r
  comp_id f := Quot.inductionOn f <| by simp
  id_comp f := Quot.inductionOn f <| by simp
  assoc f g h := Quot.inductionOn f <| Quot.inductionOn g <| Quot.inductionOn h <| by simp

/-- An equivalence between the type synonym for a quotient category and the type alias
for the original category. -/
/-
**CategoryTheory.Quotient.equiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotie
nt`。
形式化陈述：equiv {C : Type _} [Category* C] (r : HomRel C) : Quotient r ≃ C where toF
un x
参数：r : HomRel C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between the type synonym for a quotient category and the type ali
as
for the original category.
-/
def equiv {C : Type _} [Category* C] (r : HomRel C) : Quotient r ≃ C where
  toFun x := x.1
  invFun x := ⟨x⟩

noncomputable section

variable {G : Type*} [Groupoid G] (r : HomRel G)

/-- Inverse of a map in the quotient category of a groupoid. -/
/-
**CategoryTheory.Quotient.inv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotient
`。
形式化陈述：{G : Type u_2} →   [inst : CategoryTheory.Groupoid G] → (r : HomRel G) → {
X Y : CategoryTheory.Quotient r} → (X ⟶ Y) → (Y ⟶ X)
参数：r : HomRel G；X ⟶ Y；Y ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of a map in the quotient category of a groupoid.
-/
protected def inv {X Y : Quotient r} (f : X ⟶ Y) : Y ⟶ X :=
  Quot.liftOn f (fun f' => Quot.mk _ (Groupoid.inv f')) (fun _ _ con => by
    obtain ⟨_, _, a, f, g, b, hfg⟩ := con
    simpa using! (Quot.sound (HomRel.CompClosure.intro _ _
      (inv b ≫ inv g) _ _ (inv f ≫ inv a) hfg)).symm)

@[simp]
/-
**CategoryTheory.Quotient.inv_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Quoti
ent`。
形式化陈述：inv_mk {X Y : Quotient r} (f : X.as ⟶ Y.as) : Quotient.inv r (Quot.mk _ f)
 = Quot.mk _ (Groupoid.inv f)
参数：f : X.as ⟶ Y.as。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv_mk {X Y : Quotient r} (f : X.as ⟶ Y.as) :
    Quotient.inv r (Quot.mk _ f) = Quot.mk _ (Groupoid.inv f) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient of a groupoid is a groupoid. -/
/-
**CategoryTheory.Quotient.groupoid** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quo
tient`。
形式化陈述：groupoid : Groupoid (Quotient r) where inv f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a groupoid is a groupoid.
-/
instance groupoid : Groupoid (Quotient r) where
  inv f := Quotient.inv r f
  inv_comp f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]
  comp_inv f := Quot.inductionOn f <| by simp [CategoryStruct.comp, CategoryStruct.id]

end

/-- The functor from a category to its quotient. -/
@[implicit_reducible]
/-
**CategoryTheory.Quotient.functor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quot
ient`。
形式化陈述：functor : C ⥤ Quotient r where obj a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from a category to its quotient.
-/
def functor : C ⥤ Quotient r where
  obj a := { as := a }
  map f := Quot.mk _ f

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Quotient.full_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory
.Quotient`。
形式化陈述：full_functor : (functor r).Full where map_surjective f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quot.out_eq`：Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q
.out = q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance full_functor : (functor r).Full where
  map_surjective f := ⟨Quot.out f, by simp [functor]⟩
/-
**CategoryTheory.Quotient.essSurj_functor** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Quotient`。
形式化陈述：essSurj_functor : (functor r).EssSurj where mem_essImage Y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance essSurj_functor : (functor r).EssSurj where
  mem_essImage Y := ⟨Y.as, ⟨eqToIso rfl⟩⟩
/-
**CategoryTheory.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique C] : Unique (Quotient r) where
  uniq a := by ext; subsingleton
/-
**CategoryTheory.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ (x y : C), Subsingleton (x ⟶ y)] (x y : Quotient r) :
    Subsingleton (x ⟶ y) := (full_functor r).map_surjective.subsingleton
/-
**CategoryTheory.Quotient.induction** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Qu
otient`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C)   {P : {a b : CategoryTheory.Quotient r} → (a ⟶ b) → Prop},   (∀ {x y : C} (
f : x ⟶ y), P ((CategoryTheory.Quotient.functor r).map f)) →     ∀ {a b : Catego
ryTheory.Quotient r} (f : a ⟶ b), P f
参数：r : HomRel C；a ⟶ b；∀ {x y : C} (f : x ⟶ y), P ((CategoryTheory.Quotient.funct
or r).map f)；f : a ⟶ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem induction {P : ∀ {a b : Quotient r}, (a ⟶ b) → Prop}
    (h : ∀ {x y : C} (f : x ⟶ y), P ((functor r).map f)) :
    ∀ {a b : Quotient r} (f : a ⟶ b), P f := by
  rintro ⟨x⟩ ⟨y⟩ ⟨f⟩
  exact h f
/-
**CategoryTheory.Quotient.sound** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Quotie
nt`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (CategoryTheory.Quotient.functor r).m
ap f₁ = (CategoryTheory.Quotient.functor r).map f₂
参数：r : HomRel C；CategoryTheory.Quotient.functor r；CategoryTheory.Quotient.functo
r r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
protected theorem sound {a b : C} {f₁ f₂ : a ⟶ b} (h : r f₁ f₂) :
    (functor r).map f₁ = (functor r).map f₂ := by
  simpa using! Quot.sound (HomRel.CompClosure.intro _ _ (𝟙 a) f₁ f₂ (𝟙 b) h)

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Quotient.functor_map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Quotient`。
形式化陈述：functor_map_eq_iff [h : Congruence r] {X Y : C} (f f' : X ⟶ Y) : (functor 
r).map f = (functor r).map f' ↔ r f f'
参数：f f' : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Equivalence.quot_mk_eq_iff`：Equivalence.quot_mk_eq_iff {α : Type*} {r : 
α -> α -> Prop} (h : Equivalence r) (x y : α) : Quot.mk r x = Quot.mk r y ↔ r x 
y
· 使用定理 `CategoryTheory.HomRel.compClosure_eq_self`：compClosure_eq_self : CompClo
sure r = r
· 使用定理 `CategoryTheory.Congruence.toIsStableUnderPrecomp`：∀ {C : Type u_1} {inst
 : CategoryTheory.Category.{v_1, u_1} C} {r : HomRel C} [self : CategoryTheory.C
ongruence r],   CategoryTheory.HomRel.…
· 使用定理 `CategoryTheory.Congruence.toIsStableUnderPostcomp`：∀ {C : Type u_1} {ins
t : CategoryTheory.Category.{v_1, u_1} C} {r : HomRel C} [self : CategoryTheory.
Congruence r],   CategoryTheory.HomRel.…
· 使用定理 `CategoryTheory.Congruence.equivalence`：∀ {C : Type u_1} {inst : Category
Theory.Category.{v_1, u_1} C} {r : HomRel C} [self : CategoryTheory.Congruence r
]   {X Y : C}, Equivalence …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem functor_map_eq_iff [h : Congruence r] {X Y : C} (f f' : X ⟶ Y) :
    (functor r).map f = (functor r).map f' ↔ r f f' := by
  dsimp [functor]
  rw [Equivalence.quot_mk_eq_iff, HomRel.compClosure_eq_self r]
  simpa only [HomRel.compClosure_eq_self r] using h.equivalence
/-
**CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen** 是 Mathlib 中的一个定
理，位于命名空间 `CategoryTheory.Quotient`。
形式化陈述：functor_homRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) : (functor r)
.homRel f g ↔ Relation.EqvGen (@HomRel.CompClosure C _ r X Y) f g
参数：f g : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.eq`：Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} : Quot.mk r 
x = Quot.mk r y ↔ Relation.EqvGen r x y
-/
theorem functor_homRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) :
    (functor r).homRel f g ↔ Relation.EqvGen (@HomRel.CompClosure C _ r X Y) f g :=
  Quot.eq

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.Quotient.compClosure.congruence** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Quotient.compClosure`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C),   CategoryTheory.Congruence fun X Y => Relation.EqvGen (CategoryTheory.HomR
el.CompClosure r)
参数：r : HomRel C；CategoryTheory.HomRel.CompClosure r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Quotient.functor_homRel_eq_compClosure_eqvGen`：functor_ho
mRel_eq_compClosure_eqvGen {X Y : C} (f g : X ⟶ Y) : (functor r).homRel f g ↔ Re
lation.EqvGen (@HomRel.CompClosure C _ r X Y) f g
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `CategoryTheory.Functor.congruence_homRel`：∀ {C : Type u_2} {D : Type u_3
} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_1 : CategoryTheory.Categ
ory.{v_3, u_3} D] (F : Categor…
-/
theorem compClosure.congruence :
    Congruence fun X Y => Relation.EqvGen (@HomRel.CompClosure C _ r X Y) := by
  convert! (inferInstance : Congruence (functor r).homRel)
  ext
  rw [functor_homRel_eq_compClosure_eqvGen]

variable {D : Type _} [Category* D] (F : C ⥤ D)

/-- The induced functor on the quotient category. -/
@[implicit_reducible]
/-
**CategoryTheory.Quotient.lift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Quotien
t`。
形式化陈述：lift (H : forall (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂
) : Quotient r ⥤ D where obj a
参数：H : forall (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ -> F.map f₁ = F.map f₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced functor on the quotient category.
-/
def lift (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) : Quotient r ⥤ D where
  obj a := F.obj a.as
  map hf :=
    Quot.liftOn hf (fun f ↦ F.map f)
      (by
        rintro _ _ ⟨_, _, _, _, _, _, h⟩
        simp [H _ _ _ _ h])
  map_id a := F.map_id a.as
  map_comp := by
    rintro a b c ⟨f⟩ ⟨g⟩
    exact F.map_comp f g

variable (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂)
/-
**CategoryTheory.Quotient.lift_spec** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Qu
otient`。
形式化陈述：lift_spec : functor r ⋙ lift r F H = F
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_spec : functor r ⋙ lift r F H = F := by
  tauto

set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.Quotient.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Quotient`。
形式化陈述：lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H
参数：Φ : Quotient r ⥤ D；hΦ : functor r ⋙ Φ = F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.hext`：hext {F G : C ⥤ D} (h_obj : forall X, F.obj
 X = G.obj X) (h_map : forall (X Y) (f : X ⟶ Y), F.map f ≍ G.map f) : F = G
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
-/
theorem lift_unique (Φ : Quotient r ⥤ D) (hΦ : functor r ⋙ Φ = F) : Φ = lift r F H := by
  subst_vars
  fapply Functor.hext
  · rintro X
    dsimp [lift, Functor]
    congr
  · rintro _ _ f
    dsimp [lift, Functor]
    refine Quot.inductionOn f fun _ ↦ ?_
    simp only [heq_eq_eq]
    congr
/-
**CategoryTheory.Quotient.lift_unique'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Quotient`。
形式化陈述：lift_unique' (F₁ F₂ : Quotient r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂
) : F₁ = F₂
参数：F₁ F₂ : Quotient r ⥤ D；h : functor r ⋙ F₁ = functor r ⋙ F₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Quotient.sound`：∀ {C : Type u_1} [inst : CategoryTheory.C
ategory.{v_1, u_1} C] (r : HomRel C) {a b : C} {f₁ f₂ : a ⟶ b},   r f₁ f₂ → (Cat
egoryTheory.Quotien…
· 使用定理 `CategoryTheory.Quotient.lift_unique`：lift_unique (Φ : Quotient r ⥤ D) (h
Φ : functor r ⋙ Φ = F) : Φ = lift r F H
-/
lemma lift_unique' (F₁ F₂ : Quotient r ⥤ D) (h : functor r ⋙ F₁ = functor r ⋙ F₂) :
    F₁ = F₂ := by
  rw [lift_unique r (functor r ⋙ F₂) _ F₂ rfl]; swap
  · rintro X Y f g h
    dsimp
    rw [Quotient.sound r h]
  apply lift_unique
  rw [h]

set_option backward.isDefEq.respectTransparency false in
/-- The original functor factors through the induced functor. -/
/-
**CategoryTheory.Quotient.lift.isLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Quotient.lift`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     (r 
: HomRel C) →       {D : Type u_2} →         [inst_1 : CategoryTheory.Category.{
v_2, u_2} D] →           (F : CategoryTheory.Functor C D) →             (H : ∀ (
x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F.map f₂) →               (Catego
ryTheory.Quotient.functor r).comp (CategoryTheory.Quotient.lift r F H) ≅ F
参数：r : HomRel C；F : CategoryTheory.Functor C D；H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), 
r f₁ f₂ → F.map f₁ = F.map f₂；CategoryTheory.Quotient.functor r；CategoryTheory.Q
uotient.lift r F H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The original functor factors through the induced functor.
-/
def lift.isLift : functor r ⋙ lift r F H ≅ F :=
  NatIso.ofComponents fun _ ↦ Iso.refl _

@[simp]
/-
**CategoryTheory.Quotient.lift.isLift_hom** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Quotient.lift`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C) {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Catego
ryTheory.Functor C D)   (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F
.map f₂) (X : C),   (CategoryTheory.Quotient.lift.isLift r F H).hom.app X = Cate
goryTheory.CategoryStruct.id (F.obj X)
参数：r : HomRel C；F : CategoryTheory.Functor C D；H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), 
r f₁ f₂ → F.map f₁ = F.map f₂；X : C；CategoryTheory.Quotient.lift.isLift r F H；F.
obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift.isLift_hom (X : C) : (lift.isLift r F H).hom.app X = 𝟙 (F.obj X) :=
  rfl

@[simp]
/-
**CategoryTheory.Quotient.lift.isLift_inv** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Quotient.lift`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (r : HomRel
 C) {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (F : Catego
ryTheory.Functor C D)   (H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), r f₁ f₂ → F.map f₁ = F
.map f₂) (X : C),   (CategoryTheory.Quotient.lift.isLift r F H).inv.app X = Cate
goryTheory.CategoryStruct.id (F.obj X)
参数：r : HomRel C；F : CategoryTheory.Functor C D；H : ∀ (x y : C) (f₁ f₂ : x ⟶ y), 
r f₁ f₂ → F.map f₁ = F.map f₂；X : C；CategoryTheory.Quotient.lift.isLift r F H；F.
obj X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift.isLift_inv (X : C) : (lift.isLift r F H).inv.app X = 𝟙 (F.obj X) :=
  rfl
/-
**CategoryTheory.Quotient.lift_obj_functor_obj** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Quotient`。
形式化陈述：lift_obj_functor_obj (X : C) : (lift r F H).obj ((functor r).obj X) = F.ob
j X
参数：X : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_obj_functor_obj (X : C) :
    (lift r F H).obj ((functor r).obj X) = F.obj X := rfl
/-
**CategoryTheory.Quotient.lift_map_functor_map** 是 Mathlib 中的一个定理，位于命名空间 `Catego
ryTheory.Quotient`。
形式化陈述：lift_map_functor_map {X Y : C} (f : X ⟶ Y) : (lift r F H).map ((functor r)
.map f) = F.map f
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_map_functor_map {X Y : C} (f : X ⟶ Y) :
    (lift r F H).map ((functor r).map f) = F.map f :=
  rfl

variable {r}
/-
**CategoryTheory.Quotient.natTrans_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Quotient`。
形式化陈述：natTrans_ext {F G : Quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G) (h : whiskerLeft (Quot
ient.functor r) τ₁ = whiskerLeft (Quotient.functor r) τ₂) : τ₁ = τ₂
参数：τ₁ τ₂ : F ⟶ G；h : whiskerLeft (Quotient.functor r) τ₁ = whiskerLeft (Quotient
.functor r) τ₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext`：∀ {C : Type u₁} {inst : CategoryTheory.Cate
gory.{v₁, u₁} C} {D : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} D}   {
F G : CategoryThe…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.NatTrans.congr_app`：congr_app {α β : F ⟶ G} (h : α = β) (
X : C) : α.app X = β.app X
-/
lemma natTrans_ext {F G : Quotient r ⥤ D} (τ₁ τ₂ : F ⟶ G)
    (h : whiskerLeft (Quotient.functor r) τ₁ = whiskerLeft (Quotient.functor r) τ₂) : τ₁ = τ₂ :=
  NatTrans.ext (by ext1 ⟨X⟩; exact NatTrans.congr_app h X)

variable (r)

/-- In order to define a natural transformation `F ⟶ G` with `F G : Quotient r ⥤ D`, it suffices
to do so after precomposing with `Quotient.functor r`. -/
/-
**CategoryTheory.Quotient.natTransLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Quotient`。
形式化陈述：natTransLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Quotient
.functor r ⋙ G) : F ⟶ G where app
参数：τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In order to define a natural transformation `F ⟶ G` with `F G : Quotient r ⥤ D`,
 it suffices
to do so after precomposing with `Quotient.functor r`.
-/
def natTransLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) :
    F ⟶ G where
  app := fun ⟨X⟩ => τ.app X
  naturality := fun ⟨X⟩ ⟨Y⟩ => by
    rintro ⟨f⟩
    exact τ.naturality f

@[simp]
/-
**CategoryTheory.Quotient.natTransLift_app** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTh
eory.Quotient`。
形式化陈述：natTransLift_app (F G : Quotient r ⥤ D) (τ : Quotient.functor r ⋙ F ⟶ Quot
ient.functor r ⋙ G) (X : C) : (natTransLift r τ).app ((Quotient.functor r).obj X
) = τ.app X
参数：F G : Quotient r ⥤ D；τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G；X : 
C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTransLift_app (F G : Quotient r ⥤ D)
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G) (X : C) :
    (natTransLift r τ).app ((Quotient.functor r).obj X) = τ.app X := rfl

@[reassoc]
/-
**CategoryTheory.Quotient.comp_natTransLift** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Quotient`。
形式化陈述：comp_natTransLift {F G H : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ⟶ Q
uotient.functor r ⋙ G) (τ' : Quotient.functor r ⋙ G ⟶ Quotient.functor r ⋙ H) : 
natTransLift r τ ≫ natTransLift r τ' = natTransLift r (τ ≫ τ')
参数：τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G；τ' : Quotient.functor r ⋙
 G ⟶ Quotient.functor r ⋙ H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_natTransLift {F G H : Quotient r ⥤ D}
    (τ : Quotient.functor r ⋙ F ⟶ Quotient.functor r ⋙ G)
    (τ' : Quotient.functor r ⋙ G ⟶ Quotient.functor r ⋙ H) :
    natTransLift r τ ≫ natTransLift r τ' = natTransLift r (τ ≫ τ') := by cat_disch

@[simp]
/-
**CategoryTheory.Quotient.natTransLift_id** 是 Mathlib 中的一个引理，位于命名空间 `CategoryThe
ory.Quotient`。
形式化陈述：natTransLift_id (F : Quotient r ⥤ D) : natTransLift r (𝟙 (Quotient.functor
 r ⋙ F)) = 𝟙 _
参数：F : Quotient r ⥤ D。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma natTransLift_id (F : Quotient r ⥤ D) :
    natTransLift r (𝟙 (Quotient.functor r ⋙ F)) = 𝟙 _ := by cat_disch

/-- In order to define a natural isomorphism `F ≅ G` with `F G : Quotient r ⥤ D`, it suffices
to do so after precomposing with `Quotient.functor r`. -/
@[simps]
/-
**CategoryTheory.Quotient.natIsoLift** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Q
uotient`。
形式化陈述：natIsoLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ≅ Quotient.f
unctor r ⋙ G) : F ≅ G where hom
参数：τ : Quotient.functor r ⋙ F ≅ Quotient.functor r ⋙ G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In order to define a natural isomorphism `F ≅ G` with `F G : Quotient r ⥤ D`, it
 suffices
to do so after precomposing with `Quotient.functor r`.
-/
def natIsoLift {F G : Quotient r ⥤ D} (τ : Quotient.functor r ⋙ F ≅ Quotient.functor r ⋙ G) :
    F ≅ G where
  hom := natTransLift _ τ.hom
  inv := natTransLift _ τ.inv
  hom_inv_id := by rw [comp_natTransLift, τ.hom_inv_id, natTransLift_id]
  inv_hom_id := by rw [comp_natTransLift, τ.inv_hom_id, natTransLift_id]

variable (D)
/-
**CategoryTheory.Quotient.full_whiskeringLeft_functor** 是 Mathlib 中的一个实例，位于命名空间 
`CategoryTheory.Quotient`。
形式化陈述：full_whiskeringLeft_functor : ((whiskeringLeft C _ D).obj (functor r)).Ful
l where map_surjective f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance full_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Full where
  map_surjective f := ⟨natTransLift r f, by cat_disch⟩
/-
**CategoryTheory.Quotient.faithful_whiskeringLeft_functor** 是 Mathlib 中的一个实例，位于命
名空间 `CategoryTheory.Quotient`。
形式化陈述：faithful_whiskeringLeft_functor : ((whiskeringLeft C _ D).obj (functor r))
.Faithful
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Quotient.natTrans_ext`：natTrans_ext {F G : Quotient r ⥤ D
} (τ₁ τ₂ : F ⟶ G) (h : whiskerLeft (Quotient.functor r) τ₁ = whiskerLeft (Quotie
nt.functor r) τ₂) : τ₁ = τ…
-/
instance faithful_whiskeringLeft_functor :
    ((whiskeringLeft C _ D).obj (functor r)).Faithful := ⟨by apply natTrans_ext⟩

end Quotient

namespace Functor

variable {D : Type*} [Category* D] (L : C ⥤ D)

/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.Full] : (Quotient.lift L.homRel L (by simp)).Full where
  map_surjective := by
    rintro ⟨X⟩ ⟨Y⟩ (f : L.obj X ⟶ L.obj Y)
    obtain ⟨f, rfl⟩ := L.map_surjective f
    exact ⟨(Quotient.functor _).map f, rfl⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (Quotient.lift L.homRel L (by simp)).Faithful where
  map_injective := by
    rintro ⟨_⟩ ⟨_⟩ ⟨_⟩ ⟨_⟩ h
    exact Quotient.sound _ h
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.EssSurj] : (Quotient.lift L.homRel L (by simp)).EssSurj where
  mem_essImage X :=
    ⟨(Quotient.functor _).obj (L.objPreimage X), ⟨L.objObjPreimageIso X⟩⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [L.Full] [L.EssSurj] : (Quotient.lift L.homRel L (by simp)).IsEquivalence where

end Functor

end CategoryTheory

