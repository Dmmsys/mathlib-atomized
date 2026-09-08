/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.CategoryTheory.Comma.Basic

/-!
# The category of arrows

The category of arrows, with morphisms commutative squares.
We set this up as a specialization of the comma category `Comma L R`,
where `L` and `R` are both the identity functor.

## Tags

comma, arrow
-/

@[expose] public section

namespace CategoryTheory

universe v u

-- morphism levels before object levels. See note [category theory universes].
variable {T : Type u} [Category.{v} T]

variable (T) in
/-- The arrow category of `T` has as objects all morphisms in `T` and as morphisms commutative
squares in `T`. -/
/-
**CategoryTheory.Arrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory`。
形式化陈述：Arrow
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The arrow category of `T` has as objects all morphisms in `T` and as morphisms c
ommutative
squares in `T`.
-/
def Arrow := Comma (𝟭 T) (𝟭 T)

to_dual_name_hint Left Right

/-- The type of morphisms in the category `Arrow T`. -/
@[to_dual self (reorder := f g)]
/-
**CategoryTheory.Arrow.Hom** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：{T : Type u} → [inst : CategoryTheory.Category.{v, u} T] → CategoryTheory.
Arrow T → CategoryTheory.Arrow T → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the category `Arrow T`.
-/
protected def Arrow.Hom (f g : Arrow T) := CommaMorphism f g
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (Arrow T) where
  Hom := Arrow.Hom
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (Arrow T) :=
  inferInstanceAs <| Category (Comma (𝟭 T) (𝟭 T))

namespace Arrow

/-- The left object of an arrow. -/
@[to_dual /-- The right object of an arrow. -/]
/-
**CategoryTheory.Arrow.left** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：left (X : Arrow T) : T
参数：X : Arrow T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left object of an arrow.
-/
abbrev left (X : Arrow T) : T := Comma.left X

/-- Given `X : Arrow T`, this is the morphism `X.left ⟶ X.right`. -/
/-
**CategoryTheory.Arrow.hom** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：hom (X : Arrow T) : X.left ⟶ X.right
参数：X : Arrow T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `X : Arrow T`, this is the morphism `X.left ⟶ X.right`.
-/
abbrev hom (X : Arrow T) : X.left ⟶ X.right := Comma.hom X

/-- The left part of a morphism in the category of arrows. -/
@[to_dual /-- The right part of a morphism in the category of arrows. -/]
/-
**CategoryTheory.Arrow.Hom.left** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow.
Hom`。
形式化陈述：{T : Type u} → [inst : CategoryTheory.Category.{v, u} T] → {X Y : Category
Theory.Arrow T} → (X ⟶ Y) → (X.left ⟶ Y.left)
参数：X ⟶ Y；X.left ⟶ Y.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left part of a morphism in the category of arrows.
-/
abbrev Hom.left {X Y : Arrow T} (f : X ⟶ Y) : X.left ⟶ Y.left := CommaMorphism.left f

@[ext, to_dual self (reorder := X Y, h₁ h₂)]
/-
**CategoryTheory.Arrow.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right
 = g.right) : f = g
参数：f g : X ⟶ Y；h₁ : f.left = g.left；h₂ : f.right = g.right。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommaMorphism.ext`：∀ {A : Type u₁} {inst : CategoryTheory
.Category.{v₁, u₁} A} {B : Type u₂} {inst_1 : CategoryTheory.Category.{v₂, u₂} B
}   {T : Type u₃} {ins…
-/
lemma hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ : f.left = g.left) (h₂ : f.right = g.right) :
    f = g :=
  CommaMorphism.ext h₁ h₂

@[to_dual (attr := simp)]
/-
**CategoryTheory.Arrow.id_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：id_left (f : Arrow T) : Arrow.Hom.left (𝟙 f) = 𝟙 f.left
参数：f : Arrow T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_left (f : Arrow T) : Arrow.Hom.left (𝟙 f) = 𝟙 f.left :=
  rfl

@[to_dual (reorder := f g) (attr := simp, reassoc)]
/-
**CategoryTheory.Arrow.comp_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：comp_left {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).left = f.lef
t ≫ g.left
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_left {X Y Z : Arrow T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).left = f.left ≫ g.left := rfl

/-- An object in the arrow category is simply a morphism in `T`. -/
@[simps, to_dual self, implicit_reducible]
/-
**CategoryTheory.Arrow.mk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：mk {X Y : T} (f : X ⟶ Y) : Arrow T where left
参数：f : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object in the arrow category is simply a morphism in `T`.
-/
def mk {X Y : T} (f : X ⟶ Y) : Arrow T where
  left := X
  right := Y
  hom := f

attribute [to_dual existing] mk_left
attribute [to_dual self] mk_hom

@[simp]
/-
**CategoryTheory.Arrow.mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：mk_eq (f : Arrow T) : Arrow.mk f.hom = f
参数：f : Arrow T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mk_eq (f : Arrow T) : Arrow.mk f.hom = f := by
  cases f
  rfl

@[to_dual none]
/-
**CategoryTheory.Arrow.mk_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
rrow`。
形式化陈述：mk_surjective (f : Arrow T) : exists (X Y : T) (g : X ⟶ Y), f = Arrow.mk g
参数：f : Arrow T。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mk_surjective (f : Arrow T) :
    ∃ (X Y : T) (g : X ⟶ Y), f = Arrow.mk g :=
  ⟨_, _, f.hom, rfl⟩

@[to_dual self]
/-
**CategoryTheory.Arrow.mk_injective** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：mk_injective (A B : T) : Function.Injective (Arrow.mk : (A ⟶ B) -> Arrow T
)
参数：A B : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem mk_injective (A B : T) :
    Function.Injective (Arrow.mk : (A ⟶ B) → Arrow T) := fun f g h => by
  cases h
  rfl

@[to_dual self]
/-
**CategoryTheory.Arrow.mk_inj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g
参数：A B : T。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `CategoryTheory.Arrow.mk_injective`：mk_injective (A B : T) : Function.Inj
ective (Arrow.mk : (A ⟶ B) -> Arrow T)
-/
theorem mk_inj (A B : T) {f g : A ⟶ B} : Arrow.mk f = Arrow.mk g ↔ f = g :=
  (mk_injective A B).eq_iff

@[to_dual self]
/-
**CategoryTheory.Arrow.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : T} : CoeOut (X ⟶ Y) (Arrow T) where
  coe := mk

@[to_dual none, reassoc (attr := simp high)]
/-
**CategoryTheory.Arrow.w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right
参数：sq : f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
theorem w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom = f.hom ≫ sq.right :=
  CommaMorphism.w sq

@[to_dual none, reassoc]
alias Hom.w := w

@[to_dual]
/-
**CategoryTheory.Arrow.hom.congr_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.
Arrow.hom`。
形式化陈述：∀ {T : Type u} [inst : CategoryTheory.Category.{v, u} T] {f g : CategoryTh
eory.Arrow T} {φ₁ φ₂ : f ⟶ g},   φ₁ = φ₂ → CategoryTheory.Arrow.Hom.left φ₁ = Ca
tegoryTheory.Arrow.Hom.left φ₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom.congr_left {f g : Arrow T} {φ₁ φ₂ : f ⟶ g} (h : φ₁ = φ₂) : φ₁.left = φ₂.left := by
  rw [h]

@[to_dual none]
/-
**CategoryTheory.Arrow.iso_w** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = e.inv.left ≫ f.hom ≫ e.hom.rig
ht
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.w_assoc`：∀ {T : Type u} [inst : CategoryTheory.Cate
gory.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g) {Z : T}   (h : g.righ
t ⟶ Z),   Category…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = e.inv.left ≫ f.hom ≫ e.hom.right := by
  simp [← Arrow.comp_right]

@[to_dual none]
/-
**CategoryTheory.Arrow.iso_w'** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g)
 : g = e.inv.left ≫ f ≫ e.hom.right
参数：e : Arrow.mk f ≅ Arrow.mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.iso_w`：iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = 
e.inv.left ≫ f.hom ≫ e.hom.right
-/
theorem iso_w' {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (e : Arrow.mk f ≅ Arrow.mk g) :
    g = e.inv.left ≫ f ≫ e.hom.right :=
  iso_w e
/-
**CategoryTheory.Arrow.eqToHom_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：eqToHom_left {X Y : Arrow T} (h : X = Y) : (eqToHom h).left = eqToHom (by 
rw [h])
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_left {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).left = eqToHom (by rw [h]) := by subst h; rfl
/-
**CategoryTheory.Arrow.eqToHom_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.A
rrow`。
形式化陈述：eqToHom_right {X Y : Arrow T} (h : X = Y) : (eqToHom h).right = eqToHom (b
y rw [h])
参数：h : X = Y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma eqToHom_right {X Y : Arrow T} (h : X = Y) :
    (eqToHom h).right = eqToHom (by rw [h]) := by subst h; rfl
/-
**CategoryTheory.Arrow.mk_eq_mk_iff** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Ar
row`。
形式化陈述：mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y') : Arrow.mk f = Arr
ow.mk f' ↔ exists (hX : X = X') (hY : Y = Y'), f = eqToHom hX ≫ f' ≫ eqToHom hY.
symm
参数：f : X ⟶ Y；f' : X' ⟶ Y'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CategoryTheory.Arrow.eqToHom_left`：eqToHom_left {X Y : Arrow T} (h : X =
 Y) : (eqToHom h).left = eqToHom (by rw [h])
· 使用引理 `CategoryTheory.Arrow.eqToHom_right`：eqToHom_right {X Y : Arrow T} (h : X
 = Y) : (eqToHom h).right = eqToHom (by rw [h])
· 使用定理 `CategoryTheory.Arrow.iso_w`：iso_w {f g : Arrow T} (e : f ≅ g) : g.hom = 
e.inv.left ≫ f.hom ≫ e.hom.right
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶ Y) (f' : X' ⟶ Y') :
    Arrow.mk f = Arrow.mk f' ↔
      ∃ (hX : X = X') (hY : Y = Y'), f = eqToHom hX ≫ f' ≫ eqToHom hY.symm := by
  constructor
  · intro h
    refine ⟨congr_arg Arrow.left h, congr_arg Arrow.right h, ?_⟩
    simpa [eqToHom_left, eqToHom_right] using! iso_w (eqToIso h.symm)
  · rintro ⟨rfl, rfl, h⟩
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h
    rw [h]
/-
**CategoryTheory.Arrow.ext** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂ : f.right = g.right) (h₃ : 
f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = g
参数：h₁ : f.left = g.left；h₂ : f.right = g.right；h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫
 eqToHom h₂.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `CategoryTheory.Arrow.mk_eq_mk_iff`：mk_eq_mk_iff {X Y X' Y' : T} (f : X ⟶
 Y) (f' : X' ⟶ Y') : Arrow.mk f = Arrow.mk f' ↔ exists (hX : X = X') (hY : Y = Y
'), f = eqToHom hX ≫ f'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma ext {f g : Arrow T}
    (h₁ : f.left = g.left) (h₂ : f.right = g.right)
    (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = g :=
  (mk_eq_mk_iff _ _).2 (by simp_all)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Arrow.arrow_mk_comp_eqToHom** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Arrow`。
形式化陈述：arrow_mk_comp_eqToHom {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y') : Arrow.mk (f 
≫ eqToHom h) = Arrow.mk f
参数：f : X ⟶ Y；h : Y = Y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.ext`：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂
 : f.right = g.right) (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = 
g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrow_mk_comp_eqToHom {X Y Y' : T} (f : X ⟶ Y) (h : Y = Y') :
    Arrow.mk (f ≫ eqToHom h) = Arrow.mk f :=
  ext rfl h.symm (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**CategoryTheory.Arrow.arrow_mk_eqToHom_comp** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.Arrow`。
形式化陈述：arrow_mk_eqToHom_comp {X' X Y : T} (f : X ⟶ Y) (h : X' = X) : Arrow.mk (eq
ToHom h ≫ f) = Arrow.mk f
参数：f : X ⟶ Y；h : X' = X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.ext`：ext {f g : Arrow T} (h₁ : f.left = g.left) (h₂
 : f.right = g.right) (h₃ : f.hom = eqToHom h₁ ≫ g.hom ≫ eqToHom h₂.symm) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma arrow_mk_eqToHom_comp {X' X Y : T} (f : X ⟶ Y) (h : X' = X) :
    Arrow.mk (eqToHom h ≫ f) = Arrow.mk f :=
  ext h rfl (by simp)

/-- A morphism in the arrow category is a commutative square connecting two objects of the arrow
    category. -/
@[simps]
/-
**CategoryTheory.Arrow.homMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：homMk {f g : Arrow T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right) (w : u
 ≫ g.hom = f.hom ≫ v
参数：u : f.left ⟶ g.left；v : f.right ⟶ g.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism in the arrow category is a commutative square connecting two objects 
of the arrow
    category.
-/
def homMk {f g : Arrow T} (u : f.left ⟶ g.left) (v : f.right ⟶ g.right)
    (w : u ≫ g.hom = f.hom ≫ v := by cat_disch) : f ⟶ g where
  left := u
  right := v
  w := w

/-- `homMk''` is the dual of `homMk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homMk]
/-
**CategoryTheory.Arrow.homMk''** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：homMk'' {f g : Arrow T} (u : g.right ⟶ f.right) (v : g.left ⟶ f.left) (w :
 g.hom ≫ u = v ≫ f.hom
参数：u : g.right ⟶ f.right；v : g.left ⟶ f.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`homMk''` is the dual of `homMk`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev homMk'' {f g : Arrow T} (u : g.right ⟶ f.right) (v : g.left ⟶ f.left)
    (w : g.hom ≫ u = v ≫ f.hom := by cat_disch) : g ⟶ f :=
  homMk v u
attribute [to_dual none] homMk_left homMk_right

/-- We can also build a morphism in the arrow category out of any commutative square in `T`. -/
@[simps]
/-
**CategoryTheory.Arrow.homMk'** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
 (w : u ≫ g = f ≫ v
参数：u : X ⟶ P；v : Y ⟶ Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can also build a morphism in the arrow category out of any commutative square
 in `T`.
-/
def homMk' {X Y : T} {f : X ⟶ Y} {P Q : T} {g : P ⟶ Q} (u : X ⟶ P) (v : Y ⟶ Q)
    (w : u ≫ g = f ≫ v := by cat_disch) :
    Arrow.mk f ⟶ Arrow.mk g where
  left := u
  right := v
  w := w

/-- `homMk'''` is the dual of `homMk'`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing homMk']
/-
**CategoryTheory.Arrow.homMk'''** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：homMk''' {X Y : T} {f : Y ⟶ X} {P Q : T} {g : Q ⟶ P} (u : P ⟶ X) (v : Q ⟶ 
Y) (w : g ≫ u = v ≫ f
参数：u : P ⟶ X；v : Q ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`homMk'''` is the dual of `homMk'`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev homMk''' {X Y : T} {f : Y ⟶ X} {P Q : T} {g : Q ⟶ P} (u : P ⟶ X) (v : Q ⟶ Y)
    (w : g ≫ u = v ≫ f := by cat_disch) : mk g ⟶ mk f :=
  homMk' v u
attribute [to_dual none] homMk'_left

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc]
/-
**CategoryTheory.Arrow.w_mk_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：w_mk_left {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g) : dsimp% sq.
left ≫ g.hom = f ≫ sq.right
参数：sq : mk f ⟶ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
theorem w_mk_left {X Y : T} {f : X ⟶ Y} {g : Arrow T} (sq : mk f ⟶ g) :
    dsimp% sq.left ≫ g.hom = f ≫ sq.right :=
  sq.w

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc (attr := simp)]
/-
**CategoryTheory.Arrow.w_mk_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq
.left ≫ g = f.hom ≫ sq.right
参数：sq : f ⟶ mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
theorem w_mk_right {f : Arrow T} {X Y : T} {g : X ⟶ Y} (sq : f ⟶ mk g) :
    dsimp% sq.left ≫ g = f.hom ≫ sq.right :=
  sq.w

set_option backward.defeqAttrib.useBackward true in
@[to_dual none, reassoc]
/-
**CategoryTheory.Arrow.w_mk** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：w_mk {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g) : dsimp%
 sq.left ≫ g = f ≫ sq.right
参数：sq : mk f ⟶ mk g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Arrow.Hom.w`：∀ {T : Type u} [inst : CategoryTheory.Catego
ry.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : f ⟶ g),   CategoryTheory.Categ
oryStruct.comp (…
-/
theorem w_mk {X Y X' Y' : T} {f : X ⟶ Y} {g : X' ⟶ Y'} (sq : mk f ⟶ mk g) :
    dsimp% sq.left ≫ g = f ≫ sq.right :=
  sq.w

@[to_dual self (reorder := f g, 6 7)]
/-
**CategoryTheory.Arrow.isIso_of_isIso_left_of_isIso_right** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Arrow`。
形式化陈述：isIso_of_isIso_left_of_isIso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.
left] [IsIso ff.right] : IsIso ff where out
参数：ff : f ⟶ g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `CategoryTheory.Arrow.homMk_left`：∀ {T : Type u} [inst : CategoryTheory.C
ategory.{v, u} T] {f g : CategoryTheory.Arrow T} (u : f.left ⟶ g.left)   (v : f.
right ⟶ g.right)   (w…
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `CategoryTheory.Arrow.homMk_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (u : f.left ⟶ g.left)   (v : f
.right ⟶ g.right)   (w…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
-/
theorem isIso_of_isIso_left_of_isIso_right {f g : Arrow T} (ff : f ⟶ g) [IsIso ff.left]
    [IsIso ff.right] : IsIso ff where
  out := ⟨homMk (inv ff.left) (inv ff.right), by cat_disch⟩

/-- Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes. -/
@[simps!]
/-
**CategoryTheory.Arrow.isoMk** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`。
形式化陈述：isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right) (h : l
.hom ≫ g.hom = f.hom ≫ r.hom
参数：l : f.left ≅ g.left；r : f.right ≅ g.right。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create an isomorphism between arrows,
by providing isomorphisms between the domains and codomains,
and a proof that the square commutes.
-/
def isoMk {f g : Arrow T} (l : f.left ≅ g.left) (r : f.right ≅ g.right)
    (h : l.hom ≫ g.hom = f.hom ≫ r.hom := by cat_disch) : f ≅ g :=
  Comma.isoMk l r h

/-- `isoMk''` is the dual of `isoMk`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing isoMk]
/-
**CategoryTheory.Arrow.isoMk''** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：isoMk'' {f g : Arrow T} (l : f.right ≅ g.right) (r : f.left ≅ g.left) (h :
 g.hom ≫ l.inv = r.inv ≫ f.hom
参数：l : f.right ≅ g.right；r : f.left ≅ g.left。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`isoMk''` is the dual of `isoMk`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev isoMk'' {f g : Arrow T} (l : f.right ≅ g.right) (r : f.left ≅ g.left)
    (h : g.hom ≫ l.inv = r.inv ≫ f.hom := by cat_disch) : f ≅ g :=
  isoMk r l (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)
attribute [to_dual none] isoMk_hom_left isoMk_hom_right isoMk_inv_left isoMk_inv_right

/-- A variant of `Arrow.isoMk` that creates an iso between two `Arrow.mk`s with a better type
signature. -/
/-
**CategoryTheory.Arrow.isoMk'** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arrow`
。
形式化陈述：isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z) (h 
: e₁.hom ≫ g = f ≫ e₂.hom
参数：f : W ⟶ X；g : Y ⟶ Z；e₁ : W ≅ Y；e₂ : X ≅ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `Arrow.isoMk` that creates an iso between two `Arrow.mk`s with a be
tter type
signature.
-/
abbrev isoMk' {W X Y Z : T} (f : W ⟶ X) (g : Y ⟶ Z) (e₁ : W ≅ Y) (e₂ : X ≅ Z)
    (h : e₁.hom ≫ g = f ≫ e₂.hom := by cat_disch) : Arrow.mk f ≅ Arrow.mk g :=
  Arrow.isoMk e₁ e₂ h

/-- `isoMk'''` is the dual of `isoMk'`, which we need for `to_dual`.
Please avoid using this directly. -/
@[to_dual existing isoMk']
/-
**CategoryTheory.Arrow.isoMk'''** 是 Mathlib 中的一个缩写定义，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：isoMk''' {W X Y Z : T} (f : X ⟶ W) (g : Z ⟶ Y) (e₁ : W ≅ Y) (e₂ : X ≅ Z) (
h : g ≫ e₁.inv = e₂.inv ≫ f
参数：f : X ⟶ W；g : Z ⟶ Y；e₁ : W ≅ Y；e₂ : X ≅ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`isoMk'''` is the dual of `isoMk'`, which we need for `to_dual`.
Please avoid using this directly.
-/
abbrev isoMk''' {W X Y Z : T} (f : X ⟶ W) (g : Z ⟶ Y) (e₁ : W ≅ Y)
  (e₂ : X ≅ Z) (h : g ≫ e₁.inv = e₂.inv ≫ f := by cat_disch) : mk f ≅ mk g :=
  isoMk' f g e₂ e₁ (by rwa [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp] at h)

section

variable {f g : Arrow T} (sq : f ⟶ g)

@[to_dual]
/-
**CategoryTheory.Arrow.isIso_left** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：isIso_left [IsIso sq] : IsIso sq.left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
instance isIso_left [IsIso sq] : IsIso sq.left :=
  ⟨(inv sq).left, by simp [← comp_left]⟩

@[to_dual none]
/-
**CategoryTheory.Arrow.isIso_of_isIso'** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Arrow`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isIso_of_isIso' {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] [IsIso f.hom] :
    IsIso g.hom := by
  rw [iso_w (asIso sq)]
  infer_instance

@[to_dual none]
/-
**CategoryTheory.Arrow.isIso_hom_iff_isIso_hom_of_isIso** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Arrow`。
形式化陈述：isIso_hom_iff_isIso_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] :
 IsIso f.hom ↔ IsIso g.hom
参数：sq : f ⟶ g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.CategoryTheory.Comma.Arrow.0.CategoryTheory.Arrow.isIso
_of_isIso'`：∀ {T : Type u} [inst : CategoryTheory.Category.{v, u} T] {f g : Cate
goryTheory.Arrow T} (sq : f ⟶ g)   [CategoryTheory.IsIso sq] [CategoryTh…
-/
lemma isIso_hom_iff_isIso_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g.hom :=
  ⟨fun _ => isIso_of_isIso' sq, fun _ => isIso_of_isIso' (inv sq)⟩

@[to_dual none]
/-
**CategoryTheory.Arrow.isIso_iff_isIso_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Arrow`。
形式化陈述：isIso_iff_isIso_of_isIso {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f 
⟶ mk g) [IsIso sq] : IsIso f ↔ IsIso g
参数：sq : mk f ⟶ mk g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.isIso_hom_iff_isIso_hom_of_isIso`：isIso_hom_iff_isI
so_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] : IsIso f.hom ↔ IsIso g.
hom
-/
lemma isIso_iff_isIso_of_isIso {W X Y Z : T} {f : W ⟶ X} {g : Y ⟶ Z} (sq : mk f ⟶ mk g) [IsIso sq] :
    IsIso f ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual none]
/-
**CategoryTheory.Arrow.isIso_hom_iff_isIso_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Arrow`。
形式化陈述：isIso_hom_iff_isIso_of_isIso {Y Z : T} {f : Arrow T} {g : Y ⟶ Z} (sq : f ⟶
 mk g) [IsIso sq] : IsIso f.hom ↔ IsIso g
参数：sq : f ⟶ mk g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Arrow.isIso_hom_iff_isIso_hom_of_isIso`：isIso_hom_iff_isI
so_hom_of_isIso {f g : Arrow T} (sq : f ⟶ g) [IsIso sq] : IsIso f.hom ↔ IsIso g.
hom
-/
lemma isIso_hom_iff_isIso_of_isIso {Y Z : T} {f : Arrow T} {g : Y ⟶ Z} (sq : f ⟶ mk g) [IsIso sq] :
    IsIso f.hom ↔ IsIso g :=
  isIso_hom_iff_isIso_hom_of_isIso sq

@[to_dual (attr := simp, push ←)]
/-
**CategoryTheory.Arrow.inv_left** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arrow`
。
形式化陈述：inv_left [IsIso sq] : (inv sq).left = inv sq.left
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsIso.eq_inv_of_hom_inv_id`：eq_inv_of_hom_inv_id {f : X ⟶
 Y} [IsIso f] {g : Y ⟶ X} (hom_inv_id : f ≫ g = 𝟙 X) : g = inv f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id`：hom_inv_id (f : X ⟶ Y) [I : IsIso f] : 
f ≫ inv f = 𝟙 X
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_left [IsIso sq] : (inv sq).left = inv sq.left :=
  IsIso.eq_inv_of_hom_inv_id (by simp [← comp_left])

@[to_dual none]
/-
**CategoryTheory.Arrow.left_hom_inv_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Arrow`。
形式化陈述：left_hom_inv_right [IsIso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Arrow.isIso_right`：∀ {T : Type u} [inst : CategoryTheory.
Category.{v, u} T] {f g : CategoryTheory.Arrow T} (sq : g ⟶ f)   [CategoryTheory
.IsIso sq], CategoryTh…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem left_hom_inv_right [IsIso sq] : sq.left ≫ g.hom ≫ inv sq.right = f.hom := by
  simp only [← Category.assoc, IsIso.comp_inv_eq, w]

@[to_dual none]
/-
**CategoryTheory.Arrow.inv_left_hom_right** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Arrow`。
形式化陈述：inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inv_left_hom_right [IsIso sq] : inv sq.left ≫ f.hom ≫ sq.right = g.hom := by
  simp only [w, IsIso.inv_comp_eq]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[to_dual epi_right]
/-
**CategoryTheory.Arrow.mono_left** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Arrow
`。
形式化陈述：mono_left [Mono sq] : Mono sq.left where right_cancellation {Z} φ ψ h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用引理 `CategoryTheory.Arrow.hom_ext`：hom_ext {X Y : Arrow T} (f g : X ⟶ Y) (h₁ 
: f.left = g.left) (h₂ : f.right = g.right) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
-/
instance mono_left [Mono sq] : Mono sq.left where
  right_cancellation {Z} φ ψ h := by
    let aux : (Z ⟶ f.left) → (Arrow.mk (𝟙 Z) ⟶ f) := fun φ =>
      { left := φ
        right := φ ≫ f.hom }
    have : ∀ g, (aux g).right = g ≫ f.hom := fun g => rfl
    change (aux φ).left = (aux ψ).left
    congr 1
    rw [← cancel_mono sq]
    ext
    · exact h
    · simp [this, ← Arrow.w_mk_right, reassoc_of% h]

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Arrow.hom_inv_id_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Arrow`。
形式化陈述：hom_inv_id_left (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙 _
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.comp_left`：comp_left {X Y Z : Arrow T} (f : X ⟶ Y) 
(g : Y ⟶ Z) : (f ≫ g).left = f.left ≫ g.left
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Arrow.id_left`：id_left (f : Arrow T) : Arrow.Hom.left (𝟙 
f) = 𝟙 f.left
-/
lemma hom_inv_id_left (e : f ≅ g) : e.hom.left ≫ e.inv.left = 𝟙 _ := by
  rw [← comp_left, e.hom_inv_id, id_left]

@[to_dual (attr := reassoc (attr := simp))]
/-
**CategoryTheory.Arrow.inv_hom_id_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory
.Arrow`。
形式化陈述：inv_hom_id_left (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙 _
参数：e : f ≅ g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.comp_left`：comp_left {X Y Z : Arrow T} (f : X ⟶ Y) 
(g : Y ⟶ Z) : (f ≫ g).left = f.left ≫ g.left
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Arrow.id_left`：id_left (f : Arrow T) : Arrow.Hom.left (𝟙 
f) = 𝟙 f.left
-/
lemma inv_hom_id_left (e : f ≅ g) : e.inv.left ≫ e.hom.left = 𝟙 _ := by
  rw [← comp_left, e.inv_hom_id, id_left]

end

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a square from an arrow `i` to an isomorphism `p`, express the source part of `sq`
in terms of the inverse of `p`. -/
@[simp]
/-
**CategoryTheory.Arrow.square_to_iso_invert** 是 Mathlib 中的一个定理，位于命名空间 `CategoryT
heory.Arrow`。
形式化陈述：square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.m
k p.hom) : i.hom ≫ sq.right ≫ p.inv = sq.left
参数：i : Arrow T；p : X ≅ Y；sq : i ⟶ Arrow.mk p.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Arrow.w_mk_right`：w_mk_right {f : Arrow T} {X Y : T} {g :
 X ⟶ Y} (sq : f ⟶ mk g) : dsimp% sq.left ≫ g = f.hom ≫ sq.right

--- 原说明 ---
Given a square from an arrow `i` to an isomorphism `p`, express the source part 
of `sq`
in terms of the inverse of `p`.
-/
theorem square_to_iso_invert (i : Arrow T) {X Y : T} (p : X ≅ Y) (sq : i ⟶ Arrow.mk p.hom) :
    i.hom ≫ sq.right ≫ p.inv = sq.left := by
  simpa only [mk_right, Category.assoc] using! (Iso.comp_inv_eq p).mpr (Arrow.w_mk_right sq).symm

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a square from an isomorphism `i` to an arrow `p`, express the target part of `sq`
in terms of the inverse of `i`. -/
/-
**CategoryTheory.Arrow.square_from_iso_invert** 是 Mathlib 中的一个定理，位于命名空间 `Categor
yTheory.Arrow`。
形式化陈述：square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk 
i.hom ⟶ p) : i.inv ≫ sq.left ≫ p.hom = sq.right
参数：i : X ≅ Y；p : Arrow T；sq : Arrow.mk i.hom ⟶ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Arrow.w`：w {f g : Arrow T} (sq : f ⟶ g) : sq.left ≫ g.hom
 = f.hom ≫ sq.right
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a square from an isomorphism `i` to an arrow `p`, express the target part 
of `sq`
in terms of the inverse of `i`.
-/
theorem square_from_iso_invert {X Y : T} (i : X ≅ Y) (p : Arrow T) (sq : Arrow.mk i.hom ⟶ p) :
    i.inv ≫ sq.left ≫ p.hom = sq.right := by
  simp

variable {C : Type u} [Category.{v} C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- A helper construction: given a square between `i` and `f ≫ g`, produce a square between
`i` and `g`, whose top leg uses `f`:
```
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
```
-/
@[simps!]
/-
**CategoryTheory.Arrow.squareToSnd** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Ar
row.mk (f ≫ g)) : i ⟶ Arrow.mk g
参数：sq : i ⟶ Arrow.mk (f ≫ g)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper construction: given a square between `i` and `f ≫ g`, produce a square 
between
`i` and `g`, whose top leg uses `f`:
```
A  → X
     ↓f
↓i   Y             --> A → Y
     ↓g                ↓i  ↓g
B  → Z                 B → Z
```
-/
def squareToSnd {X Y Z : C} {i : Arrow C} {f : X ⟶ Y} {g : Y ⟶ Z} (sq : i ⟶ Arrow.mk (f ≫ g)) :
    i ⟶ Arrow.mk g :=
  Arrow.homMk (sq.left ≫ f) (sq.right) (by simp [w_mk sq])

/-- The functor sending an arrow to its source. -/
@[to_dual (attr := simps!) /-- The functor sending an arrow to its target. -/]
/-
**CategoryTheory.Arrow.leftFunc** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arrow`
。
形式化陈述：leftFunc : Arrow C ⥤ C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending an arrow to its source.
-/
def leftFunc : Arrow C ⥤ C :=
  Comma.fst _ _

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation from `leftFunc` to `rightFunc`, given by the arrow itself. -/
@[simps]
/-
**CategoryTheory.Arrow.leftToRight** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural transformation from `leftFunc` to `rightFunc`, given by the arrow it
self.
-/
def leftToRight : (leftFunc : Arrow C ⥤ C) ⟶ rightFunc where app f := f.hom

end Arrow

namespace Functor

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

set_option backward.defeqAttrib.useBackward true in
/-- A functor `C ⥤ D` induces a functor between the corresponding arrow categories. -/
@[simps]
/-
**CategoryTheory.Functor.mapArrow** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Func
tor`。
形式化陈述：mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where obj a
参数：F : C ⥤ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `C ⥤ D` induces a functor between the corresponding arrow categories.
-/
def mapArrow (F : C ⥤ D) : Arrow C ⥤ Arrow D where
  obj a := Arrow.mk (F.map a.hom)
  map {X Y} f := Arrow.homMk (F.map f.left) (F.map f.right) (by simp [← Functor.map_comp])

attribute [to_dual self (reorder := X Y)] mapArrow_map

variable (C D)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `(C ⥤ D) ⥤ (Arrow C ⥤ Arrow D)` which sends
a functor `F : C ⥤ D` to `F.mapArrow`. -/
@[simps]
/-
**CategoryTheory.Functor.mapArrowFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：mapArrowFunctor : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where obj F
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `(C ⥤ D) ⥤ (Arrow C ⥤ Arrow D)` which sends
a functor `F : C ⥤ D` to `F.mapArrow`.
-/
def mapArrowFunctor : (C ⥤ D) ⥤ (Arrow C ⥤ Arrow D) where
  obj F := F.mapArrow
  map {X Y} τ := { app f := Arrow.homMk (τ.app _) (τ.app _) }

attribute [to_dual self (reorder := X Y)] mapArrowFunctor_map_app

variable {C D}

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌ D`. -/
@[simps]
/-
**CategoryTheory.Functor.mapArrowEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.Functor`。
形式化陈述：mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where functor
参数：e : C ≌ D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `Arrow C ≌ Arrow D` induced by an equivalence `C ≌
 D`.
-/
def mapArrowEquivalence (e : C ≌ D) : Arrow C ≌ Arrow D where
  functor := e.functor.mapArrow
  inverse := e.inverse.mapArrow
  unitIso := Functor.mapIso (mapArrowFunctor C C) e.unitIso
  counitIso := Functor.mapIso (mapArrowFunctor D D) e.counitIso

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.essSurj_mapArrow** 是 Mathlib 中的一个实例，位于命名空间 `CategoryThe
ory.Functor`。
形式化陈述：essSurj_mapArrow (F : C ⥤ D) [F.Full] [F.EssSurj] : F.mapArrow.EssSurj whe
re mem_essImage f
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance essSurj_mapArrow (F : C ⥤ D) [F.Full] [F.EssSurj] :
    F.mapArrow.EssSurj where
  mem_essImage f :=
    ⟨Arrow.mk (F.preimage ((F.objObjPreimageIso _).hom ≫ f.hom ≫
      (F.objObjPreimageIso _).inv)),
        ⟨Arrow.isoMk (F.objObjPreimageIso _) (F.objObjPreimageIso _)⟩⟩
/-
**CategoryTheory.Functor.isEquivalence_mapArrow** 是 Mathlib 中的一个实例，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：isEquivalence_mapArrow (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.map
Arrow
参数：F : C ⥤ D。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance isEquivalence_mapArrow (F : C ⥤ D) [IsEquivalence F] :
    IsEquivalence F.mapArrow :=
  (mapArrowEquivalence (asEquivalence F)).isEquivalence_functor

end Functor

variable {C D : Type*} [Category* C] [Category* D]

set_option backward.defeqAttrib.useBackward true in
/-- The images of `f : Arrow C` by two isomorphic functors `F : C ⥤ D` are
isomorphic arrows in `D`. -/
/-
**CategoryTheory.Arrow.isoOfNatIso** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：{C : Type u_1} →   {D : Type u_2} →     [inst : CategoryTheory.Category.{v
_1, u_1} C] →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         {F
 G : CategoryTheory.Functor C D} →           (F ≅ G) → (f : CategoryTheory.Arrow
 C) → F.mapArrow.obj f ≅ G.mapArrow.obj f
参数：F ≅ G；f : CategoryTheory.Arrow C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The images of `f : Arrow C` by two isomorphic functors `F : C ⥤ D` are
isomorphic arrows in `D`.
-/
def Arrow.isoOfNatIso {F G : C ⥤ D} (e : F ≅ G)
    (f : Arrow C) : F.mapArrow.obj f ≅ G.mapArrow.obj f :=
  Arrow.isoMk (e.app f.left) (e.app f.right)

variable (T)

/-- `Arrow T` is equivalent to a sigma type. -/
@[simps!]
/-
**CategoryTheory.Arrow.equivSigma** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Arro
w`。
形式化陈述：(T : Type u) → [inst : CategoryTheory.Category.{v, u} T] → CategoryTheory.
Arrow T ≃ (X : T) × (Y : T) × (X ⟶ Y)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Arrow T` is equivalent to a sigma type.
-/
def Arrow.equivSigma :
    Arrow T ≃ Σ (X Y : T), X ⟶ Y where
  toFun f := ⟨_, _, f.hom⟩
  invFun x := Arrow.mk x.2.2

/-- The equivalence `Arrow (Discrete S) ≃ S`. -/
/-
**CategoryTheory.Arrow.discreteEquiv** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.A
rrow`。
形式化陈述：(S : Type u) → CategoryTheory.Arrow (CategoryTheory.Discrete S) ≃ S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence `Arrow (Discrete S) ≃ S`.
-/
def Arrow.discreteEquiv (S : Type u) : Arrow (Discrete S) ≃ S where
  toFun f := f.left.as
  invFun s := Arrow.mk (𝟙 (Discrete.mk s))
  left_inv := by
    rintro ⟨⟨_⟩, ⟨_⟩, f⟩
    obtain rfl := Discrete.eq_of_hom f
    rfl

/-- Extensionality lemma for functors `C ⥤ D` which uses as an assumption
that the induced maps `Arrow C → Arrow D` coincide. -/
@[to_dual self]
/-
**CategoryTheory.Arrow.functor_ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Arr
ow`。
形式化陈述：∀ {C : Type u_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1}
 C]   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {F G : CategoryTheory.Func
tor C D},   (∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.mapArrow.obj (CategoryTheory.Arrow.mk f)
 = G.mapArrow.obj (CategoryTheory.Arrow.mk f)) →     F = G
参数：∀ ⦃X Y : C⦄ (f : X ⟶ Y), F.mapArrow.obj (CategoryTheory.Arrow.mk f) = G.mapAr
row.obj (CategoryTheory.Arrow.mk f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.ext`：ext {F G : C ⥤ D} (h_obj : forall X, F.obj X
 = G.obj X) (h_map : forall X Y f, F.map f = eqToHom (h_obj X) ≫ G.map f ≫ eqToH
om (h_obj Y).sym…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.mapArrow_obj`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂
} D]   (F : CategoryTheor…

--- 原说明 ---
Extensionality lemma for functors `C ⥤ D` which uses as an assumption
that the induced maps `Arrow C → Arrow D` coincide.
-/
lemma Arrow.functor_ext {F G : C ⥤ D} (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y),
    F.mapArrow.obj (Arrow.mk f) = G.mapArrow.obj (Arrow.mk f)) :
    F = G :=
  Functor.ext (fun X ↦ congr_arg Comma.left (h (𝟙 X))) (fun X Y f ↦ by
    have := h f
    simp only [Functor.mapArrow_obj, mk_eq_mk_iff] at this
    tauto)

end CategoryTheory

