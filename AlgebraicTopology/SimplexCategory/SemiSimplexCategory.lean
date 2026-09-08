/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic

/-!
# The semi-simplex category

We define a category `SemiSimplexCategory` so that semi-simplicial objects
can be defined (TODO) as functors from `SemiSimplexCategoryᵒᵖ` similarly
as simplicial objects are functors from `SimplexCategory`.

-/

@[expose] public section

open CategoryTheory Simplicial

/-- The category whose objects are denoted `⦋n⦌ₛ` for `n : ℕ` and
morphisms `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` are order embeddings `Fin (n.len + 1) ↪o Fin (m.len + 1)`.
(This identifies to a wide subcategory of the category `SemiSimplex`, which
has the "same" objects, and morphisms `Fin (n.len + 1) →o Fin (m.len + 1)`,
see the faithful functor `SemiSimplexCategory.toSimplexCategory`.) -/
@[ext]
/-
**SemiSimplexCategory** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category whose objects are denoted `⦋n⦌ₛ` for `n : ℕ` and
morphisms `⦋n⦌ₛ ⟶ ⦋m⦌ₛ` are order embeddings `Fin (n.len + 1) ↪o Fin (m.len + 1)
`.
(This identifies to a wide subcategory of the category `SemiSimplex`, which
has the "same" objects, and morphisms `Fin (n.len + 1) →o Fin (m.len + 1)`,
see the faithful functor `SemiSimplexCategory.toSimplexCategory`.)
-/
structure SemiSimplexCategory : Type where
  /-- Constructor `ℕ → SemiSimplexCategory`. -/
  mk ::
  /-- The length of an object in `SemiSimplexCategory` -/
  len : ℕ

namespace SemiSimplexCategory

/-- The object of `SemiSimplexCategory` corresponding to `n : ℕ` is denoted `⦋n⦌ₛ`. -/
scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/-- The type of morphisms in the semi-simplex category are order embeddings.
This type is made irreducible: use `SemiSimplexCategory.homEquiv` to make
the conversion. -/
/-
**SemiSimplexCategory.Hom** 是 Mathlib 中的一个定义，位于命名空间 `SemiSimplexCategory`。
形式化陈述：Hom (n m : SemiSimplexCategory)
参数：n m : SemiSimplexCategory。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of morphisms in the semi-simplex category are order embeddings.
This type is made irreducible: use `SemiSimplexCategory.homEquiv` to make
the conversion.
-/
def Hom (n m : SemiSimplexCategory) := Fin (n.len + 1) ↪o Fin (m.len + 1)
/-
**SemiSimplexCategory.smallCategory** 是 Mathlib 中的一个实例，位于命名空间 `SemiSimplexCatego
ry`。
形式化陈述：smallCategory : SmallCategory.{0} SemiSimplexCategory where Hom
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom := Hom
  id _ := .refl _
  comp f g := f.trans g

/-- Morphisms `n ⟶ m` in `SemiSimplexCategory` identify to order embeddings
`Fin (n.len + 1) ↪o Fin (m.len + 1)`. -/
/-
**SemiSimplexCategory.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `SemiSimplexCategory`。
形式化陈述：homEquiv {n m : SemiSimplexCategory} : (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (
m.len + 1))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Morphisms `n ⟶ m` in `SemiSimplexCategory` identify to order embeddings
`Fin (n.len + 1) ↪o Fin (m.len + 1)`.
-/
def homEquiv {n m : SemiSimplexCategory} :
    (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (m.len + 1)) :=
  .refl _

@[simp]
/-
**SemiSimplexCategory.homEquiv_id** 是 Mathlib 中的一个引理，位于命名空间 `SemiSimplexCategory
`。
形式化陈述：homEquiv_id (a : SemiSimplexCategory) : homEquiv (𝟙 a) = .refl _
参数：a : SemiSimplexCategory。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_id (a : SemiSimplexCategory) :
    homEquiv (𝟙 a) = .refl _ := rfl

@[simp]
/-
**SemiSimplexCategory.homEquiv_comp** 是 Mathlib 中的一个引理，位于命名空间 `SemiSimplexCatego
ry`。
形式化陈述：homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) : homE
quiv (f ≫ g) = (homEquiv f).trans (homEquiv g)
参数：f : a ⟶ b；g : b ⟶ c。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = (homEquiv f).trans (homEquiv g) := rfl

attribute [irreducible] Hom

@[ext]
/-
**SemiSimplexCategory.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SemiSimplexCategory`。
形式化陈述：hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b} (h : homEquiv f = homEqu
iv g) : f = g
参数：h : homEquiv f = homEquiv g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b}
    (h : homEquiv f = homEquiv g) : f = g :=
  homEquiv.injective h

/-- The inclusion functor `SemiSimplexCategory ⥤ SimplexCategory`. -/
/-
**SemiSimplexCategory.toSimplexCategory** 是 Mathlib 中的一个定义，位于命名空间 `SemiSimplexCa
tegory`。
形式化陈述：toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where obj n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor `SemiSimplexCategory ⥤ SimplexCategory`.
-/
def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

@[simp]
/-
**SemiSimplexCategory.toSimplexCategory_obj** 是 Mathlib 中的一个引理，位于命名空间 `SemiSimpl
exCategory`。
形式化陈述：toSimplexCategory_obj (n : Nat) : toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toSimplexCategory_obj (n : ℕ) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl
/-
**SemiSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SemiSimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    apply ConcreteCategory.congr_hom h
/-
**SemiSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SemiSimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact (homEquiv f).injective
/-
**SemiSimplexCategory.** 是 Mathlib 中的一个实例，位于命名空间 `SemiSimplexCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

/-- Constructor for morphisms in `SemiSimplexCategory` which takes as an input
a monomorphism in `SimplexCategory`. -/
/-
**SemiSimplexCategory.homOfMono** 是 Mathlib 中的一个定义，位于命名空间 `SemiSimplexCategory`。
形式化陈述：homOfMono {n m : SemiSimplexCategory} (f : toSimplexCategory.obj n ⟶ toSim
plexCategory.obj m) [Mono f] : n ⟶ m
参数：f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Constructor for morphisms in `SemiSimplexCategory` which takes as an input
a monomorphism in `SimplexCategory`.
-/
def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

@[simp]
/-
**SemiSimplexCategory.toSimplexCategory_map_homOfMono** 是 Mathlib 中的一个引理，位于命名空间 
`SemiSimplexCategory`。
形式化陈述：toSimplexCategory_map_homOfMono {n m : SemiSimplexCategory} (f : toSimplex
Category.obj n ⟶ toSimplexCategory.obj m) [Mono f] : toSimplexCategory.map (homO
fMono f) = f
参数：f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimplexCategory.Hom.ext`：∀ {a b : SimplexCategory} (f g : a ⟶ b), Simple
xCategory.Hom.toOrderHom f = SimplexCategory.Hom.toOrderHom g → f = g
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
-/
lemma toSimplexCategory_map_homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] :
    toSimplexCategory.map (homOfMono f) = f := by
  aesop

end SemiSimplexCategory

