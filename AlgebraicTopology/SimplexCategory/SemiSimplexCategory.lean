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
/--
Definition of `SemiSimplexCategory` / `SemiSimplexCategory` 的定义

English:
structure SemiSimplexCategory
  parameters: : Type where
  axioms and operations (2):
    - mk : :
    - len : Nat

中文:
结构 SemiSimplex范畴
  参数: : 类型 where
  公理与运算 (2 个):
    - mk : :
    - len : 自然数
-/
structure SemiSimplexCategory : Type where
  /-- Constructor `ℕ → SemiSimplexCategory`. -/
  mk ::
  /-- The length of an object in `SemiSimplexCategory` -/
  len : Nat

namespace SemiSimplexCategory

/-- The object of `SemiSimplexCategory` corresponding to `n : ℕ` is denoted `⦋n⦌ₛ`. -/
scoped[Simplicial] notation "⦋" n "⦌ₛ" => SemiSimplexCategory.mk n

/--
Definition of `Hom` / `Hom` 的定义

English:
definition Hom
  signature: (n m : SemiSimplexCategory)
  body: Fin (n.len + 1) ↪o Fin (m.len + 1)

中文:
定义 态射
  签名: (n m : SemiSimplex范畴)
  定义体: Fin (n.len + 1) ↪o Fin (m.len + 1)

Depends on / 依赖: m.len, n.len
-/
def Hom (n m : SemiSimplexCategory) := Fin (n.len + 1) ↪o Fin (m.len + 1)

/--
Instance `smallCategory` / 实例 `smallCategory`

English:
instance smallCategory
  signature: : SmallCategory.{0} SemiSimplexCategory where
  body: Hom
  id _ := .refl _
  comp f g := f.trans g

中文:
实例 smallCategory
  签名: : 小范畴.{0} SemiSimplex范畴 where
  定义体: Hom
  id _ := .refl _
  comp f g := f.trans g
-/
instance smallCategory : SmallCategory.{0} SemiSimplexCategory where
  Hom := Hom
  id _ := .refl _
  comp f g := f.trans g

/--
Definition of `homEquiv` / `homEquiv` 的定义

English:
definition homEquiv
  signature: {n m : SemiSimplexCategory}
  body: .refl _

@[simp]

中文:
定义 homEquiv
  签名: {n m : SemiSimplex范畴}
  定义体: .refl _

@[simp]
-/
def homEquiv {n m : SemiSimplexCategory} :
    (n ⟶ m) ≃ (Fin (n.len + 1) ↪o Fin (m.len + 1)) :=
  .refl _

@[simp]
/--
lemma `homEquiv_id` / 引理 `homEquiv_id`

English:
lemma homEquiv_id
  given: (a : SemiSimplexCategory)
  proof: rfl

@[simp]

中文:
引理 homEquiv_id
  条件: (a : SemiSimplex范畴)
  证明: rfl

@[simp]
-/
lemma homEquiv_id (a : SemiSimplexCategory) :
    homEquiv (𝟙 a) = .refl _ := rfl

@[simp]
/--
lemma `homEquiv_comp` / 引理 `homEquiv_comp`

English:
lemma homEquiv_comp
  given: {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c)
  proof: rfl

中文:
引理 homEquiv_comp
  条件: {a b c : SemiSimplex范畴} (f : a ⟶ b) (g : b ⟶ c)
  证明: rfl
-/
lemma homEquiv_comp {a b c : SemiSimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    homEquiv (f ≫ g) = (homEquiv f).trans (homEquiv g) := rfl

attribute [irreducible] Hom

@[ext]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {a b : SemiSimplexCategory} {f g : a ⟶ b}
  proof: homEquiv.injective h

中文:
定理 hom_ext
  结论: {a b : SemiSimplex范畴} {f g : a ⟶ b}
  证明: homEquiv.injective h

Depends on / 依赖: homEquiv, homEquiv.injective, injective
-/
theorem hom_ext {a b : SemiSimplexCategory} {f g : a ⟶ b}
    (h : homEquiv f = homEquiv g) : f = g :=
  homEquiv.injective h

/--
Definition of `toSimplexCategory` / `toSimplexCategory` 的定义

English:
definition toSimplexCategory
  signature: : SemiSimplexCategory ⥤ SimplexCategory where
  body: ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

@[simp]

中文:
定义 toSimplexCategory
  签名: : SemiSimplex范畴 ⥤ 单纯形范畴 where
  定义体: ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

@[simp]

Depends on / 依赖: n.len
-/
def toSimplexCategory : SemiSimplexCategory ⥤ SimplexCategory where
  obj n := ⦋n.len⦌
  map f := SimplexCategory.Hom.mk (homEquiv f).toOrderHom

@[simp]
/--
lemma `toSimplexCategory_obj` / 引理 `toSimplexCategory_obj`

English:
lemma toSimplexCategory_obj
  given: (n : Nat)
  proof: rfl

中文:
引理 toSimplexCategory_obj
  条件: (n : 自然数)
  证明: rfl
-/
lemma toSimplexCategory_obj (n : Nat) :
    toSimplexCategory.obj ⦋n⦌ₛ = ⦋n⦌ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: toSimplexCategory.Faithful
  body: by
    ext : 2
    apply ConcreteCategory.congr_hom h

中文:
实例 :
  签名: toSimplexCategory.忠实
  定义体: by
    ext : 2
    apply ConcreteCategory.congr_hom h

Depends on / 依赖: ConcreteCategory, ConcreteCategory.congr_hom, congr_hom
-/
instance : toSimplexCategory.Faithful where
  map_injective h := by
    ext : 2
    apply ConcreteCategory.congr_hom h

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono (toSimplexCategory.map f) := by
  rw [SimplexCategory.mono_iff_injective]
  exact (homEquiv f).injective

instance {n m : SemiSimplexCategory} (f : n ⟶ m) : Mono f where
  right_cancellation g₁ g₂ h := by
    apply toSimplexCategory.map_injective
    simp only [← cancel_mono (toSimplexCategory.map f), ← Functor.map_comp, h]

/--
Definition of `homOfMono` / `homOfMono` 的定义

English:
definition homOfMono
  signature: {n m : SemiSimplexCategory}
  body: homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

@[simp]

中文:
定义 homOfMono
  签名: {n m : SemiSimplex范畴}
  定义体: homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

@[simp]

Depends on / 依赖: OrderEmbedding, OrderEmbedding.ofStrictMono, SimplexCategory, SimplexCategory.Hom.toOrderHom, SimplexCategory.mono_iff_injective, f.toOrderHom, homEquiv, homEquiv.symm, mono_iff_injective, monotone, monotone.strictMono_of_injective, ofStrictMono, strictMono_of_injective, toOrderHom
-/
def homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] : n ⟶ m :=
  homEquiv.symm (OrderEmbedding.ofStrictMono f.toOrderHom
    ((SimplexCategory.Hom.toOrderHom f).monotone.strictMono_of_injective
      (by rwa [← SimplexCategory.mono_iff_injective])))

@[simp]
/--
lemma `toSimplexCategory_map_homOfMono` / 引理 `toSimplexCategory_map_homOfMono`

English:
lemma toSimplexCategory_map_homOfMono
  statement: {n m : SemiSimplexCategory}
  proof: by
  aesop

中文:
引理 toSimplexCategory_map_homOfMono
  结论: {n m : SemiSimplex范畴}
  证明: by
  aesop
-/
lemma toSimplexCategory_map_homOfMono {n m : SemiSimplexCategory}
    (f : toSimplexCategory.obj n ⟶ toSimplexCategory.obj m) [Mono f] :
    toSimplexCategory.map (homOfMono f) = f := by
  aesop

end SemiSimplexCategory
