/-
Copyright (c) 2026 Jakob Scharmberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scharmberg
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Topological Pairs

In this file we introduce `TopPair`, the category of topological pairs. It is defined as the
category of arrows in `TopCat` which are topological embeddings.

We provide the inclusion and diagonal functors `TopCat ⥤ TopPair` and show that they are left and
right adjoint to the first projection functor, respectively.

We also define for two morphisms of topological pairs `f, g : X ⟶ Y` the structure `Homotopy f g` of
homotopies between them.
-/

@[expose] public section

universe u

open TopologicalSpace TopCat CategoryTheory MonoidalCategory

/-- A pair of topological spaces consists of an embedding `f : A ⟶ X` in `TopCat`. -/
/-
**TopPair** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：TopPair
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of topological spaces consists of an embedding `f : A ⟶ X` in `TopCat`.
-/
abbrev TopPair :=
  MorphismProperty.Arrow TopCat.isEmbedding ⊤ ⊤

namespace TopPair

variable {X Y : TopPair.{u}}

/-- The first space of the pair -/
/-
**TopPair.fst** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：fst : TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first space of the pair
-/
abbrev fst : TopCat.{u} := X.right

/-- The second space of the pair -/
/-
**TopPair.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：snd : TopCat.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second space of the pair
-/
abbrev snd : TopCat.{u} := X.left

/-- The embedding of the second into the first space -/
/-
**TopPair.map** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：map : X.snd ⟶ X.fst
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The embedding of the second into the first space
-/
abbrev map : X.snd ⟶ X.fst := X.hom
/-
**TopPair.isEmbedding_map** 是 Mathlib 中的一个引理，位于命名空间 `TopPair`。
形式化陈述：isEmbedding_map (X : TopPair.{u}) : Topology.IsEmbedding X.map
参数：X : TopPair.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.Comma.prop`：∀ {A : Type u_1} [inst : Cat
egoryTheory.Category.{v_1, u_1} A] {B : Type u_2}   [inst_1 : CategoryTheory.Cat
egory.{v_2, u_2} B] {T : Type u_…
-/
lemma isEmbedding_map (X : TopPair.{u}) : Topology.IsEmbedding X.map := X.prop

/-- Construct a topological pair from its components. -/
/-
**TopPair.of** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：of {A X : TopCat.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f) : TopPair.{
u}
参数：f : A ⟶ X；h : Topology.IsEmbedding f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a topological pair from its components.
-/
abbrev of {A X : TopCat.{u}} (f : A ⟶ X) (h : Topology.IsEmbedding f) : TopPair.{u} :=
  MorphismProperty.Arrow.mk (P := TopCat.isEmbedding) f h

/-- Constructor for a topological pair (X, A) where A ⊆ X. -/
/-
**TopPair.ofSubset** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：ofSubset {X : TopCat.{u}} (A : Set X) : TopPair.{u}
参数：A : Set X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for a topological pair (X, A) where A ⊆ X.
-/
abbrev ofSubset {X : TopCat.{u}} (A : Set X) : TopPair.{u} := TopPair.of (A := (TopCat.of A))
  (X := X) (TopCat.ofHom { toFun := Subtype.val }) Topology.IsEmbedding.subtypeVal

/-- Constructs the topological pair `(X, ∅)` from `X : TopCat`. -/
/-
**TopPair.ofTopCat** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：ofTopCat (X : TopCat.{u}) : TopPair.{u}
参数：X : TopCat.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructs the topological pair `(X, ∅)` from `X : TopCat`.
-/
abbrev ofTopCat (X : TopCat.{u}) : TopPair.{u} :=
  TopPair.of (TopCat.isInitialPEmpty.to X) (Topology.IsOpenEmbedding.of_isEmpty _).1

/-- Construct a morphism in `TopPair` from its components. -/
/-
**TopPair.ofHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f
参数：f : X.fst ⟶ Y.fst；g : X.snd ⟶ Y.snd。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Construct a morphism in `TopPair` from its components.
-/
abbrev ofHom (f : X.fst ⟶ Y.fst) (g : X.snd ⟶ Y.snd) (w : g ≫ Y.map = X.map ≫ f := by cat_disch) :=
  MorphismProperty.Arrow.homMk g f w

variable {X Y Z : TopPair.{u}}

/-- The map between the first spaces -/
/-
**TopPair.Hom.fst** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Hom`。
形式化陈述：{X Y : TopPair} → (X ⟶ Y) → (TopPair.fst ⟶ TopPair.fst)
参数：X ⟶ Y；TopPair.fst ⟶ TopPair.fst。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The map between the first spaces
-/
abbrev Hom.fst (f : X ⟶ Y) : X.fst ⟶ Y.fst := f.hom.right

/-- The map between the second spaces -/
/-
**TopPair.Hom.snd** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Hom`。
形式化陈述：{X Y : TopPair} → (X ⟶ Y) → (TopPair.snd ⟶ TopPair.snd)
参数：X ⟶ Y；TopPair.snd ⟶ TopPair.snd。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The map between the second spaces
-/
abbrev Hom.snd (f : X ⟶ Y) : X.snd ⟶ Y.snd := f.hom.left

@[reassoc, elementwise]
/-
**TopPair.Hom.w** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Hom`。
形式化陈述：∀ {X Y : TopPair} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp (TopPa
ir.Hom.snd f) TopPair.map =     CategoryTheory.CategoryStruct.comp TopPair.map (
TopPair.Hom.fst f)
参数：f : X ⟶ Y；TopPair.Hom.snd f；TopPair.Hom.fst f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `CategoryTheory.CommaMorphism.w`：∀ {A : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} A] {B : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} B] 
  {T : Type u₃} [ins…
-/
lemma Hom.w {X Y : TopPair.{u}} (f : X ⟶ Y) :
    Hom.snd f ≫ Y.map = X.map ≫ Hom.fst f :=
  f.hom.w

attribute [local simp] Hom.w_apply

/-- The functor from topological pairs to topological spaces that forgets the second space, i.e. the
projection to the first space. -/
/-
**TopPair.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from topological pairs to topological spaces that forgets the second
 space, i.e. the
projection to the first space.
-/
abbrev proj₁ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.rightFunc

/-- The functor from topological pairs to topological spaces that forgets the first space, i.e. the
projection to the second space. -/
/-
**TopPair.proj** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor from topological pairs to topological spaces that forgets the first 
space, i.e. the
projection to the second space.
-/
abbrev proj₂ : TopPair.{u} ⥤ TopCat.{u} :=
  MorphismProperty.Arrow.forget _ _ _ ⋙ CategoryTheory.Arrow.leftFunc

/-- The inclusion functor from topological spaces to topological pairs that sends a space X to
(X, ∅). -/
@[simps]
/-
**TopPair.incl** 是 Mathlib 中的一个定义，位于命名空间 `TopPair`。
形式化陈述：incl : TopCat.{u} ⥤ TopPair.{u} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The inclusion functor from topological spaces to topological pairs that sends a 
space X to
(X, ∅).
-/
def incl : TopCat.{u} ⥤ TopPair.{u} where
  obj X := ofTopCat X
  map f := TopPair.ofHom f (𝟙 _) <| by ext x; induction x

/-- The functor from topological spaces to topological pairs that sends a space X to the identity
morphism on X. -/
/-
**TopPair.diag** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：diag : TopCat.{u} ⥤ TopPair.{u} where obj X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The functor from topological spaces to topological pairs that sends a space X to
 the identity
morphism on X.
-/
abbrev diag : TopCat.{u} ⥤ TopPair.{u} where
  obj X := TopPair.of (𝟙 X) Topology.IsEmbedding.id
  map f := TopPair.ofHom f f

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The inclusion functor is left adjoint to the projection to the first component. -/
@[simps]
/-
**TopPair.inclAdjProj** 是 Mathlib 中的一个定义，位于命名空间 `TopPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion functor is left adjoint to the projection to the first component.
-/
def inclAdjProj₁ : incl ⊣ proj₁ where
  unit.app X := 𝟙 X
  counit.app X := TopPair.ofHom (𝟙 X.fst) (TopCat.isInitialPEmpty.to X.snd)

/-- The projection functor to the first component is left adjoint to the diagonal functor. -/
@[simps]
/-
**TopPair.proj** 是 Mathlib 中的一个定义，位于命名空间 `TopPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection functor to the first component is left adjoint to the diagonal fu
nctor.
-/
def proj₁AdjDiag : proj₁ ⊣ diag where
  unit.app X := TopPair.ofHom (𝟙 X.fst) X.map
  unit.naturality X Y f := MorphismProperty.Arrow.Hom.ext f.w (by cat_disch)
  counit.app X := 𝟙 X

set_option backward.defeqAttrib.useBackward true in
/-- The unique morphism (X, ∅) ⟶ (X, A) that is the identity on X. -/
/-
**TopPair.j** 是 Mathlib 中的一个缩写定义，位于命名空间 `TopPair`。
形式化陈述：j (X : TopPair.{u}) : TopPair.incl.obj X.fst ⟶ X
参数：X : TopPair.{u}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
The unique morphism (X, ∅) ⟶ (X, A) that is the identity on X.
-/
abbrev j (X : TopPair.{u}) : TopPair.incl.obj X.fst ⟶ X :=
  TopPair.ofHom (𝟙 _) (TopCat.isInitialPEmpty.to _)

/-- A homotopy of maps between topological pairs is a homotopy on the first space and a homotopy on
the second space that fit in a commutative square with the maps of the pairs. -/
@[ext]
/-
**TopPair.Homotopy** 是 Mathlib 中的一个结构，位于命名空间 `TopPair`。
形式化陈述：Homotopy (f g : X ⟶ Y) where /-- The homotopy on the first space. -/ fst :
 TopCat.Homotopy (Hom.fst f) (Hom.fst g) /-- The homotopy on the second space. -
/ snd : TopCat.Homotopy (Hom.snd f) (Hom.snd g) /-- The proof that the homotopie
s fit into a commutative square with the maps of the pairs. -/ w : X.map ▷ _ ≫ f
st.h = snd.h ≫ Y.map
参数：f g : X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A homotopy of maps between topological pairs is a homotopy on the first space an
d a homotopy on
the second space that fit in a commutative square with the maps of the pairs.
-/
structure Homotopy (f g : X ⟶ Y) where
  /-- The homotopy on the first space. -/
  fst : TopCat.Homotopy (Hom.fst f) (Hom.fst g)
  /-- The homotopy on the second space. -/
  snd : TopCat.Homotopy (Hom.snd f) (Hom.snd g)
  /-- The proof that the homotopies fit into a commutative square with the maps of the pairs. -/
  w : X.map ▷ _ ≫ fst.h = snd.h ≫ Y.map := by cat_disch

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
attribute [reassoc, elementwise] Homotopy.w
attribute [local simp] Homotopy.w Homotopy.w_apply

namespace Homotopy

@[local simp]
/-
**TopPair.Homotopy.w_apply'** 是 Mathlib 中的一个引理，位于命名空间 `TopPair.Homotopy`。
形式化陈述：w_apply' {f g : X ⟶ Y} (H : Homotopy f g) (x : TopPair.snd) (t : unitInter
val) : H.fst (t, X.map x) = Y.map (H.snd (t, x))
参数：H : Homotopy f g；x : TopPair.snd；t : unitInterval。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `TopPair.Homotopy.w_apply`：∀ {X Y : TopPair} {f g : X ⟶ Y} (self : TopPai
r.Homotopy f g)   (x : ↑(CategoryTheory.MonoidalCategoryStruct.tensorObj TopPair
.snd TopCat.I)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Homeomorph.apply_symm_apply`：apply_symm_apply (h : X ≃ₜ Y) (y : Y) : h (
h.symm y) = y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma w_apply' {f g : X ⟶ Y} (H : Homotopy f g) (x : TopPair.snd) (t : unitInterval) :
    H.fst (t, X.map x) = Y.map (H.snd (t, x)) := by
  have := w_apply H (x, I.homeomorph.symm t)
  cat_disch

/-- Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
`TopCat.Homotopy.refl` on the first and second components.
-/
@[simps]
/-
**TopPair.Homotopy.refl** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Homotopy`。
形式化陈述：refl (f : X ⟶ Y) : Homotopy f f where fst
参数：f : X ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Given a morphism `f` of topological pairs, we can define a `Homotopy f f` by
`TopCat.Homotopy.refl` on the first and second components.
-/
def refl (f : X ⟶ Y) : Homotopy f f where
  fst := TopCat.Homotopy.refl (Hom.fst f)
  snd := TopCat.Homotopy.refl (Hom.snd f)
/-
**TopPair.Homotopy.** 是 Mathlib 中的一个实例，位于命名空间 `TopPair.Homotopy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Homotopy (𝟙 X) (𝟙 X)) :=
  ⟨Homotopy.refl _⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `TopCat.Homotopy.symm` on
the first and second components.
-/
@[simps]
/-
**TopPair.Homotopy.symm** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Homotopy`。
形式化陈述：symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where fst
参数：F : Homotopy f₀ f₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Given a `Homotopy f₀ f₁`, we can define a `Homotopy f₁ f₀` by `TopCat.Homotopy.s
ymm` on
the first and second components.
-/
def symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : Homotopy f₁ f₀ where
  fst := F.fst.symm
  snd := F.snd.symm

@[simp]
/-
**TopPair.Homotopy.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Homotopy`。
形式化陈述：symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F
参数：F : Homotopy f₀ f₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `TopPair.Homotopy.ext`：∀ {X Y : TopPair} {f g : X ⟶ Y} {x y : TopPair.Hom
otopy f g}, x.fst = y.fst → x.snd = y.snd → x = y
· 使用定理 `ContinuousMap.Homotopy.ext`：ext {F G : Homotopy f₀ f₁} (h : forall x, F 
x = G x) : F = G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TopPair.Homotopy.symm_fst`：∀ {X Y : TopPair} {f₀ f₁ : X ⟶ Y} (F : TopPai
r.Homotopy f₀ f₁), F.symm.fst = F.fst.symm
· 使用定理 `ContinuousMap.Homotopy.symm_symm`：symm_symm {f₀ f₁ : C(X, Y)} (F : Homot
opy f₀ f₁) : F.symm.symm = F
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TopPair.Homotopy.symm_snd`：∀ {X Y : TopPair} {f₀ f₁ : X ⟶ Y} (F : TopPai
r.Homotopy f₀ f₁), F.symm.snd = F.snd.symm
-/
theorem symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f₁) : F.symm.symm = F := by
  cat_disch
/-
**TopPair.Homotopy.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Homotopy`。
形式化陈述：symm_bijective {f₀ f₁ : X ⟶ Y} : Function.Bijective (Homotopy.symm : Homot
opy f₀ f₁ -> Homotopy f₁ f₀)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `TopPair.Homotopy.symm_symm`：symm_symm {f₀ f₁ : X ⟶ Y} (F : Homotopy f₀ f
₁) : F.symm.symm = F
-/
theorem symm_bijective {f₀ f₁ : X ⟶ Y} :
    Function.Bijective (Homotopy.symm : Homotopy f₀ f₁ → Homotopy f₁ f₀) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

set_option backward.isDefEq.respectTransparency.types false in
/--
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
`TopCat.Homotopy.trans` on the first and second components.
-/
@[simps]
/-
**TopPair.Homotopy.trans** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Homotopy`。
形式化陈述：trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : Homot
opy f₀ f₂ where fst
参数：F : Homotopy f₀ f₁；G : Homotopy f₁ f₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Given `Homotopy f₀ f₁` and `Homotopy f₁ f₂`, we can define a `Homotopy f₀ f₂` by
`TopCat.Homotopy.trans` on the first and second components.
-/
noncomputable def trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    Homotopy f₀ f₂ where
  fst := F.fst.trans G.fst
  snd := F.snd.trans G.snd
  w := by
    ext ⟨_, _⟩
    simp only [TopCat.comp_app, Homotopy.h_hom_apply, ContinuousMap.Homotopy.trans_apply]
    cat_disch
/-
**TopPair.Homotopy.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Homotopy`。
形式化陈述：symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : 
(F.trans G).symm = G.symm.trans F.symm
参数：F : Homotopy f₀ f₁；G : Homotopy f₁ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `TopPair.Homotopy.ext`：∀ {X Y : TopPair} {f g : X ⟶ Y} {x y : TopPair.Hom
otopy f g}, x.fst = y.fst → x.snd = y.snd → x = y
· 使用定理 `ContinuousMap.Homotopy.symm_trans`：symm_trans {f₀ f₁ f₂ : C(X, Y)} (F : 
Homotopy f₀ f₁) (G : Homotopy f₁ f₂) : (F.trans G).symm = G.symm.trans F.symm
-/
theorem symm_trans {f₀ f₁ f₂ : X ⟶ Y} (F : Homotopy f₀ f₁) (G : Homotopy f₁ f₂) :
    (F.trans G).symm = G.symm.trans F.symm := by
      ext : 1 <;> exact ContinuousMap.Homotopy.symm_trans _ _

set_option backward.isDefEq.respectTransparency false in
/-- If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, we can define a
`Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)` by `TopCat.Homotopy.comp` on the first and second components.
-/
@[simps]
/-
**TopPair.Homotopy.comp** 是 Mathlib 中的一个定义，位于命名空间 `TopPair.Homotopy`。
形式化陈述：comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀
 f₁) : Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where fst
参数：G : Homotopy g₀ g₁；F : Homotopy f₀ f₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
If we have a `Homotopy g₀ g₁` and a `Homotopy f₀ f₁`, we can define a
`Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁)` by `TopCat.Homotopy.comp` on the first and second
 components.
-/
def comp {f₀ f₁ : X ⟶ Y} {g₀ g₁ : Y ⟶ Z} (G : Homotopy g₀ g₁) (F : Homotopy f₀ f₁) :
    Homotopy (f₀ ≫ g₀) (f₁ ≫ g₁) where
  fst := G.fst.comp F.fst
  snd := G.snd.comp F.snd

end Homotopy

/-- Two maps between topological pairs are homotopic if there is a homotopy between them. -/
/-
**TopPair.Homotopic** 是 Mathlib 中的一个定义，位于命名空间 `TopPair`。
形式化陈述：Homotopic (f g : X ⟶ Y)
参数：f g : X ⟶ Y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative

--- 原说明 ---
Two maps between topological pairs are homotopic if there is a homotopy between 
them.
-/
def Homotopic (f g : X ⟶ Y) := Nonempty (Homotopy f g)

namespace Homotopic

/-- Two maps of topological pairs being homotopic defines an equivalence relation. -/
/-
**TopPair.Homotopic.equivalence** 是 Mathlib 中的一个定理，位于命名空间 `TopPair.Homotopic`。
形式化陈述：equivalence : Equivalence (Homotopic (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.MorphismProperty.IsMultiplicative.instTop`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C], ⊤.IsMultiplicative
· 使用定理 `Nonempty.map`：Nonempty.map {α β} (f : α -> β) : Nonempty α -> Nonempty β
 | ⟨h⟩ => ⟨f h⟩  protected theorem Nonempty.map2 {α β γ : Sort*} (f : α -> β -> 
γ)…
· 使用定理 `Nonempty.map2`：∀ {α : Sort u_3} {β : Sort u_4} {γ : Sort u_5} (f : α → β
 → γ), Nonempty α → Nonempty β → Nonempty γ

--- 原说明 ---
Two maps of topological pairs being homotopic defines an equivalence relation.
-/
theorem equivalence : Equivalence (Homotopic (X := X) (Y := Y)) :=
  ⟨fun f ↦ ⟨Homotopy.refl f⟩, fun h ↦ h.map Homotopy.symm, fun h₀ h₁ ↦ h₀.map2 Homotopy.trans h₁⟩

end Homotopic

end TopPair

