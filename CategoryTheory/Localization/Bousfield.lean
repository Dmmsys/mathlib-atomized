/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.Localization.Adjunction

/-!
# Bousfield localization

Given a predicate `P : ObjectProperty C` on the objects of a category `C`,
we define `W.isLocal : MorphismProperty C` as the class of morphisms `f : X ⟶ Y`
such that for any `Z : C` such that `P Z`, the precomposition with `f`
induces a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`.

(This construction is part of the left Bousfield localization
in the context of model categories.)

When `G ⊣ F` is an adjunction with `F : C ⥤ D` fully faithful, then
`G : D ⥤ C` is a localization functor for the class `isLocal (· ∈ Set.range F.obj)`,
which then identifies to the inverse image by `G` of the class of
isomorphisms in `C`.

The dual results are also obtained.

## References

* https://ncatlab.org/nlab/show/left+Bousfield+localization+of+model+categories

-/

@[expose] public section

namespace CategoryTheory

open Category

variable {C D : Type*} [Category* C] [Category* D]

namespace ObjectProperty

/-! ### Left Bousfield localization -/

section

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, this is the class of morphisms `f : X ⟶ Y`
such that for all `Z : C` such that `P Z`, the precomposition with `f` induces
a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the left Bousfield localization of model categories.) -/
/-
**CategoryTheory.ObjectProperty.isLocal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheor
y.ObjectProperty`。
形式化陈述：isLocal : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, this is the class of morphisms `f : X ⟶ Y`
such that for all `Z : C` such that `P Z`, the precomposition with `f` induces
a bijection `(Y ⟶ Z) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the left Bousfield localization of model categories.)
-/
def isLocal : MorphismProperty C := fun _ _ f =>
  ∀ Z, P Z → Function.Bijective (fun (g : _ ⟶ Z) => f ≫ g)

variable {P} in
/-- The bijection `(Y ⟶ Z) ≃ (X ⟶ Z)` induced by `f : X ⟶ Y` when `P.isLocal f`
and `P Z`. -/
@[simps! apply]
/-
**CategoryTheory.ObjectProperty.isLocal.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cate
goryTheory.ObjectProperty.isLocal`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {P 
: CategoryTheory.ObjectProperty C} → {X Y : C} → {f : X ⟶ Y} → P.isLocal f → (Z 
: C) → P Z → (Y ⟶ Z) ≃ (X ⟶ Z)
参数：Z : C；Y ⟶ Z；X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(Y ⟶ Z) ≃ (X ⟶ Z)` induced by `f : X ⟶ Y` when `P.isLocal f`
and `P Z`.
-/
noncomputable def isLocal.homEquiv {X Y : C} {f : X ⟶ Y} (hf : P.isLocal f) (Z : C) (hZ : P Z) :
    (Y ⟶ Z) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hf Z hZ)
/-
**CategoryTheory.ObjectProperty.isoClosure_isLocal** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：isoClosure_isLocal : P.isoClosure.isLocal = P.isLocal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma isoClosure_isLocal : P.isoClosure.isLocal = P.isLocal := by
  ext X Y f
  constructor
  · intro hf Z hZ
    exact hf _ (P.le_isoClosure _ hZ)
  · rintro hf Z ⟨Z', hZ', ⟨e⟩⟩
    constructor
    · intro g₁ g₂ eq
      rw [← cancel_mono e.hom]
      apply (hf _ hZ').1
      simp only [reassoc_of% eq]
    · intro g
      obtain ⟨a, h⟩ := (hf _ hZ').2 (g ≫ e.hom)
      exact ⟨a ≫ e.inv, by simp only [reassoc_of% h, e.hom_inv_id, comp_id]⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isLocal.IsMultiplicative where
  id_mem X Z _ := by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg Z hZ := by
    simpa using! Function.Bijective.comp (hf Z hZ) (hg Z hZ)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isLocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff _ (hg Z hZ)]
    simpa using! hfg Z hZ
  of_precomp f g hf hfg Z hZ := by
    rw [← Function.Bijective.of_comp_iff' (hf Z hZ)]
    simpa using! hfg Z hZ
/-
**CategoryTheory.ObjectProperty.isLocal_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：isLocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isLocal f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f] {Z : 
C}   (h : X ⟶ Z), CategoryT…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isLocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isLocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_epi f]
  · intro g
    exact ⟨inv f ≫ g, by simp⟩
/-
**CategoryTheory.ObjectProperty.isLocal_iff_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：isLocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.isLocal 
f ↔ IsIso f
参数：f : X ⟶ Y；hX : P X；hY : P Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Mathlib.Tactic.Reassoc.eq_whisker'`：eq_whisker' {C : Type*} [Category* C
] {X Y : C} {f g : X ⟶ Y} (w : f = g) {Z : C} (h : Y ⟶ Z) : f ≫ h = g ≫ h
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_of_isIso`：isLocal_of_isIso {X Y : 
C} (f : X ⟶ Y) [IsIso f] : P.isLocal f
-/
lemma isLocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isLocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hX).2 (𝟙 X)
    exact ⟨g, hg, (hf _ hY).1 (by simp only [reassoc_of% hg, comp_id])⟩
  · apply isLocal_of_isIso
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isLocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isLocal.comp_mem f g (isLocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isLocal.comp_mem g f hg (isLocal_of_isIso _ f)
/-
**CategoryTheory.ObjectProperty.le_isLocal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：le_isLocal_iff (P : ObjectProperty C) (W : MorphismProperty C) : W <= P.is
Local ↔ P <= W.isLocal
参数：P : ObjectProperty C；W : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_isLocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W ≤ P.isLocal ↔ P ≤ W.isLocal :=
  ⟨fun h _ hZ _ _ _ hf ↦ h _ hf _ hZ,
    fun h _ _ _ hf _ hZ ↦ h _ hZ _ hf⟩
/-
**CategoryTheory.ObjectProperty.galoisConnection_isLocal** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：galoisConnection_isLocal : GaloisConnection (OrderDual.toDual ∘ isLocal (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.le_isLocal_iff`：le_isLocal_iff (P : Object
Property C) (W : MorphismProperty C) : W <= P.isLocal ↔ P <= W.isLocal
-/
lemma galoisConnection_isLocal :
    GaloisConnection (OrderDual.toDual ∘ isLocal (C := C))
      (MorphismProperty.isLocal ∘ OrderDual.ofDual) :=
  le_isLocal_iff

end

/-! ### Right Bousfield localization -/

section

variable (P : ObjectProperty C)

/-- Given `P : ObjectProperty C`, this is the class of morphisms `g : Y ⟶ Z`
such that for all `X : C` such that `P X`, the postcomposition with `g` induces
a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the right Bousfield localization of model categories.) -/
/-
**CategoryTheory.ObjectProperty.isColocal** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.ObjectProperty`。
形式化陈述：isColocal : MorphismProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `P : ObjectProperty C`, this is the class of morphisms `g : Y ⟶ Z`
such that for all `X : C` such that `P X`, the postcomposition with `g` induces
a bijection `(X ⟶ Y) ≃ (X ⟶ Z)`. (One of the applications of this notion
is the right Bousfield localization of model categories.)
-/
def isColocal : MorphismProperty C := fun _ _ g =>
  ∀ X, P X → Function.Bijective (fun (f : X ⟶ _) => f ≫ g)

variable {P} in
/-- The bijection `(X ⟶ Y) ≃ (X ⟶ Z)` induced by `g : Y ⟶ Z` when `P.isColocal g`
and `P X`. -/
@[simps! apply]
/-
**CategoryTheory.ObjectProperty.isColocal.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.ObjectProperty.isColocal`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {P 
: CategoryTheory.ObjectProperty C} → {Y Z : C} → {g : Y ⟶ Z} → P.isColocal g → (
X : C) → P X → (X ⟶ Y) ≃ (X ⟶ Z)
参数：X : C；X ⟶ Y；X ⟶ Z。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `(X ⟶ Y) ≃ (X ⟶ Z)` induced by `g : Y ⟶ Z` when `P.isColocal g`
and `P X`.
-/
noncomputable def isColocal.homEquiv {Y Z : C} {g : Y ⟶ Z} (hg : P.isColocal g) (X : C) (hX : P X) :
    (X ⟶ Y) ≃ (X ⟶ Z) :=
  Equiv.ofBijective _ (hg X hX)
/-
**CategoryTheory.ObjectProperty.isoClosure_isColocal** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isoClosure_isColocal : P.isoClosure.isColocal = P.isColocal
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用引理 `CategoryTheory.ObjectProperty.le_isoClosure`：le_isoClosure : P <= isoClo
sure P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.StrongEpi.epi`：∀ {C : Type u} {inst : CategoryTheory.Cate
gory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongEpi f],   Cate
goryTheory.Epi f
· 使用定理 `CategoryTheory.strongEpi_of_isIso`：∀ {C : Type u} [inst : CategoryTheory
.Category.{v, u} C] {P Q : C} (f : P ⟶ Q) [CategoryTheory.IsIso f],   CategoryTh
eory.StrongEpi f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma isoClosure_isColocal : P.isoClosure.isColocal = P.isColocal := by
  ext Y Z g
  constructor
  · intro hg X hX
    exact hg _ (P.le_isoClosure _ hX)
  · rintro hg X ⟨X', hX', ⟨e⟩⟩
    constructor
    · intro f₁ f₂ eq
      rw [← cancel_epi e.inv]
      apply (hg _ hX').1
      simp [eq]
    · intro f
      obtain ⟨a, h⟩ := (hg _ hX').2 (e.inv ≫ f)
      exact ⟨e.hom ≫ a, by simp [h]⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isColocal.IsMultiplicative where
  id_mem _ _ _ := by simpa [id_comp] using! Function.bijective_id
  comp_mem f g hf hg X hX := by
    convert! Function.Bijective.comp (hg X hX) (hf X hX)
    cat_disch
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isColocal.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg X hX := by
    rw [← Function.Bijective.of_comp_iff' (hg X hX)]
    convert! hfg X hX
    cat_disch
  of_precomp f g hf hfg X hX := by
    rw [← Function.Bijective.of_comp_iff _ (hf X hX)]
    convert! hfg X hX
    cat_disch
/-
**CategoryTheory.ObjectProperty.isColocal_of_isIso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：isColocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isColocal f
参数：f : X ⟶ Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.IsIso.inv_hom_id`：inv_hom_id (f : X ⟶ Y) [I : IsIso f] : 
inv f ≫ f = 𝟙 Y
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isColocal_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isColocal f := fun Z _ => by
  constructor
  · intro g₁ g₂ _
    simpa only [← cancel_mono f]
  · intro g
    exact ⟨g ≫ inv f, by simp⟩
/-
**CategoryTheory.ObjectProperty.isColocal_iff_isIso** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.ObjectProperty`。
形式化陈述：isColocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.isColo
cal f ↔ IsIso f
参数：f : X ⟶ Y；hX : P X；hY : P Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_of_isIso`：isColocal_of_isIso {X 
Y : C} (f : X ⟶ Y) [IsIso f] : P.isColocal f
-/
lemma isColocal_iff_isIso {X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) :
    P.isColocal f ↔ IsIso f := by
  constructor
  · intro hf
    obtain ⟨g, hg⟩ := (hf _ hY).2 (𝟙 Y)
    exact ⟨g, (hf _ hX).1 (by cat_disch), hg⟩
  · apply isColocal_of_isIso
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.isColocal.RespectsIso where
  precomp f (_ : IsIso f) g hg := P.isColocal.comp_mem f g (isColocal_of_isIso _ f) hg
  postcomp f (_ : IsIso f) g hg := P.isColocal.comp_mem g f hg (isColocal_of_isIso _ f)
/-
**CategoryTheory.ObjectProperty.le_isColocal_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.ObjectProperty`。
形式化陈述：le_isColocal_iff (P : ObjectProperty C) (W : MorphismProperty C) : W <= P.
isColocal ↔ P <= W.isColocal
参数：P : ObjectProperty C；W : MorphismProperty C。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_isColocal_iff (P : ObjectProperty C) (W : MorphismProperty C) :
    W ≤ P.isColocal ↔ P ≤ W.isColocal :=
  ⟨fun h _ hZ _ _ _ hf ↦ h _ hf _ hZ,
    fun h _ _ _ hf _ hZ ↦ h _ hZ _ hf⟩
/-
**CategoryTheory.ObjectProperty.galoisConnection_isColocal** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：galoisConnection_isColocal : GaloisConnection (OrderDual.toDual ∘ isColoca
l (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.le_isColocal_iff`：le_isColocal_iff (P : Ob
jectProperty C) (W : MorphismProperty C) : W <= P.isColocal ↔ P <= W.isColocal
-/
lemma galoisConnection_isColocal :
    GaloisConnection (OrderDual.toDual ∘ isColocal (C := C))
      (MorphismProperty.isColocal ∘ OrderDual.ofDual) :=
  le_isColocal_iff

end

/-! ### Bousfield localization and adjunctions -/

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [F.Full] [F.Faithful]
include adj

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ObjectProperty.isLocal_adj_unit_app** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：isLocal_adj_unit_app (X : D) : isLocal (· in Set.range F.obj) (adj.unit.ap
p X)
参数：X : D。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.FullyFaithful.homEquiv_symm_apply`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma isLocal_adj_unit_app (X : D) : isLocal (· ∈ Set.range F.obj) (adj.unit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv.symm.trans
        (adj.homEquiv X Y)).bijective using 1
  dsimp [Adjunction.homEquiv]
  aesop
/-
**CategoryTheory.ObjectProperty.isLocal_iff_isIso_map** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：isLocal_iff_isIso_map {X Y : D} (f : X ⟶ Y) : isLocal (· in Set.range F.ob
j) f ↔ IsIso (G.map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.postcomp_iff`：postcomp_iff [W.RespectsRi
ght W'] [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W
' g) : W (f ≫ g) ↔ W f
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.ObjectProperty.instHasTwoOutOfThreePropertyIsLocal`：∀ {C 
: Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.Ob
jectProperty C),   P.isLocal.HasTwoOutOfThreeProperty
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPostcomp
Property`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Category
Theory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_adj_unit_app`：isLocal_adj_unit_app
 (X : D) : isLocal (· in Set.range F.obj) (adj.unit.app X)
· 使用引理 `CategoryTheory.MorphismProperty.precomp_iff`：precomp_iff [W.RespectsLeft
 W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
 : W (f ≫ g) ↔ W g
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_iff_isIso`：isLocal_iff_isIso {X Y 
: C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.isLocal f ↔ IsIso f
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f
-/
lemma isLocal_iff_isIso_map {X Y : D} (f : X ⟶ Y) :
    isLocal (· ∈ Set.range F.obj) f ↔ IsIso (G.map f) := by
  have := adj.unit.naturality f
  dsimp at this
  rw [← (isLocal (· ∈ Set.range F.obj)).postcomp_iff _ _ (isLocal_adj_unit_app adj Y),
    this, (isLocal (· ∈ Set.range F.obj)).precomp_iff _ _ (isLocal_adj_unit_app adj X),
    isLocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  exact ⟨fun _ ↦ isIso_of_fully_faithful F (G.map f), fun _ ↦ inferInstance⟩
/-
**CategoryTheory.ObjectProperty.isLocal_eq_inverseImage_isomorphisms** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isLocal_eq_inverseImage_isomorphisms : isLocal (· in Set.range F.obj) = (M
orphismProperty.isomorphisms _).inverseImage G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_iff_isIso_map`：isLocal_iff_isIso_m
ap {X Y : D} (f : X ⟶ Y) : isLocal (· in Set.range F.obj) f ↔ IsIso (G.map f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLocal_eq_inverseImage_isomorphisms :
    isLocal (· ∈ Set.range F.obj) = (MorphismProperty.isomorphisms _).inverseImage G := by
  ext P₁ P₂ f
  rw [isLocal_iff_isIso_map adj]
  rfl
/-
**CategoryTheory.ObjectProperty.isLocalization_isLocal** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：isLocalization_isLocal : G.IsLocalization (isLocal (· in Set.range F.obj))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isLocal_eq_inverseImage_isomorphisms`：isLo
cal_eq_inverseImage_isomorphisms : isLocal (· in Set.range F.obj) = (MorphismPro
perty.isomorphisms _).inverseImage G
· 使用引理 `CategoryTheory.Adjunction.isLocalization`：isLocalization [F.Full] [F.Fai
thful] : G.IsLocalization ((MorphismProperty.isomorphisms C₂).inverseImage G)
-/
lemma isLocalization_isLocal : G.IsLocalization (isLocal (· ∈ Set.range F.obj)) := by
  rw [isLocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization

end

section

variable {F : C ⥤ D} {G : D ⥤ C} (adj : G ⊣ F) [G.Full] [G.Faithful]
include adj

set_option backward.isDefEq.respectTransparency.types false in
/-
**CategoryTheory.ObjectProperty.isColocal_adj_counit_app** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isColocal_adj_counit_app (X : C) : isColocal (· in Set.range G.obj) (adj.c
ounit.app X)
参数：X : C。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.FullyFaithful.homEquiv_symm_apply`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.FullyFaithful.map_preimage`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Ca
tegory.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
lemma isColocal_adj_counit_app (X : C) : isColocal (· ∈ Set.range G.obj) (adj.counit.app X) := by
  rintro _ ⟨Y, rfl⟩
  convert!
    ((Functor.FullyFaithful.ofFullyFaithful G).homEquiv.symm.trans
        (adj.homEquiv Y X).symm).bijective using 1
  dsimp [Adjunction.homEquiv]
  cat_disch
/-
**CategoryTheory.ObjectProperty.isColocal_iff_isIso_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：isColocal_iff_isIso_map {X Y : C} (f : X ⟶ Y) : isColocal (· in Set.range 
G.obj) f ↔ IsIso (F.map f)
参数：f : X ⟶ Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.MorphismProperty.precomp_iff`：precomp_iff [W.RespectsLeft
 W'] [W.HasOfPrecompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W' f)
 : W (f ≫ g) ↔ W g
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsLeft`：∀ {C : Type u} 
{inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPr
operty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toIsStableUnder
Composition`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Categ
oryTheory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Is…
· 使用定理 `CategoryTheory.ObjectProperty.instHasTwoOutOfThreePropertyIsColocal`：∀ {
C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.
ObjectProperty C),   P.isColocal.HasTwoOutOfThreeProperty
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPrecompP
roperty`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : CategoryT
heory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_adj_counit_app`：isColocal_adj_co
unit_app (X : C) : isColocal (· in Set.range G.obj) (adj.counit.app X)
· 使用引理 `CategoryTheory.MorphismProperty.postcomp_iff`：postcomp_iff [W.RespectsRi
ght W'] [W.HasOfPostcompProperty W'] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hg : W
' g) : W (f ≫ g) ↔ W f
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.HasTwoOutOfThreeProperty.toHasOfPostcomp
Property`：∀ {C : Type u} {inst : CategoryTheory.Category.{v, u} C} {W : Category
Theory.MorphismProperty C}   [self : W.HasTwoOutOfThreeProperty], W.Ha…
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_iff_isIso`：isColocal_iff_isIso {
X Y : C} (f : X ⟶ Y) (hX : P X) (hY : P Y) : P.isColocal f ↔ IsIso f
· 使用定理 `CategoryTheory.isIso_of_fully_faithful`：isIso_of_fully_faithful (f : X ⟶
 Y) [IsIso (F.map f)] : IsIso f
-/
lemma isColocal_iff_isIso_map {X Y : C} (f : X ⟶ Y) :
    isColocal (· ∈ Set.range G.obj) f ↔ IsIso (F.map f) := by
  have := adj.counit.naturality f
  dsimp at this
  rw [← (isColocal _).precomp_iff _ _ (isColocal_adj_counit_app adj X),
    ← this, (isColocal _).postcomp_iff _ _ (isColocal_adj_counit_app adj Y),
    isColocal_iff_isIso _ _ ⟨_, rfl⟩ ⟨_, rfl⟩]
  exact ⟨fun _ ↦ isIso_of_fully_faithful G (F.map f), fun _ ↦ inferInstance⟩
/-
**CategoryTheory.ObjectProperty.isColocal_eq_inverseImage_isomorphisms** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isColocal_eq_inverseImage_isomorphisms : isColocal (· in Set.range G.obj) 
= (MorphismProperty.isomorphisms _).inverseImage F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.ext`：ext (W W' : MorphismProperty C) (h 
: forall ⦃X Y : C⦄ (f : X ⟶ Y), W f ↔ W' f) : W = W'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_iff_isIso_map`：isColocal_iff_isI
so_map {X Y : C} (f : X ⟶ Y) : isColocal (· in Set.range G.obj) f ↔ IsIso (F.map
 f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isColocal_eq_inverseImage_isomorphisms :
    isColocal (· ∈ Set.range G.obj) = (MorphismProperty.isomorphisms _).inverseImage F := by
  ext P₁ P₂ f
  rw [isColocal_iff_isIso_map adj]
  rfl
/-
**CategoryTheory.ObjectProperty.isLocalization_isColocal** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isLocalization_isColocal : F.IsLocalization (isColocal (· in Set.range G.o
bj))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isColocal_eq_inverseImage_isomorphisms`：is
Colocal_eq_inverseImage_isomorphisms : isColocal (· in Set.range G.obj) = (Morph
ismProperty.isomorphisms _).inverseImage F
· 使用引理 `CategoryTheory.Adjunction.isLocalization'`：isLocalization' [G.Full] [G.F
aithful] : F.IsLocalization ((MorphismProperty.isomorphisms C₁).inverseImage F)
-/
lemma isLocalization_isColocal : F.IsLocalization (isColocal (· ∈ Set.range G.obj)) := by
  rw [isColocal_eq_inverseImage_isomorphisms adj]
  exact adj.isLocalization'

end

end ObjectProperty

open Localization

/-
**CategoryTheory.ObjectProperty.le_isLocal_isLocal** 是 Mathlib 中的一个定理，位于命名空间 `Ca
tegoryTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C),   P ≤ P.isLocal.isLocal
参数：P : CategoryTheory.ObjectProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.le_isLocal_iff`：le_isLocal_iff (P : Object
Property C) (W : MorphismProperty C) : W <= P.isLocal ↔ P <= W.isLocal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma ObjectProperty.le_isLocal_isLocal (P : ObjectProperty C) :
    P ≤ P.isLocal.isLocal := by
  rw [← le_isLocal_iff]
/-
**CategoryTheory.MorphismProperty.le_isLocal_isLocal** 是 Mathlib 中的一个定理，位于命名空间 `
CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Catego
ryTheory.MorphismProperty C),   W ≤ W.isLocal.isLocal
参数：W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.le_isLocal_iff`：le_isLocal_iff (P : Object
Property C) (W : MorphismProperty C) : W <= P.isLocal ↔ P <= W.isLocal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma MorphismProperty.le_isLocal_isLocal (W : MorphismProperty C) :
    W ≤ W.isLocal.isLocal := by
  rw [ObjectProperty.le_isLocal_iff]
/-
**CategoryTheory.ObjectProperty.le_isColocal_isColocal** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (P : Catego
ryTheory.ObjectProperty C),   P ≤ P.isColocal.isColocal
参数：P : CategoryTheory.ObjectProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.le_isColocal_iff`：le_isColocal_iff (P : Ob
jectProperty C) (W : MorphismProperty C) : W <= P.isColocal ↔ P <= W.isColocal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma ObjectProperty.le_isColocal_isColocal (P : ObjectProperty C) :
    P ≤ P.isColocal.isColocal := by
  rw [← le_isColocal_iff]
/-
**CategoryTheory.MorphismProperty.le_isColocal_isColocal** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.MorphismProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] (W : Catego
ryTheory.MorphismProperty C),   W ≤ W.isColocal.isColocal
参数：W : CategoryTheory.MorphismProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.le_isColocal_iff`：le_isColocal_iff (P : Ob
jectProperty C) (W : MorphismProperty C) : W <= P.isColocal ↔ P <= W.isColocal
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma MorphismProperty.le_isColocal_isColocal (W : MorphismProperty C) :
    W ≤ W.isColocal.isColocal := by
  rw [ObjectProperty.le_isColocal_iff]

end CategoryTheory

