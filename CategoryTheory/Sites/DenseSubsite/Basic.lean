/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Sites.LocallyFullyFaithful

/-!
# Dense subsites

We define `IsCoverDense` functors into sites as functors such that there exists a covering sieve
that factors through images of the functor for each object in `D`.

## Main results

- `CategoryTheory.Functor.IsCoverDense.Types.presheafHom`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any presheaf `ℱ` and sheaf `ℱ'` on `D`,
  and a morphism `α : G ⋙ ℱ ⟶ G ⋙ ℱ'`, we may glue them together to obtain
  a morphism of presheaves `ℱ ⟶ ℱ'`.
- `CategoryTheory.Functor.IsCoverDense.sheafIso`: If `ℱ` above is a sheaf and `α` is an iso,
  then the result is also an iso.
- `CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso`: If `G : C ⥤ (D, K)` is locally-full
  and cover-dense, then given any sheaves `ℱ, ℱ'` on `D`, and a morphism `α : ℱ ⟶ ℱ'`,
  then `α` is an iso if `G ⋙ ℱ ⟶ G ⋙ ℱ'` is iso.
- `CategoryTheory.Functor.IsDenseSubsite`:
  The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)` if `G` is cover-dense,
  locally fully-faithful, and `S` is a cover of `C` iff the image of `S` in `D` is a cover.
- `CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`: the equivalence of
  categories `Sheaf J A ≌ Sheaf K A` when `(C, J)` is a dense subsite of `(D, K)` and
  the pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, which we show
  in two situations:
  * the sites are small and `A` has suitable limits (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/SheafEquiv.lean`).
  * the category `A` has limits of size `w` and `G` is `1`-hypercover cover dense
    relatively to the universe `w` (see the file
    `Mathlib/CategoryTheory/Sites/DenseSubsite/OneHypercoverDense.lean`).

## References

* [Elephant]: *Sketches of an Elephant*, ℱ. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

universe w v u

namespace CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] {E : Type*} [Category* E]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/-- An auxiliary structure that witnesses the fact that `f` factors through an image object of `G`.
-/
/-
**CategoryTheory.Presieve.CoverByImageStructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `Cat
egoryTheory.Presieve`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → {V U : D} → (V ⟶ U) → Type (max u_1 v_2)
参数：V ⟶ U；max u_1 v_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary structure that witnesses the fact that `f` factors through an image
 object of `G`.
-/
structure Presieve.CoverByImageStructure (G : C ⥤ D) {V U : D} (f : V ⟶ U) where
  obj : C
  lift : V ⟶ G.obj obj
  map : G.obj obj ⟶ U
  fac : lift ≫ map = f := by cat_disch
attribute [nolint docBlame] Presieve.CoverByImageStructure.obj Presieve.CoverByImageStructure.lift
  Presieve.CoverByImageStructure.map Presieve.CoverByImageStructure.fac

attribute [reassoc (attr := simp)] Presieve.CoverByImageStructure.fac

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Presieve.coverByImage G U` is the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
/-
**CategoryTheory.Presieve.coverByImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory
.Presieve`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → (U : D) → CategoryTheory.Presieve U
参数：U : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `G : C ⥤ D`, and an object `U : D`, `Presieve.coverByImage G U` is
 the presieve
of `U` consisting of those arrows that factor through images of `G`.
-/
def Presieve.coverByImage (G : C ⥤ D) (U : D) : Presieve U := fun _ f =>
  Nonempty (Presieve.CoverByImageStructure G f)

/-- For a functor `G : C ⥤ D`, and an object `U : D`, `Sieve.coverByImage G U` is the sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
/-
**CategoryTheory.Sieve.coverByImage** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Si
eve`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] → CategoryTh
eory.Functor C D → (U : D) → CategoryTheory.Sieve U
参数：U : D。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a functor `G : C ⥤ D`, and an object `U : D`, `Sieve.coverByImage G U` is th
e sieve of `U`
consisting of those arrows that factor through images of `G`.
-/
def Sieve.coverByImage (G : C ⥤ D) (U : D) : Sieve U :=
  ⟨Presieve.coverByImage G U, fun ⟨⟨Z, f₁, f₂, (e : _ = _)⟩⟩ g =>
    ⟨⟨Z, g ≫ f₁, f₂, show (g ≫ f₁) ≫ f₂ = g ≫ _ by rw [Category.assoc, ← e]⟩⟩⟩
/-
**CategoryTheory.Presieve.in_coverByImage** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Presieve`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : CategoryTheory.Functo
r C D) {X : D} {Y : C} (f : G.obj Y ⟶ X),   CategoryTheory.Presieve.coverByImage
 G X f
参数：G : CategoryTheory.Functor C D；f : G.obj Y ⟶ X。
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
theorem Presieve.in_coverByImage (G : C ⥤ D) {X : D} {Y : C} (f : G.obj Y ⟶ X) :
    Presieve.coverByImage G X f :=
  ⟨⟨Y, 𝟙 _, f, by simp⟩⟩

/-- A functor `G : (C, J) ⥤ (D, K)` is cover dense if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Definition 2.2.
-/
/-
**CategoryTheory.Functor.IsCoverDense** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheor
y.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → CategoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A functor `G : (C, J) ⥤ (D, K)` is cover dense if for each object in `D`,
  there exists a covering sieve in `D` that factors through images of `G`.

This definition can be found in https://ncatlab.org/nlab/show/dense+sub-site Def
inition 2.2.
-/
class Functor.IsCoverDense (G : C ⥤ D) (K : GrothendieckTopology D) : Prop where
  is_cover : ∀ U : D, Sieve.coverByImage G U ∈ K U
/-
**CategoryTheory.Functor.is_cover_of_isCoverDense** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : CategoryTheory.Functo
r C D)   (K : CategoryTheory.GrothendieckTopology D) [G.IsCoverDense K] (U : D),
 CategoryTheory.Sieve.coverByImage G U ∈ K U
参数：G : CategoryTheory.Functor C D；K : CategoryTheory.GrothendieckTopology D；U : 
D。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCoverDense.is_cover`：∀ {C : Type u_1} {inst : C
ategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : CategoryTheory.C
ategory.{v_2, u_2} D} {G : Categor…
-/
lemma Functor.is_cover_of_isCoverDense (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsCoverDense K] (U : D) : Sieve.coverByImage G U ∈ K U := by
  apply Functor.IsCoverDense.is_cover
/-
**CategoryTheory.Functor.isCoverDense_of_generate_singleton_functor_** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Functor.isCoverDense_of_generate_singleton_functor_π_mem (G : C ⥤ D)
    (K : GrothendieckTopology D)
    (h : ∀ B, ∃ (X : C) (f : G.obj X ⟶ B), Sieve.generate (Presieve.singleton f) ∈ K B) :
    G.IsCoverDense K where
  is_cover B := by
    obtain ⟨X, f, h⟩ := h B
    refine K.superset_covering ?_ h
    intro Y f ⟨Z, g, _, h, w⟩
    cases h
    exact ⟨⟨_, g, _, w⟩⟩

attribute [nolint docBlame] CategoryTheory.Functor.IsCoverDense.is_cover

open Presieve Opposite

namespace Functor

namespace IsCoverDense

variable {K}
variable {A : Type*} [Category* A] (G : C ⥤ D)

-- this is not marked with `@[ext]` because `H` cannot be inferred from the type
/-
**CategoryTheory.Functor.IsCoverDense.ext** 是 Mathlib 中的一个定理，位于命名空间 `CategoryThe
ory.Functor.IsCoverDense`。
形式化陈述：ext [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)
} (h : forall ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.obj.map f.op s = ℱ.obj.map f.op t) : 
s = t
参数：ℱ : Sheaf K Type*；X : D；op X；h : forall ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.obj.map 
f.op s = ℱ.obj.map f.op t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSeparatedFor.ext`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X : C
}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ext [G.IsCoverDense K] (ℱ : Sheaf K Type*) (X : D) {s t : ℱ.obj.obj (op X)}
    (h : ∀ ⦃Y : C⦄ (f : G.obj Y ⟶ X), ℱ.obj.map f.op s = ℱ.obj.map f.op t) : s = t := by
  apply ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.property
    (Sieve.coverByImage G X) (G.is_cover_of_isCoverDense K X)).isSeparatedFor.ext
  rintro Y _ ⟨Z, f₁, f₂, ⟨rfl⟩⟩
  simp [h f₂]

variable {G}
/-
**CategoryTheory.Functor.IsCoverDense.functorPullback_pushforward_covering** 是 M
athlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K
] {X : C} (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G in 
K (G.obj X)
参数：T : K (G.obj X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.functorPullback_apply`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.
{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.functorPushforward_imageSieve_mem`：functorPushfor
ward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) : (G.image
Sieve f).functorPushforward G in K _
-/
theorem functorPullback_pushforward_covering [G.IsCoverDense K] [G.IsLocallyFull K] {X : C}
    (T : K (G.obj X)) : (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X) := by
  refine K.transitive T.2 _ fun Y iYX hiYX ↦ ?_
  apply K.transitive (G.is_cover_of_isCoverDense _ _) _
  rintro W _ ⟨Z, iWZ, iZY, rfl⟩
  rw [Sieve.pullback_comp]; apply K.pullback_stable; clear W iWZ
  apply K.superset_covering ?_ (G.functorPushforward_imageSieve_mem _ (iZY ≫ iYX))
  rintro W _ ⟨V, iVZ, iWV, ⟨iVX, e⟩, rfl⟩
  exact ⟨_, iVX, iWV, by simpa [e] using T.1.downward_closed hiYX (G.map iVZ ≫ iZY), by simp [e]⟩

/-- (Implementation). Given a hom between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain a hom between the pullbacks of the sheaves of maps from `X`.
-/
@[simps! app]
/-
**CategoryTheory.Functor.IsCoverDense.homOver** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.IsCoverDense`。
形式化陈述：homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) (X :
 A) : G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).obj
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj；X : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). Given a hom between the pullbacks of two sheaves, we can whisk
er it with
`coyoneda` to obtain a hom between the pullbacks of the sheaves of maps from `X`
.
-/
def homOver {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) (X : A) :
    G.op ⋙ ℱ ⋙ coyoneda.obj (op X) ⟶ G.op ⋙ (sheafOver ℱ' X).obj :=
  whiskerRight α (coyoneda.obj (op X))

/-- (Implementation). Given an iso between the pullbacks of two sheaves, we can whisker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X`.
-/
@[simps! +dsimpLhs]
/-
**CategoryTheory.Functor.IsCoverDense.isoOver** 是 Mathlib 中的一个定义，位于命名空间 `Categor
yTheory.Functor.IsCoverDense`。
形式化陈述：isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : A) : G.
op ⋙ (sheafOver ℱ X).obj ≅ G.op ⋙ (sheafOver ℱ' X).obj
参数：α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj；X : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). Given an iso between the pullbacks of two sheaves, we can whis
ker it with
`coyoneda` to obtain an iso between the pullbacks of the sheaves of maps from `X
`.
-/
def isoOver {ℱ ℱ' : Sheaf K A} (α : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : A) :
    G.op ⋙ (sheafOver ℱ X).obj ≅ G.op ⋙ (sheafOver ℱ' X).obj :=
  isoWhiskerRight α (coyoneda.obj (op X))
/-
**CategoryTheory.Functor.IsCoverDense.sheaf_eq_amalgamation** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT) (
x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) : t = (ℱ.property X 
T hT).amalgamate x hx
参数：ℱ : Sheaf K A；hT；x : FamilyOfElements _ T；hx；t；h : x.IsAmalgamation t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isSeparatedFor`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.isAmalgamation`：∀ {C : Type u₁} [inst
 : CategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)}
 {X : C}   {R : CategoryTheory.Presieve…
-/
theorem sheaf_eq_amalgamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT)
    (x : FamilyOfElements _ T) (hx) (t) (h : x.IsAmalgamation t) :
    t = (ℱ.property X T hT).amalgamate x hx :=
  (ℱ.property X T hT).isSeparatedFor x t _ h ((ℱ.property X T hT).isAmalgamation hx)

namespace Types

variable {ℱ : Dᵒᵖ ⥤ Type v} {ℱ' : Sheaf K (Type v)} (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj)

/-
**CategoryTheory.Functor.IsCoverDense.Types.naturality_apply** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：naturality_apply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x)
 : ℱ'.1.map i.op (α.app _ x) = α.app _ (ℱ.map i.op x)
参数：i : G.obj X ⟶ G.obj Y；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.ext`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Category.{v
D, uD} D]   {K : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality_apply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) :
    ℱ'.1.map i.op (α.app _ x) = α.app _ (ℱ.map i.op x) := by
  have {X Y} (i : X ⟶ Y) (x) :
      ℱ'.1.map (G.map i).op (α.app _ x) = α.app _ (ℱ.map (G.map i).op x) := by
    exact ConcreteCategory.congr_hom (α.naturality i.op).symm x
  refine IsLocallyFull.ext G _ i fun V iVX iVY e ↦ ?_
  simp only [← Functor.map_comp_apply, ← op_comp, ← e, this]

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.IsCoverDense.Types.naturality** 是 Mathlib 中的一个定理，位于命名空间
 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：naturality [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) : α.app _
 ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _
参数：i : G.obj X ⟶ G.obj Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.naturality_apply`：naturality_a
pply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) : ℱ'.1.map i.op (
α.app _ x) = α.app _ (ℱ.map i.op x)

--- 原说明 ---
`respectTransparency.types true` changes the auto-generated lemmas' signature
-/
theorem naturality [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) :
    α.app _ ≫ ℱ'.1.map i.op = ℱ.map i.op ≫ α.app _ := by ext; exact naturality_apply α i _

/--
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of elements valued in `ℱ'`
that is defined on a cover generated by the images of `G`. -/
/-
**CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：pushforwardFamily {X} (x : ℱ.obj (op X)) : FamilyOfElements ℱ'.obj (coverB
yImage G X)
参数：x : ℱ.obj (op X)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). Given a section of `ℱ` on `X`, we can obtain a family of eleme
nts valued in `ℱ'`
that is defined on a cover generated by the images of `G`.
-/
noncomputable def pushforwardFamily {X} (x : ℱ.obj (op X)) :
    FamilyOfElements ℱ'.obj (coverByImage G X) := fun _ _ hf =>
  ℱ'.obj.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x)
/-
**CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_def** 是 Mathlib 中的
一个定理，位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u
_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] {K : CategoryTheory.Grothe
ndieckTopology D}   {G : CategoryTheory.Functor C D} {ℱ : CategoryTheory.Functor
 Dᵒᵖ (Type v)} {ℱ' : CategoryTheory.Sheaf K (Type v)}   (α : G.op.comp ℱ ⟶ G.op.
comp ℱ'.obj) {X : D} (x : ℱ.obj (Opposite.op X)),   CategoryTheory.Functor.IsCov
erDense.Types.pushforwardFamily α x = fun x_1 x_2 hf =>     (CategoryTheory.Conc
reteCategory.hom (ℱ'.obj.map (Nonempty.some hf).lift.op))       ((CategoryTheory
.ConcreteCategory.hom (α.app (Opposite.op (Nonempty.some hf).1)))         ((Cate
goryTheory.ConcreteCategory.hom (ℱ.map (Nonempty.some hf).map.op)) x))
参数：Type v；Type v；α : G.op.comp ℱ ⟶ G.op.comp ℱ'.obj；x : ℱ.obj (Opposite.op X)；Ca
tegoryTheory.ConcreteCategory.hom (ℱ'.obj.map (Nonempty.some hf).lift.op)；(Categ
oryTheory.ConcreteCategory.hom (α.app (Opposite.op (Nonempty.some hf).1)))      
   ((CategoryTheory.ConcreteCategory.hom (ℱ.map (Nonempty.some hf).map.op)) x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem pushforwardFamily_def {X} (x : ℱ.obj (op X)) :
    pushforwardFamily α x = fun _ _ hf =>
    ℱ'.obj.map hf.some.lift.op <| α.app (op _) (ℱ.map hf.some.map.op x) := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_apply** 是 Mathlib 
中的一个定理，位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：pushforwardFamily_apply [G.IsLocallyFull K] {X} (x : ℱ.obj (op X)) {Y : C}
 (f : G.obj Y ⟶ X) : pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.
app (op Y) (ℱ.map f.op x)
参数：x : ℱ.obj (op X)；f : G.obj Y ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.in_coverByImage`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] (G : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.naturality_apply`：naturality_a
pply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) : ℱ'.1.map i.op (
α.app _ x) = α.app _ (ℱ.map i.op x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pushforwardFamily_apply [G.IsLocallyFull K]
    {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj Y ⟶ X) :
    pushforwardFamily α x f (Presieve.in_coverByImage G f) = α.app (op Y) (ℱ.map f.op x) := by
  simp only [pushforwardFamily_def, op_obj]
  generalize Nonempty.some (Presieve.in_coverByImage G f) = l
  obtain ⟨W, iYW, iWX, rfl⟩ := l
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply]

variable [G.IsCoverDense K] [G.IsLocallyFull K]

/-- (Implementation). The `pushforwardFamily` defined is compatible. -/
/-
**CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_compatible** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α
 x).Compatible
参数：x : ℱ.obj (op X)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCoverDense.ext`：ext [G.IsCoverDense K] (ℱ : She
af K Type*) (X : D) {s t : ℱ.obj.obj (op X)} (h : forall ⦃Y : C⦄ (f : G.obj Y ⟶ 
X), ℱ.obj.map f.op s = ℱ.obj.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.naturality_apply`：naturality_a
pply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) : ℱ'.1.map i.op (
α.app _ x) = α.app _ (ℱ.map i.op x)
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
(Implementation). The `pushforwardFamily` defined is compatible.
-/
theorem pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) :
    (pushforwardFamily α x).Compatible := by
  suffices ∀ {Z W₁ W₂} (iWX₁ : G.obj W₁ ⟶ X) (iWX₂ : G.obj W₂ ⟶ X) (iZW₁ : Z ⟶ G.obj W₁)
      (iZW₂ : Z ⟶ G.obj W₂), iZW₁ ≫ iWX₁ = iZW₂ ≫ iWX₂ →
      ℱ'.1.map iZW₁.op (α.app _ (ℱ.map iWX₁.op x)) = ℱ'.1.map iZW₂.op (α.app _ (ℱ.map iWX₂.op x)) by
    rintro Y₁ Y₂ Z iZY₁ iZY₂ f₁ f₂ h₁ h₂ e
    simp only [pushforwardFamily, ← Functor.map_comp_apply, ← op_comp]
    generalize Nonempty.some h₁ = l₁
    generalize Nonempty.some h₂ = l₂
    obtain ⟨W₁, iYW₁, iWX₁, rfl⟩ := l₁
    obtain ⟨W₂, iYW₂, iWX₂, rfl⟩ := l₂
    exact this _ _ _ _ (by simpa only [Category.assoc] using e)
  introv e
  refine ext G _ _ fun V iVZ ↦ ?_
  simp only [← op_comp, ← Functor.map_comp_apply, naturality_apply,
    Category.assoc, e]

/-- (Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFamily`. -/
/-
**CategoryTheory.Functor.IsCoverDense.Types.appHom** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.obj.obj (op X)
参数：X : D。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_compatible`：
pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α x).Co
mpatible

--- 原说明 ---
(Implementation). The morphism `ℱ(X) ⟶ ℱ'(X)` given by gluing the `pushforwardFa
mily`.
-/
noncomputable def appHom (X : D) : ℱ.obj (op X) ⟶ ℱ'.obj.obj (op X) := ↾fun x =>
  ((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _
    (G.is_cover_of_isCoverDense _ X)).amalgamate (pushforwardFamily α x)
      (pushforwardFamily_compatible α x)

@[simp]
/-
**CategoryTheory.Functor.IsCoverDense.Types.appHom_restrict** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) : ℱ'.obj.map
 f (appHom α X x) = α.app (op Y) (ℱ.map f x)
参数：f : op X ⟶ op (G.obj Y)；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.isSheaf_iff_isSheaf_of_type`：isSheaf_iff_isSheaf_of_type 
(P : Cᵒᵖ ⥤ Type w) : Presheaf.IsSheaf J P ↔ Presieve.IsSheaf J P
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_compatible`：
pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α x).Co
mpatible
· 使用定理 `CategoryTheory.Presieve.in_coverByImage`：∀ {C : Type u_1} [inst : Catego
ryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Catego
ry.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Presieve.IsSheafFor.valid_glue`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {P : CategoryTheory.Functor Cᵒᵖ (Type w)} {X 
Y : C}   {R : CategoryTheory.Presie…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_apply`：pushf
orwardFamily_apply [G.IsLocallyFull K] {X} (x : ℱ.obj (op X)) {Y : C} (f : G.obj
 Y ⟶ X) : pushforwardFamily α x f (Presieve.in_coverByI…
-/
theorem appHom_restrict {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) :
    ℱ'.obj.map f (appHom α X x) = α.app (op Y) (ℱ.map f x) :=
  (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ'.property _ (G.is_cover_of_isCoverDense _ X)).valid_glue
      (pushforwardFamily_compatible α x) f.unop
          (Presieve.in_coverByImage G f.unop)).trans (pushforwardFamily_apply _ _ _)

@[simp]
/-
**CategoryTheory.Functor.IsCoverDense.Types.appHom_valid_glue** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) : appHom α X ≫
 ℱ'.obj.map f = ℱ.map f ≫ α.app (op Y)
参数：f : op X ⟶ op (G.obj Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.appHom_restrict`：appHom_restri
ct {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) (x) : ℱ'.obj.map f (appHom α X x) =
 α.app (op Y) (ℱ.map f x)
-/
theorem appHom_valid_glue {X : D} {Y : C} (f : op X ⟶ op (G.obj Y)) :
    appHom α X ≫ ℱ'.obj.map f = ℱ.map f ≫ α.app (op Y) := by
  ext
  apply appHom_restrict

unif_hint {J J' C : Type*} [Category* J] [Category* J'] [Category* C]
    (G G' : J' ⥤ J) (F F' : Jᵒᵖ ⥤ C) (j j' : J') where
  G ≟ G'
  F ≟ F'
  j ≟ j' ⊢ (G.op ⋙ F).obj (op j) ≟ F'.obj (op (G'.obj j')) in
/--
(Implementation). The maps given in `appIso` is inverse to each other and gives a `ℱ(X) ≅ ℱ'(X)`.
-/
@[simps]
/-
**CategoryTheory.Functor.IsCoverDense.Types.appIso** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：appIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) (X : D
) : ℱ.obj.obj (op X) ≅ ℱ'.obj.obj (op X) where hom
参数：Type v；i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj；X : D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). The maps given in `appIso` is inverse to each other and gives 
a `ℱ(X) ≅ ℱ'(X)`.
-/
noncomputable def appIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj)
    (X : D) : ℱ.obj.obj (op X) ≅ ℱ'.obj.obj (op X) where
  hom := appHom i.hom X
  inv := appHom i.inv X
  hom_inv_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp
  inv_hom_id := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y f
    simp

/--
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf,
we may obtain a natural transformation between sheaves.
-/
@[simps]
/-
**CategoryTheory.Functor.IsCoverDense.Types.presheafHom** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj where app X
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf,
we may obtain a natural transformation between sheaves.
-/
noncomputable def presheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj where
  app X := appHom α (unop X)
  naturality X Y f := by
    ext x
    apply Functor.IsCoverDense.ext G
    intro Y' f'
    simp only [TypeCat.Fun.toFun_apply, types_comp_apply, ← map_comp_apply]
    rw [appHom_restrict, appHom_restrict]
    simp

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
/-
**CategoryTheory.Functor.IsCoverDense.Types.presheafIso** 是 Mathlib 中的一个定义，位于命名空
间 `CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：presheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
 ℱ.obj ≅ ℱ'.obj
参数：Type v；i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
noncomputable def presheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ.obj ≅ ℱ'.obj :=
  NatIso.ofComponents (fun X => appIso i (unop X)) @(presheafHom i.hom).naturality

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between sheaves.
-/
@[simps! hom_hom inv_hom]
/-
**CategoryTheory.Functor.IsCoverDense.Types.sheafIso** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.IsCoverDense.Types`。
形式化陈述：sheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) : ℱ 
≅ ℱ'
参数：Type v；i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of types,
where `G` is locally-full and cover-dense, and `ℱ, ℱ'` are sheaves,
we may obtain a natural isomorphism between sheaves.
-/
noncomputable def sheafIso {ℱ ℱ' : Sheaf K (Type v)} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

end Types

open IsCoverDense.Types

variable [G.IsCoverDense K] [G.IsLocallyFull K] {ℱ : Dᵒᵖ ⥤ A} {ℱ' : Sheaf K A}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms of `X`. -/
@[simps]
/-
**CategoryTheory.Functor.IsCoverDense.sheafCoyonedaHom** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : coyoneda ⋙ (whiskeringLe
ft Dᵒᵖ A (Type _)).obj ℱ ⟶ coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.obj
 where app X
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). The sheaf map given in `types.sheaf_hom` is natural in terms o
f `X`.
-/
noncomputable def sheafCoyonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ ⟶
      coyoneda ⋙ (whiskeringLeft Dᵒᵖ A (Type _)).obj ℱ'.obj where
  app X := presheafHom (homOver α (unop X))
  naturality X Y f := by
    ext U x
    change
      appHom (homOver α (unop Y)) (unop U) (f.unop ≫ x) =
        f.unop ≫ appHom (homOver α (unop X)) (unop U) x
    symm
    apply sheaf_eq_amalgamation
    · apply G.is_cover_of_isCoverDense
    -- Porting note: the following line closes a goal which didn't exist before reenableeta
    · exact pushforwardFamily_compatible (homOver α Y.unop) (f.unop ≫ x)
    intro Y' f' hf'
    dsimp
    simp only [Category.assoc]
    congr 1
    conv_lhs => rw [← hf'.some.fac]
    simp only [← Category.assoc, op_comp, Functor.map_comp]
    congr 1
    exact (appHom_restrict (homOver α (unop X)) hf'.some.map.op x).trans (by simp)

/--
(Implementation). `sheafCoyonedaHom` but the order of the arguments of the functor are swapped.
-/
/-
**CategoryTheory.Functor.IsCoverDense.sheafYonedaHom** 是 Mathlib 中的一个定义，位于命名空间 `
CategoryTheory.Functor.IsCoverDense`。
形式化陈述：sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⋙ yoneda ⟶ ℱ'.obj ⋙ yone
da where app U
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation). `sheafCoyonedaHom` but the order of the arguments of the funct
or are swapped.
-/
noncomputable def sheafYonedaHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    ℱ ⋙ yoneda ⟶ ℱ'.obj ⋙ yoneda where
  app U :=
    let α := (sheafCoyonedaHom α)
    { app := fun X => (α.app X).app U
      naturality := fun X Y f => by simpa using! congr_app (α.naturality f) U }
  naturality U V i := by
    ext X x
    exact ConcreteCategory.congr_hom (((sheafCoyonedaHom α).app X).naturality i) x

/--
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf, we may obtain a natural
transformation between presheaves.
-/
/-
**CategoryTheory.Functor.IsCoverDense.sheafHom** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.IsCoverDense`。
形式化陈述：sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural transformation `G ⋙ ℱ ⟶ G ⋙ ℱ'` between presheaves of arbitrary 
category,
where `G` is locally-full and cover-dense, and `ℱ'` is a sheaf, we may obtain a 
natural
transformation between presheaves.
-/
noncomputable def sheafHom (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : ℱ ⟶ ℱ'.obj :=
  let α' := sheafYonedaHom α
  { app := fun X => yoneda.preimage (α'.app X)
    naturality := fun X Y f => yoneda.map_injective (by simpa using! α'.naturality f) }

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps!]
/-
**CategoryTheory.Functor.IsCoverDense.presheafIso** 是 Mathlib 中的一个定义，位于命名空间 `Cat
egoryTheory.Functor.IsCoverDense`。
形式化陈述：presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) : ℱ.obj 
≅ ℱ'.obj
参数：i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary cat
egory,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
noncomputable def presheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) :
    ℱ.obj ≅ ℱ'.obj := by
  have : ∀ X : Dᵒᵖ, IsIso ((sheafHom i.hom).app X) := by
    intro X
    rw [← isIso_iff_of_reflects_iso _ yoneda]
    use (sheafYonedaHom i.inv).app X
    constructor <;> ext x : 2 <;>
      simp only [sheafHom, NatTrans.comp_app, NatTrans.id_app, Functor.map_preimage]
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).hom_inv_id
    · exact ((Types.presheafIso (isoOver i (unop x))).app X).inv_hom_id
  haveI : IsIso (sheafHom i.hom) := by apply NatIso.isIso_of_isIso_app
  apply asIso (sheafHom i.hom)

/--
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary category,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
@[simps! hom_hom inv_hom]
/-
**CategoryTheory.Functor.IsCoverDense.sheafIso** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.Functor.IsCoverDense`。
形式化陈述：sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) : ℱ ≅ ℱ'
参数：i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a natural isomorphism `G ⋙ ℱ ≅ G ⋙ ℱ'` between presheaves of arbitrary cat
egory,
where `G` is locally-full and cover-dense, and `ℱ', ℱ` are sheaves,
we may obtain a natural isomorphism between presheaves.
-/
noncomputable def sheafIso {ℱ ℱ' : Sheaf K A} (i : G.op ⋙ ℱ.obj ≅ G.op ⋙ ℱ'.obj) : ℱ ≅ ℱ' :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (presheafIso i)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The constructed `sheafHom α` is equal to `α` when restricted onto `C`. -/
/-
**CategoryTheory.Functor.IsCoverDense.sheafHom_restrict_eq** 是 Mathlib 中的一个定理，位于
命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : whiskerLeft G.op (sh
eafHom α) = α
参数：α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheaf_eq_amalgamation`：sheaf_eq_amal
gamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT) (x : FamilyOfElement
s _ T) (hx) (t) (h : x.IsAmalgamation t) : t = …
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_compatible`：
pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α x).Co
mpatible
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presieve.CoverByImageStructure.fac`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] {G : Categor…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf`：isSheaf_comp_of_isSheaf
 (s : A ⥤ B) [PreservesLimitsOfSize.{v₁, max v₁ u₁} s] (h : IsSheaf J P) : IsShe
af J (P ⋙ s)
· 使用定理 `CategoryTheory.coyoneda_preservesLimits`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] (X : Cᵒᵖ),   CategoryTheory.Limits.PreservesLimitsOfSi
ze.{t, w, v, v, u, v + 1} (Ca…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.naturality_apply`：naturality_a
pply [G.IsLocallyFull K] {X Y : C} (i : G.obj X ⟶ G.obj Y) (x) : ℱ'.1.map i.op (
α.app _ x) = α.app _ (ℱ.map i.op x)

--- 原说明 ---
The constructed `sheafHom α` is equal to `α` when restricted onto `C`.
-/
theorem sheafHom_restrict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    whiskerLeft G.op (sheafHom α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (G.obj (unop X))) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp
  simp only [Functor.map_comp, ← Category.assoc]
  congr 1
  simp only [Category.assoc]
  congr 1
  simpa using naturality_apply (G := G) (ℱ := ℱ ⋙ coyoneda.obj (op <| (G.op ⋙ ℱ).obj X))
    (ℱ' := ⟨_, Presheaf.isSheaf_comp_of_isSheaf K ℱ'.obj
      (coyoneda.obj (op ((G.op ⋙ ℱ).obj X))) ℱ'.property⟩)
    (whiskerRight α (coyoneda.obj _)) hf.some.map (𝟙 _)

set_option backward.defeqAttrib.useBackward true in
variable (G) in
set_option backward.isDefEq.respectTransparency false in
/--
If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
/-
**CategoryTheory.Functor.IsCoverDense.sheafHom_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cat
egoryTheory.Functor.IsCoverDense`。
形式化陈述：sheafHom_eq (α : ℱ ⟶ ℱ'.obj) : sheafHom (whiskerLeft G.op α) = α
参数：α : ℱ ⟶ ℱ'.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.NatTrans.ext'`：ext' {α β : F ⟶ G} (w : α.app = β.app) : α
 = β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.Functor.map_injective`：map_injective (F : C ⥤ D) [Faithfu
l F] : Function.Injective (F.map : (X ⟶ Y) -> (F.obj X ⟶ F.obj Y))
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_preimage`：map_preimage (F : C ⥤ D) [Full F] {
X Y : C} (f : F.obj X ⟶ F.obj Y) : F.map (preimage F f) = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheaf_eq_amalgamation`：sheaf_eq_amal
gamation (ℱ : Sheaf K A) {X : A} {U : D} {T : Sieve U} (hT) (x : FamilyOfElement
s _ T) (hx) (t) (h : x.IsAmalgamation t) : t = …
· 使用定理 `CategoryTheory.Functor.is_cover_of_isCoverDense`：∀ {C : Type u_1} [inst 
: CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheor
y.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.Types.pushforwardFamily_compatible`：
pushforwardFamily_compatible {X} (x : ℱ.obj (op X)) : (pushforwardFamily α x).Co
mpatible
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Presieve.CoverByImageStructure.fac`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryThe
ory.Category.{v_2, u_2} D] {G : Categor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If the pullback map is obtained via whiskering,
then the result `sheaf_hom (whisker_left G.op α)` is equal to `α`.
-/
theorem sheafHom_eq (α : ℱ ⟶ ℱ'.obj) : sheafHom (whiskerLeft G.op α) = α := by
  ext X
  apply yoneda.map_injective
  ext U
  dsimp [sheafHom, -yoneda_obj_obj, -yoneda_map_app]
  rw [yoneda.map_preimage]
  symm
  change (show (ℱ'.obj ⋙ coyoneda.obj (op (unop U))).obj (op (unop X)) from _) = _
  apply sheaf_eq_amalgamation ℱ' (G.is_cover_of_isCoverDense _ _)
  -- Porting note: next line was not needed in mathlib3
  · exact (pushforwardFamily_compatible _ _)
  intro Y f hf
  conv_lhs => rw [← hf.some.fac]
  dsimp; simp

/--
A locally-full and cover-dense functor `G` induces an equivalence between morphisms into a sheaf and
morphisms over the restrictions via `G`.
-/
/-
**CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom** 是 Mathlib 中的一个定义，位于命
名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) ≃ (ℱ ⟶ ℱ'.obj) where toFu
n
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheafHom_restrict_eq`：sheafHom_restr
ict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : whiskerLeft G.op (sheafHom α) = α
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheafHom_eq`：sheafHom_eq (α : ℱ ⟶ ℱ'
.obj) : sheafHom (whiskerLeft G.op α) = α

--- 原说明 ---
A locally-full and cover-dense functor `G` induces an equivalence between morphi
sms into a sheaf and
morphisms over the restrictions via `G`.
-/
noncomputable def restrictHomEquivHom : (G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) ≃ (ℱ ⟶ ℱ'.obj) where
  toFun := sheafHom
  invFun := whiskerLeft G.op
  left_inv := sheafHom_restrict_eq
  right_inv := sheafHom_eq _

@[reassoc]
/-
**CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_right_symm*
* 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：restrictHomEquivHom_naturality_right_symm (f : ℱ ⟶ ℱ'.obj) {𝒢'} (g : ℱ' ⟶ 
𝒢') : (restrictHomEquivHom (G
参数：f : ℱ ⟶ ℱ'.obj；g : ℱ' ⟶ 𝒢'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma restrictHomEquivHom_naturality_right_symm
    (f : ℱ ⟶ ℱ'.obj) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    (restrictHomEquivHom (G := G)).symm (f ≫ g.hom) =
      restrictHomEquivHom.symm f ≫ whiskerLeft _ g.hom := rfl

@[reassoc]
/-
**CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_right** 是 M
athlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：restrictHomEquivHom_naturality_right (f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) {𝒢'} (
g : ℱ' ⟶ 𝒢') : restrictHomEquivHom (f ≫ whiskerLeft G.op g.hom) = restrictHomEqu
ivHom f ≫ g.hom
参数：f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj；g : ℱ' ⟶ 𝒢'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_right
_symm`：restrictHomEquivHom_naturality_right_symm (f : ℱ ⟶ ℱ'.obj) {𝒢'} (g : ℱ' ⟶
 𝒢') : (restrictHomEquivHom (G
-/
lemma restrictHomEquivHom_naturality_right
    (f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) {𝒢'} (g : ℱ' ⟶ 𝒢') :
    restrictHomEquivHom (f ≫ whiskerLeft G.op g.hom) =
      restrictHomEquivHom f ≫ g.hom := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_right_symm (G := G) (restrictHomEquivHom f) g).symm

@[reassoc]
/-
**CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_left_symm**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：restrictHomEquivHom_naturality_left_symm {𝒢} (f : 𝒢 ⟶ ℱ) (g : ℱ ⟶ ℱ'.obj) 
: (restrictHomEquivHom (G
参数：f : 𝒢 ⟶ ℱ；g : ℱ ⟶ ℱ'.obj。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma restrictHomEquivHom_naturality_left_symm
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : ℱ ⟶ ℱ'.obj) :
    (restrictHomEquivHom (G := G)).symm (f ≫ g) =
      whiskerLeft G.op f ≫ restrictHomEquivHom.symm g := rfl

@[reassoc]
/-
**CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_left** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：restrictHomEquivHom_naturality_left {𝒢} (f : 𝒢 ⟶ ℱ) (g : G.op ⋙ ℱ ⟶ G.op ⋙
 ℱ'.obj) : restrictHomEquivHom (whiskerLeft _ f ≫ g) = f ≫ restrictHomEquivHom g
参数：f : 𝒢 ⟶ ℱ；g : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_left_
symm`：restrictHomEquivHom_naturality_left_symm {𝒢} (f : 𝒢 ⟶ ℱ) (g : ℱ ⟶ ℱ'.obj) 
: (restrictHomEquivHom (G
-/
lemma restrictHomEquivHom_naturality_left
    {𝒢} (f : 𝒢 ⟶ ℱ) (g : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) :
    restrictHomEquivHom (whiskerLeft _ f ≫ g) =
      f ≫ restrictHomEquivHom g := by
  apply (restrictHomEquivHom (G := G)).symm.injective
  simpa only [Equiv.symm_apply_apply] using
    (restrictHomEquivHom_naturality_left_symm (G := G) (f := f)
      (g := restrictHomEquivHom g)).symm

/-- Given a locally-full and cover-dense functor `G` and a natural transformation of sheaves
`α : ℱ ⟶ ℱ'`, if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
/-
**CategoryTheory.Functor.IsCoverDense.iso_of_restrict_iso** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLef
t G.op α.hom)) : IsIso α
参数：α : ℱ ⟶ ℱ'；i : IsIso (whiskerLeft G.op α.hom)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheafHom_eq`：sheafHom_eq (α : ℱ ⟶ ℱ'
.obj) : sheafHom (whiskerLeft G.op α) = α
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom

--- 原说明 ---
Given a locally-full and cover-dense functor `G` and a natural transformation of
 sheaves
`α : ℱ ⟶ ℱ'`, if the pullback of `α` along `G` is iso, then `α` is also iso.
-/
theorem iso_of_restrict_iso {ℱ ℱ' : Sheaf K A} (α : ℱ ⟶ ℱ') (i : IsIso (whiskerLeft G.op α.hom)) :
    IsIso α := by
  convert! (sheafIso (asIso (whiskerLeft G.op α.hom))).isIso_hom using 1
  ext1
  apply (sheafHom_eq _ _).symm

variable (G K)

/-- A locally-fully-faithful and cover-dense functor preserves compatible families. -/
/-
**CategoryTheory.Functor.IsCoverDense.compatiblePreserving** 是 Mathlib 中的一个引理，位于
命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：compatiblePreserving [G.IsLocallyFaithful K] : CompatiblePreserving K G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsCoverDense.ext`：ext [G.IsCoverDense K] (ℱ : She
af K Type*) (X : D) {s t : ℱ.obj.obj (op X)} (h : forall ⦃Y : C⦄ (f : G.obj Y ⟶ 
X), ℱ.obj.map f.op s = ℱ.obj.…
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.ext`：∀ {C : Type uC} [inst : Catego
ryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Category.{v
D, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.ext`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A locally-fully-faithful and cover-dense functor preserves compatible families.
-/
lemma compatiblePreserving [G.IsLocallyFaithful K] : CompatiblePreserving K G := by
  constructor
  intro ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ eq
  apply Functor.IsCoverDense.ext G
  intro W i
  refine IsLocallyFull.ext G _ (i ≫ f₁) fun V₁ iVW iV₁Y₁ e₁ ↦ ?_
  refine IsLocallyFull.ext G _ (G.map iVW ≫ i ≫ f₂) fun V₂ iV₂V₁ iV₂Y₂ e₂ ↦ ?_
  refine IsLocallyFaithful.ext G _ (iV₂V₁ ≫ iV₁Y₁ ≫ g₁) (iV₂Y₂ ≫ g₂) (by simp [e₁, e₂, eq]) ?_
  intro V₃ iV₃ e₄
  simp only [← op_comp, ← Functor.map_comp_apply, ← e₁, ← e₂, ← Functor.map_comp]
  apply hx
  simpa using e₄
/-
**CategoryTheory.Functor.IsCoverDense.isContinuous** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor.IsCoverDense`。
形式化陈述：isContinuous [G.IsLocallyFaithful K] (Hp : CoverPreserving J K G) : G.IsCo
ntinuous J K
参数：Hp : CoverPreserving J K G。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.isContinuous_of_coverPreserving`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用引理 `CategoryTheory.Functor.IsCoverDense.compatiblePreserving`：compatiblePres
erving [G.IsLocallyFaithful K] : CompatiblePreserving K G
-/
lemma isContinuous [G.IsLocallyFaithful K] (Hp : CoverPreserving J K G) : G.IsContinuous J K :=
  isContinuous_of_coverPreserving (compatiblePreserving K G) Hp
/-
**CategoryTheory.Functor.IsCoverDense.full_sheafPushforwardContinuous** 是 Mathli
b 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：full_sheafPushforwardContinuous [G.IsContinuous J K] : Full (G.sheafPushfo
rwardContinuous A J K) where map_surjective α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Sheaf.hom_ext`：∀ {C : Type u₁} [inst : CategoryTheory.Cat
egory.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Type u₂}   [i
nst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheafHom_restrict_eq`：sheafHom_restr
ict_eq (α : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) : whiskerLeft G.op (sheafHom α) = α
-/
instance full_sheafPushforwardContinuous [G.IsContinuous J K] :
    Full (G.sheafPushforwardContinuous A J K) where
  map_surjective α := ⟨⟨sheafHom α.hom⟩, Sheaf.hom_ext <| sheafHom_restrict_eq α.hom⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.IsCoverDense.faithful_sheafPushforwardContinuous** 是 Ma
thlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsCoverDense`。
形式化陈述：faithful_sheafPushforwardContinuous [G.IsContinuous J K] : Faithful (G.she
afPushforwardContinuous A J K) where map_injective
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.hom_ext`：hom_ext {X Y : P.FullSubcategory}
 {f g : X ⟶ Y} (h : f.hom = g.hom) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.IsCoverDense.sheafHom_eq`：sheafHom_eq (α : ℱ ⟶ ℱ'
.obj) : sheafHom (whiskerLeft G.op α) = α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance faithful_sheafPushforwardContinuous [G.IsContinuous J K] :
    Faithful (G.sheafPushforwardContinuous A J K) where
  map_injective := by
    intro ℱ ℱ' α β e
    ext1
    apply_fun fun e => e.hom at e
    dsimp [sheafPushforwardContinuous] at e
    rw [← sheafHom_eq G α.hom, ← sheafHom_eq G β.hom, e]

end IsCoverDense

/-- If `G : C ⥤ D` is cover dense and full, then the
map `(P ⟶ Q) → (G.op ⋙ P ⟶ G.op ⋙ Q)` is bijective when `Q` is a sheaf. -/
/-
**CategoryTheory.Functor.whiskerLeft_obj_map_bijective_of_isCoverDense** 是 Mathl
ib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：whiskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D) [G.IsCoverDense 
K] [G.IsLocallyFull K] {A : Type*} [Category* A] (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.
IsSheaf K Q) : Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (
P ⟶ Q) -> _)
参数：G : C ⥤ D；P Q : Dᵒᵖ ⥤ A；hQ : Presheaf.IsSheaf K Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `G : C ⥤ D` is cover dense and full, then the
map `(P ⟶ Q) → (G.op ⋙ P ⟶ G.op ⋙ Q)` is bijective when `Q` is a sheaf.
-/
lemma whiskerLeft_obj_map_bijective_of_isCoverDense (G : C ⥤ D)
    [G.IsCoverDense K] [G.IsLocallyFull K] {A : Type*} [Category* A]
    (P Q : Dᵒᵖ ⥤ A) (hQ : Presheaf.IsSheaf K Q) :
    Function.Bijective (((whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj G.op).map : (P ⟶ Q) → _) :=
  (IsCoverDense.restrictHomEquivHom (ℱ' := ⟨Q, hQ⟩)).symm.bijective

variable (G : C ⥤ D) {A : Type*} [Category* A]

/-- The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`
if `G` is cover-dense, locally fully-faithful,
and `S` is a cover of `C` if and only if the image of `S` in `D` is a cover. -/
/-
**CategoryTheory.Functor.IsDenseSubsite** 是 Mathlib 中的一个类，位于命名空间 `CategoryTheory
.Functor`。
形式化陈述：IsDenseSubsite : Prop where isCoverDense' : G.IsCoverDense K
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`
if `G` is cover-dense, locally fully-faithful,
and `S` is a cover of `C` if and only if the image of `S` in `D` is a cover.
-/
class IsDenseSubsite : Prop where
  isCoverDense' : G.IsCoverDense K := by infer_instance
  isLocallyFull' : G.IsLocallyFull K := by infer_instance
  isLocallyFaithful' : G.IsLocallyFaithful K := by infer_instance
  functorPushforward_mem_iff : ∀ {X : C} {S : Sieve X}, S.functorPushforward G ∈ K _ ↔ S ∈ J _
/-
**CategoryTheory.Functor.functorPushforward_mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：functorPushforward_mem_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] : 
S.functorPushforward G in K _ ↔ S in J _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff`：∀ {C :
 Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {J : Categor…
-/
lemma functorPushforward_mem_iff {X : C} {S : Sieve X} [G.IsDenseSubsite J K] :
    S.functorPushforward G ∈ K _ ↔ S ∈ J _ := IsDenseSubsite.functorPushforward_mem_iff

namespace IsDenseSubsite

variable [G.IsDenseSubsite J K]

include J K

/-
**CategoryTheory.Functor.IsDenseSubsite.isCoverDense** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：isCoverDense : G.IsCoverDense K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense'`：∀ {C : Type u_1} {i
nst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : CategoryT
heory.Category.{v_2, u_2} D} (J : Categor…
-/
lemma isCoverDense : G.IsCoverDense K := isCoverDense' J
/-
**CategoryTheory.Functor.IsDenseSubsite.isLocallyFull** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：isLocallyFull : G.IsLocallyFull K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull'`：∀ {C : Type u_1} {
inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Category
Theory.Category.{v_2, u_2} D} (J : Categor…
-/
lemma isLocallyFull : G.IsLocallyFull K := isLocallyFull' J
/-
**CategoryTheory.Functor.IsDenseSubsite.isLocallyFaithful** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：isLocallyFaithful : G.IsLocallyFaithful K
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFaithful'`：∀ {C : Type u_
1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_1 : Cate
goryTheory.Category.{v_2, u_2} D} (J : Categor…
-/
lemma isLocallyFaithful : G.IsLocallyFaithful K := isLocallyFaithful' J
/-
**CategoryTheory.Functor.IsDenseSubsite.coverPreserving** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：coverPreserving : CoverPreserving J K G
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff`：∀ {C :
 Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {J : Categor…
-/
lemma coverPreserving : CoverPreserving J K G :=
  ⟨functorPushforward_mem_iff.mpr⟩
/-
**CategoryTheory.Functor.IsDenseSubsite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsDenseSubsite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) : G.IsContinuous J K :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsCoverDense.isContinuous J K G (IsDenseSubsite.coverPreserving J K G)
/-
**CategoryTheory.Functor.IsDenseSubsite.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheo
ry.Functor.IsDenseSubsite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) : G.IsCocontinuous J K where
  cover_lift hS :=
    letI := IsDenseSubsite.isCoverDense J K G
    letI := IsDenseSubsite.isLocallyFull J K G
    IsDenseSubsite.functorPushforward_mem_iff.mp
      (IsCoverDense.functorPullback_pushforward_covering ⟨_, hS⟩)
/-
**CategoryTheory.Functor.IsDenseSubsite.full_sheafPushforwardContinuous** 是 Math
lib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：full_sheafPushforwardContinuous : Full (G.sheafPushforwardContinuous A J K
)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
-/
instance full_sheafPushforwardContinuous :
    Full (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance
/-
**CategoryTheory.Functor.IsDenseSubsite.faithful_sheafPushforwardContinuous** 是 
Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：faithful_sheafPushforwardContinuous : Faithful (G.sheafPushforwardContinuo
us A J K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
-/
instance faithful_sheafPushforwardContinuous :
    Faithful (G.sheafPushforwardContinuous A J K) :=
  letI := IsDenseSubsite.isCoverDense J K G
  letI := IsDenseSubsite.isLocallyFull J K G
  inferInstance
/-
**CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：imageSieve_mem {U V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
参数：f : G.obj U ⟶ G.obj V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff`：∀ {C :
 Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {J : Categor…
· 使用引理 `CategoryTheory.Functor.functorPushforward_imageSieve_mem`：functorPushfor
ward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) : (G.image
Sieve f).functorPushforward G in K _
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
-/
lemma imageSieve_mem {U V} (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f ∈ J _ :=
  letI := IsDenseSubsite.isLocallyFull J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_imageSieve_mem K f)
/-
**CategoryTheory.Functor.IsDenseSubsite.equalizer_mem** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：equalizer_mem {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) : Sieve.equa
lizer f₁ f₂ in J _
参数：f₁ f₂ : U ⟶ V；e : G.map f₁ = G.map f₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.functorPushforward_mem_iff`：∀ {C :
 Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Type u_2}   {inst_
1 : CategoryTheory.Category.{v_2, u_2} D} {J : Categor…
· 使用引理 `CategoryTheory.Functor.functorPushforward_equalizer_mem`：functorPushforw
ard_equalizer_mem [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = 
G.map f₂) : (Sieve.equalizer f₁ f₂).functorPu…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFaithful`：isLocallyFaithf
ul : G.IsLocallyFaithful K
-/
lemma equalizer_mem {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
    Sieve.equalizer f₁ f₂ ∈ J _ :=
  letI := IsDenseSubsite.isLocallyFaithful J K G
  IsDenseSubsite.functorPushforward_mem_iff.mp (G.functorPushforward_equalizer_mem K f₁ f₂ e)

variable {J} (F : Sheaf J A)

set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Functor.IsDenseSubsite.map_eq_of_eq** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：map_eq_of_eq {X Y : C} (f₁ f₂ : X ⟶ Y) (h : G.map f₁ = G.map f₂) : F.obj.m
ap f₁.op = F.obj.map f₂.op
参数：f₁ f₂ : X ⟶ Y；h : G.map f₁ = G.map f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.equalizer_mem`：equalizer_mem {U V}
 (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) : Sieve.equalizer f₁ f₂ in J _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_eq_of_eq {X Y : C} (f₁ f₂ : X ⟶ Y)
    (h : G.map f₁ = G.map f₂) :
    F.obj.map f₁.op = F.obj.map f₂.op :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, IsDenseSubsite.equalizer_mem J K G _ _ h⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      simp only [← Functor.map_comp, ← op_comp, ha])

/-- If `G : C ⥤ D` is a dense subsite and `F` a sheaf on `C`, this is the morphism
`F.val.obj (op Y) ⟶ F.val.obj (op X)` induced by a morphism
`G.obj X ⟶ G.obj Y` in the category `D`. -/
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage {X Y : C} (f : G.obj X ⟶ G.obj Y) : F.obj.obj (op Y) ⟶ F.obj.o
bj (op X)
参数：f : G.obj X ⟶ G.obj Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _

--- 原说明 ---
If `G : C ⥤ D` is a dense subsite and `F` a sheaf on `C`, this is the morphism
`F.val.obj (op Y) ⟶ F.val.obj (op X)` induced by a morphism
`G.obj X ⟶ G.obj Y` in the category `D`.
-/
noncomputable def mapPreimage {X Y : C} (f : G.obj X ⟶ G.obj Y) :
    F.obj.obj (op Y) ⟶ F.obj.obj (op X) :=
  F.property.amalgamate
    ⟨_, imageSieve_mem J K G f⟩ (fun ⟨W₀, a, ha⟩ ↦ F.obj.map ha.choose.op) (by
      rintro ⟨W₀, a, ha⟩ ⟨W₀', a', ha'⟩ ⟨T₀, p₁, p₂, fac⟩
      rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
      apply map_eq_of_eq K G
      rw [Functor.map_comp, Functor.map_comp, ha.choose_spec, ha'.choose_spec,
        ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, fac])
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map_of_fac** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (p : Z ⟶ X) (g 
: Z ⟶ Y) (fac : G.map p ≫ f = G.map g) : mapPreimage K G F f ≫ F.obj.map p.op = 
F.obj.map g.op
参数：f : G.obj X ⟶ G.obj Y；p : Z ⟶ X；g : Z ⟶ Y；fac : G.map p ≫ f = G.map g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.op_comp`：op_comp {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z} : (f
 ≫ g).op = g.op ≫ f.op
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage.eq_1`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] {J : Categor…
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.amalgamate_map`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} 
{A : Type u₂}   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.map_eq_of_eq`：map_eq_of_eq {X Y : 
C} (f₁ f₂ : X ⟶ Y) (h : G.map f₁ = G.map f₂) : F.obj.map f₁.op = F.obj.map f₂.op
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `CategoryTheory.Functor.map_comp_assoc`：∀ {C : Type u₁} [inst : CategoryT
heory.Category.{v_1, u₁} C] {D : Type u₂}   [inst_1 : CategoryTheory.Category.{v
_2, u₂} D] (F : CategoryThe…
-/
lemma mapPreimage_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (p : Z ⟶ X) (g : Z ⟶ Y) (fac : G.map p ≫ f = G.map g) :
    mapPreimage K G F f ≫ F.obj.map p.op = F.obj.map g.op :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, J.pullback_stable p (imageSieve_mem J K G f)⟩ _ _ (by
      rintro ⟨W₀, a, ha⟩
      dsimp at ha ⊢
      rw [Category.assoc, ← Functor.map_comp, ← op_comp, mapPreimage]
      rw [F.2.amalgamate_map ⟨_, imageSieve_mem J K G f⟩
        (fun ⟨W₀, a, ha⟩ ↦ F.obj.map ha.choose.op) _ ⟨W₀, a ≫ p, ha⟩,
        ← Functor.map_comp, ← op_comp]
      apply map_eq_of_eq K G
      rw [ha.choose_spec, Functor.map_comp_assoc, Functor.map_comp, fac])
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_of_eq** 是 Mathlib 中的一个引理，位于命
名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_of_eq {X Y : C} (f : G.obj X ⟶ G.obj Y) (g : X ⟶ Y) (h : G.map
 g = f) : mapPreimage K G F f = F.obj.map g.op
参数：f : G.obj X ⟶ G.obj Y；g : X ⟶ Y；h : G.map g = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map_of_fac`：mapPreimag
e_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (p : Z ⟶ X) (g : Z ⟶ Y) (fac : 
G.map p ≫ f = G.map g) : mapPreimage K G F f ≫ F.o…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mapPreimage_of_eq {X Y : C} (f : G.obj X ⟶ G.obj Y)
    (g : X ⟶ Y) (h : G.map g = f) :
    mapPreimage K G F f = F.obj.map g.op := by
  simpa using mapPreimage_map_of_fac K G F f (𝟙 _) g (by simpa using h.symm)

@[simp]
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_map {X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.ob
j.map f.op
参数：f : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_of_eq`：mapPreimage_of_
eq {X Y : C} (f : G.obj X ⟶ G.obj Y) (g : X ⟶ Y) (h : G.map g = f) : mapPreimage
 K G F f = F.obj.map g.op
-/
lemma mapPreimage_map {X Y : C} (f : X ⟶ Y) :
    mapPreimage K G F (G.map f) = F.obj.map f.op :=
  mapPreimage_of_eq K G F (G.map f) f rfl

@[simp]
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_id** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_id (X : C) : mapPreimage K G F (𝟙 (G.obj X)) = 𝟙 _
参数：X : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map`：mapPreimage_map {
X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.obj.map f.op
· 使用定理 `CategoryTheory.op_id`：op_id {X : C} : (𝟙 X).op = 𝟙 (op X)
-/
lemma mapPreimage_id (X : C) :
    mapPreimage K G F (𝟙 (G.obj X)) = 𝟙 _ := by
  rw [← G.map_id, mapPreimage_map, op_id, map_id]

@[reassoc]
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_comp {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : G.obj Y ⟶ G.obj 
Z) : mapPreimage K G F (f ≫ g) = mapPreimage K G F g ≫ mapPreimage K G F f
参数：f : G.obj X ⟶ G.obj Y；g : G.obj Y ⟶ G.obj Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presheaf.IsSheaf.hom_ext`：∀ {C : Type u₁} [inst : Categor
yTheory.Category.{v₁, u₁} C] {J : CategoryTheory.GrothendieckTopology C} {A : Ty
pe u₂}   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.imageSieve_mem`：imageSieve_mem {U 
V} (f : G.obj U ⟶ G.obj V) : G.imageSieve f in J _
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map_of_fac`：mapPreimag
e_map_of_fac {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (p : Z ⟶ X) (g : Z ⟶ Y) (fac : 
G.map p ≫ f = G.map g) : mapPreimage K G F f ≫ F.o…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapPreimage_comp {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : G.obj Y ⟶ G.obj Z) :
    mapPreimage K G F (f ≫ g) = mapPreimage K G F g ≫ mapPreimage K G F f :=
  Presheaf.IsSheaf.hom_ext F.property
    ⟨_, imageSieve_mem J K G f⟩ _ _ (by
      rintro ⟨T₀, a, ⟨b, fac₁⟩⟩
      apply Presheaf.IsSheaf.hom_ext F.property
        ⟨_, J.pullback_stable b (imageSieve_mem J K G g)⟩
      rintro ⟨U₀, c, ⟨d, fac₂⟩⟩
      dsimp
      simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
      rw [mapPreimage_map_of_fac K G F (f ≫ g) (c ≫ a) d,
        mapPreimage_map_of_fac K G F f (c ≫ a) (c ≫ b),
        mapPreimage_map_of_fac K G F g (c ≫ b) d]
      all_goals
        simp only [Functor.map_comp, Category.assoc, fac₁, fac₂])

@[reassoc]
/-
**CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp_map** 是 Mathlib 中的一个引理，
位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：mapPreimage_comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : Z ⟶ X) : map
Preimage K G F f ≫ F.obj.map g.op = mapPreimage K G F (G.map g ≫ f)
参数：f : G.obj X ⟶ G.obj Y；g : Z ⟶ X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_comp`：mapPreimage_comp
 {X Y Z : C} (f : G.obj X ⟶ G.obj Y) (g : G.obj Y ⟶ G.obj Z) : mapPreimage K G F
 (f ≫ g) = mapPreimage K G F g ≫ mapPreimage…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.mapPreimage_map`：mapPreimage_map {
X Y : C} (f : X ⟶ Y) : mapPreimage K G F (G.map f) = F.obj.map f.op
-/
lemma mapPreimage_comp_map {X Y Z : C} (f : G.obj X ⟶ G.obj Y)
    (g : Z ⟶ X) :
    mapPreimage K G F f ≫ F.obj.map g.op =
      mapPreimage K G F (G.map g ≫ f) := by
  rw [mapPreimage_comp, mapPreimage_map]

section

variable (J) [IsEquivalence (sheafPushforwardContinuous G A J K)]

section

variable [HasWeakSheafify J A]

variable (A) in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories
this is a sheafification functor `(Dᵒᵖ ⥤ A) ⥤ Sheaf K A`
when `HasWeakSheafify J A` holds. -/
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyOfIsEquivalence** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyOfIsEquivalence : (Dᵒᵖ ⥤ A) ⥤ Sheaf K A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…

--- 原说明 ---
Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`
)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories
this is a sheafification functor `(Dᵒᵖ ⥤ A) ⥤ Sheaf K A`
when `HasWeakSheafify J A` holds.
-/
noncomputable def sheafifyOfIsEquivalence :
    (Dᵒᵖ ⥤ A) ⥤ Sheaf K A :=
  (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A ⋙
    inv (G.sheafPushforwardContinuous A J K)

variable (A) in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories, this is
the isomorphism between `sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardContinuous A J K`
and the functor which sends a presheaf to the sheafification of its precomposition by `G.op`. -/
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyOfIsEquivalenceCompIso** 是 Mathl
ib 中的一个定义，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyOfIsEquivalenceCompIso : sheafifyOfIsEquivalence J K G A ⋙ G.sheaf
PushforwardContinuous A J K ≅ (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf 
J A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…

--- 原说明 ---
Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`
)
and `sheafPushforwardContinuous G A J₀ J` is an equivalence of categories, this 
is
the isomorphism between `sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardCon
tinuous A J K`
and the functor which sends a presheaf to the sheafification of its precompositi
on by `G.op`.
-/
noncomputable def sheafifyOfIsEquivalenceCompIso :
    sheafifyOfIsEquivalence J K G A ⋙ G.sheafPushforwardContinuous A J K ≅
      (whiskeringLeft _ _ _).obj G.op ⋙ presheafToSheaf J A :=
  associator _ _ _ ≪≫ isoWhiskerLeft _ (associator _ _ _) ≪≫
    isoWhiskerLeft _ (isoWhiskerLeft _
      (sheafPushforwardContinuous G A J K).asEquivalence.counitIso ≪≫ Functor.rightUnitor _)

/-- Auxiliary definition for `sheafifyAdjunctionOfIsEquivalence`. -/
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence** 是 Math
lib 中的一个定义，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyHomEquivOfIsEquivalence {P : Dᵒᵖ ⥤ A} {Q : Sheaf K A} : ((sheafify
OfIsEquivalence J K G A).obj P ⟶ Q) ≃ (P ⟶ Q.obj)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K

--- 原说明 ---
Auxiliary definition for `sheafifyAdjunctionOfIsEquivalence`.
-/
noncomputable def sheafifyHomEquivOfIsEquivalence
    {P : Dᵒᵖ ⥤ A} {Q : Sheaf K A} :
    ((sheafifyOfIsEquivalence J K G A).obj P ⟶ Q) ≃ (P ⟶ Q.obj) :=
  haveI := IsDenseSubsite.isLocallyFull J K G
  haveI := IsDenseSubsite.isCoverDense J K G
  ((G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence_naturali
ty_left** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyHomEquivOfIsEquivalence_naturality_left {P₁ P₂ : Dᵒᵖ ⥤ A} (f : P₁ 
⟶ P₂) {Q : Sheaf K A} (g : (sheafifyOfIsEquivalence J K G A).obj P₂ ⟶ Q) : sheaf
ifyHomEquivOfIsEquivalence J K G ((sheafifyOfIsEquivalence J K G A).map f ≫ g) =
 f ≫ sheafifyHomEquivOfIsEquivalence J K G g
参数：f : P₁ ⟶ P₂；g : (sheafifyOfIsEquivalence J K G A).obj P₂ ⟶ Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_left`
：restrictHomEquivHom_naturality_left {𝒢} (f : 𝒢 ⟶ ℱ) (g : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.o
bj) : restrictHomEquivHom (whiskerLeft _ f ≫ g) = f ≫ restric…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_left`：homEquiv_naturality_
left (f : X' ⟶ X) (g : F.obj X ⟶ Y) : (adj.homEquiv X' Y) (F.map f ≫ g) = f ≫ (a
dj.homEquiv X Y) g
-/
lemma sheafifyHomEquivOfIsEquivalence_naturality_left
    {P₁ P₂ : Dᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) {Q : Sheaf K A}
    (g : (sheafifyOfIsEquivalence J K G A).obj P₂ ⟶ Q) :
      sheafifyHomEquivOfIsEquivalence J K G
        ((sheafifyOfIsEquivalence J K G A).map f ≫ g) =
        f ≫ sheafifyHomEquivOfIsEquivalence J K G g := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((sheafifyOfIsEquivalence J K G A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  rw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  congr 2
  trans adj₂.homEquiv _ _ ((presheafToSheaf J A).map (G.op.whiskerLeft f) ≫
    (adj₁.homEquiv _ _) g)
  · congr 1
    apply adj₁.homEquiv_naturality_left
  · apply adj₂.homEquiv_naturality_left

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc]
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence_naturali
ty_right** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyHomEquivOfIsEquivalence_naturality_right {P : Dᵒᵖ ⥤ A} {Q₁ Q₂ : Sh
eaf K A} (f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁) (g : Q₁ ⟶ Q₂) : shea
fifyHomEquivOfIsEquivalence J K G (f ≫ g) = sheafifyHomEquivOfIsEquivalence J K 
G f ≫ g.hom
参数：f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁；g : Q₁ ⟶ Q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isLocallyFull`：isLocallyFull : G.I
sLocallyFull K
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.isCoverDense`：isCoverDense : G.IsC
overDense K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Adjunction.homEquiv_naturality_right`：homEquiv_naturality
_right (f : F.obj X ⟶ Y) (g : Y ⟶ Y') : (adj.homEquiv X Y') (f ≫ g) = (adj.homEq
uiv X Y) f ≫ G.map g
· 使用引理 `CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom_naturality_right
`：restrictHomEquivHom_naturality_right (f : G.op ⋙ ℱ ⟶ G.op ⋙ ℱ'.obj) {𝒢'} (g : 
ℱ' ⟶ 𝒢') : restrictHomEquivHom (f ≫ whiskerLeft G.op g.hom) = …
-/
lemma sheafifyHomEquivOfIsEquivalence_naturality_right
    {P : Dᵒᵖ ⥤ A} {Q₁ Q₂ : Sheaf K A}
    (f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁) (g : Q₁ ⟶ Q₂) :
      sheafifyHomEquivOfIsEquivalence J K G (f ≫ g) =
        sheafifyHomEquivOfIsEquivalence J K G f ≫ g.hom := by
  have := IsDenseSubsite.isLocallyFull J K G
  have := IsDenseSubsite.isCoverDense J K G
  let adj₁ := (G.sheafPushforwardContinuous A J K).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.hom
  rw [adj₁.homEquiv_naturality_right, adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

variable (A)

set_option backward.isDefEq.respectTransparency false in
/-- Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`)
and `sheafPushforwardContinuous G A J K` is an equivalence of categories, and
that `HasWeakSheafify J A` holds, then this adjunction shows the existence
of a left adjoint to `sheafToPresheaf K A`. -/
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafifyAdjunctionOfIsEquivalence** 是 Ma
thlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafifyAdjunctionOfIsEquivalence : sheafifyOfIsEquivalence J K G A ⊣ shea
fToPresheaf K A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用引理 `CategoryTheory.Functor.IsDenseSubsite.sheafifyHomEquivOfIsEquivalence_na
turality_right`：sheafifyHomEquivOfIsEquivalence_naturality_right {P : Dᵒᵖ ⥤ A} {
Q₁ Q₂ : Sheaf K A} (f : (sheafifyOfIsEquivalence J K G A).obj P ⟶ Q₁) (g : Q…

--- 原说明 ---
Assuming that `(C, J)` is a dense subsite of `(D, K)` (via a functor `G : C ⥤ D`
)
and `sheafPushforwardContinuous G A J K` is an equivalence of categories, and
that `HasWeakSheafify J A` holds, then this adjunction shows the existence
of a left adjoint to `sheafToPresheaf K A`.
-/
noncomputable def sheafifyAdjunctionOfIsEquivalence :
    sheafifyOfIsEquivalence J K G A ⊣ sheafToPresheaf K A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q ↦ sheafifyHomEquivOfIsEquivalence J K G
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g ↦
        (sheafifyHomEquivOfIsEquivalence J K G).injective (by
          simp [sheafifyHomEquivOfIsEquivalence_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsEquivalence_naturality_right J K G }

include G K in
/-
**CategoryTheory.Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence** 是 Mat
hlib 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：hasWeakSheafify_of_isEquivalence : HasWeakSheafify K A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
-/
lemma hasWeakSheafify_of_isEquivalence :
    HasWeakSheafify K A := ⟨_, ⟨sheafifyAdjunctionOfIsEquivalence J K G A⟩⟩

end

open Limits in
include G in
/-
**CategoryTheory.Functor.IsDenseSubsite.hasSheafify_of_isEquivalence** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：hasSheafify_of_isEquivalence [HasSheafify J A] [HasFiniteLimits A] : HasSh
eafify K A
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.instHasWeakSheafifyOfHasSheafify`：∀ {C : Type u₁} [inst :
 CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C)
 (A : Type u₂)   [inst_1 : CategoryTh…
· 使用引理 `CategoryTheory.Limits.comp_preservesFiniteLimits`：comp_preservesFiniteLi
mits (F : C ⥤ D) (G : D ⥤ E) [PreservesFiniteLimits F] [PreservesFiniteLimits G]
 : PreservesFiniteLimits (F ⋙ G)
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorOppositeSheafPresheafToSh
eaf`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] (J : CategoryTh
eory.GrothendieckTopology C) (A : Type u₂)   [inst_1 : CategoryTh…
· 使用定理 `CategoryTheory.Limits.PreservesLimits.preservesFiniteLimits`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Categor
yTheory.Category.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instPreservesLimitsOfSizeOfIsRightAdjoint`：∀ {C :
 Type u_2} {D : Type u_3} [inst : CategoryTheory.Category.{v_2, u_2} C]   [inst_
1 : CategoryTheory.Category.{v_3, u_3} D] (F : Categor…
· 使用定理 `CategoryTheory.Functor.isRightAdjoint_of_isEquivalence`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.instPreservesFiniteLimitsFunctorObjWhiskeringLeftOfHasFin
iteLimits`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type
 u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {E : Type u₃} [ins…
· 使用定理 `CategoryTheory.HasSheafify.mk'`：∀ {C : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} C] (J : CategoryTheory.GrothendieckTopology C) (A : Type u₂)   
[inst_1 : CategoryTh…
-/
lemma hasSheafify_of_isEquivalence [HasSheafify J A] [HasFiniteLimits A] :
    HasSheafify K A := by
  have : PreservesFiniteLimits (presheafToSheaf J A ⋙
    (G.sheafPushforwardContinuous A J K).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (sheafifyOfIsEquivalence J K G A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsEquivalence J K G A)

end

section

variable (J A) [IsEquivalence (sheafPushforwardContinuous G A J K)]

/--
If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and the
pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, then this
is the equivalence `Sheaf K A ≌ Sheaf J A`. -/
@[simps! inverse]
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Ca
tegoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafEquiv : Sheaf J A ≌ Sheaf K A
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…

--- 原说明 ---
If `G : C ⥤ D` exhibits `(C, J)` as a dense subsite of `(D, K)`, and the
pushforward functor `Sheaf K A ⥤ Sheaf J A` is an equivalence, then this
is the equivalence `Sheaf K A ≌ Sheaf J A`.
-/
noncomputable def sheafEquiv : Sheaf J A ≌ Sheaf K A :=
  (sheafPushforwardContinuous G A J K).asEquivalence.symm

variable [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- The natural isomorphism exhibiting the compatibility of
`IsDenseSubsite.sheafEquiv` with sheafification. -/
noncomputable
/-
**CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility** 
是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Functor.IsDenseSubsite`。
形式化陈述：sheafEquivSheafificationCompatibility : (whiskeringLeft _ _ A).obj G.op ⋙ 
presheafToSheaf J A ≅ presheafToSheaf K A ⋙ (sheafEquiv J K G A).inverse
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
-/
def sheafEquivSheafificationCompatibility :
    (whiskeringLeft _ _ A).obj G.op ⋙ presheafToSheaf J A ≅
      presheafToSheaf K A ⋙ (sheafEquiv J K G A).inverse :=
  (sheafifyOfIsEquivalenceCompIso _ _ _ _).symm ≪≫
    isoWhiskerRight
      ((sheafifyAdjunctionOfIsEquivalence J K G A).leftAdjointUniq
        (sheafificationAdjunction K A)) _

end

end IsDenseSubsite

end Functor

end CategoryTheory

