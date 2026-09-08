/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Over

/-!
# Restriction of Schemes and Morphisms

## Main definition
- `AlgebraicGeometry.Scheme.restrict`: The restriction of a scheme along an open embedding.
  The map `X.restrict f ⟶ X` is `AlgebraicGeometry.Scheme.ofRestrict`.
  `U : X.Opens` has a coercion to `Scheme` and `U.ι` is a shorthand
  for `X.restrict U.open_embedding : U ⟶ X`.
- `AlgebraicGeometry.morphismRestrict`: The restriction of `X ⟶ Y` to `X ∣_ᵤ f ⁻¹ᵁ U ⟶ Y ∣_ᵤ U`.

-/

@[expose] public section

-- Explicit universe annotations were used in this file to improve performance https://github.com/leanprover-community/mathlib4/issues/12737


noncomputable section

open TopologicalSpace CategoryTheory Opposite CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u u₁

variable {C : Type u₁} [Category.{v} C]

section

variable {X : Scheme.{u}} (U : X.Opens)

namespace Scheme.Opens

/-- Open subset of a scheme as a scheme. -/
@[coe]
/-
**AlgebraicGeometry.Scheme.Opens.toScheme** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Opens`。
形式化陈述：toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u}
参数：U : X.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Open subset of a scheme as a scheme.
-/
def toScheme {X : Scheme.{u}} (U : X.Opens) : Scheme.{u} :=
  X.restrict U.isOpenEmbedding
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut X.Opens Scheme := ⟨toScheme⟩

/-- The restriction of a scheme to an open subset. -/
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a scheme to an open subset.
-/
def ι : ↑U ⟶ X := X.ofRestrict _

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_apply (x : U) : U.ι x = x.val := rfl
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsOpenImmersion U.ι := inferInstanceAs (IsOpenImmersion (X.ofRestrict _))
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simps! over] instance : U.toScheme.CanonicallyOver X where
  hom := U.ι
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_comp_over (S : Scheme.{u}) [X.Over S] : U.ι ≫ X ↘ S = U.toScheme ↘ S := rfl
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (U : X.Opens) : U.ι.IsOver X where
/-
**AlgebraicGeometry.Scheme.Opens.toScheme_carrier** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.Opens`。
形式化陈述：toScheme_carrier : (U : Type u) = (U : Set X)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toScheme_carrier : (U : Type u) = (U : Set X) := rfl
/-
**AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_obj** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V)
参数：V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toScheme_presheaf_obj (V) : Γ(U, V) = Γ(X, U.ι ''ᵁ V) := rfl
/-
**AlgebraicGeometry.Scheme.Opens.forall_toScheme** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.Opens`。
形式化陈述：forall_toScheme {U : X.Opens} {P : U.toScheme -> Prop} : (forall x, P x) ↔
 forall (x : X) (hx : x in U), P ⟨x, hx⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.forall`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∀ (x : { a // p a }), q x) ↔ ∀ (a : α) (b : p a), q ⟨a, b⟩
-/
lemma forall_toScheme {U : X.Opens} {P : U.toScheme → Prop} :
    (∀ x, P x) ↔ ∀ (x : X) (hx : x ∈ U), P ⟨x, hx⟩ := Subtype.forall
/-
**AlgebraicGeometry.Scheme.Opens.exists_toScheme** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.Opens`。
形式化陈述：exists_toScheme {U : X.Opens} {P : U.toScheme -> Prop} : (exists x, P x) ↔
 exists (x : X) (hx : x in U), P ⟨x, hx⟩
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
-/
lemma exists_toScheme {U : X.Opens} {P : U.toScheme → Prop} :
    (∃ x, P x) ↔ ∃ (x : X) (hx : x ∈ U), P ⟨x, hx⟩ := Subtype.exists

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_map** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：toScheme_presheaf_map {V W} (i : V ⟶ W) : U.toScheme.presheaf.map i = X.pr
esheaf.map (U.ι.opensFunctor.map i.unop).op
参数：i : V ⟶ W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toScheme_presheaf_map {V W} (i : V ⟶ W) :
    U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFunctor.map i.unop).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_app (V) : U.ι.app V = X.presheaf.map
    (homOfLE (x := U.ι ''ᵁ U.ι ⁻¹ᵁ V) (Set.image_preimage_subset _ _)).op :=
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_appTop :
    U.ι.appTop = X.presheaf.map (homOfLE (x := U.ι ''ᵁ ⊤) le_top).op :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_appLE (V W e) :
    U.ι.appLE V W e =
      X.presheaf.map (homOfLE (x := U.ι ''ᵁ W) (Set.image_subset_iff.mpr ‹_›)).op := by
  simp only [Hom.appLE, ι_app, toScheme_presheaf_map, Quiver.Hom.unop_op,
    Hom.opensFunctor_map_homOfLE, ← Functor.map_comp]
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_appIso (V) : U.ι.appIso V = Iso.refl _ :=
  X.ofRestrict_appIso _ _

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.opensRange_** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma opensRange_ι : U.ι.opensRange = U :=
  Opens.ext Subtype.range_val

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.range_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma range_ι : Set.range U.ι = U :=
  Subtype.range_val
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_image_top : U.ι ''ᵁ ⊤ = U :=
  U.isOpenEmbedding_obj_top
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_image_le (W : U.toScheme.Opens) : U.ι ''ᵁ W ≤ U := by
  simp_rw [← U.ι_image_top]
  exact U.ι.image_mono le_top

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_preimage_self : U.ι ⁻¹ᵁ U = ⊤ :=
  Opens.inclusion'_map_eq_top _

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.mem_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry.Scheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_ι_image_iff {x : U} {V : Opens U} : (x : X) ∈ U.ι ''ᵁ V ↔ x ∈ V :=
  U.ι.apply_mem_image_iff

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (U.ι.appLE U ⊤ U.ι_preimage_self.ge) := by
  simp only [ι, ofRestrict_appLE]
  change IsIso (X.presheaf.map (eqToIso U.ι_image_top).hom.op)
  infer_instance
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.S
cheme.Opens`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_app_self : U.ι.app U = X.presheaf.map (eqToHom (X := U.ι ''ᵁ _) (by simp)).op := rfl
/-
**AlgebraicGeometry.Scheme.Opens.eq_presheaf_map_eqToHom** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：eq_presheaf_map_eqToHom {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W) : X.pr
esheaf.map (eqToHom e).op = U.toScheme.presheaf.map (eqToHom <| U.isOpenEmbeddin
g.functor_obj_injective e).op
参数：e : U.ι ''ᵁ V = U.ι ''ᵁ W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
lemma eq_presheaf_map_eqToHom {V W : Opens U} (e : U.ι ''ᵁ V = U.ι ''ᵁ W) :
    X.presheaf.map (eqToHom e).op =
      U.toScheme.presheaf.map (eqToHom <| U.isOpenEmbedding.functor_obj_injective e).op := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Opens`。
形式化陈述：nonempty_iff : Nonempty U.toScheme ↔ (U : Set X).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma nonempty_iff : Nonempty U.toScheme ↔ (U : Set X).Nonempty := by
  simp only [toScheme_carrier, SetLike.coe_sort_coe, nonempty_subtype]
  rfl

attribute [-simp] eqToHom_op in
/-- The global sections of the restriction is isomorphic to the sections on the open set. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.Opens.topIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Opens`。
形式化陈述：topIso : Γ(U, ⊤) ≅ Γ(X, U)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
The global sections of the restriction is isomorphic to the sections on the open
 set.
-/
def topIso : Γ(U, ⊤) ≅ Γ(X, U) :=
  X.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

/-- The stalks of an open subscheme are isomorphic to the stalks of the original scheme. -/
/-
**AlgebraicGeometry.Scheme.Opens.stalkIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Opens`。
形式化陈述：stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) : U.toScheme.presheaf.stal
k x ≅ X.presheaf.stalk x.1
参数：U : X.Opens；x : U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalks of an open subscheme are isomorphic to the stalks of the original sch
eme.
-/
def stalkIso {X : Scheme.{u}} (U : X.Opens) (x : U) :
    U.toScheme.presheaf.stalk x ≅ X.presheaf.stalk x.1 :=
  X.restrictStalkIso (Opens.isOpenEmbedding _) _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.germ_stalkIso_hom** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Opens`。
形式化陈述：germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens) {V : U.toScheme.Opens} (x
 : U) (hx : x in V) : U.toScheme.presheaf.germ V x hx ≫ (U.stalkIso x).hom = X.p
resheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩
参数：U : X.Opens；x : U；hx : x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ`：restrict
StalkIso_hom_eq_germ {U : TopCat.{v}} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶
 (X : TopCat.{v})} (h : IsOpenEmbedding f) (V : Open…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
lemma germ_stalkIso_hom {X : Scheme.{u}} (U : X.Opens)
    {V : U.toScheme.Opens} (x : U) (hx : x ∈ V) :
      U.toScheme.presheaf.germ V x hx ≫ (U.stalkIso x).hom =
        X.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ :=
    PresheafedSpace.restrictStalkIso_hom_eq_germ _ U.isOpenEmbedding _ _ _

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Opens.germ_stalkIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.Scheme.Opens`。
形式化陈述：germ_stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x
 : U) (hx : x in V) : X.presheaf.germ (U.ι ''ᵁ V) x ⟨x, hx, rfl⟩ ≫ (U.stalkIso x
).inv = U.toScheme.presheaf.germ V x hx
参数：U : X.Opens；V : U.toScheme.Opens；x : U；hx : x in V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ`：restrict
StalkIso_inv_eq_germ {U : TopCat.{v}} (X : PresheafedSpace.{_, _, v} C) {f : U ⟶
 (X : TopCat.{v})} (h : IsOpenEmbedding f) (V : Open…
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
-/
lemma germ_stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (V : U.toScheme.Opens) (x : U)
    (hx : x ∈ V) : X.presheaf.germ (U.ι ''ᵁ V) x ⟨x, hx, rfl⟩ ≫
      (U.stalkIso x).inv = U.toScheme.presheaf.germ V x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace U.isOpenEmbedding V x hx

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Opens.stalkIso_inv** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Opens`。
形式化陈述：stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (x : U) : (U.stalkIso x).inv =
 U.ι.stalkMap x
参数：U : X.Opens；x : U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Iso.inv_comp_eq`：inv_comp_eq (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : α.inv ≫ f = g ↔ f = α.hom ≫ g
· 使用定理 `TopCat.Presheaf.stalk_hom_ext`：stalk_hom_ext (F : X.Presheaf C) {x} {Y :
 C} {f₁ f₂ : F.stalk x ⟶ Y} (ih : forall (U : Opens X) (hxU : x in U), F.germ U 
x hxU ≫ f₁ = F.germ…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.Opens.germ_stalkIso_hom_assoc`：∀ {X : Algebraic
Geometry.Scheme} (U : X.Opens) {V : (↑U).Opens} (x : ↥U) (hx : x ∈ V) {Z : CommR
ingCat}   (h : X.presheaf.stalk ↑x ⟶ Z),   C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `TopCat.Presheaf.germ_res`：germ_res (F : X.Presheaf C) {U V : Opens X} (i
 : U ⟶ V) (x : X) (hx : x in U) : F.map i.op ≫ F.germ U x hx = F.germ V x (i.le 
hx)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.germ_stalkMap`：germ_stalkMap (U : Y.Opens) 
(x : X) (hx : f x in U) : Y.presheaf.germ U (f x) hx ≫ f.stalkMap x = f.app U ≫ 
X.presheaf.germ (f ⁻¹ᵁ U) x hx
-/
lemma stalkIso_inv {X : Scheme.{u}} (U : X.Opens) (x : U) :
    (U.stalkIso x).inv = U.ι.stalkMap x := by
  rw [← Category.comp_id (U.stalkIso x).inv, Iso.inv_comp_eq]
  apply TopCat.Presheaf.stalk_hom_ext
  intro W hxW
  simp only [Category.comp_id, U.germ_stalkIso_hom_assoc]
  convert! (Scheme.Hom.germ_stalkMap U.ι (U.ι ''ᵁ W) x ⟨_, hxW, rfl⟩).symm
  refine (U.toScheme.presheaf.germ_res (homOfLE ?_) _ _).symm
  exact (Set.preimage_image_eq _ Subtype.val_injective).le

end Scheme.Opens

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps! I₀ X f]
/-
**AlgebraicGeometry.Scheme.openCoverOfIsOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebraicGeometry.Scheme`。
形式化陈述：{s : Type u_1} → (X : AlgebraicGeometry.Scheme) → (U : s → X.Opens) → Topo
logicalSpace.IsOpenCover U → X.OpenCover
参数：X : AlgebraicGeometry.Scheme；U : s → X.Opens。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X
.open_cover`.
-/
def Scheme.openCoverOfIsOpenCover {s : Type*} (X : Scheme.{u}) (U : s → X.Opens)
    (hU : IsOpenCover U) : X.OpenCover where
  I₀ := s
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    have hx : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : X.Opens) by trivial
    rw [Opens.mem_iSup] at hx
    obtain ⟨i, hi⟩ := hx
    use i
    simpa

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- The open sets of an open subscheme corresponds to the open sets containing in the subset. -/
@[simps!]
/-
**AlgebraicGeometry.opensRestrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry`。
形式化陈述：opensRestrict : Scheme.Opens U ≃ { V : X.Opens // V <= U }
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
The open sets of an open subscheme corresponds to the open sets containing in th
e subset.
-/
def opensRestrict :
    Scheme.Opens U ≃ { V : X.Opens // V ≤ U } :=
  (IsOpenImmersion.opensEquiv (U.ι)).trans (Equiv.subtypeEquivProp (by simp))
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance ΓRestrictAlgebra {X : Scheme.{u}} (U : X.Opens) :
    Algebra Γ(X, ⊤) Γ(U, ⊤) :=
  U.ι.appTop.hom.toAlgebra

set_option backward.isDefEq.respectTransparency false in
/-- A variant where `r` is first mapped into `Γ(X, U)` before taking the basic open. -/
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant where `r` is first mapped into `Γ(X, U)` before taking the basic open.
-/
lemma Scheme.Opens.ι_image_basicOpen' (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen
      (X.presheaf.map (eqToHom U.ι_image_top.symm).op r) := by
  refine (Scheme.image_basicOpen (X.ofRestrict U.isOpenEmbedding) r).trans ?_
  rw [← Scheme.basicOpen_res_eq _ _ (eqToHom U.isOpenEmbedding_obj_top).op]
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp, ← op_comp, eqToHom_trans,
    eqToHom_refl, op_id]
  congr
  exact (PresheafedSpace.IsOpenImmersion.ofRestrict_invApp _ _ _).trans
    (CategoryTheory.Functor.map_id _ _).symm

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.ι_image_basicOpen (r : Γ(U, ⊤)) :
    U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen r := by
  rw [Scheme.Opens.ι_image_basicOpen', Scheme.basicOpen_res_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Opens.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.ι_image_basicOpen_topIso_inv (r : Γ(X, U)) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.topIso.inv r) = X.basicOpen r := by
  simp only [Scheme.Opens.toScheme_presheaf_obj]
  rw [ι_image_basicOpen', basicOpen_res_eq, topIso_inv, basicOpen_res_eq X]

@[simp]
/-
**AlgebraicGeometry.Scheme.Opens.mem_basicOpen_toScheme** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens} {V : (↑U).Opens} {r : ↑((↑U
).presheaf.obj (Opposite.op V))} {x : ↥U},   x ∈ (↑U).basicOpen r ↔ ↑x ∈ X.basic
Open r
参数：↑U；(↑U).presheaf.obj (Opposite.op V)；↑U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res_eq`：basicOpen_res_eq (i : op U ⟶ 
op V) [IsIso i] : X.basicOpen (X.presheaf.map i f) = X.basicOpen f
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Eq.to_iff`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.preimage_basicOpen`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) {U : Y.Opens} (r : ↑(Y.presheaf.obj (Opposite.op U))),  
 (TopologicalSpace.Opens.map f.base).…
-/
lemma Scheme.Opens.mem_basicOpen_toScheme {U : X.Opens} {V : Scheme.Opens U} {r : Γ(U, V)} {x : U} :
    x ∈ U.toScheme.basicOpen r ↔ (x : X) ∈ X.basicOpen r := by
  rw [← U.toScheme.basicOpen_res_eq _ (eqToHom (U.ι.preimage_image_eq V)).op]
  exact congr(x ∈ $(U.ι.preimage_basicOpen r)).to_iff.symm

/-- If `U ≤ V`, then `U` is also a subscheme of `V`. -/
protected noncomputable
/-
**AlgebraicGeometry.Scheme.homOfLE** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → {U V : X.Opens} → U ≤ V → (↑U ⟶ ↑V)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
def Scheme.homOfLE (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : (U : Scheme.{u}) ⟶ V :=
  IsOpenImmersion.lift V.ι U.ι (by simpa using e)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.homOfLE_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.homOfLE_ι (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) :
    X.homOfLE e ≫ V.ι = U.ι :=
  IsOpenImmersion.lift_fac _ _ _
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U V : X.Opens} (h : U ≤ V) : (X.homOfLE h).IsOver X where

@[simp]
/-
**AlgebraicGeometry.Scheme.homOfLE_rfl** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (U : X.Opens), X.homOfLE ⋯ = CategoryTheo
ry.CategoryStruct.id ↑U
参数：X : AlgebraicGeometry.Scheme；U : X.Opens。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma Scheme.homOfLE_rfl (X : Scheme.{u}) (U : X.Opens) : X.homOfLE (refl U) = 𝟙 _ := by
  rw [← cancel_mono U.ι, Scheme.homOfLE_ι, Category.id_comp]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.homOfLE_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ 
W),   CategoryTheory.CategoryStruct.comp (X.homOfLE e₁) (X.homOfLE e₂) = X.homOf
LE ⋯
参数：X : AlgebraicGeometry.Scheme；e₁ : U ≤ V；e₂ : V ≤ W；X.homOfLE e₁；X.homOfLE e₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
-/
lemma Scheme.homOfLE_homOfLE (X : Scheme.{u}) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) :
    X.homOfLE e₁ ≫ X.homOfLE e₂ = X.homOfLE (e₁.trans e₂) := by
  rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
/-
**AlgebraicGeometry.Scheme.homOfLE_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V),   (X.homOfLE
 e).base = (TopologicalSpace.Opens.toTopCat ↑X.toPresheafedSpace).map (CategoryT
heory.homOfLE e)
参数：e : U ≤ V；X.homOfLE e；TopologicalSpace.Opens.toTopCat ↑X.toPresheafedSpace；Ca
tegoryTheory.homOfLE e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TopCat.ext`：ext {X Y : TopCat.{u}} {f g : X ⟶ Y} (w : forall x : X, f x 
= g x) : f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
-/
theorem Scheme.homOfLE_base {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).base = (Opens.toTopCat _).map (homOfLE e) := by
  ext a; refine Subtype.ext ?_ -- Porting note: `ext` did not pick up `Subtype.ext`
  exact congr($(X.homOfLE_ι e) a)
/-
**AlgebraicGeometry.Scheme.homOfLE_apply'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (x : ↥X) (hx 
: x ∈ U), (X.homOfLE e) ⟨x, hx⟩ = ⟨x, ⋯⟩
参数：e : U ≤ V；x : ↥X；hx : x ∈ U；X.homOfLE e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_base`：∀ {X : AlgebraicGeometry.Scheme} 
{U V : X.Opens} (e : U ≤ V),   (X.homOfLE e).base = (TopologicalSpace.Opens.toTo
pCat ↑X.toPresheafedSpace).…
-/
theorem Scheme.homOfLE_apply' {U V : X.Opens} (e : U ≤ V) (x : X) (hx : x ∈ U) :
    X.homOfLE e ⟨x, hx⟩ = ⟨x, e hx⟩ := by
  rw [homOfLE_base]
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.homOfLE_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (x : ↥U), ↑((
X.homOfLE e) x) = ↑x
参数：e : U ≤ V；x : ↥U；(X.homOfLE e) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_apply'`：∀ {X : AlgebraicGeometry.Scheme
} {U V : X.Opens} (e : U ≤ V) (x : ↥X) (hx : x ∈ U), (X.homOfLE e) ⟨x, hx⟩ = ⟨x,
 ⋯⟩
-/
theorem Scheme.homOfLE_apply {U V : X.Opens} (e : U ≤ V) (x : U) :
    (X.homOfLE e x).1 = x := by
  rw [Scheme.homOfLE_apply']

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Scheme.ι_image_homOfLE_eq_ι_image_inf {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W = V.ι ''ᵁ W ⊓ U := by
  ext x
  constructor
  · rintro ⟨⟨y, hyU⟩, hyW, rfl⟩
    exact ⟨⟨⟨y, e hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩, hyU⟩
  · rintro ⟨⟨y, hyW, rfl⟩, hyU⟩
    exact ⟨⟨y.1, hyU⟩, by simpa [homOfLE_apply'] using hyW, rfl⟩
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Scheme.ι_image_homOfLE_le_ι_image {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    U.ι ''ᵁ X.homOfLE e ⁻¹ᵁ W ≤ V.ι ''ᵁ W := by
  simp [Scheme.ι_image_homOfLE_eq_ι_image_inf]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.homOfLE_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Ope
ns),   AlgebraicGeometry.Scheme.Hom.app (X.homOfLE e) W = X.presheaf.map (Catego
ryTheory.homOfLE ⋯).op
参数：e : U ≤ V；W : (↑V).Opens；X.homOfLE e；CategoryTheory.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
· 使用定理 `TopologicalSpace.Opens.map_functor_eq`：map_functor_eq {X : TopCat.{u}} {
U : Opens X} (V : Opens U) : ((Opens.map U.inclusion').obj <| U.isOpenEmbedding.
functor.obj V) = V
· 使用引理 `AlgebraicGeometry.Scheme.Hom.naturality`：naturality (i : op U' ⟶ op U) :
 Y.presheaf.map i ≫ f.app U = f.app U' ≫ X.presheaf.map ((Opens.map f.base).map 
i.unop).op
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `CategoryTheory.instIsIsoEqToHom`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {X Y : C} (h : X = Y),   CategoryTheory.IsIso (CategoryTheo
ry.eqToHom h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Functor.map_inv`：map_inv (F : C ⥤ D) {X Y : C} (f : X ⟶ Y
) [IsIso f] : F.map (inv f) = inv (F.map f)
· 使用定理 `CategoryTheory.IsIso.eq_comp_inv`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] {X Y Z : C} (α : Y ⟶ X) [inst_1 : CategoryTheory.IsIso α]   {
f : Z ⟶ X} {g : Z ⟶ Y}…
-/
theorem Scheme.homOfLE_app {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    (X.homOfLE e).app W = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e W).op := by
  have e₁ := Scheme.Hom.congr_app (X.homOfLE_ι e) (V.ι ''ᵁ W)
  have : V.ι ⁻¹ᵁ V.ι ''ᵁ W = W := W.map_functor_eq (U := V)
  have e₂ := (X.homOfLE e).naturality (eqToIso this).hom.op
  have e₃ := e₂.symm.trans e₁
  dsimp at e₃ ⊢
  rw [← IsIso.eq_comp_inv, ← Functor.map_inv, ← Functor.map_comp] at e₃
  rw [e₃, ← Functor.map_comp]
  congr 1

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.Scheme.homOfLE_appLE** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Ope
ns) (W' : (↑U).Opens)   (e' : W' ≤ (TopologicalSpace.Opens.map (X.homOfLE e).bas
e).obj W),   AlgebraicGeometry.Scheme.Hom.appLE (X.homOfLE e) W W' e' = X.preshe
af.map (CategoryTheory.homOfLE ⋯).op
参数：e : U ≤ V；W : (↑V).Opens；W' : (↑U).Opens；e' : W' ≤ (TopologicalSpace.Opens.ma
p (X.homOfLE e).base).obj W；X.homOfLE e；CategoryTheory.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_app`：∀ {X : AlgebraicGeometry.Scheme} {
U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   AlgebraicGeometry.Scheme.Hom.app 
(X.homOfLE e) W = X.preshe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Scheme.homOfLE_appLE {U V : X.Opens} (e : U ≤ V) (W : Opens V) (W' : Opens U) (e') :
    (X.homOfLE e).appLE W W' e' = X.presheaf.map
      (homOfLE ((U.ι.image_mono e').trans (Scheme.ι_image_homOfLE_le_ι_image ..))).op := by
  simp [Scheme.Hom.appLE, Scheme.homOfLE_app, ← Functor.map_comp, ← op_comp]
/-
**AlgebraicGeometry.Scheme.homOfLE_appTop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V),   AlgebraicG
eometry.Scheme.Hom.appTop (X.homOfLE e) = X.presheaf.map (CategoryTheory.homOfLE
 ⋯).op
参数：e : U ≤ V；X.homOfLE e；CategoryTheory.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_app`：∀ {X : AlgebraicGeometry.Scheme} {
U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   AlgebraicGeometry.Scheme.Hom.app 
(X.homOfLE e) W = X.preshe…
-/
theorem Scheme.homOfLE_appTop {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).appTop = X.presheaf.map (homOfLE <| X.ι_image_homOfLE_le_ι_image e ⊤).op :=
  homOfLE_app ..
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Scheme.{u}) {U V : X.Opens} (e : U ≤ V) : IsOpenImmersion (X.homOfLE e) := by
  delta Scheme.homOfLE
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.appIso_homOfLE_inv** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (h : U ≤ V) (W : (↑U).Ope
ns),   (AlgebraicGeometry.Scheme.Hom.appIso (X.homOfLE h) W).inv = X.presheaf.ma
p (CategoryTheory.homOfLE ⋯).op
参数：h : U ≤ V；W : (↑U).Opens；AlgebraicGeometry.Scheme.Hom.appIso (X.homOfLE h) W；
CategoryTheory.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.hom_comp_eq_id`：hom_comp_eq_id (α : X ≅ Y) {f : Y ⟶ X
} : α.hom ≫ f = 𝟙 X ↔ f = α.inv
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appIso_hom`：appIso_hom (U) : (f.appIso U).h
om = f.app (f ''ᵁ U) ≫ X.presheaf.map (eqToHom (preimage_image_eq f U).symm).op
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_app`：∀ {X : AlgebraicGeometry.Scheme} {
U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   AlgebraicGeometry.Scheme.Hom.app 
(X.homOfLE e) W = X.preshe…
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
lemma Scheme.Hom.appIso_homOfLE_inv {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V)
    (W : (U : Scheme.{u}).Opens) :
    ((X.homOfLE h).appIso W).inv =
      X.presheaf.map (.op <| homOfLE <| by
        suffices V.ι ''ᵁ _ ≤ U.ι ''ᵁ W by simpa
        simp [← Scheme.Hom.comp_image]) := by
  rw [eq_comm, ← Iso.hom_comp_eq_id]
  dsimp
  simp only [appIso_hom, homOfLE_app, homOfLE_leOfHom, eqToHom_op, Opens.toScheme_presheaf_map,
    eqToHom_unop, ← X.presheaf.map_comp, Category.assoc, ← X.presheaf.map_id]
  rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.opensRange_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V),   AlgebraicG
eometry.Scheme.Hom.opensRange (X.homOfLE e) = (TopologicalSpace.Opens.map V.ι.ba
se).obj U
参数：e : U ≤ V；X.homOfLE e；TopologicalSpace.Opens.map V.ι.base。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_injective`：image_injective : Function
.Injective (f ''ᵁ ·)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensRange.congr_simp`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenImme
rsion f],   AlgebraicGeometry.Scheme.Hom…
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.opensRange_homOfLE {U V : X.Opens} (e : U ≤ V) :
    (X.homOfLE e).opensRange = V.ι ⁻¹ᵁ U :=
  V.ι.image_injective (by simp [← Hom.opensRange_comp, Hom.image_preimage_eq_opensRange_inf, e])

/-- The open cover of `⋃ Vᵢ` by `Vᵢ`. -/
/-
**AlgebraicGeometry.Scheme.Opens.iSupOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme.Opens`。
形式化陈述：{J : Type u_1} → {X : AlgebraicGeometry.Scheme} → (U : J → X.Opens) → (↑(⨆
 i, U i)).OpenCover
参数：U : J → X.Opens；↑(⨆ i, U i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The open cover of `⋃ Vᵢ` by `Vᵢ`.
-/
def Scheme.Opens.iSupOpenCover {J : Type*} {X : Scheme} (U : J → X.Opens) :
    (⨆ i, U i).toScheme.OpenCover where
  I₀ := J
  X i := U i
  f j := X.homOfLE (le_iSup _ _)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp x.2
    use i, ⟨x.1, hi⟩
    apply Subtype.ext
    simp

set_option backward.defeqAttrib.useBackward true in
variable (X) in
/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps! obj_left obj_hom map_left]
/-
**AlgebraicGeometry.Scheme.restrictFunctor** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → CategoryTheory.Functor X.Opens (CategoryT
heory.Over X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking open subsets of `X` to open subschemes of `X`.
-/
def Scheme.restrictFunctor : X.Opens ⥤ Over X where
  obj U := Over.mk U.ι
  map {U V} i := Over.homMk (X.homOfLE i.le) (by simp)
  map_id U := by
    ext1
    exact Scheme.homOfLE_rfl _ _
  map_comp {U V W} i j := by
    ext1
    exact (X.homOfLE_homOfLE i.le j.le).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps!]
/-
**AlgebraicGeometry.Scheme.restrictFunctor** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → CategoryTheory.Functor X.Opens (CategoryT
heory.Over X)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf.
-/
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).isOpenEmbedding_obj_top).symm.op :))
    (by
      intro U V i
      dsimp
      rw [X.homOfLE_appTop, ← Functor.map_comp, ← Functor.map_comp]
      congr 1)

/-- `X ∣_ U ∣_ V` is isomorphic to `X ∣_ V ∣_ U` -/
noncomputable
/-
**AlgebraicGeometry.Scheme.restrictRestrictComm** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) →   (U V : X.Opens) → ↑((TopologicalSpace.O
pens.map U.ι.base).obj V) ≅ ↑((TopologicalSpace.Opens.map V.ι.base).obj U)
参数：TopologicalSpace.Opens.map U.ι.base；TopologicalSpace.Opens.map V.ι.base。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Scheme.restrictRestrictComm (X : Scheme.{u}) (U V : X.Opens) :
    (U.ι ⁻¹ᵁ V).toScheme ≅ V.ι ⁻¹ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ U.ι) (Opens.ι _ ≫ V.ι) <| by
    simp only [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Opens.range_ι, Opens.map_coe,
      Set.image_preimage_eq_inter_range, Set.inter_comm (U : Set X)]

/-- If `f : X ⟶ Y` is an open immersion, then for any `U : X.Opens`,
we have the isomorphism `U ≅ f ''ᵁ U`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.Hom.isoImage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) →     [inst : AlgebraicGe
ometry.IsOpenImmersion f] →       (U : X.Opens) → ↑U ≅ ↑((AlgebraicGeometry.Sche
me.Hom.opensFunctor f).obj U)
参数：f : X ⟶ Y；U : X.Opens；(AlgebraicGeometry.Scheme.Hom.opensFunctor f).obj U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Scheme.Hom.isoImage
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    U.toScheme ≅ f ''ᵁ U :=
  IsOpenImmersion.isoOfRangeEq (Opens.ι _ ≫ f) (Opens.ι _) (by simp [Set.range_comp])

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.isoImage_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.isoImage_hom_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).hom ≫ (f ''ᵁ U).ι = U.ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.isoImage_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.isoImage_inv_ι
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : X.Opens) :
    (f.isoImage U).inv ≫ U.ι ≫ f = (f ''ᵁ U).ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.isoImage_hom_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.I
sOpenImmersion f] (U V : X.Opens) (e : U ≤ V),   CategoryTheory.CategoryStruct.c
omp (AlgebraicGeometry.Scheme.Hom.isoImage f U).hom (Y.homOfLE ⋯) =     Category
Theory.CategoryStruct.comp (X.homOfLE e) (AlgebraicGeometry.Scheme.Hom.isoImage 
f V).hom
参数：f : X ⟶ Y；U V : X.Opens；e : U ≤ V；AlgebraicGeometry.Scheme.Hom.isoImage f U；Y
.homOfLE ⋯；X.homOfLE e；AlgebraicGeometry.Scheme.Hom.isoImage f V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens), 
  CategoryTheory.CategoryStruct.c…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι_assoc`：∀ (X : AlgebraicGeometry.Schem
e) {U V : X.Opens} (e : U ≤ V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),   Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.isoImage_hom_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U ≤ V) :
    (f.isoImage U).hom ≫ Y.homOfLE (f.image_mono e) = X.homOfLE e ≫ (f.isoImage V).hom := by
  simp [← cancel_mono (f ''ᵁ V).ι]

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.isoImage_inv_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.I
sOpenImmersion f] (U V : X.Opens) (e : U ≤ V),   CategoryTheory.CategoryStruct.c
omp (AlgebraicGeometry.Scheme.Hom.isoImage f U).inv (X.homOfLE e) =     Category
Theory.CategoryStruct.comp (Y.homOfLE ⋯) (AlgebraicGeometry.Scheme.Hom.isoImage 
f V).inv
参数：f : X ⟶ Y；U V : X.Opens；e : U ≤ V；AlgebraicGeometry.Scheme.Hom.isoImage f U；X
.homOfLE e；Y.homOfLE ⋯；AlgebraicGeometry.Scheme.Hom.isoImage f V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_homOfLE`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U V : X.
Opens) (e : U ≤ V),   CategoryTheory.Ca…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.isoImage_inv_homOfLE
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U V : Opens X) (e : U ≤ V) :
    (f.isoImage U).inv ≫ X.homOfLE e = Y.homOfLE (f.image_mono e) ≫ (f.isoImage V).inv := by
  simp [← cancel_mono (f.isoImage V).hom, ← f.isoImage_hom_homOfLE]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.isoImage_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.isoImage_ι_inv_ι {X : Scheme.{u}} (U : Opens X) (V : Opens U) :
    (U.ι.isoImage V).inv ≫ V.ι = X.homOfLE (U.ι_image_le V) := by
  simp [← cancel_mono U.ι]

/-- If `f : X ⟶ Y` is an open immersion, then `X` is isomorphic to its image in `Y`. -/
/-
**AlgebraicGeometry.Scheme.Hom.isoOpensRange** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → [inst : AlgebraicGeomet
ry.IsOpenImmersion f] → X ≅ ↑(AlgebraicGeometry.Scheme.Hom.opensRange f)
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.opensRange f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` is an open immersion, then `X` is isomorphic to its image in `Y`.
-/
def Scheme.Hom.isoOpensRange {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ f.opensRange :=
  IsOpenImmersion.isoOfRangeEq f f.opensRange.ι (by simp)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.isoOpensRange_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.hom ≫ f.opensRange.ι = f := by
  simp [isoOpensRange]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.I
sOpenImmersion f],   CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Schem
e.Hom.isoOpensRange f).inv f =     (AlgebraicGeometry.Scheme.Hom.opensRange f).ι
参数：f : X ⟶ Y；AlgebraicGeometry.Scheme.Hom.isoOpensRange f；AlgebraicGeometry.Sche
me.Hom.opensRange f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.isoOpensRange_inv_comp {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    f.isoOpensRange.inv ≫ f = f.opensRange.ι := by
  simp [isoOpensRange]

/-- `(⊤ : X.Opens)` as a scheme is isomorphic to `X`. -/
@[simps hom]
/-
**AlgebraicGeometry.Scheme.topIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.S
cheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → ↑⊤ ≅ X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`(⊤ : X.Opens)` as a scheme is isomorphic to `X`.
-/
def Scheme.topIso (X : Scheme) : ↑(⊤ : X.Opens) ≅ X where
  hom := Scheme.Opens.ι _
  inv := ⟨X.restrictTopIso.inv⟩
  hom_inv_id := Hom.ext' X.restrictTopIso.hom_inv_id
  inv_hom_id := Hom.ext' X.restrictTopIso.inv_hom_id

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.toIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.toIso_inv_ι (X : Scheme.{u}) : X.topIso.inv ≫ Opens.ι _ = 𝟙 _ :=
  X.topIso.inv_hom_id

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.ι_toIso_inv (X : Scheme.{u}) : Opens.ι _ ≫ X.topIso.inv = 𝟙 _ :=
  X.topIso.hom_inv_id

/-- If `U = V`, then `X ∣_ U` is isomorphic to `X ∣_ V`. -/
noncomputable
/-
**AlgebraicGeometry.Scheme.isoOfEq** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.
Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → {U V : X.Opens} → U = V → (↑U ≅ ↑V)
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
def Scheme.isoOfEq (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (U : Scheme.{u}) ≅ V :=
  IsOpenImmersion.isoOfRangeEq U.ι V.ι (by rw [e])

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.isoOfEq_hom_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.isoOfEq_hom_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom ≫ V.ι = U.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.isoOfEq_inv_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.isoOfEq_inv_ι (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv ≫ U.ι = V.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _
/-
**AlgebraicGeometry.Scheme.isoOfEq_hom** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) {U V : X.Opens} (e : U = V), (X.isoOfEq e
).hom = X.homOfLE ⋯
参数：X : AlgebraicGeometry.Scheme；e : U = V；X.isoOfEq e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.isoOfEq_hom (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).hom = X.homOfLE e.le := rfl
/-
**AlgebraicGeometry.Scheme.isoOfEq_inv** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) {U V : X.Opens} (e : U = V), (X.isoOfEq e
).inv = X.homOfLE ⋯
参数：X : AlgebraicGeometry.Scheme；e : U = V；X.isoOfEq e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.isoOfEq_inv (X : Scheme.{u}) {U V : X.Opens} (e : U = V) :
    (X.isoOfEq e).inv = X.homOfLE e.ge := rfl

@[simp]
/-
**AlgebraicGeometry.Scheme.isoOfEq_rfl** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) (U : X.Opens), X.isoOfEq ⋯ = CategoryTheo
ry.Iso.refl ↑U
参数：X : AlgebraicGeometry.Scheme；U : X.Opens。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.ext`：ext ⦃α β : X ≅ Y⦄ (w : α.hom = β.hom) : α = β
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι`：∀ (X : AlgebraicGeometry.Scheme)
 {U V : X.Opens} (e : U = V),   CategoryTheory.CategoryStruct.comp (X.isoOfEq e)
.hom V.ι = U.ι
· 使用定理 `CategoryTheory.Iso.refl_hom`：∀ {C : Type u} [inst : CategoryTheory.Categ
ory.{v, u} C] (X : C),   (CategoryTheory.Iso.refl X).hom = CategoryTheory.Catego
ryStruct.id X
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma Scheme.isoOfEq_rfl (X : Scheme.{u}) (U : X.Opens) : X.isoOfEq (refl U) = Iso.refl _ := by
  ext1
  rw [← cancel_mono U.ι, Scheme.isoOfEq_hom_ι, Iso.refl_hom, Category.id_comp]

end

/-- The restriction of an isomorphism onto an open set. -/
/-
**AlgebraicGeometry.Scheme.Hom.preimageIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} →   (f : X ⟶ Y) → [CategoryTheory.IsIso f
] → (U : Y.Opens) → ↑((TopologicalSpace.Opens.map f.base).obj U) ≅ ↑U
参数：f : X ⟶ Y；U : Y.Opens；(TopologicalSpace.Opens.map f.base).obj U。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
The restriction of an isomorphism onto an open set.
-/
noncomputable def Scheme.Hom.preimageIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ≅ U := by
  apply IsOpenImmersion.isoOfRangeEq (f := (f ⁻¹ᵁ U).ι ≫ f) U.ι _
  dsimp
  rw [Set.range_comp, Opens.range_ι, Opens.range_ι]
  refine @Set.image_preimage_eq _ _ f U.1 f.homeomorph.surjective

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.preimageIso_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.preimageIso_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).hom ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.preimageIso_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Hom.preimageIso_inv_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso (C := Scheme) f]
    (U : Y.Opens) : (f.preimageIso U).inv ≫ (f ⁻¹ᵁ U).ι ≫ f = U.ι :=
  IsOpenImmersion.isoOfRangeEq_inv_fac _ _ _

/-- If `U ≤ V` are opens of `X`, the restriction of `U` to `V` is isomorphic to `U`. -/
/-
**AlgebraicGeometry.Scheme.Opens.isoOfLE** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Scheme.Opens`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → {U V : X.Opens} → U ≤ V → (↑((Topological
Space.Opens.map V.ι.base).obj U) ≅ ↑U)
参数：↑((TopologicalSpace.Opens.map V.ι.base).obj U) ≅ ↑U。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
If `U ≤ V` are opens of `X`, the restriction of `U` to `V` is isomorphic to `U`.
-/
noncomputable def Scheme.Opens.isoOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (V.ι ⁻¹ᵁ U).toScheme ≅ U :=
  IsOpenImmersion.isoOfRangeEq ((V.ι ⁻¹ᵁ U).ι ≫ V.ι) U.ι <| by
    have : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by simpa [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Scheme.Opens.range_ι, Set.range_comp, ← this]
    simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.isoOfLE_hom_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.isoOfLE_hom_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (isoOfLE hUV).hom ≫ U.ι = (V.ι ⁻¹ᵁ U).ι ≫ V.ι := by
  simp [isoOfLE]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Opens.isoOfLE_inv_** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Scheme.Opens.isoOfLE_inv_ι {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) :
    (isoOfLE hUV).inv ≫ (V.ι ⁻¹ᵁ U).ι ≫ V.ι = U.ι := by
  simp [isoOfLE]

set_option backward.isDefEq.respectTransparency.types false in
/-- For `f : R`, `D(f)` as an open subscheme of `Spec R` is isomorphic to `Spec R[1/f]`. -/
/-
**AlgebraicGeometry.basicOpenIsoSpecAway** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) : Scheme.Opens.toScheme
 (X
参数：f : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f : R`, `D(f)` as an open subscheme of `Spec R` is isomorphic to `Spec R[1/
f]`.
-/
def basicOpenIsoSpecAway {R : CommRingCat.{u}} (f : R) :
    Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f) ≅
      Spec (.of <| Localization.Away f) :=
  IsOpenImmersion.isoOfRangeEq (Scheme.Opens.ι _) (Spec.map (CommRingCat.ofHom (algebraMap _ _)))
    (by
      simp only [Scheme.Opens.range_ι]
      exact (PrimeSpectrum.localization_away_comap_range _ _).symm)

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：basicOpenIsoSpecAway_hom_SpecMap {R : CommRingCat.{u}} (f : R) : (basicOpe
nIsoSpecAway f).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) = Scheme.Ope
ns.ι (X
参数：f : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac`：isoOfRangeEq_hom
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basicOpenIsoSpecAway_hom_SpecMap {R : CommRingCat.{u}} (f : R) :
    (basicOpenIsoSpecAway f).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R _)) =
        Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) := by
  simp [basicOpenIsoSpecAway]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/-
**AlgebraicGeometry.basicOpenIsoSpecAway_inv_homOfLE** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry`。
形式化陈述：basicOpenIsoSpecAway_inv_homOfLE {R : CommRingCat.{u}} (f g x : R) (hx : x
 = f * g) : haveI : IsLocalization.Away (f * g) (Localization.Away x)
参数：f g x : R；hx : x = f * g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `IsLocalization.Away.awayToAwayRight_eq`：awayToAwayRight_eq (y : R) [Alge
bra R P] [IsLocalization.Away (x * y) P] (a : R) : awayToAwayRight x y (algebraM
ap R S a) = algebraMap R P a
-/
lemma basicOpenIsoSpecAway_inv_homOfLE {R : CommRingCat.{u}} (f g x : R) (hx : x = f * g) :
    haveI : IsLocalization.Away (f * g) (Localization.Away x) := by rw [hx]; infer_instance
    (basicOpenIsoSpecAway x).inv ≫ (Spec R).homOfLE (by simp [hx, PrimeSpectrum.basicOpen_mul]) =
      Spec.map (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g)) ≫
        (basicOpenIsoSpecAway f).inv := by
  subst hx
  rw [← cancel_mono (Scheme.Opens.ι _)]
  simp only [basicOpenIsoSpecAway, Category.assoc, Scheme.homOfLE_ι,
    IsOpenImmersion.isoOfRangeEq_inv_fac]
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr
  ext x
  exact (IsLocalization.Away.awayToAwayRight_eq f g x (S := Localization.Away f)).symm

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
/-
**AlgebraicGeometry.pullbackRestrictIsoRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
 pullback f U.ι ≅ f ⁻¹ᵁ U
参数：f : X ⟶ Y；U : Y.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f
 ⁻¹ U}`
-/
def pullbackRestrictIsoRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    pullback f U.ι ≅ f ⁻¹ᵁ U := by
  refine IsOpenImmersion.isoOfRangeEq (pullback.fst f _) (Scheme.Opens.ι _) ?_
  simp [IsOpenImmersion.range_pullbackFst]

@[simp, reassoc]
/-
**AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry`。
形式化陈述：pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.
Opens) : (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι
参数：f : X ⟶ Y；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_inv_fac`：isoOfRangeEq_inv
_fac {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImm
ersion g] (e : Set.range f = Set.range g) : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst f _ = (f ⁻¹ᵁ U).ι := by
  delta pullbackRestrictIsoRestrict; simp

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pullbackRestrictIsoRestrict_hom_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (pullbackRestrictIsoRestrict f U).hom ≫ (f ⁻¹ᵁ U).ι = pullback.fst f _ := by
  delta pullbackRestrictIsoRestrict; simp

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
/-
**AlgebraicGeometry.morphismRestrict** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).
toScheme ⟶ U
参数：f : X ⟶ Y；U : Y.Opens。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`.
-/
def morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f ⁻¹ᵁ U).toScheme ⟶ U :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd _ _

/-- the notation for restricting a morphism of scheme to an open subset of the target scheme -/
infixl:85 " ∣_ " => morphismRestrict

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict** 是 Mathlib
 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X
 ⟶ Y) (U : Y.Opens) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.
snd _ _
参数：f : X ⟶ Y；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
-/
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Y.Opens) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd _ _ :=
  Iso.hom_inv_id_assoc _ _

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.morphismRestrict_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem morphismRestrict_ι {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f := by
  delta morphismRestrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]
/-
**AlgebraicGeometry.isPullback_morphismRestrict** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry`。
形式化陈述：isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
 IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f
参数：f : X ⟶ Y；U : Y.Opens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isPullback`：isPullback {U V X Y : Sche
me.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion iU] [
IsOpenImmersion iV] (H : iU ≫ f = …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
-/
theorem isPullback_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    IsPullback (f ∣_ U) (f ⁻¹ᵁ U).ι U.ι f := by
  apply IsOpenImmersion.isPullback <;>
  simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isPullback_opens_inf_le** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：isPullback_opens_inf_le {X : Scheme} {U V W : X.Opens} (hU : U <= W) (hV :
 V <= W) : IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (X.homOfL
E hU) (X.homOfLE hV)
参数：hU : U <= W；hV : V <= W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopologicalSpace.Opens.map_comp_obj`：map_comp_obj (f : X ⟶ Y) (g : Y ⟶ Z
) (U) : (map (f ≫ g)).obj U = (map f).obj ((map g).obj U)
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `TopologicalSpace.Opens.functor_map_eq_inf`：functor_map_eq_inf {X : TopCa
t.{u}} (U V : Opens X) : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion')
.obj V) = V ⊓ U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TopologicalSpace.Opens.isOpenEmbedding`：isOpenEmbedding {X : TopCat.{u}}
 (U : Opens X) : IsOpenEmbedding (inclusion' U)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι`：∀ (X : AlgebraicGeometry.Scheme)
 {U V : X.Opens} (e : U = V),   CategoryTheory.CategoryStruct.comp (X.isoOfEq e)
.hom V.ι = U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens), 
  CategoryTheory.CategoryStruct.c…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_assoc`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   C
ategoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isPullback_opens_inf_le {X : Scheme} {U V W : X.Opens} (hU : U ≤ W) (hV : V ≤ W) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) (X.homOfLE hU) (X.homOfLE hV) := by
  refine (isPullback_morphismRestrict (X.homOfLE hV) (W.ι ⁻¹ᵁ U)).of_iso (V.ι.isoImage _ ≪≫
    X.isoOfEq ?_) (W.ι.isoImage _ ≪≫ X.isoOfEq ?_) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · rw [← TopologicalSpace.Opens.map_comp_obj, ← Scheme.Hom.comp_base, Scheme.homOfLE_ι]
    exact V.functor_map_eq_inf U
  · exact (W.functor_map_eq_inf U).trans (by simpa)
  all_goals { simp [← cancel_mono (Scheme.Opens.ι _)] }

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.isPullback_opens_inf** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：isPullback_opens_inf {X : Scheme} (U V : X.Opens) : IsPullback (X.homOfLE 
inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι
参数：U V : X.Opens。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.IsPullback.of_iso`：of_iso (h : IsPullback fst snd f g) {P
' X' Y' Z' : C} {fst' : P' ⟶ X'} {snd' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'} 
(e₁ : P ≅ P') (e₂ : X …
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `TopologicalSpace.Opens.functor_map_eq_inf`：functor_map_eq_inf {X : TopCa
t.{u}} (U V : Opens X) : U.isOpenEmbedding.functor.obj ((Opens.map U.inclusion')
.obj V) = V ⊓ U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι`：∀ (X : AlgebraicGeometry.Scheme)
 {U V : X.Opens} (e : U = V),   CategoryTheory.CategoryStruct.comp (X.isoOfEq e)
.hom V.ι = U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens), 
  CategoryTheory.CategoryStruct.c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma isPullback_opens_inf {X : Scheme} (U V : X.Opens) :
    IsPullback (X.homOfLE inf_le_left) (X.homOfLE inf_le_right) U.ι V.ι :=
  (isPullback_morphismRestrict V.ι U).of_iso (V.ι.isoImage _ ≪≫ X.isoOfEq
    (V.functor_map_eq_inf U)) (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp [← cancel_mono U.ι])
    (by simp [← cancel_mono V.ι]) (by simp) (by simp)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.morphismRestrict_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _
参数：U : X.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
-/
lemma morphismRestrict_id {X : Scheme.{u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _ := by
  rw [← cancel_mono U.ι, morphismRestrict_ι, Category.comp_id, Category.id_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.morphismRestrict_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Op
ens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U
参数：f : X ⟶ Y；g : Y ⟶ Z；U : Opens Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instFstScheme`：∀ {X Y Z : AlgebraicGeo
metry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [H : AlgebraicGeometry.IsOpenImmersion f],
   AlgebraicGeometry.IsOpenImmersion …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_snd`：pullbackR
ightPullbackFstIso_inv_snd_snd : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.snd _ _ = pullback.snd _ _
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst`：pullbackRestrictI
soRestrict_inv_fst {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (pullbackRestr
ictIsoRestrict f U).inv ≫ pullback.fst f _ …
· 使用定理 `CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_snd_fst`：pullbackR
ightPullbackFstIso_inv_snd_fst : (pullbackRightPullbackFstIso f g f').inv ≫ pull
back.snd _ _ ≫ pullback.fst _ _ = pullback.fst _ _ …
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用定理 `AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst_assoc`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme}
 (h : X ⟶ Z),   CategoryTheory.CategoryStruct.com…
-/
theorem morphismRestrict_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) :
    (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U ≫ g ∣_ U := by
  delta morphismRestrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono (pullback.fst _ _)]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl

@[reassoc]
/-
**AlgebraicGeometry.morphismRestrict_homOfLE** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：morphismRestrict_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e
 : U <= V) : (f ∣_ U) ≫ Y.homOfLE e = X.homOfLE (f.preimage_mono e) ≫ (f ∣_ V)
参数：f : X ⟶ Y；U V : Y.Opens；e : U <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι_assoc`：∀ (X : AlgebraicGeometry.Schem
e) {U V : X.Opens} (e : U ≤ V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),   Cat
egoryTheory.CategoryStruct.com…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem morphismRestrict_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U V : Y.Opens) (e : U ≤ V) :
    (f ∣_ U) ≫ Y.homOfLE e = X.homOfLE (f.preimage_mono e) ≫ (f ∣_ V) := by
  simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.isoImage_preimage_hom_homOfLE** 是 Mathlib 中的一个定理，
位于命名空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.I
sOpenImmersion f] (U : Y.Opens),   CategoryTheory.CategoryStruct.comp       (Alg
ebraicGeometry.Scheme.Hom.isoImage f ((TopologicalSpace.Opens.map f.base).obj U)
).hom (Y.homOfLE ⋯) =     f ∣_ U
参数：f : X ⟶ Y；U : Y.Opens；AlgebraicGeometry.Scheme.Hom.isoImage f ((TopologicalSp
ace.Opens.map f.base).obj U)；Y.homOfLE ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_le`：image_preimage_le (U : Y
.Opens) : f ''ᵁ f ⁻¹ᵁ U <= U
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_ι`：∀ (X : AlgebraicGeometry.Scheme) {U 
V : X.Opens} (e : U ≤ V), CategoryTheory.CategoryStruct.comp (X.homOfLE e) V.ι =
 U.ι
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens), 
  CategoryTheory.CategoryStruct.c…
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Scheme.Hom.isoImage_preimage_hom_homOfLE {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Y.Opens) :
    (f.isoImage (f ⁻¹ᵁ U)).hom ≫ Y.homOfLE (f.image_preimage_le U) = f ∣_ U := by
  simp [← cancel_mono U.ι]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (U : Y.Opens) : IsIso (f ∣_ U) := by
  delta morphismRestrict; infer_instance

@[simp]
/-
**AlgebraicGeometry.morphismRestrict_base_coe** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x)
 : ((f ∣_ U) x).1 = f x.1
参数：f : X ⟶ Y；U : Y.Opens；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
-/
theorem morphismRestrict_base_coe {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    ((f ∣_ U) x).1 = f x.1 :=
  congr_arg (fun f => (Scheme.Hom.toLRSHom f).base x)
    (morphismRestrict_ι f U)
/-
**AlgebraicGeometry.morphismRestrict_base** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : ⇑(f ∣
_ U) = U.1.restrictPreimage f
参数：f : X ⟶ Y；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgebraicGeometry.morphismRestrict_base_coe`：morphismRestrict_base_coe {
X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) : ((f ∣_ U) x).1 = f x.1
-/
theorem morphismRestrict_base {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    ⇑(f ∣_ U) = U.1.restrictPreimage f :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)
/-
**AlgebraicGeometry.image_morphismRestrict_preimage** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry`。
形式化陈述：image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Open
s) (V : Opens U) : (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V)
参数：f : X ⟶ Y；U : Y.Opens；V : Opens U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.image_preimage_eq_preimage_image_of_is
Pullback`：image_preimage_eq_preimage_image_of_isPullback {X Y U V : Scheme.{u}} 
{f : X ⟶ Y} {f' : U ⟶ V} {iU : U ⟶ X} {iV : V ⟶ Y} [IsOpenImmersion iV…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
-/
theorem image_morphismRestrict_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι ''ᵁ V) :=
  IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback (isPullback_morphismRestrict f U) V

set_option backward.isDefEq.respectTransparency false in
open Scheme in
/-
**AlgebraicGeometry.morphismRestrict_app** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.t
oScheme.Opens) : (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫ X.presheaf.map (eqToHom (i
mage_morphismRestrict_preimage f U V)).op
参数：f : X ⟶ Y；U : Y.Opens；V : U.toScheme.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.eqToHom_unop`：eqToHom_unop {X Y : Cᵒᵖ} (h : X = Y) : (eqT
oHom h).unop = eqToHom (congr_arg unop h.symm)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.NatTrans.naturality_assoc`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.congr_app`：congr_app {X Y : Scheme} {f g : 
X ⟶ Y} (e : f = g) (U) : f.app U = g.app U ≫ X.presheaf.map (eqToHom (by subst e
; rfl)).op
-/
theorem morphismRestrict_app {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    (f ∣_ U).app V = f.app (U.ι ''ᵁ V) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  obtain ⟨V, rfl⟩ : ∃ V', U.ι ⁻¹ᵁ U.ι ''ᵁ V' = V := ⟨_, U.ι.preimage_image_eq V⟩
  simpa [← Functor.map_comp_assoc, ← Functor.map_comp] using!
    congr(Y.presheaf.map (eqToHom (congr_arg (U.ι ''ᵁ ·) (U.ι.preimage_image_eq V).symm)).op ≫
      $(Scheme.Hom.congr_app (morphismRestrict_ι f U) (U.ι ''ᵁ V)))
/-
**AlgebraicGeometry.morphismRestrict_appTop** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : (f 
∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫ X.presheaf.map (eqToHom (image_morphismRestri
ct_preimage f U ⊤)).op
参数：f : X ⟶ Y；U : Y.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.morphismRestrict_app`：morphismRestrict_app {X Y : Sche
me.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) : (f ∣_ U).app V = f.ap
p (U.ι ''ᵁ V) ≫ X.presheaf.m…
-/
theorem morphismRestrict_appTop {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) :
    (f ∣_ U).appTop = f.app (U.ι ''ᵁ ⊤) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U ⊤)).op :=
  morphismRestrict_app ..

@[simp]
/-
**AlgebraicGeometry.morphismRestrict_app'** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry`。
形式化陈述：morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Op
ens U) : (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le
参数：f : X ⟶ Y；U : Y.Opens；V : Opens U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.morphismRestrict_app`：morphismRestrict_app {X Y : Sche
me.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) : (f ∣_ U).app V = f.ap
p (U.ι ''ᵁ V) ≫ X.presheaf.m…
-/
theorem morphismRestrict_app' {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) :
    (f ∣_ U).app V = f.appLE _ _ (image_morphismRestrict_preimage f U V).le :=
  morphismRestrict_app f U V

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AlgebraicGeometry.morphismRestrict_appLE** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry`。
形式化陈述：morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e
) : (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W) ((Set.image_m
ono e).trans (image_morphismRestrict_preimage f U V).le)
参数：f : X ⟶ Y；U : Y.Opens；V W e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.appLE.eq_1`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens)   (e : V ≤ (TopologicalSpace.Opens.m
ap f.base).obj U),   Algebrai…
· 使用定理 `AlgebraicGeometry.morphismRestrict_app'`：morphismRestrict_app' {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ∣_ U).app V = f.appLE _ _
 (image_morphismRestrict_prei…
· 使用引理 `AlgebraicGeometry.Scheme.Opens.toScheme_presheaf_map`：toScheme_presheaf_
map {V W} (i : V ⟶ W) : U.toScheme.presheaf.map i = X.presheaf.map (U.ι.opensFun
ctor.map i.unop).op
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
-/
theorem morphismRestrict_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V W e) :
    (f ∣_ U).appLE V W e = f.appLE (U.ι ''ᵁ V) ((f ⁻¹ᵁ U).ι ''ᵁ W)
      ((Set.image_mono e).trans (image_morphismRestrict_preimage f U V).le) := by
  rw [Scheme.Hom.appLE, morphismRestrict_app', Scheme.Opens.toScheme_presheaf_map,
    Scheme.Hom.appLE_map]

@[reassoc]
/-
**AlgebraicGeometry.morphismRestrict_homOfLE_isoImage_** 是 Mathlib 中的一个定理，位于命名空间
 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem morphismRestrict_homOfLE_isoImage_ι_hom
    {X : Scheme.{u}} {U V : X.Opens} (e : U ≤ V) (W : Opens V) :
    X.homOfLE e ∣_ W ≫ (V.ι.isoImage W).hom =
      (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).hom ≫ X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) := by
  simp [← cancel_mono (V.ι ''ᵁ W).ι]

@[reassoc]
/-
**AlgebraicGeometry.isoImage_** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isoImage_ι_inv_morphismRestrict_homOfLE {X : Scheme.{u}} {U V : X.Opens}
    (e : U ≤ V) (W : Opens V) :
    (U.ι.isoImage (X.homOfLE e ⁻¹ᵁ W)).inv ≫ X.homOfLE e ∣_ W =
      X.homOfLE (X.ι_image_homOfLE_le_ι_image e W) ≫ (V.ι.isoImage W).inv := by
  simp [← cancel_mono (V.ι.isoImage W).hom, morphismRestrict_homOfLE_isoImage_ι_hom]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism onto the image of an open immersion is isomorphic to the base change
along the immersion. -/
/-
**AlgebraicGeometry.morphismRestrictOpensRange** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry`。
形式化陈述：morphismRestrictOpensRange {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [I
sOpenImmersion g] : Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g)
参数：f : X ⟶ Y；g : U ⟶ Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
Restricting a morphism onto the image of an open immersion is isomorphic to the 
base change
along the immersion.
-/
def morphismRestrictOpensRange {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y) [IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd f g) := by
  let V : Y.Opens := g.opensRange
  let e :=
    IsOpenImmersion.isoOfRangeEq g V.ι Subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f V.ι :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom_fac])
  symm
  refine Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e ?_
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g]
  dsimp
  rw [Category.assoc, Category.assoc, Category.assoc, IsOpenImmersion.isoOfRangeEq_inv_fac,
    ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_ι_assoc, pullback.lift_fst_assoc, Category.comp_id]

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
/-
**AlgebraicGeometry.morphismRestrictEq** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try`。
形式化陈述：morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U =
 V) : Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V)
参数：f : X ⟶ Y；e : U = V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restrictions onto two equal open sets are isomorphic. This currently has bad
 defeqs when
unfolded, but it should not matter for now. Replace this definition if better de
feqs are needed.
-/
def morphismRestrictEq {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e; rfl)

@[reassoc]
/-
**AlgebraicGeometry.morphismRestrict_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeomet
ry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma morphismRestrict_ι_image_ι_isoImage_inv
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U.ι ''ᵁ V ≫ (U.ι.isoImage V).inv = (X.homOfLE (image_morphismRestrict_preimage f U V).ge ≫
      ((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).inv) ≫ f ∣_ U ∣_ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

@[reassoc]
/-
**AlgebraicGeometry.morphismRestrict_morphismRestrict_** 是 Mathlib 中的一个引理，位于命名空间
 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma morphismRestrict_morphismRestrict_ι_isoImage_hom
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    f ∣_ U ∣_ V ≫ (U.ι.isoImage V).hom = (((f ⁻¹ᵁ U).ι.isoImage ((f ∣_ U) ⁻¹ᵁ V)).hom ≫
      X.homOfLE (image_morphismRestrict_preimage f U V).le) ≫ f ∣_ U.ι ''ᵁ V := by
  simp [← cancel_mono (Scheme.Opens.ι _)]

/-- Restricting a morphism twice is isomorphic to one restriction. -/
/-
**AlgebraicGeometry.morphismRestrictRestrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V :
 U.toScheme.Opens) : Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V)
参数：f : X ⟶ Y；U : Y.Opens；V : U.toScheme.Opens。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…

--- 原说明 ---
Restricting a morphism twice is isomorphic to one restriction.
-/
def morphismRestrictRestrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : U.toScheme.Opens) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.ι ''ᵁ V) := by
  refine Arrow.isoMk' _ _ ((Scheme.Opens.ι _).isoImage _ ≪≫ Scheme.isoOfEq _ ?_)
    ((Scheme.Opens.ι _).isoImage _) ?_
  · exact image_morphismRestrict_preimage f U V
  · simp [← cancel_mono (Scheme.Opens.ι _)]

set_option backward.isDefEq.respectTransparency false in
/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction. -/
/-
**AlgebraicGeometry.morphismRestrictRestrictBasicOpen** 是 Mathlib 中的一个定义，位于命名空间 
`AlgebraicGeometry`。
形式化陈述：morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Op
ens) (r : Γ(Y, U)) : Arrow.mk (f ∣_ U ∣_ U.toScheme.basicOpen (Y.presheaf.map (e
qToHom U.isOpenEmbedding_obj_top).op r)) ≅ Arrow.mk (f ∣_ Y.basicOpen r)
参数：f : X ⟶ Y；U : Y.Opens；r : Γ(Y, U)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι

--- 原说明 ---
Restricting a morphism twice onto a basic open set is isomorphic to one restrict
ion.
-/
def morphismRestrictRestrictBasicOpen {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (r : Γ(Y, U)) :
    Arrow.mk (f ∣_ U ∣_
          U.toScheme.basicOpen (Y.presheaf.map (eqToHom U.isOpenEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) := by
  refine morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ ?_
  simp [Scheme.Opens.ι_image_basicOpen]

set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
/-
**AlgebraicGeometry.morphismRestrictStalkMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry`。
形式化陈述：morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) 
: Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1)
参数：f : X ⟶ Y；U : Y.Opens；x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalk map of a restriction of a morphism is isomorphic to the stalk map of t
he original map.
-/
def morphismRestrictStalkMap {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (x) :
    Arrow.mk ((f ∣_ U).stalkMap x) ≅ Arrow.mk (f.stalkMap x.1) := Arrow.isoMk' _ _
  (U.stalkIso ((f ∣_ U) x) ≪≫
    (TopCat.Presheaf.stalkCongr _ <| Inseparable.of_eq <| morphismRestrict_base_coe f U x))
  ((f ⁻¹ᵁ U).stalkIso x) <| TopCat.Presheaf.stalk_hom_ext _ fun V hxV ↦ by
    simp [Scheme.Hom.germ_stalkMap_assoc, Scheme.Hom.appLE]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphismRestrict
  exact PresheafedSpace.IsOpenImmersion.comp _ _

variable {X Y : Scheme.{u}}

namespace Scheme.Hom

/-- The restriction of a morphism `f : X ⟶ Y` to open sets on the source and target. -/
/-
**AlgebraicGeometry.Scheme.Hom.resLE** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y.Scheme.Hom`。
形式化陈述：resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U) : V.toS
cheme ⟶ U.toScheme
参数：f : Hom X Y；U : Y.Opens；V : X.Opens；e : V <= f ⁻¹ᵁ U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The restriction of a morphism `f : X ⟶ Y` to open sets on the source and target.
-/
def resLE (f : Hom X Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) : V.toScheme ⟶ U.toScheme :=
  X.homOfLE e ≫ f ∣_ U

variable (f : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
/-
**AlgebraicGeometry.Scheme.Hom.resLE_eq_morphismRestrict** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.Hom`。
形式化陈述：resLE_eq_morphismRestrict : f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.homOfLE ⋯ = CategoryTheory.CategoryStruct.id ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resLE_eq_morphismRestrict : f.resLE U (f ⁻¹ᵁ U) le_rfl = f ∣_ U := by
  simp [resLE]

@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.resLE_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeom
etry.Scheme.Hom`。
形式化陈述：resLE_id (i : V <= V') : resLE (𝟙 X) V' V i = X.homOfLE i
参数：i : V <= V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.morphismRestrict_id`：morphismRestrict_id {X : Scheme.{
u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _
-/
lemma resLE_id (i : V ≤ V') : resLE (𝟙 X) V' V i = X.homOfLE i := by
  simp only [resLE, morphismRestrict_id]
  rfl

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.resLE_comp_** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma resLE_comp_ι : f.resLE U V e ≫ U.ι = V.ι ≫ f := by
  simp [resLE]

@[reassoc]
/-
**AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：resLE_comp_resLE {Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') : f.resLE
 U V e ≫ g.resLE W U e' = (f ≫ g).resLE W V (e.trans ((Opens.map f.base).map (ho
mOfLE e')).le)
参数：g : Y ⟶ Z；e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι_assoc`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}   (e : V ≤ (TopologicalSpace
.Opens.map f.base).obj U) {Z : Algebr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resLE_comp_resLE {Z : Scheme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') :
    f.resLE U V e ≫ g.resLE W U e' = (f ≫ g).resLE W V
      (e.trans ((Opens.map f.base).map (homOfLE e')).le) := by
  simp [← cancel_mono W.ι]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.map_resLE** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：map_resLE (i : V' <= V) : X.homOfLE i ≫ f.resLE U V e = f.resLE U V' (i.tr
ans e)
参数：i : V' <= V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE`：resLE_comp_resLE {Z : Sch
eme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') : f.resLE U V e ≫ g.resLE W U e' = (f ≫ 
g).resLE W V (e.trans ((Opens.map f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.resLE.congr_simp`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f f_1 : X.Hom Y) (e_f : f = f_1) (U : Y.Opens) (V : X.Opens)   (e : V
 ≤ (TopologicalSpace.Opens.map f.ba…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_resLE (i : V' ≤ V) :
    X.homOfLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.id_comp]

set_option backward.isDefEq.respectTransparency.types false in
@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.Hom.resLE_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry.Scheme.Hom`。
形式化陈述：resLE_map (i : U <= U') : f.resLE U V e ≫ Y.homOfLE i = f.resLE U' V (e.tr
ans ((Opens.map f.base).map i.hom).le)
参数：i : U <= U'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_resLE`：resLE_comp_resLE {Z : Sch
eme.{u}} (g : Y ⟶ Z) {W : Z.Opens} (e') : f.resLE U V e ≫ g.resLE W U e' = (f ≫ 
g).resLE W V (e.trans ((Opens.map f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.resLE.congr_simp`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f f_1 : X.Hom Y) (e_f : f = f_1) (U : Y.Opens) (V : X.Opens)   (e : V
 ≤ (TopologicalSpace.Opens.map f.ba…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma resLE_map (i : U ≤ U') :
    f.resLE U V e ≫ Y.homOfLE i =
      f.resLE U' V (e.trans ((Opens.map f.base).map i.hom).le) := by
  simp_rw [← resLE_id, resLE_comp_resLE, Category.comp_id]
/-
**AlgebraicGeometry.Scheme.Hom.resLE_congr** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：resLE_congr (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty Scheme.{u}) 
: P (f.resLE U V e) ↔ P (f.resLE U' V' (e₁ ▸ e₂ ▸ e))
参数：e₁ : U = U'；e₂ : V = V'；P : MorphismProperty Scheme.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma resLE_congr (e₁ : U = U') (e₂ : V = V') (P : MorphismProperty Scheme.{u}) :
    P (f.resLE U V e) ↔ P (f.resLE U' V' (e₁ ▸ e₂ ▸ e)) := by
  subst e₁; subst e₂; rfl
/-
**AlgebraicGeometry.Scheme.Hom.resLE_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：resLE_preimage (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) 
(O : U.toScheme.Opens) : f.resLE U V e ⁻¹ᵁ O = V.ι ⁻¹ᵁ (f ⁻¹ᵁ U.ι ''ᵁ O)
参数：f : X ⟶ Y；e : V <= f ⁻¹ᵁ U；O : U.toScheme.Opens。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_preimage`：comp_preimage {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`：preimage_image_eq (U : X
.Opens) : f ⁻¹ᵁ f ''ᵁ U = U
-/
lemma resLE_preimage (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) :
    f.resLE U V e ⁻¹ᵁ O = V.ι ⁻¹ᵁ (f ⁻¹ᵁ U.ι ''ᵁ O) := by
  rw [← comp_preimage, ← resLE_comp_ι f e, comp_preimage, preimage_image_eq]
/-
**AlgebraicGeometry.Scheme.Hom.le_resLE_preimage_iff** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme.Hom`。
形式化陈述：le_resLE_preimage_iff {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (O : 
U.toScheme.Opens) (W : V.toScheme.Opens) : W <= (f.resLE U V e) ⁻¹ᵁ O ↔ V.ι ''ᵁ 
W <= f ⁻¹ᵁ U.ι ''ᵁ O
参数：e : V <= f ⁻¹ᵁ U；O : U.toScheme.Opens；W : V.toScheme.Opens。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_preimage`：resLE_preimage (f : X ⟶ Y) 
{U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (O : U.toScheme.Opens) : f.resLE 
U V e ⁻¹ᵁ O = V.ι ⁻¹ᵁ (f ⁻¹ᵁ U.ι …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_le_image_iff`：image_le_image_iff (f :
 X ⟶ Y) [IsOpenImmersion f] (U U' : X.Opens) : f ''ᵁ U <= f ''ᵁ U' ↔ U <= U'
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_le`：ι_image_le (W : U.toScheme.Op
ens) : U.ι ''ᵁ W <= U
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_resLE_preimage_iff {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) :
    W ≤ (f.resLE U V e) ⁻¹ᵁ O ↔ V.ι ''ᵁ W ≤ f ⁻¹ᵁ U.ι ''ᵁ O := by
  simp [resLE_preimage, ← image_le_image_iff V.ι, image_preimage_eq_opensRange_inf, V.ι_image_le]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.resLE_app_top** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
   (e : V ≤ (TopologicalSpace.Opens.map f.base).obj U),   AlgebraicGeometry.Sche
me.Hom.app (AlgebraicGeometry.Scheme.Hom.resLE f U V e) ⊤ =     CategoryTheory.C
ategoryStruct.comp U.topIso.hom       (CategoryTheory.CategoryStruct.comp (Algeb
raicGeometry.Scheme.Hom.appLE f U V e) V.topIso.inv)
参数：f : X ⟶ Y；e : V ≤ (TopologicalSpace.Opens.map f.base).obj U；AlgebraicGeometry
.Scheme.Hom.resLE f U V e；CategoryTheory.CategoryStruct.comp (AlgebraicGeometry.
Scheme.Hom.appLE f U V e) V.topIso.inv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_app'`：morphismRestrict_app' {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ∣_ U).app V = f.appLE _ _
 (image_morphismRestrict_prei…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_app`：∀ {X : AlgebraicGeometry.Scheme} {
U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   AlgebraicGeometry.Scheme.Hom.app 
(X.homOfLE e) W = X.preshe…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.appLE_map`：appLE_map (e : V <= f ⁻¹ᵁ U) (i 
: op V ⟶ op V') : f.appLE U V e ≫ X.presheaf.map i = f.appLE U V' (i.unop.le.tra
ns e)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_hom`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.hom = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用定理 `CategoryTheory.eqToHom_op`：eqToHom_op {X Y : C} (h : X = Y) : (eqToHom h
).op = eqToHom (congr_arg op h.symm)
· 使用定理 `AlgebraicGeometry.Scheme.Opens.topIso_inv`：∀ {X : AlgebraicGeometry.Sche
me} (U : X.Opens), U.topIso.inv = X.presheaf.map (CategoryTheory.eqToHom ⋯).op
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_appLE`：map_appLE (e : V <= f ⁻¹ᵁ U) (i 
: op U' ⟶ op U) : Y.presheaf.map i ≫ f.appLE U V e = f.appLE U' V (e.trans ((Ope
ns.map f.base).map i.unop).l…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma resLE_app_top : (f.resLE U V e).app ⊤ =
    U.topIso.hom ≫ f.appLE U V e ≫ V.topIso.inv := by simp [Scheme.Hom.resLE]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Hom.resLE_appLE** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Hom`。
形式化陈述：resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (O : U.toScheme
.Opens) (W : V.toScheme.Opens) (e' : W <= resLE f U V e ⁻¹ᵁ O) : (f.resLE U V e)
.appLE O W e' = f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_resLE_preimage_iff f e O W)
.mp e')
参数：e : V <= f ⁻¹ᵁ U；O : U.toScheme.Opens；W : V.toScheme.Opens；e' : W <= resLE f 
U V e ⁻¹ᵁ O。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.Hom.le_resLE_preimage_iff`：le_resLE_preimage_if
f {U : Y.Opens} {V : X.Opens} (e : V <= f ⁻¹ᵁ U) (O : U.toScheme.Opens) (W : V.t
oScheme.Opens) : W <= (f.resLE U V e) ⁻¹…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_app'`：morphismRestrict_app' {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ∣_ U).app V = f.appLE _ _
 (image_morphismRestrict_prei…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_app`：∀ {X : AlgebraicGeometry.Scheme} {
U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   AlgebraicGeometry.Scheme.Hom.app 
(X.homOfLE e) W = X.preshe…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
-/
lemma resLE_appLE {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U)
    (O : U.toScheme.Opens) (W : V.toScheme.Opens) (e' : W ≤ resLE f U V e ⁻¹ᵁ O) :
    (f.resLE U V e).appLE O W e' =
      f.appLE (U.ι ''ᵁ O) (V.ι ''ᵁ W) ((le_resLE_preimage_iff f e O W).mp e') := by
  dsimp [appLE, resLE]
  simp only [morphismRestrict_app', appLE, homOfLE_leOfHom, homOfLE_app, Category.assoc]
  rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.Hom.coe_resLE_apply** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme.Hom`。
形式化陈述：coe_resLE_apply (x : V) : (f.resLE U V e x).1 = f x
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgebraicGeometry.morphismRestrict_base`：morphismRestrict_base {X Y : Sc
heme.{u}} (f : X ⟶ Y) (U : Y.Opens) : ⇑(f ∣_ U) = U.1.restrictPreimage f
· 使用定理 `Set.restrictPreimage_coe`：∀ {α : Type u} {β : Type v} (t : Set β) (f : α
 → β) (a : ↑(f ⁻¹' t)), ↑(t.restrictPreimage f a) = f ↑a
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_apply`：∀ {X : AlgebraicGeometry.Scheme}
 {U V : X.Opens} (e : U ≤ V) (x : ↥U), ↑((X.homOfLE e) x) = ↑x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_resLE_apply (x : V) : (f.resLE U V e x).1 = f x := by
  simp [resLE, morphismRestrict_base]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The stalk map of `f.resLE U V` at `x : V` is the stalk map of `f` at `x`. -/
/-
**AlgebraicGeometry.Scheme.Hom.resLEStalkMap** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：resLEStalkMap (x : V) : Arrow.mk ((f.resLE U V e).stalkMap x) ≅ Arrow.mk (
f.stalkMap x)
参数：x : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stalk map of `f.resLE U V` at `x : V` is the stalk map of `f` at `x`.
-/
def resLEStalkMap (x : V) :
    Arrow.mk ((f.resLE U V e).stalkMap x) ≅ Arrow.mk (f.stalkMap x) :=
  Arrow.isoMk (U.stalkIso _ ≪≫
      (Y.presheaf.stalkCongr <| Inseparable.of_eq <| by simp)) (V.stalkIso x) <| by
    dsimp
    rw [Category.assoc, ← Iso.eq_inv_comp, ← Category.assoc, ← Iso.comp_inv_eq,
      Opens.stalkIso_inv, Opens.stalkIso_inv, ← stalkMap_comp,
      stalkMap_congr_hom _ _ (resLE_comp_ι f e), stalkMap_comp]
    simp

end Scheme.Hom

set_option backward.isDefEq.respectTransparency false in
/-- `f.resLE U V` induces `f.appLE U V` on global sections. -/
/-
**AlgebraicGeometry.arrowResLEAppIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometr
y`。
形式化陈述：arrowResLEAppIso (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V <= f ⁻¹ᵁ U
) : Arrow.mk ((f.resLE U V e).appTop) ≅ Arrow.mk (f.appLE U V e)
参数：f : X ⟶ Y；U : Y.Opens；V : X.Opens；e : V <= f ⁻¹ᵁ U。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`f.resLE U V` induces `f.appLE U V` on global sections.
-/
noncomputable def arrowResLEAppIso (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    Arrow.mk ((f.resLE U V e).appTop) ≅ Arrow.mk (f.appLE U V e) :=
  Arrow.isoMk U.topIso V.topIso <| by
  simp only [Scheme.Opens.topIso_hom, eqToHom_op, Arrow.mk_hom, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, ← Scheme.Hom.appLE_eq_app, Scheme.Hom.resLE_appLE, Scheme.Hom.appLE_map]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Hom.isPullback_resLE** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y S T : AlgebraicGeometry.Scheme} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S
} {iY : Y ⟶ T},   CategoryTheory.IsPullback g iY iX f →     ∀ {US : S.Opens} {UT
 : T.Opens} {UX : X.Opens} (hUST : UT ≤ (TopologicalSpace.Opens.map f.base).obj 
US)       (hUSX : UX ≤ (TopologicalSpace.Opens.map iX.base).obj US) {UY : Y.Open
s}       (hUY : UY = (TopologicalSpace.Opens.map g.base).obj UX ⊓ (TopologicalSp
ace.Opens.map iY.base).obj UT),       CategoryTheory.IsPullback (AlgebraicGeomet
ry.Scheme.Hom.resLE g UX UY ⋯)         (AlgebraicGeometry.Scheme.Hom.resLE iY UT
 UY ⋯) (AlgebraicGeometry.Scheme.Hom.resLE iX US UX hUSX)         (AlgebraicGeom
etry.Scheme.Hom.resLE f US UT hUST)
参数：hUST : UT ≤ (TopologicalSpace.Opens.map f.base).obj US；hUSX : UX ≤ (Topologic
alSpace.Opens.map iX.base).obj US；hUY : UY = (TopologicalSpace.Opens.map g.base)
.obj UX ⊓ (TopologicalSpace.Opens.map iY.base).obj UT；AlgebraicGeometry.Scheme.H
om.resLE g UX UY ⋯；AlgebraicGeometry.Scheme.Hom.resLE iY UT UY ⋯；AlgebraicGeomet
ry.Scheme.Hom.resLE iX US UX hUSX；AlgebraicGeometry.Scheme.Hom.resLE f US UT hUS
T。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.IsPullback.paste_horiz`：paste_horiz {X₁₁ X₁₂ X₁₃ X₂₁ X₂₂ 
X₂₃ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₁₂ : X₁₂ ⟶ X₁₃} {h₂₁ : X₂₁ ⟶ X₂₂} {h₂₂ : X₂₂ ⟶ X₂₃}
 {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X…
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `CategoryTheory.CommSq.w`：∀ {C : Type u_1} [inst : CategoryTheory.Categor
y.{v_1, u_1} C] {W X Y Z : C} {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z}   {i : Y ⟶ Z},
   CategoryTh…
· 使用定理 `CategoryTheory.IsPullback.toCommSq`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {P X Y Z : C} {fst : P ⟶ X} {snd : P ⟶ Y} {f : X ⟶ Z}   
{g : Y ⟶ Z}, CategoryThe…
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsPullback.flip`：flip (h : IsPullback fst snd f g) : IsPu
llback snd fst g f
· 使用引理 `AlgebraicGeometry.IsOpenImmersion.isPullback`：isPullback {U V X Y : Sche
me.{u}} (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y) (f : X ⟶ Y) [IsOpenImmersion iU] [
IsOpenImmersion iV] (H : iU ≫ f = …
· 使用定理 `AlgebraicGeometry.instIsOpenImmersionHomOfLE`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U ≤ V), AlgebraicGeometry.IsOpenImmersion (X.homOfLE
 e)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.map_resLE`：map_resLE (i : V' <= V) : X.homO
fLE i ≫ f.resLE U V e = f.resLE U V' (i.trans e)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_map`：resLE_map (i : U <= U') : f.resL
E U V e ≫ Y.homOfLE i = f.resLE U' V (e.trans ((Opens.map f.base).map i.hom).le)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.opensRange_homOfLE`：∀ {X : AlgebraicGeometry.Sc
heme} {U V : X.Opens} (e : U ≤ V),   AlgebraicGeometry.Scheme.Hom.opensRange (X.
homOfLE e) = (TopologicalSpace.Op…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`：resLE_comp_ι : f.resLE U V e 
≫ U.ι = V.ι ≫ f
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_preimage`：comp_preimage {X Y Z : Schem
e.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U) : (f ≫ g) ⁻¹ᵁ U = f ⁻¹ᵁ g ⁻¹ᵁ U
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_injective`：image_injective : Function
.Injective (f ''ᵁ ·)
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf`：image_pre
image_eq_opensRange_inf (U : Y.Opens) : f ''ᵁ f ⁻¹ᵁ U = f.opensRange ⊓ U
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `CategoryTheory.IsPullback.of_bot`：of_bot {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃₂ : C} {
h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {v₁₂ : X₁
₂ ⟶ X₂₂} {v₂₁ : X₂₁ ⟶ …
· 使用定理 `CategoryTheory.IsPullback.paste_vert`：paste_vert {X₁₁ X₁₂ X₂₁ X₂₂ X₃₁ X₃
₂ : C} {h₁₁ : X₁₁ ⟶ X₁₂} {h₂₁ : X₂₁ ⟶ X₂₂} {h₃₁ : X₃₁ ⟶ X₃₂} {v₁₁ : X₁₁ ⟶ X₂₁} {
v₁₂ : X₁₂ ⟶ X₂₂} {v₂₁ : X₂…
· 使用定理 `AlgebraicGeometry.isPullback_morphismRestrict`：isPullback_morphismRestri
ct {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) : IsPullback (f ∣_ U) (f ⁻¹ᵁ U).
ι U.ι f
（共 35 条，此处仅展示前 30 条）
-/
lemma Scheme.Hom.isPullback_resLE
    {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {iX : X ⟶ S} {iY : Y ⟶ T}
    (H : IsPullback g iY iX f)
    {US : S.Opens} {UT : T.Opens}
    {UX : X.Opens} (hUST : UT ≤ f ⁻¹ᵁ US) (hUSX : UX ≤ iX ⁻¹ᵁ US)
    {UY : Y.Opens} (hUY : UY = g ⁻¹ᵁ UX ⊓ iY ⁻¹ᵁ UT) :
    IsPullback (g.resLE UX UY (by simp [*])) (iY.resLE UT UY (by simp [*]))
      (iX.resLE US UX hUSX) (f.resLE US UT hUST) := by
  refine .paste_horiz (v₁₂ := iY.resLE _ _
    ((g.preimage_mono hUSX).trans_eq congr(($H.w) ⁻¹ᵁ US) :)) ?_ ?_
  · refine (IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_).flip
    simp only [Scheme.opensRange_homOfLE, ← Scheme.Hom.comp_preimage, Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_preimage, ← (g ⁻¹ᵁ UX).ι.image_injective.eq_iff]
    simp only [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    simp [hUY]
  · refine .of_bot ?_ ?_ (isPullback_morphismRestrict f US)
    · simpa using (isPullback_morphismRestrict g UX).paste_vert H
    · simp [← cancel_mono US.ι, H.w]

end MorphismRestrict

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The restriction of an open cover to an open subset. -/
@[simps! I₀ X f]
noncomputable
/-
**AlgebraicGeometry.Scheme.OpenCover.restrict** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
icGeometry.Scheme.OpenCover`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → X.OpenCover → (U : X.Opens) → (↑U).OpenCo
ver
参数：U : X.Opens；↑U。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsStableUnderBaseChangePrecoverageOfIsJoint
lySurjectivePreservingOfIsStableUnderBaseChange`：∀ (P : CategoryTheory.MorphismP
roperty AlgebraicGeometry.Scheme)   [AlgebraicGeometry.Scheme.IsJointlySurjectiv
ePreserving P] [P.IsStableUnd…
· 使用定理 `AlgebraicGeometry.Scheme.instIsJointlySurjectivePreservingIsOpenImmersio
n`：AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving AlgebraicGeometry.IsOp
enImmersion
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
def Scheme.OpenCover.restrict {X : Scheme.{u}} (𝒰 : Scheme.OpenCover.{v} X) (U : Opens X) :
    U.toScheme.OpenCover := by
  refine Cover.copy (𝒰.pullback₁ U.ι) 𝒰.I₀ _ (𝒰.f · ∣_ U) (Equiv.refl _)
    (fun i ↦ IsOpenImmersion.isoOfRangeEq (Opens.ι _) (pullback.snd _ _) ?_) ?_
  · dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_I₀, Equiv.refl_apply, PreZeroHypercover.pullback₁_X]
    rw [IsOpenImmersion.range_pullbackSnd U.ι (𝒰.f i), Opens.opensRange_ι]
    exact Subtype.range_val
  · intro i
    rw [← cancel_mono U.ι]
    simp [morphismRestrict_ι, Equiv.refl_apply, Category.assoc, pullback.condition]

end AlgebraicGeometry

