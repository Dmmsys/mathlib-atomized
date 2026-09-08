/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.Birational.Dominant

/-!
# Composition of rational maps

This file defines composition for partial maps and rational maps between schemes.

## Main definitions

- `Scheme.PartialMap.comp`: given a dominant partial map `f : X.PartialMap Y` and any partial map
  `g : Y.PartialMap Z`, their composition `f.comp g : X.PartialMap Z` is defined on the preimage
  of `g`'s domain under `f`.
- `Scheme.RationalMap.comp`: composition of rational maps, defined via a dominant representative.

## Main statements

- `Scheme.PartialMap.comp_equiv_of_equiv`: Composition respects equivalence of partial maps.
- `Scheme.PartialMap.comp_assoc`: Composition of partial maps is associative.
- `Scheme.RationalMap.comp_assoc`: Composition of rational maps is associative.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

section PreirreducibleSpace

variable [PreirreducibleSpace X] [Nonempty Y]

namespace PartialMap

/-- Composition of partial maps. The domain of `f.comp g` is the preimage of `g.domain` under `f`,
viewed as an open subscheme of `X`. Requires `f.hom` to be dominant so that the domain is dense. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.PartialMap`。
形式化陈述：comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) : X.Part
ialMap Z where domain
参数：f : X.PartialMap Y；g : Y.PartialMap Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of partial maps. The domain of `f.comp g` is the preimage of `g.doma
in` under `f`,
viewed as an open subscheme of `X`. Requires `f.hom` to be dominant so that the 
domain is dense.
-/
noncomputable def comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    X.PartialMap Z where
  domain := f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain
  dense_domain := (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain).2.dense <| by
    simpa [← Set.nonempty_preimage_iff] using
      f.hom.denseRange.inter_open_nonempty _ g.domain.2 g.dense_domain.nonempty
  hom := (f.domain.ι.isoImage _).inv ≫ f.hom ∣_ g.domain ≫ g.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_restrict_left** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens) (
hU : Dense (U : Set X)) (hU' : U <= f.domain) (g : Y.PartialMap Z) : (f.restrict
 U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U) 
((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left
参数：f : X.PartialMap Y；U : X.Opens；hU : Dense (U : Set X)；hU' : U <= f.domain；g :
 Y.PartialMap Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Dense.inter_of_isOpen_right`：Dense.inter_of_isOpen_right (hs : Dense s) 
(ht : Dense t) (hto : IsOpen t) : Dense (s inter t)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_eq_ι_image_inf`：∀ {X : Algebrai
cGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeom
etry.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicGeometry.Scheme.ι_image_homOfLE_le_ι_image`：∀ {X : AlgebraicGeo
metry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : (↑V).Opens),   (AlgebraicGeometry
.Scheme.Hom.opensFunctor U.ι).obj ((Topol…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.isoImage_ι_inv_morphismRestrict_homOfLE_assoc`：∀ {X : 
AlgebraicGeometry.Scheme} {U V : X.Opens} (e : U ≤ V) (W : TopologicalSpace.Open
s ↥↑V)   {Z : AlgebraicGeometry.Scheme} (h : ↑W ⟶ Z),…
· 使用定理 `AlgebraicGeometry.Scheme.homOfLE_homOfLE_assoc`：∀ (X : AlgebraicGeometry
.Scheme) {U V W : X.Opens} (e₁ : U ≤ V) (e₂ : V ≤ W) {Z : AlgebraicGeometry.Sche
me}   (h : ↑W ⟶ Z),   CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_restrict_left (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.domain) (g : Y.PartialMap Z) :
    (f.restrict U hU hU').comp g = (f.comp g).restrict (f.domain.ι ''ᵁ f.hom ⁻¹ᵁ g.domain ⊓ U)
      ((f.comp g).dense_domain.inter_of_isOpen_right hU U.2) inf_le_left := by
  ext
  · simp [ι_image_homOfLE_eq_ι_image_inf]
  · simp [morphismRestrict_comp, isoImage_ι_inv_morphismRestrict_homOfLE_assoc, isoOfEq_hom]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_restrict_right** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.Partial
Map Z) (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V <= g.domain) : f.comp (g.
restrict V hV hV') = (f.comp g).restrict (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ((f.doma
in.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense <| by simpa [← Set.nonempty_preimage_iff] using f.
hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty) (f.domain.ι.image_mono (f.
hom.preimage_mono hV'))
参数：f : X.PartialMap Y；g : Y.PartialMap Z；V : Y.Opens；hV : Dense (V : Set Y)；hV' 
: V <= g.domain。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `IsOpen.dense`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [
PreirreducibleSpace X], IsOpen s → s.Nonempty → Dense s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_inv_homOfLE_assoc`：∀ {X Y : Algebr
aicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U 
V : X.Opens) (e : U ≤ V)   {Z : AlgebraicGeom…
· 使用定理 `AlgebraicGeometry.morphismRestrict_homOfLE_assoc`：∀ {X Y : AlgebraicGeom
etry.Scheme} (f : X ⟶ Y) (U V : Y.Opens) (e : U ≤ V) {Z : AlgebraicGeometry.Sche
me} (h : ↑V ⟶ Z),   CategoryTheory.Cat…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_restrict_right (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    (V : Y.Opens) (hV : Dense (V : Set Y)) (hV' : V ≤ g.domain) :
    f.comp (g.restrict V hV hV') = (f.comp g).restrict
      (f.domain.ι ''ᵁ (f.hom ⁻¹ᵁ V)) ((f.domain.ι ''ᵁ f.hom ⁻¹ᵁ V).2.dense <| by
        simpa [← Set.nonempty_preimage_iff] using
          f.hom.denseRange.inter_open_nonempty _ V.2 hV.nonempty)
      (f.domain.ι.image_mono (f.hom.preimage_mono hV')) := by
  ext
  · simp
  · simp [← f.domain.ι.isoImage_inv_homOfLE_assoc _ _ (f.hom.preimage_mono hV'),
      ← morphismRestrict_homOfLE_assoc f.hom _ _ hV']

set_option backward.defeqAttrib.useBackward true in
/-- Composition respects equivalence of partial maps on the left. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_left** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_equiv_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsD
ominant f₂.hom] (h : f₁.equiv f₂) (g : Y.PartialMap Z) : (f₁.comp g).equiv (f₂.c
omp g)
参数：h : f₁.equiv f₂；g : Y.PartialMap Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_of_restrict_eq`：equiv_of_restr
ict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)} {hW₂ 
: Dense (W₂ : Set X)} {hW₁' : W₁ <= f.domain} …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `Dense.inter_of_isOpen_right`：Dense.inter_of_isOpen_right (hs : Dense s) 
(ht : Dense t) (hto : IsOpen t) : Dense (s inter t)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.dense_domain`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialMap Y), Dense ↑self.domain
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_restrict_left`：comp_restrict_le
ft (f : X.PartialMap Y) [IsDominant f.hom] (U : X.Opens) (hU : Dense (U : Set X)
) (hU' : U <= f.domain) (g : Y.PartialMap Z)…

--- 原说明 ---
Composition respects equivalence of partial maps on the left.
-/
lemma comp_equiv_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom]
    (h : f₁.equiv f₂) (g : Y.PartialMap Z) :
    (f₁.comp g).equiv (f₂.comp g) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : f₁.restrict W hW hW₁ = f₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr($(e).comp g)
  rw [comp_restrict_left, comp_restrict_left] at e
  exact equiv_of_restrict_eq _ _ e

set_option backward.defeqAttrib.useBackward true in
/-- Composition respects equivalence of partial maps on the right. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_right** 是 Mathlib 中的一个
引理，位于命名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ :
 Y.PartialMap Z} (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂)
参数：f : X.PartialMap Y；h : g₁.equiv g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equiv_of_restrict_eq`：equiv_of_restr
ict_eq (f g : X.PartialMap Y) {W₁ W₂ : X.Opens} {hW₁ : Dense (W₁ : Set X)} {hW₂ 
: Dense (W₂ : Set X)} {hW₁' : W₁ <= f.domain} …
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `IsOpen.dense`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X} [
PreirreducibleSpace X], IsOpen s → s.Nonempty → Dense s
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_mono`：image_mono {U V : X.Opens} (e :
 U <= V) : f ''ᵁ U <= f ''ᵁ V
· 使用引理 `AlgebraicGeometry.Scheme.Hom.preimage_mono`：preimage_mono {U U' : Y.Open
s} (hUU' : U <= U') : f ⁻¹ᵁ U <= f ⁻¹ᵁ U'
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_restrict_right`：comp_restrict_r
ight (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) (V : Y.Opens) 
(hV : Dense (V : Set Y)) (hV' : V <= g.domain…

--- 原说明 ---
Composition respects equivalence of partial maps on the right.
-/
lemma comp_equiv_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z}
    (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂) := by
  obtain ⟨W, hW, hW₁, hW₂, e⟩ := h
  replace e : g₁.restrict W hW hW₁ = g₂.restrict W hW hW₂ :=
    PartialMap.ext _ _ rfl (by simpa using e)
  replace e := congr(f.comp $e)
  rw [comp_restrict_right, comp_restrict_right] at e
  exact equiv_of_restrict_eq _ _ e

/-- Composition respects equivalence of partial maps in both arguments. -/
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDomina
nt f₂.hom] (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) : (f₁.
comp g₁).equiv (f₂.comp g₂)
参数：f₁ f₂ : X.PartialMap Y；hf : f₁.equiv f₂；g₁ g₂ : Y.PartialMap Z；hg : g₁.equiv 
g₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.equivalence_rel`：equivalence_rel : E
quivalence (@Scheme.PartialMap.equiv X Y) where refl
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_left`：comp_equiv
_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom] 
(h : f₁.equiv f₂) (g : Y.PartialMap Z) : (f₁.comp …
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_right`：comp_equi
v_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z
} (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂)

--- 原说明 ---
Composition respects equivalence of partial maps in both arguments.
-/
lemma comp_equiv_of_equiv (f₁ f₂ : X.PartialMap Y) [IsDominant f₁.hom] [IsDominant f₂.hom]
    (hf : f₁.equiv f₂) (g₁ g₂ : Y.PartialMap Z) (hg : g₁.equiv g₂) :
    (f₁.comp g₁).equiv (f₂.comp g₂) :=
  equivalence_rel.trans (comp_equiv_of_equiv_left hf _) (comp_equiv_of_equiv_right _ hg)

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.isDominant_comp_hom** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：isDominant_comp_hom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.Partial
Map Z) [IsDominant g.hom] : IsDominant (f.comp g).hom
参数：f : X.PartialMap Y；g : Y.PartialMap Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsZariskiLocalAtTarget.restrict`：restrict (hf : P f) (
U : Y.Opens) : P (f ∣_ U)
· 使用定理 `AlgebraicGeometry.IsDominant.isZariskiLocalAtTarget`：AlgebraicGeometry.I
sZariskiLocalAtTarget @AlgebraicGeometry.IsDominant
· 使用定理 `AlgebraicGeometry.instIsDominantCompScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsDominant f]   [AlgebraicGe
ometry.IsDominant g], AlgebraicG…
· 使用定理 `AlgebraicGeometry.instIsDominantOfSurjective`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], AlgebraicGeometry.IsDomin
ant f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
-/
instance isDominant_comp_hom (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z)
    [IsDominant g.hom] : IsDominant (f.comp g).hom := by
  dsimp only [comp_domain, comp_hom]
  have := IsZariskiLocalAtTarget.restrict ‹IsDominant f.hom› g.domain
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme.PartialMap`。
形式化陈述：comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [Irreducible
Space X₂] [Nonempty X₃] (f : X₁.PartialMap X₂) [IsDominant f.hom] (g : X₂.Partia
lMap X₃) [IsDominant g.hom] (h : X₃.PartialMap Y) : (f.comp g).comp h = f.comp (
g.comp h)
参数：f : X₁.PartialMap X₂；g : X₂.PartialMap X₃；h : X₃.PartialMap Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `AlgebraicGeometry.Scheme.Hom.inv_preimage`：inv_preimage {X Y : Scheme} (
e : X ≅ Y) (U : X.Opens) : e.inv ⁻¹ᵁ U = e.hom ''ᵁ U
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens), 
  CategoryTheory.CategoryStruct.c…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensFunctor.congr_simp`：∀ {X Y : Algebraic
Geometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenIm
mersion f],   AlgebraicGeometry.Scheme.Hom…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Hom.comp_image`：comp_image {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (U : X.Opens) [IsOpenImmersion f] [IsOpenImmersion g] : (f 
≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.image_morphismRestrict_preimage`：image_morphismRestric
t_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (V : Opens U) : (f ⁻¹ᵁ U
).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V) = f ⁻¹ᵁ (U.ι '…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_image_ι_isoImage_inv_assoc`：∀ {X Y 
: AlgebraicGeometry.Scheme} (f : X ⟶ Y) (U : Y.Opens) (V : (↑U).Opens) {Z : Alge
braicGeometry.Scheme}   (h : ↑V ⟶ Z),   CategoryTheor…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_le`：ι_image_le (W : U.toScheme.Op
ens) : U.ι ''ᵁ W <= U
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι`：morphismRestrict_ι {X Y : Scheme.{
u}} (f : X ⟶ Y) (U : Y.Opens) : f ∣_ U ≫ U.ι = (f ⁻¹ᵁ U).ι ≫ f
（共 36 条，此处仅展示前 30 条）
-/
lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f : X₁.PartialMap X₂) [IsDominant f.hom] (g : X₂.PartialMap X₃)
    [IsDominant g.hom] (h : X₃.PartialMap Y) :
    (f.comp g).comp h = f.comp (g.comp h) := by
  ext
  · simp_rw [comp_domain, comp_hom, ← Category.assoc, Hom.comp_preimage, Hom.inv_preimage,
      ← Hom.comp_image, Hom.isoImage_hom_ι, Hom.comp_image, image_morphismRestrict_preimage]
  · dsimp
    simp_rw [morphismRestrict_comp, morphismRestrict_ι_image_ι_isoImage_inv_assoc,
      Hom.comp_preimage, Category.assoc]
    conv_lhs => rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
    congr 1
    simp [← cancel_mono (Opens.ι _)]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_toPartialMap** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme.PartialMap`。
形式化陈述：comp_toPartialMap (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) : f.
comp g.toPartialMap = f.compHom g
参数：f : X.PartialMap Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_top_eq_opensRange`：image_top_eq_opens
Range : f ''ᵁ ⊤ = f.opensRange
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.morphismRestrict_ι_assoc`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) (U : Y.Opens) {Z : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   C
ategoryTheory.CategoryStruct.com…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用引理 `AlgebraicGeometry.Scheme.Opens.ι_image_le`：ι_image_le (W : U.toScheme.Op
ens) : U.ι ''ᵁ W <= U
· 使用定理 `AlgebraicGeometry.Scheme.Opens.isoImage_ι_inv_ι_assoc`：∀ {X : AlgebraicG
eometry.Scheme} (U : X.Opens) (V : (↑U).Opens) {Z : AlgebraicGeometry.Scheme} (h
 : ↑U ⟶ Z),   CategoryTheory.CategoryStruct…
-/
lemma comp_toPartialMap (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) :
    f.comp g.toPartialMap = f.compHom g := by
  ext1
  · simp
  · simp_rw [comp_hom, Hom.toPartialMap_domain, Hom.toPartialMap_hom, compHom_hom, topIso_hom,
      morphismRestrict_ι_assoc, f.domain.isoImage_ι_inv_ι_assoc, isoOfEq_hom]

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialMap.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.PartialMap`。
形式化陈述：comp_id (f : X.PartialMap Y) [IsDominant f.hom] : f.comp (PartialMap.id Y)
 = f
参数：f : X.PartialMap Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_toPartialMap`：comp_toPartialMap
 (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) : f.comp g.toPartialMap = f
.compHom g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.compHom_id`：compHom_id (f : X.Partia
lMap Y) : f.compHom (𝟙 Y) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_id (f : X.PartialMap Y) [IsDominant f.hom] : f.comp (PartialMap.id Y) = f := by simp

end PartialMap

namespace RationalMap

-- If better def-eqs are required, consider refactoring this by using `Quotient.liftOn₂`
-- and a bundled structure `DominantPartialMap`.
/-- Composition of rational maps. Requires `f` to be dominant, so that we may choose
a dominant representative. -/
/-
**AlgebraicGeometry.Scheme.RationalMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.RationalMap`。
形式化陈述：comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z
参数：f : X ⤏ Y；g : Y ⤏ Z。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantHomRepresentativeOfIsDominant`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y) [f.IsDominant],   Algebra
icGeometry.IsDominant f.representative.hom

--- 原说明 ---
Composition of rational maps. Requires `f` to be dominant, so that we may choose
a dominant representative.
-/
noncomputable def comp (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) : X ⤏ Z :=
  Quotient.liftOn g (PartialMap.toRationalMap ∘ f.representative.comp) <| fun _ _ h ↦ by
    rw [Function.comp_apply, Function.comp_apply, PartialMap.toRationalMap_eq_iff]
    exact PartialMap.comp_equiv_of_equiv_right _ h
/-
**AlgebraicGeometry.Scheme.RationalMap.comp_def** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.RationalMap`。
形式化陈述：comp_def (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z) : f.comp g.toRati
onalMap = (f.representative.comp g).toRationalMap
参数：f : X ⤏ Y；g : Y.PartialMap Z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_def (f : X ⤏ Y) [f.IsDominant] (g : Y.PartialMap Z) :
    f.comp g.toRationalMap = (f.representative.comp g).toRationalMap :=
  rfl
/-
**AlgebraicGeometry.Scheme.RationalMap.toRationalMap_comp** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：toRationalMap_comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialM
ap Z) : f.toRationalMap.comp g.toRationalMap = (f.comp g).toRationalMap
参数：f : X.PartialMap Y；g : Y.PartialMap Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantToRationalMapOfIsDominantHom`：∀ {
X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y) [AlgebraicGeometry.IsDomina
nt f.hom], f.toRationalMap.IsDominant
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantHomRepresentativeOfIsDominant`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y) [f.IsDominant],   Algebra
icGeometry.IsDominant f.representative.hom
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.RationalMap.comp_def`：comp_def (f : X ⤏ Y) [f.I
sDominant] (g : Y.PartialMap Z) : f.comp g.toRationalMap = (f.representative.com
p g).toRationalMap
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff`：∀ {X Y : Algeb
raicGeometry.Scheme} {f g : X.PartialMap Y}, f.toRationalMap = g.toRationalMap ↔
 f.equiv g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_left`：comp_equiv
_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom] 
(h : f₁.equiv f₂) (g : Y.PartialMap Z) : (f₁.comp …
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.representative_toRationalMap_equiv`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.toRationalMap.represe
ntative.equiv f
-/
lemma toRationalMap_comp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) :
    f.toRationalMap.comp g.toRationalMap = (f.comp g).toRationalMap := by
  rw [RationalMap.comp_def, PartialMap.toRationalMap_eq_iff]
  exact PartialMap.comp_equiv_of_equiv_left f.representative_toRationalMap_equiv _

@[simp]
/-
**AlgebraicGeometry.Scheme.RationalMap.comp_id** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme.RationalMap`。
形式化陈述：comp_id (f : X ⤏ Y) [f.IsDominant] : f.comp (RationalMap.id Y) = f
参数：f : X ⤏ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantHomRepresentativeOfIsDominant`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y) [f.IsDominant],   Algebra
icGeometry.IsDominant f.representative.hom
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_toPartialMap`：comp_toPartialMap
 (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) : f.comp g.toPartialMap = f
.compHom g
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.compHom_id`：compHom_id (f : X.Partia
lMap Y) : f.compHom (𝟙 Y) = f
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative.toRational
Map = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_id (f : X ⤏ Y) [f.IsDominant] : f.comp (RationalMap.id Y) = f := by
  simp [RationalMap.comp_def]
/-
**AlgebraicGeometry.Scheme.RationalMap.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeom
etry.Scheme.RationalMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⤏ Y) [f.IsDominant] (g : Y ⤏ Z) [g.IsDominant] : (f.comp g).IsDominant := by
  rw [← g.toRationalMap_representative, RationalMap.comp_def]
  infer_instance
/-
**AlgebraicGeometry.Scheme.RationalMap.comp_toRationalMap** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.RationalMap`。
形式化陈述：comp_toRationalMap (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z) : f.comp h.toRat
ionalMap = f.compHom h
参数：f : X ⤏ Y；h : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantHomRepresentativeOfIsDominant`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y) [f.IsDominant],   Algebra
icGeometry.IsDominant f.representative.hom
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_toPartialMap`：comp_toPartialMap
 (f : X.PartialMap Y) [IsDominant f.hom] (g : Y ⟶ Z) : f.comp g.toPartialMap = f
.compHom g
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative.toRational
Map = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_toRationalMap (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z) :
    f.comp h.toRationalMap = f.compHom h := by
  simp [comp_def, PartialMap.comp_toPartialMap]

@[grind _=_]
/-
**AlgebraicGeometry.Scheme.RationalMap.comp_assoc** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.RationalMap`。
形式化陈述：comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [Irreducible
Space X₂] [Nonempty X₃] (f₁ : X₁ ⤏ X₂) [f₁.IsDominant] (f₂ : X₂ ⤏ X₃) [f₂.IsDomi
nant] (f₃ : X₃ ⤏ Y) : (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃)
参数：f₁ : X₁ ⤏ X₂；f₂ : X₂ ⤏ X₃；f₃ : X₃ ⤏ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.instIsDominantComp`：∀ {X Y Z : Alge
braicGeometry.Scheme} [inst : PreirreducibleSpace ↥X] [inst_1 : Nonempty ↥Y] (f 
: X.RationalMap Y)   [inst_2 : f.IsDominant] …
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative.toRational
Map = f
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantHomRepresentativeOfIsDominant`：∀ 
{X Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y) [f.IsDominant],   Algebra
icGeometry.IsDominant f.representative.hom
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_left`：comp_equiv
_of_equiv_left {f₁ f₂ : X.PartialMap Y} [IsDominant f₁.hom] [IsDominant f₂.hom] 
(h : f₁.equiv f₂) (g : Y.PartialMap Z) : (f₁.comp …
· 使用引理 `AlgebraicGeometry.Scheme.RationalMap.comp_def`：comp_def (f : X ⤏ Y) [f.I
sDominant] (g : Y.PartialMap Z) : f.comp g.toRationalMap = (f.representative.com
p g).toRationalMap
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.equiv.trans`：∀ {X Y : AlgebraicGeome
try.Scheme} {f g h : X.PartialMap Y}, f.equiv g → g.equiv h → f.equiv h
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.representative_toRationalMap_equiv`：
∀ {X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y), f.toRationalMap.represe
ntative.equiv f
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.comp_equiv_of_equiv_right`：comp_equi
v_of_equiv_right (f : X.PartialMap Y) [IsDominant f.hom] {g₁ g₂ : Y.PartialMap Z
} (h : g₁.equiv g₂) : (f.comp g₁).equiv (f.comp g₂)
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.equiv.refl`：∀ {X Y : AlgebraicGeomet
ry.Scheme} (f : X.PartialMap Y), f.equiv f
-/
lemma comp_assoc {X₁ X₂ X₃ Y : Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂]
    [Nonempty X₃] (f₁ : X₁ ⤏ X₂) [f₁.IsDominant] (f₂ : X₂ ⤏ X₃) [f₂.IsDominant] (f₃ : X₃ ⤏ Y) :
    (f₁.comp f₂).comp f₃ = f₁.comp (f₂.comp f₃) := by
  rw [← f₃.toRationalMap_representative]
  simp_rw [comp_def, ← PartialMap.comp_assoc, PartialMap.toRationalMap_eq_iff]
  apply PartialMap.comp_equiv_of_equiv_left
  rw [← f₂.toRationalMap_representative, comp_def]
  apply (f₁.representative.comp f₂.representative).representative_toRationalMap_equiv.trans
  apply PartialMap.comp_equiv_of_equiv_right
  rw [toRationalMap_representative]
/-
**AlgebraicGeometry.Scheme.RationalMap.isOver_comp** 是 Mathlib 中的一个实例，位于命名空间 `Al
gebraicGeometry.Scheme.RationalMap`。
形式化陈述：isOver_comp {S : Scheme.{u}} [IrreducibleSpace Y] [Nonempty Z] [X.Over S] 
[Y.Over S] [Z.Over S] (f : X ⤏ Y) [f.IsDominant] [f.IsOver S] (g : Y ⤏ Z) [g.IsD
ominant] [g.IsOver S] : (f.comp g).IsOver S
参数：f : X ⤏ Y；g : Y ⤏ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.isOver_iff`：∀ {X Y S : AlgebraicGeo
metry.Scheme} [inst : X.Over S] [inst_1 : Y.Over S] {f : X.RationalMap Y},   Alg
ebraicGeometry.Scheme.RationalMap.IsO…
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.instIsDominantComp`：∀ {X Y Z : Alge
braicGeometry.Scheme} [inst : PreirreducibleSpace ↥X] [inst_1 : Nonempty ↥Y] (f 
: X.RationalMap Y)   [inst_2 : f.IsDominant] …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.RationalMap.comp_toRationalMap`：comp_toRational
Map (f : X ⤏ Y) [f.IsDominant] (h : Y ⟶ Z) : f.comp h.toRationalMap = f.compHom 
h
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用引理 `AlgebraicGeometry.Scheme.RationalMap.comp_assoc`：comp_assoc {X₁ X₂ X₃ Y 
: Scheme.{u}} [PreirreducibleSpace X₁] [IrreducibleSpace X₂] [Nonempty X₃] (f₁ :
 X₁ ⤏ X₂) [f₁.IsDominant] (f₂ : X₂ ⤏ …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
instance isOver_comp {S : Scheme.{u}} [IrreducibleSpace Y] [Nonempty Z] [X.Over S] [Y.Over S]
    [Z.Over S] (f : X ⤏ Y) [f.IsDominant] [f.IsOver S] (g : Y ⤏ Z) [g.IsDominant] [g.IsOver S] :
    (f.comp g).IsOver S := by
  rw [isOver_iff, ← comp_toRationalMap, comp_assoc, comp_toRationalMap,
    isOver_iff.mp ‹g.IsOver S›, comp_toRationalMap, RationalMap.isOver_iff.mp ‹f.IsOver S›]

end RationalMap

end PreirreducibleSpace

set_option backward.defeqAttrib.useBackward true in
@[simp]
/-
**AlgebraicGeometry.Scheme.PartialMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.PartialMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : IrreducibleSpace ↥X] (f : X.Par
tialMap Y),   (AlgebraicGeometry.Scheme.PartialMap.id X).comp f = f
参数：f : X.PartialMap Y；AlgebraicGeometry.Scheme.PartialMap.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.PartialMap.ext`：ext (f g : X.PartialMap Y) (e :
 f.domain = g.domain) (H : f.hom = (X.isoOfEq e).hom ≫ g.hom) : f = g
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.instIsDominantHomToPartialMap`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f],   Al
gebraicGeometry.IsDominant (AlgebraicGeometry.Scheme.Ho…
· 使用定理 `AlgebraicGeometry.instIsDominantOfSurjective`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], AlgebraicGeometry.IsDomin
ant f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso`：∀ {Y Z : 
AlgebraicGeometry.LocallyRingedSpace} (g : Y ⟶ Z) [CategoryTheory.IsIso g],   Al
gebraicGeometry.LocallyRingedSpace.IsOpenImmersion …
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.comp`：∀ {X Y Z : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.IsOpenImmersion f]   [AlgebraicG
eometry.IsOpenImmersion g], …
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensFunctor.congr_simp`：∀ {X Y : Algebraic
Geometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenIm
mersion f],   AlgebraicGeometry.Scheme.Hom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `AlgebraicGeometry.Scheme.Hom.id_image`：id_image {X : Scheme} (U : X.Open
s) : 𝟙 X ''ᵁ U = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.morphismRestrict_comp`：morphismRestrict_comp {X Y Z : 
Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z) : (f ≫ g) ∣_ U = f ∣_ g ⁻¹ᵁ U 
≫ g ∣_ U
· 使用引理 `AlgebraicGeometry.morphismRestrict_id`：morphismRestrict_id {X : Scheme.{
u}} (U : X.Opens) : 𝟙 X ∣_ U = 𝟙 _
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `AlgebraicGeometry.Scheme.Hom.image_preimage_le`：image_preimage_le (U : Y
.Opens) : f ''ᵁ f ⁻¹ᵁ U <= U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_preimage_hom_homOfLE`：∀ {X Y : Alg
ebraicGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] 
(U : Y.Opens),   CategoryTheory.CategoryStruct.c…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma PartialMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X.PartialMap Y) :
    (PartialMap.id X).comp f = f := by
  ext1
  · simp_rw [comp_domain, Hom.toPartialMap_domain, Hom.toPartialMap_hom, Category.comp_id,
      ← X.topIso_hom, ← Hom.inv_image, ← Hom.comp_image, Iso.inv_hom_id, Hom.id_image]
  · simp_rw [comp_hom, Hom.toPartialMap_hom, Hom.toPartialMap_domain, morphismRestrict_comp,
      morphismRestrict_id, ← X.topIso_hom, Hom.comp_preimage, Hom.id_preimage,
      Category.comp_id, ← X.topIso.hom.isoImage_preimage_hom_homOfLE, Category.assoc,
      Iso.inv_hom_id_assoc]
    rfl

@[simp, grind =]
/-
**AlgebraicGeometry.Scheme.RationalMap.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.RationalMap`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} [inst : IrreducibleSpace ↥X] (f : X.Rat
ionalMap Y),   (AlgebraicGeometry.Scheme.RationalMap.id X).comp f = f
参数：f : X.RationalMap Y；AlgebraicGeometry.Scheme.RationalMap.id X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IrreducibleSpace.toPreirreducibleSpace`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : IrreducibleSpace X], PreirreducibleSpace X
· 使用定理 `ConnectedSpace.toNonempty`：∀ {α : Type u} {inst : TopologicalSpace α} [s
elf : ConnectedSpace α], Nonempty α
· 使用定理 `IrreducibleSpace.connectedSpace`：∀ (α : Type u) [inst : TopologicalSpace
 α] [IrreducibleSpace α], ConnectedSpace α
· 使用定理 `AlgebraicGeometry.Scheme.instIsDominantToRationalMapOfIsDominantHom`：∀ {
X Y : AlgebraicGeometry.Scheme} (f : X.PartialMap Y) [AlgebraicGeometry.IsDomina
nt f.hom], f.toRationalMap.IsDominant
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.instIsDominantHomToPartialMap`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f],   Al
gebraicGeometry.IsDominant (AlgebraicGeometry.Scheme.Ho…
· 使用定理 `AlgebraicGeometry.instIsDominantOfSurjective`：∀ {X Y : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f], AlgebraicGeometry.IsDomin
ant f
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_representative`：∀ {X 
Y : AlgebraicGeometry.Scheme} (f : X.RationalMap Y), f.representative.toRational
Map = f
· 使用引理 `AlgebraicGeometry.Scheme.RationalMap.toRationalMap_comp`：toRationalMap_c
omp (f : X.PartialMap Y) [IsDominant f.hom] (g : Y.PartialMap Z) : f.toRationalM
ap.comp g.toRationalMap = (f.comp g).toRation…
· 使用定理 `AlgebraicGeometry.Scheme.PartialMap.id_comp`：∀ {X Y : AlgebraicGeometry.
Scheme} [inst : IrreducibleSpace ↥X] (f : X.PartialMap Y),   (AlgebraicGeometry.
Scheme.PartialMap.id X).comp f = …
-/
lemma RationalMap.id_comp {X Y : Scheme.{u}} [IrreducibleSpace X] (f : X ⤏ Y) :
    (RationalMap.id X).comp f = f := by
  rw [← f.toRationalMap_representative, toRationalMap_comp, PartialMap.id_comp]

end AlgebraicGeometry.Scheme

