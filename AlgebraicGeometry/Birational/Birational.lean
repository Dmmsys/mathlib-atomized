/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# Birationality and Rationality of schemes.

This file defines partial isomorphisms between schemes and uses them to formalize
birationality and rationality.

## Main definitions

- `Scheme.PartialIso X Y`: an isomorphism between a dense open subscheme of `X` and a
  dense open subscheme of `Y`.
- `Scheme.Birational X Y`: `X` and `Y` are birational, i.e. there exists a `PartialIso X Y`.
- `Scheme.BirationalOver sX sY`: `X` and `Y` are birational over `S` via structure maps
  `sX : X ⟶ S` and `sY : Y ⟶ S`.
- `Scheme.IsRationalOver sX`: `X` is rational over `S` via structure map `sX : X ⟶ S`,
  i.e. birational over `S` to some affine space `𝔸(n; S)`.

-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A partial isomorphism from `X` to `Y` is an isomorphism between dense open subschemes
of `X` and `Y`. -/
/-
**AlgebraicGeometry.Scheme.PartialIso** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → AlgebraicGeometry.Scheme → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial isomorphism from `X` to `Y` is an isomorphism between dense open subsc
hemes
of `X` and `Y`.
-/
structure PartialIso (X Y : Scheme.{u}) where
  /-- The source open subscheme of a partial isomorphism. -/
  source : X.Opens
  dense_source : Dense (source : Set X)
  /-- The target open subscheme of a partial isomorphism. -/
  target : Y.Opens
  dense_target : Dense (target : Set Y)
  /-- The underlying isomorphism of a partial isomorphism. -/
  iso : source.toScheme ≅ target.toScheme

namespace PartialIso

variable {X Y Z S : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}

variable (sX sY) in
/-- A partial iso is an `S`-map if the underlying morphism is. -/
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algebr
aicGeometry.Scheme.PartialIso`。
形式化陈述：IsOver (f : X.PartialIso Y) : Prop
参数：f : X.PartialIso Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partial iso is an `S`-map if the underlying morphism is.
-/
abbrev IsOver (f : X.PartialIso Y) : Prop :=
  f.iso.hom ≫ f.target.ι ≫ sY = f.source.ι ≫ sX
/-
**AlgebraicGeometry.Scheme.PartialIso.ext_iff** 是 Mathlib 中的一个引理，位于命名空间 `Algebra
icGeometry.Scheme.PartialIso`。
形式化陈述：ext_iff (f g : X.PartialIso Y) : f = g ↔ exists (e : f.source = g.source) 
(e' : g.target = f.target), f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e'
参数：f g : X.PartialIso Y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.mk.injEq`：∀ {X Y : AlgebraicGeometry
.Scheme} (source : X.Opens) (dense_source : Dense ↑source) (target : Y.Opens)   
(dense_target : Dense ↑target) (is…
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma ext_iff (f g : X.PartialIso Y) :
    f = g ↔ ∃ (e : f.source = g.source) (e' : g.target = f.target),
      f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e' := by
  constructor
  · rintro rfl
    simp
  · obtain ⟨U₁, hU₁, U₂, hU₂, f⟩ := f
    obtain ⟨V₁, hV₁, V₂, hU₂, g⟩ := g
    simp only [forall_exists_index]
    rintro rfl rfl e
    simpa using e

@[ext]
/-
**AlgebraicGeometry.Scheme.PartialIso.ext** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.PartialIso`。
形式化陈述：ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.ta
rget) (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g
参数：f g : X.PartialIso Y；e : f.source = g.source；e' : g.target = f.target；H : f.i
so = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `AlgebraicGeometry.Scheme.PartialIso.ext_iff`：ext_iff (f g : X.PartialIso
 Y) : f = g ↔ exists (e : f.source = g.source) (e' : g.target = f.target), f.iso
 = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoO…
-/
lemma ext (f g : X.PartialIso Y) (e : f.source = g.source) (e' : g.target = f.target)
    (H : f.iso = X.isoOfEq e ≪≫ g.iso ≪≫ Y.isoOfEq e') : f = g := by
  rw [ext_iff]
  exact ⟨e, e', H⟩

variable (X) in
/-- The identity partial isomorphism on `X`, defined on all of `X`. -/
@[refl, simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.refl** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.PartialIso`。
形式化陈述：refl : X.PartialIso X where source
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity partial isomorphism on `X`, defined on all of `X`.
-/
def refl : X.PartialIso X where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := Iso.refl _

/-- The inverse of a partial isomorphism. -/
@[symm, simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.symm** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicG
eometry.Scheme.PartialIso`。
形式化陈述：symm (f : X.PartialIso Y) : Y.PartialIso X where source
参数：f : X.PartialIso Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.dense_target`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialIso Y), Dense ↑self.target
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.dense_source`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialIso Y), Dense ↑self.source

--- 原说明 ---
The inverse of a partial isomorphism.
-/
def symm (f : X.PartialIso Y) : Y.PartialIso X where
  source := f.target
  dense_source := f.dense_target
  target := f.source
  dense_target := f.dense_source
  iso := f.iso.symm

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver.symm** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.PartialIso.IsOver`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.Part
ialIso Y},   AlgebraicGeometry.Scheme.PartialIso.IsOver sX sY f → AlgebraicGeome
try.Scheme.PartialIso.IsOver sY sX f.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `CategoryTheory.instEffectiveEpiOfIsIso`：∀ {C : Type u_1} [inst : Categor
yTheory.Category.{v_1, u_1} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsIso f],  
 CategoryTheory.EffectiveEpi…
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
-/
lemma IsOver.symm {f : X.PartialIso Y} (hf : f.IsOver sX sY) : f.symm.IsOver sY sX := by
  simpa [IsOver, ← cancel_epi f.iso.hom] using Eq.symm hf

/-- Compose two partial isomorphisms along a proof that the target of `f` equals the source
of `g`. See `trans` for the version that does not require this. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.trans'** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme.PartialIso`。
形式化陈述：trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source)
 : X.PartialIso Z where source
参数：f : X.PartialIso Y；g : Y.PartialIso Z；e : f.target = g.source。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.dense_source`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialIso Y), Dense ↑self.source
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.dense_target`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialIso Y), Dense ↑self.target

--- 原说明 ---
Compose two partial isomorphisms along a proof that the target of `f` equals the
 source
of `g`. See `trans` for the version that does not require this.
-/
noncomputable def trans' (f : X.PartialIso Y) (g : Y.PartialIso Z) (e : f.target = g.source) :
    X.PartialIso Z where
  source := f.source
  dense_source := f.dense_source
  target := g.target
  dense_target := g.dense_target
  iso := f.iso ≪≫ Y.isoOfEq e ≪≫ g.iso

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver.trans'** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Scheme.PartialIso.IsOver`。
形式化陈述：∀ {X Y Z S : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶
 S} {f : X.PartialIso Y} {g : Y.PartialIso Z}   {e : f.target = g.source},   Alg
ebraicGeometry.Scheme.PartialIso.IsOver sX sY f →     AlgebraicGeometry.Scheme.P
artialIso.IsOver sY sZ g → AlgebraicGeometry.Scheme.PartialIso.IsOver sX sZ (f.t
rans' g e)
参数：f.trans' g e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_hom_ι_assoc`：∀ (X : AlgebraicGeometry.S
cheme) {U V : X.Opens} (e : U = V) {Z : AlgebraicGeometry.Scheme} (h : X ⟶ Z),  
 CategoryTheory.CategoryStruct.com…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsOver.trans' {f : X.PartialIso Y} {g : Y.PartialIso Z} {e : f.target = g.source}
    (hf : f.IsOver sX sY) (hg : g.IsOver sY sZ) : (trans' f g e).IsOver sX sZ := by
  simp [IsOver, ← hf, hg]

/-- Restrict the source of a partial isomorphism to a smaller dense open. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.restrictSource** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.PartialIso`。
形式化陈述：restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
 (hU' : U <= f.source) : X.PartialIso Y where source
参数：f : X.PartialIso Y；U : Opens X；hU : Dense (U : Set X)；hU' : U <= f.source。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the source of a partial isomorphism to a smaller dense open.
-/
noncomputable def restrictSource (f : X.PartialIso Y) (U : Opens X) (hU : Dense (U : Set X))
    (hU' : U ≤ f.source) : X.PartialIso Y where
  source := U
  dense_source := hU
  target := f.target.ι ''ᵁ f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U
  dense_target :=
    have := Opens.isDominant_ι f.dense_target
    f.target.ι.denseRange.dense_image f.target.ι.continuous <|
      f.iso.hom.denseRange.dense_image f.iso.hom.continuous <|
        hU.preimage f.source.ι.isOpenEmbedding.isOpenMap
  iso := (Opens.isoOfLE hU').symm ≪≫
    (f.iso.hom.isoImage (f.source.ι ⁻¹ᵁ U)) ≪≫
    (f.target.ι.isoImage (f.iso.hom ''ᵁ f.source.ι ⁻¹ᵁ U))

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver.restrictSource** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.PartialIso.IsOver`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.Part
ialIso Y},   AlgebraicGeometry.Scheme.PartialIso.IsOver sX sY f →     ∀ (U : X.O
pens) (hU : Dense ↑U) (hU' : U ≤ f.source),       AlgebraicGeometry.Scheme.Parti
alIso.IsOver sX sY (f.restrictSource U hU hU')
参数：U : X.Opens；hU : Dense ↑U；hU' : U ≤ f.source；f.restrictSource U hU hU'。
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
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoImage_hom_ι_assoc`：∀ {X Y : AlgebraicGeo
metry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f] (U : X.Op
ens)   {Z : AlgebraicGeometry.Scheme} (…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.isoOfLE_inv_ι_assoc`：∀ {X : AlgebraicGeom
etry.Scheme} {U V : X.Opens} (hUV : U ≤ V) {Z : AlgebraicGeometry.Scheme} (h : X
 ⟶ Z),   CategoryTheory.CategoryStruct.c…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsOver.restrictSource {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens X)
    (hU : Dense (U : Set X)) (hU' : U ≤ f.source) :
    (f.restrictSource U hU hU').IsOver sX sY := by
  simp [IsOver, hf]

/-- Restrict the target of a partial isomorphism to a smaller dense open. -/
@[simps! source target iso]
/-
**AlgebraicGeometry.Scheme.PartialIso.restrictTarget** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.PartialIso`。
形式化陈述：restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
 (hU' : U <= f.target) : X.PartialIso Y
参数：f : X.PartialIso Y；U : Opens Y；hU : Dense (U : Set Y)；hU' : U <= f.target。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the target of a partial isomorphism to a smaller dense open.
-/
noncomputable def restrictTarget (f : X.PartialIso Y) (U : Opens Y) (hU : Dense (U : Set Y))
    (hU' : U ≤ f.target) : X.PartialIso Y :=
  (f.symm.restrictSource U hU hU').symm
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver.restrictTarget** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.PartialIso.IsOver`。
形式化陈述：∀ {X Y S : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.Part
ialIso Y},   AlgebraicGeometry.Scheme.PartialIso.IsOver sX sY f →     ∀ (U : Y.O
pens) (hU : Dense ↑U) (hU' : U ≤ f.target),       AlgebraicGeometry.Scheme.Parti
alIso.IsOver sX sY (f.restrictTarget U hU hU')
参数：U : Y.Opens；hU : Dense ↑U；hU' : U ≤ f.target；f.restrictTarget U hU hU'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.symm`：∀ {X Y S : AlgebraicGeo
metry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.PartialIso Y},   AlgebraicGeometr
y.Scheme.PartialIso.IsOver sX sY f → …
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.restrictSource`：∀ {X Y S : Al
gebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.PartialIso Y},   Algebr
aicGeometry.Scheme.PartialIso.IsOver sX sY f → …
-/
lemma IsOver.restrictTarget {f : X.PartialIso Y} (hf : f.IsOver sX sY) (U : Opens Y)
    (hU : Dense (U : Set Y)) (hU' : U ≤ f.target) :
    (f.restrictTarget U hU hU').IsOver sX sY :=
  (hf.symm.restrictSource U hU hU').symm

/-- Compose two partial isomorphisms, restricting to the intersection of the intermediate opens. -/
@[trans, simps! source target iso]
/-
**AlgebraicGeometry.Scheme.PartialIso.trans** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.PartialIso`。
形式化陈述：trans (f : X.PartialIso Y) (g : Y.PartialIso Z) : X.PartialIso Z
参数：f : X.PartialIso Y；g : Y.PartialIso Z。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose two partial isomorphisms, restricting to the intersection of the interme
diate opens.
-/
noncomputable def trans (f : X.PartialIso Y) (g : Y.PartialIso Z) : X.PartialIso Z :=
  have := f.dense_target.inter_of_isOpen_right g.dense_source g.source.2
  (f.restrictTarget _ this inf_le_left).trans' (g.restrictSource _ this inf_le_right) rfl
/-
**AlgebraicGeometry.Scheme.PartialIso.IsOver.trans** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry.Scheme.PartialIso.IsOver`。
形式化陈述：∀ {X Y Z S : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶
 S} {f : X.PartialIso Y} {g : Y.PartialIso Z},   AlgebraicGeometry.Scheme.Partia
lIso.IsOver sX sY f →     AlgebraicGeometry.Scheme.PartialIso.IsOver sY sZ g → A
lgebraicGeometry.Scheme.PartialIso.IsOver sX sZ (f.trans g)
参数：f.trans g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.trans'`：∀ {X Y Z S : Algebrai
cGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S} {f : X.PartialIso Y} {g
 : Y.PartialIso Z}   {e : f.target = g.…
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.restrictTarget`：∀ {X Y S : Al
gebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.PartialIso Y},   Algebr
aicGeometry.Scheme.PartialIso.IsOver sX sY f → …
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.restrictSource`：∀ {X Y S : Al
gebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.PartialIso Y},   Algebr
aicGeometry.Scheme.PartialIso.IsOver sX sY f → …
-/
lemma IsOver.trans {f : X.PartialIso Y} {g : Y.PartialIso Z} (hf : f.IsOver sX sY)
    (hg : g.IsOver sY sZ) : (f.trans g).IsOver sX sZ :=
  (hf.restrictTarget _ _ _).trans' (hg.restrictSource _ _ _)

/-- The underlying partial map of a partial isomorphism. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.toPartialMap** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.PartialIso`。
形式化陈述：toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where domain
参数：f : X.PartialIso Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.dense_source`：∀ {X Y : AlgebraicGeom
etry.Scheme} (self : X.PartialIso Y), Dense ↑self.source

--- 原说明 ---
The underlying partial map of a partial isomorphism.
-/
def toPartialMap (f : X.PartialIso Y) : X.PartialMap Y where
  domain := f.source
  dense_domain := f.dense_source
  hom := f.iso.hom ≫ f.target.ι

/-- The underlying rational map of a partial isomorphism. -/
/-
**AlgebraicGeometry.Scheme.PartialIso.toRationalMap** 是 Mathlib 中的一个缩写定义，位于命名空间 
`AlgebraicGeometry.Scheme.PartialIso`。
形式化陈述：toRationalMap (f : X.PartialIso Y) : X ⤏ Y
参数：f : X.PartialIso Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying rational map of a partial isomorphism.
-/
abbrev toRationalMap (f : X.PartialIso Y) : X ⤏ Y := f.toPartialMap.toRationalMap

/-- A scheme isomorphism viewed as a partial isomorphism defined on all of `X` and `Y`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.PartialIso.ofIso** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Scheme.PartialIso`。
形式化陈述：ofIso (f : X ≅ Y) : X.PartialIso Y where source
参数：f : X ≅ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme isomorphism viewed as a partial isomorphism defined on all of `X` and `
Y`.
-/
noncomputable def ofIso (f : X ≅ Y) : X.PartialIso Y where
  source := ⊤
  dense_source := dense_univ
  target := ⊤
  dense_target := dense_univ
  iso := X.topIso ≪≫ f ≪≫ Y.topIso.symm

end PartialIso

/-- `X` and `Y` are birational if there exists a partial isomorphism between them. -/
@[stacks 0A20 "(1)"]
/-
**AlgebraicGeometry.Scheme.Birational** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeomet
ry.Scheme`。
形式化陈述：Birational (X Y : Scheme.{u}) : Prop
参数：X Y : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` and `Y` are birational if there exists a partial isomorphism between them.
-/
def Birational (X Y : Scheme.{u}) : Prop := Nonempty (PartialIso X Y)

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational. -/
/-
**AlgebraicGeometry.Scheme.Birational.partialIso** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme.Birational`。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → X.Birational Y → X.PartialIso Y
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choose a partial isomorphism witnessing that `X` and `Y` are birational.
-/
noncomputable def Birational.partialIso {X Y : Scheme.{u}} (h : Birational X Y) :
    PartialIso X Y :=
  Classical.choice h

@[refl]
/-
**AlgebraicGeometry.Scheme.Birational.refl** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Birational`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme), X.Birational X
参数：X : AlgebraicGeometry.Scheme。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Birational.refl (X : Scheme.{u}) : Birational X X :=
  ⟨.refl X⟩

@[symm]
/-
**AlgebraicGeometry.Scheme.Birational.symm** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicG
eometry.Scheme.Birational`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme}, X.Birational Y → Y.Birational X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Birational.symm {X Y : Scheme.{u}} (h : Birational X Y) : Birational Y X :=
  ⟨h.partialIso.symm⟩

@[trans]
/-
**AlgebraicGeometry.Scheme.Birational.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algebraic
Geometry.Scheme.Birational`。
形式化陈述：∀ {X Y Z : AlgebraicGeometry.Scheme}, X.Birational Y → Y.Birational Z → X.
Birational Z
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Birational.trans {X Y Z : Scheme.{u}} (h₁ : Birational X Y) (h₂ : Birational Y Z) :
    Birational X Z :=
  ⟨h₁.partialIso.trans h₂.partialIso⟩

/-- `X` and `Y` are birational over `S` if there exists a partial isomorphism between them
that is compatible with the structure maps to `S`. -/
/-
**AlgebraicGeometry.Scheme.BirationalOver** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme`。
形式化陈述：BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop
参数：sX : X ⟶ S；sY : Y ⟶ S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` and `Y` are birational over `S` if there exists a partial isomorphism betwee
n them
that is compatible with the structure maps to `S`.
-/
def BirationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S) : Prop :=
  ∃ f : PartialIso X Y, f.IsOver sX sY

/-- Choose a partial isomorphism witnessing that `X` and `Y` are birational over `S`. -/
/-
**AlgebraicGeometry.Scheme.BirationalOver.partialIso** 是 Mathlib 中的一个定义，位于命名空间 `
AlgebraicGeometry.Scheme.BirationalOver`。
形式化陈述：{S X Y : AlgebraicGeometry.Scheme} →   (sX : X ⟶ S) → (sY : Y ⟶ S) → Algeb
raicGeometry.Scheme.BirationalOver sX sY → X.PartialIso Y
参数：sX : X ⟶ S；sY : Y ⟶ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choose a partial isomorphism witnessing that `X` and `Y` are birational over `S`
.
-/
noncomputable def BirationalOver.partialIso {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) :=
  h.choose
/-
**AlgebraicGeometry.Scheme.BirationalOver.partialIso_isOver** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme.BirationalOver`。
形式化陈述：∀ {S X Y : AlgebraicGeometry.Scheme} (sX : X ⟶ S) (sY : Y ⟶ S) (h : Algebr
aicGeometry.Scheme.BirationalOver sX sY),   AlgebraicGeometry.Scheme.PartialIso.
IsOver sX sY (AlgebraicGeometry.Scheme.BirationalOver.partialIso sX sY h)
参数：sX : X ⟶ S；sY : Y ⟶ S；h : AlgebraicGeometry.Scheme.BirationalOver sX sY；Algeb
raicGeometry.Scheme.BirationalOver.partialIso sX sY h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma BirationalOver.partialIso_isOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    (h : BirationalOver sX sY) : h.partialIso.IsOver sX sY :=
  h.choose_spec

set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.BirationalOver.refl** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.BirationalOver`。
形式化陈述：∀ {S X : AlgebraicGeometry.Scheme} (sX : X ⟶ S), AlgebraicGeometry.Scheme.
BirationalOver sX sX
参数：sX : X ⟶ S。
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
lemma BirationalOver.refl {S X : Scheme.{u}} (sX : X ⟶ S) : BirationalOver sX sX :=
  ⟨.refl X, by simp [PartialIso.IsOver]⟩
/-
**AlgebraicGeometry.Scheme.BirationalOver.symm** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
aicGeometry.Scheme.BirationalOver`。
形式化陈述：∀ {S X Y : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S},   Algebrai
cGeometry.Scheme.BirationalOver sX sY → AlgebraicGeometry.Scheme.BirationalOver 
sY sX
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.symm`：∀ {X Y S : AlgebraicGeo
metry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {f : X.PartialIso Y},   AlgebraicGeometr
y.Scheme.PartialIso.IsOver sX sY f → …
· 使用定理 `AlgebraicGeometry.Scheme.BirationalOver.partialIso_isOver`：∀ {S X Y : Al
gebraicGeometry.Scheme} (sX : X ⟶ S) (sY : Y ⟶ S) (h : AlgebraicGeometry.Scheme.
BirationalOver sX sY),   AlgebraicGeometry.Sche…
-/
lemma BirationalOver.symm {S X Y : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S}
    (h : BirationalOver sX sY) : BirationalOver sY sX :=
  ⟨h.partialIso.symm, h.partialIso_isOver.symm⟩
/-
**AlgebraicGeometry.Scheme.BirationalOver.trans** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Scheme.BirationalOver`。
形式化陈述：∀ {S X Y Z : AlgebraicGeometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶
 S},   AlgebraicGeometry.Scheme.BirationalOver sX sY →     AlgebraicGeometry.Sch
eme.BirationalOver sY sZ → AlgebraicGeometry.Scheme.BirationalOver sX sZ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.PartialIso.IsOver.trans`：∀ {X Y Z S : Algebraic
Geometry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S} {f : X.PartialIso Y} {g 
: Y.PartialIso Z},   AlgebraicGeometry…
· 使用定理 `AlgebraicGeometry.Scheme.BirationalOver.partialIso_isOver`：∀ {S X Y : Al
gebraicGeometry.Scheme} (sX : X ⟶ S) (sY : Y ⟶ S) (h : AlgebraicGeometry.Scheme.
BirationalOver sX sY),   AlgebraicGeometry.Sche…
-/
lemma BirationalOver.trans {S X Y Z : Scheme.{u}} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S}
    (h₁ : BirationalOver sX sY) (h₂ : BirationalOver sY sZ) :
    BirationalOver sX sZ :=
  ⟨h₁.partialIso.trans h₂.partialIso, h₁.partialIso_isOver.trans h₂.partialIso_isOver⟩

/-- `X` is rational over `S` (or `S`-rational) if it is birational over `S` to some
affine space `𝔸(n; S)`. Note that we do not require `n` to be finite here. -/
@[mk_iff]
/-
**AlgebraicGeometry.Scheme.IsRationalOver** 是 Mathlib 中的一个归纳类型，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：{S X : AlgebraicGeometry.Scheme} → (X ⟶ S) → Prop
参数：X ⟶ S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is rational over `S` (or `S`-rational) if it is birational over `S` to some
affine space `𝔸(n; S)`. Note that we do not require `n` to be finite here.
-/
class IsRationalOver {S X : Scheme.{u}} (sX : X ⟶ S) : Prop where
  exists_birationalOver_affineSpace (sX) : ∃ (n : Type u), BirationalOver sX (𝔸(n; S) ↘ S)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (S : Scheme.{u}) (n : Type u) : IsRationalOver (𝔸(n; S) ↘ S) where
  exists_birationalOver_affineSpace := ⟨n, .refl _⟩

/-- If a scheme `X` is `S`-birational to an `S`-rational scheme `Y`, then `X` is `S`-rational. -/
/-
**AlgebraicGeometry.Scheme.BirationalOver.isRationalOver** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.BirationalOver`。
形式化陈述：∀ {S X Y : AlgebraicGeometry.Scheme} (sX : X ⟶ S) (sY : Y ⟶ S) [AlgebraicG
eometry.Scheme.IsRationalOver sY],   AlgebraicGeometry.Scheme.BirationalOver sX 
sY → AlgebraicGeometry.Scheme.IsRationalOver sX
参数：sX : X ⟶ S；sY : Y ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsRationalOver.exists_birationalOver_affineSpac
e`：∀ {S X : AlgebraicGeometry.Scheme} (sX : X ⟶ S) [self : AlgebraicGeometry.Sch
eme.IsRationalOver sX],   ∃ n, AlgebraicGeometry.Scheme.Biratio…
· 使用定理 `AlgebraicGeometry.Scheme.BirationalOver.trans`：∀ {S X Y Z : AlgebraicGeo
metry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S},   AlgebraicGeometry.Scheme
.BirationalOver sX sY →     Algebra…

--- 原说明 ---
If a scheme `X` is `S`-birational to an `S`-rational scheme `Y`, then `X` is `S`
-rational.
-/
lemma BirationalOver.isRationalOver {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsRationalOver sY] (h : BirationalOver sX sY) : IsRationalOver sX := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sY
  exact ⟨n, h.trans hn⟩

section DenseOpen

variable {X S : Scheme.{u}} (U : Opens X) (sX : X ⟶ S)

/-- A dense open set `U : Opens X` induces a partial isomorphism between `U` and `X`. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Opens.partialIsoOfDense** 是 Mathlib 中的一个定义，位于命名空间 `Al
gebraicGeometry.Scheme.Opens`。
形式化陈述：{X : AlgebraicGeometry.Scheme} → (U : X.Opens) → Dense ↑U → (↑U).PartialIs
o X
参数：U : X.Opens；↑U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dense open set `U : Opens X` induces a partial isomorphism between `U` and `X`
.
-/
def Opens.partialIsoOfDense (hU : Dense (U : Set X)) : PartialIso U X where
  source := ⊤
  dense_source := dense_univ
  target := U
  dense_target := hU
  iso := U.toScheme.topIso

/-- A dense open set `U : Opens X` is birational to `X`. -/
/-
**AlgebraicGeometry.Scheme.Opens.birational_of_dense** 是 Mathlib 中的一个定理，位于命名空间 `
AlgebraicGeometry.Scheme.Opens`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (U : X.Opens), Dense ↑U → (↑U).Birational
 X
参数：U : X.Opens；↑U。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A dense open set `U : Opens X` is birational to `X`.
-/
lemma Opens.birational_of_dense (hU : Dense (U : Set X)) : Birational U X :=
  ⟨U.partialIsoOfDense hU⟩

set_option backward.defeqAttrib.useBackward true in
/-- A dense open set `U : Opens X` of a scheme `X` over `S` is `S`-birational to `X`. -/
/-
**AlgebraicGeometry.Scheme.Opens.birationalOver_of_dense** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (U : X.Opens) (sX : X ⟶ S),   Dense ↑U 
→ AlgebraicGeometry.Scheme.BirationalOver (CategoryTheory.CategoryStruct.comp U.
ι sX) sX
参数：U : X.Opens；sX : X ⟶ S；CategoryTheory.CategoryStruct.comp U.ι sX。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A dense open set `U : Opens X` of a scheme `X` over `S` is `S`-birational to `X`
.
-/
lemma Opens.birationalOver_of_dense (hU : Dense (U : Set X)) : BirationalOver (U.ι ≫ sX) sX :=
  ⟨U.partialIsoOfDense hU, by simp [PartialIso.IsOver]⟩

/-- A dense open set `U : Opens X` of a `S`-rational scheme `X` is `S`-rational. -/
/-
**AlgebraicGeometry.Scheme.Opens.isRationalOver_of_dense** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry.Scheme.Opens`。
形式化陈述：∀ {X S : AlgebraicGeometry.Scheme} (U : X.Opens) (sX : X ⟶ S),   Dense ↑U 
→     ∀ [AlgebraicGeometry.Scheme.IsRationalOver sX],       AlgebraicGeometry.Sc
heme.IsRationalOver (CategoryTheory.CategoryStruct.comp U.ι sX)
参数：U : X.Opens；sX : X ⟶ S；CategoryTheory.CategoryStruct.comp U.ι sX。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsRationalOver.exists_birationalOver_affineSpac
e`：∀ {S X : AlgebraicGeometry.Scheme} (sX : X ⟶ S) [self : AlgebraicGeometry.Sch
eme.IsRationalOver sX],   ∃ n, AlgebraicGeometry.Scheme.Biratio…
· 使用定理 `AlgebraicGeometry.Scheme.BirationalOver.trans`：∀ {S X Y Z : AlgebraicGeo
metry.Scheme} {sX : X ⟶ S} {sY : Y ⟶ S} {sZ : Z ⟶ S},   AlgebraicGeometry.Scheme
.BirationalOver sX sY →     Algebra…
· 使用定理 `AlgebraicGeometry.Scheme.Opens.birationalOver_of_dense`：∀ {X S : Algebra
icGeometry.Scheme} (U : X.Opens) (sX : X ⟶ S),   Dense ↑U → AlgebraicGeometry.Sc
heme.BirationalOver (CategoryTheory.Category…

--- 原说明 ---
A dense open set `U : Opens X` of a `S`-rational scheme `X` is `S`-rational.
-/
lemma Opens.isRationalOver_of_dense (hU : Dense (U : Set X)) [IsRationalOver sX] :
    IsRationalOver (U.ι ≫ sX) := by
  obtain ⟨n, hn⟩ := IsRationalOver.exists_birationalOver_affineSpace sX
  exact ⟨n, (U.birationalOver_of_dense sX hU).trans hn⟩

end DenseOpen

section OpenImmersion

variable {X U S : Scheme.{u}}

/-- A dominant open immersion `f : U ⟶ X` induces a partial isomorphism between `U` and `X`. -/
@[simps! source target iso]
/-
**AlgebraicGeometry.Scheme.Hom.partialIso** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：{X U : AlgebraicGeometry.Scheme} →   (f : U ⟶ X) → [AlgebraicGeometry.IsOp
enImmersion f] → [AlgebraicGeometry.IsDominant f] → U.PartialIso X
参数：f : U ⟶ X。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.denseRange`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f], DenseRange ⇑f

--- 原说明 ---
A dominant open immersion `f : U ⟶ X` induces a partial isomorphism between `U` 
and `X`.
-/
noncomputable def Hom.partialIso (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : U.PartialIso X :=
  (PartialIso.ofIso f.isoOpensRange).trans' (f.opensRange.partialIsoOfDense f.denseRange) rfl
/-
**AlgebraicGeometry.Scheme.Hom.birational** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGe
ometry.Scheme.Hom`。
形式化陈述：∀ {X U : AlgebraicGeometry.Scheme} (f : U ⟶ X) [AlgebraicGeometry.IsOpenIm
mersion f] [AlgebraicGeometry.IsDominant f],   U.Birational X
参数：f : U ⟶ X。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Hom.birational (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] : Birational U X :=
  ⟨f.partialIso⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.Hom.birationalOver** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry.Scheme.Hom`。
形式化陈述：∀ {X U S : AlgebraicGeometry.Scheme} (f : U ⟶ X) [AlgebraicGeometry.IsOpen
Immersion f] [AlgebraicGeometry.IsDominant f]   (sX : X ⟶ S) (sU : U ⟶ S),   Cat
egoryTheory.CategoryStruct.comp f sX = sU → AlgebraicGeometry.Scheme.BirationalO
ver sU sX
参数：f : U ⟶ X；sX : X ⟶ S；sU : U ⟶ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.denseRange`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y) [AlgebraicGeometry.IsDominant f], DenseRange ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Hom.partialIso_iso`：∀ {X U : AlgebraicGeometry.
Scheme} (f : U ⟶ X) [inst : AlgebraicGeometry.IsOpenImmersion f]   [inst_1 : Alg
ebraicGeometry.IsDominant f],   (…
· 使用定理 `AlgebraicGeometry.Scheme.isoOfEq_rfl`：∀ (X : AlgebraicGeometry.Scheme) (
U : X.Opens), X.isoOfEq ⋯ = CategoryTheory.Iso.refl ↑U
· 使用定理 `CategoryTheory.Iso.refl_trans`：refl_trans (α : X ≅ Y) : Iso.refl X ≪≫ α 
= α
· 使用定理 `CategoryTheory.Iso.symm_self_id`：symm_self_id (α : X ≅ Y) : α.symm ≪≫ α 
= Iso.refl Y
· 使用定理 `CategoryTheory.Iso.trans_refl`：trans_refl (α : X ≅ Y) : α ≪≫ Iso.refl Y 
= α
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isoOpensRange_hom_ι_assoc`：∀ {X Y : Algebra
icGeometry.Scheme} (f : X ⟶ Y) [inst : AlgebraicGeometry.IsOpenImmersion f]   {Z
 : AlgebraicGeometry.Scheme} (h : Y ⟶ Z),   …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Hom.birationalOver (f : U ⟶ X) [IsOpenImmersion f] [IsDominant f] (sX : X ⟶ S) (sU : U ⟶ S)
    (hf : f ≫ sX = sU) : BirationalOver sU sX :=
  ⟨f.partialIso, by simp [PartialIso.IsOver, hf]⟩

end OpenImmersion

end AlgebraicGeometry.Scheme

