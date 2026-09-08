/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.LocallyDirected
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Locally directed covers

A locally directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`.

Gluing along directed covers is easier, because the intersections `𝒰ᵢ ×[X] 𝒰ⱼ` can
be covered by a subcover of `𝒰`. In particular, if `𝒰` is a Zariski cover,
`X` naturally is the colimit of the `𝒰ᵢ`.

Many natural covers are naturally directed, most importantly the cover of all affine
opens of a scheme.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}}

namespace Cover

/-- A directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`. -/
/-
**AlgebraicGeometry.Scheme.Cover.LocallyDirected** 是 Mathlib 中的一个类，位于命名空间 `Algeb
raicGeometry.Scheme.Cover`。
形式化陈述：LocallyDirected (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] where /-- T
he transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/ trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰
.X i ⟶ 𝒰.X j trans_id (i : 𝒰.I₀) : trans (𝟙 i) = 𝟙 (𝒰.X i)
参数：𝒰 : X.Cover (precoverage P)；hij : i ⟶ j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A directed `P`-cover of a scheme `X` is a cover `𝒰` with an ordering
on the indices and compatible transition maps `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j` such that
every `x : 𝒰ᵢ ×[X] 𝒰ⱼ` comes from some `𝒰ₖ` for a `k ≤ i` and `k ≤ j`.
-/
class LocallyDirected (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] where
  /-- The transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/
  trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j
  trans_id (i : 𝒰.I₀) : trans (𝟙 i) = 𝟙 (𝒰.X i) := by cat_disch
  trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans (hij ≫ hjk) = trans hij ≫ trans hjk := by cat_disch
  w {i j : 𝒰.I₀} (hij : i ⟶ j) : trans hij ≫ 𝒰.f j = 𝒰.f i := by cat_disch
  directed {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
  property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (trans hij) := by infer_instance

variable (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-- The transition maps of a directed cover. -/
/-
**AlgebraicGeometry.Scheme.Cover.trans** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme.Cover`。
形式化陈述：trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j
参数：hij : i ⟶ j。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The transition maps of a directed cover.
-/
def trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j := LocallyDirected.trans hij

@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.trans_map** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicG
eometry.Scheme.Cover`。
形式化陈述：trans_map {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i
参数：hij : i ⟶ j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.LocallyDirected.w`：∀ {P : CategoryTheory.
MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   {𝒰 :
 AlgebraicGeometry.Scheme.Cover (Algeb…
-/
lemma trans_map {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i :=
  LocallyDirected.w hij

@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.trans_id** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGe
ometry.Scheme.Cover`。
形式化陈述：trans_id (i : 𝒰.I₀) : 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i)
参数：i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.LocallyDirected.trans_id`：∀ {P : Category
Theory.MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}
   {𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb…
-/
lemma trans_id (i : 𝒰.I₀) : 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i) := LocallyDirected.trans_id i

@[simp]
/-
**AlgebraicGeometry.Scheme.Cover.trans_comp** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme.Cover`。
形式化陈述：trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) : 𝒰.trans (hij ≫ hjk
) = 𝒰.trans hij ≫ 𝒰.trans hjk
参数：hij : i ⟶ j；hjk : j ⟶ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.LocallyDirected.trans_comp`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Schem
e}   {𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb…
-/
lemma trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    𝒰.trans (hij ≫ hjk) = 𝒰.trans hij ≫ 𝒰.trans hjk := LocallyDirected.trans_comp hij hjk
/-
**AlgebraicGeometry.Scheme.Cover.exists_lift_trans_eq** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme.Cover`。
形式化陈述：exists_lift_trans_eq {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier)
 : exists (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k), pullback.lift (𝒰.t
rans hki) (𝒰.trans hkj) (by simp) y = x
参数：x : (pullback (𝒰.f i) (𝒰.f j)).carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `AlgebraicGeometry.Scheme.Cover.LocallyDirected.directed`：∀ {P : Category
Theory.MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}
   {𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb…
-/
lemma exists_lift_trans_eq {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    ∃ (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp) y = x :=
  LocallyDirected.directed x

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.exists_of_f_eq_f** 是 Mathlib 中的一个引理，位于命名空间 `Alg
ebraicGeometry.Scheme.Cover`。
形式化陈述：exists_of_f_eq_f {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.
f j xj) : exists (k : 𝒰.I₀) (fi : k ⟶ i) (fj : k ⟶ j) (xk : 𝒰.X k), 𝒰.trans fi x
k = xi ∧ 𝒰.trans fj xk = xj
参数：xi : 𝒰.X i；xj : 𝒰.X j；h : 𝒰.f i xi = 𝒰.f j xj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用引理 `AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback`：exists_preim
age_pullback (x : X) (y : Y) (h : f x = g y) : exists z : ↑(pullback f g), pullb
ack.fst f g z = x ∧ pullback.snd f g z = y
· 使用引理 `AlgebraicGeometry.Scheme.Cover.exists_lift_trans_eq`：exists_lift_trans_e
q {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) : exists (k : 𝒰.I₀) (hki
 : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k), pull…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.Limits.PullbackCone.mk_π_app`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} {W : C} (fst :
 W ⟶ X)   (snd : W ⟶ Y)   (eq :  …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma exists_of_f_eq_f {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj) :
    ∃ (k : 𝒰.I₀) (fi : k ⟶ i) (fj : k ⟶ j) (xk : 𝒰.X k),
      𝒰.trans fi xk = xi ∧ 𝒰.trans fj xk = xj := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, xk, rfl⟩ := 𝒰.exists_lift_trans_eq z
  use k, fi, fj, xk
  simp [← Scheme.Hom.comp_apply]
/-
**AlgebraicGeometry.Scheme.Cover.exists_of_trans_eq_trans** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：exists_of_trans_eq_trans {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.
X i) (xj : 𝒰.X j) (h : 𝒰.trans fi xi = 𝒰.trans fj xj) : exists (l : 𝒰.I₀) (fli :
 l ⟶ i) (flj : l ⟶ j) (x : 𝒰.X l), 𝒰.trans fli x = xi ∧ 𝒰.trans flj x = xj
参数：fi : i ⟶ k；fj : j ⟶ k；xi : 𝒰.X i；xj : 𝒰.X j；h : 𝒰.trans fi xi = 𝒰.trans fj xj
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.Cover.exists_of_f_eq_f`：exists_of_f_eq_f {i j :
 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj) : exists (k : 𝒰.I₀) (
fi : k ⟶ i) (fj : k ⟶ j) (xk : 𝒰.X k)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.Cover.trans_map`：trans_map {i j : 𝒰.I₀} (hij : 
i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `CategoryTheory.ConcreteCategory.comp_apply`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (
C → Type w)}   {inst_1 : outPara…
-/
lemma exists_of_trans_eq_trans {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.X i)
    (xj : 𝒰.X j) (h : 𝒰.trans fi xi = 𝒰.trans fj xj) :
    ∃ (l : 𝒰.I₀) (fli : l ⟶ i) (flj : l ⟶ j) (x : 𝒰.X l),
      𝒰.trans fli x = xi ∧ 𝒰.trans flj x = xj := exists_of_f_eq_f _ _ _ <| by
  rw [← 𝒰.trans_map fi, ← 𝒰.trans_map fj, Hom.comp_base, Hom.comp_base,
    ConcreteCategory.comp_apply, h, ConcreteCategory.comp_apply]
/-
**AlgebraicGeometry.Scheme.Cover.property_trans** 是 Mathlib 中的一个引理，位于命名空间 `Algeb
raicGeometry.Scheme.Cover`。
形式化陈述：property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij)
参数：hij : i ⟶ j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.LocallyDirected.property_trans`：∀ {P : Ca
tegoryTheory.MorphismProperty AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.S
cheme}   {𝒰 : AlgebraicGeometry.Scheme.Cover (Algeb…
-/
lemma property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij) :=
  LocallyDirected.property_trans hij

/-- If `𝒰` is a directed cover of `X`, this is the cover of `𝒰ᵢ ×[X] 𝒰ⱼ` by `{𝒰ₖ}` where
`k ≤ i` and `k ≤ j`. -/
@[simps f]
/-
**AlgebraicGeometry.Scheme.Cover.intersectionOfLocallyDirected** 是 Mathlib 中的一个定
义，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：intersectionOfLocallyDirected [P.IsStableUnderBaseChange] [P.HasOfPostcomp
Property P] (i j : 𝒰.I₀) : (pullback (𝒰.f i) (𝒰.f j)).Cover (precoverage P) wher
e I₀
参数：i j : 𝒰.I₀。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒰` is a directed cover of `X`, this is the cover of `𝒰ᵢ ×[X] 𝒰ⱼ` by `{𝒰ₖ}` w
here
`k ≤ i` and `k ≤ j`.
-/
def intersectionOfLocallyDirected [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (i j : 𝒰.I₀) : (pullback (𝒰.f i) (𝒰.f j)).Cover (precoverage P) where
  I₀ := Σ (k : 𝒰.I₀), (k ⟶ i) × (k ⟶ j)
  X k := 𝒰.X k.1
  f k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun k ↦ ?_⟩
    · use ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
        (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
      exact (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
    · apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
      rw [pullback.lift_fst]
      exact 𝒰.property_trans _

/-- The canonical diagram induced by a locally directed cover. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.functorOfLocallyDirected** 是 Mathlib 中的一个定义，位于命
名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：functorOfLocallyDirected : 𝒰.I₀ ⥤ Scheme.{u} where obj
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical diagram induced by a locally directed cover.
-/
def functorOfLocallyDirected : 𝒰.I₀ ⥤ Scheme.{u} where
  obj := 𝒰.X
  map := 𝒰.trans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (𝒰.functorOfLocallyDirected ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj hxij := by
    simp only [Functor.comp_obj, functorOfLocallyDirected_obj, forget_obj, Functor.comp_map,
      functorOfLocallyDirected_map, forget_map, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] at hxij
    have : 𝒰.f i xi = 𝒰.f j xj := by
      rw [← 𝒰.trans_map fi, ← 𝒰.trans_map fj, Hom.comp_base, Hom.comp_base,
        ConcreteCategory.comp_apply, hxij, ConcreteCategory.comp_apply]
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj this
    obtain ⟨l, gi, gj, y, rfl⟩ := 𝒰.exists_lift_trans_eq z
    refine ⟨l, gi, gj, y, ?_, ?_⟩ <;> simp [← Scheme.Hom.comp_apply]

set_option backward.defeqAttrib.useBackward true in
/-- The structure maps to `S` as a natural transformation. -/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.functorOfLocallyDirectedHomBase** 是 Mathlib 中的一
个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：functorOfLocallyDirectedHomBase : 𝒰.functorOfLocallyDirected ⟶ (Functor.co
nst _).obj X where app i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure maps to `S` as a natural transformation.
-/
def functorOfLocallyDirectedHomBase :
    𝒰.functorOfLocallyDirected ⟶ (Functor.const _).obj X where
  app i := 𝒰.f i

/--
The canonical cocone with point `X` on the functor induced by the locally directed cover `𝒰`.
If `𝒰` is an open cover, this is colimiting (see `OpenCover.isColimitCoconeOfLocallyDirected`).
-/
@[simps]
/-
**AlgebraicGeometry.Scheme.Cover.coconeOfLocallyDirected** 是 Mathlib 中的一个定义，位于命名
空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：coconeOfLocallyDirected : Cocone 𝒰.functorOfLocallyDirected where pt
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical cocone with point `X` on the functor induced by the locally direct
ed cover `𝒰`.
If `𝒰` is an open cover, this is colimiting (see `OpenCover.isColimitCoconeOfLoc
allyDirected`).
-/
def coconeOfLocallyDirected : Cocone 𝒰.functorOfLocallyDirected where
  pt := X
  ι := 𝒰.functorOfLocallyDirectedHomBase

section BaseChange

variable [P.IsStableUnderBaseChange] (𝒰 : X.Cover (precoverage P))
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Scheme.{u}} (f : Y ⟶ X)

/-
**AlgebraicGeometry.Scheme.Cover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.S
cheme.Cover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Category (𝒰.pullback₁ f).I₀ := inferInstanceAs <| Category 𝒰.I₀

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.Cover.locallyDirectedPullbackCover** 是 Mathlib 中的一个实例
，位于命名空间 `AlgebraicGeometry.Scheme.Cover`。
形式化陈述：locallyDirectedPullbackCover : Cover.LocallyDirected (𝒰.pullback₁ f) where
 trans {i j} hij
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance locallyDirectedPullbackCover : Cover.LocallyDirected (𝒰.pullback₁ f) where
  trans {i j} hij := pullback.map f (𝒰.f i) f (𝒰.f j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
    (by simp) (by simp)
  trans_id i := by simp
  trans_comp hij hjk := by simp [pullback.map_comp]
  directed {i j} x := by
    dsimp at i j x ⊢
    let iso : pullback (pullback.fst f (𝒰.f i)) (pullback.fst f (𝒰.f j)) ≅
        pullback f (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) :=
      pullbackRightPullbackFstIso _ _ _ ≪≫ pullback.congrHom pullback.condition rfl ≪≫
        pullbackAssoc ..
    have (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) :
        (pullback.lift
          (pullback.map f (𝒰.f k) f (𝒰.f i) (𝟙 Y) (𝒰.trans hki) (𝟙 X) (by simp) (by simp))
          (pullback.map f (𝒰.f k) f (𝒰.f j) (𝟙 Y) (𝒰.trans hkj) (𝟙 X) (by simp) (by simp))
            (by simp)) =
          pullback.map _ _ _ _ (𝟙 Y) (pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp)) (𝟙 X)
            (by simp) (by simp) ≫ iso.inv := by
      apply pullback.hom_ext <;> apply pullback.hom_ext <;> simp [iso]
    obtain ⟨k, hki, hkj, yk, hyk⟩ := 𝒰.exists_lift_trans_eq ((iso.hom ≫ pullback.snd _ _) x)
    refine ⟨k, hki, hkj, show x ∈ Set.range _ from ?_⟩
    rw [this, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_map]
    use iso.hom x
    simp only [Hom.id_base, TopCat.hom_id, ContinuousMap.coe_id, Set.range_id, Set.preimage_univ,
      Set.univ_inter, Set.mem_preimage, Set.mem_range, hom_inv_apply, and_true]
    exact ⟨yk, hyk⟩
  property_trans {i j} hij := by
    let iso : pullback f (𝒰.f i) ≅ pullback (pullback.snd f (𝒰.f j)) (𝒰.trans hij) :=
      pullback.congrHom rfl (by simp) ≪≫ (pullbackLeftPullbackSndIso _ _ _).symm
    rw [← P.cancel_left_of_respectsIso iso.inv]
    simp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, Iso.trans_inv, Iso.symm_inv, pullback.congrHom_inv,
      Category.assoc, iso]
    convert! P.pullback_fst (pullback.snd f (𝒰.f j)) _ (𝒰.property_trans hij)
    apply pullback.hom_ext <;> simp [pullback.condition]

end BaseChange

end Cover

namespace OpenCover

variable (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/-
**AlgebraicGeometry.Scheme.OpenCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeomet
ry.Scheme.OpenCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.trans f) :=
  𝒰.property_trans f
/-
**AlgebraicGeometry.Scheme.OpenCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeomet
ry.Scheme.OpenCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.functorOfLocallyDirected.map f) :=
  𝒰.property_trans f

set_option backward.isDefEq.respectTransparency false in
/--
If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` it suffices
to check compatibility with the transition maps.
See `OpenCover.isColimitCoconeOfLocallyDirected` for this result stated in the language of
colimits.
-/
/-
**AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOfLocallyDirected** 是 Mathlib 
中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.Local
lyDirected] {Y : Scheme.{u}} (g : forall i, 𝒰.X i ⟶ Y) (h : forall {i j : 𝒰.I₀} 
(hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) : X ⟶ Y
参数：𝒰 : X.OpenCover；g : forall i, 𝒰.X i ⟶ Y；h : forall {i j : 𝒰.I₀} (hij : i ⟶ j)
, 𝒰.trans hij ≫ g j = g i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` it suf
fices
to check compatibility with the transition maps.
See `OpenCover.isColimitCoconeOfLocallyDirected` for this result stated in the l
anguage of
colimits.
-/
def glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]
    {Y : Scheme.{u}}
    (g : ∀ i, 𝒰.X i ⟶ Y) (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) :
    X ⟶ Y :=
  𝒰.glueMorphisms g <| fun i j ↦ by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOfLocallyDirected** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：map_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : forall i, 𝒰.X i ⟶
 Y) (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.I₀) 
: 𝒰.f i ≫ 𝒰.glueMorphismsOfLocallyDirected g h = g i
参数：g : forall i, 𝒰.X i ⟶ Y；h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ 
g j = g i；i : 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms`：ι_glueMorphisms (𝒰 : Ope
nCover.{v} X) {Y : Scheme} (f : forall x, 𝒰.X x ⟶ Y) (hf : forall x y, pullback.
fst (𝒰.f x) (𝒰.f y) ≫ f x = pullback…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : ∀ i, 𝒰.X i ⟶ Y)
    (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphismsOfLocallyDirected g h = g i := by
  simp [glueMorphismsOfLocallyDirected]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `𝒰` is an open cover of `X` that is locally directed, `X` is
the colimit of the components of `𝒰`. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.isColimitCoconeOfLocallyDirected** 是 Mathli
b 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：isColimitCoconeOfLocallyDirected : IsColimit 𝒰.coconeOfLocallyDirected whe
re desc s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒰` is an open cover of `X` that is locally directed, `X` is
the colimit of the components of `𝒰`.
-/
def isColimitCoconeOfLocallyDirected : IsColimit 𝒰.coconeOfLocallyDirected where
  desc s := 𝒰.glueMorphismsOfLocallyDirected s.ι.app fun _ ↦ s.ι.naturality _
  uniq s m hm := 𝒰.hom_ext _ _ fun j ↦ by simpa using hm j

/-- If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` over `S` it suffices
to check compatibility with the transition maps. -/
/-
**AlgebraicGeometry.Scheme.OpenCover.glueMorphismsOverOfLocallyDirected** 是 Math
lib 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：glueMorphismsOverOfLocallyDirected {S : Scheme.{u}} {X : Over S} (𝒰 : X.le
ft.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S} (g : forall i, 𝒰
.X i ⟶ Y.left) (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) 
(w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) : X ⟶ Y
参数：𝒰 : X.left.OpenCover；g : forall i, 𝒰.X i ⟶ Y.left；h : forall {i j : 𝒰.I₀} (hi
j : i ⟶ j), 𝒰.trans hij ≫ g j = g i；w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `𝒰` is a directed open cover of `X`, to glue morphisms `{gᵢ : 𝒰ᵢ ⟶ Y}` over `
S` it suffices
to check compatibility with the transition maps.
-/
def glueMorphismsOverOfLocallyDirected {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : ∀ i, 𝒰.X i ⟶ Y.left)
    (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) :
    X ⟶ Y :=
  Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) <| by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]
/-
**AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOverOfLocallyDirected_left
** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.OpenCover`。
形式化陈述：map_glueMorphismsOverOfLocallyDirected_left {S : Scheme.{u}} {X : Over S} 
(𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S} (g : fo
rall i, 𝒰.X i ⟶ Y.left) (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g 
j = g i) (w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) (i : 𝒰.I₀) : 𝒰.f i ≫ (𝒰.glu
eMorphismsOverOfLocallyDirected g h w).left = g i
参数：𝒰 : X.left.OpenCover；g : forall i, 𝒰.X i ⟶ Y.left；h : forall {i j : 𝒰.I₀} (hi
j : i ⟶ j), 𝒰.trans hij ≫ g j = g i；w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom；i 
: 𝒰.I₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Over.homMk_left`：∀ {T : Type u₁} [inst : CategoryTheory.C
ategory.{v₁, u₁} T] {X : T} {U V : CategoryTheory.Over X} (f : U.left ⟶ V.left) 
  (w : autoParam (Ca…
· 使用引理 `AlgebraicGeometry.Scheme.OpenCover.map_glueMorphismsOfLocallyDirected`：m
ap_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : forall i, 𝒰.X i ⟶ Y) (h 
: forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_glueMorphismsOverOfLocallyDirected_left {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : ∀ i, 𝒰.X i ⟶ Y.left) (h : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : ∀ i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) (i : 𝒰.I₀) :
    𝒰.f i ≫ (𝒰.glueMorphismsOverOfLocallyDirected g h w).left = g i := by
  simp [glueMorphismsOverOfLocallyDirected]

end OpenCover

set_option backward.isDefEq.respectTransparency.types false in
/-- If `𝒰` is an open cover such that the images of the components form a basis of the topology
of `X`, `𝒰` is directed by the ordering of subset inclusion of the images. -/
@[instance_reducible]
/-
**AlgebraicGeometry.Scheme.Cover.LocallyDirected.ofIsBasisOpensRange** 是 Mathlib
 中的一个定义，位于命名空间 `AlgebraicGeometry.Scheme.Cover.LocallyDirected`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   {𝒰 : X.OpenCover} →     [inst : Preorde
r 𝒰.I₀] →       (∀ {i j : 𝒰.I₀},           i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.
opensRange (𝒰.f i) ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j)) →         
TopologicalSpace.Opens.IsBasis (Set.range fun i => AlgebraicGeometry.Scheme.Hom.
opensRange (𝒰.f i)) →           AlgebraicGeometry.Scheme.Cover.LocallyDirected 𝒰
参数：∀ {i j : 𝒰.I₀},           i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.
f i) ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j)；Set.range fun i => Algebr
aicGeometry.Scheme.Hom.opensRange (𝒰.f i)。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)

--- 原说明 ---
If `𝒰` is an open cover such that the images of the components form a basis of t
he topology
of `X`, `𝒰` is directed by the ordering of subset inclusion of the images.
-/
def Cover.LocallyDirected.ofIsBasisOpensRange {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
    (hle : ∀ {i j : 𝒰.I₀}, i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange)
    (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.f i).opensRange)) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    have : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x ∈
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
    refine ⟨k, homOfLE <| hle.mpr <| le_trans h ?_, homOfLE <| hle.mpr <| le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc, IsOpenImmersion.lift_fac, hy]

section Constructions

section

variable {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
  (hle : ∀ {i j : 𝒰.I₀}, i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange)
  (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i ↦ (𝒰.f i).opensRange))

include hle in
/-
**AlgebraicGeometry.Scheme.Cover.LocallyDirected.ofIsBasisOpensRange_le_iff** 是 
Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.LocallyDirected`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {𝒰 : X.OpenCover} [inst : Preorder 𝒰.I₀],
   (∀ {i j : 𝒰.I₀},       i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f i
) ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j)) →     ∀ (i j : 𝒰.I₀),      
 i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f i) ≤ AlgebraicGeometry.Sch
eme.Hom.opensRange (𝒰.f j)
参数：∀ {i j : 𝒰.I₀},       i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f i)
 ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j)；i j : 𝒰.I₀；𝒰.f i；𝒰.f j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
-/
lemma Cover.LocallyDirected.ofIsBasisOpensRange_le_iff (i j : 𝒰.I₀) :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i ≤ j ↔ (𝒰.f i).opensRange ≤ (𝒰.f j).opensRange := hle

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.Cover.LocallyDirected.ofIsBasisOpensRange_trans** 是 M
athlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.Cover.LocallyDirected`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {𝒰 : X.OpenCover} [inst : Preorder 𝒰.I₀] 
  (hle :     ∀ {i j : 𝒰.I₀},       i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRan
ge (𝒰.f i) ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j))   (H : Topological
Space.Opens.IsBasis (Set.range fun i => AlgebraicGeometry.Scheme.Hom.opensRange 
(𝒰.f i))) {i j : 𝒰.I₀}   (hij : i ≤ j),   AlgebraicGeometry.Scheme.Cover.trans 𝒰
 (CategoryTheory.homOfLE hij) =     AlgebraicGeometry.IsOpenImmersion.lift (𝒰.f 
j) (𝒰.f i) ⋯
参数：hle :     ∀ {i j : 𝒰.I₀},       i ≤ j ↔ AlgebraicGeometry.Scheme.Hom.opensRan
ge (𝒰.f i) ≤ AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f j)；H : TopologicalSpac
e.Opens.IsBasis (Set.range fun i => AlgebraicGeometry.Scheme.Hom.opensRange (𝒰.f
 i))；hij : i ≤ j；CategoryTheory.homOfLE hij；𝒰.f j；𝒰.f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
-/
lemma Cover.LocallyDirected.ofIsBasisOpensRange_trans {i j : 𝒰.I₀} :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i ≤ j) → 𝒰.trans (homOfLE hij) = IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp hij) :=
  fun _ ↦ rfl

end

variable (X) in
open TopologicalSpace.Opens in
/-- The directed affine open cover of `X` given by all affine opens. -/
@[simps I₀ X f]
/-
**AlgebraicGeometry.Scheme.directedAffineCover** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：directedAffineCover : X.OpenCover where I₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed affine open cover of `X` given by all affine opens.
-/
def directedAffineCover : X.OpenCover where
  I₀ := X.affineOpens
  X U := U
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    use ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    simpa using (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder X.directedAffineCover.I₀ := inferInstanceAs <| Preorder X.affineOpens

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Scheme.Cover.LocallyDirected X.directedAffineCover :=
  .ofIsBasisOpensRange (by intros; simp; rfl) <| by
    convert! X.isBasis_affineOpens
    simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**AlgebraicGeometry.Scheme.directedAffineCover_trans** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Scheme`。
形式化陈述：directedAffineCover_trans {U V : X.affineOpens} (hUV : U <= V) : Cover.tra
ns X.directedAffineCover (homOfLE hUV) = X.homOfLE hUV
参数：hUV : U <= V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma directedAffineCover_trans {U V : X.affineOpens} (hUV : U ≤ V) :
    Cover.trans X.directedAffineCover (homOfLE hUV) = X.homOfLE hUV := rfl

end Constructions

end AlgebraicGeometry.Scheme

