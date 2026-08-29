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

/--
Definition of `LocallyDirected` / `LocallyDirected` 的定义

English:
class LocallyDirected
  parameters: (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀]
  axioms and operations (6):
    - trans({i j : 𝒰.I₀} (hij : i ⟶ j)) : 𝒰.X i ⟶ 𝒰.X j
    - trans_id((i : 𝒰.I₀)) : trans (𝟙 i) = 𝟙 (𝒰.X i)  [default: by cat_disch]
    - trans_comp({i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)) : trans (hij ≫ hjk) = trans hij ≫ trans hjk  [default: by cat_disch]
    - w({i j : 𝒰.I₀} (hij : i ⟶ j)) : trans hij ≫ 𝒰.f j = 𝒰.f i  [default: by cat_disch]
    - directed({i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier)) : exists (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k), pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
    - property_trans({i j : 𝒰.I₀} (hij : i ⟶ j)) : P (trans hij)  [default: by infer_instance]

中文:
类 LocallyDirected
  参数: (𝒰 : X.Cover (precoverage P)) [范畴* 𝒰.I₀]
  公理与运算 (6 个):
    - trans({i j : 𝒰.I₀} (hij : i ⟶ j)) : 𝒰.X i ⟶ 𝒰.X j
    - trans_id((i : 𝒰.I₀)) : trans (𝟙 i) = 𝟙 (𝒰.X i)  [默认: by cat_disch]
    - trans_comp({i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)) : trans (hij ≫ hjk) = trans hij ≫ trans hjk  [默认: by cat_disch]
    - w({i j : 𝒰.I₀} (hij : i ⟶ j)) : trans hij ≫ 𝒰.f j = 𝒰.f i  [默认: by cat_disch]
    - directed({i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier)) : 存在 (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k), pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
    - property_trans({i j : 𝒰.I₀} (hij : i ⟶ j)) : P (trans hij)  [默认: by infer_instance]

Depends on / 依赖: carrier, cat_disch, directed, infer_instance, property_trans, pullback, pullback.lift, trans_comp
-/
class LocallyDirected (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] where
  /-- The transition map `𝒰ᵢ ⟶ 𝒰ⱼ` for `i ≤ j`. -/
  trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j
  trans_id (i : 𝒰.I₀) : trans (𝟙 i) = 𝟙 (𝒰.X i) := by cat_disch
  trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    trans (hij ≫ hjk) = trans hij ≫ trans hjk := by cat_disch
  w {i j : 𝒰.I₀} (hij : i ⟶ j) : trans hij ≫ 𝒰.f j = 𝒰.f i := by cat_disch
  directed {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    exists (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (trans hki) (trans hkj) (by simp [w]) y = x
  property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (trans hij) := by infer_instance

variable (𝒰 : X.Cover (precoverage P)) [Category* 𝒰.I₀] [𝒰.LocallyDirected]

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: {i j : 𝒰.I₀} (hij : i ⟶ j)
  body: LocallyDirected.trans hij

@[simp]

中文:
定义 trans
  签名: {i j : 𝒰.I₀} (hij : i ⟶ j)
  定义体: LocallyDirected.trans hij

@[simp]

Depends on / 依赖: LocallyDirected, LocallyDirected.trans
-/
def trans {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.X i ⟶ 𝒰.X j := LocallyDirected.trans hij

@[simp]
/--
lemma `trans_map` / 引理 `trans_map`

English:
lemma trans_map
  given: {i j : 𝒰.I₀} (hij : i ⟶ j)
  statement: 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i
  proof: LocallyDirected.w hij

@[simp]

中文:
引理 trans_map
  条件: {i j : 𝒰.I₀} (hij : i ⟶ j)
  结论: 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i
  证明: LocallyDirected.w hij

@[simp]

Depends on / 依赖: LocallyDirected, LocallyDirected.w
-/
lemma trans_map {i j : 𝒰.I₀} (hij : i ⟶ j) : 𝒰.trans hij ≫ 𝒰.f j = 𝒰.f i :=
  LocallyDirected.w hij

@[simp]
/--
lemma `trans_id` / 引理 `trans_id`

English:
lemma trans_id
  given: (i : 𝒰.I₀)
  statement: 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i)
  proof: LocallyDirected.trans_id i

@[simp]

中文:
引理 trans_id
  条件: (i : 𝒰.I₀)
  结论: 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i)
  证明: LocallyDirected.trans_id i

@[simp]

Depends on / 依赖: LocallyDirected, LocallyDirected.trans_id, trans_id
-/
lemma trans_id (i : 𝒰.I₀) : 𝒰.trans (𝟙 i) = 𝟙 (𝒰.X i) := LocallyDirected.trans_id i

@[simp]
/--
lemma `trans_comp` / 引理 `trans_comp`

English:
lemma trans_comp
  given: {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
  proof: LocallyDirected.trans_comp hij hjk

中文:
引理 trans_comp
  条件: {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k)
  证明: LocallyDirected.trans_comp hij hjk

Depends on / 依赖: LocallyDirected, LocallyDirected.trans_comp, trans_comp
-/
lemma trans_comp {i j k : 𝒰.I₀} (hij : i ⟶ j) (hjk : j ⟶ k) :
    𝒰.trans (hij ≫ hjk) = 𝒰.trans hij ≫ 𝒰.trans hjk := LocallyDirected.trans_comp hij hjk

/--
lemma `exists_lift_trans_eq` / 引理 `exists_lift_trans_eq`

English:
lemma exists_lift_trans_eq
  given: {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier)
  proof: LocallyDirected.directed x

中文:
引理 存在_lift_trans_eq
  条件: {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier)
  证明: LocallyDirected.directed x

Depends on / 依赖: LocallyDirected, LocallyDirected.directed, directed
-/
lemma exists_lift_trans_eq {i j : 𝒰.I₀} (x : (pullback (𝒰.f i) (𝒰.f j)).carrier) :
    exists (k : 𝒰.I₀) (hki : k ⟶ i) (hkj : k ⟶ j) (y : 𝒰.X k),
      pullback.lift (𝒰.trans hki) (𝒰.trans hkj) (by simp) y = x :=
  LocallyDirected.directed x

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_of_f_eq_f` / 引理 `exists_of_f_eq_f`

English:
lemma exists_of_f_eq_f
  given: {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj)
  proof: by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, xk, rfl⟩ := 𝒰.exists_lift_trans_eq z
  use k, fi, fj, xk
  simp [← Scheme.Hom.comp_apply]

中文:
引理 存在_of_f_eq_f
  条件: {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj)
  证明: by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, xk, rfl⟩ := 𝒰.exists_lift_trans_eq z
  use k, fi, fj, xk
  simp [← Scheme.Hom.comp_apply]

Depends on / 依赖: Pullback, Scheme, Scheme.Hom.comp_apply, Scheme.Pullback.exists_preimage_pullback, comp_apply, exists_lift_trans_eq, exists_preimage_pullback
-/
lemma exists_of_f_eq_f {i j : 𝒰.I₀} (xi : 𝒰.X i) (xj : 𝒰.X j) (h : 𝒰.f i xi = 𝒰.f j xj) :
    exists (k : 𝒰.I₀) (fi : k ⟶ i) (fj : k ⟶ j) (xk : 𝒰.X k),
      𝒰.trans fi xk = xi ∧ 𝒰.trans fj xk = xj := by
  obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj h
  obtain ⟨k, fi, fj, xk, rfl⟩ := 𝒰.exists_lift_trans_eq z
  use k, fi, fj, xk
  simp [← Scheme.Hom.comp_apply]

/--
lemma `exists_of_trans_eq_trans` / 引理 `exists_of_trans_eq_trans`

English:
lemma exists_of_trans_eq_trans
  statement: {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.X i)
  proof: exists_of_f_eq_f _ _ _ by
  rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [h]; rw [ConcreteCategory.comp_apply]

中文:
引理 存在_of_trans_eq_trans
  结论: {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.X i)
  证明: exists_of_f_eq_f _ _ _ by
  rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [h]; rw [ConcreteCategory.comp_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, Hom.comp_base, comp_apply, comp_base, exists_of_f_eq_f, trans_map
-/
lemma exists_of_trans_eq_trans {i j k : 𝒰.I₀} (fi : i ⟶ k) (fj : j ⟶ k) (xi : 𝒰.X i)
    (xj : 𝒰.X j) (h : 𝒰.trans fi xi = 𝒰.trans fj xj) :
    exists (l : 𝒰.I₀) (fli : l ⟶ i) (flj : l ⟶ j) (x : 𝒰.X l),
𝒰.trans fli x = xi ∧ 𝒰.trans flj x = xj := exists_of_f_eq_f _ _ _ by
  rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [h]; rw [ConcreteCategory.comp_apply]

/--
lemma `property_trans` / 引理 `property_trans`

English:
lemma property_trans
  given: {i j : 𝒰.I₀} (hij : i ⟶ j)
  statement: P (𝒰.trans hij)
  proof: LocallyDirected.property_trans hij

中文:
引理 property_trans
  条件: {i j : 𝒰.I₀} (hij : i ⟶ j)
  结论: P (𝒰.trans hij)
  证明: LocallyDirected.property_trans hij

Depends on / 依赖: LocallyDirected, LocallyDirected.property_trans, property_trans
-/
lemma property_trans {i j : 𝒰.I₀} (hij : i ⟶ j) : P (𝒰.trans hij) :=
  LocallyDirected.property_trans hij

/-- If `𝒰` is a directed cover of `X`, this is the cover of `𝒰ᵢ ×[X] 𝒰ⱼ` by `{𝒰ₖ}` where
`k ≤ i` and `k ≤ j`. -/
@[simps f]
/--
Definition of `intersectionOfLocallyDirected` / `intersectionOfLocallyDirected` 的定义

English:
definition intersectionOfLocallyDirected
  signature: [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
  body: Σ (k : 𝒰.I₀), (k ⟶ i) × (k ⟶ j)
  X k := 𝒰.X k.1
  f k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun k => ?_⟩
    · use ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
        (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
      exact (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
    · apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
      rw [pullback.lift_fst]
      exact 𝒰.property_trans _

中文:
定义 intersectionOfLocallyDirected
  签名: [P.是StableUnderBaseChange] [P.有OfPostcompProperty P]
  定义体: Σ (k : 𝒰.I₀), (k ⟶ i) × (k ⟶ j)
  X k := 𝒰.X k.1
  f k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun k => ?_⟩
    · use ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
        (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
      exact (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
    · apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
      rw [pullback.lift_fst]
      exact 𝒰.property_trans _
-/
def intersectionOfLocallyDirected [P.IsStableUnderBaseChange] [P.HasOfPostcompProperty P]
    (i j : 𝒰.I₀) : (pullback (𝒰.f i) (𝒰.f j)).Cover (precoverage P) where
  I₀ := Σ (k : 𝒰.I₀), (k ⟶ i) × (k ⟶ j)
  X k := 𝒰.X k.1
  f k := pullback.lift (𝒰.trans k.2.1) (𝒰.trans k.2.2) (by simp)
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, fun k => ?_⟩
    · use ⟨(𝒰.exists_lift_trans_eq x).choose, (𝒰.exists_lift_trans_eq x).choose_spec.choose,
        (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose⟩
      exact (𝒰.exists_lift_trans_eq x).choose_spec.choose_spec.choose_spec
    · apply P.of_postcomp (W' := P) _ (pullback.fst _ _) (P.pullback_fst _ _ (𝒰.map_prop _))
      rw [pullback.lift_fst]
      exact 𝒰.property_trans _

/-- The canonical diagram induced by a locally directed cover. -/
@[simps]
/--
Definition of `functorOfLocallyDirected` / `functorOfLocallyDirected` 的定义

English:
definition functorOfLocallyDirected
  signature: : 𝒰.I₀ ⥤ Scheme.{u} where
  body: 𝒰.X
  map := 𝒰.trans

中文:
定义 functorOfLocallyDirected
  签名: : 𝒰.I₀ ⥤ 概形.{u} where
  定义体: 𝒰.X
  map := 𝒰.trans
-/
def functorOfLocallyDirected : 𝒰.I₀ ⥤ Scheme.{u} where
  obj := 𝒰.X
  map := 𝒰.trans

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (𝒰.functorOfLocallyDirected ⋙ Scheme.forget).IsLocallyDirected
  body: by
    simp only [Functor.comp_obj, functorOfLocallyDirected_obj, forget_obj, Functor.comp_map,
      functorOfLocallyDirected_map, forget_map, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] at hxij
    have : 𝒰.f i xi = 𝒰.f j xj := by
      rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [hxij]; rw [ConcreteCategory.comp_apply]
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj this
    obtain ⟨l, gi, gj, y, rfl⟩ := 𝒰.exists_lift_trans_eq z
    refine ⟨l, gi, gj, y, ?_, ?_⟩ <;> simp [← Scheme.Hom.comp_apply]

中文:
实例 :
  签名: (𝒰.functorOfLocallyDirected ⋙ 概形.forget).是LocallyDirected
  定义体: by
    simp only [Functor.comp_obj, functorOfLocallyDirected_obj, forget_obj, Functor.comp_map,
      functorOfLocallyDirected_map, forget_map, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] at hxij
    have : 𝒰.f i xi = 𝒰.f j xj := by
      rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [hxij]; rw [ConcreteCategory.comp_apply]
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj this
    obtain ⟨l, gi, gj, y, rfl⟩ := 𝒰.exists_lift_trans_eq z
    refine ⟨l, gi, gj, y, ?_, ?_⟩ <;> simp [← Scheme.Hom.comp_apply]

Depends on / 依赖: ConcreteCategory, ConcreteCategory.comp_apply, ConcreteCategory.hom_ofHom, Functor, Functor.comp_map, Functor.comp_obj, Hom.comp_base, Pullback, Scheme, Scheme.Pullback.exists_preimage_pullback, TypeCat, TypeCat.Fun.coe_mk, coe_mk, comp_apply, comp_base, comp_map, comp_obj, exists_preimage_pullback, forget_map, forget_obj
-/
instance : (𝒰.functorOfLocallyDirected ⋙ Scheme.forget).IsLocallyDirected where
  cond {i j k} fi fj xi xj hxij := by
    simp only [Functor.comp_obj, functorOfLocallyDirected_obj, forget_obj, Functor.comp_map,
      functorOfLocallyDirected_map, forget_map, ConcreteCategory.hom_ofHom,
      TypeCat.Fun.coe_mk] at hxij
    have : 𝒰.f i xi = 𝒰.f j xj := by
      rw [← 𝒰.trans_map fi]; rw [← 𝒰.trans_map fj]; rw [Hom.comp_base]; rw [Hom.comp_base]; rw [ConcreteCategory.comp_apply]; rw [hxij]; rw [ConcreteCategory.comp_apply]
    obtain ⟨z, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback xi xj this
    obtain ⟨l, gi, gj, y, rfl⟩ := 𝒰.exists_lift_trans_eq z
    refine ⟨l, gi, gj, y, ?_, ?_⟩ <;> simp [← Scheme.Hom.comp_apply]

set_option backward.defeqAttrib.useBackward true in
/-- The structure maps to `S` as a natural transformation. -/
@[simps]
/--
Definition of `functorOfLocallyDirectedHomBase` / `functorOfLocallyDirectedHomBase` 的定义

English:
definition functorOfLocallyDirectedHomBase
  signature: :
  body: 𝒰.f i

中文:
定义 functorOfLocallyDirectedHomBase
  签名: :
  定义体: 𝒰.f i
-/
def functorOfLocallyDirectedHomBase :
    𝒰.functorOfLocallyDirected ⟶ (Functor.const _).obj X where
  app i := 𝒰.f i

/--
The canonical cocone with point `X` on the functor induced by the locally directed cover `𝒰`.
If `𝒰` is an open cover, this is colimiting (see `OpenCover.isColimitCoconeOfLocallyDirected`).
-/
@[simps]
/--
Definition of `coconeOfLocallyDirected` / `coconeOfLocallyDirected` 的定义

English:
definition coconeOfLocallyDirected
  signature: : Cocone 𝒰.functorOfLocallyDirected where
  body: X
  ι := 𝒰.functorOfLocallyDirectedHomBase

中文:
定义 coconeOfLocallyDirected
  签名: : 余锥 𝒰.functorOfLocallyDirected where
  定义体: X
  ι := 𝒰.functorOfLocallyDirectedHomBase
-/
def coconeOfLocallyDirected : Cocone 𝒰.functorOfLocallyDirected where
  pt := X
  ι := 𝒰.functorOfLocallyDirectedHomBase

section BaseChange

variable [P.IsStableUnderBaseChange] (𝒰 : X.Cover (precoverage P))
    [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Scheme.{u}} (f : Y ⟶ X)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Category (𝒰.pullback₁ f).I₀
  body: inferInstanceAs Category 𝒰.I₀

中文:
实例 :
  签名: 范畴 (𝒰.pullback₁ f).I₀
  定义体: inferInstanceAs Category 𝒰.I₀

Depends on / 依赖: Category
-/
instance : Category (𝒰.pullback₁ f).I₀ := inferInstanceAs Category 𝒰.I₀

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `locallyDirectedPullbackCover` / 实例 `locallyDirectedPullbackCover`

English:
instance locallyDirectedPullbackCover
  signature: : Cover.LocallyDirected (𝒰.pullback₁ f) where
  body: pullback.map f (𝒰.f i) f (𝒰.f j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
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
    refine ⟨k, hki, hkj, show x in Set.range _ from ?_⟩
    rw [this]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Pullback.range_map]
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

中文:
实例 locallyDirectedPullbackCover
  签名: : Cover.LocallyDirected (𝒰.pullback₁ f) where
  定义体: pullback.map f (𝒰.f i) f (𝒰.f j) (𝟙 _) (𝒰.trans hij) (𝟙 _)
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
    refine ⟨k, hki, hkj, show x in Set.range _ from ?_⟩
    rw [this]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Pullback.range_map]
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

Depends on / 依赖: pullback, pullback.map
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
    refine ⟨k, hki, hkj, show x in Set.range _ from ?_⟩
    rw [this]; rw [Scheme.Hom.comp_base]; rw [TopCat.coe_comp]; rw [Set.range_comp]; rw [Pullback.range_map]
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

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.trans f) :=
  𝒰.property_trans f

instance {i j : 𝒰.I₀} (f : i ⟶ j) : IsOpenImmersion (𝒰.functorOfLocallyDirected.map f) :=
  𝒰.property_trans f

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `glueMorphismsOfLocallyDirected` / `glueMorphismsOfLocallyDirected` 的定义

English:
definition glueMorphismsOfLocallyDirected
  signature: (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]
  body: 𝒰.glueMorphisms g fun i j => by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]

中文:
定义 glueMorphismsOfLocallyDirected
  签名: (𝒰 : X.OpenCover) [范畴* 𝒰.I₀] [𝒰.LocallyDirected]
  定义体: 𝒰.glueMorphisms g fun i j => by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]

Depends on / 依赖: glueMorphisms, hom_ext, intersectionOfLocallyDirected
-/
def glueMorphismsOfLocallyDirected (𝒰 : X.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected]
    {Y : Scheme.{u}}
    (g : forall i, 𝒰.X i ⟶ Y) (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) :
    X ⟶ Y :=
𝒰.glueMorphisms g fun i j => by
    apply (𝒰.intersectionOfLocallyDirected i j).hom_ext
    intro k
    simp [h]

@[reassoc (attr := simp)]
/--
lemma `map_glueMorphismsOfLocallyDirected` / 引理 `map_glueMorphismsOfLocallyDirected`

English:
lemma map_glueMorphismsOfLocallyDirected
  statement: {Y : Scheme.{u}} (g : forall i, 𝒰.X i ⟶ Y)
  proof: by
  simp [glueMorphismsOfLocallyDirected]

中文:
引理 map_glueMorphismsOfLocallyDirected
  结论: {Y : 概形.{u}} (g : 对任意 i, 𝒰.X i ⟶ Y)
  证明: by
  simp [glueMorphismsOfLocallyDirected]

Depends on / 依赖: glueMorphismsOfLocallyDirected
-/
lemma map_glueMorphismsOfLocallyDirected {Y : Scheme.{u}} (g : forall i, 𝒰.X i ⟶ Y)
    (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i) (i : 𝒰.I₀) :
    𝒰.f i ≫ 𝒰.glueMorphismsOfLocallyDirected g h = g i := by
  simp [glueMorphismsOfLocallyDirected]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `isColimitCoconeOfLocallyDirected` / `isColimitCoconeOfLocallyDirected` 的定义

English:
definition isColimitCoconeOfLocallyDirected
  signature: : IsColimit 𝒰.coconeOfLocallyDirected where
  body: 𝒰.glueMorphismsOfLocallyDirected s.ι.app fun _ => s.ι.naturality _
  uniq s m hm := 𝒰.hom_ext _ _ fun j => by simpa using hm j

中文:
定义 isColimitCoconeOfLocallyDirected
  签名: : 是余极限 𝒰.coconeOfLocallyDirected where
  定义体: 𝒰.glueMorphismsOfLocallyDirected s.ι.app fun _ => s.ι.naturality _
  uniq s m hm := 𝒰.hom_ext _ _ fun j => by simpa using hm j

Depends on / 依赖: glueMorphismsOfLocallyDirected, naturality
-/
def isColimitCoconeOfLocallyDirected : IsColimit 𝒰.coconeOfLocallyDirected where
  desc s := 𝒰.glueMorphismsOfLocallyDirected s.ι.app fun _ => s.ι.naturality _
  uniq s m hm := 𝒰.hom_ext _ _ fun j => by simpa using hm j

/--
Definition of `glueMorphismsOverOfLocallyDirected` / `glueMorphismsOverOfLocallyDirected` 的定义

English:
definition glueMorphismsOverOfLocallyDirected
  signature: {S : Scheme.{u}} {X : Over S}
  body: Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]

中文:
定义 glueMorphismsOverOfLocallyDirected
  签名: {S : 概形.{u}} {X : Over S}
  定义体: Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]

Depends on / 依赖: Over.homMk, glueMorphismsOfLocallyDirected, hom_ext
-/
def glueMorphismsOverOfLocallyDirected {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : forall i, 𝒰.X i ⟶ Y.left)
    (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) :
    X ⟶ Y :=
Over.homMk (𝒰.glueMorphismsOfLocallyDirected g h) by
    apply 𝒰.hom_ext
    intro i
    simp [w]

@[reassoc (attr := simp)]
/--
lemma `map_glueMorphismsOverOfLocallyDirected_left` / 引理 `map_glueMorphismsOverOfLocallyDirected_left`

English:
lemma map_glueMorphismsOverOfLocallyDirected_left
  statement: {S : Scheme.{u}} {X : Over S}
  proof: by
  simp [glueMorphismsOverOfLocallyDirected]

中文:
引理 map_glueMorphismsOverOfLocallyDirected_left
  结论: {S : 概形.{u}} {X : Over S}
  证明: by
  simp [glueMorphismsOverOfLocallyDirected]

Depends on / 依赖: glueMorphismsOverOfLocallyDirected
-/
lemma map_glueMorphismsOverOfLocallyDirected_left {S : Scheme.{u}} {X : Over S}
    (𝒰 : X.left.OpenCover) [Category* 𝒰.I₀] [𝒰.LocallyDirected] {Y : Over S}
    (g : forall i, 𝒰.X i ⟶ Y.left) (h : forall {i j : 𝒰.I₀} (hij : i ⟶ j), 𝒰.trans hij ≫ g j = g i)
    (w : forall i, g i ≫ Y.hom = 𝒰.f i ≫ X.hom) (i : 𝒰.I₀) :
    𝒰.f i ≫ (𝒰.glueMorphismsOverOfLocallyDirected g h w).left = g i := by
  simp [glueMorphismsOverOfLocallyDirected]

end OpenCover

set_option backward.isDefEq.respectTransparency.types false in
/-- If `𝒰` is an open cover such that the images of the components form a basis of the topology
of `X`, `𝒰` is directed by the ordering of subset inclusion of the images. -/
@[instance_reducible]
/--
Definition of `Cover.LocallyDirected.ofIsBasisOpensRange` / `Cover.LocallyDirected.ofIsBasisOpensRange` 的定义

English:
definition Cover.LocallyDirected.ofIsBasisOpensRange
  signature: {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
  body: IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    have : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x in
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
refine ⟨k, homOfLE hle.mpr le_trans h ?_, homOfLE hle.mpr le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply]; rw [pullback.lift_fst_assoc]; rw [IsOpenImmersion.lift_fac]; rw [hy]

中文:
定义 Cover.LocallyDirected.ofIsBasisOpensRange
  签名: {𝒰 : X.OpenCover} [预序 𝒰.I₀]
  定义体: IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    have : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x in
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
refine ⟨k, homOfLE hle.mpr le_trans h ?_, homOfLE hle.mpr le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply]; rw [pullback.lift_fst_assoc]; rw [IsOpenImmersion.lift_fac]; rw [hy]

Depends on / 依赖: IsOpenImmersion, IsOpenImmersion.lift, hle.mp, leOfHom
-/
def Cover.LocallyDirected.ofIsBasisOpensRange {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
    (hle : forall {i j : 𝒰.I₀}, i <= j ↔ (𝒰.f i).opensRange <= (𝒰.f j).opensRange)
    (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i => (𝒰.f i).opensRange)) :
    𝒰.LocallyDirected where
  trans {i j} hij := IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp (leOfHom hij))
  trans_id i := by rw [← cancel_mono (𝒰.f i)]; simp
  trans_comp hij hjk := by rw [← cancel_mono (𝒰.f _)]; simp
  directed {i j} x := by
    have : (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) x in
      (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).opensRange := ⟨x, rfl⟩
    obtain ⟨k, ⟨k, rfl⟩, ⟨y, hy⟩, h⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp H this
refine ⟨k, homOfLE hle.mpr le_trans h ?_, homOfLE hle.mpr le_trans h ?_, y, ?_⟩
    · rw [Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · simp_rw [pullback.condition, Scheme.Hom.opensRange_comp]
      exact Set.image_subset_range _ _
    · apply (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply]; rw [pullback.lift_fst_assoc]; rw [IsOpenImmersion.lift_fac]; rw [hy]

section Constructions

section

variable {𝒰 : X.OpenCover} [Preorder 𝒰.I₀]
  (hle : forall {i j : 𝒰.I₀}, i <= j ↔ (𝒰.f i).opensRange <= (𝒰.f j).opensRange)
  (H : TopologicalSpace.Opens.IsBasis (Set.range <| fun i => (𝒰.f i).opensRange))

include hle in
/--
lemma `Cover.LocallyDirected.ofIsBasisOpensRange_le_iff` / 引理 `Cover.LocallyDirected.ofIsBasisOpensRange_le_iff`

English:
lemma Cover.LocallyDirected.ofIsBasisOpensRange_le_iff
  given: (i j : 𝒰.I₀)
  proof: Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i <= j ↔ (𝒰.f i).opensRange <= (𝒰.f j).opensRange := hle

中文:
引理 Cover.LocallyDirected.ofIsBasisOpensRange_le_iff
  条件: (i j : 𝒰.I₀)
  证明: Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i <= j ↔ (𝒰.f i).opensRange <= (𝒰.f j).opensRange := hle

Depends on / 依赖: Cover.LocallyDirected.ofIsBasisOpensRange, LocallyDirected, ofIsBasisOpensRange
-/
lemma Cover.LocallyDirected.ofIsBasisOpensRange_le_iff (i j : 𝒰.I₀) :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    i <= j ↔ (𝒰.f i).opensRange <= (𝒰.f j).opensRange := hle

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `Cover.LocallyDirected.ofIsBasisOpensRange_trans` / 引理 `Cover.LocallyDirected.ofIsBasisOpensRange_trans`

English:
lemma Cover.LocallyDirected.ofIsBasisOpensRange_trans
  given: {i j : 𝒰.I₀}
  proof: Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i <= j) -> 𝒰.trans (homOfLE hij) = IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp hij) :=
  fun _ => rfl

中文:
引理 Cover.LocallyDirected.ofIsBasisOpensRange_trans
  条件: {i j : 𝒰.I₀}
  证明: Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i <= j) -> 𝒰.trans (homOfLE hij) = IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp hij) :=
  fun _ => rfl

Depends on / 依赖: Cover.LocallyDirected.ofIsBasisOpensRange, LocallyDirected, ofIsBasisOpensRange
-/
lemma Cover.LocallyDirected.ofIsBasisOpensRange_trans {i j : 𝒰.I₀} :
    letI := Cover.LocallyDirected.ofIsBasisOpensRange hle H
    (hij : i <= j) -> 𝒰.trans (homOfLE hij) = IsOpenImmersion.lift (𝒰.f j) (𝒰.f i) (hle.mp hij) :=
  fun _ => rfl

end

variable (X) in
open TopologicalSpace.Opens in
/-- The directed affine open cover of `X` given by all affine opens. -/
@[simps I₀ X f]
/--
Definition of `directedAffineCover` / `directedAffineCover` 的定义

English:
definition directedAffineCover
  signature: : X.OpenCover where
  body: X.affineOpens
  X U := U
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    simpa using (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1

中文:
定义 directedAffineCover
  签名: : X.OpenCover where
  定义体: X.affineOpens
  X U := U
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    simpa using (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1

Depends on / 依赖: X.affineOpens, affineOpens
-/
def directedAffineCover : X.OpenCover where
  I₀ := X.affineOpens
  X U := U
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x => ?_, inferInstance⟩
    use ⟨(isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose,
      (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.1⟩
    simpa using (isBasis_iff_nbhd.mp X.isBasis_affineOpens (mem_top x)).choose_spec.2.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preorder X.directedAffineCover.I₀
  body: inferInstanceAs Preorder X.affineOpens

中文:
实例 :
  签名: 预序 X.directedAffineCover.I₀
  定义体: inferInstanceAs Preorder X.affineOpens

Depends on / 依赖: Preorder, X.affineOpens, affineOpens
-/
instance : Preorder X.directedAffineCover.I₀ := inferInstanceAs Preorder X.affineOpens

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Scheme.Cover.LocallyDirected X.directedAffineCover
  body: .ofIsBasisOpensRange (by intros; simp; rfl) by
    convert! X.isBasis_affineOpens
    simp

中文:
实例 :
  签名: 概形.Cover.LocallyDirected X.directedAffineCover
  定义体: .ofIsBasisOpensRange (by intros; simp; rfl) by
    convert! X.isBasis_affineOpens
    simp

Depends on / 依赖: X.isBasis_affineOpens, convert, intros, isBasis_affineOpens, ofIsBasisOpensRange
-/
instance : Scheme.Cover.LocallyDirected X.directedAffineCover :=
.ofIsBasisOpensRange (by intros; simp; rfl) by
    convert! X.isBasis_affineOpens
    simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/--
lemma `directedAffineCover_trans` / 引理 `directedAffineCover_trans`

English:
lemma directedAffineCover_trans
  given: {U V : X.affineOpens} (hUV : U <= V)
  proof: rfl

中文:
引理 directedAffineCover_trans
  条件: {U V : X.affineOpens} (hUV : U <= V)
  证明: rfl
-/
lemma directedAffineCover_trans {U V : X.affineOpens} (hUV : U <= V) :
    Cover.trans X.directedAffineCover (homOfLE hUV) = X.homOfLE hUV := rfl

end Constructions

end AlgebraicGeometry.Scheme
