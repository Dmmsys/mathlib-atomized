/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RepresentationTheory.Rep.Iso
/-!
# Restriction of representations

Given a group homomorphism `f : H →* G`, we have the restriction functor
`resFunctor f : Rep k G ⥤ Rep k H` which sends a `G`-representation `ρ` to the
`H`-representation `ρ.comp f`.

-/

public section

universe t w u v v1 v2

variable {k : Type u} [Semiring k] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/-- The map induced by a monoid homomorphism `f : H →* G` on morphisms between
`G`-representations. -/
@[expose, implicit_reducible]
/--
Definition of `resMap` / `resMap` 的定义

English:
definition resMap
  signature: {X Y : Rep k G} (f : H ->* G) (p : X ⟶ Y)
  body: ofHom ⟨p.hom, fun h => by simpa using p.hom.2 (f h)⟩

中文:
定义 resMap
  签名: {X Y : Rep k G} (f : H ->* G) (p : X ⟶ Y)
  定义体: ofHom ⟨p.hom, fun h => by simpa using p.hom.2 (f h)⟩
-/
def resMap {X Y : Rep k G} (f : H ->* G) (p : X ⟶ Y) :
    of (X := X.V) (X.ρ.comp f) ⟶ of (X := Y.V) (Y.ρ.comp f) :=
  ofHom ⟨p.hom, fun h => by simpa using p.hom.2 (f h)⟩

/--
Definition of `resFunctor` / `resFunctor` 的定义

English:
abbreviation resFunctor
  signature: (f : H ->* G)
  body: of (X := A.V) (A.ρ.comp f)
  map f' := resMap f f'

中文:
缩写 resFunctor
  签名: (f : H ->* G)
  定义体: of (X := A.V) (A.ρ.comp f)
  map f' := resMap f f'
-/
abbrev resFunctor (f : H ->* G) : Rep.{t} k G ⥤ Rep k H where
  obj A := of (X := A.V) (A.ρ.comp f)
  map f' := resMap f f'

/--
Definition of `res` / `res` 的定义

English:
abbreviation res
  signature: (f : H ->* G) (M : Rep k G)
  body: (resFunctor f).obj M

中文:
缩写 res
  签名: (f : H ->* G) (M : Rep k G)
  定义体: (resFunctor f).obj M

Depends on / 依赖: resFunctor
-/
abbrev res (f : H ->* G) (M : Rep k G) := (resFunctor f).obj M

variable (f : H ->* G) (M : Rep k G)

/--
lemma `res_id` / 引理 `res_id`

English:
lemma res_id
  statement: res (MonoidHom.id G) M = M
  proof: rfl

中文:
引理 res_id
  结论: res (幺半群态射.id G) M = M
  证明: rfl
-/
lemma res_id : res (MonoidHom.id G) M = M := rfl

/--
lemma `res_obj_ρ` / 引理 `res_obj_ρ`

English:
lemma res_obj_ρ
  statement: (res f M).ρ = (M.ρ.comp f)
  proof: rfl

中文:
引理 res_obj_ρ
  结论: (res f M).ρ = (M.ρ.comp f)
  证明: rfl
-/
@[simp] lemma res_obj_ρ : (res f M).ρ = (M.ρ.comp f) := rfl

/--
lemma `coe_res_obj_ρ'` / 引理 `coe_res_obj_ρ'`

English:
lemma coe_res_obj_ρ'
  given: (h : H)
  statement: (res f M).ρ h = M.ρ (f h)
  proof: rfl

中文:
引理 coe_res_obj_ρ'
  条件: (h : H)
  结论: (res f M).ρ h = M.ρ (f h)
  证明: rfl
-/
lemma coe_res_obj_ρ' (h : H) : (res f M).ρ h = M.ρ (f h) := rfl

/--
lemma `res_obj_V` / 引理 `res_obj_V`

English:
lemma res_obj_V
  statement: (res f M).V = M.V
  proof: rfl

@[simp]

中文:
引理 res_obj_V
  结论: (res f M).V = M.V
  证明: rfl

@[simp]
-/
lemma res_obj_V : (res f M).V = M.V := rfl

@[simp]
/--
lemma `resMap_hom_toLinearMap` / 引理 `resMap_hom_toLinearMap`

English:
lemma resMap_hom_toLinearMap
  given: {M N : Rep k G} (p : M ⟶ N)
  proof: rfl

@[deprecated (since := "2026-06-26")]
alias res_map_hom_toLinearMap := resMap_hom_toLinearMap

@[simp]

中文:
引理 resMap_hom_toLinearMap
  条件: {M N : Rep k G} (p : M ⟶ N)
  证明: rfl

@[deprecated (since := "2026-06-26")]
alias res_map_hom_toLinearMap := resMap_hom_toLinearMap

@[simp]
-/
lemma resMap_hom_toLinearMap {M N : Rep k G} (p : M ⟶ N) :
    (resMap f p).hom.toLinearMap = p.hom.toLinearMap := rfl

@[deprecated (since := "2026-06-26")]
alias res_map_hom_toLinearMap := resMap_hom_toLinearMap

@[simp]
/--
lemma `resMap_hom_apply` / 引理 `resMap_hom_apply`

English:
lemma resMap_hom_apply
  given: {M N : Rep k G} (p : M ⟶ N) (x : M.V)
  proof: rfl

中文:
引理 resMap_hom_apply
  条件: {M N : Rep k G} (p : M ⟶ N) (x : M.V)
  证明: rfl
-/
lemma resMap_hom_apply {M N : Rep k G} (p : M ⟶ N) (x : M.V) :
    @DFunLike.coe (Representation.IntertwiningMap (M.ρ.comp f) (N.ρ.comp f)) _ _ _
      (resMap f p).hom x = p.hom x := rfl

section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (resFunctor (k := k) f).Faithful
  body: by
    simpa [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] using h

中文:
实例 :
  签名: (resFunctor (k := k) f).忠实
  定义体: by
    simpa [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] using h

Depends on / 依赖: Faithful
-/
instance : (resFunctor (k := k) f).Faithful where
  map_injective h := by
    simpa [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] using h

/--
Definition of `liftHomOfSurj` / `liftHomOfSurj` 的定义

English:
abbreviation liftHomOfSurj
  signature: {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶ res f Y)
  body: ofHom ⟨f'.hom.toLinearMap, fun g => by obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]

中文:
缩写 liftHomOfSurj
  签名: {X Y : Rep k G} (hf : 函数.满射 f) (f' : res f X ⟶ res f Y)
  定义体: ofHom ⟨f'.hom.toLinearMap, fun g => by obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]

Depends on / 依赖: hom.toLinearMap, toLinearMap
-/
abbrev liftHomOfSurj {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶ res f Y) :
    X ⟶ Y := ofHom ⟨f'.hom.toLinearMap, fun g => by obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]
/--
lemma `liftHomOfSurj_toLinearMap` / 引理 `liftHomOfSurj_toLinearMap`

English:
lemma liftHomOfSurj_toLinearMap
  statement: {X Y : Rep k G} (hf : Function.Surjective f)
  proof: rfl

中文:
引理 liftHomOfSurj_toLinearMap
  结论: {X Y : Rep k G} (hf : 函数.满射 f)
  证明: rfl
-/
lemma liftHomOfSurj_toLinearMap {X Y : Rep k G} (hf : Function.Surjective f)
    (f' : res f X ⟶ res f Y) : (liftHomOfSurj f hf f').hom.toLinearMap =
      f'.hom.toLinearMap := rfl

/--
lemma `full_res` / 引理 `full_res`

English:
lemma full_res
  given: (hf : (⇑f).Surjective)
  statement: (resFunctor (k := k) f).Full where
  proof: ⟨liftHomOfSurj f hf f', by ext; simp⟩

中文:
引理 full_res
  条件: (hf : (⇑f).满射)
  结论: (resFunctor (k := k) f).满 where
  证明: ⟨liftHomOfSurj f hf f', by ext; simp⟩
-/
lemma full_res (hf : (⇑f).Surjective) : (resFunctor (k := k) f).Full where
  map_surjective {X Y} f' := ⟨liftHomOfSurj f hf f', by ext; simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: (resFunctor (k := k) f).Additive
  body: by ext : 2; simp [add_hom]

中文:
实例 :
  签名: (resFunctor (k := k) f).加性
  定义体: by ext : 2; simp [add_hom]

Depends on / 依赖: Additive
-/
instance : (resFunctor (k := k) f).Additive where
  map_add {_ _} _ _ := by ext : 2; simp [add_hom]

instance {k : Type u} [CommSemiring k] : (resFunctor (k := k) f).Linear k where
  map_smul {_ _} _ _ := by ext : 2; simp [smul_hom]

section ShortComplex

open Limits

variable {k : Type u} [Ring k]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PreservesLimits (resFunctor.{w} (k := k) f)
  body: have : PreservesLimitsOfSize.{w, w} (resFunctor f ⋙ forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

中文:
实例 :
  签名: PreservesLimits (resFunctor.{w} (k := k) f)
  定义体: have : PreservesLimitsOfSize.{w, w} (resFunctor f ⋙ forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))
-/
instance : PreservesLimits (resFunctor.{w} (k := k) f) :=
  have : PreservesLimitsOfSize.{w, w} (resFunctor f ⋙ forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesLimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesLimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Limits.PreservesColimits (resFunctor.{w} (k := k) f)
  body: have : PreservesColimitsOfSize.{w, w} (resFunctor (k := k) f ⋙
      forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

中文:
实例 :
  签名: Limits.PreservesColimits (resFunctor.{w} (k := k) f)
  定义体: have : PreservesColimitsOfSize.{w, w} (resFunctor (k := k) f ⋙
      forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))
-/
instance : Limits.PreservesColimits (resFunctor.{w} (k := k) f) :=
  have : PreservesColimitsOfSize.{w, w} (resFunctor (k := k) f ⋙
      forget₂ (Rep.{w} k H) (ModuleCat k)) :=
    inferInstanceAs (PreservesColimitsOfSize.{w, w} (forget₂ (Rep.{w} k G) (ModuleCat k)))
  preservesColimits_of_reflects_of_preserves _ (forget₂ (Rep.{w} k H) (ModuleCat k))

/--
lemma `isZero_res_iff` / 引理 `isZero_res_iff`

English:
lemma isZero_res_iff
  given: (M : Rep k G)
  proof: by
  rw [isZero_iff]; rw [isZero_iff]; rw [Rep.res_obj_V]

中文:
引理 isZero_res_iff
  条件: (M : Rep k G)
  证明: by
  rw [isZero_iff]; rw [isZero_iff]; rw [Rep.res_obj_V]

Depends on / 依赖: Rep.res_obj_V, isZero_iff, res_obj_V
-/
lemma isZero_res_iff (M : Rep k G) :
    IsZero (res f M) ↔ IsZero M := by
  rw [isZero_iff]; rw [isZero_iff]; rw [Rep.res_obj_V]

/--
lemma `res_map_exact` / 引理 `res_map_exact`

English:
lemma res_map_exact
  statement: {k : Type u} [CommRing k]
  proof: by
  rw [ShortComplex.exact_map_iff_of_faithful]

中文:
引理 res_map_exact
  结论: {k : 类型u} [交换环 k]
  证明: by
  rw [ShortComplex.exact_map_iff_of_faithful]

Depends on / 依赖: ShortComplex, ShortComplex.exact_map_iff_of_faithful, exact_map_iff_of_faithful
-/
lemma res_map_exact {k : Type u} [CommRing k]
    (S : ShortComplex (Rep.{w} k G)) :
    (S.map (resFunctor f)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `shortExact_res` / 引理 `shortExact_res`

English:
lemma shortExact_res
  given: {k : Type u} [CommRing k] (φ : H ->* G) {S : ShortComplex (Rep.{w} k G)}
  proof: by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, mono_iff_injective, ShortComplex.map_g,
      epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injecti

中文:
引理 shortExact_res
  条件: {k : 类型u} [交换环 k] (φ : H ->* G) {S : 短复形 (Rep.{w} k G)}
  证明: by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, mono_iff_injective, ShortComplex.map_g,
      epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injecti

Depends on / 依赖: ShortComplex, ShortComplex.exact_map_iff_of_faithful, ShortComplex.map_f, ShortComplex.map_g, epi_g, epi_iff_surjecti, epi_iff_surjective, exact_map_iff_of_faithful, map_f, map_g, mono_f, mono_iff_injective
-/
lemma shortExact_res {k : Type u} [CommRing k] (φ : H ->* G) {S : ShortComplex (Rep.{w} k G)} :
    (S.map (resFunctor φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_f, mono_iff_injective, ShortComplex.map_g,
      epi_iff_surjective] at h₂ h₃
    exact {exact := h₁, mono_f := mono_iff_injective _|>.2 h₂, epi_g := epi_iff_surjective _|>.2 h₃}
  · rintro @⟨_, mono_f, epi_g⟩
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa [mono_iff_injective] using! mono_f
      epi_g := by simpa [epi_iff_surjective] using! epi_g
    }

end ShortComplex

noncomputable section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/--
Definition of `ofQuotient` / `ofQuotient` 的定义

English:
abbreviation ofQuotient
  signature: : Rep k (G ⧸ S)
  body: Rep.of (A.ρ.ofQuotient S)

中文:
缩写 ofQuotient
  签名: : Rep k (G ⧸ S)
  定义体: Rep.of (A.ρ.ofQuotient S)

Depends on / 依赖: Rep.of, ofQuotient
-/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/--
Definition of `resOfQuotientIso` / `resOfQuotientIso` 的定义

English:
abbreviation resOfQuotientIso
  signature: : (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A
  body: Iso.refl _

中文:
缩写 resOfQuotientIso
  签名: : (res (商群.mk' S) (A.ofQuotient S)) ≅ A
  定义体: Iso.refl _

Depends on / 依赖: Iso.refl
-/
abbrev resOfQuotientIso : (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A := Iso.refl _

end

end

end Rep
