/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov, Frédéric Dupuis,
  Heather Macbeth
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Module.Submodule.RestrictScalars

/-!
# Kernel of a linear map

This file defines the kernel of a linear map.

## Main definitions

* `LinearMap.ker`: the kernel of a linear map as a submodule of the domain

## Notation

* We continue to use the notations `M →ₛₗ[σ] M₂` and `M →ₗ[R] M₂` for the type of semilinear
  (resp. linear) maps from `M` to `M₂` over the ring homomorphism `σ` (resp. over the ring `R`).

## Tags
linear algebra, vector space, module

-/

@[expose] public section

open Function
open scoped Pointwise

variable {R : Type*} {R₂ : Type*} {R₃ : Type*}
variable {K : Type*}
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {V : Type*} {V₂ : Type*}

/-! ### Properties of linear maps -/


namespace LinearMap

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]

open Submodule

variable {τ₁₂ : R ->+* R₂} {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/--
Definition of `ker` / `ker` 的定义

English:
definition ker
  signature: (f : M ->ₛₗ[τ₁₂] M₂)
  body: comap f ⊥

@[simp]

中文:
定义 ker
  签名: (f : M ->ₛₗ[τ₁₂] M₂)
  定义体: comap f ⊥

@[simp]
-/
def ker (f : M ->ₛₗ[τ₁₂] M₂) : Submodule R M :=
  comap f ⊥

@[simp]
/--
theorem `mem_ker` / 定理 `mem_ker`

English:
theorem mem_ker
  given: {f : M ->ₛₗ[τ₁₂] M₂} {y}
  statement: y in ker f ↔ f y = 0
  proof: mem_bot R₂

@[simp]

中文:
定理 mem_ker
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {y}
  结论: y in ker f ↔ f y = 0
  证明: mem_bot R₂

@[simp]

Depends on / 依赖: mem_bot
-/
theorem mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y = 0 :=
  mem_bot R₂

@[simp]
/--
theorem `ker_id` / 定理 `ker_id`

English:
theorem ker_id
  statement: ker (LinearMap.id : M ->ₗ[R] M) = ⊥
  proof: rfl

@[simp]

中文:
定理 ker_id
  结论: ker (LinearMap.id : M ->ₗ[R] M) = ⊥
  证明: rfl

@[simp]
-/
theorem ker_id : ker (LinearMap.id : M ->ₗ[R] M) = ⊥ :=
  rfl

@[simp]
/--
theorem `map_coe_ker` / 定理 `map_coe_ker`

English:
theorem map_coe_ker
  given: (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f)
  statement: f x = 0
  proof: mem_ker.1 x.2

中文:
定理 map_coe_ker
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f)
  结论: f x = 0
  证明: mem_ker.1 x.2

Depends on / 依赖: mem_ker
-/
theorem map_coe_ker (f : M ->ₛₗ[τ₁₂] M₂) (x : ker f) : f x = 0 :=
  mem_ker.1 x.2

/--
theorem `ker_toAddSubmonoid` / 定理 `ker_toAddSubmonoid`

English:
theorem ker_toAddSubmonoid
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: (ker f).toAddSubmonoid = (AddMonoidHom.mker f)
  proof: rfl

中文:
定理 ker_toAddSubmonoid
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: (ker f).toAddSubmonoid = (AddMonoidHom.mker f)
  证明: rfl
-/
theorem ker_toAddSubmonoid (f : M ->ₛₗ[τ₁₂] M₂) : (ker f).toAddSubmonoid = (AddMonoidHom.mker f) :=
  rfl

/--
theorem `le_ker_iff_comp_subtype_eq_zero` / 定理 `le_ker_iff_comp_subtype_eq_zero`

English:
theorem le_ker_iff_comp_subtype_eq_zero
  given: {N : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  rw [SetLike.le_def]; rw [LinearMap.ext_iff]; rw [Subtype.forall]; rfl

中文:
定理 le_ker_iff_comp_subtype_eq_zero
  条件: {N : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  rw [SetLike.le_def]; rw [LinearMap.ext_iff]; rw [Subtype.forall]; rfl

Depends on / 依赖: LinearMap, LinearMap.ext_iff, SetLike, SetLike.le_def, Subtype, Subtype.forall, ext_iff, le_def
-/
theorem le_ker_iff_comp_subtype_eq_zero {N : Submodule R M} {f : M ->ₛₗ[τ₁₂] M₂} :
    N <= ker f ↔ f ∘ₛₗ N.subtype = 0 := by
  rw [SetLike.le_def]; rw [LinearMap.ext_iff]; rw [Subtype.forall]; rfl

/--
theorem `comp_ker_subtype` / 定理 `comp_ker_subtype`

English:
theorem comp_ker_subtype
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: f.comp (ker f).subtype = 0
  proof: LinearMap.ext fun x => mem_ker.1 x.2

中文:
定理 comp_ker_subtype
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: f.comp (ker f).subtype = 0
  证明: LinearMap.ext fun x => mem_ker.1 x.2

Depends on / 依赖: LinearMap, LinearMap.ext, mem_ker
-/
theorem comp_ker_subtype (f : M ->ₛₗ[τ₁₂] M₂) : f.comp (ker f).subtype = 0 :=
  LinearMap.ext fun x => mem_ker.1 x.2

/--
theorem `ker_comp` / 定理 `ker_comp`

English:
theorem ker_comp
  given: (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃)
  proof: rfl

中文:
定理 ker_comp
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃)
  证明: rfl
-/
theorem ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) :
    ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g) :=
  rfl

/--
theorem `ker_le_ker_comp` / 定理 `ker_le_ker_comp`

English:
theorem ker_le_ker_comp
  given: (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃)
  proof: by rw [ker_comp]; exact comap_mono bot_le

中文:
定理 ker_le_ker_comp
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃)
  证明: by rw [ker_comp]; exact comap_mono bot_le

Depends on / 依赖: bot_le, comap_mono, ker_comp
-/
theorem ker_le_ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) :
    ker f <= ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) := by rw [ker_comp]; exact comap_mono bot_le

/--
theorem `ker_sup_ker_le_ker_comp_of_commute` / 定理 `ker_sup_ker_le_ker_comp_of_commute`

English:
theorem ker_sup_ker_le_ker_comp_of_commute
  given: {f g : M ->ₗ[R] M} (h : Commute f g)
  proof: by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]

中文:
定理 ker_sup_ker_le_ker_comp_of_commute
  条件: {f g : M ->ₗ[R] M} (h : Commute f g)
  证明: by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]

Depends on / 依赖: Module, Module.End.mul_eq_comp, h.eq, ker_le_ker_comp, mul_eq_comp, sup_le_iff, sup_le_iff.mpr
-/
theorem ker_sup_ker_le_ker_comp_of_commute {f g : M ->ₗ[R] M} (h : Commute f g) :
    ker f ⊔ ker g <= ker (f ∘ₗ g) := by
  refine sup_le_iff.mpr ⟨?_, ker_le_ker_comp g f⟩
  rw [← Module.End.mul_eq_comp]; rw [h.eq]; rw [Module.End.mul_eq_comp]
  exact ker_le_ker_comp f g

@[simp]
/--
theorem `ker_le_comap` / 定理 `ker_le_comap`

English:
theorem ker_le_comap
  given: {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ₁₂] M₂)
  proof: fun x hx => by simp [mem_ker.mp hx]

中文:
定理 ker_le_comap
  条件: {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ₁₂] M₂)
  证明: fun x hx => by simp [mem_ker.mp hx]

Depends on / 依赖: mem_ker, mem_ker.mp
-/
theorem ker_le_comap {p : Submodule R₂ M₂} (f : M ->ₛₗ[τ₁₂] M₂) :
    ker f <= p.comap f :=
  fun x hx => by simp [mem_ker.mp hx]

/--
theorem `disjoint_ker` / 定理 `disjoint_ker`

English:
theorem disjoint_ker
  given: {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  proof: by
  simp [disjoint_def]

中文:
定理 disjoint_ker
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  证明: by
  simp [disjoint_def]

Depends on / 依赖: disjoint_def
-/
theorem disjoint_ker {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    Disjoint p (ker f) ↔ forall x in p, f x = 0 -> x = 0 := by
  simp [disjoint_def]

/--
theorem `ker_eq_bot'` / 定理 `ker_eq_bot'`

English:
theorem ker_eq_bot'
  given: {f : M ->ₛₗ[τ₁₂] M₂}
  statement: ker f = ⊥ ↔ forall m, f m = 0 -> m = 0
  proof: by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)

中文:
定理 ker_eq_bot'
  条件: {f : M ->ₛₗ[τ₁₂] M₂}
  结论: ker f = ⊥ ↔ 对任意 m, f m = 0 -> m = 0
  证明: by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)

Depends on / 依赖: disjoint_iff_inf_le, disjoint_ker
-/
theorem ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ forall m, f m = 0 -> m = 0 := by
  simpa [disjoint_iff_inf_le] using disjoint_ker (f := f) (p := ⊤)

/--
theorem `ker_eq_bot_of_inverse` / 定理 `ker_eq_bot_of_inverse`

English:
theorem ker_eq_bot_of_inverse
  statement: {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M ->ₛₗ[τ₁₂] M₂}
  proof: ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]

中文:
定理 ker_eq_bot_of_inverse
  结论: {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M ->ₛₗ[τ₁₂] M₂}
  证明: ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]

Depends on / 依赖: comp_apply, g.map_zero, id_apply, ker_eq_bot, map_zero
-/
theorem ker_eq_bot_of_inverse {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁] {f : M ->ₛₗ[τ₁₂] M₂}
    {g : M₂ ->ₛₗ[τ₂₁] M} (h : (g.comp f : M ->ₗ[R] M) = id) : ker f = ⊥ :=
  ker_eq_bot'.2 fun m hm => by rw [← id_apply (R := R) m, ← h, comp_apply, hm, g.map_zero]

/--
theorem `le_ker_iff_map` / 定理 `le_ker_iff_map`

English:
theorem le_ker_iff_map
  given: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  proof: by rw [ker, eq_bot_iff, map_le_iff_le_comap]

@[simp]

中文:
定理 le_ker_iff_map
  条件: [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M}
  证明: by rw [ker, eq_bot_iff, map_le_iff_le_comap]

@[simp]

Depends on / 依赖: eq_bot_iff, map_le_iff_le_comap
-/
theorem le_ker_iff_map [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R M} :
    p <= ker f ↔ map f p = ⊥ := by rw [ker, eq_bot_iff, map_le_iff_le_comap]

@[simp]
/--
theorem `ker_codRestrict` / 定理 `ker_codRestrict`

English:
theorem ker_codRestrict
  given: (p : Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂) (hf)
  proof: by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl

中文:
定理 ker_codRestrict
  条件: (p : Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂) (hf)
  证明: by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl

Depends on / 依赖: Submodule, Submodule.map_bot, comap_codRestrict, map_bot
-/
theorem ker_codRestrict (p : Submodule R₂ M₂) (f : M ->ₛₗ[τ₁₂] M₂) (hf) :
    ker (codRestrict p f hf) = ker f := by rw [ker, comap_codRestrict, Submodule.map_bot]; rfl

/--
lemma `ker_domRestrict` / 引理 `ker_domRestrict`

English:
lemma ker_domRestrict
  given: (p : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂)
  proof: ker_comp ..

中文:
引理 ker_domRestrict
  条件: (p : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂)
  证明: ker_comp ..

Depends on / 依赖: ker_comp
-/
lemma ker_domRestrict (p : Submodule R M) (f : M ->ₛₗ[τ₁₂] M₂) :
    ker (domRestrict f p) = (ker f).comap p.subtype := ker_comp ..

set_option backward.isDefEq.respectTransparency false in
/--
theorem `ker_restrict` / 定理 `ker_restrict`

English:
theorem ker_restrict
  statement: {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [ker_codRestrict]; rw [ker_domRestrict]

@[simp]

中文:
定理 ker_restrict
  结论: {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  rw [restrict_eq_codRestrict_domRestrict]; rw [ker_codRestrict]; rw [ker_domRestrict]

@[simp]

Depends on / 依赖: ker_codRestrict, ker_domRestrict, restrict_eq_codRestrict_domRestrict
-/
theorem ker_restrict {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
    (hf : forall x : M, x in p -> f x in q) :
    ker (f.restrict hf) = (ker f).comap p.subtype := by
  rw [restrict_eq_codRestrict_domRestrict]; rw [ker_codRestrict]; rw [ker_domRestrict]

@[simp]
/--
theorem `ker_zero` / 定理 `ker_zero`

English:
theorem ker_zero
  statement: ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
  proof: eq_top_iff'.2 fun x => by simp

@[simp]

中文:
定理 ker_zero
  结论: ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤
  证明: eq_top_iff'.2 fun x => by simp

@[simp]

Depends on / 依赖: eq_top_iff
-/
theorem ker_zero : ker (0 : M ->ₛₗ[τ₁₂] M₂) = ⊤ :=
  eq_top_iff'.2 fun x => by simp

@[simp]
/--
theorem `ker_eq_top` / 定理 `ker_eq_top`

English:
theorem ker_eq_top
  given: {f : M ->ₛₗ[τ₁₂] M₂}
  statement: ker f = ⊤ ↔ f = 0
  proof: ⟨fun h => ext fun _ => mem_ker.1 h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩

@[simp]

中文:
定理 ker_eq_top
  条件: {f : M ->ₛₗ[τ₁₂] M₂}
  结论: ker f = ⊤ ↔ f = 0
  证明: ⟨fun h => ext fun _ => mem_ker.1 h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩

@[simp]

Depends on / 依赖: h.symm, ker_zero, mem_ker
-/
theorem ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 0 :=
⟨fun h => ext fun _ => mem_ker.1 h.symm ▸ trivial, fun h => h.symm ▸ ker_zero⟩

@[simp]
/--
lemma `domRestrict_ker_self` / 引理 `domRestrict_ker_self`

English:
lemma domRestrict_ker_self
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: f.domRestrict f.ker = 0
  proof: by
  ext; simp

中文:
引理 domRestrict_ker_self
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: f.domRestrict f.ker = 0
  证明: by
  ext; simp
-/
lemma domRestrict_ker_self (f : M ->ₛₗ[τ₁₂] M₂) : f.domRestrict f.ker = 0 := by
  ext; simp

/--
theorem `exists_ne_zero_of_sSup_eq_top` / 定理 `exists_ne_zero_of_sSup_eq_top`

English:
theorem exists_ne_zero_of_sSup_eq_top
  statement: {f : M ->ₛₗ[τ₁₂] M₂} (h : f != 0) (s : Set (Submodule R M))
  proof: by
  contrapose! h
  simp_rw [← ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, le_ker_iff_comp_subtype_eq_zero]
  exact h

@[simp]

中文:
定理 exists_ne_zero_of_sSup_eq_top
  结论: {f : M ->ₛₗ[τ₁₂] M₂} (h : f != 0) (s : Set (Submodule R M))
  证明: by
  contrapose! h
  simp_rw [← ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, le_ker_iff_comp_subtype_eq_zero]
  exact h

@[simp]

Depends on / 依赖: contrapose, eq_top_iff, ker_eq_top, le_ker_iff_comp_subtype_eq_zero, sSup_le_iff, simp_rw
-/
theorem exists_ne_zero_of_sSup_eq_top {f : M ->ₛₗ[τ₁₂] M₂} (h : f != 0) (s : Set (Submodule R M))
    (hs : sSup s = ⊤) : exists m in s, f ∘ₛₗ m.subtype != 0 := by
  contrapose! h
  simp_rw [← ker_eq_top, eq_top_iff, ← hs, sSup_le_iff, le_ker_iff_comp_subtype_eq_zero]
  exact h

@[simp]
/--
theorem `_root_.AddMonoidHom.coe_toIntLinearMap_ker` / 定理 `_root_.AddMonoidHom.coe_toIntLinearMap_ker`

English:
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker
  statement: {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
  proof: rfl

中文:
定理 _root_.AddMonoidHom.coe_toIntLinearMap_ker
  结论: {M M₂ : 类型} [AddCommGroup M] [AddCommGroup M₂]
  证明: rfl
-/
theorem _root_.AddMonoidHom.coe_toIntLinearMap_ker {M M₂ : Type*} [AddCommGroup M] [AddCommGroup M₂]
    (f : M ->+ M₂) : LinearMap.ker f.toIntLinearMap = AddSubgroup.toIntSubmodule f.ker := rfl

/--
theorem `ker_eq_bot_of_injective` / 定理 `ker_eq_bot_of_injective`

English:
theorem ker_eq_bot_of_injective
  given: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Injective f)
  statement: ker f = ⊥
  proof: by
  rw [eq_bot_iff]
  intro x hx
  simpa only [mem_ker, mem_bot, ← map_zero f, hf.eq_iff] using hx

中文:
定理 ker_eq_bot_of_injective
  条件: {f : M ->ₛₗ[τ₁₂] M₂} (hf : Injective f)
  结论: ker f = ⊥
  证明: by
  rw [eq_bot_iff]
  intro x hx
  simpa only [mem_ker, mem_bot, ← map_zero f, hf.eq_iff] using hx

Depends on / 依赖: eq_bot_iff, eq_iff, hf.eq_iff, map_zero, mem_bot, mem_ker
-/
theorem ker_eq_bot_of_injective {f : M ->ₛₗ[τ₁₂] M₂} (hf : Injective f) : ker f = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa only [mem_ker, mem_bot, ← map_zero f, hf.eq_iff] using hx

/-- The increasing sequence of submodules consisting of the kernels of the iterates of a linear map.
-/
@[simps]
/--
Definition of `iterateKer` / `iterateKer` 的定义

English:
definition iterateKer
  signature: (f : M ->ₗ[R] M)
  body: ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker]; rw [add_comm]; rw [pow_add]; rw [Module.End.mul_apply]; rw [h]; rw [map_zero]

中文:
定义 iterateKer
  签名: (f : M ->ₗ[R] M)
  定义体: ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker]; rw [add_comm]; rw [pow_add]; rw [Module.End.mul_apply]; rw [h]; rw [map_zero]
-/
def iterateKer (f : M ->ₗ[R] M) : Nat ->o Submodule R M where
  toFun n := ker (f ^ n)
  monotone' n m w x h := by
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le w
    rw [LinearMap.mem_ker] at h
    rw [LinearMap.mem_ker]; rw [add_comm]; rw [pow_add]; rw [Module.End.mul_apply]; rw [h]; rw [map_zero]

/--
lemma `ker_submoduleMap` / 引理 `ker_submoduleMap`

English:
lemma ker_submoduleMap
  statement: {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁]
  proof: by
  ext; simp [Subtype.ext_iff]

中文:
引理 ker_submoduleMap
  结论: {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁]
  证明: by
  ext; simp [Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.ext_iff, ext_iff
-/
lemma ker_submoduleMap {τ₂₁ : R₂ ->+* R} [RingHomInvPair τ₁₂ τ₂₁]
    (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule R M) :
    (f.submoduleMap p).ker = f.ker.comap p.subtype := by
  ext; simp [Subtype.ext_iff]

end AddCommMonoid

section Ring

variable [Ring R] [Ring R₂]
variable [AddCommGroup M] [AddCommGroup M₂]
variable [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂}
variable {f : M ->ₛₗ[τ₁₂] M₂}

open Submodule

/--
theorem `ker_neg` / 定理 `ker_neg`

English:
theorem ker_neg
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: (-f).ker = f.ker
  proof: by ext; simp

中文:
定理 ker_neg
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: (-f).ker = f.ker
  证明: by ext; simp
-/
@[simp] theorem ker_neg (f : M ->ₛₗ[τ₁₂] M₂) : (-f).ker = f.ker := by ext; simp

/--
theorem `ker_toAddSubgroup` / 定理 `ker_toAddSubgroup`

English:
theorem ker_toAddSubgroup
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: (ker f).toAddSubgroup = f.toAddMonoidHom.ker
  proof: rfl

中文:
定理 ker_toAddSubgroup
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: (ker f).toAddSubgroup = f.toAddMonoidHom.ker
  证明: rfl
-/
theorem ker_toAddSubgroup (f : M ->ₛₗ[τ₁₂] M₂) : (ker f).toAddSubgroup = f.toAddMonoidHom.ker :=
  rfl

/--
theorem `sub_mem_ker_iff` / 定理 `sub_mem_ker_iff`

English:
theorem sub_mem_ker_iff
  given: {x y}
  statement: x - y in ker f ↔ f x = f y
  proof: by rw [mem_ker, map_sub, sub_eq_zero]

中文:
定理 sub_mem_ker_iff
  条件: {x y}
  结论: x - y in ker f ↔ f x = f y
  证明: by rw [mem_ker, map_sub, sub_eq_zero]

Depends on / 依赖: map_sub, mem_ker, sub_eq_zero
-/
theorem sub_mem_ker_iff {x y} : x - y in ker f ↔ f x = f y := by rw [mem_ker, map_sub, sub_eq_zero]

/--
theorem `disjoint_ker_iff_injOn` / 定理 `disjoint_ker_iff_injOn`

English:
theorem disjoint_ker_iff_injOn
  given: {p : Submodule R M}
  proof: by
  rw [disjoint_ker]; rw [Set.injOn_iff_map_eq_zero]

中文:
定理 disjoint_ker_iff_injOn
  条件: {p : Submodule R M}
  证明: by
  rw [disjoint_ker]; rw [Set.injOn_iff_map_eq_zero]

Depends on / 依赖: Set.injOn_iff_map_eq_zero, disjoint_ker, injOn_iff_map_eq_zero
-/
theorem disjoint_ker_iff_injOn {p : Submodule R M} :
    Disjoint p (LinearMap.ker f) ↔ Set.InjOn f p := by
  rw [disjoint_ker]; rw [Set.injOn_iff_map_eq_zero]

/--
theorem `injOn_of_disjoint_ker` / 定理 `injOn_of_disjoint_ker`

English:
theorem injOn_of_disjoint_ker
  statement: {p : Submodule R M} {s : Set M} (h : s subseteq p)
  proof: .mono h disjoint_ker_iff_injOn.mp hd

中文:
定理 injOn_of_disjoint_ker
  结论: {p : Submodule R M} {s : Set M} (h : s subseteq p)
  证明: .mono h disjoint_ker_iff_injOn.mp hd

Depends on / 依赖: disjoint_ker_iff_injOn, disjoint_ker_iff_injOn.mp
-/
theorem injOn_of_disjoint_ker {p : Submodule R M} {s : Set M} (h : s subseteq p)
    (hd : Disjoint p (ker f)) : Set.InjOn f s :=
.mono h disjoint_ker_iff_injOn.mp hd

/--
theorem `ker_eq_bot` / 定理 `ker_eq_bot`

English:
theorem ker_eq_bot
  given: {f : M ->ₛₗ[τ₁₂] M₂}
  statement: ker f = ⊥ ↔ Injective f
  proof: by
  simpa [disjoint_iff_inf_le] using disjoint_ker_iff_injOn (f := f) (p := ⊤)

中文:
定理 ker_eq_bot
  条件: {f : M ->ₛₗ[τ₁₂] M₂}
  结论: ker f = ⊥ ↔ Injective f
  证明: by
  simpa [disjoint_iff_inf_le] using disjoint_ker_iff_injOn (f := f) (p := ⊤)

Depends on / 依赖: disjoint_iff_inf_le, disjoint_ker_iff_injOn
-/
theorem ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Injective f := by
  simpa [disjoint_iff_inf_le] using disjoint_ker_iff_injOn (f := f) (p := ⊤)

/--
lemma `injective_domRestrict_iff` / 引理 `injective_domRestrict_iff`

English:
lemma injective_domRestrict_iff
  given: {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M}
  proof: by
  simp [← ker_eq_bot, ker_domRestrict, disjoint_iff_comap_eq_bot]

@[simp]

中文:
引理 injective_domRestrict_iff
  条件: {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M}
  证明: by
  simp [← ker_eq_bot, ker_domRestrict, disjoint_iff_comap_eq_bot]

@[simp]
-/
@[simp] lemma injective_domRestrict_iff {f : M ->ₛₗ[τ₁₂] M₂} {S : Submodule R M} :
    Injective (f.domRestrict S) ↔ Disjoint S f.ker := by
  simp [← ker_eq_bot, ker_domRestrict, disjoint_iff_comap_eq_bot]

@[simp]
/--
theorem `injective_restrict_iff` / 定理 `injective_restrict_iff`

English:
theorem injective_restrict_iff
  statement: {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  proof: by
  simp [← ker_eq_bot, ker_restrict, disjoint_iff_comap_eq_bot]

@[deprecated (since := "2026-07-01")]
alias injective_restrict_iff_disjoint := injective_restrict_iff

@[simp]

中文:
定理 injective_restrict_iff
  结论: {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  证明: by
  simp [← ker_eq_bot, ker_restrict, disjoint_iff_comap_eq_bot]

@[deprecated (since := "2026-07-01")]
alias injective_restrict_iff_disjoint := injective_restrict_iff

@[simp]

Depends on / 依赖: disjoint_iff_comap_eq_bot, ker_eq_bot, ker_restrict
-/
theorem injective_restrict_iff {p : Submodule R M} {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
    (hf : forall x in p, f x in q) : Injective (f.restrict hf) ↔ Disjoint p (ker f) := by
  simp [← ker_eq_bot, ker_restrict, disjoint_iff_comap_eq_bot]

@[deprecated (since := "2026-07-01")]
alias injective_restrict_iff_disjoint := injective_restrict_iff

@[simp]
/--
theorem `injective_codRestrict_iff` / 定理 `injective_codRestrict_iff`

English:
theorem injective_codRestrict_iff
  statement: {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  proof: Set.injective_codRestrict _

中文:
定理 injective_codRestrict_iff
  结论: {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
  证明: Set.injective_codRestrict _

Depends on / 依赖: Set.injective_codRestrict, injective_codRestrict
-/
theorem injective_codRestrict_iff {q : Submodule R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂}
    (hf : forall x, f x in q) : Injective (f.codRestrict q hf) ↔ Injective f :=
  Set.injective_codRestrict _

end Ring

section CommSemiring

variable [Semiring R] [CommSemiring R₂]
variable [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
variable {τ₁₂ : R ->+* R₂}

/--
theorem `ker_le_ker_smul` / 定理 `ker_le_ker_smul`

English:
theorem ker_le_ker_smul
  given: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  statement: ker f <= ker (c • f)
  proof: by
  simpa only [ker] using Submodule.comap_le_comap_smul _ _ _

中文:
定理 ker_le_ker_smul
  条件: (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂)
  结论: ker f <= ker (c • f)
  证明: by
  simpa only [ker] using Submodule.comap_le_comap_smul _ _ _

Depends on / 依赖: Submodule, Submodule.comap_le_comap_smul, comap_le_comap_smul
-/
theorem ker_le_ker_smul (f : M ->ₛₗ[τ₁₂] M₂) (c : R₂) : ker f <= ker (c • f) := by
  simpa only [ker] using Submodule.comap_le_comap_smul _ _ _

end CommSemiring

section Semifield

variable [Semifield K]
variable [AddCommMonoid V] [Module K V]
variable [AddCommMonoid V₂] [Module K V₂]

/--
theorem `ker_smul` / 定理 `ker_smul`

English:
theorem ker_smul
  given: (f : V ->ₗ[K] V₂) (a : K) (h : a != 0)
  statement: ker (a • f) = ker f
  proof: Submodule.comap_smul f _ a h

中文:
定理 ker_smul
  条件: (f : V ->ₗ[K] V₂) (a : K) (h : a != 0)
  结论: ker (a • f) = ker f
  证明: Submodule.comap_smul f _ a h

Depends on / 依赖: Submodule, Submodule.comap_smul, comap_smul
-/
theorem ker_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : ker (a • f) = ker f :=
  Submodule.comap_smul f _ a h

/--
theorem `ker_smul'` / 定理 `ker_smul'`

English:
theorem ker_smul'
  given: (f : V ->ₗ[K] V₂) (a : K)
  statement: ker (a • f) = ⨅ _ : a != 0, ker f
  proof: Submodule.comap_smul' f _ a

中文:
定理 ker_smul'
  条件: (f : V ->ₗ[K] V₂) (a : K)
  结论: ker (a • f) = ⨅ _ : a != 0, ker f
  证明: Submodule.comap_smul' f _ a

Depends on / 依赖: Submodule, Submodule.comap_smul, comap_smul
-/
theorem ker_smul' (f : V ->ₗ[K] V₂) (a : K) : ker (a • f) = ⨅ _ : a != 0, ker f :=
  Submodule.comap_smul' f _ a

end Semifield

end LinearMap

namespace Submodule

section AddCommMonoid

variable [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂]
variable [Module R M] [Module R₂ M₂]
variable (p : Submodule R M)
variable {τ₁₂ : R ->+* R₂}

open LinearMap

@[simp]
/--
theorem `comap_bot` / 定理 `comap_bot`

English:
theorem comap_bot
  given: (f : M ->ₛₗ[τ₁₂] M₂)
  statement: comap f ⊥ = ker f
  proof: rfl

@[simp]

中文:
定理 comap_bot
  条件: (f : M ->ₛₗ[τ₁₂] M₂)
  结论: comap f ⊥ = ker f
  证明: rfl

@[simp]
-/
theorem comap_bot (f : M ->ₛₗ[τ₁₂] M₂) : comap f ⊥ = ker f :=
  rfl

@[simp]
/--
theorem `ker_subtype` / 定理 `ker_subtype`

English:
theorem ker_subtype
  statement: ker p.subtype = ⊥
  proof: ker_eq_bot_of_injective fun _ _ => Subtype.ext

@[simp]

中文:
定理 ker_subtype
  结论: ker p.subtype = ⊥
  证明: ker_eq_bot_of_injective fun _ _ => Subtype.ext

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, ker_eq_bot_of_injective
-/
theorem ker_subtype : ker p.subtype = ⊥ :=
  ker_eq_bot_of_injective fun _ _ => Subtype.ext

@[simp]
/--
theorem `ker_inclusion` / 定理 `ker_inclusion`

English:
theorem ker_inclusion
  given: (p p' : Submodule R M) (h : p <= p')
  statement: ker (inclusion h) = ⊥
  proof: by
  rw [inclusion]; rw [ker_codRestrict]; rw [ker_subtype]

中文:
定理 ker_inclusion
  条件: (p p' : Submodule R M) (h : p <= p')
  结论: ker (inclusion h) = ⊥
  证明: by
  rw [inclusion]; rw [ker_codRestrict]; rw [ker_subtype]

Depends on / 依赖: inclusion, ker_codRestrict, ker_subtype
-/
theorem ker_inclusion (p p' : Submodule R M) (h : p <= p') : ker (inclusion h) = ⊥ := by
  rw [inclusion]; rw [ker_codRestrict]; rw [ker_subtype]

end AddCommMonoid

end Submodule

namespace LinearMap

section Semiring

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable [Module R M] [Module R₂ M₂] [Module R₃ M₃]
variable {τ₁₂ : R ->+* R₂} {τ₂₃ : R₂ ->+* R₃} {τ₁₃ : R ->+* R₃}
variable [RingHomCompTriple τ₁₂ τ₂₃ τ₁₃]

/--
theorem `ker_comp_of_ker_eq_bot` / 定理 `ker_comp_of_ker_eq_bot`

English:
theorem ker_comp_of_ker_eq_bot
  given: (f : M ->ₛₗ[τ₁₂] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥)
  proof: by rw [ker_comp, hg, Submodule.comap_bot]

中文:
定理 ker_comp_of_ker_eq_bot
  条件: (f : M ->ₛₗ[τ₁₂] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥)
  证明: by rw [ker_comp, hg, Submodule.comap_bot]

Depends on / 依赖: Submodule, Submodule.comap_bot, comap_bot, ker_comp
-/
theorem ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) :
    ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = ker f := by rw [ker_comp, hg, Submodule.comap_bot]

end Semiring

section RestrictScalars

variable (R : Type*) {S M N : Type*} [Semiring R] [Semiring S] [SMul R S]
variable [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

@[simp]
/--
theorem `ker_restrictScalars` / 定理 `ker_restrictScalars`

English:
theorem ker_restrictScalars
  given: (f : M ->ₗ[S] N)
  proof: rfl

中文:
定理 ker_restrictScalars
  条件: (f : M ->ₗ[S] N)
  证明: rfl
-/
theorem ker_restrictScalars (f : M ->ₗ[S] N) :
    ker (f.restrictScalars R) = (ker f).restrictScalars R :=
  rfl

end RestrictScalars

end LinearMap

/-! ### Linear equivalences -/


namespace LinearEquiv

section AddCommMonoid

section

variable [Semiring R] [Semiring R₂] [Semiring R₃]
variable [AddCommMonoid M] [AddCommMonoid M₂] [AddCommMonoid M₃]
variable {module_M : Module R M} {module_M₂ : Module R₂ M₂} {module_M₃ : Module R₃ M₃}
variable {σ₁₂ : R ->+* R₂} {σ₂₁ : R₂ ->+* R}
variable {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
variable {σ₃₂ : R₃ ->+* R₂}
variable {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}
variable {re₂₃ : RingHomInvPair σ₂₃ σ₃₂} {re₃₂ : RingHomInvPair σ₃₂ σ₂₃}
variable (e : M ≃ₛₗ[σ₁₂] M₂) (e'' : M₂ ≃ₛₗ[σ₂₃] M₃)

@[simp]
/--
theorem `ker` / 定理 `ker`

English:
theorem ker
  statement: LinearMap.ker (e : M ->ₛₗ[σ₁₂] M₂) = ⊥
  proof: LinearMap.ker_eq_bot_of_injective e.toEquiv.injective

@[simp]

中文:
定理 ker
  结论: LinearMap.ker (e : M ->ₛₗ[σ₁₂] M₂) = ⊥
  证明: LinearMap.ker_eq_bot_of_injective e.toEquiv.injective

@[simp]
-/
protected theorem ker : LinearMap.ker (e : M ->ₛₗ[σ₁₂] M₂) = ⊥ :=
  LinearMap.ker_eq_bot_of_injective e.toEquiv.injective

@[simp]
/--
theorem `ker_comp` / 定理 `ker_comp`

English:
theorem ker_comp
  given: (l : M ->ₛₗ[σ₁₂] M₂)
  proof: LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

中文:
定理 ker_comp
  条件: (l : M ->ₛₗ[σ₁₂] M₂)
  证明: LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

Depends on / 依赖: LinearMap, LinearMap.ker_comp_of_ker_eq_bot, ker_comp_of_ker_eq_bot
-/
theorem ker_comp (l : M ->ₛₗ[σ₁₂] M₂) :
    LinearMap.ker (((e'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) =
    LinearMap.ker l :=
  LinearMap.ker_comp_of_ker_eq_bot _ e''.ker

end

end AddCommMonoid

end LinearEquiv
