/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Projection to a subspace

In this file we define
* `Submodule.projectionOnto (p q : Submodule R E) (h : IsCompl p q)`:
  the projection of a module `E` to a submodule `p` along its complement `q`;
  it is the unique linear map `f : E → p` such that `f x = x` for `x ∈ p` and `f x = 0` for `x ∈ q`.
* `Submodule.projection` (p q : Submodule R E) (h : IsCompl p q)`:
  the projection `Submodule.projectionOnto` as a linear map from `E` to `E`.
* `Submodule.isComplEquivProj p`: equivalence between submodules `q`
  such that `IsCompl p q` and projections `f : E → p`, `∀ x ∈ p, f x = x`.

We also provide some lemmas justifying correctness of our definitions.

## Tags

projection, complement subspace
-/

@[expose] public section

noncomputable section Ring

variable {R : Type*} [Ring R] {E : Type*} [AddCommGroup E] [Module R E]
variable {F : Type*} [AddCommGroup F] [Module R F] {G : Type*} [AddCommGroup G] [Module R G]
variable (p q : Submodule R E)
variable {S : Type*} [Semiring S] {M : Type*} [AddCommMonoid M] [Module S M] (m : Submodule S M)

namespace LinearMap

variable {p}

open Submodule

/--
theorem `ker_id_sub_eq_of_proj` / 定理 `ker_id_sub_eq_of_proj`

English:
theorem ker_id_sub_eq_of_proj
  given: {f : E ->ₗ[R] p} (hf : forall x : p, f x = x)
  proof: by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

中文:
定理 ker_id_sub_eq_of_proj
  条件: {f : E ->ₗ[R] p} (hf : 对任意 x : p, f x = x)
  证明: by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

Depends on / 依赖: Submodule, Submodule.coe_mem, Subtype, Subtype.coe_mk, coe_mem, coe_mk, comp_apply, h.symm, id_apply, mem_ker, sub_apply, sub_eq_zero, subtype_apply
-/
theorem ker_id_sub_eq_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) :
    ker (id - p.subtype.comp f) = p := by
  ext x
  simp only [comp_apply, mem_ker, subtype_apply, sub_apply, id_apply, sub_eq_zero]
  exact ⟨fun h => h.symm ▸ Submodule.coe_mem _, fun hx => by rw [hf ⟨x, hx⟩, Subtype.coe_mk]⟩

/--
theorem `range_eq_of_proj` / 定理 `range_eq_of_proj`

English:
theorem range_eq_of_proj
  given: {f : E ->ₗ[R] p} (hf : forall x : p, f x = x)
  statement: range f = ⊤
  proof: range_eq_top.2 fun x => ⟨x, hf x⟩

中文:
定理 range_eq_of_proj
  条件: {f : E ->ₗ[R] p} (hf : 对任意 x : p, f x = x)
  结论: range f = ⊤
  证明: range_eq_top.2 fun x => ⟨x, hf x⟩

Depends on / 依赖: range_eq_top
-/
theorem range_eq_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) : range f = ⊤ :=
  range_eq_top.2 fun x => ⟨x, hf x⟩

/--
theorem `isCompl_of_proj` / 定理 `isCompl_of_proj`

English:
theorem isCompl_of_proj
  given: {f : E ->ₗ[R] p} (hf : forall x : p, f x = x)
  statement: IsCompl p (ker f)
  proof: by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe]; rw [mem_ker]; rw [hf ⟨x]; rw [hpx⟩]; rw [mk_eq_zero] at hfx
    simp only [hfx, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩

中文:
定理 isCompl_of_proj
  条件: {f : E ->ₗ[R] p} (hf : 对任意 x : p, f x = x)
  结论: IsCompl p (ker f)
  证明: by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe]; rw [mem_ker]; rw [hf ⟨x]; rw [hpx⟩]; rw [mk_eq_zero] at hfx
    simp only [hfx, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩

Depends on / 依赖: SetLike, SetLike.mem_coe, add_sub_cancel, codisjoint_iff_le_sup, disjoint_iff_inf_le, map_sub, mem_coe, mem_ker, mem_sup, mk_eq_zero, sub_self, zero_mem
-/
theorem isCompl_of_proj {f : E ->ₗ[R] p} (hf : forall x : p, f x = x) : IsCompl p (ker f) := by
  constructor
  · rw [disjoint_iff_inf_le]
    rintro x ⟨hpx, hfx⟩
    rw [SetLike.mem_coe]; rw [mem_ker]; rw [hf ⟨x]; rw [hpx⟩]; rw [mk_eq_zero] at hfx
    simp only [hfx, zero_mem]
  · rw [codisjoint_iff_le_sup]
    intro x _
    rw [mem_sup']
    refine ⟨f x, ⟨x - f x, ?_⟩, add_sub_cancel _ _⟩
    rw [mem_ker]; rw [map_sub]; rw [hf]; rw [sub_self]

end LinearMap

namespace Submodule

open LinearMap

/--
Definition of `prodEquivOfIsCompl` / `prodEquivOfIsCompl` 的定义

English:
definition prodEquivOfIsCompl
  signature: (h : IsCompl p q)
  body: by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    rw [range_subtype]; rw [range_subtype]
    exact h.1
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]

@[simp]

中文:
定义 prodEquivOfIsCompl
  签名: (h : IsCompl p q)
  定义体: by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    rw [range_subtype]; rw [range_subtype]
    exact h.1
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, coprod, h.sup_eq_top, ker_coprod_of_disjoint_range, ker_eq_bot, ker_subtype, ofBijective, p.subtype.coprod, prod_bot, q.subtype, range_eq_top, range_subtype, subtype, sup_eq_range, sup_eq_top
-/
def prodEquivOfIsCompl (h : IsCompl p q) : (p × q) ≃ₗ[R] E := by
  apply LinearEquiv.ofBijective (p.subtype.coprod q.subtype)
  constructor
  · rw [← ker_eq_bot, ker_coprod_of_disjoint_range, ker_subtype, ker_subtype, prod_bot]
    rw [range_subtype]; rw [range_subtype]
    exact h.1
  · rw [← range_eq_top, ← sup_eq_range, h.sup_eq_top]

@[simp]
/--
theorem `coe_prodEquivOfIsCompl` / 定理 `coe_prodEquivOfIsCompl`

English:
theorem coe_prodEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: rfl

@[simp]

中文:
定理 coe_prodEquivOfIsCompl
  条件: (h : IsCompl p q)
  证明: rfl

@[simp]
-/
theorem coe_prodEquivOfIsCompl (h : IsCompl p q) :
    (prodEquivOfIsCompl p q h : p × q ->ₗ[R] E) = p.subtype.coprod q.subtype := rfl

@[simp]
/--
theorem `coe_prodEquivOfIsCompl'` / 定理 `coe_prodEquivOfIsCompl'`

English:
theorem coe_prodEquivOfIsCompl'
  given: (h : IsCompl p q) (x : p × q)
  proof: rfl

中文:
定理 coe_prodEquivOfIsCompl'
  条件: (h : IsCompl p q) (x : p × q)
  证明: rfl
-/
theorem coe_prodEquivOfIsCompl' (h : IsCompl p q) (x : p × q) :
    prodEquivOfIsCompl p q h x = x.1 + x.2 := rfl

/--
theorem `prodEquivOfIsCompl_symm_apply_left` / 定理 `prodEquivOfIsCompl_symm_apply_left`

English:
theorem prodEquivOfIsCompl_symm_apply_left
  given: (h : IsCompl p q) (x : p)
  proof: (prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

中文:
定理 prodEquivOfIsCompl_symm_apply_left
  条件: (h : IsCompl p q) (x : p)
  证明: (prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

Depends on / 依赖: prodEquivOfIsCompl, symm_apply_eq
-/
theorem prodEquivOfIsCompl_symm_apply_left (h : IsCompl p q) (x : p) :
    (prodEquivOfIsCompl p q h).symm x = (x, 0) :=
(prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

/--
theorem `prodEquivOfIsCompl_symm_apply_right` / 定理 `prodEquivOfIsCompl_symm_apply_right`

English:
theorem prodEquivOfIsCompl_symm_apply_right
  given: (h : IsCompl p q) (x : q)
  proof: (prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

中文:
定理 prodEquivOfIsCompl_symm_apply_right
  条件: (h : IsCompl p q) (x : q)
  证明: (prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

Depends on / 依赖: prodEquivOfIsCompl, symm_apply_eq
-/
theorem prodEquivOfIsCompl_symm_apply_right (h : IsCompl p q) (x : q) :
    (prodEquivOfIsCompl p q h).symm x = (0, x) :=
(prodEquivOfIsCompl p q h).symm_apply_eq.2 by simp

/--
theorem `prodEquivOfIsCompl_symm_apply_fst_eq_zero` / 定理 `prodEquivOfIsCompl_symm_apply_fst_eq_zero`

English:
theorem prodEquivOfIsCompl_symm_apply_fst_eq_zero
  given: (h : IsCompl p q) {x : E}
  proof: by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_left _ (Submodule.coe_mem _)]; rw [mem_right_iff_eq_zero_of_disjoint h.disjoint]

中文:
定理 prodEquivOfIsCompl_symm_apply_fst_eq_zero
  条件: (h : IsCompl p q) {x : E}
  证明: by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_left _ (Submodule.coe_mem _)]; rw [mem_right_iff_eq_zero_of_disjoint h.disjoint]

Depends on / 依赖: Submodule, Submodule.add_mem_iff_left, Submodule.coe_mem, add_mem_iff_left, apply_symm_apply, coe_mem, coe_prodEquivOfIsCompl, conv_rhs, disjoint, h.disjoint, mem_right_iff_eq_zero_of_disjoint, prodEquivOfIsCompl
-/
theorem prodEquivOfIsCompl_symm_apply_fst_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).1 = 0 ↔ x in q := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_left _ (Submodule.coe_mem _)]; rw [mem_right_iff_eq_zero_of_disjoint h.disjoint]

/--
theorem `prodEquivOfIsCompl_symm_apply_snd_eq_zero` / 定理 `prodEquivOfIsCompl_symm_apply_snd_eq_zero`

English:
theorem prodEquivOfIsCompl_symm_apply_snd_eq_zero
  given: (h : IsCompl p q) {x : E}
  proof: by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_right _ (Submodule.coe_mem _)]; rw [mem_left_iff_eq_zero_of_disjoint h.disjoint]

@[simp]

中文:
定理 prodEquivOfIsCompl_symm_apply_snd_eq_zero
  条件: (h : IsCompl p q) {x : E}
  证明: by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_right _ (Submodule.coe_mem _)]; rw [mem_left_iff_eq_zero_of_disjoint h.disjoint]

@[simp]

Depends on / 依赖: Submodule, Submodule.add_mem_iff_right, Submodule.coe_mem, add_mem_iff_right, apply_symm_apply, coe_mem, coe_prodEquivOfIsCompl, conv_rhs, disjoint, h.disjoint, mem_left_iff_eq_zero_of_disjoint, prodEquivOfIsCompl
-/
theorem prodEquivOfIsCompl_symm_apply_snd_eq_zero (h : IsCompl p q) {x : E} :
    ((prodEquivOfIsCompl p q h).symm x).2 = 0 ↔ x in p := by
  conv_rhs => rw [← (prodEquivOfIsCompl p q h).apply_symm_apply x]
  rw [coe_prodEquivOfIsCompl']; rw [Submodule.add_mem_iff_right _ (Submodule.coe_mem _)]; rw [mem_left_iff_eq_zero_of_disjoint h.disjoint]

@[simp]
/--
theorem `prodComm_trans_prodEquivOfIsCompl` / 定理 `prodComm_trans_prodEquivOfIsCompl`

English:
theorem prodComm_trans_prodEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: LinearEquiv.ext fun _ => add_comm _ _

中文:
定理 prodComm_trans_prodEquivOfIsCompl
  条件: (h : IsCompl p q)
  证明: LinearEquiv.ext fun _ => add_comm _ _

Depends on / 依赖: LinearEquiv, LinearEquiv.ext, add_comm
-/
theorem prodComm_trans_prodEquivOfIsCompl (h : IsCompl p q) :
    LinearEquiv.prodComm R q p ≪≫ₗ prodEquivOfIsCompl p q h = prodEquivOfIsCompl q p h.symm :=
  LinearEquiv.ext fun _ => add_comm _ _

/--
Definition of `projectionOnto` / `projectionOnto` 的定义

English:
definition projectionOnto
  signature: (h : IsCompl p q)
  body: LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

中文:
定义 projectionOnto
  签名: (h : IsCompl p q)
  定义体: LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

Depends on / 依赖: LinearMap, LinearMap.fst, prodEquivOfIsCompl
-/
def projectionOnto (h : IsCompl p q) : E ->ₗ[R] p :=
  LinearMap.fst R p q ∘ₗ ↑(prodEquivOfIsCompl p q h).symm

/--
Definition of `projection` / `projection` 的定义

English:
definition projection
  signature: (hpq : IsCompl p q)
  body: p.subtype ∘ₗ p.projectionOnto q hpq

中文:
定义 projection
  签名: (hpq : IsCompl p q)
  定义体: p.subtype ∘ₗ p.projectionOnto q hpq

Depends on / 依赖: p.projectionOnto, p.subtype, projectionOnto, subtype
-/
noncomputable def projection (hpq : IsCompl p q) :=
  p.subtype ∘ₗ p.projectionOnto q hpq

variable {p q}

open Submodule

/--
theorem `projection_apply` / 定理 `projection_apply`

English:
theorem projection_apply
  given: (hpq : IsCompl p q) (x : E)
  proof: rfl

@[simp]

中文:
定理 projection_apply
  条件: (hpq : IsCompl p q) (x : E)
  证明: rfl

@[simp]
-/
theorem projection_apply (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x = p.projectionOnto q hpq x :=
  rfl

@[simp]
/--
theorem `coe_projectionOnto_apply` / 定理 `coe_projectionOnto_apply`

English:
theorem coe_projectionOnto_apply
  given: (hpq : IsCompl p q) (x : E)
  proof: rfl

@[simp]

中文:
定理 coe_projectionOnto_apply
  条件: (hpq : IsCompl p q) (x : E)
  证明: rfl

@[simp]
-/
theorem coe_projectionOnto_apply (hpq : IsCompl p q) (x : E) :
    (p.projectionOnto q hpq x : E) = p.projection q hpq x :=
  rfl

@[simp]
/--
theorem `projection_apply_mem` / 定理 `projection_apply_mem`

English:
theorem projection_apply_mem
  given: (hpq : IsCompl p q) (x : E)
  proof: SetLike.coe_mem _

@[simp]

中文:
定理 projection_apply_mem
  条件: (hpq : IsCompl p q) (x : E)
  证明: SetLike.coe_mem _

@[simp]

Depends on / 依赖: SetLike, SetLike.coe_mem, coe_mem
-/
theorem projection_apply_mem (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x in p :=
  SetLike.coe_mem _

@[simp]
/--
theorem `projectionOnto_apply_left` / 定理 `projectionOnto_apply_left`

English:
theorem projectionOnto_apply_left
  given: (h : IsCompl p q) (x : p)
  proof: by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_left]

@[simp]

中文:
定理 projectionOnto_apply_left
  条件: (h : IsCompl p q) (x : p)
  证明: by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_left]

@[simp]

Depends on / 依赖: prodEquivOfIsCompl_symm_apply_left, projectionOnto
-/
theorem projectionOnto_apply_left (h : IsCompl p q) (x : p) :
    projectionOnto p q h x = x := by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_left]

@[simp]
/--
theorem `projection_apply_left` / 定理 `projection_apply_left`

English:
theorem projection_apply_left
  given: (hpq : IsCompl p q) (x : p)
  proof: by simp [projection]

中文:
定理 projection_apply_left
  条件: (hpq : IsCompl p q) (x : p)
  证明: by simp [projection]

Depends on / 依赖: projection
-/
theorem projection_apply_left (hpq : IsCompl p q) (x : p) :
    p.projection q hpq x = x := by simp [projection]

/--
lemma `projectionOnto_apply_of_mem_left` / 引理 `projectionOnto_apply_of_mem_left`

English:
lemma projectionOnto_apply_of_mem_left
  given: (hpq : IsCompl p q) {x : E} (hx : x in p)
  proof: projectionOnto_apply_left hpq ⟨x, hx⟩

中文:
引理 projectionOnto_apply_of_mem_left
  条件: (hpq : IsCompl p q) {x : E} (hx : x in p)
  证明: projectionOnto_apply_left hpq ⟨x, hx⟩

Depends on / 依赖: projectionOnto_apply_left
-/
lemma projectionOnto_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x in p) :
    p.projectionOnto q hpq x = ⟨x, hx⟩ := projectionOnto_apply_left hpq ⟨x, hx⟩

/--
lemma `projection_apply_of_mem_left` / 引理 `projection_apply_of_mem_left`

English:
lemma projection_apply_of_mem_left
  given: (hpq : IsCompl p q) {x : E} (hx : x in p)
  proof: projection_apply_left hpq ⟨x, hx⟩

@[simp]

中文:
引理 projection_apply_of_mem_left
  条件: (hpq : IsCompl p q) {x : E} (hx : x in p)
  证明: projection_apply_left hpq ⟨x, hx⟩

@[simp]

Depends on / 依赖: projection_apply_left
-/
lemma projection_apply_of_mem_left (hpq : IsCompl p q) {x : E} (hx : x in p) :
    p.projection q hpq x = x := projection_apply_left hpq ⟨x, hx⟩

@[simp]
/--
theorem `range_projectionOnto` / 定理 `range_projectionOnto`

English:
theorem range_projectionOnto
  given: (h : IsCompl p q)
  statement: range (projectionOnto p q h) = ⊤
  proof: range_eq_of_proj (projectionOnto_apply_left h)

@[simp]

中文:
定理 range_projectionOnto
  条件: (h : IsCompl p q)
  结论: range (projectionOnto p q h) = ⊤
  证明: range_eq_of_proj (projectionOnto_apply_left h)

@[simp]

Depends on / 依赖: projectionOnto_apply_left, range_eq_of_proj
-/
theorem range_projectionOnto (h : IsCompl p q) : range (projectionOnto p q h) = ⊤ :=
  range_eq_of_proj (projectionOnto_apply_left h)

@[simp]
/--
theorem `range_projection` / 定理 `range_projection`

English:
theorem range_projection
  given: (hpq : IsCompl p q)
  statement: range (p.projection q hpq) = p
  proof: by
  simp [projection, range_comp]

中文:
定理 range_projection
  条件: (hpq : IsCompl p q)
  结论: range (p.projection q hpq) = p
  证明: by
  simp [projection, range_comp]

Depends on / 依赖: projection, range_comp
-/
theorem range_projection (hpq : IsCompl p q) : range (p.projection q hpq) = p := by
  simp [projection, range_comp]

/--
theorem `projectionOnto_surjective` / 定理 `projectionOnto_surjective`

English:
theorem projectionOnto_surjective
  given: (h : IsCompl p q)
  proof: range_eq_top.mp (range_projectionOnto h)

@[simp]

中文:
定理 projectionOnto_surjective
  条件: (h : IsCompl p q)
  证明: range_eq_top.mp (range_projectionOnto h)

@[simp]

Depends on / 依赖: range_eq_top, range_eq_top.mp, range_projectionOnto
-/
theorem projectionOnto_surjective (h : IsCompl p q) :
    Function.Surjective (projectionOnto p q h) :=
  range_eq_top.mp (range_projectionOnto h)

@[simp]
/--
theorem `projectionOnto_apply_eq_zero_iff` / 定理 `projectionOnto_apply_eq_zero_iff`

English:
theorem projectionOnto_apply_eq_zero_iff
  given: (h : IsCompl p q) {x : E}
  proof: by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_fst_eq_zero]

@[simp]

中文:
定理 projectionOnto_apply_eq_zero_iff
  条件: (h : IsCompl p q) {x : E}
  证明: by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_fst_eq_zero]

@[simp]

Depends on / 依赖: prodEquivOfIsCompl_symm_apply_fst_eq_zero, projectionOnto
-/
theorem projectionOnto_apply_eq_zero_iff (h : IsCompl p q) {x : E} :
    projectionOnto p q h x = 0 ↔ x in q := by
  simp [projectionOnto, prodEquivOfIsCompl_symm_apply_fst_eq_zero]

@[simp]
/--
theorem `projection_apply_eq_zero_iff` / 定理 `projection_apply_eq_zero_iff`

English:
theorem projection_apply_eq_zero_iff
  given: (hpq : IsCompl p q) {x : E}
  proof: by
  simp [projection, -coe_projectionOnto_apply]

alias ⟨_, projectionOnto_apply_of_mem_right⟩ :=
  projectionOnto_apply_eq_zero_iff

alias ⟨_, projection_apply_of_mem_right⟩ :=
  projection_apply_eq_zero_iff

@[simp]

中文:
定理 projection_apply_eq_zero_iff
  条件: (hpq : IsCompl p q) {x : E}
  证明: by
  simp [projection, -coe_projectionOnto_apply]

alias ⟨_, projectionOnto_apply_of_mem_right⟩ :=
  projectionOnto_apply_eq_zero_iff

alias ⟨_, projection_apply_of_mem_right⟩ :=
  projection_apply_eq_zero_iff

@[simp]

Depends on / 依赖: coe_projectionOnto_apply, projection
-/
theorem projection_apply_eq_zero_iff (hpq : IsCompl p q) {x : E} :
    p.projection q hpq x = 0 ↔ x in q := by
  simp [projection, -coe_projectionOnto_apply]

alias ⟨_, projectionOnto_apply_of_mem_right⟩ :=
  projectionOnto_apply_eq_zero_iff

alias ⟨_, projection_apply_of_mem_right⟩ :=
  projection_apply_eq_zero_iff

@[simp]
/--
theorem `projectionOnto_apply_right` / 定理 `projectionOnto_apply_right`

English:
theorem projectionOnto_apply_right
  given: (h : IsCompl p q) (x : q)
  proof: projectionOnto_apply_of_mem_right h x.2

@[simp]

中文:
定理 projectionOnto_apply_right
  条件: (h : IsCompl p q) (x : q)
  证明: projectionOnto_apply_of_mem_right h x.2

@[simp]

Depends on / 依赖: projectionOnto_apply_of_mem_right
-/
theorem projectionOnto_apply_right (h : IsCompl p q) (x : q) :
    projectionOnto p q h x = 0 :=
  projectionOnto_apply_of_mem_right h x.2

@[simp]
/--
theorem `projection_apply_right` / 定理 `projection_apply_right`

English:
theorem projection_apply_right
  given: (h : IsCompl p q) (x : q)
  proof: projection_apply_of_mem_right h x.2

@[simp]

中文:
定理 projection_apply_right
  条件: (h : IsCompl p q) (x : q)
  证明: projection_apply_of_mem_right h x.2

@[simp]

Depends on / 依赖: projection_apply_of_mem_right
-/
theorem projection_apply_right (h : IsCompl p q) (x : q) :
    p.projection q h x = 0 :=
  projection_apply_of_mem_right h x.2

@[simp]
/--
theorem `ker_projectionOnto` / 定理 `ker_projectionOnto`

English:
theorem ker_projectionOnto
  given: (h : IsCompl p q)
  statement: ker (projectionOnto p q h) = q
  proof: ext fun _ => mem_ker.trans (projectionOnto_apply_eq_zero_iff h)

@[simp]

中文:
定理 ker_projectionOnto
  条件: (h : IsCompl p q)
  结论: ker (projectionOnto p q h) = q
  证明: ext fun _ => mem_ker.trans (projectionOnto_apply_eq_zero_iff h)

@[simp]

Depends on / 依赖: mem_ker, mem_ker.trans, projectionOnto_apply_eq_zero_iff
-/
theorem ker_projectionOnto (h : IsCompl p q) : ker (projectionOnto p q h) = q :=
  ext fun _ => mem_ker.trans (projectionOnto_apply_eq_zero_iff h)

@[simp]
/--
theorem `ker_projection` / 定理 `ker_projection`

English:
theorem ker_projection
  given: (hpq : IsCompl p q)
  proof: by
  simp [projection, ker_comp]

中文:
定理 ker_projection
  条件: (hpq : IsCompl p q)
  证明: by
  simp [projection, ker_comp]

Depends on / 依赖: ker_comp, projection
-/
theorem ker_projection (hpq : IsCompl p q) :
    ker (p.projection q hpq) = q := by
  simp [projection, ker_comp]

/--
theorem `projectionOnto_comp_subtype` / 定理 `projectionOnto_comp_subtype`

English:
theorem projectionOnto_comp_subtype
  given: (h : IsCompl p q)
  proof: LinearMap.ext projectionOnto_apply_left h

中文:
定理 projectionOnto_comp_subtype
  条件: (h : IsCompl p q)
  证明: LinearMap.ext projectionOnto_apply_left h

Depends on / 依赖: LinearMap, LinearMap.ext, projectionOnto_apply_left
-/
theorem projectionOnto_comp_subtype (h : IsCompl p q) :
    (projectionOnto p q h).comp p.subtype = LinearMap.id :=
LinearMap.ext projectionOnto_apply_left h

/--
theorem `projectionOnto_projection` / 定理 `projectionOnto_projection`

English:
theorem projectionOnto_projection
  given: (h : IsCompl p q) (x : E)
  proof: projectionOnto_apply_left h _

中文:
定理 projectionOnto_projection
  条件: (h : IsCompl p q) (x : E)
  证明: projectionOnto_apply_left h _

Depends on / 依赖: projectionOnto_apply_left
-/
theorem projectionOnto_projection (h : IsCompl p q) (x : E) :
    projectionOnto p q h (p.projection q h x) = projectionOnto p q h x :=
  projectionOnto_apply_left h _

/-- The linear projection onto a subspace along its complement is an idempotent. -/
@[simp]
/--
theorem `isIdempotentElem_projection` / 定理 `isIdempotentElem_projection`

English:
theorem isIdempotentElem_projection
  given: (hpq : IsCompl p q)
  proof: LinearMap.ext fun _ => congr($(projectionOnto_projection hpq _))

中文:
定理 isIdempotentElem_projection
  条件: (hpq : IsCompl p q)
  证明: LinearMap.ext fun _ => congr($(projectionOnto_projection hpq _))

Depends on / 依赖: LinearMap, LinearMap.ext, projectionOnto_projection
-/
theorem isIdempotentElem_projection (hpq : IsCompl p q) :
    IsIdempotentElem (p.projection q hpq) :=
  LinearMap.ext fun _ => congr($(projectionOnto_projection hpq _))

/--
theorem `existsUnique_add_of_isCompl_prod` / 定理 `existsUnique_add_of_isCompl_prod`

English:
theorem existsUnique_add_of_isCompl_prod
  given: (hc : IsCompl p q) (x : E)
  proof: (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _

中文:
定理 existsUnique_add_of_isCompl_prod
  条件: (hc : IsCompl p q) (x : E)
  证明: (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _

Depends on / 依赖: bijective, existsUnique, prodEquivOfIsCompl, toEquiv, toEquiv.bijective.existsUnique
-/
theorem existsUnique_add_of_isCompl_prod (hc : IsCompl p q) (x : E) :
    exists! u : p × q, (u.fst : E) + u.snd = x :=
  (prodEquivOfIsCompl _ _ hc).toEquiv.bijective.existsUnique _

/--
theorem `existsUnique_add_of_isCompl` / 定理 `existsUnique_add_of_isCompl`

English:
theorem existsUnique_add_of_isCompl
  given: (hc : IsCompl p q) (x : E)
  proof: let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

中文:
定理 existsUnique_add_of_isCompl
  条件: (hc : IsCompl p q) (x : E)
  证明: let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

Depends on / 依赖: Prod.eq_iff_fst_eq_snd_eq, eq_iff_fst_eq_snd_eq, existsUnique_add_of_isCompl_prod
-/
theorem existsUnique_add_of_isCompl (hc : IsCompl p q) (x : E) :
    exists (u : p) (v : q), (u : E) + v = x ∧ forall (r : p) (s : q), (r : E) + s = x -> r = u ∧ s = v :=
  let ⟨u, hu₁, hu₂⟩ := existsUnique_add_of_isCompl_prod hc x
  ⟨u.1, u.2, hu₁, fun r s hrs => Prod.eq_iff_fst_eq_snd_eq.1 (hu₂ ⟨r, s⟩ hrs)⟩

/--
theorem `projection_add_projection_eq_self` / 定理 `projection_add_projection_eq_self`

English:
theorem projection_add_projection_eq_self
  given: (hpq : IsCompl p q) (x : E)
  proof: by
  dsimp only [projection, projectionOnto]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x

中文:
定理 projection_add_projection_eq_self
  条件: (hpq : IsCompl p q) (x : E)
  证明: by
  dsimp only [projection, projectionOnto]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x

Depends on / 依赖: apply_symm_apply, prodComm_trans_prodEquivOfIsCompl, prodEquivOfIsCompl, projection, projectionOnto
-/
theorem projection_add_projection_eq_self (hpq : IsCompl p q) (x : E) :
    (p.projection q hpq) x + (q.projection p hpq.symm) x = x := by
  dsimp only [projection, projectionOnto]
  rw [← prodComm_trans_prodEquivOfIsCompl _ _ hpq]
  exact (prodEquivOfIsCompl _ _ hpq).apply_symm_apply x

/--
theorem `projection_add_projection_eq_id` / 定理 `projection_add_projection_eq_id`

English:
theorem projection_add_projection_eq_id
  given: (hpq : IsCompl p q)
  proof: LinearMap.ext (projection_add_projection_eq_self hpq)

中文:
定理 projection_add_projection_eq_id
  条件: (hpq : IsCompl p q)
  证明: LinearMap.ext (projection_add_projection_eq_self hpq)

Depends on / 依赖: LinearMap, LinearMap.ext, projection_add_projection_eq_self
-/
theorem projection_add_projection_eq_id (hpq : IsCompl p q) :
    p.projection q hpq + q.projection p hpq.symm = .id :=
  LinearMap.ext (projection_add_projection_eq_self hpq)

/--
lemma `projection_eq_self_sub_projection` / 引理 `projection_eq_self_sub_projection`

English:
lemma projection_eq_self_sub_projection
  given: (hpq : IsCompl p q) (x : E)
  proof: by
  rw [eq_sub_iff_add_eq]; rw [projection_add_projection_eq_self]

中文:
引理 projection_eq_self_sub_projection
  条件: (hpq : IsCompl p q) (x : E)
  证明: by
  rw [eq_sub_iff_add_eq]; rw [projection_add_projection_eq_self]

Depends on / 依赖: eq_sub_iff_add_eq, projection_add_projection_eq_self
-/
lemma projection_eq_self_sub_projection (hpq : IsCompl p q) (x : E) :
    q.projection p hpq.symm x = x - p.projection q hpq x := by
  rw [eq_sub_iff_add_eq]; rw [projection_add_projection_eq_self]

/--
lemma `projection_eq_id_sub_projection` / 引理 `projection_eq_id_sub_projection`

English:
lemma projection_eq_id_sub_projection
  given: (hpq : IsCompl p q)
  proof: LinearMap.ext (projection_eq_self_sub_projection hpq)

中文:
引理 projection_eq_id_sub_projection
  条件: (hpq : IsCompl p q)
  证明: LinearMap.ext (projection_eq_self_sub_projection hpq)

Depends on / 依赖: LinearMap, LinearMap.ext, projection_eq_self_sub_projection
-/
lemma projection_eq_id_sub_projection (hpq : IsCompl p q) :
    q.projection p hpq.symm = .id - p.projection q hpq :=
  LinearMap.ext (projection_eq_self_sub_projection hpq)

/--
lemma `projection_eq_self_iff` / 引理 `projection_eq_self_iff`

English:
lemma projection_eq_self_iff
  given: (hpq : IsCompl p q) (x : E)
  proof: by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← projection_eq_self_sub_projection]; rw [projection_apply_eq_zero_iff]

@[simp]

中文:
引理 projection_eq_self_iff
  条件: (hpq : IsCompl p q) (x : E)
  证明: by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← projection_eq_self_sub_projection]; rw [projection_apply_eq_zero_iff]

@[simp]
-/
@[simp] lemma projection_eq_self_iff (hpq : IsCompl p q) (x : E) :
    p.projection q hpq x = x ↔ x in p := by
  rw [eq_comm]; rw [← sub_eq_zero]; rw [← projection_eq_self_sub_projection]; rw [projection_apply_eq_zero_iff]

@[simp]
/--
theorem `prodEquivOfIsCompl_symm_apply` / 定理 `prodEquivOfIsCompl_symm_apply`

English:
theorem prodEquivOfIsCompl_symm_apply
  given: (hpq : IsCompl p q) (x : E)
  proof: Prod.ext rfl congr(($(prodComm_trans_prodEquivOfIsCompl p q hpq).symm x).1)

@[simp]

中文:
定理 prodEquivOfIsCompl_symm_apply
  条件: (hpq : IsCompl p q) (x : E)
  证明: Prod.ext rfl congr(($(prodComm_trans_prodEquivOfIsCompl p q hpq).symm x).1)

@[simp]

Depends on / 依赖: Prod.ext, prodComm_trans_prodEquivOfIsCompl
-/
theorem prodEquivOfIsCompl_symm_apply (hpq : IsCompl p q) (x : E) :
    (p.prodEquivOfIsCompl q hpq).symm x =
      (p.projectionOnto q hpq x, q.projectionOnto p hpq.symm x) :=
  Prod.ext rfl congr(($(prodComm_trans_prodEquivOfIsCompl p q hpq).symm x).1)

@[simp]
/--
theorem `toLinearMap_prodEquivOfIsCompl_symm` / 定理 `toLinearMap_prodEquivOfIsCompl_symm`

English:
theorem toLinearMap_prodEquivOfIsCompl_symm
  given: (hpq : IsCompl p q)
  proof: LinearMap.ext by simp

中文:
定理 toLinearMap_prodEquivOfIsCompl_symm
  条件: (hpq : IsCompl p q)
  证明: LinearMap.ext by simp

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem toLinearMap_prodEquivOfIsCompl_symm (hpq : IsCompl p q) :
    (p.prodEquivOfIsCompl q hpq).symm.toLinearMap =
      (p.projectionOnto q hpq).prod (q.projectionOnto p hpq.symm) :=
LinearMap.ext by simp

/--
theorem `sub_projection_mem` / 定理 `sub_projection_mem`

English:
theorem sub_projection_mem
  given: (h : IsCompl p q) (x : E)
  statement: x - p.projection q h x in q
  proof: by
  rw [← projection_eq_self_sub_projection h]
  exact projection_apply_mem h.symm x

中文:
定理 sub_projection_mem
  条件: (h : IsCompl p q) (x : E)
  结论: x - p.projection q h x in q
  证明: by
  rw [← projection_eq_self_sub_projection h]
  exact projection_apply_mem h.symm x

Depends on / 依赖: h.symm, projection_apply_mem, projection_eq_self_sub_projection
-/
theorem sub_projection_mem (h : IsCompl p q) (x : E) : x - p.projection q h x in q := by
  rw [← projection_eq_self_sub_projection h]
  exact projection_apply_mem h.symm x

variable (p q) in
/-- If `q` is a complement of `p`, then `M ⧸ p ≃ q`. The forward direction sends a quotient class
to its projection onto `q` along `p`; the backward direction sends an element of `q` to its class
in `M ⧸ p`. -/
@[simps! symm_apply]
/--
Definition of `quotientEquivOfIsCompl` / `quotientEquivOfIsCompl` 的定义

English:
definition quotientEquivOfIsCompl
  signature: (h : IsCompl p q)
  body: .ofLinearMap
    (p.liftQ (q.projectionOnto p h.symm) (by simp))
    (p.mkQ ∘ₗ q.subtype)
    (by ext; simp)
    (by ext; simp [Quotient.eq, sub_mem_comm_iff, sub_projection_mem])

中文:
定义 quotientEquivOfIsCompl
  签名: (h : IsCompl p q)
  定义体: .ofLinearMap
    (p.liftQ (q.projectionOnto p h.symm) (by simp))
    (p.mkQ ∘ₗ q.subtype)
    (by ext; simp)
    (by ext; simp [Quotient.eq, sub_mem_comm_iff, sub_projection_mem])

Depends on / 依赖: Quotient, Quotient.eq, h.symm, ofLinearMap, p.liftQ, p.mkQ, projectionOnto, q.projectionOnto, q.subtype, sub_mem_comm_iff, sub_projection_mem, subtype
-/
def quotientEquivOfIsCompl (h : IsCompl p q) : (E ⧸ p) ≃ₗ[R] q :=
  .ofLinearMap
    (p.liftQ (q.projectionOnto p h.symm) (by simp))
    (p.mkQ ∘ₗ q.subtype)
    (by ext; simp)
    (by ext; simp [Quotient.eq, sub_mem_comm_iff, sub_projection_mem])

/--
theorem `quotientEquivOfIsCompl_comp_mkQ` / 定理 `quotientEquivOfIsCompl_comp_mkQ`

English:
theorem quotientEquivOfIsCompl_comp_mkQ
  given: (h : IsCompl p q)
  proof: rfl

@[simp]

中文:
定理 quotientEquivOfIsCompl_comp_mkQ
  条件: (h : IsCompl p q)
  证明: rfl

@[simp]
-/
theorem quotientEquivOfIsCompl_comp_mkQ (h : IsCompl p q) :
    (quotientEquivOfIsCompl p q h : E ⧸ p ->ₗ[R] q) ∘ₗ p.mkQ = q.projectionOnto p h.symm :=
  rfl

@[simp]
/--
theorem `quotientEquivOfIsCompl_apply_mk` / 定理 `quotientEquivOfIsCompl_apply_mk`

English:
theorem quotientEquivOfIsCompl_apply_mk
  given: (h : IsCompl p q) (x : E)
  proof: rfl

中文:
定理 quotientEquivOfIsCompl_apply_mk
  条件: (h : IsCompl p q) (x : E)
  证明: rfl
-/
theorem quotientEquivOfIsCompl_apply_mk (h : IsCompl p q) (x : E) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = q.projectionOnto p h.symm x :=
  rfl

/--
theorem `quotientEquivOfIsCompl_apply_mk_right` / 定理 `quotientEquivOfIsCompl_apply_mk_right`

English:
theorem quotientEquivOfIsCompl_apply_mk_right
  given: (h : IsCompl p q) (x : q)
  proof: (quotientEquivOfIsCompl p q h).apply_symm_apply x

@[deprecated (since := "2026-05-06")]
alias quotientEquivOfIsCompl_apply_mk_coe := quotientEquivOfIsCompl_apply_mk_right

@[simp]

中文:
定理 quotientEquivOfIsCompl_apply_mk_right
  条件: (h : IsCompl p q) (x : q)
  证明: (quotientEquivOfIsCompl p q h).apply_symm_apply x

@[deprecated (since := "2026-05-06")]
alias quotientEquivOfIsCompl_apply_mk_coe := quotientEquivOfIsCompl_apply_mk_right

@[simp]

Depends on / 依赖: apply_symm_apply, quotientEquivOfIsCompl
-/
theorem quotientEquivOfIsCompl_apply_mk_right (h : IsCompl p q) (x : q) :
    quotientEquivOfIsCompl p q h (Quotient.mk x) = x :=
  (quotientEquivOfIsCompl p q h).apply_symm_apply x

@[deprecated (since := "2026-05-06")]
alias quotientEquivOfIsCompl_apply_mk_coe := quotientEquivOfIsCompl_apply_mk_right

@[simp]
/--
theorem `mk_quotientEquivOfIsCompl_apply` / 定理 `mk_quotientEquivOfIsCompl_apply`

English:
theorem mk_quotientEquivOfIsCompl_apply
  given: (h : IsCompl p q) (x : E ⧸ p)
  proof: (quotientEquivOfIsCompl p q h).symm_apply_apply x

@[simp]

中文:
定理 mk_quotientEquivOfIsCompl_apply
  条件: (h : IsCompl p q) (x : E ⧸ p)
  证明: (quotientEquivOfIsCompl p q h).symm_apply_apply x

@[simp]

Depends on / 依赖: quotientEquivOfIsCompl, symm_apply_apply
-/
theorem mk_quotientEquivOfIsCompl_apply (h : IsCompl p q) (x : E ⧸ p) :
    (Quotient.mk (quotientEquivOfIsCompl p q h x) : E ⧸ p) = x :=
  (quotientEquivOfIsCompl p q h).symm_apply_apply x

@[simp]
/--
lemma `toLinearMap_quotientEquivOfIsCompl` / 引理 `toLinearMap_quotientEquivOfIsCompl`

English:
lemma toLinearMap_quotientEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: rfl

@[simp]

中文:
引理 toLinearMap_quotientEquivOfIsCompl
  条件: (h : IsCompl p q)
  证明: rfl

@[simp]
-/
lemma toLinearMap_quotientEquivOfIsCompl (h : IsCompl p q) :
    (p.quotientEquivOfIsCompl q h).toLinearMap = p.liftQ (q.projectionOnto p h.symm) (by simp) :=
  rfl

@[simp]
/--
lemma `toLinearMap_symm_quotientEquivOfIsCompl` / 引理 `toLinearMap_symm_quotientEquivOfIsCompl`

English:
lemma toLinearMap_symm_quotientEquivOfIsCompl
  given: (h : IsCompl p q)
  proof: rfl

中文:
引理 toLinearMap_symm_quotientEquivOfIsCompl
  条件: (h : IsCompl p q)
  证明: rfl
-/
lemma toLinearMap_symm_quotientEquivOfIsCompl (h : IsCompl p q) :
    (p.quotientEquivOfIsCompl q h).symm.toLinearMap = p.mkQ ∘ₗ q.subtype :=
  rfl

end Submodule

namespace LinearMap

open Submodule

section

/--
Definition of `linearProjOfIsCompl` / `linearProjOfIsCompl` 的定义

English:
definition linearProjOfIsCompl
  signature: {F : Type*} [AddCommGroup F] [Module R F]
  body: (LinearEquiv.ofInjective i hi).symm ∘ₗ (LinearMap.range i).projectionOnto q h

中文:
定义 linearProjOfIsCompl
  签名: {F : 类型} [AddCommGroup F] [Module R F]
  定义体: (LinearEquiv.ofInjective i hi).symm ∘ₗ (LinearMap.range i).projectionOnto q h

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, LinearMap, LinearMap.range, ofInjective, projectionOnto
-/
def linearProjOfIsCompl {F : Type*} [AddCommGroup F] [Module R F]
    (i : F ->ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q) : E ->ₗ[R] F :=
  (LinearEquiv.ofInjective i hi).symm ∘ₗ (LinearMap.range i).projectionOnto q h

variable {F : Type*} [AddCommGroup F] [Module R F] (i : F ->ₗ[R] E) (hi : Function.Injective i)
    (h : IsCompl (LinearMap.range i) q)

@[simp]
/--
theorem `linearProjOfIsCompl_apply_left` / 定理 `linearProjOfIsCompl_apply_left`

English:
theorem linearProjOfIsCompl_apply_left
  given: (x : F)
  statement: linearProjOfIsCompl q i hi h (i x) = x
  proof: by
  obtain ⟨ix, rfl⟩ := (LinearEquiv.ofInjective i hi).symm.surjective x
  simp [linearProjOfIsCompl]

中文:
定理 linearProjOfIsCompl_apply_left
  条件: (x : F)
  结论: linearProjOfIsCompl q i hi h (i x) = x
  证明: by
  obtain ⟨ix, rfl⟩ := (LinearEquiv.ofInjective i hi).symm.surjective x
  simp [linearProjOfIsCompl]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, linearProjOfIsCompl, ofInjective, surjective, symm.surjective
-/
theorem linearProjOfIsCompl_apply_left (x : F) : linearProjOfIsCompl q i hi h (i x) = x := by
  obtain ⟨ix, rfl⟩ := (LinearEquiv.ofInjective i hi).symm.surjective x
  simp [linearProjOfIsCompl]

/--
lemma `linearProjOfIsCompl_apply_right'` / 引理 `linearProjOfIsCompl_apply_right'`

English:
lemma linearProjOfIsCompl_apply_right'
  given: (x : E) (hx : x in q)
  proof: by
  simpa [LinearMap.linearProjOfIsCompl]

@[simp]

中文:
引理 linearProjOfIsCompl_apply_right'
  条件: (x : E) (hx : x in q)
  证明: by
  simpa [LinearMap.linearProjOfIsCompl]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.linearProjOfIsCompl, linearProjOfIsCompl
-/
lemma linearProjOfIsCompl_apply_right' (x : E) (hx : x in q) :
    linearProjOfIsCompl q i hi h x = 0 := by
  simpa [LinearMap.linearProjOfIsCompl]

@[simp]
/--
lemma `linearProjOfIsCompl_apply_right` / 引理 `linearProjOfIsCompl_apply_right`

English:
lemma linearProjOfIsCompl_apply_right
  given: (x : q)
  statement: linearProjOfIsCompl q i hi h x = 0
  proof: by
  simp [LinearMap.linearProjOfIsCompl]

@[simp]

中文:
引理 linearProjOfIsCompl_apply_right
  条件: (x : q)
  结论: linearProjOfIsCompl q i hi h x = 0
  证明: by
  simp [LinearMap.linearProjOfIsCompl]

@[simp]

Depends on / 依赖: LinearMap, LinearMap.linearProjOfIsCompl, linearProjOfIsCompl
-/
lemma linearProjOfIsCompl_apply_right (x : q) : linearProjOfIsCompl q i hi h x = 0 := by
  simp [LinearMap.linearProjOfIsCompl]

@[simp]
/--
lemma `ker_linearProjOfIsCompl` / 引理 `ker_linearProjOfIsCompl`

English:
lemma ker_linearProjOfIsCompl
  statement: ker (linearProjOfIsCompl q i hi h) = q
  proof: by
  simp [LinearMap.linearProjOfIsCompl]

中文:
引理 ker_linearProjOfIsCompl
  结论: ker (linearProjOfIsCompl q i hi h) = q
  证明: by
  simp [LinearMap.linearProjOfIsCompl]

Depends on / 依赖: LinearMap, LinearMap.linearProjOfIsCompl, linearProjOfIsCompl
-/
lemma ker_linearProjOfIsCompl : ker (linearProjOfIsCompl q i hi h) = q := by
  simp [LinearMap.linearProjOfIsCompl]

end

/--
Definition of `ofIsCompl` / `ofIsCompl` 的定义

English:
definition ofIsCompl
  signature: {p q : Submodule R E} (h : IsCompl p q) (φ : p ->ₗ[R] F) (ψ : q ->ₗ[R] F)
  body: LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm

中文:
定义 ofIsCompl
  签名: {p q : Submodule R E} (h : IsCompl p q) (φ : p ->ₗ[R] F) (ψ : q ->ₗ[R] F)
  定义体: LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm

Depends on / 依赖: LinearMap, LinearMap.coprod, Submodule, Submodule.prodEquivOfIsCompl, coprod, prodEquivOfIsCompl
-/
def ofIsCompl {p q : Submodule R E} (h : IsCompl p q) (φ : p ->ₗ[R] F) (ψ : q ->ₗ[R] F) : E ->ₗ[R] F :=
  LinearMap.coprod φ ψ ∘ₗ ↑(Submodule.prodEquivOfIsCompl _ _ h).symm

variable {p q}

@[simp]
/--
theorem `ofIsCompl_apply_left` / 定理 `ofIsCompl_apply_left`

English:
theorem ofIsCompl_apply_left
  given: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p)
  proof: by simp [ofIsCompl]

@[simp]

中文:
定理 ofIsCompl_apply_left
  条件: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p)
  证明: by simp [ofIsCompl]

@[simp]

Depends on / 依赖: ofIsCompl
-/
theorem ofIsCompl_apply_left (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (u : p) :
    ofIsCompl h φ ψ (u : E) = φ u := by simp [ofIsCompl]

@[simp]
/--
theorem `ofIsCompl_apply_right` / 定理 `ofIsCompl_apply_right`

English:
theorem ofIsCompl_apply_right
  given: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q)
  proof: by simp [ofIsCompl]

中文:
定理 ofIsCompl_apply_right
  条件: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q)
  证明: by simp [ofIsCompl]

Depends on / 依赖: ofIsCompl
-/
theorem ofIsCompl_apply_right (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (v : q) :
    ofIsCompl h φ ψ (v : E) = ψ v := by simp [ofIsCompl]

/--
theorem `ofIsCompl_eq` / 定理 `ofIsCompl_eq`

English:
theorem ofIsCompl_eq
  statement: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
  proof: by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  simp [ofIsCompl, hφ, hψ]

中文:
定理 ofIsCompl_eq
  结论: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
  证明: by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  simp [ofIsCompl, hφ, hψ]

Depends on / 依赖: existsUnique_add_of_isCompl, ofIsCompl
-/
theorem ofIsCompl_eq (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
    (hφ : forall u, φ u = χ u) (hψ : forall u, ψ u = χ u) : ofIsCompl h φ ψ = χ := by
  ext x
  obtain ⟨_, _, rfl, _⟩ := existsUnique_add_of_isCompl h x
  simp [ofIsCompl, hφ, hψ]

/--
theorem `ofIsCompl_eq'` / 定理 `ofIsCompl_eq'`

English:
theorem ofIsCompl_eq'
  statement: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
  proof: ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl

中文:
定理 ofIsCompl_eq'
  结论: (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
  证明: ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl

Depends on / 依赖: ofIsCompl_eq
-/
theorem ofIsCompl_eq' (h : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} {χ : E ->ₗ[R] F}
    (hφ : φ = χ.comp p.subtype) (hψ : ψ = χ.comp q.subtype) : ofIsCompl h φ ψ = χ :=
  ofIsCompl_eq h (fun _ => hφ.symm ▸ rfl) fun _ => hψ.symm ▸ rfl

/--
theorem `ofIsCompl_eq_add` / 定理 `ofIsCompl_eq_add`

English:
theorem ofIsCompl_eq_add
  given: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  proof: by
  ext x
  obtain ⟨a, b, rfl, _⟩ := existsUnique_add_of_isCompl hpq x
  simp

@[simp]

中文:
定理 ofIsCompl_eq_add
  条件: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  证明: by
  ext x
  obtain ⟨a, b, rfl, _⟩ := existsUnique_add_of_isCompl hpq x
  simp

@[simp]

Depends on / 依赖: existsUnique_add_of_isCompl
-/
theorem ofIsCompl_eq_add (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} :
    ofIsCompl hpq φ ψ = (φ ∘ₗ p.projectionOnto q hpq) + (ψ ∘ₗ q.projectionOnto p hpq.symm) := by
  ext x
  obtain ⟨a, b, rfl, _⟩ := existsUnique_add_of_isCompl hpq x
  simp

@[simp]
/--
theorem `ofIsCompl_zero` / 定理 `ofIsCompl_zero`

English:
theorem ofIsCompl_zero
  given: (h : IsCompl p q)
  statement: (ofIsCompl h 0 0 : E ->ₗ[R] F) = 0
  proof: ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]

中文:
定理 ofIsCompl_zero
  条件: (h : IsCompl p q)
  结论: (ofIsCompl h 0 0 : E ->ₗ[R] F) = 0
  证明: ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]

Depends on / 依赖: ofIsCompl_eq
-/
theorem ofIsCompl_zero (h : IsCompl p q) : (ofIsCompl h 0 0 : E ->ₗ[R] F) = 0 :=
  ofIsCompl_eq _ (fun _ => rfl) fun _ => rfl

@[simp]
/--
theorem `ofIsCompl_add` / 定理 `ofIsCompl_add`

English:
theorem ofIsCompl_add
  given: (h : IsCompl p q) {φ₁ φ₂ : p ->ₗ[R] F} {ψ₁ ψ₂ : q ->ₗ[R] F}
  proof: ofIsCompl_eq _ (by simp) (by simp)

@[simp]

中文:
定理 ofIsCompl_add
  条件: (h : IsCompl p q) {φ₁ φ₂ : p ->ₗ[R] F} {ψ₁ ψ₂ : q ->ₗ[R] F}
  证明: ofIsCompl_eq _ (by simp) (by simp)

@[simp]

Depends on / 依赖: ofIsCompl_eq
-/
theorem ofIsCompl_add (h : IsCompl p q) {φ₁ φ₂ : p ->ₗ[R] F} {ψ₁ ψ₂ : q ->ₗ[R] F} :
    ofIsCompl h (φ₁ + φ₂) (ψ₁ + ψ₂) = ofIsCompl h φ₁ ψ₁ + ofIsCompl h φ₂ ψ₂ :=
  ofIsCompl_eq _ (by simp) (by simp)

@[simp]
/--
theorem `ofIsCompl_smul` / 定理 `ofIsCompl_smul`

English:
theorem ofIsCompl_smul
  statement: {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
  proof: ofIsCompl_eq _ (by simp) (by simp)

中文:
定理 ofIsCompl_smul
  结论: {R : 类型} [CommRing R] {E : 类型} [AddCommGroup E] [Module R E]
  证明: ofIsCompl_eq _ (by simp) (by simp)

Depends on / 依赖: ofIsCompl_eq
-/
theorem ofIsCompl_smul {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E]
    {F : Type*} [AddCommGroup F] [Module R F] {p q : Submodule R E} (h : IsCompl p q)
    {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} (c : R) : ofIsCompl h (c • φ) (c • ψ) = c • ofIsCompl h φ ψ :=
  ofIsCompl_eq _ (by simp) (by simp)

/--
theorem `surjective_comp_projectionOnto` / 定理 `surjective_comp_projectionOnto`

English:
theorem surjective_comp_projectionOnto
  given: (h : IsCompl p q) [Module R M]
  proof: fun f => ⟨p.subtype ∘ₗ f, by ext; simp⟩

中文:
定理 surjective_comp_projectionOnto
  条件: (h : IsCompl p q) [Module R M]
  证明: fun f => ⟨p.subtype ∘ₗ f, by ext; simp⟩

Depends on / 依赖: p.subtype, subtype
-/
theorem surjective_comp_projectionOnto (h : IsCompl p q) [Module R M] :
    Function.Surjective (comp (p.projectionOnto q h) : (M ->ₗ[R] E) -> _) :=
  fun f => ⟨p.subtype ∘ₗ f, by ext; simp⟩

/--
theorem `surjective_comp_subtype_of_isComplemented` / 定理 `surjective_comp_subtype_of_isComplemented`

English:
theorem surjective_comp_subtype_of_isComplemented
  given: (h : IsComplemented p) [Module R M]
  proof: have ⟨q, h⟩ := h; fun f => ⟨f ∘ₗ p.projectionOnto q h, by ext; simp⟩

@[simp]

中文:
定理 surjective_comp_subtype_of_isComplemented
  条件: (h : IsComplemented p) [Module R M]
  证明: have ⟨q, h⟩ := h; fun f => ⟨f ∘ₗ p.projectionOnto q h, by ext; simp⟩

@[simp]

Depends on / 依赖: p.projectionOnto, projectionOnto
-/
theorem surjective_comp_subtype_of_isComplemented (h : IsComplemented p) [Module R M] :
    Function.Surjective fun f : E ->ₗ[R] M => f ∘ₗ p.subtype :=
  have ⟨q, h⟩ := h; fun f => ⟨f ∘ₗ p.projectionOnto q h, by ext; simp⟩

@[simp]
/--
theorem `range_ofIsCompl` / 定理 `range_ofIsCompl`

English:
theorem range_ofIsCompl
  given: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  proof: by
  rw [ofIsCompl_eq_add]
  apply le_antisymm
.trans · apply range_add_le _ _
    gcongr
    all_goals exact range_comp_le_range ..
  · apply sup_le
    all_goals rintro - ⟨x, rfl⟩; exact ⟨x, by simp⟩

中文:
定理 range_ofIsCompl
  条件: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  证明: by
  rw [ofIsCompl_eq_add]
  apply le_antisymm
.trans · apply range_add_le _ _
    gcongr
    all_goals exact range_comp_le_range ..
  · apply sup_le
    all_goals rintro - ⟨x, rfl⟩; exact ⟨x, by simp⟩

Depends on / 依赖: all_goals, le_antisymm, ofIsCompl_eq_add, range_add_le, range_comp_le_range, sup_le
-/
theorem range_ofIsCompl (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} :
    range (ofIsCompl hpq φ ψ) = range φ ⊔ range ψ := by
  rw [ofIsCompl_eq_add]
  apply le_antisymm
.trans · apply range_add_le _ _
    gcongr
    all_goals exact range_comp_le_range ..
  · apply sup_le
    all_goals rintro - ⟨x, rfl⟩; exact ⟨x, by simp⟩

/--
theorem `ofIsCompl_subtype_zero_eq` / 定理 `ofIsCompl_subtype_zero_eq`

English:
theorem ofIsCompl_subtype_zero_eq
  given: (hpq : IsCompl p q)
  proof: by
  simp [ofIsCompl_eq_add, projection]

中文:
定理 ofIsCompl_subtype_zero_eq
  条件: (hpq : IsCompl p q)
  证明: by
  simp [ofIsCompl_eq_add, projection]

Depends on / 依赖: ofIsCompl_eq_add, projection
-/
theorem ofIsCompl_subtype_zero_eq (hpq : IsCompl p q) :
    ofIsCompl hpq p.subtype 0 = p.projection q hpq := by
  simp [ofIsCompl_eq_add, projection]

/--
theorem `ofIsCompl_symm` / 定理 `ofIsCompl_symm`

English:
theorem ofIsCompl_symm
  given: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  proof: by
  simp [ofIsCompl_eq_add, add_comm]

中文:
定理 ofIsCompl_symm
  条件: (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F}
  证明: by
  simp [ofIsCompl_eq_add, add_comm]

Depends on / 依赖: add_comm, ofIsCompl_eq_add
-/
theorem ofIsCompl_symm (hpq : IsCompl p q) {φ : p ->ₗ[R] F} {ψ : q ->ₗ[R] F} :
    ofIsCompl hpq.symm ψ φ = ofIsCompl hpq φ ψ := by
  simp [ofIsCompl_eq_add, add_comm]

section

variable {R₁ : Type*} [CommRing R₁] [Module R₁ E] [Module R₁ F]

/--
Definition of `ofIsComplProd` / `ofIsComplProd` 的定义

English:
definition ofIsComplProd
  signature: {p q : Submodule R₁ E} (h : IsCompl p q)
  body: ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]

@[simp]

中文:
定义 ofIsComplProd
  签名: {p q : Submodule R₁ E} (h : IsCompl p q)
  定义体: ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]

@[simp]

Depends on / 依赖: ofIsCompl
-/
def ofIsComplProd {p q : Submodule R₁ E} (h : IsCompl p q) :
    (p ->ₗ[R₁] F) × (q ->ₗ[R₁] F) ->ₗ[R₁] E ->ₗ[R₁] F where
  toFun φ := ofIsCompl h φ.1 φ.2
  map_add' := by intro φ ψ; rw [Prod.snd_add, Prod.fst_add, ofIsCompl_add]
  map_smul' := by intro c φ; simp [Prod.smul_snd, Prod.smul_fst, ofIsCompl_smul]

@[simp]
/--
theorem `ofIsComplProd_apply` / 定理 `ofIsComplProd_apply`

English:
theorem ofIsComplProd_apply
  statement: {p q : Submodule R₁ E} (h : IsCompl p q)
  proof: rfl

中文:
定理 ofIsComplProd_apply
  结论: {p q : Submodule R₁ E} (h : IsCompl p q)
  证明: rfl
-/
theorem ofIsComplProd_apply {p q : Submodule R₁ E} (h : IsCompl p q)
    (φ : (p ->ₗ[R₁] F) × (q ->ₗ[R₁] F)) : ofIsComplProd h φ = ofIsCompl h φ.1 φ.2 :=
  rfl

/--
Definition of `ofIsComplProdEquiv` / `ofIsComplProdEquiv` 的定义

English:
definition ofIsComplProdEquiv
  signature: {p q : Submodule R₁ E} (h : IsCompl p q)
  body: { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ => by
      ext x
      · exact ofIsCompl_apply_left h x
      · exact ofIsCompl_apply_right h x
    right_inv := fun φ => by
      ext x
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl 

中文:
定义 ofIsComplProdEquiv
  签名: {p q : Submodule R₁ E} (h : IsCompl p q)
  定义体: { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ => by
      ext x
      · exact ofIsCompl_apply_left h x
      · exact ofIsCompl_apply_right h x
    right_inv := fun φ => by
      ext x
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl 

Depends on / 依赖: domRestrict, existsUnique_add_of_isCompl, invFun, left_inv, ofIsComplProd, ofIsCompl_apply_left, ofIsCompl_apply_right, right_inv
-/
def ofIsComplProdEquiv {p q : Submodule R₁ E} (h : IsCompl p q) :
    ((p ->ₗ[R₁] F) × (q ->ₗ[R₁] F)) ≃ₗ[R₁] E ->ₗ[R₁] F :=
  { ofIsComplProd h with
    invFun := fun φ => ⟨φ.domRestrict p, φ.domRestrict q⟩
    left_inv := fun φ => by
      ext x
      · exact ofIsCompl_apply_left h x
      · exact ofIsCompl_apply_right h x
    right_inv := fun φ => by
      ext x
      obtain ⟨a, b, hab, _⟩ := existsUnique_add_of_isCompl h x
      rw [← hab]; simp }

end

@[simp]
/--
theorem `projectionOnto_of_proj` / 定理 `projectionOnto_of_proj`

English:
theorem projectionOnto_of_proj
  given: (f : E ->ₗ[R] p) (hf : forall x : p, f x = x)
  proof: by
  ext x
  have : x in p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  simp [hf]

中文:
定理 projectionOnto_of_proj
  条件: (f : E ->ₗ[R] p) (hf : 对任意 x : p, f x = x)
  证明: by
  ext x
  have : x in p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  simp [hf]

Depends on / 依赖: isCompl_of_proj, mem_sup, mem_top, sup_eq_top
-/
theorem projectionOnto_of_proj (f : E ->ₗ[R] p) (hf : forall x : p, f x = x) :
    p.projectionOnto (ker f) (isCompl_of_proj hf) = f := by
  ext x
  have : x in p ⊔ (ker f) := by simp only [(isCompl_of_proj hf).sup_eq_top, mem_top]
  rcases mem_sup'.1 this with ⟨x, y, rfl⟩
  simp [hf]

/--
Definition of `equivProdOfSurjectiveOfIsCompl` / `equivProdOfSurjectiveOfIsCompl` 的定义

English:
definition equivProdOfSurjectiveOfIsCompl
  signature: (f : E ->ₗ[R] F) (g : E ->ₗ[R] G) (hf : range f = ⊤)
  body: LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
      rw [← range_eq_top]
      simp [range_prod_eq hfg.sup_eq_top, *]⟩

@[simp]

中文:
定义 equivProdOfSurjectiveOfIsCompl
  签名: (f : E ->ₗ[R] F) (g : E ->ₗ[R] G) (hf : range f = ⊤)
  定义体: LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
      rw [← range_eq_top]
      simp [range_prod_eq hfg.sup_eq_top, *]⟩

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, f.prod, hfg.inf_eq_bot, hfg.sup_eq_top, inf_eq_bot, ker_eq_bot, ofBijective, range_eq_top, range_prod_eq, sup_eq_top
-/
def equivProdOfSurjectiveOfIsCompl (f : E ->ₗ[R] F) (g : E ->ₗ[R] G) (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) : E ≃ₗ[R] F × G :=
  LinearEquiv.ofBijective (f.prod g)
    ⟨by simp [← ker_eq_bot, hfg.inf_eq_bot], by
      rw [← range_eq_top]
      simp [range_prod_eq hfg.sup_eq_top, *]⟩

@[simp]
/--
theorem `coe_equivProdOfSurjectiveOfIsCompl` / 定理 `coe_equivProdOfSurjectiveOfIsCompl`

English:
theorem coe_equivProdOfSurjectiveOfIsCompl
  statement: {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
  proof: rfl

@[simp]

中文:
定理 coe_equivProdOfSurjectiveOfIsCompl
  结论: {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
  证明: rfl

@[simp]
-/
theorem coe_equivProdOfSurjectiveOfIsCompl {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) :
    (equivProdOfSurjectiveOfIsCompl f g hf hg hfg : E ->ₗ[R] F × G) = f.prod g := rfl

@[simp]
/--
theorem `equivProdOfSurjectiveOfIsCompl_apply` / 定理 `equivProdOfSurjectiveOfIsCompl_apply`

English:
theorem equivProdOfSurjectiveOfIsCompl_apply
  statement: {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
  proof: rfl

中文:
定理 equivProdOfSurjectiveOfIsCompl_apply
  结论: {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
  证明: rfl
-/
theorem equivProdOfSurjectiveOfIsCompl_apply {f : E ->ₗ[R] F} {g : E ->ₗ[R] G} (hf : range f = ⊤)
    (hg : range g = ⊤) (hfg : IsCompl (ker f) (ker g)) (x : E) :
    equivProdOfSurjectiveOfIsCompl f g hf hg hfg x = (f x, g x) := rfl

end LinearMap

namespace Submodule

open LinearMap

/--
Definition of `isComplEquivProj` / `isComplEquivProj` 的定义

English:
definition isComplEquivProj
  signature: : { q // IsCompl p q } ≃ { f : E ->ₗ[R] p // forall x : p, f x = x } where
  body: ⟨projectionOnto p q q.2, projectionOnto_apply_left q.2⟩
  invFun f := ⟨ker (f : E ->ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [ker_projectionOnto]
right_inv := fun ⟨f, hf⟩ => Subtype.ext f.projectionOnto_of_proj hf

@[simp]

中文:
定义 isComplEquivProj
  签名: : { q // IsCompl p q } ≃ { f : E ->ₗ[R] p // 对任意 x : p, f x = x } where
  定义体: ⟨projectionOnto p q q.2, projectionOnto_apply_left q.2⟩
  invFun f := ⟨ker (f : E ->ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [ker_projectionOnto]
right_inv := fun ⟨f, hf⟩ => Subtype.ext f.projectionOnto_of_proj hf

@[simp]

Depends on / 依赖: projectionOnto, projectionOnto_apply_left
-/
def isComplEquivProj : { q // IsCompl p q } ≃ { f : E ->ₗ[R] p // forall x : p, f x = x } where
  toFun q := ⟨projectionOnto p q q.2, projectionOnto_apply_left q.2⟩
  invFun f := ⟨ker (f : E ->ₗ[R] p), isCompl_of_proj f.2⟩
  left_inv := fun ⟨q, hq⟩ => by simp only [ker_projectionOnto]
right_inv := fun ⟨f, hf⟩ => Subtype.ext f.projectionOnto_of_proj hf

@[simp]
/--
theorem `coe_isComplEquivProj_apply` / 定理 `coe_isComplEquivProj_apply`

English:
theorem coe_isComplEquivProj_apply
  given: (q : { q // IsCompl p q })
  proof: rfl

@[simp]

中文:
定理 coe_isComplEquivProj_apply
  条件: (q : { q // IsCompl p q })
  证明: rfl

@[simp]
-/
theorem coe_isComplEquivProj_apply (q : { q // IsCompl p q }) :
    (p.isComplEquivProj q : E ->ₗ[R] p) = projectionOnto p q q.2 := rfl

@[simp]
/--
theorem `coe_isComplEquivProj_symm_apply` / 定理 `coe_isComplEquivProj_symm_apply`

English:
theorem coe_isComplEquivProj_symm_apply
  given: (f : { f : E ->ₗ[R] p // forall x : p, f x = x })
  proof: rfl

中文:
定理 coe_isComplEquivProj_symm_apply
  条件: (f : { f : E ->ₗ[R] p // 对任意 x : p, f x = x })
  证明: rfl
-/
theorem coe_isComplEquivProj_symm_apply (f : { f : E ->ₗ[R] p // forall x : p, f x = x }) :
    (p.isComplEquivProj.symm f : Submodule R E) = ker (f : E ->ₗ[R] p) := rfl

/--
Definition of `isIdempotentElemEquiv` / `isIdempotentElemEquiv` 的定义

English:
definition isIdempotentElemEquiv
  signature: :
  body: ⟨f.1.codRestrict _ fun x => by simp_rw [← f.2.2]; exact mem_range_self f.1 x,
fun ⟨x, hx⟩ => Subtype.ext by
      obtain ⟨x, rfl⟩ := f.2.2.symm ▸ hx
      exact DFunLike.congr_fun f.2.1 x⟩
  invFun f := ⟨p.subtype ∘ₗ f.1, LinearMap.ext fun x => by simp [f.2], le_antisymm
    ((range_comp_le_range _ 

中文:
定义 isIdempotentElemEquiv
  签名: :
  定义体: ⟨f.1.codRestrict _ fun x => by simp_rw [← f.2.2]; exact mem_range_self f.1 x,
fun ⟨x, hx⟩ => Subtype.ext by
      obtain ⟨x, rfl⟩ := f.2.2.symm ▸ hx
      exact DFunLike.congr_fun f.2.1 x⟩
  invFun f := ⟨p.subtype ∘ₗ f.1, LinearMap.ext fun x => by simp [f.2], le_antisymm
    ((range_comp_le_range _ 
-/
@[simps] def isIdempotentElemEquiv :
    { f : Module.End R E // IsIdempotentElem f ∧ range f = p } ≃
    { f : E ->ₗ[R] p // forall x : p, f x = x } where
  toFun f := ⟨f.1.codRestrict _ fun x => by simp_rw [← f.2.2]; exact mem_range_self f.1 x,
fun ⟨x, hx⟩ => Subtype.ext by
      obtain ⟨x, rfl⟩ := f.2.2.symm ▸ hx
      exact DFunLike.congr_fun f.2.1 x⟩
  invFun f := ⟨p.subtype ∘ₗ f.1, LinearMap.ext fun x => by simp [f.2], le_antisymm
    ((range_comp_le_range _ _).trans_eq p.range_subtype)
fun x hx => ⟨x, Subtype.ext_iff.1 f.2 ⟨x, hx⟩⟩⟩

end Submodule

namespace LinearMap

open Submodule

/--
Definition of `IsProj` / `IsProj` 的定义

English:
structure IsProj
  parameters: {F : Type*} [FunLike F M M] (f : F)
  axioms and operations (2):
    - map_mem : forall x, f x in m
    - map_id : forall x in m, f x = x

中文:
结构 IsProj
  参数: {F : 类型} [FunLike F M M] (f : F)
  公理与运算 (2 个):
    - map_mem : 对任意 x, f x in m
    - map_id : 对任意 x in m, f x = x
-/
structure IsProj {F : Type*} [FunLike F M M] (f : F) : Prop where
  map_mem : forall x, f x in m
  map_id : forall x in m, f x = x

/--
theorem `isProj_range_iff_isIdempotentElem` / 定理 `isProj_range_iff_isIdempotentElem`

English:
theorem isProj_range_iff_isIdempotentElem
  given: (f : M ->ₗ[S] M)
  proof: by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hf =>
    ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by rw [← hy, ← Module.End.mul_apply, hf.eq]⟩⟩
  ext x
  exact h2 (f x) (h1 x)

alias ⟨_, IsIdempotentElem.isProj_range⟩ := isProj_range_iff_isIdempotentElem

中文:
定理 isProj_range_iff_isIdempotentElem
  条件: (f : M ->ₗ[S] M)
  证明: by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hf =>
    ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by rw [← hy, ← Module.End.mul_apply, hf.eq]⟩⟩
  ext x
  exact h2 (f x) (h1 x)

alias ⟨_, IsIdempotentElem.isProj_range⟩ := isProj_range_iff_isIdempotentElem

Depends on / 依赖: Module, Module.End.mul_apply, hf.eq, mem_range_self, mul_apply
-/
theorem isProj_range_iff_isIdempotentElem (f : M ->ₗ[S] M) :
    IsProj (range f) f ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨h1, h2⟩ => ?_, fun hf =>
    ⟨fun x => mem_range_self f x, fun x ⟨y, hy⟩ => by rw [← hy, ← Module.End.mul_apply, hf.eq]⟩⟩
  ext x
  exact h2 (f x) (h1 x)

alias ⟨_, IsIdempotentElem.isProj_range⟩ := isProj_range_iff_isIdempotentElem

/--
theorem `isProj_iff_isIdempotentElem` / 定理 `isProj_iff_isIdempotentElem`

English:
theorem isProj_iff_isIdempotentElem
  given: (f : M ->ₗ[S] M)
  proof: by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun h => ⟨_, IsIdempotentElem.isProj_range _ h⟩⟩
  ext x
  exact hp.map_id (f x) (hp.map_mem x)

中文:
定理 isProj_iff_isIdempotentElem
  条件: (f : M ->ₗ[S] M)
  证明: by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun h => ⟨_, IsIdempotentElem.isProj_range _ h⟩⟩
  ext x
  exact hp.map_id (f x) (hp.map_mem x)

Depends on / 依赖: IsIdempotentElem, IsIdempotentElem.isProj_range, hp.map_id, hp.map_mem, isProj_range, map_id, map_mem
-/
theorem isProj_iff_isIdempotentElem (f : M ->ₗ[S] M) :
    (exists p : Submodule S M, IsProj p f) ↔ IsIdempotentElem f := by
  refine ⟨fun ⟨p, hp⟩ => ?_, fun h => ⟨_, IsIdempotentElem.isProj_range _ h⟩⟩
  ext x
  exact hp.map_id (f x) (hp.map_mem x)

namespace IsProj

variable {p m}

/--
theorem `isIdempotentElem` / 定理 `isIdempotentElem`

English:
theorem isIdempotentElem
  given: {f : M ->ₗ[S] M} (h : IsProj m f)
  statement: IsIdempotentElem f
  proof: f.isProj_iff_isIdempotentElem.mp ⟨m, h⟩

中文:
定理 isIdempotentElem
  条件: {f : M ->ₗ[S] M} (h : IsProj m f)
  结论: IsIdempotentElem f
  证明: f.isProj_iff_isIdempotentElem.mp ⟨m, h⟩

Depends on / 依赖: f.isProj_iff_isIdempotentElem.mp, isProj_iff_isIdempotentElem
-/
theorem isIdempotentElem {f : M ->ₗ[S] M} (h : IsProj m f) : IsIdempotentElem f :=
  f.isProj_iff_isIdempotentElem.mp ⟨m, h⟩

/--
theorem `mem_iff_map_id` / 定理 `mem_iff_map_id`

English:
theorem mem_iff_map_id
  given: {f : M ->ₗ[S] M} (hf : IsProj m f) {x : M}
  proof: ⟨hf.map_id x, fun h => h ▸ hf.map_mem x⟩

中文:
定理 mem_iff_map_id
  条件: {f : M ->ₗ[S] M} (hf : IsProj m f) {x : M}
  证明: ⟨hf.map_id x, fun h => h ▸ hf.map_mem x⟩

Depends on / 依赖: hf.map_id, hf.map_mem, map_id, map_mem
-/
theorem mem_iff_map_id {f : M ->ₗ[S] M} (hf : IsProj m f) {x : M} :
    x in m ↔ f x = x :=
  ⟨hf.map_id x, fun h => h ▸ hf.map_mem x⟩

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: {f : M ->ₗ[S] M} (h : IsProj m f)
  body: f.codRestrict m h.map_mem

@[simp]

中文:
定义 codRestrict
  签名: {f : M ->ₗ[S] M} (h : IsProj m f)
  定义体: f.codRestrict m h.map_mem

@[simp]

Depends on / 依赖: codRestrict, f.codRestrict, h.map_mem, map_mem
-/
def codRestrict {f : M ->ₗ[S] M} (h : IsProj m f) : M ->ₗ[S] m :=
  f.codRestrict m h.map_mem

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: {f : M ->ₗ[S] M} (h : IsProj m f) (x : M)
  statement: ↑(h.codRestrict x) = f x
  proof: f.codRestrict_apply m x

@[simp]

中文:
定理 codRestrict_apply
  条件: {f : M ->ₗ[S] M} (h : IsProj m f) (x : M)
  结论: ↑(h.codRestrict x) = f x
  证明: f.codRestrict_apply m x

@[simp]

Depends on / 依赖: codRestrict_apply, f.codRestrict_apply
-/
theorem codRestrict_apply {f : M ->ₗ[S] M} (h : IsProj m f) (x : M) : ↑(h.codRestrict x) = f x :=
  f.codRestrict_apply m x

@[simp]
/--
theorem `codRestrict_apply_cod` / 定理 `codRestrict_apply_cod`

English:
theorem codRestrict_apply_cod
  given: {f : M ->ₗ[S] M} (h : IsProj m f) (x : m)
  statement: h.codRestrict x = x
  proof: by
  ext
  rw [codRestrict_apply]
  exact h.map_id x x.2

中文:
定理 codRestrict_apply_cod
  条件: {f : M ->ₗ[S] M} (h : IsProj m f) (x : m)
  结论: h.codRestrict x = x
  证明: by
  ext
  rw [codRestrict_apply]
  exact h.map_id x x.2

Depends on / 依赖: codRestrict_apply, h.map_id, map_id
-/
theorem codRestrict_apply_cod {f : M ->ₗ[S] M} (h : IsProj m f) (x : m) : h.codRestrict x = x := by
  ext
  rw [codRestrict_apply]
  exact h.map_id x x.2

/--
theorem `codRestrict_ker` / 定理 `codRestrict_ker`

English:
theorem codRestrict_ker
  given: {f : M ->ₗ[S] M} (h : IsProj m f)
  statement: ker h.codRestrict = ker f
  proof: f.ker_codRestrict m _

中文:
定理 codRestrict_ker
  条件: {f : M ->ₗ[S] M} (h : IsProj m f)
  结论: ker h.codRestrict = ker f
  证明: f.ker_codRestrict m _

Depends on / 依赖: f.ker_codRestrict, ker_codRestrict
-/
theorem codRestrict_ker {f : M ->ₗ[S] M} (h : IsProj m f) : ker h.codRestrict = ker f :=
  f.ker_codRestrict m _

/--
theorem `isCompl` / 定理 `isCompl`

English:
theorem isCompl
  given: {f : E ->ₗ[R] E} (h : IsProj p f)
  statement: IsCompl p (ker f)
  proof: by
  rw [← codRestrict_ker h]
  exact isCompl_of_proj h.codRestrict_apply_cod

中文:
定理 isCompl
  条件: {f : E ->ₗ[R] E} (h : IsProj p f)
  结论: IsCompl p (ker f)
  证明: by
  rw [← codRestrict_ker h]
  exact isCompl_of_proj h.codRestrict_apply_cod

Depends on / 依赖: codRestrict_apply_cod, codRestrict_ker, h.codRestrict_apply_cod, isCompl_of_proj
-/
theorem isCompl {f : E ->ₗ[R] E} (h : IsProj p f) : IsCompl p (ker f) := by
  rw [← codRestrict_ker h]
  exact isCompl_of_proj h.codRestrict_apply_cod

/--
theorem `eq_conj_prod_map'` / 定理 `eq_conj_prod_map'`

English:
theorem eq_conj_prod_map'
  given: {f : E ->ₗ[R] E} (h : IsProj p f)
  proof: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.eq_comp_toLinearMap_symm]
  ext x
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coe_subtype,
      map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, co

中文:
定理 eq_conj_prod_map'
  条件: {f : E ->ₗ[R] E} (h : IsProj p f)
  证明: by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.eq_comp_toLinearMap_symm]
  ext x
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coe_subtype,
      map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, co

Depends on / 依赖: LinearEquiv, LinearEquiv.eq_comp_toLinearMap_symm, LinearMap, LinearMap.comp_assoc, add_zero, coe_inl, coe_inr, coe_prodEquivOfIsCompl, coe_subtype, comp_apply, comp_assoc, coprod_apply, eq_comp_toLinearMap_symm, h.map_id, id_apply, map_coe_ker, map_id, map_zero, prodMap_apply, zero_add
-/
theorem eq_conj_prod_map' {f : E ->ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).toLinearMap ∘ₗ
        prodMap id 0 ∘ₗ (p.prodEquivOfIsCompl (ker f) h.isCompl).symm.toLinearMap := by
  rw [← LinearMap.comp_assoc]; rw [LinearEquiv.eq_comp_toLinearMap_symm]
  ext x
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inl, coprod_apply, coe_subtype,
      map_zero, add_zero, h.map_id x x.2, prodMap_apply, id_apply]
  · simp only [coe_prodEquivOfIsCompl, comp_apply, coe_inr, coprod_apply, map_zero,
      coe_subtype, zero_add, map_coe_ker, prodMap_apply, zero_apply, add_zero]

/--
theorem `submodule_unique` / 定理 `submodule_unique`

English:
theorem submodule_unique
  statement: {f : M ->ₗ[S] M} {m₁ m₂ : Submodule S M}
  proof: by
  ext; simp [hf₁.mem_iff_map_id, hf₂.mem_iff_map_id]

中文:
定理 submodule_unique
  结论: {f : M ->ₗ[S] M} {m₁ m₂ : Submodule S M}
  证明: by
  ext; simp [hf₁.mem_iff_map_id, hf₂.mem_iff_map_id]

Depends on / 依赖: mem_iff_map_id
-/
theorem submodule_unique {f : M ->ₗ[S] M} {m₁ m₂ : Submodule S M}
    (hf₁ : IsProj m₁ f) (hf₂ : IsProj m₂ f) : m₁ = m₂ := by
  ext; simp [hf₁.mem_iff_map_id, hf₂.mem_iff_map_id]

open LinearMap in
/--
theorem `range` / 定理 `range`

English:
theorem range
  given: {f : M ->ₗ[S] M} (h : IsProj m f)
  statement: range f = m
  proof: h.isIdempotentElem.isProj_range.submodule_unique h

中文:
定理 range
  条件: {f : M ->ₗ[S] M} (h : IsProj m f)
  结论: range f = m
  证明: h.isIdempotentElem.isProj_range.submodule_unique h
-/
protected theorem range {f : M ->ₗ[S] M} (h : IsProj m f) : range f = m :=
  h.isIdempotentElem.isProj_range.submodule_unique h

variable (S M) in
/--
theorem `bot` / 定理 `bot`

English:
theorem bot
  statement: IsProj (⊥ : Submodule S M) (0 : M ->ₗ[S] M)
  proof: ⟨congrFun rfl, by simp only [mem_bot, zero_apply, forall_eq]⟩

中文:
定理 bot
  结论: IsProj (⊥ : Submodule S M) (0 : M ->ₗ[S] M)
  证明: ⟨congrFun rfl, by simp only [mem_bot, zero_apply, forall_eq]⟩
-/
protected theorem bot : IsProj (⊥ : Submodule S M) (0 : M ->ₗ[S] M) :=
  ⟨congrFun rfl, by simp only [mem_bot, zero_apply, forall_eq]⟩

variable (S M) in
/--
theorem `top` / 定理 `top`

English:
theorem top
  statement: IsProj (⊤ : Submodule S M) (id (R := S))
  proof: ⟨fun _ => trivial, fun _ => congrFun rfl⟩

中文:
定理 top
  结论: IsProj (⊤ : Submodule S M) (id (R := S))
  证明: ⟨fun _ => trivial, fun _ => congrFun rfl⟩
-/
protected theorem top : IsProj (⊤ : Submodule S M) (id (R := S)) :=
  ⟨fun _ => trivial, fun _ => congrFun rfl⟩

/--
theorem `subtype_comp_codRestrict` / 定理 `subtype_comp_codRestrict`

English:
theorem subtype_comp_codRestrict
  given: {U : Submodule S M} {f : M ->ₗ[S] M} (hf : IsProj U f)
  proof: rfl

中文:
定理 subtype_comp_codRestrict
  条件: {U : Submodule S M} {f : M ->ₗ[S] M} (hf : IsProj U f)
  证明: rfl
-/
theorem subtype_comp_codRestrict {U : Submodule S M} {f : M ->ₗ[S] M} (hf : IsProj U f) :
    U.subtype ∘ₗ hf.codRestrict = f := rfl

/--
theorem `submodule_eq_top_iff` / 定理 `submodule_eq_top_iff`

English:
theorem submodule_eq_top_iff
  given: {f : M ->ₗ[S] M} (hf : IsProj m f)
  proof: by
  constructor <;> rintro rfl
  · ext
    simp [hf.map_id]
  · rw [← hf.range, range_id]

中文:
定理 submodule_eq_top_iff
  条件: {f : M ->ₗ[S] M} (hf : IsProj m f)
  证明: by
  constructor <;> rintro rfl
  · ext
    simp [hf.map_id]
  · rw [← hf.range, range_id]

Depends on / 依赖: hf.map_id, hf.range, map_id, range_id
-/
theorem submodule_eq_top_iff {f : M ->ₗ[S] M} (hf : IsProj m f) :
    m = (⊤ : Submodule S M) ↔ f = LinearMap.id := by
  constructor <;> rintro rfl
  · ext
    simp [hf.map_id]
  · rw [← hf.range, range_id]

/--
theorem `submodule_eq_bot_iff` / 定理 `submodule_eq_bot_iff`

English:
theorem submodule_eq_bot_iff
  given: {f : M ->ₗ[S] M} (hf : IsProj m f)
  proof: by
  constructor <;> rintro rfl
  · ext
    simpa using hf.map_mem _
  · rw [← hf.range, range_zero]

中文:
定理 submodule_eq_bot_iff
  条件: {f : M ->ₗ[S] M} (hf : IsProj m f)
  证明: by
  constructor <;> rintro rfl
  · ext
    simpa using hf.map_mem _
  · rw [← hf.range, range_zero]

Depends on / 依赖: hf.map_mem, hf.range, map_mem, range_zero
-/
theorem submodule_eq_bot_iff {f : M ->ₗ[S] M} (hf : IsProj m f) :
    m = (⊥ : Submodule S M) ↔ f = 0 := by
  constructor <;> rintro rfl
  · ext
    simpa using hf.map_mem _
  · rw [← hf.range, range_zero]

end IsProj

open LinearMap in
/--
lemma `IsIdempotentElem.isCompl` / 引理 `IsIdempotentElem.isCompl`

English:
lemma IsIdempotentElem.isCompl
  given: {f : E ->ₗ[R] E} (hf : IsIdempotentElem f)
  proof: hf.isProj_range.isCompl

中文:
引理 IsIdempotentElem.isCompl
  条件: {f : E ->ₗ[R] E} (hf : IsIdempotentElem f)
  证明: hf.isProj_range.isCompl

Depends on / 依赖: hf.isProj_range.isCompl, isCompl, isProj_range
-/
lemma IsIdempotentElem.isCompl {f : E ->ₗ[R] E} (hf : IsIdempotentElem f) :
    IsCompl (range f) (ker f) := hf.isProj_range.isCompl

open LinearMap in
/--
theorem `IsIdempotentElem.mem_range_iff` / 定理 `IsIdempotentElem.mem_range_iff`

English:
theorem IsIdempotentElem.mem_range_iff
  given: {p : M ->ₗ[S] M} (hp : IsIdempotentElem p) {x : M}
  proof: hp.isProj_range.mem_iff_map_id

中文:
定理 IsIdempotentElem.mem_range_iff
  条件: {p : M ->ₗ[S] M} (hp : IsIdempotentElem p) {x : M}
  证明: hp.isProj_range.mem_iff_map_id

Depends on / 依赖: hp.isProj_range.mem_iff_map_id, isProj_range, mem_iff_map_id
-/
theorem IsIdempotentElem.mem_range_iff {p : M ->ₗ[S] M} (hp : IsIdempotentElem p) {x : M} :
    x in range p ↔ p x = x := hp.isProj_range.mem_iff_map_id

open LinearMap in
/--
theorem `IsIdempotentElem.eq_projection` / 定理 `IsIdempotentElem.eq_projection`

English:
theorem IsIdempotentElem.eq_projection
  given: {T : E ->ₗ[R] E} (hT : IsIdempotentElem T)
  proof: by
  convert! ofIsCompl_subtype_zero_eq hT.isCompl
.symm exact ofIsCompl_eq _ (by simp [hT.isProj_range.map_id]) (by simp)

中文:
定理 IsIdempotentElem.eq_projection
  条件: {T : E ->ₗ[R] E} (hT : IsIdempotentElem T)
  证明: by
  convert! ofIsCompl_subtype_zero_eq hT.isCompl
.symm exact ofIsCompl_eq _ (by simp [hT.isProj_range.map_id]) (by simp)

Depends on / 依赖: convert, hT.isCompl, hT.isProj_range.map_id, isCompl, isProj_range, map_id, ofIsCompl_eq, ofIsCompl_subtype_zero_eq
-/
theorem IsIdempotentElem.eq_projection {T : E ->ₗ[R] E} (hT : IsIdempotentElem T) :
    T = T.range.projection T.ker hT.isCompl := by
  convert! ofIsCompl_subtype_zero_eq hT.isCompl
.symm exact ofIsCompl_eq _ (by simp [hT.isProj_range.map_id]) (by simp)

open LinearMap in
/--
theorem `isIdempotentElem_iff_eq_projection_range_ker` / 定理 `isIdempotentElem_iff_eq_projection_range_ker`

English:
theorem isIdempotentElem_iff_eq_projection_range_ker
  given: {T : E ->ₗ[R] E}
  proof: ⟨fun hT => ⟨hT.isProj_range.isCompl, hT.eq_projection⟩,
   fun ⟨hT, h⟩ => h.symm ▸ isIdempotentElem_projection hT⟩

中文:
定理 isIdempotentElem_iff_eq_projection_range_ker
  条件: {T : E ->ₗ[R] E}
  证明: ⟨fun hT => ⟨hT.isProj_range.isCompl, hT.eq_projection⟩,
   fun ⟨hT, h⟩ => h.symm ▸ isIdempotentElem_projection hT⟩

Depends on / 依赖: R1Space, Regular, Regular.weaklyRegular, eq_projection, h.symm, hT.eq_projection, hT.isProj_range.isCompl, isCompl, isIdempotentElem_projection, isProj_range, weaklyRegular
-/
theorem isIdempotentElem_iff_eq_projection_range_ker {T : E ->ₗ[R] E} :
    IsIdempotentElem T ↔ exists (h : IsCompl (range T) (ker T)), T = T.range.projection T.ker h :=
  ⟨fun hT => ⟨hT.isProj_range.isCompl, hT.eq_projection⟩,
   fun ⟨hT, h⟩ => h.symm ▸ isIdempotentElem_projection hT⟩

open LinearMap in
/--
theorem `IsIdempotentElem.comp_eq_right_iff` / 定理 `IsIdempotentElem.comp_eq_right_iff`

English:
theorem IsIdempotentElem.comp_eq_right_iff
  statement: {q : M ->ₗ[S] M} (hq : IsIdempotentElem q)
  proof: by
  simp_rw [LinearMap.ext_iff, comp_apply, ← hq.mem_range_iff,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

中文:
定理 IsIdempotentElem.comp_eq_right_iff
  结论: {q : M ->ₗ[S] M} (hq : IsIdempotentElem q)
  证明: by
  simp_rw [LinearMap.ext_iff, comp_apply, ← hq.mem_range_iff,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

Depends on / 依赖: LinearMap, LinearMap.ext_iff, SetLike, SetLike.le_def, comp_apply, ext_iff, forall_apply_eq_imp_iff, forall_exists_index, hq.mem_range_iff, le_def, mem_range, mem_range_iff, simp_rw
-/
theorem IsIdempotentElem.comp_eq_right_iff {q : M ->ₗ[S] M} (hq : IsIdempotentElem q)
    {E : Type*} [AddCommMonoid E] [Module S E] (p : E ->ₗ[S] M) :
    q.comp p = p ↔ range p <= range q := by
  simp_rw [LinearMap.ext_iff, comp_apply, ← hq.mem_range_iff,
    SetLike.le_def, mem_range, forall_exists_index, forall_apply_eq_imp_iff]

open LinearMap in
/--
lemma `IsIdempotentElem.ext_iff` / 引理 `IsIdempotentElem.ext_iff`

English:
lemma IsIdempotentElem.ext_iff
  statement: {p q : E ->ₗ[R] E}
  proof: by
  refine ⟨fun h => ⟨congrArg range h, congrArg ker h⟩, fun ⟨hr, hk⟩ => ?_⟩
  ext x
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, rfl, _⟩ :=
    (ker p).existsUnique_add_of_isCompl hp.isCompl.symm x
  simp [mem_ker.mp, hv, (hk ▸ hv), (mem_range_iff hp).mp, hw, (mem_range_iff hq).mp, (hr ▸ hw)]

alias ⟨_, IsIdempote

中文:
引理 IsIdempotentElem.ext_iff
  结论: {p q : E ->ₗ[R] E}
  证明: by
  refine ⟨fun h => ⟨congrArg range h, congrArg ker h⟩, fun ⟨hr, hk⟩ => ?_⟩
  ext x
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, rfl, _⟩ :=
    (ker p).existsUnique_add_of_isCompl hp.isCompl.symm x
  simp [mem_ker.mp, hv, (hk ▸ hv), (mem_range_iff hp).mp, hw, (mem_range_iff hq).mp, (hr ▸ hw)]

alias ⟨_, IsIdempote

Depends on / 依赖: existsUnique_add_of_isCompl, hp.isCompl.symm, isCompl, mem_ker, mem_ker.mp, mem_range_iff
-/
lemma IsIdempotentElem.ext_iff {p q : E ->ₗ[R] E}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q) :
    p = q ↔ range p = range q ∧ ker p = ker q := by
  refine ⟨fun h => ⟨congrArg range h, congrArg ker h⟩, fun ⟨hr, hk⟩ => ?_⟩
  ext x
  obtain ⟨⟨v, hv⟩, ⟨w, hw⟩, rfl, _⟩ :=
    (ker p).existsUnique_add_of_isCompl hp.isCompl.symm x
  simp [mem_ker.mp, hv, (hk ▸ hv), (mem_range_iff hp).mp, hw, (mem_range_iff hq).mp, (hr ▸ hw)]

alias ⟨_, IsIdempotentElem.ext⟩ := IsIdempotentElem.ext_iff

/--
theorem `IsIdempotentElem.range_eq_ker` / 定理 `IsIdempotentElem.range_eq_ker`

English:
theorem IsIdempotentElem.range_eq_ker
  statement: {E : Type*} [AddCommGroup E] [Module S E]
  proof: le_antisymm
    (LinearMap.range_le_ker_iff.mpr hp.one_sub_mul_self)
    fun x hx => ⟨x, by simpa [sub_eq_zero, eq_comm (a := x)] using hx⟩

中文:
定理 IsIdempotentElem.range_eq_ker
  结论: {E : 类型} [AddCommGroup E] [Module S E]
  证明: le_antisymm
    (LinearMap.range_le_ker_iff.mpr hp.one_sub_mul_self)
    fun x hx => ⟨x, by simpa [sub_eq_zero, eq_comm (a := x)] using hx⟩

Depends on / 依赖: LinearMap, LinearMap.range_le_ker_iff.mpr, eq_comm, hp.one_sub_mul_self, le_antisymm, one_sub_mul_self, range_le_ker_iff, sub_eq_zero
-/
theorem IsIdempotentElem.range_eq_ker {E : Type*} [AddCommGroup E] [Module S E]
    {p : E ->ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.range p = LinearMap.ker (id - p) :=
  le_antisymm
    (LinearMap.range_le_ker_iff.mpr hp.one_sub_mul_self)
    fun x hx => ⟨x, by simpa [sub_eq_zero, eq_comm (a := x)] using hx⟩

/--
theorem `IsIdempotentElem.range_eq_ker_one_sub` / 定理 `IsIdempotentElem.range_eq_ker_one_sub`

English:
theorem IsIdempotentElem.range_eq_ker_one_sub
  statement: {E : Type*} [AddCommGroup E] [Module S E]
  proof: range_eq_ker hp

中文:
定理 IsIdempotentElem.range_eq_ker_one_sub
  结论: {E : 类型} [AddCommGroup E] [Module S E]
  证明: range_eq_ker hp

Depends on / 依赖: range_eq_ker
-/
theorem IsIdempotentElem.range_eq_ker_one_sub {E : Type*} [AddCommGroup E] [Module S E]
    {p : E ->ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.range p = LinearMap.ker (1 - p) :=
  range_eq_ker hp

open LinearMap in
/--
theorem `IsIdempotentElem.ker_eq_range` / 定理 `IsIdempotentElem.ker_eq_range`

English:
theorem IsIdempotentElem.ker_eq_range
  statement: {E : Type*} [AddCommGroup E] [Module S E]
  proof: by
  simpa using! hp.one_sub.range_eq_ker_one_sub.symm

中文:
定理 IsIdempotentElem.ker_eq_range
  结论: {E : 类型} [AddCommGroup E] [Module S E]
  证明: by
  simpa using! hp.one_sub.range_eq_ker_one_sub.symm

Depends on / 依赖: hp.one_sub.range_eq_ker_one_sub.symm, one_sub, range_eq_ker_one_sub
-/
theorem IsIdempotentElem.ker_eq_range {E : Type*} [AddCommGroup E] [Module S E]
    {p : E ->ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.ker p = LinearMap.range (id - p) := by
  simpa using! hp.one_sub.range_eq_ker_one_sub.symm

/--
theorem `IsIdempotentElem.ker_eq_range_one_sub` / 定理 `IsIdempotentElem.ker_eq_range_one_sub`

English:
theorem IsIdempotentElem.ker_eq_range_one_sub
  statement: {E : Type*} [AddCommGroup E] [Module S E]
  proof: ker_eq_range hp

中文:
定理 IsIdempotentElem.ker_eq_range_one_sub
  结论: {E : 类型} [AddCommGroup E] [Module S E]
  证明: ker_eq_range hp

Depends on / 依赖: ker_eq_range
-/
theorem IsIdempotentElem.ker_eq_range_one_sub {E : Type*} [AddCommGroup E] [Module S E]
    {p : E ->ₗ[S] E} (hp : IsIdempotentElem p) : LinearMap.ker p = LinearMap.range (1 - p) :=
  ker_eq_range hp

open LinearMap in
/--
theorem `IsIdempotentElem.comp_eq_left_iff` / 定理 `IsIdempotentElem.comp_eq_left_iff`

English:
theorem IsIdempotentElem.comp_eq_left_iff
  statement: {M : Type*} [AddCommGroup M] [Module S M] {q : M ->ₗ[S] M}
  proof: by
  simp [hq.ker_eq_range, range_le_ker_iff, comp_sub, sub_eq_zero, eq_comm]

中文:
定理 IsIdempotentElem.comp_eq_left_iff
  结论: {M : 类型} [AddCommGroup M] [Module S M] {q : M ->ₗ[S] M}
  证明: by
  simp [hq.ker_eq_range, range_le_ker_iff, comp_sub, sub_eq_zero, eq_comm]

Depends on / 依赖: comp_sub, eq_comm, hq.ker_eq_range, ker_eq_range, range_le_ker_iff, sub_eq_zero
-/
theorem IsIdempotentElem.comp_eq_left_iff {M : Type*} [AddCommGroup M] [Module S M] {q : M ->ₗ[S] M}
    (hq : IsIdempotentElem q) {E : Type*} [AddCommGroup E] [Module S E] (p : M ->ₗ[S] E) :
    p ∘ₗ q = p ↔ ker q <= ker p := by
  simp [hq.ker_eq_range, range_le_ker_iff, comp_sub, sub_eq_zero, eq_comm]

end LinearMap

end Ring

section CommRing

namespace LinearMap

variable {R : Type*} [CommRing R] {E : Type*} [AddCommGroup E] [Module R E] {p : Submodule R E}

/--
theorem `IsProj.eq_conj_prodMap` / 定理 `IsProj.eq_conj_prodMap`

English:
theorem IsProj.eq_conj_prodMap
  given: {f : E ->ₗ[R] E} (h : IsProj p f)
  proof: by
  rw [LinearEquiv.conj_apply]
  exact h.eq_conj_prod_map'

中文:
定理 IsProj.eq_conj_prodMap
  条件: {f : E ->ₗ[R] E} (h : IsProj p f)
  证明: by
  rw [LinearEquiv.conj_apply]
  exact h.eq_conj_prod_map'

Depends on / 依赖: LinearEquiv, LinearEquiv.conj_apply, conj_apply, eq_conj_prod_map, h.eq_conj_prod_map
-/
theorem IsProj.eq_conj_prodMap {f : E ->ₗ[R] E} (h : IsProj p f) :
    f = (p.prodEquivOfIsCompl (ker f) h.isCompl).conj (prodMap id 0) := by
  rw [LinearEquiv.conj_apply]
  exact h.eq_conj_prod_map'

end LinearMap

end CommRing

namespace LinearMap.IsIdempotentElem

open Submodule LinearMap

variable {E R : Type*} [Ring R] [AddCommGroup E] [Module R E] {T f : E ->ₗ[R] E}

/--
lemma `range_mem_invtSubmodule_iff` / 引理 `range_mem_invtSubmodule_iff`

English:
lemma range_mem_invtSubmodule_iff
  given: (hf : IsIdempotentElem f)
  proof: by
  rw [hf.comp_eq_right_iff]; rw [range_comp]; rw [Module.End.mem_invtSubmodule_iff_map_le]

alias ⟨conj_eq_of_range_mem_invtSubmodule, range_mem_invtSubmodule⟩ := range_mem_invtSubmodule_iff

中文:
引理 range_mem_invtSubmodule_iff
  条件: (hf : IsIdempotentElem f)
  证明: by
  rw [hf.comp_eq_right_iff]; rw [range_comp]; rw [Module.End.mem_invtSubmodule_iff_map_le]

alias ⟨conj_eq_of_range_mem_invtSubmodule, range_mem_invtSubmodule⟩ := range_mem_invtSubmodule_iff

Depends on / 依赖: Module, Module.End.mem_invtSubmodule_iff_map_le, comp_eq_right_iff, hf.comp_eq_right_iff, mem_invtSubmodule_iff_map_le, range_comp
-/
lemma range_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    range f in Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f := by
  rw [hf.comp_eq_right_iff]; rw [range_comp]; rw [Module.End.mem_invtSubmodule_iff_map_le]

alias ⟨conj_eq_of_range_mem_invtSubmodule, range_mem_invtSubmodule⟩ := range_mem_invtSubmodule_iff

/--
lemma `_root_.LinearMap.IsProj.mem_invtSubmodule_iff` / 引理 `_root_.LinearMap.IsProj.mem_invtSubmodule_iff`

English:
lemma _root_.LinearMap.IsProj.mem_invtSubmodule_iff
  statement: {U : Submodule R E}
  proof: hf.range ▸ hf.isIdempotentElem.range_mem_invtSubmodule_iff

中文:
引理 _root_.LinearMap.IsProj.mem_invtSubmodule_iff
  结论: {U : Submodule R E}
  证明: hf.range ▸ hf.isIdempotentElem.range_mem_invtSubmodule_iff

Depends on / 依赖: hf.isIdempotentElem.range_mem_invtSubmodule_iff, hf.range, isIdempotentElem, range_mem_invtSubmodule_iff
-/
lemma _root_.LinearMap.IsProj.mem_invtSubmodule_iff {U : Submodule R E}
    (hf : IsProj U f) : U in Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = T ∘ₗ f :=
  hf.range ▸ hf.isIdempotentElem.range_mem_invtSubmodule_iff

open LinearMap in
/--
lemma `ker_mem_invtSubmodule_iff` / 引理 `ker_mem_invtSubmodule_iff`

English:
lemma ker_mem_invtSubmodule_iff
  given: (hf : IsIdempotentElem f)
  proof: by
  rw [← comp_assoc]; rw [hf.comp_eq_left_iff]; rw [ker_comp]; rw [Module.End.mem_invtSubmodule]

alias ⟨conj_eq_of_ker_mem_invtSubmodule, ker_mem_invtSubmodule⟩ := ker_mem_invtSubmodule_iff

中文:
引理 ker_mem_invtSubmodule_iff
  条件: (hf : IsIdempotentElem f)
  证明: by
  rw [← comp_assoc]; rw [hf.comp_eq_left_iff]; rw [ker_comp]; rw [Module.End.mem_invtSubmodule]

alias ⟨conj_eq_of_ker_mem_invtSubmodule, ker_mem_invtSubmodule⟩ := ker_mem_invtSubmodule_iff

Depends on / 依赖: Module, Module.End.mem_invtSubmodule, comp_assoc, comp_eq_left_iff, hf.comp_eq_left_iff, ker_comp, mem_invtSubmodule
-/
lemma ker_mem_invtSubmodule_iff (hf : IsIdempotentElem f) :
    ker f in Module.End.invtSubmodule T ↔ f ∘ₗ T ∘ₗ f = f ∘ₗ T := by
  rw [← comp_assoc]; rw [hf.comp_eq_left_iff]; rw [ker_comp]; rw [Module.End.mem_invtSubmodule]

alias ⟨conj_eq_of_ker_mem_invtSubmodule, ker_mem_invtSubmodule⟩ := ker_mem_invtSubmodule_iff

/--
lemma `commute_iff` / 引理 `commute_iff`

English:
lemma commute_iff
  given: (hf : IsIdempotentElem f)
  proof: by
  simp_rw [hf.range_mem_invtSubmodule_iff, hf.ker_mem_invtSubmodule_iff, ← Module.End.mul_eq_comp]
  exact ⟨fun h => (by simp [← h.eq, ← mul_assoc, hf.eq]), fun ⟨h1, h2⟩ => h2.symm.trans h1⟩

中文:
引理 commute_iff
  条件: (hf : IsIdempotentElem f)
  证明: by
  simp_rw [hf.range_mem_invtSubmodule_iff, hf.ker_mem_invtSubmodule_iff, ← Module.End.mul_eq_comp]
  exact ⟨fun h => (by simp [← h.eq, ← mul_assoc, hf.eq]), fun ⟨h1, h2⟩ => h2.symm.trans h1⟩

Depends on / 依赖: Module, Module.End.mul_eq_comp, h.eq, h2.symm.trans, hf.eq, hf.ker_mem_invtSubmodule_iff, hf.range_mem_invtSubmodule_iff, ker_mem_invtSubmodule_iff, mul_assoc, mul_eq_comp, range_mem_invtSubmodule_iff, simp_rw
-/
lemma commute_iff (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f in Module.End.invtSubmodule T ∧ ker f in Module.End.invtSubmodule T) := by
  simp_rw [hf.range_mem_invtSubmodule_iff, hf.ker_mem_invtSubmodule_iff, ← Module.End.mul_eq_comp]
  exact ⟨fun h => (by simp [← h.eq, ← mul_assoc, hf.eq]), fun ⟨h1, h2⟩ => h2.symm.trans h1⟩

/--
theorem `commute_iff_of_isUnit` / 定理 `commute_iff_of_isUnit`

English:
theorem commute_iff_of_isUnit
  given: (hT : IsUnit T) (hf : IsIdempotentElem f)
  proof: by
  lift T to GeneralLinearGroup R E using hT
  simp_rw [← GeneralLinearGroup.generalLinearEquiv_to_linearMap, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map_le, ← Module.End.mem_invtSubmodule_symm_iff_le_map,
    and_and_and_comm (c := (ker f in _)), ← hf.commute_iff,
    GeneralLinea

中文:
定理 commute_iff_of_isUnit
  条件: (hT : IsUnit T) (hf : IsIdempotentElem f)
  证明: by
  lift T to GeneralLinearGroup R E using hT
  simp_rw [← GeneralLinearGroup.generalLinearEquiv_to_linearMap, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map_le, ← Module.End.mem_invtSubmodule_symm_iff_le_map,
    and_and_and_comm (c := (ker f in _)), ← hf.commute_iff,
    GeneralLinea

Depends on / 依赖: Commute, Commute.units_inv_right, GeneralLinearGroup, GeneralLinearGroup.generalLinearEquiv_to_linearMap, Module, Module.End.mem_invtSubmodule_iff_map_le, Module.End.mem_invtSubmodule_symm_iff_le_map, and_and_and_comm, commute_iff, generalLinearEquiv_to_linearMap, hf.commute_iff, iff_self_and, le_antisymm_iff, mem_invtSubmodule_iff_map_le, mem_invtSubmodule_symm_iff_le_map, simp_rw, units_inv_right
-/
theorem commute_iff_of_isUnit (hT : IsUnit T) (hf : IsIdempotentElem f) :
    Commute f T ↔ (range f).map T = range f ∧ (ker f).map T = ker f := by
  lift T to GeneralLinearGroup R E using hT
  simp_rw [← GeneralLinearGroup.generalLinearEquiv_to_linearMap, le_antisymm_iff,
    ← Module.End.mem_invtSubmodule_iff_map_le, ← Module.End.mem_invtSubmodule_symm_iff_le_map,
    and_and_and_comm (c := (ker f in _)), ← hf.commute_iff,
    GeneralLinearGroup.generalLinearEquiv_to_linearMap, iff_self_and]
  exact Commute.units_inv_right

end LinearMap.IsIdempotentElem

/-! ## Deprecated -/

namespace Submodule

@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl := projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection := projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply := projection_apply
@[deprecated (since := "2026-05-04")] alias coe_linearProjOfIsCompl_apply :=
  coe_projectionOnto_apply
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_mem := projection_apply_mem
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_left :=
  projectionOnto_apply_left
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_left := projection_apply_left
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_range := range_projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_range := range_projection
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_surjective :=
  projectionOnto_surjective
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_eq_zero_iff :=
  projectionOnto_apply_eq_zero_iff
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_apply_eq_zero_iff :=
  projection_apply_eq_zero_iff
@[deprecated (since := "2026-05-05")] alias linearProjOfIsCompl_apply_of_mem_right :=
  projectionOnto_apply_of_mem_right
@[deprecated (since := "2026-04-27")] alias linearProjOfIsCompl_apply_right' :=
  projectionOnto_apply_of_mem_right
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_apply_of_mem_right :=
  projection_apply_of_mem_right
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_apply_right :=
  projectionOnto_apply_right
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_apply_right :=
  projection_apply_right
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_ker := ker_projectionOnto
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_ker := ker_projection
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_comp_subtype :=
  projectionOnto_comp_subtype
@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_isCompl_projection :=
  projectionOnto_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_isIdempotentElem :=
  isIdempotentElem_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_add_projection_eq_self :=
  projection_add_projection_eq_self
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_add_projection_eq_id :=
  projection_add_projection_eq_id
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_eq_self_sub_projection :=
  projection_eq_self_sub_projection
@[deprecated (since := "2026-05-05")] alias IsCompl.projection_eq_id_sub_projection :=
  projection_eq_id_sub_projection
@[deprecated (since := "2026-05-04")] alias IsCompl.projection_eq_self_iff := projection_eq_self_iff

end Submodule

namespace LinearMap

@[deprecated (since := "2026-05-04")] alias linearProjOfIsCompl_of_proj := projectionOnto_of_proj
@[deprecated (since := "2026-05-04")] alias IsIdempotentElem.eq_isCompl_projection :=
  IsIdempotentElem.eq_projection
@[deprecated (since := "2026-05-04")] alias surjective_comp_linearProjOfIsCompl :=
  surjective_comp_projectionOnto
@[deprecated (since := "2026-05-04")] alias isIdempotentElem_iff_eq_isCompl_projection_range_ker :=
  isIdempotentElem_iff_eq_projection_range_ker
@[deprecated (since := "2026-05-16")] alias ofIsCompl_left_apply := ofIsCompl_apply_left
@[deprecated (since := "2026-05-16")] alias ofIsCompl_right_apply := ofIsCompl_apply_right

end LinearMap
