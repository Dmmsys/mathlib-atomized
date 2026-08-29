/-
Copyright (c) 2024 Gabin Kolly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly, David Wärn
-/
module

public import Mathlib.ModelTheory.DirectLimit
public import Mathlib.Order.Ideal

/-!
# Partial Isomorphisms

This file defines partial isomorphisms between first-order structures.

## Main Definitions
- `FirstOrder.Language.PartialEquiv` is defined so that `L.PartialEquiv M N`, annotated
  `M ≃ₚ[L] N`, is the type of equivalences between substructures of `M` and `N`. These can be
  ordered, with an order that is defined here in terms of a commutative square, but could also be
  defined as the order on the graphs of the partial equivalences under inclusion as subsets of
  `M × N`.
- `FirstOrder.Language.FGEquiv` is the type of partial equivalences `M ≃ₚ[L] N` with
  finitely-generated domain (or equivalently, codomain).
- `FirstOrder.Language.IsExtensionPair` is defined so that `L.IsExtensionPair M N` indicates that
  any finitely-generated partial equivalence from `M` to `N` can be extended to include an arbitrary
  element `m : M` in its domain.

## Main Results
- `FirstOrder.Language.embedding_from_cg` shows that if structures `M` and `N` form an equivalence
  pair with `M` countably-generated, then any finite-generated partial equivalence between them
  can be extended to an embedding `M ↪[L] N`.
- `FirstOrder.Language.equiv_from_cg` shows that if countably-generated structures `M` and `N` form
  an equivalence pair in both directions, then any finite-generated partial equivalence between them
  can be extended to an isomorphism `M ↪[L] N`.
- The proofs of these results are adapted in part from David Wärn's approach to countable dense
  linear orders, a special case of this phenomenon in the case where `L = Language.order`.

-/

@[expose] public section

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) (M : Type w) (N : Type w')
variable [L.Structure M] [L.Structure N]

open FirstOrder Structure Substructure

/--
Definition of `PartialEquiv` / `PartialEquiv` 的定义

English:
structure PartialEquiv
  parameters: where
  axioms and operations (3):
    - dom : L.Substructure M
    - cod : L.Substructure N
    - toEquiv : dom ≃[L] cod

中文:
结构 部分等价
  参数: where
  公理与运算 (3 个):
    - dom : L.子结构 M
    - cod : L.子结构 N
    - toEquiv : dom ≃[L] cod
-/
structure PartialEquiv where
  /-- The substructure which is the domain of the equivalence. -/
  dom : L.Substructure M
  /-- The substructure which is the codomain of the equivalence. -/
  cod : L.Substructure N
  /-- The equivalence between the two subdomains. -/
  toEquiv : dom ≃[L] cod

@[inherit_doc]
scoped[FirstOrder] notation:25 M " ≃ₚ[" L "] " N =>
  FirstOrder.Language.PartialEquiv L M N

variable {L M N}

namespace PartialEquiv

/--
Instance `instInhabited_self` / 实例 `instInhabited_self`

English:
instance instInhabited_self
  signature: : Inhabited (M ≃ₚ[L] M)
  body: ⟨⊤, ⊤, Equiv.refl L (⊤ : L.Substructure M)⟩

中文:
实例 instInhabited_self
  签名: : 可居 (M ≃ₚ[L] M)
  定义体: ⟨⊤, ⊤, Equiv.refl L (⊤ : L.Substructure M)⟩

Depends on / 依赖: Equiv.refl, L.Substructure, Substructure
-/
noncomputable instance instInhabited_self : Inhabited (M ≃ₚ[L] M) :=
  ⟨⊤, ⊤, Equiv.refl L (⊤ : L.Substructure M)⟩

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : M ≃ₚ[L] N)
  body: f.cod
  cod := f.dom
  toEquiv := f.toEquiv.symm

@[simp]

中文:
定义 symm
  签名: (f : M ≃ₚ[L] N)
  定义体: f.cod
  cod := f.dom
  toEquiv := f.toEquiv.symm

@[simp]

Depends on / 依赖: f.cod
-/
def symm (f : M ≃ₚ[L] N) : N ≃ₚ[L] M where
  dom := f.cod
  cod := f.dom
  toEquiv := f.toEquiv.symm

@[simp]
/--
theorem `symm_symm` / 定理 `symm_symm`

English:
theorem symm_symm
  given: (f : M ≃ₚ[L] N)
  statement: f.symm.symm = f
  proof: rfl

中文:
定理 symm_symm
  条件: (f : M ≃ₚ[L] N)
  结论: f.symm.symm = f
  证明: rfl
-/
theorem symm_symm (f : M ≃ₚ[L] N) : f.symm.symm = f :=
  rfl

/--
theorem `symm_bijective` / 定理 `symm_bijective`

English:
theorem symm_bijective
  statement: Function.Bijective (symm : (M ≃ₚ[L] N) -> _)
  proof: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

中文:
定理 symm_bijective
  结论: 函数.双射 (symm : (M ≃ₚ[L] N) -> _)
  证明: Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]

Depends on / 依赖: Function, Function.bijective_iff_has_inverse.mpr, bijective_iff_has_inverse, symm_symm
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃ₚ[L] N) -> _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/--
theorem `symm_apply` / 定理 `symm_apply`

English:
theorem symm_apply
  given: (f : M ≃ₚ[L] N) (x : f.cod)
  statement: f.symm.toEquiv x = f.toEquiv.symm x
  proof: rfl

中文:
定理 symm_apply
  条件: (f : M ≃ₚ[L] N) (x : f.cod)
  结论: f.symm.toEquiv x = f.toEquiv.symm x
  证明: rfl
-/
theorem symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.toEquiv x = f.toEquiv.symm x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (M ≃ₚ[L] N)
  body: ⟨fun f g => exists h : f.dom <= g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding⟩

中文:
实例 :
  签名: LE (M ≃ₚ[L] N)
  定义体: ⟨fun f g => exists h : f.dom <= g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding⟩

Depends on / 依赖: Substructure, Substructure.inclusion, f.dom, f.toEquiv.toEmbedding, g.dom, g.toEquiv.toEmbedding.comp, inclusion, subtype, toEmbedding, toEquiv
-/
instance : LE (M ≃ₚ[L] N) :=
  ⟨fun f g => exists h : f.dom <= g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: (f g : M ≃ₚ[L] N)
  statement: f <= g ↔ exists h : f.dom <= g.dom,
  proof: Iff.rfl

中文:
定理 le_def
  条件: (f g : M ≃ₚ[L] N)
  结论: f <= g ↔ 存在 h : f.dom <= g.dom,
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def (f g : M ≃ₚ[L] N) : f <= g ↔ exists h : f.dom <= g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding :=
  Iff.rfl

/--
theorem `dom_le_dom` / 定理 `dom_le_dom`

English:
theorem dom_le_dom
  given: {f g : M ≃ₚ[L] N}
  statement: f <= g -> f.dom <= g.dom
  proof: fun ⟨le, _⟩ => le

中文:
定理 dom_le_dom
  条件: {f g : M ≃ₚ[L] N}
  结论: f <= g -> f.dom <= g.dom
  证明: fun ⟨le, _⟩ => le
-/
@[gcongr] theorem dom_le_dom {f g : M ≃ₚ[L] N} : f <= g -> f.dom <= g.dom := fun ⟨le, _⟩ => le

/--
theorem `cod_le_cod` / 定理 `cod_le_cod`

English:
theorem cod_le_cod
  given: {f g : M ≃ₚ[L] N}
  statement: f <= g -> f.cod <= g.cod
  proof: by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.toEquiv.symm ⟨n, hn⟩
  have : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coe_subtype]
  rw [← this]; rw [← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
    SetLike.coe_mem]

中文:
定理 cod_le_cod
  条件: {f g : M ≃ₚ[L] N}
  结论: f <= g -> f.cod <= g.cod
  证明: by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.toEquiv.symm ⟨n, hn⟩
  have : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coe_subtype]
  rw [← this]; rw [← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
    SetLike.coe_mem]
-/
@[gcongr] theorem cod_le_cod {f g : M ≃ₚ[L] N} : f <= g -> f.cod <= g.cod := by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.toEquiv.symm ⟨n, hn⟩
  have : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coe_subtype]
  rw [← this]; rw [← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
    SetLike.coe_mem]

/--
theorem `subtype_toEquiv_inclusion` / 定理 `subtype_toEquiv_inclusion`

English:
theorem subtype_toEquiv_inclusion
  given: {f g : M ≃ₚ[L] N} (h : f <= g)
  proof: by
  let ⟨_, eq⟩ := h; exact eq

中文:
定理 subtype_toEquiv_inclusion
  条件: {f g : M ≃ₚ[L] N} (h : f <= g)
  证明: by
  let ⟨_, eq⟩ := h; exact eq
-/
theorem subtype_toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) :
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h))) =
      (subtype _).comp f.toEquiv.toEmbedding := by
  let ⟨_, eq⟩ := h; exact eq

/--
theorem `toEquiv_inclusion` / 定理 `toEquiv_inclusion`

English:
theorem toEquiv_inclusion
  given: {f g : M ≃ₚ[L] N} (h : f <= g)
  proof: by
  rw [← (subtype _).comp_inj]; rw [subtype_toEquiv_inclusion h]
  ext
  simp

中文:
定理 toEquiv_inclusion
  条件: {f g : M ≃ₚ[L] N} (h : f <= g)
  证明: by
  rw [← (subtype _).comp_inj]; rw [subtype_toEquiv_inclusion h]
  ext
  simp

Depends on / 依赖: comp_inj, subtype, subtype_toEquiv_inclusion
-/
theorem toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f <= g) :
    g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h)) =
      (Substructure.inclusion (cod_le_cod h)).comp f.toEquiv.toEmbedding := by
  rw [← (subtype _).comp_inj]; rw [subtype_toEquiv_inclusion h]
  ext
  simp

/--
theorem `toEquiv_inclusion_apply` / 定理 `toEquiv_inclusion_apply`

English:
theorem toEquiv_inclusion_apply
  given: {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom)
  proof: by
  apply (subtype _).injective
  change (subtype _).comp (g.toEquiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_toEquiv_inclusion h]
  simp

中文:
定理 toEquiv_inclusion_apply
  条件: {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom)
  证明: by
  apply (subtype _).injective
  change (subtype _).comp (g.toEquiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_toEquiv_inclusion h]
  simp

Depends on / 依赖: g.toEquiv.toEmbedding.comp, inclusion, injective, subtype, subtype_toEquiv_inclusion, toEmbedding, toEquiv
-/
theorem toEquiv_inclusion_apply {f g : M ≃ₚ[L] N} (h : f <= g) (x : f.dom) :
    g.toEquiv (Substructure.inclusion (dom_le_dom h) x) =
      Substructure.inclusion (cod_le_cod h) (f.toEquiv x) := by
  apply (subtype _).injective
  change (subtype _).comp (g.toEquiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_toEquiv_inclusion h]
  simp

/--
theorem `le_iff` / 定理 `le_iff`

English:
theorem le_iff
  given: {f g : M ≃ₚ[L] N}
  statement: f <= g ↔
  proof: by
  constructor
  · exact fun h => ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [toEquiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.toEquiv _) = _; rw [← h_eq]; rfl⟩

中文:
定理 le_iff
  条件: {f g : M ≃ₚ[L] N}
  结论: f <= g ↔
  证明: by
  constructor
  · exact fun h => ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [toEquiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.toEquiv _) = _; rw [← h_eq]; rfl⟩

Depends on / 依赖: cod_le_cod, dom_le_dom, g.toEquiv, h_eq, le_cod, le_def, subtype, toEquiv, toEquiv_inclusion_apply
-/
theorem le_iff {f g : M ≃ₚ[L] N} : f <= g ↔
    exists dom_le_dom : f.dom <= g.dom,
    exists cod_le_cod : f.cod <= g.cod,
    forall x, inclusion cod_le_cod (f.toEquiv x) = g.toEquiv (inclusion dom_le_dom x) := by
  constructor
  · exact fun h => ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [toEquiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.toEquiv _) = _; rw [← h_eq]; rfl⟩

-- probably the initial design intended this to be private, just like `le_refl` and `le_antisymm`?
/--
theorem `le_trans` / 定理 `le_trans`

English:
theorem le_trans
  given: (f g h : M ≃ₚ[L] N)
  statement: f <= g -> g <= h -> f <= h
  proof: by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg]; rw [← Embedding.comp_assoc (g := g.toEquiv.toEmbedding)]; rw [← eq_gh]
  ext
  simp

中文:
定理 le_trans
  条件: (f g h : M ≃ₚ[L] N)
  结论: f <= g -> g <= h -> f <= h
  证明: by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg]; rw [← Embedding.comp_assoc (g := g.toEquiv.toEmbedding)]; rw [← eq_gh]
  ext
  simp

Depends on / 依赖: Embedding, Embedding.comp_assoc, comp_assoc, eq_fg, eq_gh, g.toEquiv.toEmbedding, le_fg, le_fg.trans, le_gh, toEmbedding, toEquiv
-/
theorem le_trans (f g h : M ≃ₚ[L] N) : f <= g -> g <= h -> f <= h := by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg]; rw [← Embedding.comp_assoc (g := g.toEquiv.toEmbedding)]; rw [← eq_gh]
  ext
  simp

/--
theorem `le_refl` / 定理 `le_refl`

English:
theorem le_refl
  given: (f : M ≃ₚ[L] N)
  statement: f <= f
  proof: ⟨le_rfl, rfl⟩

中文:
定理 le_refl
  条件: (f : M ≃ₚ[L] N)
  结论: f <= f
  证明: ⟨le_rfl, rfl⟩
-/
private theorem le_refl (f : M ≃ₚ[L] N) : f <= f := ⟨le_rfl, rfl⟩

/--
theorem `le_antisymm` / 定理 `le_antisymm`

English:
theorem le_antisymm
  given: (f g : M ≃ₚ[L] N) (le_fg : f <= g) (le_gf : g <= f)
  statement: f = g
  proof: by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert! rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_toEquiv_inclusion le_fg))

中文:
定理 le_antisymm
  条件: (f g : M ≃ₚ[L] N) (le_fg : f <= g) (le_gf : g <= f)
  结论: f = g
  证明: by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert! rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_toEquiv_inclusion le_fg))
-/
private theorem le_antisymm (f g : M ≃ₚ[L] N) (le_fg : f <= g) (le_gf : g <= f) : f = g := by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert! rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_toEquiv_inclusion le_fg))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (M ≃ₚ[L] N)
  body: private le_refl
  le_trans := le_trans
  le_antisymm := private le_antisymm

中文:
实例 :
  签名: 偏序 (M ≃ₚ[L] N)
  定义体: private le_refl
  le_trans := le_trans
  le_antisymm := private le_antisymm

Depends on / 依赖: le_refl, private
-/
instance : PartialOrder (M ≃ₚ[L] N) where
  le_refl := private le_refl
  le_trans := le_trans
  le_antisymm := private le_antisymm

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `symm_le_symm` / 引理 `symm_le_symm`

English:
lemma symm_le_symm
  given: {f g : M ≃ₚ[L] N} (hfg : f <= g)
  statement: f.symm <= g.symm
  proof: by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.toEquiv.injective
  change g.toEquiv (inclusion _ (f.toEquiv.symm x)) = g.toEquiv (g.toEquiv.symm _)
  rw [g.toEquiv.apply_symm_apply]; rw [(Equiv.apply_symm_apply f.toEquiv x).symm]; rw [f.toEquiv.symm_apply_apply]
  exact toEquiv_inclusion_apply hfg _

中文:
引理 symm_le_symm
  条件: {f g : M ≃ₚ[L] N} (hfg : f <= g)
  结论: f.symm <= g.symm
  证明: by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.toEquiv.injective
  change g.toEquiv (inclusion _ (f.toEquiv.symm x)) = g.toEquiv (g.toEquiv.symm _)
  rw [g.toEquiv.apply_symm_apply]; rw [(Equiv.apply_symm_apply f.toEquiv x).symm]; rw [f.toEquiv.symm_apply_apply]
  exact toEquiv_inclusion_apply hfg _
-/
@[gcongr] lemma symm_le_symm {f g : M ≃ₚ[L] N} (hfg : f <= g) : f.symm <= g.symm := by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.toEquiv.injective
  change g.toEquiv (inclusion _ (f.toEquiv.symm x)) = g.toEquiv (g.toEquiv.symm _)
  rw [g.toEquiv.apply_symm_apply]; rw [(Equiv.apply_symm_apply f.toEquiv x).symm]; rw [f.toEquiv.symm_apply_apply]
  exact toEquiv_inclusion_apply hfg _

/--
theorem `monotone_symm` / 定理 `monotone_symm`

English:
theorem monotone_symm
  statement: Monotone (fun (f : M ≃ₚ[L] N) => f.symm)
  proof: fun _ _ => symm_le_symm

中文:
定理 monotone_symm
  结论: 递增 (fun (f : M ≃ₚ[L] N) => f.symm)
  证明: fun _ _ => symm_le_symm

Depends on / 依赖: symm_le_symm
-/
theorem monotone_symm : Monotone (fun (f : M ≃ₚ[L] N) => f.symm) := fun _ _ => symm_le_symm

/--
theorem `symm_le_iff` / 定理 `symm_le_iff`

English:
theorem symm_le_iff
  given: {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M}
  statement: f.symm <= g ↔ f <= g.symm
  proof: ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw [← g.symm_symm]; exact monotone_symm h⟩

中文:
定理 symm_le_iff
  条件: {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M}
  结论: f.symm <= g ↔ f <= g.symm
  证明: ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw [← g.symm_symm]; exact monotone_symm h⟩

Depends on / 依赖: f.symm_symm, g.symm_symm, monotone_symm, symm_symm
-/
theorem symm_le_iff {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M} : f.symm <= g ↔ f <= g.symm :=
  ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw [← g.symm_symm]; exact monotone_symm h⟩

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom)
  statement: (forall x : M, forall h : x in f.dom,
  proof: by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use le_rfl; ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx

中文:
定理 ext
  条件: {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom)
  结论: (对任意 x : M, 对任意 h : x in f.dom,
  证明: by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use le_rfl; ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx

Depends on / 依赖: cod_f, dom_f, equiv_f, h_dom, le_antisymm, le_def, le_rfl
-/
theorem ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (forall x : M, forall h : x in f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩)) -> f = g := by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use le_rfl; ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx

/--
theorem `ext_iff` / 定理 `ext_iff`

English:
theorem ext_iff
  given: {f g : M ≃ₚ[L] N}
  statement: f = g ↔ exists h_dom : f.dom = g.dom,
  proof: by
  constructor
  · intro h_eq
    rcases f with ⟨dom_f, cod_f, equiv_f⟩
    cases h_eq
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨h, H⟩; exact ext h H

中文:
定理 ext_iff
  条件: {f g : M ≃ₚ[L] N}
  结论: f = g ↔ 存在 h_dom : f.dom = g.dom,
  证明: by
  constructor
  · intro h_eq
    rcases f with ⟨dom_f, cod_f, equiv_f⟩
    cases h_eq
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨h, H⟩; exact ext h H

Depends on / 依赖: cod_f, dom_f, equiv_f, h_eq
-/
theorem ext_iff {f g : M ≃ₚ[L] N} : f = g ↔ exists h_dom : f.dom = g.dom,
    forall x : M, forall h : x in f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩) := by
  constructor
  · intro h_eq
    rcases f with ⟨dom_f, cod_f, equiv_f⟩
    cases h_eq
    exact ⟨rfl, fun _ _ => rfl⟩
  · rintro ⟨h, H⟩; exact ext h H

/--
theorem `monotone_dom` / 定理 `monotone_dom`

English:
theorem monotone_dom
  statement: Monotone (fun f : M ≃ₚ[L] N => f.dom)
  proof: fun _ _ => dom_le_dom

中文:
定理 monotone_dom
  结论: 递增 (fun f : M ≃ₚ[L] N => f.dom)
  证明: fun _ _ => dom_le_dom

Depends on / 依赖: dom_le_dom
-/
theorem monotone_dom : Monotone (fun f : M ≃ₚ[L] N => f.dom) := fun _ _ => dom_le_dom

/--
theorem `monotone_cod` / 定理 `monotone_cod`

English:
theorem monotone_cod
  statement: Monotone (fun f : M ≃ₚ[L] N => f.cod)
  proof: fun _ _ => cod_le_cod

中文:
定理 monotone_cod
  结论: 递增 (fun f : M ≃ₚ[L] N => f.cod)
  证明: fun _ _ => cod_le_cod

Depends on / 依赖: cod_le_cod, hs.prod, prod_mem_prod
-/
theorem monotone_cod : Monotone (fun f : M ≃ₚ[L] N => f.cod) := fun _ _ => cod_le_cod

/--
Definition of `domRestrict` / `domRestrict` 的定义

English:
definition domRestrict
  signature: (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom)
  body: by
  let g := (subtype _).comp (f.toEquiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    toEquiv := g.equivRange
  }

中文:
定义 domRestrict
  签名: (f : M ≃ₚ[L] N) {A : L.子结构 M} (h : A <= f.dom)
  定义体: by
  let g := (subtype _).comp (f.toEquiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    toEquiv := g.equivRange
  }

Depends on / 依赖: A.inclusion, equivRange, f.toEquiv.toEmbedding.comp, g.equivRange, g.toHom.range, inclusion, subtype, toEmbedding, toEquiv
-/
noncomputable def domRestrict (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom) :
    M ≃ₚ[L] N := by
  let g := (subtype _).comp (f.toEquiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    toEquiv := g.equivRange
  }

/--
theorem `domRestrict_le` / 定理 `domRestrict_le`

English:
theorem domRestrict_le
  given: (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom)
  proof: ⟨h, rfl⟩

中文:
定理 domRestrict_le
  条件: (f : M ≃ₚ[L] N) {A : L.子结构 M} (h : A <= f.dom)
  证明: ⟨h, rfl⟩
-/
theorem domRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A <= f.dom) :
    f.domRestrict h <= f := ⟨h, rfl⟩

/--
theorem `le_domRestrict` / 定理 `le_domRestrict`

English:
theorem le_domRestrict
  statement: (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom <= A)
  proof: ⟨hf, by rw [← (subtype_toEquiv_inclusion hfg)]; rfl⟩

中文:
定理 le_domRestrict
  结论: (f g : M ≃ₚ[L] N) {A : L.子结构 M} (hf : f.dom <= A)
  证明: ⟨hf, by rw [← (subtype_toEquiv_inclusion hfg)]; rfl⟩

Depends on / 依赖: subtype_toEquiv_inclusion
-/
theorem le_domRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom <= A)
    (hg : A <= g.dom) (hfg : f <= g) : f <= g.domRestrict hg :=
  ⟨hf, by rw [← (subtype_toEquiv_inclusion hfg)]; rfl⟩

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod)
  body: (f.symm.domRestrict h).symm

中文:
定义 codRestrict
  签名: (f : M ≃ₚ[L] N) {A : L.子结构 N} (h : A <= f.cod)
  定义体: (f.symm.domRestrict h).symm

Depends on / 依赖: domRestrict, f.symm.domRestrict
-/
noncomputable def codRestrict (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod) :
    M ≃ₚ[L] N :=
  (f.symm.domRestrict h).symm

/--
theorem `codRestrict_le` / 定理 `codRestrict_le`

English:
theorem codRestrict_le
  given: (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod)
  proof: symm_le_iff.2 (f.symm.domRestrict_le h)

中文:
定理 codRestrict_le
  条件: (f : M ≃ₚ[L] N) {A : L.子结构 N} (h : A <= f.cod)
  证明: symm_le_iff.2 (f.symm.domRestrict_le h)

Depends on / 依赖: domRestrict_le, f.symm.domRestrict_le, symm_le_iff
-/
theorem codRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A <= f.cod) :
    codRestrict f h <= f :=
  symm_le_iff.2 (f.symm.domRestrict_le h)

/--
theorem `le_codRestrict` / 定理 `le_codRestrict`

English:
theorem le_codRestrict
  statement: (f g : M ≃ₚ[L] N) {A : L.Substructure N} (hf : f.cod <= A)
  proof: symm_le_iff.1 (le_domRestrict f.symm g.symm hf hg (monotone_symm hfg))

中文:
定理 le_codRestrict
  结论: (f g : M ≃ₚ[L] N) {A : L.子结构 N} (hf : f.cod <= A)
  证明: symm_le_iff.1 (le_domRestrict f.symm g.symm hf hg (monotone_symm hfg))

Depends on / 依赖: f.symm, g.symm, le_domRestrict, monotone_symm, symm_le_iff
-/
theorem le_codRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure N} (hf : f.cod <= A)
    (hg : A <= g.cod) (hfg : f <= g) : f <= g.codRestrict hg :=
  symm_le_iff.1 (le_domRestrict f.symm g.symm hf hg (monotone_symm hfg))

/--
Definition of `toEmbedding` / `toEmbedding` 的定义

English:
definition toEmbedding
  signature: (f : M ≃ₚ[L] N)
  body: (subtype _).comp f.toEquiv.toEmbedding

@[simp]

中文:
定义 toEmbedding
  签名: (f : M ≃ₚ[L] N)
  定义体: (subtype _).comp f.toEquiv.toEmbedding

@[simp]

Depends on / 依赖: f.toEquiv.toEmbedding, subtype, toEmbedding, toEquiv
-/
def toEmbedding (f : M ≃ₚ[L] N) : f.dom ↪[L] N :=
  (subtype _).comp f.toEquiv.toEmbedding

@[simp]
/--
theorem `toEmbedding_apply` / 定理 `toEmbedding_apply`

English:
theorem toEmbedding_apply
  given: {f : M ≃ₚ[L] N} (m : f.dom)
  proof: rfl

中文:
定理 toEmbedding_apply
  条件: {f : M ≃ₚ[L] N} (m : f.dom)
  证明: rfl
-/
theorem toEmbedding_apply {f : M ≃ₚ[L] N} (m : f.dom) :
    f.toEmbedding m = f.toEquiv m :=
  rfl

/--
Definition of `toEmbeddingOfEqTop` / `toEmbeddingOfEqTop` 的定义

English:
definition toEmbeddingOfEqTop
  signature: {f : M ≃ₚ[L] N} (h : f.dom = ⊤)
  body: (h ▸ f.toEmbedding).comp topEquiv.symm.toEmbedding

@[simp]

中文:
定义 toEmbeddingOfEqTop
  签名: {f : M ≃ₚ[L] N} (h : f.dom = ⊤)
  定义体: (h ▸ f.toEmbedding).comp topEquiv.symm.toEmbedding

@[simp]

Depends on / 依赖: f.toEmbedding, toEmbedding, topEquiv, topEquiv.symm.toEmbedding
-/
def toEmbeddingOfEqTop {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : M ↪[L] N :=
  (h ▸ f.toEmbedding).comp topEquiv.symm.toEmbedding

@[simp]
/--
theorem `toEmbeddingOfEqTop_apply` / 定理 `toEmbeddingOfEqTop_apply`

English:
theorem toEmbeddingOfEqTop_apply
  given: {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M)
  proof: by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

中文:
定理 toEmbeddingOfEqTop_apply
  条件: {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M)
  证明: by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl
-/
theorem toEmbeddingOfEqTop_apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) :
    toEmbeddingOfEqTop h m = f.toEquiv ⟨m, h.symm ▸ mem_top m⟩ := by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

set_option linter.style.nameCheck false in
/--
Definition of `toEquivOfEqTop` / `toEquivOfEqTop` 的定义

English:
definition toEquivOfEqTop
  signature: {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
  body: (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.toEquiv).comp (topEquiv (M := M)).symm)

@[simp]

中文:
定义 toEquivOfEqTop
  签名: {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
  定义体: (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.toEquiv).comp (topEquiv (M := M)).symm)

@[simp]

Depends on / 依赖: f.toEquiv, h_cod, h_dom, toEquiv, topEquiv
-/
def toEquivOfEqTop {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) : M ≃[L] N :=
  (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.toEquiv).comp (topEquiv (M := M)).symm)

@[simp]
/--
theorem `toEquivOfEqTop_toEmbedding` / 定理 `toEquivOfEqTop_toEmbedding`

English:
theorem toEquivOfEqTop_toEmbedding
  statement: {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
  proof: by
  rcases f with ⟨dom, cod, g⟩
  cases h_dom
  cases h_cod
  rfl

中文:
定理 toEquivOfEqTop_toEmbedding
  结论: {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
  证明: by
  rcases f with ⟨dom, cod, g⟩
  cases h_dom
  cases h_cod
  rfl

Depends on / 依赖: h_cod, h_dom
-/
theorem toEquivOfEqTop_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) :
    (toEquivOfEqTop h_dom h_cod).toEmbedding = toEmbeddingOfEqTop h_dom := by
  rcases f with ⟨dom, cod, g⟩
  cases h_dom
  cases h_cod
  rfl

/--
theorem `dom_fg_iff_cod_fg` / 定理 `dom_fg_iff_cod_fg`

English:
theorem dom_fg_iff_cod_fg
  given: {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N)
  proof: by
  rw [Substructure.fg_iff_structure_fg]; rw [f.toEquiv.fg_iff]; rw [Substructure.fg_iff_structure_fg]

中文:
定理 dom_fg_iff_cod_fg
  条件: {N : 类型} [L.结构 N] (f : M ≃ₚ[L] N)
  证明: by
  rw [Substructure.fg_iff_structure_fg]; rw [f.toEquiv.fg_iff]; rw [Substructure.fg_iff_structure_fg]

Depends on / 依赖: Substructure, Substructure.fg_iff_structure_fg, f.toEquiv.fg_iff, fg_iff, fg_iff_structure_fg, toEquiv
-/
theorem dom_fg_iff_cod_fg {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N) :
    f.dom.FG ↔ f.cod.FG := by
  rw [Substructure.fg_iff_structure_fg]; rw [f.toEquiv.fg_iff]; rw [Substructure.fg_iff_structure_fg]

end PartialEquiv

namespace Embedding

/--
Definition of `toPartialEquiv` / `toPartialEquiv` 的定义

English:
definition toPartialEquiv
  signature: (f : M ↪[L] N)
  body: ⟨⊤, f.toHom.range, f.equivRange.comp (Substructure.topEquiv)⟩

中文:
定义 toPartialEquiv
  签名: (f : M ↪[L] N)
  定义体: ⟨⊤, f.toHom.range, f.equivRange.comp (Substructure.topEquiv)⟩

Depends on / 依赖: Substructure, Substructure.topEquiv, equivRange, f.equivRange.comp, f.toHom.range, topEquiv
-/
noncomputable def toPartialEquiv (f : M ↪[L] N) : M ≃ₚ[L] N :=
  ⟨⊤, f.toHom.range, f.equivRange.comp (Substructure.topEquiv)⟩

/--
theorem `toPartialEquiv_injective` / 定理 `toPartialEquiv_injective`

English:
theorem toPartialEquiv_injective
  proof: by
  intro _ _ h
  ext
  rw [PartialEquiv.ext_iff] at h
  rcases h with ⟨_, H⟩
  exact H _ (Substructure.mem_top _)

@[simp]

中文:
定理 toPartialEquiv_injective
  证明: by
  intro _ _ h
  ext
  rw [PartialEquiv.ext_iff] at h
  rcases h with ⟨_, H⟩
  exact H _ (Substructure.mem_top _)

@[simp]

Depends on / 依赖: PartialEquiv, PartialEquiv.ext_iff, Substructure, Substructure.mem_top, ext_iff, mem_top
-/
theorem toPartialEquiv_injective :
    Function.Injective (fun f : M ↪[L] N => f.toPartialEquiv) := by
  intro _ _ h
  ext
  rw [PartialEquiv.ext_iff] at h
  rcases h with ⟨_, H⟩
  exact H _ (Substructure.mem_top _)

@[simp]
/--
theorem `toEmbedding_toPartialEquiv` / 定理 `toEmbedding_toPartialEquiv`

English:
theorem toEmbedding_toPartialEquiv
  given: (f : M ↪[L] N)
  proof: rfl

@[simp]

中文:
定理 toEmbedding_toPartialEquiv
  条件: (f : M ↪[L] N)
  证明: rfl

@[simp]

Depends on / 依赖: f.toPartialEquiv, toPartialEquiv
-/
theorem toEmbedding_toPartialEquiv (f : M ↪[L] N) :
    PartialEquiv.toEmbeddingOfEqTop (f := f.toPartialEquiv) rfl = f :=
  rfl

@[simp]
/--
theorem `toPartialEquiv_toEmbedding` / 定理 `toPartialEquiv_toEmbedding`

English:
theorem toPartialEquiv_toEmbedding
  given: {f : M ≃ₚ[L] N} (h : f.dom = ⊤)
  proof: by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

中文:
定理 toPartialEquiv_toEmbedding
  条件: {f : M ≃ₚ[L] N} (h : f.dom = ⊤)
  证明: by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

Depends on / 依赖: PartialEquiv, PartialEquiv.ext
-/
theorem toPartialEquiv_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) :
    (PartialEquiv.toEmbeddingOfEqTop h).toPartialEquiv = f := by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

end Embedding

namespace DirectLimit

open PartialEquiv

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (S : ι ->o M ≃ₚ[L] N)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem (fun i => (S i).dom)
  body: rfl
  map_map _ _ _ _ _ _ := rfl

中文:
实例 :
  签名: DirectedSystem (fun i => (S i).dom)
  定义体: rfl
  map_map _ _ _ _ _ _ := rfl
-/
instance : DirectedSystem (fun i => (S i).dom)
    (fun _ _ h => Substructure.inclusion (dom_le_dom (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectedSystem (fun i => (S i).cod)
  body: rfl
  map_map _ _ _ _ _ _ := rfl

中文:
实例 :
  签名: DirectedSystem (fun i => (S i).cod)
  定义体: rfl
  map_map _ _ _ _ _ _ := rfl
-/
instance : DirectedSystem (fun i => (S i).cod)
    (fun _ _ h => Substructure.inclusion (cod_le_cod (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/--
Definition of `partialEquivLimit` / `partialEquivLimit` 的定义

English:
definition partialEquivLimit
  signature: : M ≃ₚ[L] N where
  body: iSup (fun i => (S i).dom)
  cod := iSup (fun i => (S i).cod)
  toEquiv :=
    (Equiv_iSup {
      toFun := (fun i => (S i).cod)
      monotone' := monotone_cod.comp S.monotone }).comp
      ((DirectLimit.equiv_lift L ι (fun i => (S i).dom)
        (fun _ _ hij => Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i => (S i).cod)
        (fun _ _ hij => Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i => (S i).toEquiv)
        (fun _ _ hij _ => toEquiv_inclusion_apply (S.monotone hij) _)).comp
        (Equiv_iSup {
          toFun := (fun i => (S i).dom)
          monotone' := monotone_dom.comp S.monotone }).symm)

@[simp]

中文:
定义 partialEquivLimit
  签名: : M ≃ₚ[L] N where
  定义体: iSup (fun i => (S i).dom)
  cod := iSup (fun i => (S i).cod)
  toEquiv :=
    (Equiv_iSup {
      toFun := (fun i => (S i).cod)
      monotone' := monotone_cod.comp S.monotone }).comp
      ((DirectLimit.equiv_lift L ι (fun i => (S i).dom)
        (fun _ _ hij => Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i => (S i).cod)
        (fun _ _ hij => Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i => (S i).toEquiv)
        (fun _ _ hij _ => toEquiv_inclusion_apply (S.monotone hij) _)).comp
        (Equiv_iSup {
          toFun := (fun i => (S i).dom)
          monotone' := monotone_dom.comp S.monotone }).symm)

@[simp]
-/
noncomputable def partialEquivLimit : M ≃ₚ[L] N where
  dom := iSup (fun i => (S i).dom)
  cod := iSup (fun i => (S i).cod)
  toEquiv :=
    (Equiv_iSup {
      toFun := (fun i => (S i).cod)
      monotone' := monotone_cod.comp S.monotone }).comp
      ((DirectLimit.equiv_lift L ι (fun i => (S i).dom)
        (fun _ _ hij => Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i => (S i).cod)
        (fun _ _ hij => Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i => (S i).toEquiv)
        (fun _ _ hij _ => toEquiv_inclusion_apply (S.monotone hij) _)).comp
        (Equiv_iSup {
          toFun := (fun i => (S i).dom)
          monotone' := monotone_dom.comp S.monotone }).symm)

@[simp]
/--
theorem `dom_partialEquivLimit` / 定理 `dom_partialEquivLimit`

English:
theorem dom_partialEquivLimit
  statement: (partialEquivLimit S).dom = iSup (fun x => (S x).dom)
  proof: rfl

@[simp]

中文:
定理 dom_partialEquivLimit
  结论: (partialEquivLimit S).dom = iSup (fun x => (S x).dom)
  证明: rfl

@[simp]
-/
theorem dom_partialEquivLimit : (partialEquivLimit S).dom = iSup (fun x => (S x).dom) := rfl

@[simp]
/--
theorem `cod_partialEquivLimit` / 定理 `cod_partialEquivLimit`

English:
theorem cod_partialEquivLimit
  statement: (partialEquivLimit S).cod = iSup (fun x => (S x).cod)
  proof: rfl

中文:
定理 cod_partialEquivLimit
  结论: (partialEquivLimit S).cod = iSup (fun x => (S x).cod)
  证明: rfl
-/
theorem cod_partialEquivLimit : (partialEquivLimit S).cod = iSup (fun x => (S x).cod) := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `partialEquivLimit_comp_inclusion` / 引理 `partialEquivLimit_comp_inclusion`

English:
lemma partialEquivLimit_comp_inclusion
  given: {i : ι}
  proof: by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_isup_symm_inclusion]
  congr

中文:
引理 partialEquivLimit_comp_inclusion
  条件: {i : ι}
  证明: by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_isup_symm_inclusion]
  congr

Depends on / 依赖: Embedding, Embedding.comp_assoc, Equiv.comp_toEmbedding, Equiv_isup_symm_inclusion, comp_assoc, comp_toEmbedding, partialEquivLimit
-/
lemma partialEquivLimit_comp_inclusion {i : ι} :
    (partialEquivLimit S).toEquiv.toEmbedding.comp (Substructure.inclusion (le_iSup _ i)) =
    (Substructure.inclusion (le_iSup _ i)).comp (S i).toEquiv.toEmbedding := by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_isup_symm_inclusion]
  congr

set_option backward.isDefEq.respectTransparency false in
/--
theorem `le_partialEquivLimit` / 定理 `le_partialEquivLimit`

English:
theorem le_partialEquivLimit
  given: (i : ι)
  statement: S i <= partialEquivLimit S
  proof: ⟨le_iSup (f := fun i => (S i).dom) _, by
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
    these two `simp` calls cannot be combined. -/
    simp only [partialEquivLimit_comp_inclusion]
    simp only [cod_partialEquivLimit, ← Embedding.comp_assoc,
      subtype_comp_inclusion]⟩

中文:
定理 le_partialEquivLimit
  条件: (i : ι)
  结论: S i <= partialEquivLimit S
  证明: ⟨le_iSup (f := fun i => (S i).dom) _, by
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
    these two `simp` calls cannot be combined. -/
    simp only [partialEquivLimit_comp_inclusion]
    simp only [cod_partialEquivLimit, ← Embedding.comp_assoc,
      subtype_comp_inclusion]⟩

Depends on / 依赖: Embedding, Embedding.comp_assoc, adaptation_note, cannot, cod_partialEquivLimit, combined, comp_assoc, github, github.com, le_iSup, leanprover, partialEquivLimit_comp_inclusion, subtype_comp_inclusion
-/
theorem le_partialEquivLimit (i : ι) : S i <= partialEquivLimit S :=
  ⟨le_iSup (f := fun i => (S i).dom) _, by
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
    these two `simp` calls cannot be combined. -/
    simp only [partialEquivLimit_comp_inclusion]
    simp only [cod_partialEquivLimit, ← Embedding.comp_assoc,
      subtype_comp_inclusion]⟩

end DirectLimit

section FGEquiv

open PartialEquiv Set Language.DirectLimit

variable (M) (N) (L)

/--
Definition of `FGEquiv` / `FGEquiv` 的定义

English:
abbreviation FGEquiv
  body: {f : M ≃ₚ[L] N // f.dom.FG}

中文:
缩写 FGEquiv
  定义体: {f : M ≃ₚ[L] N // f.dom.FG}

Depends on / 依赖: f.dom.FG
-/
abbrev FGEquiv := {f : M ≃ₚ[L] N // f.dom.FG}

/--
Definition of `IsExtensionPair` / `IsExtensionPair` 的定义

English:
definition IsExtensionPair
  signature: : Prop
  body: forall (f : L.FGEquiv M N) (m : M), exists g, m in g.1.dom ∧ f <= g

中文:
定义 IsExtensionPair
  签名: : 命题
  定义体: forall (f : L.FGEquiv M N) (m : M), exists g, m in g.1.dom ∧ f <= g

Depends on / 依赖: FGEquiv, L.FGEquiv
-/
def IsExtensionPair : Prop := forall (f : L.FGEquiv M N) (m : M), exists g, m in g.1.dom ∧ f <= g

variable {M N L}

/--
theorem `countable_self_fgequiv_of_countable` / 定理 `countable_self_fgequiv_of_countable`

English:
theorem countable_self_fgequiv_of_countable
  given: [Countable M]
  proof: by
  let g : L.FGEquiv M M ->
      Σ U : { S : L.Substructure M // S.FG }, U.val ->[L] M :=
    fun f => ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.toEquiv.toHom⟩
  have g_inj : Function.Injective g := by
    intro f f' h
    ext
    let ⟨⟨dom_f, cod_f, equiv_f⟩, f_fin⟩ := f
    cases congr_arg (·.1) h
    apply PartialEquiv.ext (by rfl)
    simp only [g, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact fun x hx => congr_fun (congr_arg (↑) h) ⟨x, hx⟩
  have : forall U : { S : L.Substructure M // S.FG }, Structure.FG L U.val :=
    fun U => (U.val.fg_iff_structure_fg.1 U.prop)
  exact Function.Embedding.countable ⟨g, g_inj⟩

中文:
定理 countable_self_fgequiv_of_countable
  条件: [可数 M]
  证明: by
  let g : L.FGEquiv M M ->
      Σ U : { S : L.Substructure M // S.FG }, U.val ->[L] M :=
    fun f => ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.toEquiv.toHom⟩
  have g_inj : Function.Injective g := by
    intro f f' h
    ext
    let ⟨⟨dom_f, cod_f, equiv_f⟩, f_fin⟩ := f
    cases congr_arg (·.1) h
    apply PartialEquiv.ext (by rfl)
    simp only [g, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact fun x hx => congr_fun (congr_arg (↑) h) ⟨x, hx⟩
  have : forall U : { S : L.Substructure M // S.FG }, Structure.FG L U.val :=
    fun U => (U.val.fg_iff_structure_fg.1 U.prop)
  exact Function.Embedding.countable ⟨g, g_inj⟩

Depends on / 依赖: FGEquiv, Function, Function.Injective, Injective, L.FGEquiv, L.Substructure, PartialEquiv, PartialEquiv.ext, S.FG, Sigma.mk.inj_iff, Structure, Structure.FG, Substructure, U.val, cod_f, congr_arg, congr_fun, dom_f, equiv_f, f.prop
-/
theorem countable_self_fgequiv_of_countable [Countable M] :
    Countable (L.FGEquiv M M) := by
  let g : L.FGEquiv M M ->
      Σ U : { S : L.Substructure M // S.FG }, U.val ->[L] M :=
    fun f => ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.toEquiv.toHom⟩
  have g_inj : Function.Injective g := by
    intro f f' h
    ext
    let ⟨⟨dom_f, cod_f, equiv_f⟩, f_fin⟩ := f
    cases congr_arg (·.1) h
    apply PartialEquiv.ext (by rfl)
    simp only [g, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact fun x hx => congr_fun (congr_arg (↑) h) ⟨x, hx⟩
  have : forall U : { S : L.Substructure M // S.FG }, Structure.FG L U.val :=
    fun U => (U.val.fg_iff_structure_fg.1 U.prop)
  exact Function.Embedding.countable ⟨g, g_inj⟩

/--
Instance `inhabited_self_FGEquiv` / 实例 `inhabited_self_FGEquiv`

English:
instance inhabited_self_FGEquiv
  signature: : Inhabited (L.FGEquiv M M)
  body: ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩

中文:
实例 inhabited_self_FGEquiv
  签名: : 可居 (L.FGEquiv M M)
  定义体: ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩

Depends on / 依赖: Equiv.refl, L.Substructure, Substructure, fg_bot
-/
instance inhabited_self_FGEquiv : Inhabited (L.FGEquiv M M) :=
  ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩

/--
Instance `inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations` / 实例 `inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations`

English:
instance inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations
  body: ⟨⟨⟨⊥, ⊥, {
      toFun := isEmptyElim
      invFun := isEmptyElim
      left_inv := isEmptyElim
      right_inv := isEmptyElim
      map_fun' := fun {n} f x => by
        subsingleton
      map_rel' := fun {n} r x => by
        cases n
        · exact isEmptyElim r
        · exact isEmptyElim (x 0)
    }⟩, fg_bot⟩⟩

中文:
实例 inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations
  定义体: ⟨⟨⟨⊥, ⊥, {
      toFun := isEmptyElim
      invFun := isEmptyElim
      left_inv := isEmptyElim
      right_inv := isEmptyElim
      map_fun' := fun {n} f x => by
        subsingleton
      map_rel' := fun {n} r x => by
        cases n
        · exact isEmptyElim r
        · exact isEmptyElim (x 0)
    }⟩, fg_bot⟩⟩

Depends on / 依赖: fg_bot, invFun, isEmptyElim, left_inv, map_fun, map_rel, right_inv, subsingleton
-/
instance inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations
    [IsEmpty L.Constants] [IsEmpty (L.Relations 0)] : Inhabited (L.FGEquiv M N) :=
  ⟨⟨⟨⊥, ⊥, {
      toFun := isEmptyElim
      invFun := isEmptyElim
      left_inv := isEmptyElim
      right_inv := isEmptyElim
      map_fun' := fun {n} f x => by
        subsingleton
      map_rel' := fun {n} r x => by
        cases n
        · exact isEmptyElim r
        · exact isEmptyElim (x 0)
    }⟩, fg_bot⟩⟩

/-- Maps to the symmetric finitely-generated partial equivalence. -/
@[simps]
/--
Definition of `FGEquiv.symm` / `FGEquiv.symm` 的定义

English:
definition FGEquiv.symm
  signature: (f : L.FGEquiv M N)
  body: ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩

中文:
定义 FGEquiv.symm
  签名: (f : L.FGEquiv M N)
  定义体: ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩

Depends on / 依赖: dom_fg_iff_cod_fg
-/
def FGEquiv.symm (f : L.FGEquiv M N) : L.FGEquiv N M := ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩

/--
lemma `isExtensionPair_iff_cod` / 引理 `isExtensionPair_iff_cod`

English:
lemma isExtensionPair_iff_cod
  statement: L.IsExtensionPair M N ↔
  proof: by
  refine Iff.intro ?_ ?_ <;>
  · intro h f m
    obtain ⟨g, h1, h2⟩ := h f.symm m
    exact ⟨g.symm, h1, monotone_symm h2⟩

中文:
引理 isExtensionPair_iff_cod
  结论: L.IsExtensionPair M N ↔
  证明: by
  refine Iff.intro ?_ ?_ <;>
  · intro h f m
    obtain ⟨g, h1, h2⟩ := h f.symm m
    exact ⟨g.symm, h1, monotone_symm h2⟩

Depends on / 依赖: Iff.intro, f.symm, g.symm, monotone_symm
-/
lemma isExtensionPair_iff_cod : L.IsExtensionPair M N ↔
    forall (f : L.FGEquiv N M) (m : M), exists g, m in g.1.cod ∧ f <= g := by
  refine Iff.intro ?_ ?_ <;>
  · intro h f m
    obtain ⟨g, h1, h2⟩ := h f.symm m
    exact ⟨g.symm, h1, monotone_symm h2⟩

/--
theorem `isExtensionPair_iff_exists_embedding_closure_singleton_sup` / 定理 `isExtensionPair_iff_exists_embedding_closure_singleton_sup`

English:
theorem isExtensionPair_iff_exists_embedding_closure_singleton_sup
  proof: by
  refine ⟨fun h S S_FG f m => ?_, fun h ⟨f, f_FG⟩ m => ?_⟩
  · obtain ⟨⟨f', hf'⟩, mf', ff'1, ff'2⟩ := h ⟨⟨S, _, f.equivRange⟩, S_FG⟩ m
    refine ⟨f'.toEmbedding.comp (Substructure.inclusion ?_), ?_⟩
    · simp only [sup_le_iff, ff'1, closure_le, singleton_subset_iff, SetLike.mem_coe, mf',
        and_self]
    · ext ⟨x, hx⟩
      rw [Embedding.subtype_equivRange] at ff'2
      simp only [← ff'2, Embedding.comp_apply, Substructure.coe_inclusion,
        Equiv.coe_toEmbedding, coe_subtype, PartialEquiv.toEmbedding_apply]
  · obtain ⟨f', eq_f'⟩ := h f.dom f_FG f.toEmbedding m
    refine ⟨⟨⟨closure L {m} ⊔ f.dom, f'.toHom.range, f'.equivRange⟩,
      (fg_closure_singleton _).sup f_FG⟩,
      subset_closure.trans (le_sup_left : (closure L) {m} <= _) (mem_singleton m),
      ⟨le_sup_right, Embedding.ext (fun _ => ?_)⟩⟩
    rw [PartialEquiv.toEmbedding] at eq_f'
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
      Embedding.equivRange_apply, eq_f']

中文:
定理 isExtensionPair_iff_存在_embedding_closure_singleton_sup
  证明: by
  refine ⟨fun h S S_FG f m => ?_, fun h ⟨f, f_FG⟩ m => ?_⟩
  · obtain ⟨⟨f', hf'⟩, mf', ff'1, ff'2⟩ := h ⟨⟨S, _, f.equivRange⟩, S_FG⟩ m
    refine ⟨f'.toEmbedding.comp (Substructure.inclusion ?_), ?_⟩
    · simp only [sup_le_iff, ff'1, closure_le, singleton_subset_iff, SetLike.mem_coe, mf',
        and_self]
    · ext ⟨x, hx⟩
      rw [Embedding.subtype_equivRange] at ff'2
      simp only [← ff'2, Embedding.comp_apply, Substructure.coe_inclusion,
        Equiv.coe_toEmbedding, coe_subtype, PartialEquiv.toEmbedding_apply]
  · obtain ⟨f', eq_f'⟩ := h f.dom f_FG f.toEmbedding m
    refine ⟨⟨⟨closure L {m} ⊔ f.dom, f'.toHom.range, f'.equivRange⟩,
      (fg_closure_singleton _).sup f_FG⟩,
      subset_closure.trans (le_sup_left : (closure L) {m} <= _) (mem_singleton m),
      ⟨le_sup_right, Embedding.ext (fun _ => ?_)⟩⟩
    rw [PartialEquiv.toEmbedding] at eq_f'
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
      Embedding.equivRange_apply, eq_f']

Depends on / 依赖: Embedding, Embedding.comp_apply, Embedding.subtype_equivRange, Equiv.coe_toEmbedding, PartialEquiv, PartialEquiv.toEmbedding_apply, S_FG, SetLike, SetLike.mem_coe, Substructure, Substructure.coe_inclusion, Substructure.inclusion, and_self, closure_le, coe_inclusion, coe_subtype, coe_toEmbedding, comp_apply, equivRange, f.equivRange
-/
theorem isExtensionPair_iff_exists_embedding_closure_singleton_sup :
    L.IsExtensionPair M N ↔
    forall (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] N) (m : M),
      exists g : (closure L {m} ⊔ S : L.Substructure M) ↪[L] N, f =
        g.comp (Substructure.inclusion le_sup_right) := by
  refine ⟨fun h S S_FG f m => ?_, fun h ⟨f, f_FG⟩ m => ?_⟩
  · obtain ⟨⟨f', hf'⟩, mf', ff'1, ff'2⟩ := h ⟨⟨S, _, f.equivRange⟩, S_FG⟩ m
    refine ⟨f'.toEmbedding.comp (Substructure.inclusion ?_), ?_⟩
    · simp only [sup_le_iff, ff'1, closure_le, singleton_subset_iff, SetLike.mem_coe, mf',
        and_self]
    · ext ⟨x, hx⟩
      rw [Embedding.subtype_equivRange] at ff'2
      simp only [← ff'2, Embedding.comp_apply, Substructure.coe_inclusion,
        Equiv.coe_toEmbedding, coe_subtype, PartialEquiv.toEmbedding_apply]
  · obtain ⟨f', eq_f'⟩ := h f.dom f_FG f.toEmbedding m
    refine ⟨⟨⟨closure L {m} ⊔ f.dom, f'.toHom.range, f'.equivRange⟩,
      (fg_closure_singleton _).sup f_FG⟩,
      subset_closure.trans (le_sup_left : (closure L) {m} <= _) (mem_singleton m),
      ⟨le_sup_right, Embedding.ext (fun _ => ?_)⟩⟩
    rw [PartialEquiv.toEmbedding] at eq_f'
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
      Embedding.equivRange_apply, eq_f']

namespace IsExtensionPair

protected alias ⟨cod, _⟩ := isExtensionPair_iff_cod

/--
Definition of `definedAtLeft` / `definedAtLeft` 的定义

English:
definition definedAtLeft
  body: {f | m in f.val.dom}
  isCofinal := fun f => h f m

中文:
定义 definedAtLeft
  定义体: {f | m in f.val.dom}
  isCofinal := fun f => h f m

Depends on / 依赖: f.val.dom
-/
def definedAtLeft
    (h : L.IsExtensionPair M N) (m : M) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | m in f.val.dom}
  isCofinal := fun f => h f m

/--
Definition of `definedAtRight` / `definedAtRight` 的定义

English:
definition definedAtRight
  body: {f | n in f.val.cod}
  isCofinal := fun f => h.cod f n

中文:
定义 definedAtRight
  定义体: {f | n in f.val.cod}
  isCofinal := fun f => h.cod f n

Depends on / 依赖: f.val.cod
-/
def definedAtRight
    (h : L.IsExtensionPair N M) (n : N) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | n in f.val.cod}
  isCofinal := fun f => h.cod f n

end IsExtensionPair

/--
theorem `embedding_from_cg` / 定理 `embedding_from_cg`

English:
theorem embedding_from_cg
  statement: (M_cg : Structure.CG L M) (g : L.FGEquiv M N)
  proof: by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X -> Order.Cofinal (FGEquiv L M N) := fun x => H.definedAtLeft x
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨toEmbeddingOfEqTop isTop,
        by convert! (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

中文:
定理 embedding_from_cg
  结论: (M_cg : 结构.CG L M) (g : L.FGEquiv M N)
  证明: by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X -> Order.Cofinal (FGEquiv L M N) := fun x => H.definedAtLeft x
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨toEmbeddingOfEqTop isTop,
        by convert! (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

Depends on / 依赖: Cofinal, Countable, DirectLimit, DirectLimit.partialEquivLimit, Encodable, Encodable.ofCountable, F.dom, FGEquiv, H.definedAtLeft, M_cg, Order.Cofinal, Order.sequenceOfCofinals, Order.sequenceOfCofinals.enc, Order.sequenceOfCofinals.monotone, Subtype, Subtype.mono_coe, Subtype.val, X_gen, countable_coe_iff, definedAtLeft
-/
theorem embedding_from_cg (M_cg : Structure.CG L M) (g : L.FGEquiv M N)
    (H : L.IsExtensionPair M N) :
    exists f : M ↪[L] N, g <= f.toPartialEquiv := by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X -> Order.Cofinal (FGEquiv L M N) := fun x => H.definedAtLeft x
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨toEmbeddingOfEqTop isTop,
        by convert! (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

/--
theorem `equiv_between_cg` / 定理 `equiv_between_cg`

English:
theorem equiv_between_cg
  statement: (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
  proof: by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y -> Order.Cofinal (FGEquiv L M N) := fun p =>
    Sum.recOn p (fun x => ext_dom.definedAtLeft x) (fun y => ext_cod.definedAtRight y)
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ Nat _ _ _ S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y subseteq F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨toEquivOfEqTop dom_top cod_top, ?_⟩
  convert! le_partialEquivLimit S 0
  rw [toEquivOfEqTop_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

中文:
定理 equiv_between_cg
  结论: (M_cg : 结构.CG L M) (N_cg : 结构.CG L N)
  证明: by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y -> Order.Cofinal (FGEquiv L M N) := fun p =>
    Sum.recOn p (fun x => ext_dom.definedAtLeft x) (fun y => ext_cod.definedAtRight y)
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ Nat _ _ _ S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y subseteq F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨toEquivOfEqTop dom_top cod_top, ?_⟩
  convert! le_partialEquivLimit S 0
  rw [toEquivOfEqTop_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

Depends on / 依赖: Cofinal, Countable, Encodable, Encodable.ofCountable, FGEquiv, M_cg, N_cg, Order.Cofinal, Sum.recOn, X_count, X_gen, Y_count, Y_gen, countable_coe_iff, definedAtLeft, definedAtRight, ext_cod, ext_cod.definedAtRight, ext_dom, ext_dom.definedAtLeft
-/
theorem equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
    (g : L.FGEquiv M N)
    (ext_dom : L.IsExtensionPair M N)
    (ext_cod : L.IsExtensionPair N M) :
    exists f : M ≃[L] N, g <= f.toEmbedding.toPartialEquiv := by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y -> Order.Cofinal (FGEquiv L M N) := fun p =>
    Sum.recOn p (fun x => ext_dom.definedAtLeft x) (fun y => ext_cod.definedAtRight y)
  let S : Nat ->o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ Nat _ _ _ S
  have _ : X subseteq F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y subseteq F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨toEquivOfEqTop dom_top cod_top, ?_⟩
  convert! le_partialEquivLimit S 0
  rw [toEquivOfEqTop_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

end FGEquiv

end Language

end FirstOrder
