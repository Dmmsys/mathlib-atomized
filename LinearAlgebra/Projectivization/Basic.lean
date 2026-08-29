/-
Copyright (c) 2022 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!

# Projective Spaces

This file contains the definition of the projectivization of a vector space over a field,
as well as the bijection between said projectivization and the collection of all one
dimensional subspaces of the vector space.

## Notation
`ℙ K V` is localized notation for `Projectivization K V`, the projectivization of a `K`-vector
space `V`.

## Constructing terms of `ℙ K V`.
We have three ways to construct terms of `ℙ K V`:
- `Projectivization.mk K v hv` where `v : V` and `hv : v ≠ 0`.
- `Projectivization.mk' K v` where `v : { w : V // w ≠ 0 }`.
- `Projectivization.mk'' H h` where `H : Submodule K V` and `h : finrank H = 1`.

## Other definitions
- For `v : ℙ K V`, `v.submodule` gives the corresponding submodule of `V`.
- `Projectivization.equivSubmodule` is the equivalence between `ℙ K V`
  and `{ H : Submodule K V // finrank H = 1 }`.
- For `v : ℙ K V`, `v.rep : V` is a representative of `v`.

-/

@[expose] public section

variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

/-- The setoid whose quotient is the projectivization of `V`. -/
@[instance_reducible]
/--
Definition of `projectivizationSetoid` / `projectivizationSetoid` 的定义

English:
definition projectivizationSetoid
  signature: : Setoid { v : V // v != 0 }
  body: (MulAction.orbitRel Kˣ V).comap (↑)

中文:
定义 projectivizationSetoid
  签名: : 集合等价关系 { v : V // v != 0 }
  定义体: (MulAction.orbitRel Kˣ V).comap (↑)

Depends on / 依赖: MulAction, MulAction.orbitRel, orbitRel
-/
def projectivizationSetoid : Setoid { v : V // v != 0 } :=
  (MulAction.orbitRel Kˣ V).comap (↑)

/--
Definition of `Projectivization` / `Projectivization` 的定义

English:
definition Projectivization
  body: Quotient (projectivizationSetoid K V)

中文:
定义 Projectivization
  定义体: Quotient (projectivizationSetoid K V)

Depends on / 依赖: Quotient, projectivizationSetoid
-/
def Projectivization := Quotient (projectivizationSetoid K V)

/-- We define notations `ℙ K V` for the projectivization of the `K`-vector space `V`. -/
scoped[LinearAlgebra.Projectivization] notation "ℙ" => Projectivization

namespace Projectivization

open scoped LinearAlgebra.Projectivization

variable {V}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (v : V) (hv : v != 0)
  body: Quotient.mk'' ⟨v, hv⟩

中文:
定义 mk
  签名: (v : V) (hv : v != 0)
  定义体: Quotient.mk'' ⟨v, hv⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk (v : V) (hv : v != 0) : ℙ K V :=
  Quotient.mk'' ⟨v, hv⟩

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: (v : { v : V // v != 0 })
  body: Quotient.mk'' v

@[simp]

中文:
定义 mk'
  签名: (v : { v : V // v != 0 })
  定义体: Quotient.mk'' v

@[simp]

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk' (v : { v : V // v != 0 }) : ℙ K V :=
  Quotient.mk'' v

@[simp]
/--
theorem `mk'_eq_mk` / 定理 `mk'_eq_mk`

English:
theorem mk'_eq_mk
  given: (v : { v : V // v != 0 })
  statement: mk' K v = mk K ↑v v.2
  proof: rfl

中文:
定理 mk'_eq_mk
  条件: (v : { v : V // v != 0 })
  结论: mk' K v = mk K ↑v v.2
  证明: rfl
-/
theorem mk'_eq_mk (v : { v : V // v != 0 }) : mk' K v = mk K ↑v v.2 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: V] : Nonempty (ℙ K V)
  body: let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

中文:
实例 [非平凡
  签名: V] : 非空 (ℙ K V)
  定义体: let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

Depends on / 依赖: InnerRegularCompactLTTop, IsFiniteMeasure, exists_ne
-/
instance [Nontrivial V] : Nonempty (ℙ K V) :=
  let ⟨v, hv⟩ := exists_ne (0 : V)
  ⟨mk K v hv⟩

variable {K}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: {α : Type*} (f : { v : V // v != 0 } -> α)
  body: Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x

@[simp]

中文:
定义 lift
  签名: {α : 类型} (f : { v : V // v != 0 } -> α)
  定义体: Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x

@[simp]

Depends on / 依赖: BorelSpace, InnerRegularCompactLTTop, R1Space
-/
protected def lift {α : Type*} (f : { v : V // v != 0 } -> α)
    (hf : forall (a b : { v : V // v != 0 }) (t : K), a = t • (b : V) -> f a = f b)
    (x : ℙ K V) : α :=
  Quotient.lift f (by rintro ⟨-, hv⟩ ⟨w, hw⟩ ⟨⟨t, -⟩, rfl⟩; exact hf ⟨_, hv⟩ ⟨w, hw⟩ t rfl) x

@[simp]
/--
lemma `lift_mk` / 引理 `lift_mk`

English:
lemma lift_mk
  statement: {α : Type*} (f : { v : V // v != 0 } -> α)
  proof: rfl

中文:
引理 lift_mk
  结论: {α : 类型} (f : { v : V // v != 0 } -> α)
  证明: rfl

Depends on / 依赖: BorelSpace, InnerRegularCompactLTTop, R1Space
-/
protected lemma lift_mk {α : Type*} (f : { v : V // v != 0 } -> α)
    (hf : forall (a b : { v : V // v != 0 }) (t : K), a = t • (b : V) -> f a = f b)
    (v : V) (hv : v != 0) :
    Projectivization.lift f hf (mk K v hv) = f ⟨v, hv⟩ :=
  rfl

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def rep (v : ℙ K V)
  body: v.out

中文:
定义 noncomputable
  签名: def rep (v : ℙ K V)
  定义体: v.out
-/
protected noncomputable def rep (v : ℙ K V) : V :=
  v.out

/--
theorem `rep_nonzero` / 定理 `rep_nonzero`

English:
theorem rep_nonzero
  given: (v : ℙ K V)
  statement: v.rep != 0
  proof: v.out.2

@[simp]

中文:
定理 rep_nonzero
  条件: (v : ℙ K V)
  结论: v.rep != 0
  证明: v.out.2

@[simp]

Depends on / 依赖: v.out
-/
theorem rep_nonzero (v : ℙ K V) : v.rep != 0 :=
  v.out.2

@[simp]
/--
theorem `mk_rep` / 定理 `mk_rep`

English:
theorem mk_rep
  given: (v : ℙ K V)
  statement: mk K v.rep v.rep_nonzero = v
  proof: Quotient.out_eq' _

中文:
定理 mk_rep
  条件: (v : ℙ K V)
  结论: mk K v.rep v.rep_nonzero = v
  证明: Quotient.out_eq' _

Depends on / 依赖: InnerRegular, InnerRegularCompactLTTop, Quotient, Quotient.out_eq, SigmaFinite, out_eq
-/
theorem mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero = v := Quotient.out_eq' _

open Module

/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: (v : ℙ K V)
  body: (Quotient.liftOn' v fun v => K ∙ (v : V)) by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _

中文:
定义 submodule
  签名: (v : ℙ K V)
  定义体: (Quotient.liftOn' v fun v => K ∙ (v : V)) by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _
-/
protected def submodule (v : ℙ K V) : Submodule K V :=
(Quotient.liftOn' v fun v => K ∙ (v : V)) by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨x, rfl : x • b = a⟩
    exact Submodule.span_singleton_group_smul_eq _ x _

variable (K)

/--
theorem `mk_eq_mk_iff` / 定理 `mk_eq_mk_iff`

English:
theorem mk_eq_mk_iff
  given: (v w : V) (hv : v != 0) (hw : w != 0)
  proof: Quotient.eq''

中文:
定理 mk_eq_mk_iff
  条件: (v w : V) (hv : v != 0) (hw : w != 0)
  证明: Quotient.eq''

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq_mk_iff (v w : V) (hv : v != 0) (hw : w != 0) :
    mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v :=
  Quotient.eq''

/--
theorem `mk_eq_mk_iff'` / 定理 `mk_eq_mk_iff'`

English:
theorem mk_eq_mk_iff'
  given: (v w : V) (hv : v != 0) (hw : w != 0)
  proof: by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha

中文:
定理 mk_eq_mk_iff'
  条件: (v w : V) (hv : v != 0) (hw : w != 0)
  证明: by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha

Depends on / 依赖: Units.mk0, hv.symm, mk_eq_mk_iff, zero_smul
-/
theorem mk_eq_mk_iff' (v w : V) (hv : v != 0) (hw : w != 0) :
    mk K v hv = mk K w hw ↔ exists a : K, a • w = v := by
  rw [mk_eq_mk_iff K v w hv hw]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨Units.mk0 a fun c => hv.symm ?_, ha⟩
    rwa [c, zero_smul] at ha

/--
theorem `exists_smul_eq_mk_rep` / 定理 `exists_smul_eq_mk_rep`

English:
theorem exists_smul_eq_mk_rep
  given: (v : V) (hv : v != 0)
  statement: exists a : Kˣ, a • v = (mk K v hv).rep
  proof: (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)

中文:
定理 存在_smul_eq_mk_rep
  条件: (v : V) (hv : v != 0)
  结论: 存在 a : Kˣ, a • v = (mk K v hv).rep
  证明: (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)

Depends on / 依赖: mk_eq_mk_iff, mk_rep, rep_nonzero
-/
theorem exists_smul_eq_mk_rep (v : V) (hv : v != 0) : exists a : Kˣ, a • v = (mk K v hv).rep :=
  (mk_eq_mk_iff K _ _ (rep_nonzero _) hv).1 (mk_rep _)

variable {K}

/-- An induction principle for `Projectivization`. Use as `induction v`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {P : ℙ K V -> Prop} (h : forall (v : V) (h : v != 0), P (mk K v h))
  statement: forall p, P p
  proof: Quotient.ind' Subtype.rec h

@[simp]

中文:
定理 ind
  条件: {P : ℙ K V -> 命题} (h : 对任意 (v : V) (h : v != 0), P (mk K v h))
  结论: 对任意 p, P p
  证明: Quotient.ind' Subtype.rec h

@[simp]

Depends on / 依赖: Quotient, Quotient.ind, Subtype, Subtype.rec
-/
theorem ind {P : ℙ K V -> Prop} (h : forall (v : V) (h : v != 0), P (mk K v h)) : forall p, P p :=
Quotient.ind' Subtype.rec h

@[simp]
/--
theorem `submodule_mk` / 定理 `submodule_mk`

English:
theorem submodule_mk
  given: (v : V) (hv : v != 0)
  statement: (mk K v hv).submodule = K ∙ v
  proof: rfl

中文:
定理 submodule_mk
  条件: (v : V) (hv : v != 0)
  结论: (mk K v hv).submodule = K ∙ v
  证明: rfl
-/
theorem submodule_mk (v : V) (hv : v != 0) : (mk K v hv).submodule = K ∙ v :=
  rfl

/--
theorem `submodule_eq` / 定理 `submodule_eq`

English:
theorem submodule_eq
  given: (v : ℙ K V)
  statement: v.submodule = K ∙ v.rep
  proof: by
  conv_lhs => rw [← v.mk_rep]
  rfl

中文:
定理 submodule_eq
  条件: (v : ℙ K V)
  结论: v.submodule = K ∙ v.rep
  证明: by
  conv_lhs => rw [← v.mk_rep]
  rfl

Depends on / 依赖: conv_lhs, mk_rep, v.mk_rep
-/
theorem submodule_eq (v : ℙ K V) : v.submodule = K ∙ v.rep := by
  conv_lhs => rw [← v.mk_rep]
  rfl

/--
theorem `finrank_submodule` / 定理 `finrank_submodule`

English:
theorem finrank_submodule
  given: (v : ℙ K V)
  statement: finrank K v.submodule = 1
  proof: by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero

中文:
定理 finrank_submodule
  条件: (v : ℙ K V)
  结论: finrank K v.submodule = 1
  证明: by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero

Depends on / 依赖: finrank_span_singleton, rep_nonzero, submodule_eq, v.rep_nonzero
-/
theorem finrank_submodule (v : ℙ K V) : finrank K v.submodule = 1 := by
  rw [submodule_eq]
  exact finrank_span_singleton v.rep_nonzero

instance (v : ℙ K V) : FiniteDimensional K v.submodule := by
  rw [← v.mk_rep]
  change FiniteDimensional K (K ∙ v.rep)
  infer_instance

/--
theorem `submodule_injective` / 定理 `submodule_injective`

English:
theorem submodule_injective
  proof: fun u v h => by
  induction u using ind with | h u hu =>
  induction v using ind with | h v hv =>
  rw [submodule_mk]; rw [submodule_mk]; rw [Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm

中文:
定理 submodule_injective
  证明: fun u v h => by
  induction u using ind with | h u hu =>
  induction v using ind with | h v hv =>
  rw [submodule_mk]; rw [submodule_mk]; rw [Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm

Depends on / 依赖: Submodule, Submodule.span_singleton_eq_span_singleton, mk_eq_mk_iff, span_singleton_eq_span_singleton, submodule_mk
-/
theorem submodule_injective :
    Function.Injective (Projectivization.submodule : ℙ K V -> Submodule K V) := fun u v h => by
  induction u using ind with | h u hu =>
  induction v using ind with | h v hv =>
  rw [submodule_mk]; rw [submodule_mk]; rw [Submodule.span_singleton_eq_span_singleton] at h
  exact ((mk_eq_mk_iff K v u hv hu).2 h).symm

variable (K V)

/--
Definition of `equivSubmodule` / `equivSubmodule` 的定义

English:
definition equivSubmodule
  signature: : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 }
  body: (Equiv.ofInjective _ submodule_injective).trans .subtypeEquiv (.refl _) fun H => by
    refine ⟨fun ⟨v, hv⟩ => hv ▸ v.finrank_submodule, fun h => ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : forall w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk]; 

中文:
定义 equivSubmodule
  签名: : ℙ K V ≃ { H : 子模 K V // finrank K H = 1 }
  定义体: (Equiv.ofInjective _ submodule_injective).trans .subtypeEquiv (.refl _) fun H => by
    refine ⟨fun ⟨v, hv⟩ => hv ▸ v.finrank_submodule, fun h => ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : forall w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk]; 

Depends on / 依赖: Equiv.ofInjective, H.smul_mem, Set.range_subset_iff, SetLike, SetLike.ext, Submodule, Submodule.span_singleton_eq_range, Subtype, Subtype.coe_injective.ne, Subtype.val, _iff, antisymm, coe_injective, congr_arg, finrank_eq_one_iff, finrank_submodule, ofInjective, of_pseudoMetrizableSpace_of_isFiniteMeasure, range_subset_iff, smul_mem
-/
noncomputable def equivSubmodule : ℙ K V ≃ { H : Submodule K V // finrank K H = 1 } :=
(Equiv.ofInjective _ submodule_injective).trans .subtypeEquiv (.refl _) fun H => by
    refine ⟨fun ⟨v, hv⟩ => hv ▸ v.finrank_submodule, fun h => ?_⟩
    rcases finrank_eq_one_iff'.1 h with ⟨v : H, hv₀, hv : forall w : H, _⟩
    use mk K (v : V) (Subtype.coe_injective.ne hv₀)
    rw [submodule_mk]; rw [SetLike.ext'_iff]; rw [Submodule.span_singleton_eq_range]
    refine (Set.range_subset_iff.2 fun _ => H.smul_mem _ v.2).antisymm fun x hx => ?_
    rcases hv ⟨x, hx⟩ with ⟨c, hc⟩
    exact ⟨c, congr_arg Subtype.val hc⟩

variable {K V}

/--
Definition of `mk''` / `mk''` 的定义

English:
definition mk''
  signature: (H : Submodule K V) (h : finrank K H = 1)
  body: (equivSubmodule K V).symm ⟨H, h⟩

@[simp]

中文:
定义 mk''
  签名: (H : 子模 K V) (h : finrank K H = 1)
  定义体: (equivSubmodule K V).symm ⟨H, h⟩

@[simp]

Depends on / 依赖: equivSubmodule, of_pseudoMetrizableSpace_secondCountable_of_locallyFinite
-/
noncomputable def mk'' (H : Submodule K V) (h : finrank K H = 1) : ℙ K V :=
  (equivSubmodule K V).symm ⟨H, h⟩

@[simp]
/--
theorem `submodule_mk''` / 定理 `submodule_mk''`

English:
theorem submodule_mk''
  given: (H : Submodule K V) (h : finrank K H = 1)
  statement: (mk'' H h).submodule = H
  proof: congr_arg Subtype.val (equivSubmodule K V).apply_symm_apply ⟨H, h⟩

@[simp]

中文:
定理 submodule_mk''
  条件: (H : 子模 K V) (h : finrank K H = 1)
  结论: (mk'' H h).submodule = H
  证明: congr_arg Subtype.val (equivSubmodule K V).apply_symm_apply ⟨H, h⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, apply_symm_apply, congr_arg, equivSubmodule
-/
theorem submodule_mk'' (H : Submodule K V) (h : finrank K H = 1) : (mk'' H h).submodule = H :=
congr_arg Subtype.val (equivSubmodule K V).apply_symm_apply ⟨H, h⟩

@[simp]
/--
theorem `mk''_submodule` / 定理 `mk''_submodule`

English:
theorem mk''_submodule
  given: (v : ℙ K V)
  statement: mk'' v.submodule v.finrank_submodule = v
  proof: (equivSubmodule K V).symm_apply_apply v

中文:
定理 mk''_submodule
  条件: (v : ℙ K V)
  结论: mk'' v.submodule v.finrank_submodule = v
  证明: (equivSubmodule K V).symm_apply_apply v
-/
theorem mk''_submodule (v : ℙ K V) : mk'' v.submodule v.finrank_submodule = v :=
  (equivSubmodule K V).symm_apply_apply v

section Map

variable {L W : Type*} [DivisionRing L] [AddCommGroup W] [Module L W]

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f)
  body: Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      simp [f.map_smulₛₗ, ← ha, Units.smul_def])

中文:
定义 map
  签名: {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : 函数.单射 f)
  定义体: Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      simp [f.map_smulₛₗ, ← ha, Units.smul_def])

Depends on / 依赖: Quotient, Quotient.map, Units.map, Units.smul_def, f.map_smul, smul_def, toMonoidHom
-/
def map {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f) : ℙ K V -> ℙ L W :=
  Quotient.map' (fun v => ⟨f v, fun c => v.2 (hf (by simp [c]))⟩)
    (by
      rintro ⟨u, hu⟩ ⟨v, hv⟩ ⟨a, ha⟩
      use Units.map σ.toMonoidHom a
      dsimp at ha ⊢
      simp [f.map_smulₛₗ, ← ha, Units.smul_def])

/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v != 0)
  proof: rfl

中文:
定理 map_mk
  条件: {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : 函数.单射 f) (v : V) (hv : v != 0)
  证明: rfl
-/
theorem map_mk {σ : K ->+* L} (f : V ->ₛₗ[σ] W) (hf : Function.Injective f) (v : V) (hv : v != 0) :
    map f hf (mk K v hv) = mk L (f v) (map_zero f ▸ hf.ne hv) :=
  rfl

/--
theorem `map_injective` / 定理 `map_injective`

English:
theorem map_injective
  statement: {σ : K ->+* L} {τ : L ->+* K} [RingHomInvPair σ τ] (f : V ->ₛₗ[σ] W)
  proof: fun u v h => by
  induction u using ind with | h u hu => induction v using ind with | h v hv =>
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]

@[simp]

中文:
定理 map_injective
  结论: {σ : K ->+* L} {τ : L ->+* K} [RingHomInvPair σ τ] (f : V ->ₛₗ[σ] W)
  证明: fun u v h => by
  induction u using ind with | h u hu => induction v using ind with | h v hv =>
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]

@[simp]

Depends on / 依赖: RingHomInvPair, RingHomInvPair.comp_apply_eq, f.map_smul, map_mk, mk_eq_mk_iff
-/
theorem map_injective {σ : K ->+* L} {τ : L ->+* K} [RingHomInvPair σ τ] (f : V ->ₛₗ[σ] W)
    (hf : Function.Injective f) : Function.Injective (map f hf) := fun u v h => by
  induction u using ind with | h u hu => induction v using ind with | h v hv =>
  simp only [map_mk, mk_eq_mk_iff'] at h ⊢
  rcases h with ⟨a, ha⟩
  refine ⟨τ a, hf ?_⟩
  rwa [f.map_smulₛₗ, RingHomInvPair.comp_apply_eq₂]

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map (LinearMap.id : V ->ₗ[K] V) (LinearEquiv.refl K V).injective = id
  proof: by
  ext ⟨v⟩
  rfl

@[simp]

中文:
定理 map_id
  结论: map (线性映射.id : V ->ₗ[K] V) (线性等价.refl K V).injective = id
  证明: by
  ext ⟨v⟩
  rfl

@[simp]

Depends on / 依赖: InnerRegularCompactLTTop, Regular
-/
theorem map_id : map (LinearMap.id : V ->ₗ[K] V) (LinearEquiv.refl K V).injective = id := by
  ext ⟨v⟩
  rfl

@[simp]
/--
theorem `map_comp` / 定理 `map_comp`

English:
theorem map_comp
  statement: {F U : Type*} [DivisionRing F] [AddCommGroup U] [Module F U] {σ : K ->+* L}
  proof: by
  ext ⟨v⟩
  rfl

中文:
定理 map_comp
  结论: {F U : 类型} [除环 F] [加法交换群 U] [模 F U] {σ : K ->+* L}
  证明: by
  ext ⟨v⟩
  rfl

Depends on / 依赖: hg.comp
-/
theorem map_comp {F U : Type*} [DivisionRing F] [AddCommGroup U] [Module F U] {σ : K ->+* L}
    {τ : L ->+* F} {γ : K ->+* F} [RingHomCompTriple σ τ γ] (f : V ->ₛₗ[σ] W)
    (hf : Function.Injective f) (g : W ->ₛₗ[τ] U) (hg : Function.Injective g)
    (hgf : Function.Injective (g.comp f) := hg.comp hf) :
    map (g.comp f) hgf = map g hg ∘ map f hf := by
  ext ⟨v⟩
  rfl

end Map

section linearIndependent

/--
theorem `linearIndependent_pair_iff_ne` / 定理 `linearIndependent_pair_iff_ne`

English:
theorem linearIndependent_pair_iff_ne
  given: {D D' : ℙ K V}
  proof: by
    rw [LinearIndependent.pair_iff' (rep_nonzero _)]
    refine ⟨fun h hD => h 1 (by simp [hD]), fun h a hD => h ?_⟩
    rw [eq_comm]; rw [← mk_rep D]; rw [← mk_rep D']; rw [mk_eq_mk_iff]
    suffices a != 0 by refine ⟨(Ne.isUnit this).unit, by simp [← hD]⟩
    exact fun ha => D'.rep_nonzero (by 

中文:
定理 linearIndependent_pair_iff_ne
  条件: {D D' : ℙ K V}
  证明: by
    rw [LinearIndependent.pair_iff' (rep_nonzero _)]
    refine ⟨fun h hD => h 1 (by simp [hD]), fun h a hD => h ?_⟩
    rw [eq_comm]; rw [← mk_rep D]; rw [← mk_rep D']; rw [mk_eq_mk_iff]
    suffices a != 0 by refine ⟨(Ne.isUnit this).unit, by simp [← hD]⟩
    exact fun ha => D'.rep_nonzero (by 

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_iff, Ne.isUnit, eq_comm, isUnit, mk_eq_mk_iff, mk_rep, pair_iff, rep_nonzero
-/
theorem linearIndependent_pair_iff_ne {D D' : ℙ K V} :
  LinearIndependent K ![D.rep, D'.rep] ↔ D != D' := by
    rw [LinearIndependent.pair_iff' (rep_nonzero _)]
    refine ⟨fun h hD => h 1 (by simp [hD]), fun h a hD => h ?_⟩
    rw [eq_comm]; rw [← mk_rep D]; rw [← mk_rep D']; rw [mk_eq_mk_iff]
    suffices a != 0 by refine ⟨(Ne.isUnit this).unit, by simp [← hD]⟩
    exact fun ha => D'.rep_nonzero (by simp [← hD, ha])

/--
theorem `linearIndepOn_pair` / 定理 `linearIndepOn_pair`

English:
theorem linearIndepOn_pair
  given: (D D' : ℙ K V)
  proof: by
  by_cases h : D = D'
  · simpa [h] using D'.rep_nonzero
  rw [← ne_eq]; rw [← linearIndependent_pair_iff_ne]; rw [LinearIndependent.pair_symm_iff]; rw [← linearIndepOn_id_range_iff] at h
  · simpa using h
  · simpa [injective_pair_iff_ne, injective_pair_iff_ne, ne_eq] using h.injective

中文:
定理 linearIndepOn_pair
  条件: (D D' : ℙ K V)
  证明: by
  by_cases h : D = D'
  · simpa [h] using D'.rep_nonzero
  rw [← ne_eq]; rw [← linearIndependent_pair_iff_ne]; rw [LinearIndependent.pair_symm_iff]; rw [← linearIndepOn_id_range_iff] at h
  · simpa using h
  · simpa [injective_pair_iff_ne, injective_pair_iff_ne, ne_eq] using h.injective

Depends on / 依赖: LinearIndependent, LinearIndependent.pair_symm_iff, h.injective, injective, injective_pair_iff_ne, linearIndepOn_id_range_iff, linearIndependent_pair_iff_ne, ne_eq, pair_symm_iff, rep_nonzero
-/
theorem linearIndepOn_pair (D D' : ℙ K V) :
    LinearIndepOn K id {D.rep, D'.rep} := by
  by_cases h : D = D'
  · simpa [h] using D'.rep_nonzero
  rw [← ne_eq]; rw [← linearIndependent_pair_iff_ne]; rw [LinearIndependent.pair_symm_iff]; rw [← linearIndepOn_id_range_iff] at h
  · simpa using h
  · simpa [injective_pair_iff_ne, injective_pair_iff_ne, ne_eq] using h.injective

end linearIndependent

end Projectivization
