/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.RingTheory.Coalgebra.Equiv
public import Mathlib.RingTheory.Flat.Domain

/-!
# Group-like elements in a coalgebra

This file defines group-like elements in a coalgebra, i.e. elements `a` such that `ε a = 1` and
`Δ a = a ⊗ₜ a`.

## Main declarations

* `IsGroupLikeElem`: Predicate for an element in a coalgebra to be group-like.
* `linearIndepOn_isGroupLikeElem`: Group-like elements over a domain are linearly independent.
-/

@[expose] public section

open Coalgebra Function Module TensorProduct

variable {F R A B : Type*}

section CommSemiring
variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Coalgebra R A]
  [Module R B] [Coalgebra R B] {a b : A}

variable (R) in
/-- A group-like element in a coalgebra is an element `a` such that `ε(a) = 1` and `Δ(a) = a ⊗ₜ a`,
where `ε` and `Δ` are the counit and comultiplication respectively. -/
@[mk_iff]
/--
Definition of `IsGroupLikeElem` / `IsGroupLikeElem` 的定义

English:
structure IsGroupLikeElem
  parameters: (a : A)
  axioms and operations (2):
    - counit_eq_one : counit (R := R) a = 1
    - comul_eq_tmul_self : comul a = a otimesₜ[R] a

中文:
结构 IsGroupLikeElem
  参数: (a : A)
  公理与运算 (2 个):
    - counit_eq_one : counit (R := R) a = 1
    - comul_eq_tmul_self : comul a = a otimesₜ[R] a
-/
structure IsGroupLikeElem (a : A) : Prop where
  /-- A group-like element `a` satisfies `ε(a) = 1`. -/
  counit_eq_one : counit (R := R) a = 1
  /-- A group-like element `a` satisfies `Δ(a) = a ⊗ₜ a`. -/
  comul_eq_tmul_self : comul a = a otimesₜ[R] a

attribute [simp] IsGroupLikeElem.counit_eq_one IsGroupLikeElem.comul_eq_tmul_self

/--
lemma `isGroupLikeElem_self` / 引理 `isGroupLikeElem_self`

English:
lemma isGroupLikeElem_self
  given: {r : R}
  statement: IsGroupLikeElem R r ↔ r = 1
  proof: by
  simp +contextual [isGroupLikeElem_iff]

中文:
引理 isGroupLikeElem_self
  条件: {r : R}
  结论: IsGroupLikeElem R r ↔ r = 1
  证明: by
  simp +contextual [isGroupLikeElem_iff]
-/
@[simp] lemma isGroupLikeElem_self {r : R} : IsGroupLikeElem R r ↔ r = 1 := by
  simp +contextual [isGroupLikeElem_iff]

/--
lemma `IsGroupLikeElem.ne_zero` / 引理 `IsGroupLikeElem.ne_zero`

English:
lemma IsGroupLikeElem.ne_zero
  given: [Nontrivial R] (ha : IsGroupLikeElem R a)
  statement: a != 0
  proof: by
  rintro rfl; simpa using ha.counit_eq_one

中文:
引理 IsGroupLikeElem.ne_zero
  条件: [Nontrivial R] (ha : IsGroupLikeElem R a)
  结论: a != 0
  证明: by
  rintro rfl; simpa using ha.counit_eq_one

Depends on / 依赖: counit_eq_one, ha.counit_eq_one
-/
lemma IsGroupLikeElem.ne_zero [Nontrivial R] (ha : IsGroupLikeElem R a) : a != 0 := by
  rintro rfl; simpa using ha.counit_eq_one

/--
lemma `IsGroupLikeElem.map` / 引理 `IsGroupLikeElem.map`

English:
lemma IsGroupLikeElem.map
  statement: [FunLike F A B] [CoalgHomClass F R A B] (f : F)
  proof: by rw [CoalgHomClass.counit_comp_apply, ha.counit_eq_one]
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

中文:
引理 IsGroupLikeElem.map
  结论: [FunLike F A B] [CoalgHomClass F R A B] (f : F)
  证明: by rw [CoalgHomClass.counit_comp_apply, ha.counit_eq_one]
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

Depends on / 依赖: CoalgHomClass, CoalgHomClass.counit_comp_apply, CoalgHomClass.map_comp_comul_apply, comul_eq_tmul_self, counit_comp_apply, counit_eq_one, ha.comul_eq_tmul_self, ha.counit_eq_one, map_comp_comul_apply
-/
lemma IsGroupLikeElem.map [FunLike F A B] [CoalgHomClass F R A B] (f : F)
    (ha : IsGroupLikeElem R a) : IsGroupLikeElem R (f a) where
  counit_eq_one := by rw [CoalgHomClass.counit_comp_apply, ha.counit_eq_one]
  comul_eq_tmul_self := by rw [← CoalgHomClass.map_comp_comul_apply, ha.comul_eq_tmul_self]; simp

/--
lemma `isGroupLikeElem_map_equiv` / 引理 `isGroupLikeElem_map_equiv`

English:
lemma isGroupLikeElem_map_equiv
  given: [EquivLike F A B] [CoalgEquivClass F R A B] (f : F)
  proof: (CoalgEquivClass.toCoalgEquiv f).symm_apply_apply a ▸ ha.map _
  mpr := .map f

中文:
引理 isGroupLikeElem_map_equiv
  条件: [EquivLike F A B] [CoalgEquivClass F R A B] (f : F)
  证明: (CoalgEquivClass.toCoalgEquiv f).symm_apply_apply a ▸ ha.map _
  mpr := .map f
-/
@[simp] lemma isGroupLikeElem_map_equiv [EquivLike F A B] [CoalgEquivClass F R A B] (f : F) :
    IsGroupLikeElem R (f a) ↔ IsGroupLikeElem R a where
  mp ha := (CoalgEquivClass.toCoalgEquiv f).symm_apply_apply a ▸ ha.map _
  mpr := .map f

variable (R A) in
/-- The type of group-like elements in a coalgebra. -/
@[ext]
/--
Definition of `GroupLike` / `GroupLike` 的定义

English:
structure GroupLike
  parameters: where
  axioms and operations (2):
    - val : A
    - isGroupLikeElem_val : IsGroupLikeElem R val

中文:
结构 GroupLike
  参数: where
  公理与运算 (2 个):
    - val : A
    - isGroupLikeElem_val : IsGroupLikeElem R val
-/
structure GroupLike where
  /-- The underlying element of a group-like element. -/
  val : A
  isGroupLikeElem_val : IsGroupLikeElem R val

namespace GroupLike

initialize_simps_projections GroupLike (as_prefix val)

attribute [simp] isGroupLikeElem_val

attribute [coe] val

/--
Instance `instCoeOut` / 实例 `instCoeOut`

English:
instance instCoeOut
  signature: : CoeOut (GroupLike R A) A where coe
  body: val

中文:
实例 instCoeOut
  签名: : CoeOut (GroupLike R A) A where coe
  定义体: val
-/
instance instCoeOut : CoeOut (GroupLike R A) A where coe := val

/--
lemma `val_injective` / 引理 `val_injective`

English:
lemma val_injective
  statement: Injective (val : GroupLike R A -> A)
  proof: by rintro ⟨a, ha⟩; congr!

中文:
引理 val_injective
  结论: Injective (val : GroupLike R A -> A)
  证明: by rintro ⟨a, ha⟩; congr!
-/
lemma val_injective : Injective (val : GroupLike R A -> A) := by rintro ⟨a, ha⟩; congr!

/--
lemma `val_inj` / 引理 `val_inj`

English:
lemma val_inj
  given: {a b : GroupLike R A}
  statement: a.val = b.val ↔ a = b
  proof: val_injective.eq_iff

中文:
引理 val_inj
  条件: {a b : GroupLike R A}
  结论: a.val = b.val ↔ a = b
  证明: val_injective.eq_iff
-/
@[simp, norm_cast] lemma val_inj {a b : GroupLike R A} : a.val = b.val ↔ a = b :=
  val_injective.eq_iff

/-- Identity equivalence between `GroupLike R A` and `{a : A // IsGroupLikeElem R a}`. -/
@[simps]
/--
Definition of `valEquiv` / `valEquiv` 的定义

English:
definition valEquiv
  signature: : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A -> Prop) where
  body: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

中文:
定义 valEquiv
  签名: : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A -> 命题) where
  定义体: ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
-/
def valEquiv : GroupLike R A ≃ Subtype (IsGroupLikeElem R : A -> Prop) where
  toFun a := ⟨a.1, a.2⟩
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end GroupLike
end CommSemiring

section CommRing
variable [CommRing R] [IsDomain R] [AddCommGroup A] [Module R A] [Coalgebra R A]
  [IsTorsionFree R A]

open Submodule in
/--
lemma `linearIndepOn_isGroupLikeElem` / 引理 `linearIndepOn_isGroupLikeElem`

English:
lemma linearIndepOn_isGroupLikeElem
  statement: LinearIndepOn R id {a : A | IsGroupLikeElem R a}
  proof: by
  classical
  -- We show that any finset `s` of group-like elements is linearly independent.
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  -- For this, we do induction on `s`.
  induction s using Finset.cons_induction with
  -- The case `s = ∅` is trivial.
  | empty => simp
  -- L

中文:
引理 linearIndepOn_isGroupLikeElem
  结论: LinearIndepOn R id {a : A | IsGroupLikeElem R a}
  证明: by
  classical
  -- We show that any finset `s` of group-like elements is linearly independent.
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  -- For this, we do induction on `s`.
  induction s using Finset.cons_induction with
  -- The case `s = ∅` is trivial.
  | empty => simp
  -- L

Depends on / 依赖: classical
-/
lemma linearIndepOn_isGroupLikeElem : LinearIndepOn R id {a : A | IsGroupLikeElem R a} := by
  classical
  -- We show that any finset `s` of group-like elements is linearly independent.
  rw [linearIndepOn_iff_linearIndepOn_finset]
  rintro s hs
  -- For this, we do induction on `s`.
  induction s using Finset.cons_induction with
  -- The case `s = ∅` is trivial.
  | empty => simp
  -- Let's deal with the `s ∪ {a}` case.
  | cons a s has ih =>
  simp only [Finset.cons_eq_insert, Finset.coe_insert, Set.subset_def, Set.mem_insert_iff,
    Finset.mem_coe, Set.mem_ofPred_eq, forall_eq_or_imp] at hs
  obtain ⟨ha, hs⟩ := hs
  specialize ih hs
  -- Assume that there is some `c : A → R` and `d : R` such that `∑ x ∈ s, c x • x = d • a`.
  -- We want to prove `d = 0` and `∀ x ∈ s, c x = 0`.
  rw [Finset.coe_cons]
  refine ih.id_insert' ?_
  simp only [mem_span_finset, forall_exists_index, and_imp]
  rintro d c - hc
  -- `x ⊗ y` over `x, y ∈ s` are linearly independent since `s` is linearly independent and
  -- `R` is a domain.
  replace ih := ih.tmul_of_isDomain ih
  simp_rw [← Finset.coe_product, linearIndepOn_finset_iffₛ, id] at ih
  -- Tensoring the equality `∑ x ∈ s, c x • x = d • a` with itself, we get by linear independence
  -- that `c x ^ 2 = d * c x` and `c x * c y = 0` for `x ≠ y`.
  have key := calc
        ∑ x in s, ∑ y in s, (if x = y then d * c x else 0) • x otimesₜ[R] y
    _ = d • ∑ x in s, c x • x otimesₜ[R] x := by simp [Finset.smul_sum, mul_smul]
    _ = d • comul (d • a) := by rw [← hc]; simp +contextual [(hs _ _).comul_eq_tmul_self]
    _ = (d • a) otimesₜ (d • a) := by simp [ha.comul_eq_tmul_self, smul_tmul, tmul_smul, -neg_smul]
    _ = ∑ x in s, ∑ y in s, (c x * c y) • x otimesₜ[R] y := by
      simp_rw [← hc, sum_tmul, smul_tmul, Finset.smul_sum, tmul_sum, tmul_smul, mul_smul]
  simp_rw [← Finset.sum_product'] at key
  apply ih at key
  -- Therefore, `c x = 0` for all `x ∈ s`.
  replace key x (hx : x in s) : c x = 0 := by
    -- Otherwise, we deduce from `key` that `c y = 0` for any `y ≠ x` with `y ∈ s`.
    by_contra! hcx
    have hcy (y) (hys : y in s) (hyx : y != x) : c y = 0 := by
      simpa [*] using (key (y, x) (by simp [*])).symm
    -- Then substitute this into `hc` to get `c x • x = d • a`.
    rw [Finset.sum_eq_single x (by simp +contextual [hcy]) (by simp [hx])] at hc
    -- But `key` also says that `c x = d`.
    have hcxa : d = c x := mul_left_injective₀ hcx (by simpa using (key (x, x) (by simp [*])))
    -- So `x = a`...
    obtain rfl : x = a := by rwa [hcxa, smul_right_inj hcx] at hc
    -- ... which contradicts `x ∈ s` and `a ∉ s`.
    contradiction
  -- We are now done, since `d • a = ∑ x ∈ s, c x • x = 0`
  simp_all [ha.ne_zero, eq_comm]

/--
lemma `linearIndep_groupLikeVal` / 引理 `linearIndep_groupLikeVal`

English:
lemma linearIndep_groupLikeVal
  statement: LinearIndependent R (GroupLike.val (R := R) (A := A))
  proof: by
  simpa using! (linearIndependent_equiv GroupLike.valEquiv).2 linearIndepOn_isGroupLikeElem

中文:
引理 linearIndep_groupLikeVal
  结论: LinearIndependent R (GroupLike.val (R := R) (A := A))
  证明: by
  simpa using! (linearIndependent_equiv GroupLike.valEquiv).2 linearIndepOn_isGroupLikeElem

Depends on / 依赖: GroupLike, GroupLike.valEquiv, linearIndepOn_isGroupLikeElem, linearIndependent_equiv, valEquiv
-/
lemma linearIndep_groupLikeVal : LinearIndependent R (GroupLike.val (R := R) (A := A)) := by
  simpa using! (linearIndependent_equiv GroupLike.valEquiv).2 linearIndepOn_isGroupLikeElem

end CommRing
