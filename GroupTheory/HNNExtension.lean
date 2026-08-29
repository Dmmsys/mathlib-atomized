/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Ring.CharZero
public import Mathlib.Algebra.Ring.Int.Units
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Complement

/-!

## HNN Extensions of Groups

This file defines the HNN extension of a group `G`, `HNNExtension G A B φ`. Given a group `G`,
subgroups `A` and `B` and an isomorphism `φ` of `A` and `B`, we adjoin a letter `t` to `G`, such
that for any `a ∈ A`, the conjugate of `of a` by `t` is `of (φ a)`, where `of` is the canonical map
from `G` into the `HNNExtension`. This construction is named after Graham Higman, Bernhard Neumann
and Hanna Neumann.

## Main definitions

- `HNNExtension G A B φ` : The HNN Extension of a group `G`, where `A` and `B` are subgroups and `φ`
  is an isomorphism between `A` and `B`.
- `HNNExtension.of` : The canonical embedding of `G` into `HNNExtension G A B φ`.
- `HNNExtension.t` : The stable letter of the HNN extension.
- `HNNExtension.lift` : Define a function `HNNExtension G A B φ →* H`, by defining it on `G` and `t`
- `HNNExtension.of_injective` : The canonical embedding `G →* HNNExtension G A B φ` is injective.
- `HNNExtension.ReducedWord.toList_eq_nil_of_mem_of_range` : Britton's Lemma. If an element of
  `G` is represented by a reduced word, then this reduced word does not contain `t`.

-/

@[expose] public section

assert_not_exists Field

open Monoid Coprod Multiplicative Subgroup Function

/--
Definition of `HNNExtension.con` / `HNNExtension.con` 的定义

English:
definition HNNExtension.con
  signature: (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B)
  body: conGen (fun x y => exists (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

中文:
定义 HNNExtension.con
  签名: (G : 类型) [群 G] (A B : 子群 G) (φ : A ≃* B)
  定义体: conGen (fun x y => exists (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

Depends on / 依赖: conGen
-/
def HNNExtension.con (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) :
    Con (G ∗ Multiplicative Int) :=
  conGen (fun x y => exists (a : A),
    x = inr (ofAdd 1) * inl (a : G) ∧
    y = inl (φ a : G) * inr (ofAdd 1))

/--
Definition of `HNNExtension` / `HNNExtension` 的定义

English:
definition HNNExtension
  signature: (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B)
  body: (HNNExtension.con G A B φ).Quotient

中文:
定义 HNNExtension
  签名: (G : 类型) [群 G] (A B : 子群 G) (φ : A ≃* B)
  定义体: (HNNExtension.con G A B φ).Quotient

Depends on / 依赖: HNNExtension, HNNExtension.con, Quotient
-/
def HNNExtension (G : Type*) [Group G] (A B : Subgroup G) (φ : A ≃* B) : Type _ :=
  (HNNExtension.con G A B φ).Quotient

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B} {H : Type*}
  [Group H] {M : Type*} [Monoid M]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Group (HNNExtension G A B φ)
  body: by
  delta HNNExtension; infer_instance

中文:
实例 :
  签名: 群 (HNNExtension G A B φ)
  定义体: by
  delta HNNExtension; infer_instance

Depends on / 依赖: HNNExtension, infer_instance
-/
instance : Group (HNNExtension G A B φ) := by
  delta HNNExtension; infer_instance

namespace HNNExtension

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : G ->* HNNExtension G A B φ
  body: (HNNExtension.con G A B φ).mk'.comp inl

中文:
定义 of
  签名: : G ->* HNNExtension G A B φ
  定义体: (HNNExtension.con G A B φ).mk'.comp inl

Depends on / 依赖: HNNExtension, HNNExtension.con
-/
def of : G ->* HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inl

/--
Definition of `t` / `t` 的定义

English:
definition t
  signature: : HNNExtension G A B φ
  body: (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

中文:
定义 t
  签名: : HNNExtension G A B φ
  定义体: (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

Depends on / 依赖: HNNExtension, HNNExtension.con
-/
def t : HNNExtension G A B φ :=
  (HNNExtension.con G A B φ).mk'.comp inr (ofAdd 1)

/--
theorem `t_mul_of` / 定理 `t_mul_of`

English:
theorem t_mul_of
  given: (a : A)
  proof: (Con.eq _).2 ConGen.Rel.of _ _ ⟨a, by simp⟩

中文:
定理 t_mul_of
  条件: (a : A)
  证明: (Con.eq _).2 ConGen.Rel.of _ _ ⟨a, by simp⟩

Depends on / 依赖: Con.eq, ConGen, ConGen.Rel.of
-/
theorem t_mul_of (a : A) :
    t * (of (a : G) : HNNExtension G A B φ) = of (φ a : G) * t :=
(Con.eq _).2 ConGen.Rel.of _ _ ⟨a, by simp⟩

/--
theorem `of_mul_t` / 定理 `of_mul_t`

English:
theorem of_mul_t
  given: (b : B)
  proof: by
  rw [t_mul_of]; simp

中文:
定理 of_mul_t
  条件: (b : B)
  证明: by
  rw [t_mul_of]; simp

Depends on / 依赖: t_mul_of
-/
theorem of_mul_t (b : B) :
    (of (b : G) : HNNExtension G A B φ) * t = t * of (φ.symm b : G) := by
  rw [t_mul_of]; simp

/--
theorem `equiv_eq_conj` / 定理 `equiv_eq_conj`

English:
theorem equiv_eq_conj
  given: (a : A)
  proof: by
  rw [t_mul_of]; simp

中文:
定理 equiv_eq_conj
  条件: (a : A)
  证明: by
  rw [t_mul_of]; simp

Depends on / 依赖: t_mul_of
-/
theorem equiv_eq_conj (a : A) :
    (of (φ a : G) : HNNExtension G A B φ) = t * of (a : G) * t⁻¹ := by
  rw [t_mul_of]; simp

/--
theorem `equiv_symm_eq_conj` / 定理 `equiv_symm_eq_conj`

English:
theorem equiv_symm_eq_conj
  given: (b : B)
  proof: by
  rw [mul_assoc]; rw [of_mul_t]; simp

中文:
定理 equiv_symm_eq_conj
  条件: (b : B)
  证明: by
  rw [mul_assoc]; rw [of_mul_t]; simp

Depends on / 依赖: mul_assoc, of_mul_t
-/
theorem equiv_symm_eq_conj (b : B) :
    (of (φ.symm b : G) : HNNExtension G A B φ) = t⁻¹ * of (b : G) * t := by
  rw [mul_assoc]; rw [of_mul_t]; simp

/--
theorem `inv_t_mul_of` / 定理 `inv_t_mul_of`

English:
theorem inv_t_mul_of
  given: (b : B)
  proof: by
  rw [equiv_symm_eq_conj]; simp

中文:
定理 inv_t_mul_of
  条件: (b : B)
  证明: by
  rw [equiv_symm_eq_conj]; simp

Depends on / 依赖: equiv_symm_eq_conj
-/
theorem inv_t_mul_of (b : B) :
    t⁻¹ * (of (b : G) : HNNExtension G A B φ) = of (φ.symm b : G) * t⁻¹ := by
  rw [equiv_symm_eq_conj]; simp

/--
theorem `of_mul_inv_t` / 定理 `of_mul_inv_t`

English:
theorem of_mul_inv_t
  given: (a : A)
  proof: by
  rw [equiv_eq_conj]; simp [mul_assoc]

中文:
定理 of_mul_inv_t
  条件: (a : A)
  证明: by
  rw [equiv_eq_conj]; simp [mul_assoc]

Depends on / 依赖: equiv_eq_conj, mul_assoc
-/
theorem of_mul_inv_t (a : A) :
    (of (a : G) : HNNExtension G A B φ) * t⁻¹ = t⁻¹ * of (φ a : G) := by
  rw [equiv_eq_conj]; simp [mul_assoc]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x)
  body: Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le.2 <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

中文:
定义 lift
  签名: (f : G ->* H) (x : H) (hx : 对任意 a : A, x * f ↑a = f (φ a : G) * x)
  定义体: Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le.2 <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

Depends on / 依赖: Con.conGen_le, Con.lift, Coprod, Coprod.lift, conGen_le, zpowersHom
-/
def lift (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x) :
    HNNExtension G A B φ ->* H :=
  Con.lift _ (Coprod.lift f (zpowersHom H x)) (Con.conGen_le.2 <| by
    rintro _ _ ⟨a, rfl, rfl⟩
    simp [hx])

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_t` / 定理 `lift_t`

English:
theorem lift_t
  given: (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x)
  proof: by
  delta HNNExtension; simp [lift, t]

中文:
定理 lift_t
  条件: (f : G ->* H) (x : H) (hx : 对任意 a : A, x * f ↑a = f (φ a : G) * x)
  证明: by
  delta HNNExtension; simp [lift, t]

Depends on / 依赖: HNNExtension
-/
theorem lift_t (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x) :
    lift f x hx t = x := by
  delta HNNExtension; simp [lift, t]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x) (g : G)
  proof: by
  delta HNNExtension; simp [lift, of]

@[ext high]

中文:
定理 lift_of
  条件: (f : G ->* H) (x : H) (hx : 对任意 a : A, x * f ↑a = f (φ a : G) * x) (g : G)
  证明: by
  delta HNNExtension; simp [lift, of]

@[ext high]

Depends on / 依赖: HNNExtension
-/
theorem lift_of (f : G ->* H) (x : H) (hx : forall a : A, x * f ↑a = f (φ a : G) * x) (g : G) :
    lift f x hx (of g) = f g := by
  delta HNNExtension; simp [lift, of]

@[ext high]
/--
theorem `hom_ext` / 定理 `hom_ext`

English:
theorem hom_ext
  statement: {f g : HNNExtension G A B φ ->* M}
  proof: (MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext hg (MonoidHom.ext_mint ht)

中文:
定理 hom_ext
  结论: {f g : HNNExtension G A B φ ->* M}
  证明: (MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext hg (MonoidHom.ext_mint ht)

Depends on / 依赖: Con.mk, Coprod, Coprod.hom_ext, MonoidHom, MonoidHom.cancel_right, MonoidHom.ext_mint, _surjective, cancel_right, ext_mint, hom_ext
-/
theorem hom_ext {f g : HNNExtension G A B φ ->* M}
    (hg : f.comp of = g.comp of) (ht : f t = g t) : f = g :=
(MonoidHom.cancel_right Con.mk'_surjective).mp
    Coprod.hom_ext hg (MonoidHom.ext_mint ht)

set_option backward.isDefEq.respectTransparency false in
@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : HNNExtension G A B φ -> Prop}
  proof: by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := Set.ofPred motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ ->* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp [f]) (by simp [f])
  change motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

中文:
定理 induction_on
  结论: {motive : HNNExtension G A B φ -> 命题}
  证明: by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := Set.ofPred motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ ->* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp [f]) (by simp [f])
  change motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

Depends on / 依赖: HNNExtension, HNNExtension.of.codRestrict, HNNExtension.t, MonoidHom, MonoidHom.id, S.subtype.comp, Set.ofPred, Subgroup, carrier, codRestrict, equiv_eq_conj, hom_ext, inv_mem, motive, mul_assoc, mul_mem, ofPred, one_mem, subtype
-/
theorem induction_on {motive : HNNExtension G A B φ -> Prop}
    (x : HNNExtension G A B φ) (of : forall g, motive (of g))
    (t : motive t) (mul : forall x y, motive x -> motive y -> motive (x * y))
    (inv : forall x, motive x -> motive x⁻¹) : motive x := by
  let S : Subgroup (HNNExtension G A B φ) :=
    { carrier := Set.ofPred motive
      one_mem' := by simpa using of 1
      mul_mem' := mul _ _
      inv_mem' := inv _ }
  let f : HNNExtension G A B φ ->* S :=
    lift (HNNExtension.of.codRestrict S of)
      ⟨HNNExtension.t, t⟩ (by intro a; ext; simp [equiv_eq_conj, mul_assoc])
  have hf : S.subtype.comp f = MonoidHom.id _ :=
    hom_ext (by ext; simp [f]) (by simp [f])
  change motive (MonoidHom.id _ x)
  rw [← hf]
  exact (f x).2

variable (A B φ)

/--
Definition of `toSubgroup` / `toSubgroup` 的定义

English:
definition toSubgroup
  signature: (u : Intˣ)
  body: if u = 1 then A else B

@[simp]

中文:
定义 toSubgroup
  签名: (u : 整数ˣ)
  定义体: if u = 1 then A else B

@[simp]
-/
def toSubgroup (u : Intˣ) : Subgroup G :=
  if u = 1 then A else B

@[simp]
/--
theorem `toSubgroup_one` / 定理 `toSubgroup_one`

English:
theorem toSubgroup_one
  statement: toSubgroup A B 1 = A
  proof: rfl

@[simp]

中文:
定理 toSubgroup_one
  结论: toSubgroup A B 1 = A
  证明: rfl

@[simp]
-/
theorem toSubgroup_one : toSubgroup A B 1 = A := rfl

@[simp]
/--
theorem `toSubgroup_neg_one` / 定理 `toSubgroup_neg_one`

English:
theorem toSubgroup_neg_one
  statement: toSubgroup A B (-1) = B
  proof: rfl

中文:
定理 toSubgroup_neg_one
  结论: toSubgroup A B (-1) = B
  证明: rfl
-/
theorem toSubgroup_neg_one : toSubgroup A B (-1) = B := rfl

variable {A B}

/--
Definition of `toSubgroupEquiv` / `toSubgroupEquiv` 的定义

English:
definition toSubgroupEquiv
  signature: (u : Intˣ)
  body: if hu : u = 1 then hu ▸ φ else by
    convert! φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]

中文:
定义 toSubgroupEquiv
  签名: (u : 整数ˣ)
  定义体: if hu : u = 1 then hu ▸ φ else by
    convert! φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]

Depends on / 依赖: Int.units_eq_one_or, convert, units_eq_one_or
-/
def toSubgroupEquiv (u : Intˣ) : toSubgroup A B u ≃* toSubgroup A B (-u) :=
  if hu : u = 1 then hu ▸ φ else by
    convert! φ.symm <;>
    cases Int.units_eq_one_or u <;> simp_all

@[simp]
/--
theorem `toSubgroupEquiv_one` / 定理 `toSubgroupEquiv_one`

English:
theorem toSubgroupEquiv_one
  statement: toSubgroupEquiv φ 1 = φ
  proof: rfl

@[simp]

中文:
定理 toSubgroupEquiv_one
  结论: toSubgroupEquiv φ 1 = φ
  证明: rfl

@[simp]
-/
theorem toSubgroupEquiv_one : toSubgroupEquiv φ 1 = φ := rfl

@[simp]
/--
theorem `toSubgroupEquiv_neg_one` / 定理 `toSubgroupEquiv_neg_one`

English:
theorem toSubgroupEquiv_neg_one
  statement: toSubgroupEquiv φ (-1) = φ.symm
  proof: rfl

中文:
定理 toSubgroupEquiv_neg_one
  结论: toSubgroupEquiv φ (-1) = φ.symm
  证明: rfl
-/
theorem toSubgroupEquiv_neg_one : toSubgroupEquiv φ (-1) = φ.symm := rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `toSubgroupEquiv_neg_apply` / 定理 `toSubgroupEquiv_neg_apply`

English:
theorem toSubgroupEquiv_neg_apply
  given: (u : Intˣ) (a : toSubgroup A B u)
  proof: by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [toSubgroup]
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

中文:
定理 toSubgroupEquiv_neg_apply
  条件: (u : 整数ˣ) (a : toSubgroup A B u)
  证明: by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [toSubgroup]
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

Depends on / 依赖: Int.units_eq_one_or, SetLike, SetLike.coe_eq_coe, apply_symm_apply, coe_eq_coe, toSubgroup, toSubgroupEquiv_neg_one, toSubgroup_neg_one, units_eq_one_or
-/
theorem toSubgroupEquiv_neg_apply (u : Intˣ) (a : toSubgroup A B u) :
    (toSubgroupEquiv φ (-u) (toSubgroupEquiv φ u a) : G) = a := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp [toSubgroup]
  · simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, SetLike.coe_eq_coe]
    exact φ.apply_symm_apply a

namespace NormalWord

variable (G A B)
/--
Definition of `TransversalPair` / `TransversalPair` 的定义

English:
structure TransversalPair
  parameters: : Type _ where
  axioms and operations (2):
    - set : Intˣ -> Set G
    - compl : forall u, IsComplement (toSubgroup A B u : Subgroup G) (set u)

中文:
结构 横截对
  参数: : 类型 _ where
  公理与运算 (2 个):
    - set : 整数ˣ -> 集合 G
    - compl : 对任意 u, IsComplement (toSubgroup A B u : 子群 G) (set u)
-/
structure TransversalPair : Type _ where
  /-- The transversal of each subgroup -/
  set : Intˣ -> Set G
  /-- We have exactly one element of each coset of the subgroup -/
  compl : forall u, IsComplement (toSubgroup A B u : Subgroup G) (set u)

/--
Instance `TransversalPair.nonempty` / 实例 `TransversalPair.nonempty`

English:
instance TransversalPair.nonempty
  signature: : Nonempty (TransversalPair G A B)
  body: by
  choose t ht using fun u => (toSubgroup A B u).exists_isComplement_right 1
  exact ⟨⟨t, fun i => (ht i).1⟩⟩

中文:
实例 横截对.nonempty
  签名: : 非空 (横截对 G A B)
  定义体: by
  choose t ht using fun u => (toSubgroup A B u).exists_isComplement_right 1
  exact ⟨⟨t, fun i => (ht i).1⟩⟩

Depends on / 依赖: exists_isComplement_right, toSubgroup
-/
instance TransversalPair.nonempty : Nonempty (TransversalPair G A B) := by
  choose t ht using fun u => (toSubgroup A B u).exists_isComplement_right 1
  exact ⟨⟨t, fun i => (ht i).1⟩⟩

/--
Definition of `ReducedWord` / `ReducedWord` 的定义

English:
structure ReducedWord
  parameters: : Type _ where
  axioms and operations (3):
    - head : G
    - toList : List (Intˣ × G)
    - chain : toList.IsChain (fun a b => a.2 in toSubgroup A B a.1 -> a.1 = b.1)

中文:
结构 ReducedWord
  参数: : 类型 _ where
  公理与运算 (3 个):
    - head : G
    - toList : 列表 (整数ˣ × G)
    - chain : toList.IsChain (fun a b => a.2 in toSubgroup A B a.1 -> a.1 = b.1)
-/
structure ReducedWord : Type _ where
  /-- Every `ReducedWord` is the product of an element of the group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : G
  /-- The list of pairs `(ℤˣ × G)`, where each pair `(u, g)` represents the element `t^u * g` of
  `HNNExtension G A B φ` -/
  toList : List (Intˣ × G)
  /-- There are no sequences of the form `t^u * g * t^-u` where `g ∈ toSubgroup A B u`. -/
  chain : toList.IsChain (fun a b => a.2 in toSubgroup A B a.1 -> a.1 = b.1)

/-- The empty reduced word. -/
@[simps]
/--
Definition of `ReducedWord.empty` / `ReducedWord.empty` 的定义

English:
definition ReducedWord.empty
  signature: : ReducedWord G A B
  body: { head := 1
    toList := []
    chain := List.isChain_nil }

中文:
定义 ReducedWord.empty
  签名: : ReducedWord G A B
  定义体: { head := 1
    toList := []
    chain := List.isChain_nil }

Depends on / 依赖: List.isChain_nil, isChain_nil, toList
-/
def ReducedWord.empty : ReducedWord G A B :=
  { head := 1
    toList := []
    chain := List.isChain_nil }

variable {G A B}
/--
Definition of `ReducedWord.prod` / `ReducedWord.prod` 的定义

English:
definition ReducedWord.prod
  signature: : ReducedWord G A B -> HNNExtension G A B φ
  body: fun w => of w.head * (w.toList.map (fun x => t ^ (x.1 : Int) * of x.2)).prod

中文:
定义 ReducedWord.乘积
  签名: : ReducedWord G A B -> HNNExtension G A B φ
  定义体: fun w => of w.head * (w.toList.map (fun x => t ^ (x.1 : Int) * of x.2)).prod

Depends on / 依赖: toList, w.head, w.toList.map
-/
def ReducedWord.prod : ReducedWord G A B -> HNNExtension G A B φ :=
  fun w => of w.head * (w.toList.map (fun x => t ^ (x.1 : Int) * of x.2)).prod

/--
Definition of `_root_.HNNExtension.NormalWord` / `_root_.HNNExtension.NormalWord` 的定义

English:
structure _root_.HNNExtension.NormalWord
  parameters: (d : TransversalPair G A B)
  extends: ReducedWord G A B
  axioms and operations (1):
    - mem_set : forall (u : Intˣ) (g : G), (u, g) in toList -> g in d.set u

中文:
结构 _root_.HNNExtension.NormalWord
  参数: (d : 横截对 G A B)
  继承: ReducedWord G A B
  公理与运算 (1 个):
    - mem_set : 对任意 (u : 整数ˣ) (g : G), (u, g) in toList -> g in d.set u
-/
structure _root_.HNNExtension.NormalWord (d : TransversalPair G A B) : Type _
    extends ReducedWord G A B where
  /-- Every element `g : G` in the list is the chosen element of its coset -/
  mem_set : forall (u : Intˣ) (g : G), (u, g) in toList -> g in d.set u

variable {d : TransversalPair G A B}

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  statement: {w w' : NormalWord d}
  proof: by
  rcases w with ⟨⟨⟩, _⟩; cases w'; simp_all

中文:
定理 ext
  结论: {w w' : NormalWord d}
  证明: by
  rcases w with ⟨⟨⟩, _⟩; cases w'; simp_all
-/
theorem ext {w w' : NormalWord d}
    (h1 : w.head = w'.head) (h2 : w.toList = w'.toList) : w = w' := by
  rcases w with ⟨⟨⟩, _⟩; cases w'; simp_all

/-- The empty word -/
@[simps]
/--
Definition of `empty` / `empty` 的定义

English:
definition empty
  signature: : NormalWord d
  body: { head := 1
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

中文:
定义 empty
  签名: : NormalWord d
  定义体: { head := 1
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

Depends on / 依赖: List.isChain_nil, isChain_nil, mem_set, toList
-/
def empty : NormalWord d :=
  { head := 1
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

/-- The `NormalWord` representing an element `g` of the group `G`, which is just the element `g`
itself. -/
@[simps]
/--
Definition of `ofGroup` / `ofGroup` 的定义

English:
definition ofGroup
  signature: (g : G)
  body: { head := g
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

中文:
定义 ofGroup
  签名: (g : G)
  定义体: { head := g
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

Depends on / 依赖: List.isChain_nil, isChain_nil, mem_set, toList
-/
def ofGroup (g : G) : NormalWord d :=
  { head := g
    toList := []
    mem_set := by simp
    chain := List.isChain_nil }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (NormalWord d)
  body: ⟨empty⟩

中文:
实例 :
  签名: 可居 (NormalWord d)
  定义体: ⟨empty⟩
-/
instance : Inhabited (NormalWord d) := ⟨empty⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (NormalWord d)
  body: { smul := fun g w => { w with head := g * w.head }
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

中文:
实例 :
  签名: 乘法作用 G (NormalWord d)
  定义体: { smul := fun g w => { w with head := g * w.head }
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

Depends on / 依赖: instHSMul, instances, mul_assoc, mul_smul, one_smul, w.head
-/
instance : MulAction G (NormalWord d) :=
  { smul := fun g w => { w with head := g * w.head }
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }

/--
theorem `group_smul_def` / 定理 `group_smul_def`

English:
theorem group_smul_def
  given: (g : G) (w : NormalWord d)
  proof: rfl

@[simp]

中文:
定理 group_smul_def
  条件: (g : G) (w : NormalWord d)
  证明: rfl

@[simp]

Depends on / 依赖: w.head
-/
theorem group_smul_def (g : G) (w : NormalWord d) :
    g • w = { w with head := g * w.head } := rfl

@[simp]
/--
theorem `group_smul_head` / 定理 `group_smul_head`

English:
theorem group_smul_head
  given: (g : G) (w : NormalWord d)
  statement: (g • w).head = g * w.head
  proof: rfl

@[simp]

中文:
定理 group_smul_head
  条件: (g : G) (w : NormalWord d)
  结论: (g • w).head = g * w.head
  证明: rfl

@[simp]
-/
theorem group_smul_head (g : G) (w : NormalWord d) : (g • w).head = g * w.head := rfl

@[simp]
/--
theorem `group_smul_toList` / 定理 `group_smul_toList`

English:
theorem group_smul_toList
  given: (g : G) (w : NormalWord d)
  statement: (g • w).toList = w.toList
  proof: rfl

中文:
定理 group_smul_toList
  条件: (g : G) (w : NormalWord d)
  结论: (g • w).toList = w.toList
  证明: rfl
-/
theorem group_smul_toList (g : G) (w : NormalWord d) : (g • w).toList = w.toList := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul G (NormalWord d)
  body: ⟨by simp [group_smul_def]⟩

中文:
实例 :
  签名: 忠实标量乘法 G (NormalWord d)
  定义体: ⟨by simp [group_smul_def]⟩

Depends on / 依赖: group_smul_def
-/
instance : FaithfulSMul G (NormalWord d) := ⟨by simp [group_smul_def]⟩

/-- A constructor to append an element `g` of `G` and `u : ℤˣ` to a word `w` with sufficient
hypotheses that no normalization or cancellation need take place for the result to be in normal form
-/
@[simps]
/--
Definition of `cons` / `cons` 的定义

English:
definition cons
  signature: (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  body: { head := g,
    toList := (u, w.head) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.isChain_cons.2 ⟨?_, w.chain⟩
      rintro ⟨u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

中文:
定义 cons
  签名: (g : G) (u : 整数ˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  定义体: { head := g,
    toList := (u, w.head) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.isChain_cons.2 ⟨?_, w.chain⟩
      rintro ⟨u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

Depends on / 依赖: List.isChain_cons, List.mem_cons, Prod.mk.injEq, isChain_cons, mem_cons, mem_set, toList, w.chain, w.head, w.mem_set, w.toList
-/
def cons (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
    (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u') :
    NormalWord d :=
  { head := g,
    toList := (u, w.head) :: w.toList,
    mem_set := by
      intro u' g' h'
      simp only [List.mem_cons, Prod.mk.injEq] at h'
      rcases h' with ⟨rfl, rfl⟩ | h'
      · exact h1
      · exact w.mem_set _ _ h'
    chain := by
      refine List.isChain_cons.2 ⟨?_, w.chain⟩
      rintro ⟨u', g'⟩ hu' hw1
      exact h2 _ (by simp_all) hw1 }

/-- A recursor to induct on a `NormalWord`, by proving the property is preserved under `cons` -/
@[elab_as_elim]
/--
Definition of `consRecOn` / `consRecOn` 的定义

English:
definition consRecOn
  signature: {motive : NormalWord d -> Sort*} (w : NormalWord d)
  body: by
  rcases w with ⟨⟨g, l, chain⟩, mem_set⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1
      { head := a.2
        toList := l
        mem_set := fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
        chain := (List.isChain_cons.1 chain).2 }
      (mem_set a.1 a.2 List.mem_cons_self)
      (by simpa using (List.isChain_cons.1 chain).1)
      (ih _ _ _)

@[simp]

中文:
定义 consRecOn
  签名: {motive : NormalWord d -> 类型层*} (w : NormalWord d)
  定义体: by
  rcases w with ⟨⟨g, l, chain⟩, mem_set⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1
      { head := a.2
        toList := l
        mem_set := fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
        chain := (List.isChain_cons.1 chain).2 }
      (mem_set a.1 a.2 List.mem_cons_self)
      (by simpa using (List.isChain_cons.1 chain).1)
      (ih _ _ _)

@[simp]

Depends on / 依赖: List.isChain_cons, List.mem_cons_of_mem, List.mem_cons_self, generalizing, isChain_cons, mem_cons_of_mem, mem_cons_self, mem_set, ofGroup, toList
-/
def consRecOn {motive : NormalWord d -> Sort*} (w : NormalWord d)
    (ofGroup : forall g, motive (ofGroup g))
    (cons : forall (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
      (h2 : forall u' in Option.map Prod.fst w.toList.head?,
        w.head in toSubgroup A B u -> u = u'),
      motive w -> motive (cons g u w h1 h2)) : motive w := by
  rcases w with ⟨⟨g, l, chain⟩, mem_set⟩
  induction l generalizing g with
  | nil => exact ofGroup _
  | cons a l ih =>
    exact cons g a.1
      { head := a.2
        toList := l
        mem_set := fun _ _ h => mem_set _ _ (List.mem_cons_of_mem _ h),
        chain := (List.isChain_cons.1 chain).2 }
      (mem_set a.1 a.2 List.mem_cons_self)
      (by simpa using (List.isChain_cons.1 chain).1)
      (ih _ _ _)

@[simp]
/--
theorem `consRecOn_ofGroup` / 定理 `consRecOn_ofGroup`

English:
theorem consRecOn_ofGroup
  statement: {motive : NormalWord d -> Sort*}
  proof: rfl

@[simp]

中文:
定理 consRecOn_ofGroup
  结论: {motive : NormalWord d -> 类型层*}
  证明: rfl

@[simp]
-/
theorem consRecOn_ofGroup {motive : NormalWord d -> Sort*}
    (g : G) (ofGroup : forall g, motive (ofGroup g))
    (cons : forall (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
      (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head
        in toSubgroup A B u -> u = u'),
      motive w -> motive (cons g u w h1 h2)) :
    consRecOn (.ofGroup g) ofGroup cons = ofGroup g := rfl

@[simp]
/--
theorem `consRecOn_cons` / 定理 `consRecOn_cons`

English:
theorem consRecOn_cons
  statement: {motive : NormalWord d -> Sort*}
  proof: rfl

@[simp]

中文:
定理 consRecOn_cons
  结论: {motive : NormalWord d -> 类型层*}
  证明: rfl

@[simp]
-/
theorem consRecOn_cons {motive : NormalWord d -> Sort*}
    (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
    (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u')
    (ofGroup : forall g, motive (ofGroup g))
    (cons : forall (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
      (h2 : forall u' in Option.map Prod.fst w.toList.head?,
        w.head in toSubgroup A B u -> u = u'),
      motive w -> motive (cons g u w h1 h2)) :
    consRecOn (.cons g u w h1 h2) ofGroup cons = cons g u w h1 h2
      (consRecOn w ofGroup cons) := rfl

@[simp]
/--
theorem `smul_cons` / 定理 `smul_cons`

English:
theorem smul_cons
  statement: (g₁ g₂ : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  proof: rfl

@[simp]

中文:
定理 smul_cons
  结论: (g₁ g₂ : G) (u : 整数ˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  证明: rfl

@[simp]
-/
theorem smul_cons (g₁ g₂ : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
    (h2 : forall u' in Option.map Prod.fst w.toList.head?, w.head in toSubgroup A B u -> u = u') :
    g₁ • cons g₂ u w h1 h2 = cons (g₁ * g₂) u w h1 h2 :=
  rfl

@[simp]
/--
theorem `smul_ofGroup` / 定理 `smul_ofGroup`

English:
theorem smul_ofGroup
  given: (g₁ g₂ : G)
  proof: rfl

中文:
定理 smul_ofGroup
  条件: (g₁ g₂ : G)
  证明: rfl
-/
theorem smul_ofGroup (g₁ g₂ : G) :
    g₁ • (ofGroup g₂ : NormalWord d) = ofGroup (g₁ * g₂) := rfl

variable (d)
/--
Definition of `unitsSMulGroup` / `unitsSMulGroup` 的定义

English:
definition unitsSMulGroup
  signature: (u : Intˣ) (g : G)
  body: let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

中文:
定义 unitsSMulGroup
  签名: (u : 整数ˣ) (g : G)
  定义体: let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

Depends on / 依赖: d.compl, toSubgroupEquiv
-/
noncomputable def unitsSMulGroup (u : Intˣ) (g : G) :
    (toSubgroup A B (-u)) × d.set u :=
  let g' := (d.compl u).equiv g
  (toSubgroupEquiv φ u g'.1, g'.2)

/--
theorem `unitsSMulGroup_snd` / 定理 `unitsSMulGroup_snd`

English:
theorem unitsSMulGroup_snd
  given: (u : Intˣ) (g : G)
  proof: by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

中文:
定理 unitsSMulGroup_snd
  条件: (u : 整数ˣ) (g : G)
  证明: by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

Depends on / 依赖: Int.units_eq_one_or, units_eq_one_or
-/
theorem unitsSMulGroup_snd (u : Intˣ) (g : G) :
    (unitsSMulGroup φ d u g).2 = ((d.compl u).equiv g).2 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> rfl

variable {d}

/--
Definition of `Cancels` / `Cancels` 的定义

English:
definition Cancels
  signature: (u : Intˣ) (w : NormalWord d)
  body: (w.head in (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

中文:
定义 Cancels
  签名: (u : 整数ˣ) (w : NormalWord d)
  定义体: (w.head in (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

Depends on / 依赖: Prod.fst, Subgroup, toList, toSubgroup, w.head, w.toList.head
-/
def Cancels (u : Intˣ) (w : NormalWord d) : Prop :=
  (w.head in (toSubgroup A B u : Subgroup G)) ∧ w.toList.head?.map Prod.fst = some (-u)

/--
Definition of `unitsSMulWithCancel` / `unitsSMulWithCancel` 的定义

English:
definition unitsSMulWithCancel
  signature: (u : Intˣ) (w : NormalWord d)
  body: consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g _ w _ _ _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

中文:
定义 unitsSMulWithCancel
  签名: (u : 整数ˣ) (w : NormalWord d)
  定义体: consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g _ w _ _ _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

Depends on / 依赖: Cancels, consRecOn, ofGroup, toSubgroupEquiv
-/
def unitsSMulWithCancel (u : Intˣ) (w : NormalWord d) : Cancels u w -> NormalWord d :=
  consRecOn w
    (by simp [Cancels, ofGroup]; tauto)
    (fun g _ w _ _ _ can =>
      (toSubgroupEquiv φ u ⟨g, can.1⟩ : G) • w)

/--
Definition of `unitsSMul` / `unitsSMul` 的定义

English:
definition unitsSMul
  signature: (u : Intˣ) (w : NormalWord d)
  body: letI := Classical.dec
  if h : Cancels u w
  then unitsSMulWithCancel φ u w h
  else let g' := unitsSMulGroup φ d u w.head
    cons g'.1 u ((g'.2 * w.head⁻¹ : G) • w)
      (by simp)
      (by
        simp only [g', group_smul_toList, Option.mem_def, Option.map_eq_some_iff, Prod.exists,
          exists_and_right, exists_eq_right, group_smul_head, inv_mul_cancel_right,
          forall_exists_index, unitsSMulGroup]
        simp only [Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        intro u' x hx hmem
        have : w.head in toSubgroup A B u := by
          have := (d.compl u).rightCosetEquivalence_equiv_snd w.head
          rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [mul_mem_cancel_left hmem] at this
          simp_all
        have := h this x
        simp_all [Int.units_ne_iff_eq_neg])

中文:
定义 unitsSMul
  签名: (u : 整数ˣ) (w : NormalWord d)
  定义体: letI := Classical.dec
  if h : Cancels u w
  then unitsSMulWithCancel φ u w h
  else let g' := unitsSMulGroup φ d u w.head
    cons g'.1 u ((g'.2 * w.head⁻¹ : G) • w)
      (by simp)
      (by
        simp only [g', group_smul_toList, Option.mem_def, Option.map_eq_some_iff, Prod.exists,
          exists_and_right, exists_eq_right, group_smul_head, inv_mul_cancel_right,
          forall_exists_index, unitsSMulGroup]
        simp only [Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        intro u' x hx hmem
        have : w.head in toSubgroup A B u := by
          have := (d.compl u).rightCosetEquivalence_equiv_snd w.head
          rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [mul_mem_cancel_left hmem] at this
          simp_all
        have := h this x
        simp_all [Int.units_ne_iff_eq_neg])

Depends on / 依赖: Cancels, Classical, Classical.dec, Option.map_eq_some_iff, Option.mem_def, Prod.exists, exists_and_right, exists_eq_right, forall_exists_index, group_smul_head, group_smul_toList, inv_mul_cancel_right, map_eq_some_iff, mem_def, not_and, not_exists, unitsSMulGroup, unitsSMulWithCancel, w.head
-/
noncomputable def unitsSMul (u : Intˣ) (w : NormalWord d) : NormalWord d :=
  letI := Classical.dec
  if h : Cancels u w
  then unitsSMulWithCancel φ u w h
  else let g' := unitsSMulGroup φ d u w.head
    cons g'.1 u ((g'.2 * w.head⁻¹ : G) • w)
      (by simp)
      (by
        simp only [g', group_smul_toList, Option.mem_def, Option.map_eq_some_iff, Prod.exists,
          exists_and_right, exists_eq_right, group_smul_head, inv_mul_cancel_right,
          forall_exists_index, unitsSMulGroup]
        simp only [Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right,
          not_and, not_exists] at h
        intro u' x hx hmem
        have : w.head in toSubgroup A B u := by
          have := (d.compl u).rightCosetEquivalence_equiv_snd w.head
          rw [RightCosetEquivalence]; rw [rightCoset_eq_iff]; rw [mul_mem_cancel_left hmem] at this
          simp_all
        have := h this x
        simp_all [Int.units_ne_iff_eq_neg])

/--
theorem `not_cancels_of_cons_hyp` / 定理 `not_cancels_of_cons_hyp`

English:
theorem not_cancels_of_cons_hyp
  statement: (u : Intˣ) (w : NormalWord d)
  proof: by
  simp only [Cancels, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  simpa using h2 (-u) rfl hw

中文:
定理 not_cancels_of_cons_hyp
  结论: (u : 整数ˣ) (w : NormalWord d)
  证明: by
  simp only [Cancels, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  simpa using h2 (-u) rfl hw

Depends on / 依赖: Cancels, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right, map_eq_some_iff, not_and, not_exists
-/
theorem not_cancels_of_cons_hyp (u : Intˣ) (w : NormalWord d)
    (h2 : forall u' in Option.map Prod.fst w.toList.head?,
      w.head in toSubgroup A B u -> u = u') :
    ¬ Cancels u w := by
  simp only [Cancels, Option.map_eq_some_iff, Prod.exists,
    exists_and_right, exists_eq_right, not_and, not_exists]
  intro hw x hx
  rw [hx] at h2
  simpa using h2 (-u) rfl hw

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unitsSMul_cancels_iff` / 定理 `unitsSMul_cancels_iff`

English:
theorem unitsSMul_cancels_iff
  given: (u : Intˣ) (w : NormalWord d)
  proof: by
  by_cases h : Cancels u w
  · simp only [unitsSMul, h, dite_true, not_true_eq_false, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitsSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyp _ _ h2
      simp only [Cancels, cons_head, cons_toList, List.head?_cons,
        Option.map_some, Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitsSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitsSMul, dif_neg h]
    simpa [Cancels] using h

中文:
定理 unitsSMul_cancels_iff
  条件: (u : 整数ˣ) (w : NormalWord d)
  证明: by
  by_cases h : Cancels u w
  · simp only [unitsSMul, h, dite_true, not_true_eq_false, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitsSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyp _ _ h2
      simp only [Cancels, cons_head, cons_toList, List.head?_cons,
        Option.map_some, Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitsSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitsSMul, dif_neg h]
    simpa [Cancels] using h

Depends on / 依赖: Cancels, List.head, Option.map_some, Option.some.injEq, Subgroup, Subgroup.mul_mem_cancel_left, _cons, consRecOn, cons_head, cons_toList, dif_neg, dite_true, iff_false, map_some, mul_mem_cancel_left, not_cancels_of_cons_hyp, not_true_eq_false, ofGroup, unitsSMul, unitsSMulWithCancel
-/
theorem unitsSMul_cancels_iff (u : Intˣ) (w : NormalWord d) :
    Cancels (-u) (unitsSMul φ u w) ↔ ¬ Cancels u w := by
  by_cases h : Cancels u w
  · simp only [unitsSMul, h, dite_true, not_true_eq_false, iff_false]
    induction w using consRecOn with
    | ofGroup => simp [Cancels, unitsSMulWithCancel]
    | cons g u' w h1 h2 _ =>
      intro hc
      apply not_cancels_of_cons_hyp _ _ h2
      simp only [Cancels, cons_head, cons_toList, List.head?_cons,
        Option.map_some, Option.some.injEq] at h
      cases h.2
      simpa [Cancels, unitsSMulWithCancel,
        Subgroup.mul_mem_cancel_left] using hc
  · simp only [unitsSMul, dif_neg h]
    simpa [Cancels] using h

/--
theorem `unitsSMul_neg` / 定理 `unitsSMul_neg`

English:
theorem unitsSMul_neg
  given: (u : Intˣ) (w : NormalWord d)
  proof: by
  rw [unitsSMul]
  split_ifs with hcan
  · set_option backward.isDefEq.respectTransparency false in
    have hncan : ¬ Cancels u w := (unitsSMul_cancels_iff _ _ _).1 hcan
    unfold unitsSMul
    simp only [dif_neg hncan]
    simp [unitsSMulWithCancel, unitsSMulGroup, (d.compl u).equiv_snd_eq_inv_mul,
      -SetLike.coe_sort_coe]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitsSMul_cancels_iff _ _ _).2 hcan)
    unfold unitsSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp only [unitsSMulGroup, SetLike.coe_sort_coe, unitsSMulWithCancel, consRecOn_cons,
        group_smul_head,
        mul_inv_rev]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.head).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      simpa [NormalWord.ext_iff, (d.compl (-u)).equiv_mul_left, Units.ext_iff,
        (d.compl (-u)).equiv_snd_eq_inv_mul]

中文:
定理 unitsSMul_neg
  条件: (u : 整数ˣ) (w : NormalWord d)
  证明: by
  rw [unitsSMul]
  split_ifs with hcan
  · set_option backward.isDefEq.respectTransparency false in
    have hncan : ¬ Cancels u w := (unitsSMul_cancels_iff _ _ _).1 hcan
    unfold unitsSMul
    simp only [dif_neg hncan]
    simp [unitsSMulWithCancel, unitsSMulGroup, (d.compl u).equiv_snd_eq_inv_mul,
      -SetLike.coe_sort_coe]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitsSMul_cancels_iff _ _ _).2 hcan)
    unfold unitsSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp only [unitsSMulGroup, SetLike.coe_sort_coe, unitsSMulWithCancel, consRecOn_cons,
        group_smul_head,
        mul_inv_rev]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.head).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      simpa [NormalWord.ext_iff, (d.compl (-u)).equiv_mul_left, Units.ext_iff,
        (d.compl (-u)).equiv_snd_eq_inv_mul]

Depends on / 依赖: Cancels, SetLike, SetLike.coe_sort_coe, backward, backward.isDefEq.respectTransparency, coe_sort_coe, consRecOn, d.compl, dif_neg, dif_pos, equiv_snd_eq_inv_mul, isDefEq, not_not, ofGroup, respectTransparency, set_option, split_ifs, unitsSMul, unitsSMulGroup, unitsSMulWithCancel
-/
theorem unitsSMul_neg (u : Intˣ) (w : NormalWord d) :
    unitsSMul φ (-u) (unitsSMul φ u w) = w := by
  rw [unitsSMul]
  split_ifs with hcan
  · set_option backward.isDefEq.respectTransparency false in
    have hncan : ¬ Cancels u w := (unitsSMul_cancels_iff _ _ _).1 hcan
    unfold unitsSMul
    simp only [dif_neg hncan]
    simp [unitsSMulWithCancel, unitsSMulGroup, (d.compl u).equiv_snd_eq_inv_mul,
      -SetLike.coe_sort_coe]
  · have hcan2 : Cancels u w := not_not.1 (mt (unitsSMul_cancels_iff _ _ _).2 hcan)
    unfold unitsSMul at hcan ⊢
    simp only [dif_pos hcan2] at hcan ⊢
    cases w using consRecOn with
    | ofGroup => simp [Cancels] at hcan2
    | cons g u' w h1 h2 ih =>
      clear ih
      simp only [unitsSMulGroup, SetLike.coe_sort_coe, unitsSMulWithCancel, consRecOn_cons,
        group_smul_head,
        mul_inv_rev]
      cases hcan2.2
      have : ((d.compl (-u)).equiv w.head).1 = 1 :=
        (d.compl (-u)).equiv_fst_eq_one_of_mem_of_one_mem _ h1
      simpa [NormalWord.ext_iff, (d.compl (-u)).equiv_mul_left, Units.ext_iff,
        (d.compl (-u)).equiv_snd_eq_inv_mul]

/-- the equivalence given by multiplication on the left by `t` -/
@[simps]
/--
Definition of `unitsSMulEquiv` / `unitsSMulEquiv` 的定义

English:
definition unitsSMulEquiv
  signature: : NormalWord d ≃ NormalWord d
  body: { toFun := unitsSMul φ 1
    invFun := unitsSMul φ (-1),
    left_inv := fun _ => by rw [unitsSMul_neg]
    right_inv := fun w => by convert! unitsSMul_neg _ _ w; simp }

中文:
定义 unitsSMulEquiv
  签名: : NormalWord d ≃ NormalWord d
  定义体: { toFun := unitsSMul φ 1
    invFun := unitsSMul φ (-1),
    left_inv := fun _ => by rw [unitsSMul_neg]
    right_inv := fun w => by convert! unitsSMul_neg _ _ w; simp }

Depends on / 依赖: convert, invFun, left_inv, right_inv, unitsSMul, unitsSMul_neg
-/
noncomputable def unitsSMulEquiv : NormalWord d ≃ NormalWord d :=
  { toFun := unitsSMul φ 1
    invFun := unitsSMul φ (-1),
    left_inv := fun _ => by rw [unitsSMul_neg]
    right_inv := fun w => by convert! unitsSMul_neg _ _ w; simp }

set_option backward.isDefEq.respectTransparency false in
/--
theorem `unitsSMul_one_group_smul` / 定理 `unitsSMul_one_group_smul`

English:
theorem unitsSMul_one_group_smul
  given: (g : A) (w : NormalWord d)
  proof: by
  unfold unitsSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp only [unitsSMulWithCancel, toSubgroup_one, id_eq, toSubgroup_neg_one, toSubgroupEquiv_one,
      group_smul_head, mul_inv_rev, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons]
      rw [← mul_smul]; rw [← Subgroup.coe_mul]; rw [← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    -- Before https://github.com/leanprover/lean4/pull/2644, all this was just
    -- `simp [← mul_smul, mul_assoc, unitsSMulGroup]`
    simp +instances only [toSubgroup_neg_one, unitsSMulGroup, toSubgroup_one, toSubgroupEquiv_one,
      SetLike.coe_sort_coe, group_smul_head, mul_inv_rev, ← mul_smul, mul_assoc, inv_mul_cancel,
      mul_one, smul_cons]
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    congr 1
    · conv_lhs => erw [IsComplement.equiv_mul_left]
      simp_rw [toSubgroup_one]
      simp only [SetLike.coe_sort_coe, map_mul, Subgroup.coe_mul]
    conv_lhs => erw [IsComplement.equiv_mul_left]
    rfl

中文:
定理 unitsSMul_one_group_smul
  条件: (g : A) (w : NormalWord d)
  证明: by
  unfold unitsSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp only [unitsSMulWithCancel, toSubgroup_one, id_eq, toSubgroup_neg_one, toSubgroupEquiv_one,
      group_smul_head, mul_inv_rev, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons]
      rw [← mul_smul]; rw [← Subgroup.coe_mul]; rw [← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    -- Before https://github.com/leanprover/lean4/pull/2644, all this was just
    -- `simp [← mul_smul, mul_assoc, unitsSMulGroup]`
    simp +instances only [toSubgroup_neg_one, unitsSMulGroup, toSubgroup_one, toSubgroupEquiv_one,
      SetLike.coe_sort_coe, group_smul_head, mul_inv_rev, ← mul_smul, mul_assoc, inv_mul_cancel,
      mul_one, smul_cons]
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    congr 1
    · conv_lhs => erw [IsComplement.equiv_mul_left]
      simp_rw [toSubgroup_one]
      simp only [SetLike.coe_sort_coe, map_mul, Subgroup.coe_mul]
    conv_lhs => erw [IsComplement.equiv_mul_left]
    rfl

Depends on / 依赖: Cancels, Subgroup, Subgroup.coe_mul, Subgroup.mul_mem_cancel_left, coe_mul, consRecOn, consRecOn_cons, dif_neg, dif_pos, group_smul_head, id_eq, map_mul, mul_inv_rev, mul_mem_cancel_left, mul_smul, smul_cons, toSubgroupEquiv_one, toSubgroup_neg_one, toSubgroup_one, unitsSMul
-/
theorem unitsSMul_one_group_smul (g : A) (w : NormalWord d) :
    unitsSMul φ 1 ((g : G) • w) = (φ g : G) • (unitsSMul φ 1 w) := by
  unfold unitsSMul
  have : Cancels 1 ((g : G) • w) ↔ Cancels 1 w := by
    simp [Cancels, Subgroup.mul_mem_cancel_left]
  by_cases hcan : Cancels 1 w
  · simp only [unitsSMulWithCancel, toSubgroup_one, id_eq, toSubgroup_neg_one, toSubgroupEquiv_one,
      group_smul_head, mul_inv_rev, dif_pos (this.2 hcan), dif_pos hcan]
    cases w using consRecOn
    · simp [Cancels] at hcan
    · simp only [smul_cons, consRecOn_cons]
      rw [← mul_smul]; rw [← Subgroup.coe_mul]; rw [← map_mul φ]
      rfl
  · rw [dif_neg (mt this.1 hcan), dif_neg hcan]
    -- Before https://github.com/leanprover/lean4/pull/2644, all this was just
    -- `simp [← mul_smul, mul_assoc, unitsSMulGroup]`
    simp +instances only [toSubgroup_neg_one, unitsSMulGroup, toSubgroup_one, toSubgroupEquiv_one,
      SetLike.coe_sort_coe, group_smul_head, mul_inv_rev, ← mul_smul, mul_assoc, inv_mul_cancel,
      mul_one, smul_cons]
    -- This used to be the end of the proof before https://github.com/leanprover/lean4/pull/2644
    congr 1
    · conv_lhs => erw [IsComplement.equiv_mul_left]
      simp_rw [toSubgroup_one]
      simp only [SetLike.coe_sort_coe, map_mul, Subgroup.coe_mul]
    conv_lhs => erw [IsComplement.equiv_mul_left]
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction (HNNExtension G A B φ) (NormalWord d)
  body: MulAction.ofEndHom (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitsSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitsSMul_one_group_smul])

@[simp]

中文:
实例 :
  签名: 乘法作用 (HNNExtension G A B φ) (NormalWord d)
  定义体: MulAction.ofEndHom (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitsSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitsSMul_one_group_smul])

@[simp]

Depends on / 依赖: Equiv.Perm, HNNExtension, HNNExtension.lift, MulAction, MulAction.ofEndHom, MulAction.toEndHom, MulAction.toPermHom, NormalWord, ofEndHom, toEndHom, toPermHom, unitsSMulEquiv, unitsSMul_one_group_smul
-/
noncomputable instance : MulAction (HNNExtension G A B φ) (NormalWord d) :=
MulAction.ofEndHom (MulAction.toEndHom (M := Equiv.Perm (NormalWord d))).comp
    (HNNExtension.lift (MulAction.toPermHom _ _) (unitsSMulEquiv φ) <| by
      intro a
      ext : 1
      simp [unitsSMul_one_group_smul])

@[simp]
/--
theorem `prod_group_smul` / 定理 `prod_group_smul`

English:
theorem prod_group_smul
  given: (g : G) (w : NormalWord d)
  proof: by
  simp [ReducedWord.prod, mul_assoc]

中文:
定理 prod_group_smul
  条件: (g : G) (w : NormalWord d)
  证明: by
  simp [ReducedWord.prod, mul_assoc]

Depends on / 依赖: ReducedWord, ReducedWord.prod, mul_assoc
-/
theorem prod_group_smul (g : G) (w : NormalWord d) :
    (g • w).prod φ = of g * (w.prod φ) := by
  simp [ReducedWord.prod, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_smul_eq_smul` / 定理 `of_smul_eq_smul`

English:
theorem of_smul_eq_smul
  given: (g : G) (w : NormalWord d)
  proof: by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

中文:
定理 of_smul_eq_smul
  条件: (g : G) (w : NormalWord d)
  证明: by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

Depends on / 依赖: MulAction, MulAction.toEndHom, SMul.smul, instHSMul, instances, toEndHom
-/
theorem of_smul_eq_smul (g : G) (w : NormalWord d) :
    (of g : HNNExtension G A B φ) • w = g • w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `t_smul_eq_unitsSMul` / 定理 `t_smul_eq_unitsSMul`

English:
theorem t_smul_eq_unitsSMul
  given: (w : NormalWord d)
  proof: by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

中文:
定理 t_smul_eq_unitsSMul
  条件: (w : NormalWord d)
  证明: by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

Depends on / 依赖: MulAction, MulAction.toEndHom, SMul.smul, instHSMul, instances, toEndHom
-/
theorem t_smul_eq_unitsSMul (w : NormalWord d) :
    (t : HNNExtension G A B φ) • w = unitsSMul φ 1 w := by
  simp +instances [instHSMul, SMul.smul, MulAction.toEndHom]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `t_pow_smul_eq_unitsSMul` / 定理 `t_pow_smul_eq_unitsSMul`

English:
theorem t_pow_smul_eq_unitsSMul
  given: (u : Intˣ) (w : NormalWord d)
  proof: by
  rcases Int.units_eq_one_or u with (rfl | rfl) <;>
    simp +instances [instHSMul, SMul.smul, MulAction.toEndHom, Equiv.Perm.inv_def]

@[simp]

中文:
定理 t_pow_smul_eq_unitsSMul
  条件: (u : 整数ˣ) (w : NormalWord d)
  证明: by
  rcases Int.units_eq_one_or u with (rfl | rfl) <;>
    simp +instances [instHSMul, SMul.smul, MulAction.toEndHom, Equiv.Perm.inv_def]

@[simp]

Depends on / 依赖: Equiv.Perm.inv_def, Int.units_eq_one_or, MulAction, MulAction.toEndHom, SMul.smul, instHSMul, instances, inv_def, toEndHom, units_eq_one_or
-/
theorem t_pow_smul_eq_unitsSMul (u : Intˣ) (w : NormalWord d) :
    (t ^ (u : Int) : HNNExtension G A B φ) • w = unitsSMul φ u w := by
  rcases Int.units_eq_one_or u with (rfl | rfl) <;>
    simp +instances [instHSMul, SMul.smul, MulAction.toEndHom, Equiv.Perm.inv_def]

@[simp]
/--
theorem `prod_cons` / 定理 `prod_cons`

English:
theorem prod_cons
  statement: (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  proof: by
  simp [ReducedWord.prod, cons, mul_assoc]

中文:
定理 prod_cons
  结论: (g : G) (u : 整数ˣ) (w : NormalWord d) (h1 : w.head in d.set u)
  证明: by
  simp [ReducedWord.prod, cons, mul_assoc]

Depends on / 依赖: ReducedWord, ReducedWord.prod, mul_assoc
-/
theorem prod_cons (g : G) (u : Intˣ) (w : NormalWord d) (h1 : w.head in d.set u)
    (h2 : forall u' in Option.map Prod.fst w.toList.head?,
      w.head in toSubgroup A B u -> u = u') :
    (cons g u w h1 h2).prod φ = of g * (t ^ (u : Int) * w.prod φ) := by
  simp [ReducedWord.prod, cons, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `prod_unitsSMul` / 定理 `prod_unitsSMul`

English:
theorem prod_unitsSMul
  given: (u : Intˣ) (w : NormalWord d)
  proof: by
  rw [unitsSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp only [unitsSMulWithCancel, id_eq, consRecOn_cons, prod_group_smul, prod_cons, zpow_neg]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
        -- simp [equiv_symm_eq_conj, mul_assoc].
        simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
          Int.reduceNeg, zpow_neg, zpow_one, inv_inv]
        erw [equiv_symm_eq_conj, mul_assoc, mul_assoc]
  · simp only [unitsSMulGroup, SetLike.coe_sort_coe, prod_cons, prod_group_smul, map_mul, map_inv]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul].
      simp only [toSubgroup_neg_one, toSubgroup_one, toSubgroupEquiv_one, equiv_eq_conj, mul_assoc,
        Units.val_one, zpow_one, inv_mul_cancel_left, mul_right_inj]
      erw [(d.compl 1).equiv_snd_eq_inv_mul]
      simp [mul_assoc]
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
      simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
        Int.reduceNeg, zpow_neg, zpow_one, mul_assoc]
      erw [equiv_symm_eq_conj, (d.compl (-1)).equiv_snd_eq_inv_mul]
      simp [mul_assoc]

@[simp]

中文:
定理 prod_unitsSMul
  条件: (u : 整数ˣ) (w : NormalWord d)
  证明: by
  rw [unitsSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp only [unitsSMulWithCancel, id_eq, consRecOn_cons, prod_group_smul, prod_cons, zpow_neg]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
        -- simp [equiv_symm_eq_conj, mul_assoc].
        simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
          Int.reduceNeg, zpow_neg, zpow_one, inv_inv]
        erw [equiv_symm_eq_conj, mul_assoc, mul_assoc]
  · simp only [unitsSMulGroup, SetLike.coe_sort_coe, prod_cons, prod_group_smul, map_mul, map_inv]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul].
      simp only [toSubgroup_neg_one, toSubgroup_one, toSubgroupEquiv_one, equiv_eq_conj, mul_assoc,
        Units.val_one, zpow_one, inv_mul_cancel_left, mul_right_inj]
      erw [(d.compl 1).equiv_snd_eq_inv_mul]
      simp [mul_assoc]
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
      simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
        Int.reduceNeg, zpow_neg, zpow_one, mul_assoc]
      erw [equiv_symm_eq_conj, (d.compl (-1)).equiv_snd_eq_inv_mul]
      simp [mul_assoc]

@[simp]

Depends on / 依赖: Before, Cancels, Int.units_eq_one_or, consRecOn, consRecOn_cons, equiv_eq_conj, github, github.com, id_eq, leanprover, mul_assoc, prod_cons, prod_group_smul, split_ifs, unitsSMul, unitsSMulWithCancel, units_eq_one_or, zpow_neg
-/
theorem prod_unitsSMul (u : Intˣ) (w : NormalWord d) :
    (unitsSMul φ u w).prod φ = (t ^ (u : Int) * w.prod φ : HNNExtension G A B φ) := by
  rw [unitsSMul]
  split_ifs with hcan
  · cases w using consRecOn
    · simp [Cancels] at hcan
    · cases hcan.2
      simp only [unitsSMulWithCancel, id_eq, consRecOn_cons, prod_group_smul, prod_cons, zpow_neg]
      rcases Int.units_eq_one_or u with (rfl | rfl)
      · simp [equiv_eq_conj, mul_assoc]
      · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
        -- simp [equiv_symm_eq_conj, mul_assoc].
        simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
          Int.reduceNeg, zpow_neg, zpow_one, inv_inv]
        erw [equiv_symm_eq_conj, mul_assoc, mul_assoc]
  · simp only [unitsSMulGroup, SetLike.coe_sort_coe, prod_cons, prod_group_smul, map_mul, map_inv]
    rcases Int.units_eq_one_or u with (rfl | rfl)
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul].
      simp only [toSubgroup_neg_one, toSubgroup_one, toSubgroupEquiv_one, equiv_eq_conj, mul_assoc,
        Units.val_one, zpow_one, inv_mul_cancel_left, mul_right_inj]
      erw [(d.compl 1).equiv_snd_eq_inv_mul]
      simp [mul_assoc]
    · -- Before https://github.com/leanprover/lean4/pull/2644, this proof was just
      -- simp [equiv_symm_eq_conj, mul_assoc, (d.compl _).equiv_snd_eq_inv_mul]
      simp only [toSubgroup_neg_one, toSubgroupEquiv_neg_one, Units.val_neg, Units.val_one,
        Int.reduceNeg, zpow_neg, zpow_one, mul_assoc]
      erw [equiv_symm_eq_conj, (d.compl (-1)).equiv_snd_eq_inv_mul]
      simp [mul_assoc]

@[simp]
/--
theorem `prod_empty` / 定理 `prod_empty`

English:
theorem prod_empty
  statement: (empty : NormalWord d).prod φ = 1
  proof: by
  simp [ReducedWord.prod]

@[simp]

中文:
定理 prod_empty
  结论: (empty : NormalWord d).乘积 φ = 1
  证明: by
  simp [ReducedWord.prod]

@[simp]

Depends on / 依赖: ReducedWord, ReducedWord.prod
-/
theorem prod_empty : (empty : NormalWord d).prod φ = 1 := by
  simp [ReducedWord.prod]

@[simp]
/--
theorem `prod_smul` / 定理 `prod_smul`

English:
theorem prod_smul
  given: (g : HNNExtension G A B φ) (w : NormalWord d)
  proof: by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    rw [← mul_right_inj x]; rw [← ih]
    simp

@[simp]

中文:
定理 prod_smul
  条件: (g : HNNExtension G A B φ) (w : NormalWord d)
  证明: by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    rw [← mul_right_inj x]; rw [← ih]
    simp

@[simp]

Depends on / 依赖: generalizing, induction_on, mul_assoc, mul_right_inj, mul_smul, of_smul_eq_smul, prod_unitsSMul, t_smul_eq_unitsSMul
-/
theorem prod_smul (g : HNNExtension G A B φ) (w : NormalWord d) :
    (g • w).prod φ = g * w.prod φ := by
  induction g using induction_on generalizing w with
  | of => simp [of_smul_eq_smul]
  | t => simp [t_smul_eq_unitsSMul, prod_unitsSMul]
  | mul => simp_all [mul_smul, mul_assoc]
  | inv x ih =>
    rw [← mul_right_inj x]; rw [← ih]
    simp

@[simp]
/--
theorem `prod_smul_empty` / 定理 `prod_smul_empty`

English:
theorem prod_smul_empty
  given: (w : NormalWord d)
  proof: by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, ReducedWord.prod, of_smul_eq_smul, group_smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons]; rw [← mul_assoc]; rw [mul_smul]; rw [ih]; rw [mul_smul]; rw [t_pow_smul_eq_unitsSMul]; rw [of_smul_eq_smul]; rw [unitsSMul]
    rw [dif_neg (not_cancels_of_cons_hyp u w h2)]
    -- Before https://github.com/leanprover/lean4/pull/2644, this was just
    -- simp [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
    -- -SetLike.coe_sort_coe]
    -- ext <;> simp [-SetLike.coe_sort_coe]
    simp only [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
      (d.compl _).equiv_snd_eq_inv_mul, inv_one, one_mul, mul_inv_cancel, one_smul, smul_cons]
    ext <;> simp

中文:
定理 prod_smul_empty
  条件: (w : NormalWord d)
  证明: by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, ReducedWord.prod, of_smul_eq_smul, group_smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons]; rw [← mul_assoc]; rw [mul_smul]; rw [ih]; rw [mul_smul]; rw [t_pow_smul_eq_unitsSMul]; rw [of_smul_eq_smul]; rw [unitsSMul]
    rw [dif_neg (not_cancels_of_cons_hyp u w h2)]
    -- Before https://github.com/leanprover/lean4/pull/2644, this was just
    -- simp [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
    -- -SetLike.coe_sort_coe]
    -- ext <;> simp [-SetLike.coe_sort_coe]
    simp only [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
      (d.compl _).equiv_snd_eq_inv_mul, inv_one, one_mul, mul_inv_cancel, one_smul, smul_cons]
    ext <;> simp

Depends on / 依赖: ReducedWord, ReducedWord.prod, consRecOn, dif_neg, group_smul_def, mul_assoc, mul_smul, not_cancels_of_cons_hyp, ofGroup, of_smul_eq_smul, prod_cons, t_pow_smul_eq_unitsSMul, unitsSMul
-/
theorem prod_smul_empty (w : NormalWord d) :
    (w.prod φ) • empty = w := by
  induction w using consRecOn with
  | ofGroup => simp [ofGroup, ReducedWord.prod, of_smul_eq_smul, group_smul_def]
  | cons g u w h1 h2 ih =>
    rw [prod_cons]; rw [← mul_assoc]; rw [mul_smul]; rw [ih]; rw [mul_smul]; rw [t_pow_smul_eq_unitsSMul]; rw [of_smul_eq_smul]; rw [unitsSMul]
    rw [dif_neg (not_cancels_of_cons_hyp u w h2)]
    -- Before https://github.com/leanprover/lean4/pull/2644, this was just
    -- simp [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
    -- -SetLike.coe_sort_coe]
    -- ext <;> simp [-SetLike.coe_sort_coe]
    simp only [unitsSMulGroup, (d.compl _).equiv_fst_eq_one_of_mem_of_one_mem (one_mem _) h1,
      (d.compl _).equiv_snd_eq_inv_mul, inv_one, one_mul, mul_inv_cancel, one_smul, smul_cons]
    ext <;> simp

variable (d)
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: : HNNExtension G A B φ ≃ NormalWord d
  body: { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }

中文:
定义 equiv
  签名: : HNNExtension G A B φ ≃ NormalWord d
  定义体: { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }

Depends on / 依赖: invFun, left_inv, prod_smul, right_inv, w.prod
-/
noncomputable def equiv : HNNExtension G A B φ ≃ NormalWord d :=
  { toFun := fun g => g • empty,
    invFun := fun w => w.prod φ,
    left_inv := fun g => by simp [prod_smul]
    right_inv := fun w => by simp }

/--
theorem `prod_injective` / 定理 `prod_injective`

English:
theorem prod_injective
  statement: Injective
  proof: (equiv φ d).symm.injective

中文:
定理 prod_injective
  结论: 单射
  证明: (equiv φ d).symm.injective

Depends on / 依赖: injective, symm.injective
-/
theorem prod_injective : Injective
    (fun w => w.prod φ : NormalWord d -> HNNExtension G A B φ) :=
  (equiv φ d).symm.injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FaithfulSMul (HNNExtension G A B φ) (NormalWord d)
  body: ⟨fun h => by simpa using congr_arg (fun w => w.prod φ) (h empty)⟩

中文:
实例 :
  签名: 忠实标量乘法 (HNNExtension G A B φ) (NormalWord d)
  定义体: ⟨fun h => by simpa using congr_arg (fun w => w.prod φ) (h empty)⟩

Depends on / 依赖: congr_arg, w.prod
-/
instance : FaithfulSMul (HNNExtension G A B φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg (fun w => w.prod φ) (h empty)⟩

end NormalWord

open NormalWord

/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  statement: Function.Injective (of : G -> HNNExtension G A B φ)
  proof: by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((· • ·) : HNNExtension G A B φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

中文:
定理 of_injective
  结论: 函数.单射 (of : G -> HNNExtension G A B φ)
  证明: by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((· • ·) : HNNExtension G A B φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

Depends on / 依赖: Function, Function.Injective.of_comp, HNNExtension, Injective, NormalWord, TransversalPair, TransversalPair.nonempty, eq_of_smul_eq_smul, funext_iff, nonempty, of_comp, of_smul_eq_smul
-/
theorem of_injective : Function.Injective (of : G -> HNNExtension G A B φ) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  refine Function.Injective.of_comp
    (f := ((· • ·) : HNNExtension G A B φ -> NormalWord d -> NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])

namespace ReducedWord

/--
theorem `exists_normalWord_prod_eq` / 定理 `exists_normalWord_prod_eq`

English:
theorem exists_normalWord_prod_eq
  proof: by
  suffices forall w : ReducedWord G A B,
      w.head = 1 -> exists w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      forall u in w.toList.head?.map Prod.fst,
      w'.head in toSubgroup A B (-u) by
    by_cases hw1 : w.head = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases this ⟨1, w.toList, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.head • w', by
        simpa [ReducedWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ head := 1
         toList := []
         mem_set := by simp
         chain := List.isChain_nil }, by simp⟩
  | cons a l ih =>
    rcases ih (List.isChain_cons.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : Int) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, group_smul_head, group_smul_toList, Option.map_eq_some_iff,
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map]; rw [hw'2]; rw [List.head?_map]; rw [Option.map_some] at hx'
        have : w'.head in toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.fst = -a.fst := by
          have hl : l != [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.isChain_cons.1 chain).1 (l.head hl)
            (List.head?_eq_some_head _) hS
          rwa [List.head?_eq_some_head hl, Option.map_some, ← this, Option.some_inj] at hx'
        simp at this
      simp [mul_smul, of_smul_eq_smul, t_pow_smul_eq_unitsSMul, unitsSMul, dif_neg this, ← hw'2]

中文:
定理 存在_normalWord_prod_eq
  证明: by
  suffices forall w : ReducedWord G A B,
      w.head = 1 -> exists w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      forall u in w.toList.head?.map Prod.fst,
      w'.head in toSubgroup A B (-u) by
    by_cases hw1 : w.head = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases this ⟨1, w.toList, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.head • w', by
        simpa [ReducedWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ head := 1
         toList := []
         mem_set := by simp
         chain := List.isChain_nil }, by simp⟩
  | cons a l ih =>
    rcases ih (List.isChain_cons.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : Int) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, group_smul_head, group_smul_toList, Option.map_eq_some_iff,
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map]; rw [hw'2]; rw [List.head?_map]; rw [Option.map_some] at hx'
        have : w'.head in toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.fst = -a.fst := by
          have hl : l != [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.isChain_cons.1 chain).1 (l.head hl)
            (List.head?_eq_some_head _) hS
          rwa [List.head?_eq_some_head hl, Option.map_some, ← this, Option.some_inj] at hx'
        simp at this
      simp [mul_smul, of_smul_eq_smul, t_pow_smul_eq_unitsSMul, unitsSMul, dif_neg this, ← hw'2]

Depends on / 依赖: NormalWord, Prod.fst, ReducedWord, ReducedWord.prod, inv_mem_iff, mul_assoc, mul_one, toList, toList.map, toSubgroup, w.chain, w.head, w.prod, w.toList, w.toList.head, w.toList.map
-/
theorem exists_normalWord_prod_eq
    (d : TransversalPair G A B) (w : ReducedWord G A B) :
    exists w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      forall u in w.toList.head?.map Prod.fst,
      w'.head⁻¹ * w.head in toSubgroup A B (-u) := by
  suffices forall w : ReducedWord G A B,
      w.head = 1 -> exists w' : NormalWord d, w'.prod φ = w.prod φ ∧
      w'.toList.map Prod.fst = w.toList.map Prod.fst ∧
      forall u in w.toList.head?.map Prod.fst,
      w'.head in toSubgroup A B (-u) by
    by_cases hw1 : w.head = 1
    · simp only [hw1, inv_mem_iff, mul_one]
      exact this w hw1
    · rcases this ⟨1, w.toList, w.chain⟩ rfl with ⟨w', hw'⟩
      exact ⟨w.head • w', by
        simpa [ReducedWord.prod, mul_assoc] using hw'⟩
  intro w hw1
  rcases w with ⟨g, l, chain⟩
  dsimp at hw1; subst hw1
  induction l with
  | nil =>
    exact
      ⟨{ head := 1
         toList := []
         mem_set := by simp
         chain := List.isChain_nil }, by simp⟩
  | cons a l ih =>
    rcases ih (List.isChain_cons.1 chain).2 with ⟨w', hw'1, hw'2, hw'3⟩
    clear ih
    refine ⟨(t^(a.1 : Int) * of a.2 : HNNExtension G A B φ) • w', ?_, ?_⟩
    · rw [prod_smul, hw'1]
      simp [ReducedWord.prod]
    · have : ¬ Cancels a.1 (a.2 • w') := by
        simp only [Cancels, group_smul_head, group_smul_toList, Option.map_eq_some_iff,
          Prod.exists, exists_and_right, exists_eq_right, not_and, not_exists]
        intro hS x hx
        have hx' := congr_arg (Option.map Prod.fst) hx
        rw [← List.head?_map]; rw [hw'2]; rw [List.head?_map]; rw [Option.map_some] at hx'
        have : w'.head in toSubgroup A B a.fst := by
          simpa using hw'3 _ hx'
        rw [mul_mem_cancel_right this] at hS
        have : a.fst = -a.fst := by
          have hl : l != [] := by rintro rfl; simp_all
          have : a.fst = (l.head hl).fst := (List.isChain_cons.1 chain).1 (l.head hl)
            (List.head?_eq_some_head _) hS
          rwa [List.head?_eq_some_head hl, Option.map_some, ← this, Option.some_inj] at hx'
        simp at this
      simp [mul_smul, of_smul_eq_smul, t_pow_smul_eq_unitsSMul, unitsSMul, dif_neg this, ← hw'2]

/--
theorem `map_fst_eq_and_of_prod_eq` / 定理 `map_fst_eq_and_of_prod_eq`

English:
theorem map_fst_eq_and_of_prod_eq
  statement: {w₁ w₂ : ReducedWord G A B}
  proof: by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by dsimp only; rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu]; rw [← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

中文:
定理 map_fst_eq_and_of_prod_eq
  结论: {w₁ w₂ : ReducedWord G A B}
  证明: by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by dsimp only; rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu]; rw [← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

Depends on / 依赖: List.head, NormalWord, NormalWord.prod_injective, TransversalPair, TransversalPair.nonempty, _map, exists_normalWord_prod_eq, leftCoset_eq_iff, nonempty, prod_injective
-/
theorem map_fst_eq_and_of_prod_eq {w₁ w₂ : ReducedWord G A B}
    (hprod : w₁.prod φ = w₂.prod φ) :
    w₁.toList.map Prod.fst = w₂.toList.map Prod.fst ∧
     forall u in w₁.toList.head?.map Prod.fst,
      w₁.head⁻¹ * w₂.head in toSubgroup A B (-u) := by
  rcases TransversalPair.nonempty G A B with ⟨d⟩
  rcases exists_normalWord_prod_eq φ d w₁ with ⟨w₁', hw₁'1, hw₁'2, hw₁'3⟩
  rcases exists_normalWord_prod_eq φ d w₂ with ⟨w₂', hw₂'1, hw₂'2, hw₂'3⟩
  have : w₁' = w₂' :=
    NormalWord.prod_injective φ d (by dsimp only; rw [hw₁'1, hw₂'1, hprod])
  subst this
  refine ⟨by rw [← hw₁'2, hw₂'2], ?_⟩
  simp only [← leftCoset_eq_iff] at *
  intro u hu
  rw [← hw₁'3 _ hu]; rw [← hw₂'3 _]
  rwa [← List.head?_map, ← hw₂'2, hw₁'2, List.head?_map]

/--
theorem `toList_eq_nil_of_mem_of_range` / 定理 `toList_eq_nil_of_mem_of_range`

English:
theorem toList_eq_nil_of_mem_of_range
  statement: (w : ReducedWord G A B)
  proof: by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { ReducedWord.empty G A B with head := g }
  have : w.prod φ = w'.prod φ := by simp [w', ReducedWord.prod, hg]
  simpa [w'] using (map_fst_eq_and_of_prod_eq φ this).1

中文:
定理 toList_eq_nil_of_mem_of_range
  结论: (w : ReducedWord G A B)
  证明: by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { ReducedWord.empty G A B with head := g }
  have : w.prod φ = w'.prod φ := by simp [w', ReducedWord.prod, hg]
  simpa [w'] using (map_fst_eq_and_of_prod_eq φ this).1

Depends on / 依赖: ReducedWord, ReducedWord.empty, ReducedWord.prod, map_fst_eq_and_of_prod_eq, w.prod
-/
theorem toList_eq_nil_of_mem_of_range (w : ReducedWord G A B)
    (hw : w.prod φ in (of.range : Subgroup (HNNExtension G A B φ))) :
    w.toList = [] := by
  rcases hw with ⟨g, hg⟩
  let w' : ReducedWord G A B := { ReducedWord.empty G A B with head := g }
  have : w.prod φ = w'.prod φ := by simp [w', ReducedWord.prod, hg]
  simpa [w'] using (map_fst_eq_and_of_prod_eq φ this).1

end ReducedWord

end HNNExtension
