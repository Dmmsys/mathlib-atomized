/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-!
# Splitting fields

In this file we prove the existence and uniqueness of splitting fields.

## Main definitions

* `Polynomial.SplittingField f`: A fixed splitting field of the polynomial `f`.

## Main statements

* `Polynomial.IsSplittingField.algEquiv`: Every splitting field of a polynomial `f` is isomorphic
  to `SplittingField f` and thus, being a splitting field is unique up to isomorphism.

## Implementation details
We construct a `SplittingFieldAux` without worrying about whether the instances satisfy nice
definitional equalities. Then the actual `SplittingField` is defined to be a quotient of a
`MvPolynomial` ring by the kernel of the obvious map into `SplittingFieldAux`. Because the
actual `SplittingField` will be a quotient of a `MvPolynomial`, it has nice instances on it.

-/

@[expose] public section

noncomputable section

universe u v w

variable {F : Type u} {K : Type v} {L : Type w}

namespace Polynomial

variable [Field K] [Field L] [Field F]

open Polynomial

section SplittingField

open scoped Classical in
/--
Definition of `factor` / `factor` 的定义

English:
definition factor
  signature: (f : K[X])
  body: if H : exists g, Irreducible g ∧ g ∣ f then Classical.choose H else X

中文:
定义 factor
  签名: (f : K[X])
  定义体: if H : exists g, Irreducible g ∧ g ∣ f then Classical.choose H else X

Depends on / 依赖: Classical, Classical.choose, Irreducible
-/
def factor (f : K[X]) : K[X] :=
  if H : exists g, Irreducible g ∧ g ∣ f then Classical.choose H else X

/--
theorem `irreducible_factor` / 定理 `irreducible_factor`

English:
theorem irreducible_factor
  given: (f : K[X])
  statement: Irreducible (factor f)
  proof: by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

中文:
定理 irreducible_factor
  条件: (f : K[X])
  结论: 不可约 (factor f)
  证明: by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, factor, irreducible_X, split_ifs
-/
theorem irreducible_factor (f : K[X]) : Irreducible (factor f) := by
  rw [factor]
  split_ifs with H
  · exact (Classical.choose_spec H).1
  · exact irreducible_X

/--
theorem `fact_irreducible_factor` / 定理 `fact_irreducible_factor`

English:
theorem fact_irreducible_factor
  given: (f : K[X])
  statement: Fact (Irreducible (factor f))
  proof: ⟨irreducible_factor f⟩

中文:
定理 fact_irreducible_factor
  条件: (f : K[X])
  结论: Fact (不可约 (factor f))
  证明: ⟨irreducible_factor f⟩

Depends on / 依赖: irreducible_factor
-/
theorem fact_irreducible_factor (f : K[X]) : Fact (Irreducible (factor f)) :=
  ⟨irreducible_factor f⟩

attribute [local instance] fact_irreducible_factor

/--
theorem `factor_dvd_of_not_isUnit` / 定理 `factor_dvd_of_not_isUnit`

English:
theorem factor_dvd_of_not_isUnit
  given: {f : K[X]} (hf1 : ¬IsUnit f)
  statement: factor f ∣ f
  proof: by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor]; rw [dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

中文:
定理 factor_dvd_of_not_isUnit
  条件: {f : K[X]} (hf1 : ¬是单位 f)
  结论: factor f ∣ f
  证明: by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor]; rw [dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

Depends on / 依赖: Classical, Classical.choose_spec, WfDvdMonoid, WfDvdMonoid.exists_irreducible_factor, choose_spec, dif_pos, dvd_zero, exists_irreducible_factor, factor
-/
theorem factor_dvd_of_not_isUnit {f : K[X]} (hf1 : ¬IsUnit f) : factor f ∣ f := by
  by_cases hf2 : f = 0; · rw [hf2]; exact dvd_zero _
  rw [factor]; rw [dif_pos (WfDvdMonoid.exists_irreducible_factor hf1 hf2)]
  exact (Classical.choose_spec <| WfDvdMonoid.exists_irreducible_factor hf1 hf2).2

/--
theorem `factor_dvd_of_degree_ne_zero` / 定理 `factor_dvd_of_degree_ne_zero`

English:
theorem factor_dvd_of_degree_ne_zero
  given: {f : K[X]} (hf : f.degree != 0)
  statement: factor f ∣ f
  proof: factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)

中文:
定理 factor_dvd_of_degree_ne_zero
  条件: {f : K[X]} (hf : f.degree != 0)
  结论: factor f ∣ f
  证明: factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)

Depends on / 依赖: degree_eq_zero_of_isUnit, factor_dvd_of_not_isUnit
-/
theorem factor_dvd_of_degree_ne_zero {f : K[X]} (hf : f.degree != 0) : factor f ∣ f :=
  factor_dvd_of_not_isUnit (mt degree_eq_zero_of_isUnit hf)

/--
theorem `factor_dvd_of_natDegree_ne_zero` / 定理 `factor_dvd_of_natDegree_ne_zero`

English:
theorem factor_dvd_of_natDegree_ne_zero
  given: {f : K[X]} (hf : f.natDegree != 0)
  statement: factor f ∣ f
  proof: factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)

中文:
定理 factor_dvd_of_natDegree_ne_zero
  条件: {f : K[X]} (hf : f.natDegree != 0)
  结论: factor f ∣ f
  证明: factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)

Depends on / 依赖: factor_dvd_of_degree_ne_zero, natDegree_eq_of_degree_eq_some
-/
theorem factor_dvd_of_natDegree_ne_zero {f : K[X]} (hf : f.natDegree != 0) : factor f ∣ f :=
  factor_dvd_of_degree_ne_zero (mt natDegree_eq_of_degree_eq_some hf)

/--
lemma `isCoprime_iff_aeval_ne_zero` / 引理 `isCoprime_iff_aeval_ne_zero`

English:
lemma isCoprime_iff_aeval_ne_zero
  given: (f g : K[X])
  statement: IsCoprime f g ↔ forall {A : Type v} [CommRing A]
  proof: by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hx _ => ?_⟩
  · replace h := @h K _ _ _ 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
replace h := not_and_or.mpr h AdjoinRoot.root x.factor
    simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero,
dvd_mul_of_dvd_left factor_dvd_of_not_isUnit hx, true_and, not_true] at h

中文:
引理 isCoprime_iff_aeval_ne_zero
  条件: (f g : K[X])
  结论: IsCoprime f g ↔ 对任意 {A : 类型v} [交换环 A]
  证明: by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hx _ => ?_⟩
  · replace h := @h K _ _ _ 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
replace h := not_and_or.mpr h AdjoinRoot.root x.factor
    simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero,
dvd_mul_of_dvd_left factor_dvd_of_not_isUnit hx, true_and, not_true] at h

Depends on / 依赖: AdjoinRoot, AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero, AdjoinRoot.root, aeval_eq, aeval_ne_zero_of_isCoprime, and_self, contrapose, dvd_mul_of_dvd_left, factor, factor_dvd_of_not_isUnit, h.left, h.right, isCoprime_of_dvd, map_zero, mk_eq_zero, not_and_or, not_and_or.mpr, not_true, replace
-/
lemma isCoprime_iff_aeval_ne_zero (f g : K[X]) : IsCoprime f g ↔ forall {A : Type v} [CommRing A]
    [IsDomain A] [Algebra K A] (a : A), aeval a f != 0 ∨ aeval a g != 0 := by
  refine ⟨fun h => aeval_ne_zero_of_isCoprime h, fun h => isCoprime_of_dvd _ _ ?_ fun x hx _ => ?_⟩
  · replace h := @h K _ _ _ 0
    contrapose! h
    rw [h.left]; rw [h.right]; rw [map_zero]; rw [and_self]
  · rintro ⟨_, rfl⟩ ⟨_, rfl⟩
replace h := not_and_or.mpr h AdjoinRoot.root x.factor
    simp only [AdjoinRoot.aeval_eq, AdjoinRoot.mk_eq_zero,
dvd_mul_of_dvd_left factor_dvd_of_not_isUnit hx, true_and, not_true] at h

/--
Definition of `removeFactor` / `removeFactor` 的定义

English:
definition removeFactor
  signature: (f : K[X])
  body: map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

中文:
定义 removeFactor
  签名: (f : K[X])
  定义体: map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

Depends on / 依赖: AdjoinRoot, AdjoinRoot.of, AdjoinRoot.root, f.factor, factor
-/
def removeFactor (f : K[X]) : Polynomial (AdjoinRoot <| factor f) :=
  map (AdjoinRoot.of f.factor) f /ₘ (X - C (AdjoinRoot.root f.factor))

/--
theorem `X_sub_C_mul_removeFactor` / 定理 `X_sub_C_mul_removeFactor`

English:
theorem X_sub_C_mul_removeFactor
  given: (f : K[X]) (hf : f.natDegree != 0)
  proof: by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def]; rw [eval_map]; rw [hg]; rw [eval₂_mul]; rw [← hg]; rw [AdjoinRoot.eval₂_root]; rw [zero_mul]

中文:
定理 X_sub_C_mul_removeFactor
  条件: (f : K[X]) (hf : f.natDegree != 0)
  证明: by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def]; rw [eval_map]; rw [hg]; rw [eval₂_mul]; rw [← hg]; rw [AdjoinRoot.eval₂_root]; rw [zero_mul]

Depends on / 依赖: AdjoinRoot, AdjoinRoot.eval, AdjoinRoot.root, IsRoot, IsRoot.def, Subtype, Subtype.map, eval_map, f.factor, factor, factor_dvd_of_natDegree_ne_zero, mul_divByMonic_eq_iff_isRoot, smul_ne_zero_iff_ne, zero_mul
-/
theorem X_sub_C_mul_removeFactor (f : K[X]) (hf : f.natDegree != 0) :
    (X - C (AdjoinRoot.root f.factor)) * f.removeFactor = map (AdjoinRoot.of f.factor) f := by
  let ⟨g, hg⟩ := factor_dvd_of_natDegree_ne_zero hf
  apply (mul_divByMonic_eq_iff_isRoot
    (R := AdjoinRoot f.factor) (a := AdjoinRoot.root f.factor)).mpr
  rw [IsRoot.def]; rw [eval_map]; rw [hg]; rw [eval₂_mul]; rw [← hg]; rw [AdjoinRoot.eval₂_root]; rw [zero_mul]

/--
theorem `natDegree_removeFactor` / 定理 `natDegree_removeFactor`

English:
theorem natDegree_removeFactor
  given: (f : K[X])
  statement: f.removeFactor.natDegree = f.natDegree - 1
  proof: by
  rw [removeFactor]; rw [natDegree_divByMonic _ (monic_X_sub_C _)]; rw [natDegree_map]; rw [natDegree_X_sub_C]

中文:
定理 natDegree_removeFactor
  条件: (f : K[X])
  结论: f.removeFactor.natDegree = f.natDegree - 1
  证明: by
  rw [removeFactor]; rw [natDegree_divByMonic _ (monic_X_sub_C _)]; rw [natDegree_map]; rw [natDegree_X_sub_C]

Depends on / 依赖: monic_X_sub_C, natDegree_X_sub_C, natDegree_divByMonic, natDegree_map, removeFactor
-/
theorem natDegree_removeFactor (f : K[X]) : f.removeFactor.natDegree = f.natDegree - 1 := by
  rw [removeFactor]; rw [natDegree_divByMonic _ (monic_X_sub_C _)]; rw [natDegree_map]; rw [natDegree_X_sub_C]

/--
theorem `natDegree_removeFactor'` / 定理 `natDegree_removeFactor'`

English:
theorem natDegree_removeFactor'
  given: {f : K[X]} {n : Nat} (hfn : f.natDegree = n + 1)
  proof: by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

中文:
定理 natDegree_removeFactor'
  条件: {f : K[X]} {n : 自然数} (hfn : f.natDegree = n + 1)
  证明: by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

Depends on / 依赖: add_sub_cancel, n.add_sub_cancel, natDegree_removeFactor
-/
theorem natDegree_removeFactor' {f : K[X]} {n : Nat} (hfn : f.natDegree = n + 1) :
    f.removeFactor.natDegree = n := by rw [natDegree_removeFactor, hfn, n.add_sub_cancel]

/--
Definition of `SplittingFieldAuxAux` / `SplittingFieldAuxAux` 的定义

English:
definition SplittingFieldAuxAux
  signature: (n : Nat)
  body: -- Porting note: added motive
  Nat.recOn (motive := fun (_x : Nat) => forall {K : Type u} [_inst_4 : Field K], K[X] ->
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

中文:
定义 SplittingFieldAuxAux
  签名: (n : 自然数)
  定义体: -- Porting note: added motive
  Nat.recOn (motive := fun (_x : Nat) => forall {K : Type u} [_inst_4 : Field K], K[X] ->
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩
-/
def SplittingFieldAuxAux (n : Nat) : forall {K : Type u} [Field K], K[X] ->
    Σ (L : Type u) (_ : Field L), Algebra K L :=
  -- Porting note: added motive
  Nat.recOn (motive := fun (_x : Nat) => forall {K : Type u} [_inst_4 : Field K], K[X] ->
      Σ (L : Type u) (_ : Field L), Algebra K L) n
    (fun {K} _ _ => ⟨K, inferInstance, inferInstance⟩)
    fun _ ih _ _ f =>
      let ⟨L, fL, _⟩ := ih f.removeFactor
      ⟨L, fL, (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor)).toAlgebra⟩

/--
Definition of `SplittingFieldAux` / `SplittingFieldAux` 的定义

English:
definition SplittingFieldAux
  signature: (n : Nat) {K : Type u} [Field K] (f : K[X])
  body: (SplittingFieldAuxAux n f).1

中文:
定义 SplittingFieldAux
  签名: (n : 自然数) {K : 类型u} [域 K] (f : K[X])
  定义体: (SplittingFieldAuxAux n f).1

Depends on / 依赖: SplittingFieldAuxAux
-/
def SplittingFieldAux (n : Nat) {K : Type u} [Field K] (f : K[X]) : Type u :=
  (SplittingFieldAuxAux n f).1

/--
Instance `SplittingFieldAux.field` / 实例 `SplittingFieldAux.field`

English:
instance SplittingFieldAux.field
  signature: (n : Nat) {K : Type u} [Field K] (f : K[X])
  body: (SplittingFieldAuxAux n f).2.1

中文:
实例 SplittingFieldAux.field
  签名: (n : 自然数) {K : 类型u} [域 K] (f : K[X])
  定义体: (SplittingFieldAuxAux n f).2.1

Depends on / 依赖: SplittingFieldAuxAux
-/
instance SplittingFieldAux.field (n : Nat) {K : Type u} [Field K] (f : K[X]) :
    Field (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.1

instance (n : Nat) {K : Type u} [Field K] (f : K[X]) : Inhabited (SplittingFieldAux n f) :=
  ⟨0⟩

/--
Instance `SplittingFieldAux.algebra` / 实例 `SplittingFieldAux.algebra`

English:
instance SplittingFieldAux.algebra
  signature: (n : Nat) {K : Type u} [Field K] (f : K[X])
  body: (SplittingFieldAuxAux n f).2.2

中文:
实例 SplittingFieldAux.algebra
  签名: (n : 自然数) {K : 类型u} [域 K] (f : K[X])
  定义体: (SplittingFieldAuxAux n f).2.2

Depends on / 依赖: SplittingFieldAuxAux
-/
instance SplittingFieldAux.algebra (n : Nat) {K : Type u} [Field K] (f : K[X]) :
    Algebra K (SplittingFieldAux n f) :=
  (SplittingFieldAuxAux n f).2.2

namespace SplittingFieldAux

/--
theorem `succ` / 定理 `succ`

English:
theorem succ
  given: (n : Nat) (f : K[X])
  proof: rfl

中文:
定理 succ
  条件: (n : 自然数) (f : K[X])
  证明: rfl
-/
theorem succ (n : Nat) (f : K[X]) :
    SplittingFieldAux (n + 1) f = SplittingFieldAux n f.removeFactor :=
  rfl

/--
Instance `algebra'''` / 实例 `algebra'''`

English:
instance algebra'''
  signature: {n : Nat} {f : K[X]}
  body: SplittingFieldAux.algebra n _

中文:
实例 algebra'''
  签名: {n : 自然数} {f : K[X]}
  定义体: SplittingFieldAux.algebra n _

Depends on / 依赖: SplittingFieldAux, SplittingFieldAux.algebra, algebra
-/
instance algebra''' {n : Nat} {f : K[X]} :
    Algebra (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  SplittingFieldAux.algebra n _

/--
Instance `algebra'` / 实例 `algebra'`

English:
instance algebra'
  signature: {n : Nat} {f : K[X]}
  body: SplittingFieldAux.algebra'''

中文:
实例 algebra'
  签名: {n : 自然数} {f : K[X]}
  定义体: SplittingFieldAux.algebra'''

Depends on / 依赖: SplittingFieldAux, SplittingFieldAux.algebra, algebra
-/
instance algebra' {n : Nat} {f : K[X]} : Algebra (AdjoinRoot f.factor) (SplittingFieldAux n.succ f) :=
  SplittingFieldAux.algebra'''

/--
Instance `algebra''` / 实例 `algebra''`

English:
instance algebra''
  signature: {n : Nat} {f : K[X]}
  body: RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))

中文:
实例 algebra''
  签名: {n : 自然数} {f : K[X]}
  定义体: RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))

Depends on / 依赖: AdjoinRoot, AdjoinRoot.of, RingHom, RingHom.comp, RingHom.toAlgebra, algebraMap, f.factor, factor, toAlgebra
-/
instance algebra'' {n : Nat} {f : K[X]} : Algebra K (SplittingFieldAux n f.removeFactor) :=
  RingHom.toAlgebra (RingHom.comp (algebraMap _ _) (AdjoinRoot.of f.factor))

/--
Instance `scalar_tower'` / 实例 `scalar_tower'`

English:
instance scalar_tower'
  signature: {n : Nat} {f : K[X]}
  body: IsScalarTower.of_algebraMap_eq fun _ => rfl

中文:
实例 scalar_tower'
  签名: {n : 自然数} {f : K[X]}
  定义体: IsScalarTower.of_algebraMap_eq fun _ => rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
instance scalar_tower' {n : Nat} {f : K[X]} :
    IsScalarTower K (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/--
theorem `algebraMap_succ` / 定理 `algebraMap_succ`

English:
theorem algebraMap_succ
  given: (n : Nat) (f : K[X])
  proof: rfl

中文:
定理 algebraMap_succ
  条件: (n : 自然数) (f : K[X])
  证明: rfl
-/
theorem algebraMap_succ (n : Nat) (f : K[X]) :
    algebraMap K (SplittingFieldAux (n + 1) f) =
      (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor)).comp
        (AdjoinRoot.of f.factor) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `splits` / 定理 `splits`

English:
theorem splits
  given: (n : Nat)
  proof: Nat.recOn (motive := fun n => forall {K : Type u} [Field K], forall (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f))) n
    (fun {_} _ _ hf =>
Splits.of_degree_le_one degree_map_le.trans
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    rw [Polynomial.map_mul]
    exact Splits.mul ((Splits.X_sub_C _).map _) (ih _ (natDegree_removeFactor' hf))

中文:
定理 splits
  条件: (n : 自然数)
  证明: Nat.recOn (motive := fun n => forall {K : Type u} [Field K], forall (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f))) n
    (fun {_} _ _ hf =>
Splits.of_degree_le_one degree_map_le.trans
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    rw [Polynomial.map_mul]
    exact Splits.mul ((Splits.X_sub_C _).map _) (ih _ (natDegree_removeFactor' hf))
-/
protected theorem splits (n : Nat) :
    forall {K : Type u} [Field K], forall (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f)) :=
  Nat.recOn (motive := fun n => forall {K : Type u} [Field K], forall (f : K[X]) (_hfn : f.natDegree = n),
      Splits (f.map (algebraMap K <| SplittingFieldAux n f))) n
    (fun {_} _ _ hf =>
Splits.of_degree_le_one degree_map_le.trans
        (le_trans degree_le_natDegree <| hf.symm ▸ WithBot.coe_le_coe.2 zero_le_one))
    fun n ih {K} _ f hf => by
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor f fun h => by rw [h] at hf; cases hf]
    rw [Polynomial.map_mul]
    exact Splits.mul ((Splits.X_sub_C _).map _) (ih _ (natDegree_removeFactor' hf))

set_option backward.isDefEq.respectTransparency false in
/--
theorem `adjoin_rootSet` / 定理 `adjoin_rootSet`

English:
theorem adjoin_rootSet
  given: (n : Nat)
  proof: Nat.recOn (motive := fun n =>
    forall {K : Type u} [Field K],
      forall (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree != 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f != 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f != 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def]; rw [aroots_def]
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor _ hndf]; rw [Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]; rw [← Set.image_singleton]
    simp only [SplittingFieldAux.succ]
    rw [← Algebra.adjoin_eq_adjoin_union K {AdjoinRoot.root f.factor}
      ((map (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor))
        f.removeFactor).roots.toFinset : Set (SplittingFieldAux n f.removeFactor))
      AdjoinRoot.adjoinRoot_eq_top]; rw [← rootSet_def]; rw [ih _ (natDegree_removeFactor' hfn)]; rw [Subalgebra.restrictScalars_top]

中文:
定理 adjoin_rootSet
  条件: (n : 自然数)
  证明: Nat.recOn (motive := fun n =>
    forall {K : Type u} [Field K],
      forall (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree != 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f != 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f != 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def]; rw [aroots_def]
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor _ hndf]; rw [Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]; rw [← Set.image_singleton]
    simp only [SplittingFieldAux.succ]
    rw [← Algebra.adjoin_eq_adjoin_union K {AdjoinRoot.root f.factor}
      ((map (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor))
        f.removeFactor).roots.toFinset : Set (SplittingFieldAux n f.removeFactor))
      AdjoinRoot.adjoinRoot_eq_top]; rw [← rootSet_def]; rw [ih _ (natDegree_removeFactor' hfn)]; rw [Subalgebra.restrictScalars_top]

Depends on / 依赖: Algebra, Algebra.adjoin, Algebra.eq_top_iff, Nat.recOn, SplittingFieldAux, Subalgebra, Subalgebra.range_le, _hfn, adjoin, algebraMap, eq_top_iff, f.natDegree, f.rootSet, map_ne_zero, motive, n.succ, natDegree, neg_ne_zero, range_le, rootSet
-/
theorem adjoin_rootSet (n : Nat) :
    forall {K : Type u} [Field K],
      forall (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤ :=
  Nat.recOn (motive := fun n =>
    forall {K : Type u} [Field K],
      forall (f : K[X]) (_hfn : f.natDegree = n),
        Algebra.adjoin K (f.rootSet (SplittingFieldAux n f)) = ⊤)
    n (fun {_} _ _ _hf => Algebra.eq_top_iff.2 fun x => Subalgebra.range_le _ ⟨x, rfl⟩)
    fun n ih {K} _ f hfn => by
    have hndf : f.natDegree != 0 := by intro h; rw [h] at hfn; cases hfn
    have hfn0 : f != 0 := by intro h; rw [h] at hndf; exact hndf rfl
    have hmf0 : map (algebraMap K (SplittingFieldAux n.succ f)) f != 0 := map_ne_zero hfn0
    classical
    rw [rootSet_def]; rw [aroots_def]
    rw [algebraMap_succ]; rw [← map_map]; rw [← X_sub_C_mul_removeFactor _ hndf]; rw [Polynomial.map_mul] at hmf0 ⊢
    rw [roots_mul hmf0]; rw [Polynomial.map_sub]; rw [map_X]; rw [map_C]; rw [roots_X_sub_C]; rw [Multiset.toFinset_add]; rw [Finset.coe_union]; rw [Multiset.toFinset_singleton]; rw [Finset.coe_singleton]; rw [← Set.image_singleton]
    simp only [SplittingFieldAux.succ]
    rw [← Algebra.adjoin_eq_adjoin_union K {AdjoinRoot.root f.factor}
      ((map (algebraMap (AdjoinRoot f.factor) (SplittingFieldAux n f.removeFactor))
        f.removeFactor).roots.toFinset : Set (SplittingFieldAux n f.removeFactor))
      AdjoinRoot.adjoinRoot_eq_top]; rw [← rootSet_def]; rw [ih _ (natDegree_removeFactor' hfn)]; rw [Subalgebra.restrictScalars_top]

instance (f : K[X]) : IsSplittingField K (SplittingFieldAux f.natDegree f) f :=
  ⟨SplittingFieldAux.splits _ _ rfl, SplittingFieldAux.adjoin_rootSet _ _ rfl⟩

end SplittingFieldAux

/-- A splitting field of a polynomial. -/
@[stacks 09HV "The construction of the splitting field."]
/--
Definition of `SplittingField` / `SplittingField` 的定义

English:
definition SplittingField
  signature: (f : K[X])
  body: MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited

中文:
定义 分裂域
  签名: (f : K[X])
  定义体: MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited

Depends on / 依赖: MvPolynomial, MvPolynomial.aeval, RingHom, RingHom.ker, SplittingFieldAux, f.natDegree, natDegree, toRingHom
-/
def SplittingField (f : K[X]) :=
  MvPolynomial (SplittingFieldAux f.natDegree f) K ⧸
    RingHom.ker (MvPolynomial.aeval (R := K) id).toRingHom
deriving Inhabited

namespace SplittingField

variable (f : K[X])

variable {S : Type*} [DistribSMul S K] [IsScalarTower S K K] in
deriving instance SMul S for SplittingField f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (SplittingField f)
  body: inferInstanceAs CommRing (_ ⧸ _)

中文:
实例 :
  签名: 交换环 (分裂域 f)
  定义体: inferInstanceAs CommRing (_ ⧸ _)

Depends on / 依赖: CommRing, RayVector, RayVector.ext_iff, coe_neg, ext_iff, neg_neg
-/
instance : CommRing (SplittingField f) := inferInstanceAs CommRing (_ ⧸ _)

variable {R : Type*} [CommSemiring R] [Algebra R K] in
deriving instance Algebra R, IsScalarTower R K for SplittingField f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra K f.SplittingField
  body: inferInstance

中文:
实例 :
  签名: 代数 K f.分裂域
  定义体: inferInstance
-/
instance : Algebra K f.SplittingField := inferInstance

/--
Definition of `algEquivSplittingFieldAux` / `algEquivSplittingFieldAux` 的定义

English:
definition algEquivSplittingFieldAux
  signature: (f : K[X])
  body: Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩

中文:
定义 algEquivSplittingFieldAux
  签名: (f : K[X])
  定义体: Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩

Depends on / 依赖: Ideal.quotientKerAlgEquivOfSurjective, MvPolynomial, MvPolynomial.X, quotientKerAlgEquivOfSurjective
-/
def algEquivSplittingFieldAux (f : K[X]) : SplittingField f ≃ₐ[K] SplittingFieldAux f.natDegree f :=
  Ideal.quotientKerAlgEquivOfSurjective fun x => ⟨MvPolynomial.X x, by simp⟩

/--
Instance `instGroupWithZero` / 实例 `instGroupWithZero`

English:
instance instGroupWithZero
  signature: : GroupWithZero (SplittingField f)
  body: let e := algEquivSplittingFieldAux f
  { inv := fun a => e.symm (e a)⁻¹
    inv_zero := by simp
mul_inv_cancel := fun a ha => e.injective by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }

中文:
实例 instGroupWithZero
  签名: : 带零群 (分裂域 f)
  定义体: let e := algEquivSplittingFieldAux f
  { inv := fun a => e.symm (e a)⁻¹
    inv_zero := by simp
mul_inv_cancel := fun a ha => e.injective by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }

Depends on / 依赖: EmbeddingLike, EmbeddingLike.map_ne_zero_iff, algEquivSplittingFieldAux, e.injective, e.surjective.nontrivial, e.symm, injective, inv_zero, map_ne_zero_iff, mul_inv_cancel, nontrivial, surjective
-/
instance instGroupWithZero : GroupWithZero (SplittingField f) :=
  let e := algEquivSplittingFieldAux f
  { inv := fun a => e.symm (e a)⁻¹
    inv_zero := by simp
mul_inv_cancel := fun a ha => e.injective by simp [EmbeddingLike.map_ne_zero_iff.2 ha]
    __ := e.surjective.nontrivial }

/--
Instance `instField` / 实例 `instField`

English:
instance instField
  signature: : Field (SplittingField f) where
  body: (inferInstance : CommRing (SplittingField f))
  __ := instGroupWithZero f
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
nnqsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
qsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

中文:
实例 instField
  签名: : 域 (分裂域 f) where
  定义体: (inferInstance : CommRing (SplittingField f))
  __ := instGroupWithZero f
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
nnqsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
qsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

Depends on / 依赖: CommRing, SplittingField
-/
instance instField : Field (SplittingField f) where
  __ := (inferInstance : CommRing (SplittingField f))
  __ := instGroupWithZero f
  nnratCast q := algebraMap K _ q
  ratCast q := algebraMap K _ q
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by change algebraMap K _ _ = _; simp_rw [NNRat.cast_def, map_div₀, map_natCast]
  ratCast_def q := by
    change algebraMap K _ _ = _; rw [Rat.cast_def, map_div₀, map_intCast, map_natCast]
nnqsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, NNRat.smul_def]
qsmul_def q x := Quotient.inductionOn x fun p => congr_arg Quotient.mk'' by
    ext; simp [MvPolynomial.algebraMap_eq, Rat.smul_def]

/--
Instance `instCharZero` / 实例 `instCharZero`

English:
instance instCharZero
  signature: [CharZero K]
  body: charZero_of_injective_algebraMap (algebraMap K _).injective

中文:
实例 instCharZero
  签名: [特征零 K]
  定义体: charZero_of_injective_algebraMap (algebraMap K _).injective

Depends on / 依赖: algebraMap, charZero_of_injective_algebraMap, injective
-/
instance instCharZero [CharZero K] : CharZero (SplittingField f) :=
  charZero_of_injective_algebraMap (algebraMap K _).injective

/--
Instance `instCharP` / 实例 `instCharP`

English:
instance instCharP
  signature: (p : Nat) [CharP K p]
  body: charP_of_injective_algebraMap (algebraMap K _).injective p

中文:
实例 instCharP
  签名: (p : 自然数) [特征p K p]
  定义体: charP_of_injective_algebraMap (algebraMap K _).injective p

Depends on / 依赖: algebraMap, charP_of_injective_algebraMap, injective
-/
instance instCharP (p : Nat) [CharP K p] : CharP (SplittingField f) p :=
  charP_of_injective_algebraMap (algebraMap K _).injective p

/--
Instance `instExpChar` / 实例 `instExpChar`

English:
instance instExpChar
  signature: (p : Nat) [ExpChar K p]
  body: expChar_of_injective_algebraMap (algebraMap K _).injective p

中文:
实例 instExpChar
  签名: (p : 自然数) [ExpChar K p]
  定义体: expChar_of_injective_algebraMap (algebraMap K _).injective p

Depends on / 依赖: algebraMap, expChar_of_injective_algebraMap, injective
-/
instance instExpChar (p : Nat) [ExpChar K p] : ExpChar (SplittingField f) p :=
  expChar_of_injective_algebraMap (algebraMap K _).injective p

/--
Instance `_root_.Polynomial.IsSplittingField.splittingField` / 实例 `_root_.Polynomial.IsSplittingField.splittingField`

English:
instance _root_.Polynomial.IsSplittingField.splittingField
  signature: (f : K[X])
  body: IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm

@[stacks 09HU "Splitting part"]

中文:
实例 _root_.多项式.是分裂域.splittingField
  签名: (f : K[X])
  定义体: IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm

@[stacks 09HU "Splitting part"]

Depends on / 依赖: IsSplittingField, IsSplittingField.of_algEquiv, algEquivSplittingFieldAux, of_algEquiv
-/
instance _root_.Polynomial.IsSplittingField.splittingField (f : K[X]) :
    IsSplittingField K (SplittingField f) f :=
  IsSplittingField.of_algEquiv _ f (algEquivSplittingFieldAux f).symm

@[stacks 09HU "Splitting part"]
/--
theorem `splits` / 定理 `splits`

English:
theorem splits
  statement: Splits (f.map (algebraMap K (SplittingField f)))
  proof: IsSplittingField.splits f.SplittingField f

中文:
定理 splits
  结论: Splits (f.map (algebraMap K (分裂域 f)))
  证明: IsSplittingField.splits f.SplittingField f
-/
protected theorem splits : Splits (f.map (algebraMap K (SplittingField f))) :=
  IsSplittingField.splits f.SplittingField f

variable [Algebra K L] (hb : Splits (f.map (algebraMap K L)))

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : SplittingField f ->ₐ[K] L
  body: IsSplittingField.lift f.SplittingField f hb

中文:
定义 lift
  签名: : 分裂域 f ->ₐ[K] L
  定义体: IsSplittingField.lift f.SplittingField f hb

Depends on / 依赖: IsSplittingField, IsSplittingField.lift, SplittingField, f.SplittingField
-/
def lift : SplittingField f ->ₐ[K] L :=
  IsSplittingField.lift f.SplittingField f hb

/--
theorem `adjoin_rootSet` / 定理 `adjoin_rootSet`

English:
theorem adjoin_rootSet
  statement: Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤
  proof: Polynomial.IsSplittingField.adjoin_rootSet _ f

中文:
定理 adjoin_rootSet
  结论: 代数.adjoin K (f.rootSet (分裂域 f)) = ⊤
  证明: Polynomial.IsSplittingField.adjoin_rootSet _ f

Depends on / 依赖: IsSplittingField, Polynomial, Polynomial.IsSplittingField.adjoin_rootSet, adjoin_rootSet
-/
theorem adjoin_rootSet : Algebra.adjoin K (f.rootSet (SplittingField f)) = ⊤ :=
  Polynomial.IsSplittingField.adjoin_rootSet _ f

end SplittingField

end SplittingField

namespace IsSplittingField

variable (K L)
variable [Algebra K L]
variable {K}

instance (f : K[X]) : FiniteDimensional K f.SplittingField :=
  finiteDimensional f.SplittingField f

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Finite
  signature: K] (f
  body: Module.finite_of_finite K

中文:
实例 [有限
  签名: K] (f
  定义体: Module.finite_of_finite K

Depends on / 依赖: Module, Module.finite_of_finite, finite_of_finite
-/
instance [Finite K] (f : K[X]) : Finite f.SplittingField :=
  Module.finite_of_finite K

instance (f : K[X]) : Module.IsTorsionFree K f.SplittingField :=
  inferInstance

/--
Definition of `algEquiv` / `algEquiv` 的定义

English:
definition algEquiv
  signature: (f : K[X]) [h : IsSplittingField K L f]
  body: AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f)
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

中文:
定义 algEquiv
  签名: (f : K[X]) [h : 是分裂域 K L f]
  定义体: AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f)
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

Depends on / 依赖: AlgEquiv, AlgEquiv.ofBijective, Algebra, Algebra.IsAlgebraic.of_finite, IsAlgebraic, SplittingField, finiteDimensional, ofBijective, of_finite, splits
-/
def algEquiv (f : K[X]) [h : IsSplittingField K L f] : L ≃ₐ[K] SplittingField f :=
AlgEquiv.ofBijective (lift L f <| splits (SplittingField f) f)
    have := finiteDimensional L f
    ((Algebra.IsAlgebraic.of_finite K L).algHom_bijective₂ _ <| lift _ f h.1).1

end IsSplittingField

end Polynomial
