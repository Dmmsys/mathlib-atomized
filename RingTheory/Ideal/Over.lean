/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.Algebra.Group.Subgroup.Actions
public import Mathlib.RingTheory.Ideal.Pointwise
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Ideals over/under ideals

This file concerns ideals lying over other ideals.
Let `f : R →+* S` be a ring homomorphism (typically a ring extension), `I` an ideal of `R` and
`J` an ideal of `S`. We say `J` lies over `I` (and `I` under `J`) if `I` is the `f`-preimage of `J`.
This is expressed here by writing `I = J.comap f`.
-/

@[expose] public section

-- for going-up results about integral extensions, see `Mathlib/RingTheory/Ideal/GoingUp.lean`
assert_not_exists Algebra.IsIntegral

-- for results about finiteness, see `Mathlib/RingTheory/Finiteness/Quotient.lean`
assert_not_exists Module.Finite

variable {R : Type*} [CommRing R]

namespace Ideal

open Submodule

open scoped Pointwise

section CommRing

variable {S : Type*} [CommRing S] {f : R ->+* S} {I J : Ideal S}

variable {p : Ideal R} {P : Ideal S}

/--
theorem `comap_eq_of_scalar_tower_quotient` / 定理 `comap_eq_of_scalar_tower_quotient`

English:
theorem comap_eq_of_scalar_tower_quotient
  statement: [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
  proof: by
  ext x
  rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← Quotient.eq_zero_iff_mem]; rw [Quotient.mk_algebraMap]; rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P)]; rw [Quotient.algebraMap_eq]
  exact map_eq_zero_iff _ h

中文:
定理 comap_eq_of_scalar_tower_quotient
  结论: [代数 R S] [代数 (R ⧸ p) (S ⧸ P)]
  证明: by
  ext x
  rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← Quotient.eq_zero_iff_mem]; rw [Quotient.mk_algebraMap]; rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P)]; rw [Quotient.algebraMap_eq]
  exact map_eq_zero_iff _ h

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_apply, Quotient, Quotient.algebraMap_eq, Quotient.eq_zero_iff_mem, Quotient.mk_algebraMap, algebraMap_apply, algebraMap_eq, eq_zero_iff_mem, map_eq_zero_iff, mem_comap, mk_algebraMap
-/
theorem comap_eq_of_scalar_tower_quotient [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)]
    [IsScalarTower R (R ⧸ p) (S ⧸ P)] (h : Function.Injective (algebraMap (R ⧸ p) (S ⧸ P))) :
    comap (algebraMap R S) P = p := by
  ext x
  rw [mem_comap]; rw [← Quotient.eq_zero_iff_mem]; rw [← Quotient.eq_zero_iff_mem]; rw [Quotient.mk_algebraMap]; rw [IsScalarTower.algebraMap_apply R (R ⧸ p) (S ⧸ P)]; rw [Quotient.algebraMap_eq]
  exact map_eq_zero_iff _ h

variable [Algebra R S]

/--
Instance `Quotient.algebraQuotientMapQuotient` / 实例 `Quotient.algebraQuotientMapQuotient`

English:
instance Quotient.algebraQuotientMapQuotient
  signature: : Algebra (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  body: Ideal.Quotient.algebraQuotientOfLEComap le_comap_map

@[simp]

中文:
实例 商.algebraQuotientMapQuotient
  签名: : 代数 (R ⧸ p) (S ⧸ map (algebraMap R S) p)
  定义体: Ideal.Quotient.algebraQuotientOfLEComap le_comap_map

@[simp]

Depends on / 依赖: Ideal.Quotient.algebraQuotientOfLEComap, Quotient, algebraQuotientOfLEComap, le_comap_map
-/
instance Quotient.algebraQuotientMapQuotient : Algebra (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  Ideal.Quotient.algebraQuotientOfLEComap le_comap_map

@[simp]
/--
theorem `Quotient.algebraMap_quotient_map_quotient` / 定理 `Quotient.algebraMap_quotient_map_quotient`

English:
theorem Quotient.algebraMap_quotient_map_quotient
  given: (x : R)
  proof: algebraMap R S
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl

@[simp]

中文:
定理 商.algebraMap_quotient_map_quotient
  条件: (x : R)
  证明: algebraMap R S
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl

@[simp]

Depends on / 依赖: algebraMap
-/
theorem Quotient.algebraMap_quotient_map_quotient (x : R) :
    letI f := algebraMap R S
    algebraMap (R ⧸ p) (S ⧸ map f p) (Ideal.Quotient.mk p x) =
    Ideal.Quotient.mk (map f p) (f x) :=
  rfl

@[simp]
/--
theorem `Quotient.mk_smul_mk_quotient_map_quotient` / 定理 `Quotient.mk_smul_mk_quotient_map_quotient`

English:
theorem Quotient.mk_smul_mk_quotient_map_quotient
  given: (x : R) (y : S)
  proof: algebraMap R S
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  Algebra.smul_def _ _

中文:
定理 商.mk_smul_mk_quotient_map_quotient
  条件: (x : R) (y : S)
  证明: algebraMap R S
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  Algebra.smul_def _ _

Depends on / 依赖: algebraMap
-/
theorem Quotient.mk_smul_mk_quotient_map_quotient (x : R) (y : S) :
    letI f := algebraMap R S
    Quotient.mk p x • Quotient.mk (map f p) y = Quotient.mk (map f p) (f x * y) :=
  Algebra.smul_def _ _

/--
Instance `Quotient.tower_quotient_map_quotient` / 实例 `Quotient.tower_quotient_map_quotient`

English:
instance Quotient.tower_quotient_map_quotient
  signature: :
  body: IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq]; rw [Quotient.algebraMap_quotient_map_quotient]; rw [Quotient.mk_algebraMap]

中文:
实例 商.tower_quotient_map_quotient
  签名: :
  定义体: IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq]; rw [Quotient.algebraMap_quotient_map_quotient]; rw [Quotient.mk_algebraMap]

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, Quotient, Quotient.algebraMap_eq, Quotient.algebraMap_quotient_map_quotient, Quotient.mk_algebraMap, algebraMap_eq, algebraMap_quotient_map_quotient, mk_algebraMap, of_algebraMap_eq
-/
instance Quotient.tower_quotient_map_quotient :
    IsScalarTower R (R ⧸ p) (S ⧸ map (algebraMap R S) p) :=
  IsScalarTower.of_algebraMap_eq fun x => by
    rw [Quotient.algebraMap_eq]; rw [Quotient.algebraMap_quotient_map_quotient]; rw [Quotient.mk_algebraMap]

end CommRing

section ideal_liesOver

section Semiring

variable (A : Type*) [CommSemiring A] {B C : Type*} [Semiring B] [Semiring C] [Algebra A B]
  [Algebra A C] (P : Ideal B) {Q : Ideal C} (p : Ideal A)
  {G : Type*} [Group G] [MulSemiringAction G B] (g : G)

/--
Definition of `under` / `under` 的定义

English:
abbreviation under
  signature: : Ideal A
  body: Ideal.comap (algebraMap A B) P

中文:
缩写 under
  签名: : 理想 A
  定义体: Ideal.comap (algebraMap A B) P

Depends on / 依赖: Ideal.comap, algebraMap
-/
abbrev under : Ideal A := Ideal.comap (algebraMap A B) P

/--
theorem `under_def` / 定理 `under_def`

English:
theorem under_def
  statement: P.under A = Ideal.comap (algebraMap A B) P
  proof: rfl

中文:
定理 under_def
  结论: P.under A = 理想.comap (algebraMap A B) P
  证明: rfl
-/
theorem under_def : P.under A = Ideal.comap (algebraMap A B) P := rfl

/--
theorem `mem_under` / 定理 `mem_under`

English:
theorem mem_under
  given: {x : A}
  statement: x in P.under A ↔ algebraMap A B x in P
  proof: mem_comap

中文:
定理 mem_under
  条件: {x : A}
  结论: x in P.under A ↔ algebraMap A B x in P
  证明: mem_comap

Depends on / 依赖: mem_comap
-/
theorem mem_under {x : A} : x in P.under A ↔ algebraMap A B x in P := mem_comap

/--
Instance `IsPrime.under` / 实例 `IsPrime.under`

English:
instance IsPrime.under
  signature: [hP : P.IsPrime]
  body: hP.comap (algebraMap A B)

@[simp]

中文:
实例 是素.under
  签名: [hP : P.是素]
  定义体: hP.comap (algebraMap A B)

@[simp]

Depends on / 依赖: algebraMap, hP.comap
-/
instance IsPrime.under [hP : P.IsPrime] : (P.under A).IsPrime :=
  hP.comap (algebraMap A B)

@[simp]
/--
lemma `under_smul` / 引理 `under_smul`

English:
lemma under_smul
  given: [SMulCommClass G A B]
  statement: (g • P : Ideal B).under A = P.under A
  proof: by
  ext a
  rw [mem_comap]; rw [mem_comap]; rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [smul_algebraMap]

@[simp]

中文:
引理 under_smul
  条件: [标量交换类 G A B]
  结论: (g • P : 理想 B).under A = P.under A
  证明: by
  ext a
  rw [mem_comap]; rw [mem_comap]; rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [smul_algebraMap]

@[simp]

Depends on / 依赖: mem_comap, mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap
-/
lemma under_smul [SMulCommClass G A B] : (g • P : Ideal B).under A = P.under A := by
  ext a
  rw [mem_comap]; rw [mem_comap]; rw [mem_pointwise_smul_iff_inv_smul_mem]; rw [smul_algebraMap]

@[simp]
/--
theorem `smul_under` / 定理 `smul_under`

English:
theorem smul_under
  given: [MulSemiringAction G A] [SMulDistribClass G A B]
  proof: by
  conv_lhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  conv_rhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  congr
  ext
  simp [algebraMap.smul']

中文:
定理 smul_under
  条件: [MulSemiring作用 G A] [SMulDistrib类 G A B]
  证明: by
  conv_lhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  conv_rhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  congr
  ext
  simp [algebraMap.smul']

Depends on / 依赖: algebraMap, algebraMap.smul, comap_coe, comap_comap, conv_lhs, conv_rhs, pointwise_smul_eq_comap, under_def
-/
theorem smul_under [MulSemiringAction G A] [SMulDistribClass G A B] :
    g • P.under A = (g • P).under A := by
  conv_lhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  conv_rhs => rw [pointwise_smul_eq_comap, ← comap_coe, under_def, comap_comap]
  congr
  ext
  simp [algebraMap.smul']

variable (B) in
/--
theorem `under_top` / 定理 `under_top`

English:
theorem under_top
  statement: under A (⊤ : Ideal B) = ⊤
  proof: comap_top

中文:
定理 under_top
  结论: under A (⊤ : 理想 B) = ⊤
  证明: comap_top

Depends on / 依赖: comap_top
-/
theorem under_top : under A (⊤ : Ideal B) = ⊤ := comap_top

variable {A}

/--
Definition of `LiesOver` / `LiesOver` 的定义

English:
class LiesOver
  parameters: : Prop where
  axioms and operations (1):
    - over : p = P.under A

中文:
类 LiesOver
  参数: : 命题 where
  公理与运算 (1 个):
    - over : p = P.under A
-/
@[mk_iff] class LiesOver : Prop where
  over : p = P.under A

/--
Instance `over_under` / 实例 `over_under`

English:
instance over_under
  signature: : P.LiesOver (P.under A) where over
  body: rfl

中文:
实例 over_under
  签名: : P.LiesOver (P.under A) where over
  定义体: rfl
-/
instance over_under : P.LiesOver (P.under A) where over := rfl

/--
theorem `over_def` / 定理 `over_def`

English:
theorem over_def
  given: [P.LiesOver p]
  statement: p = P.under A
  proof: LiesOver.over

中文:
定理 over_def
  条件: [P.LiesOver p]
  结论: p = P.under A
  证明: LiesOver.over

Depends on / 依赖: LiesOver, LiesOver.over
-/
theorem over_def [P.LiesOver p] : p = P.under A := LiesOver.over

/--
theorem `mem_of_liesOver` / 定理 `mem_of_liesOver`

English:
theorem mem_of_liesOver
  given: [P.LiesOver p] (x : A)
  statement: x in p ↔ algebraMap A B x in P
  proof: by
  rw [P.over_def p]
  rfl

中文:
定理 mem_of_liesOver
  条件: [P.LiesOver p] (x : A)
  结论: x in p ↔ algebraMap A B x in P
  证明: by
  rw [P.over_def p]
  rfl

Depends on / 依赖: P.over_def, over_def
-/
theorem mem_of_liesOver [P.LiesOver p] (x : A) : x in p ↔ algebraMap A B x in P := by
  rw [P.over_def p]
  rfl

variable (A B) in
/--
Instance `top_liesOver_top` / 实例 `top_liesOver_top`

English:
instance top_liesOver_top
  signature: : (⊤ : Ideal B).LiesOver (⊤ : Ideal A) where
  body: (under_top A B).symm

中文:
实例 top_liesOver_top
  签名: : (⊤ : 理想 B).LiesOver (⊤ : 理想 A) where
  定义体: (under_top A B).symm

Depends on / 依赖: under_top
-/
instance top_liesOver_top : (⊤ : Ideal B).LiesOver (⊤ : Ideal A) where
  over := (under_top A B).symm

/--
theorem `eq_top_iff_of_liesOver` / 定理 `eq_top_iff_of_liesOver`

English:
theorem eq_top_iff_of_liesOver
  given: [P.LiesOver p]
  statement: P = ⊤ ↔ p = ⊤
  proof: by
  rw [P.over_def p]
  exact comap_eq_top_iff.symm

中文:
定理 eq_top_iff_of_liesOver
  条件: [P.LiesOver p]
  结论: P = ⊤ ↔ p = ⊤
  证明: by
  rw [P.over_def p]
  exact comap_eq_top_iff.symm

Depends on / 依赖: P.over_def, comap_eq_top_iff, comap_eq_top_iff.symm, over_def
-/
theorem eq_top_iff_of_liesOver [P.LiesOver p] : P = ⊤ ↔ p = ⊤ := by
  rw [P.over_def p]
  exact comap_eq_top_iff.symm

/--
lemma `ne_top_iff_of_liesOver` / 引理 `ne_top_iff_of_liesOver`

English:
lemma ne_top_iff_of_liesOver
  given: [P.LiesOver p]
  statement: P != ⊤ ↔ p != ⊤
  proof: (eq_top_iff_of_liesOver ..).ne

中文:
引理 ne_top_iff_of_liesOver
  条件: [P.LiesOver p]
  结论: P != ⊤ ↔ p != ⊤
  证明: (eq_top_iff_of_liesOver ..).ne

Depends on / 依赖: eq_top_iff_of_liesOver
-/
lemma ne_top_iff_of_liesOver [P.LiesOver p] : P != ⊤ ↔ p != ⊤ := (eq_top_iff_of_liesOver ..).ne

/--
lemma `isPrime_of_liesOver` / 引理 `isPrime_of_liesOver`

English:
lemma isPrime_of_liesOver
  given: [P.LiesOver p] [P.IsPrime]
  statement: p.IsPrime
  proof: by
  rw [over_def P p]
  exact IsPrime.under A P

中文:
引理 isPrime_of_liesOver
  条件: [P.LiesOver p] [P.是素]
  结论: p.是素
  证明: by
  rw [over_def P p]
  exact IsPrime.under A P

Depends on / 依赖: IsPrime, IsPrime.under, over_def
-/
lemma isPrime_of_liesOver [P.LiesOver p] [P.IsPrime] : p.IsPrime := by
  rw [over_def P p]
  exact IsPrime.under A P

variable {P}

/--
theorem `LiesOver.of_eq_comap` / 定理 `LiesOver.of_eq_comap`

English:
theorem LiesOver.of_eq_comap
  statement: [Q.LiesOver p] {F : Type*} [FunLike F B C]
  proof: by
    rw [h]
exact (over_def Q p).trans
      congrFun (congrFun (congrArg
        comap ((AlgHomClass.toAlgHom f : B ->ₐ[A] C).comp_algebraMap.symm)) _) Q

中文:
定理 LiesOver.of_eq_comap
  结论: [Q.LiesOver p] {F : 类型} [函数状 F B C]
  证明: by
    rw [h]
exact (over_def Q p).trans
      congrFun (congrFun (congrArg
        comap ((AlgHomClass.toAlgHom f : B ->ₐ[A] C).comp_algebraMap.symm)) _) Q

Depends on / 依赖: AlgHomClass, AlgHomClass.toAlgHom, comp_algebraMap, comp_algebraMap.symm, over_def, toAlgHom
-/
theorem LiesOver.of_eq_comap [Q.LiesOver p] {F : Type*} [FunLike F B C]
    [AlgHomClass F A B C] (f : F) (h : P = Q.comap f) : P.LiesOver p where
  over := by
    rw [h]
exact (over_def Q p).trans
      congrFun (congrFun (congrArg
        comap ((AlgHomClass.toAlgHom f : B ->ₐ[A] C).comp_algebraMap.symm)) _) Q

/--
theorem `LiesOver.of_eq_map_equiv` / 定理 `LiesOver.of_eq_map_equiv`

English:
theorem LiesOver.of_eq_map_equiv
  statement: [P.LiesOver p] {E : Type*} [EquivLike E B C]
  proof: by
  rw [← show _ = P.map σ from comap_symm (RingEquivClass.toRingEquiv σ)] at h
  exact of_eq_comap p (AlgEquivClass.toAlgEquiv σ : B ≃ₐ[A] C).symm h

中文:
定理 LiesOver.of_eq_map_equiv
  结论: [P.LiesOver p] {E : 类型} [等价状 E B C]
  证明: by
  rw [← show _ = P.map σ from comap_symm (RingEquivClass.toRingEquiv σ)] at h
  exact of_eq_comap p (AlgEquivClass.toAlgEquiv σ : B ≃ₐ[A] C).symm h

Depends on / 依赖: AlgEquivClass, AlgEquivClass.toAlgEquiv, P.map, RingEquivClass, RingEquivClass.toRingEquiv, comap_symm, of_eq_comap, toAlgEquiv, toRingEquiv
-/
theorem LiesOver.of_eq_map_equiv [P.LiesOver p] {E : Type*} [EquivLike E B C]
    [AlgEquivClass E A B C] (σ : E) (h : Q = P.map σ) : Q.LiesOver p := by
  rw [← show _ = P.map σ from comap_symm (RingEquivClass.toRingEquiv σ)] at h
  exact of_eq_comap p (AlgEquivClass.toAlgEquiv σ : B ≃ₐ[A] C).symm h

variable {p} in
/--
Instance `LiesOver.smul` / 实例 `LiesOver.smul`

English:
instance LiesOver.smul
  signature: [SMulCommClass G A B] [h : P.LiesOver p]
  body: ⟨h.over.trans (under_smul A P g).symm⟩

中文:
实例 LiesOver.smul
  签名: [标量交换类 G A B] [h : P.LiesOver p]
  定义体: ⟨h.over.trans (under_smul A P g).symm⟩

Depends on / 依赖: h.over.trans, under_smul
-/
instance LiesOver.smul [SMulCommClass G A B] [h : P.LiesOver p] : (g • P).LiesOver p :=
  ⟨h.over.trans (under_smul A P g).symm⟩

variable (P) (Q)

/--
Instance `comap_liesOver` / 实例 `comap_liesOver`

English:
instance comap_liesOver
  signature: [Q.LiesOver p] {F : Type*} [FunLike F B C] [AlgHomClass F A B C]
  body: LiesOver.of_eq_comap p f rfl

中文:
实例 comap_liesOver
  签名: [Q.LiesOver p] {F : 类型} [函数状 F B C] [代数态射类 F A B C]
  定义体: LiesOver.of_eq_comap p f rfl

Depends on / 依赖: LiesOver, LiesOver.of_eq_comap, of_eq_comap
-/
instance comap_liesOver [Q.LiesOver p] {F : Type*} [FunLike F B C] [AlgHomClass F A B C]
    (f : F) : (Q.comap f).LiesOver p :=
  LiesOver.of_eq_comap p f rfl

/--
Instance `map_equiv_liesOver` / 实例 `map_equiv_liesOver`

English:
instance map_equiv_liesOver
  signature: [P.LiesOver p] {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C]
  body: LiesOver.of_eq_map_equiv p σ rfl

中文:
实例 map_equiv_liesOver
  签名: [P.LiesOver p] {E : 类型} [等价状 E B C] [代数等价类 E A B C]
  定义体: LiesOver.of_eq_map_equiv p σ rfl

Depends on / 依赖: LiesOver, LiesOver.of_eq_map_equiv, of_eq_map_equiv
-/
instance map_equiv_liesOver [P.LiesOver p] {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C]
    (σ : E) : (P.map σ).LiesOver p :=
  LiesOver.of_eq_map_equiv p σ rfl

end Semiring

section CommSemiring

variable {A : Type*} [CommSemiring A] {B : Type*} [CommSemiring B] {C : Type*} [Semiring C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (𝔓 : Ideal C) (P : Ideal B) (p : Ideal A)

@[simp]
/--
theorem `under_under` / 定理 `under_under`

English:
theorem under_under
  statement: (𝔓.under B).under A = 𝔓.under A
  proof: by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]

中文:
定理 under_under
  结论: (𝔓.under B).under A = 𝔓.under A
  证明: by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, comap_comap, simp_rw
-/
theorem under_under : (𝔓.under B).under A = 𝔓.under A := by
  simp_rw [comap_comap, ← IsScalarTower.algebraMap_eq]

/--
theorem `LiesOver.trans` / 定理 `LiesOver.trans`

English:
theorem LiesOver.trans
  given: [𝔓.LiesOver P] [P.LiesOver p]
  statement: 𝔓.LiesOver p where
  proof: by rw [P.over_def p, 𝔓.over_def P, under_under]

中文:
定理 LiesOver.trans
  条件: [𝔓.LiesOver P] [P.LiesOver p]
  结论: 𝔓.LiesOver p where
  证明: by rw [P.over_def p, 𝔓.over_def P, under_under]

Depends on / 依赖: P.over_def, over_def, under_under
-/
theorem LiesOver.trans [𝔓.LiesOver P] [P.LiesOver p] : 𝔓.LiesOver p where
  over := by rw [P.over_def p, 𝔓.over_def P, under_under]

/--
theorem `LiesOver.tower_bot` / 定理 `LiesOver.tower_bot`

English:
theorem LiesOver.tower_bot
  given: [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P]
  statement: P.LiesOver p where
  proof: by rw [𝔓.over_def p, 𝔓.over_def P, under_under]

中文:
定理 LiesOver.tower_bot
  条件: [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P]
  结论: P.LiesOver p where
  证明: by rw [𝔓.over_def p, 𝔓.over_def P, under_under]

Depends on / 依赖: over_def, under_under
-/
theorem LiesOver.tower_bot [hp : 𝔓.LiesOver p] [hP : 𝔓.LiesOver P] : P.LiesOver p where
  over := by rw [𝔓.over_def p, 𝔓.over_def P, under_under]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [𝔓.LiesOver
  signature: P] : 𝔓.LiesOver (P.under A)
  body: .trans 𝔓 P (P.under A)

中文:
实例 [𝔓.LiesOver
  签名: P] : 𝔓.LiesOver (P.under A)
  定义体: .trans 𝔓 P (P.under A)

Depends on / 依赖: P.under
-/
instance [𝔓.LiesOver P] : 𝔓.LiesOver (P.under A) :=
  .trans 𝔓 P (P.under A)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [𝔓.LiesOver
  signature: P] : P.LiesOver (𝔓.under A)
  body: .tower_bot 𝔓 P (𝔓.under A)

中文:
实例 [𝔓.LiesOver
  签名: P] : P.LiesOver (𝔓.under A)
  定义体: .tower_bot 𝔓 P (𝔓.under A)

Depends on / 依赖: tower_bot
-/
instance [𝔓.LiesOver P] : P.LiesOver (𝔓.under A) :=
  .tower_bot 𝔓 P (𝔓.under A)

/--
theorem `map_under_le_under_map` / 定理 `map_under_le_under_map`

English:
theorem map_under_le_under_map
  statement: {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
  proof: by
  apply le_comap_of_map_le
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [map_le_iff_le_comap]; rw [IsScalarTower.algebraMap_eq A B D]; rw [← comap_comap]
exact comap_mono le_comap_map

中文:
定理 map_under_le_under_map
  结论: {C D : 类型} [交换半环 C] [半环 D] [代数 A C]
  证明: by
  apply le_comap_of_map_le
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [map_le_iff_le_comap]; rw [IsScalarTower.algebraMap_eq A B D]; rw [← comap_comap]
exact comap_mono le_comap_map

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, algebraMap_eq, comap_comap, comap_mono, le_comap_map, le_comap_of_map_le, map_le_iff_le_comap, map_map
-/
theorem map_under_le_under_map {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D] :
    map (algebraMap A C) (under A P) <= under C (map (algebraMap B D) P) := by
  apply le_comap_of_map_le
  rw [map_map]; rw [← IsScalarTower.algebraMap_eq]; rw [map_le_iff_le_comap]; rw [IsScalarTower.algebraMap_eq A B D]; rw [← comap_comap]
exact comap_mono le_comap_map

/--
theorem `under_map_eq_map_under` / 定理 `under_map_eq_map_under`

English:
theorem under_map_eq_map_under
  statement: {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
  proof: (IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂)).mp
    map_under_le_under_map P

中文:
定理 under_map_eq_map_under
  结论: {C D : 类型} [交换半环 C] [半环 D] [代数 A C]
  证明: (IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂)).mp
    map_under_le_under_map P

Depends on / 依赖: IsCoatom, IsCoatom.le_iff_eq, algebraMap, comap_ne_top, isMaximal_def, isMaximal_def.mp, le_iff_eq, map_under_le_under_map
-/
theorem under_map_eq_map_under {C D : Type*} [CommSemiring C] [Semiring D] [Algebra A C]
    [Algebra C D] [Algebra A D] [Algebra B D] [IsScalarTower A C D] [IsScalarTower A B D]
    (h₁ : (map (algebraMap A C) (under A P)).IsMaximal) (h₂ : map (algebraMap B D) P != ⊤) :
    under C (map (algebraMap B D) P) = map (algebraMap A C) (under A P) :=
(IsCoatom.le_iff_eq (isMaximal_def.mp h₁) (comap_ne_top (algebraMap C D) h₂)).mp
    map_under_le_under_map P

/--
theorem `disjoint_primeCompl_of_liesOver` / 定理 `disjoint_primeCompl_of_liesOver`

English:
theorem disjoint_primeCompl_of_liesOver
  given: [p.IsPrime] [hPp : 𝔓.LiesOver p]
  proof: by
  rw [liesOver_iff]; rw [under_def]; rw [SetLike.ext'_iff]; rw [coe_comap] at hPp
  simpa only [Algebra.algebraMapSubmonoid, primeCompl, hPp, ← le_compl_iff_disjoint_left]
    using! Set.subset_compl_comm.mp (by simp)

中文:
定理 disjoint_primeCompl_of_liesOver
  条件: [p.是素] [hPp : 𝔓.LiesOver p]
  证明: by
  rw [liesOver_iff]; rw [under_def]; rw [SetLike.ext'_iff]; rw [coe_comap] at hPp
  simpa only [Algebra.algebraMapSubmonoid, primeCompl, hPp, ← le_compl_iff_disjoint_left]
    using! Set.subset_compl_comm.mp (by simp)

Depends on / 依赖: Algebra, Algebra.algebraMapSubmonoid, Set.subset_compl_comm.mp, SetLike, SetLike.ext, _iff, algebraMapSubmonoid, coe_comap, le_compl_iff_disjoint_left, liesOver_iff, primeCompl, subset_compl_comm, under_def
-/
theorem disjoint_primeCompl_of_liesOver [p.IsPrime] [hPp : 𝔓.LiesOver p] :
  Disjoint ((Algebra.algebraMapSubmonoid C p.primeCompl) : Set C) (𝔓 : Set C) := by
  rw [liesOver_iff]; rw [under_def]; rw [SetLike.ext'_iff]; rw [coe_comap] at hPp
  simpa only [Algebra.algebraMapSubmonoid, primeCompl, hPp, ← le_compl_iff_disjoint_left]
    using! Set.subset_compl_comm.mp (by simp)

/--
theorem `algebraMapSubmonoid_primeCompl_of_liesOver_surjective` / 定理 `algebraMapSubmonoid_primeCompl_of_liesOver_surjective`

English:
theorem algebraMapSubmonoid_primeCompl_of_liesOver_surjective
  proof: by
  simpa [over_def P p] using! P.map_primeCompl_comap_of_surjective (algebraMap A B) hf

中文:
定理 algebraMapSubmonoid_primeCompl_of_liesOver_surjective
  证明: by
  simpa [over_def P p] using! P.map_primeCompl_comap_of_surjective (algebraMap A B) hf

Depends on / 依赖: P.map_primeCompl_comap_of_surjective, algebraMap, map_primeCompl_comap_of_surjective, over_def
-/
theorem algebraMapSubmonoid_primeCompl_of_liesOver_surjective
    [p.IsPrime] [P.IsPrime] [P.LiesOver p] (hf : Function.Surjective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B p.primeCompl = P.primeCompl := by
  simpa [over_def P p] using! P.map_primeCompl_comap_of_surjective (algebraMap A B) hf

variable (B)

/--
Instance `under_liesOver_of_liesOver` / 实例 `under_liesOver_of_liesOver`

English:
instance under_liesOver_of_liesOver
  signature: [𝔓.LiesOver p]
  body: LiesOver.tower_bot 𝔓 (𝔓.under B) p

中文:
实例 under_liesOver_of_liesOver
  签名: [𝔓.LiesOver p]
  定义体: LiesOver.tower_bot 𝔓 (𝔓.under B) p

Depends on / 依赖: LiesOver, LiesOver.tower_bot, tower_bot
-/
instance under_liesOver_of_liesOver [𝔓.LiesOver p] : (𝔓.under B).LiesOver p :=
  LiesOver.tower_bot 𝔓 (𝔓.under B) p

end CommSemiring

section CommRing

variable (A B : Type*) [CommSemiring A] [Semiring B]
  [Algebra A B] [FaithfulSMul A B] {p : Ideal A}

@[simp]
/--
theorem `under_bot` / 定理 `under_bot`

English:
theorem under_bot
  statement: under A (⊥ : Ideal B) = ⊥
  proof: comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

中文:
定理 under_bot
  结论: under A (⊥ : 理想 B) = ⊥
  证明: comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, algebraMap, algebraMap_injective, comap_bot_of_injective
-/
theorem under_bot : under A (⊥ : Ideal B) = ⊥ :=
  comap_bot_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

/--
Instance `bot_liesOver_bot` / 实例 `bot_liesOver_bot`

English:
instance bot_liesOver_bot
  signature: : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  body: (under_bot A B).symm

中文:
实例 bot_liesOver_bot
  签名: : (⊥ : 理想 B).LiesOver (⊥ : 理想 A) where
  定义体: (under_bot A B).symm

Depends on / 依赖: under_bot
-/
instance bot_liesOver_bot : (⊥ : Ideal B).LiesOver (⊥ : Ideal A) where
  over := (under_bot A B).symm

variable {A B} in
/--
theorem `ne_bot_of_liesOver_of_ne_bot` / 定理 `ne_bot_of_liesOver_of_ne_bot`

English:
theorem ne_bot_of_liesOver_of_ne_bot
  given: (hp : p != ⊥) (P : Ideal B) [P.LiesOver p]
  statement: P != ⊥
  proof: by
  contrapose hp
  rw [over_def P p]; rw [hp]; rw [under_bot]

中文:
定理 ne_bot_of_liesOver_of_ne_bot
  条件: (hp : p != ⊥) (P : 理想 B) [P.LiesOver p]
  结论: P != ⊥
  证明: by
  contrapose hp
  rw [over_def P p]; rw [hp]; rw [under_bot]

Depends on / 依赖: contrapose, over_def, under_bot
-/
theorem ne_bot_of_liesOver_of_ne_bot (hp : p != ⊥) (P : Ideal B) [P.LiesOver p] : P != ⊥ := by
  contrapose hp
  rw [over_def P p]; rw [hp]; rw [under_bot]

end CommRing

instance {K A : Type*} [Field K] [Semiring A] [Algebra K A] (P : Ideal A) [P.IsPrime] :
    P.LiesOver (⊥ : Ideal K) :=
  ⟨((IsSimpleOrder.eq_bot_or_eq_top _).resolve_right Ideal.IsPrime.ne_top').symm⟩
namespace Quotient

variable (R : Type*) [CommSemiring R] {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra A C] [Algebra R A] [Algebra R B] [IsScalarTower R A B]
  (P : Ideal B) {Q : Ideal C} (p : Ideal A) [Q.LiesOver p] [P.LiesOver p]
  (G : Type*) [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/--
Instance `algebraOfLiesOver` / 实例 `algebraOfLiesOver`

English:
instance algebraOfLiesOver
  signature: : Algebra (A ⧸ p) (B ⧸ P)
  body: algebraQuotientOfLEComap (le_of_eq (P.over_def p))

@[simp]

中文:
实例 algebraOfLiesOver
  签名: : 代数 (A ⧸ p) (B ⧸ P)
  定义体: algebraQuotientOfLEComap (le_of_eq (P.over_def p))

@[simp]

Depends on / 依赖: P.over_def, algebraQuotientOfLEComap, le_of_eq, over_def
-/
instance algebraOfLiesOver : Algebra (A ⧸ p) (B ⧸ P) :=
  algebraQuotientOfLEComap (le_of_eq (P.over_def p))

@[simp]
/--
lemma `algebraMap_mk_of_liesOver` / 引理 `algebraMap_mk_of_liesOver`

English:
lemma algebraMap_mk_of_liesOver
  given: (x : A)
  proof: rfl

中文:
引理 algebraMap_mk_of_liesOver
  条件: (x : A)
  证明: rfl
-/
lemma algebraMap_mk_of_liesOver (x : A) :
    algebraMap (A ⧸ p) (B ⧸ P) (Ideal.Quotient.mk p x) = Ideal.Quotient.mk P (algebraMap _ _ x) :=
  rfl

/--
Instance `isScalarTower_of_liesOver` / 实例 `isScalarTower_of_liesOver`

English:
instance isScalarTower_of_liesOver
  signature: : IsScalarTower R (A ⧸ p) (B ⧸ P)
  body: IsScalarTower.of_algebraMap_eq'
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)

中文:
实例 isScalarTower_of_liesOver
  签名: : 标量塔 R (A ⧸ p) (B ⧸ P)
  定义体: IsScalarTower.of_algebraMap_eq'
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)

Depends on / 依赖: IsScalarTower, IsScalarTower.algebraMap_eq, IsScalarTower.of_algebraMap_eq, algebraMap, algebraMap_eq, of_algebraMap_eq
-/
instance isScalarTower_of_liesOver : IsScalarTower R (A ⧸ p) (B ⧸ P) :=
IsScalarTower.of_algebraMap_eq'
    congrArg (algebraMap B (B ⧸ P)).comp (IsScalarTower.algebraMap_eq R A B)

/--
Instance `instFaithfulSMul` / 实例 `instFaithfulSMul`

English:
instance instFaithfulSMul
  signature: : FaithfulSMul (A ⧸ p) (B ⧸ P)
  body: by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [map_sub]
  exact Quotient.eq.mp hab

中文:
实例 instFaithfulSMul
  签名: : 忠实标量乘法 (A ⧸ p) (B ⧸ P)
  定义体: by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [map_sub]
  exact Quotient.eq.mp hab

Depends on / 依赖: Quotient, Quotient.eq.mp, Quotient.eq.mpr, faithfulSMul_iff_algebraMap_injective, map_sub, mem_of_liesOver
-/
instance instFaithfulSMul : FaithfulSMul (A ⧸ p) (B ⧸ P) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  rintro ⟨a⟩ ⟨b⟩ hab
  apply Quotient.eq.mpr ((mem_of_liesOver P p (a - b)).mpr _)
  rw [map_sub]
  exact Quotient.eq.mp hab

variable {p} in
/--
theorem `nontrivial_of_liesOver_of_ne_top` / 定理 `nontrivial_of_liesOver_of_ne_top`

English:
theorem nontrivial_of_liesOver_of_ne_top
  given: (hp : p != ⊤)
  statement: Nontrivial (B ⧸ P)
  proof: by
  rwa [Quotient.nontrivial_iff, ne_top_iff_of_liesOver _ p]

中文:
定理 nontrivial_of_liesOver_of_ne_top
  条件: (hp : p != ⊤)
  结论: 非平凡 (B ⧸ P)
  证明: by
  rwa [Quotient.nontrivial_iff, ne_top_iff_of_liesOver _ p]

Depends on / 依赖: Quotient, Quotient.nontrivial_iff, ne_top_iff_of_liesOver, nontrivial_iff
-/
theorem nontrivial_of_liesOver_of_ne_top (hp : p != ⊤) : Nontrivial (B ⧸ P) := by
  rwa [Quotient.nontrivial_iff, ne_top_iff_of_liesOver _ p]

/--
theorem `nontrivial_of_liesOver_of_isPrime` / 定理 `nontrivial_of_liesOver_of_isPrime`

English:
theorem nontrivial_of_liesOver_of_isPrime
  given: [hp : p.IsPrime]
  statement: Nontrivial (B ⧸ P)
  proof: nontrivial_of_liesOver_of_ne_top P hp.ne_top

中文:
定理 nontrivial_of_liesOver_of_isPrime
  条件: [hp : p.是素]
  结论: 非平凡 (B ⧸ P)
  证明: nontrivial_of_liesOver_of_ne_top P hp.ne_top

Depends on / 依赖: hp.ne_top, ne_top, nontrivial_of_liesOver_of_ne_top
-/
theorem nontrivial_of_liesOver_of_isPrime [hp : p.IsPrime] : Nontrivial (B ⧸ P) :=
  nontrivial_of_liesOver_of_ne_top P hp.ne_top

section algEquiv

variable {P} {E : Type*} [EquivLike E B C] [AlgEquivClass E A B C] (σ : E)

/--
Definition of `algEquivOfEqMap` / `algEquivOfEqMap` 的定义

English:
definition algEquivOfEqMap
  signature: (h : Q = P.map σ)
  body: quotientEquiv P Q (RingEquivClass.toRingEquiv σ) h
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgHomClass.commutes σ x)

@[simp]

中文:
定义 algEquivOfEqMap
  签名: (h : Q = P.map σ)
  定义体: quotientEquiv P Q (RingEquivClass.toRingEquiv σ) h
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgHomClass.commutes σ x)

@[simp]

Depends on / 依赖: RingEquivClass, RingEquivClass.toRingEquiv, quotientEquiv, toRingEquiv
-/
def algEquivOfEqMap (h : Q = P.map σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) where
  __ := quotientEquiv P Q (RingEquivClass.toRingEquiv σ) h
  commutes' := by
    rintro ⟨x⟩
    exact congrArg (Ideal.Quotient.mk Q) (AlgHomClass.commutes σ x)

@[simp]
/--
theorem `algEquivOfEqMap_apply` / 定理 `algEquivOfEqMap_apply`

English:
theorem algEquivOfEqMap_apply
  given: (h : Q = P.map σ) (x : B)
  statement: algEquivOfEqMap p σ h x = σ x
  proof: rfl

中文:
定理 algEquivOfEqMap_apply
  条件: (h : Q = P.map σ) (x : B)
  结论: algEquivOfEqMap p σ h x = σ x
  证明: rfl
-/
theorem algEquivOfEqMap_apply (h : Q = P.map σ) (x : B) : algEquivOfEqMap p σ h x = σ x :=
  rfl

/--
Definition of `algEquivOfEqComap` / `algEquivOfEqComap` 的定义

English:
definition algEquivOfEqComap
  signature: (h : P = Q.comap σ)
  body: algEquivOfEqMap p σ ((congrArg (map σ) h).trans (Q.map_comap_eq_self_of_equiv σ)).symm

@[simp]

中文:
定义 algEquivOfEqComap
  签名: (h : P = Q.comap σ)
  定义体: algEquivOfEqMap p σ ((congrArg (map σ) h).trans (Q.map_comap_eq_self_of_equiv σ)).symm

@[simp]

Depends on / 依赖: Q.map_comap_eq_self_of_equiv, algEquivOfEqMap, map_comap_eq_self_of_equiv
-/
def algEquivOfEqComap (h : P = Q.comap σ) : (B ⧸ P) ≃ₐ[A ⧸ p] (C ⧸ Q) :=
  algEquivOfEqMap p σ ((congrArg (map σ) h).trans (Q.map_comap_eq_self_of_equiv σ)).symm

@[simp]
/--
theorem `algEquivOfEqComap_apply` / 定理 `algEquivOfEqComap_apply`

English:
theorem algEquivOfEqComap_apply
  given: (h : P = Q.comap σ) (x : B)
  statement: algEquivOfEqComap p σ h x = σ x
  proof: rfl

中文:
定理 algEquivOfEqComap_apply
  条件: (h : P = Q.comap σ) (x : B)
  结论: algEquivOfEqComap p σ h x = σ x
  证明: rfl
-/
theorem algEquivOfEqComap_apply (h : P = Q.comap σ) (x : B) : algEquivOfEqComap p σ h x = σ x :=
  rfl

end algEquiv

/--
Definition of `stabilizerHom` / `stabilizerHom` 的定义

English:
definition stabilizerHom
  signature: : MulAction.stabilizer G P ->* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  body: algEquivOfEqMap p (MulSemiringAction.toAlgEquiv A B g) g.2.symm
  map_one' := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (one_smul G x)
  map_mul' g h := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (mul_smul g h x)

中文:
定义 stabilizerHom
  签名: : 乘法作用.stabilizer G P ->* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  定义体: algEquivOfEqMap p (MulSemiringAction.toAlgEquiv A B g) g.2.symm
  map_one' := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (one_smul G x)
  map_mul' g h := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (mul_smul g h x)

Depends on / 依赖: MulSemiringAction, MulSemiringAction.toAlgEquiv, algEquivOfEqMap, toAlgEquiv
-/
def stabilizerHom : MulAction.stabilizer G P ->* ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) where
  toFun g := algEquivOfEqMap p (MulSemiringAction.toAlgEquiv A B g) g.2.symm
  map_one' := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (one_smul G x)
  map_mul' g h := by
    ext ⟨x⟩
    exact congrArg (Ideal.Quotient.mk P) (mul_smul g h x)

/--
theorem `stabilizerHom_apply` / 定理 `stabilizerHom_apply`

English:
theorem stabilizerHom_apply
  given: (g : MulAction.stabilizer G P) (b : B)
  proof: rfl

中文:
定理 stabilizerHom_apply
  条件: (g : 乘法作用.stabilizer G P) (b : B)
  证明: rfl
-/
@[simp] theorem stabilizerHom_apply (g : MulAction.stabilizer G P) (b : B) :
    stabilizerHom P p G g b = ↑(g • b) :=
  rfl

/--
lemma `ker_stabilizerHom` / 引理 `ker_stabilizerHom`

English:
lemma ker_stabilizerHom
  statement: (stabilizerHom P p G).ker = P.inertia (MulAction.stabilizer G P)
  proof: by
  ext σ
  simp [DFunLike.ext_iff, mk_surjective.forall, Quotient.eq]

中文:
引理 ker_stabilizerHom
  结论: (stabilizerHom P p G).ker = P.inertia (乘法作用.stabilizer G P)
  证明: by
  ext σ
  simp [DFunLike.ext_iff, mk_surjective.forall, Quotient.eq]

Depends on / 依赖: DFunLike, DFunLike.ext_iff, Quotient, Quotient.eq, ext_iff, mk_surjective, mk_surjective.forall
-/
lemma ker_stabilizerHom : (stabilizerHom P p G).ker = P.inertia (MulAction.stabilizer G P) := by
  ext σ
  simp [DFunLike.ext_iff, mk_surjective.forall, Quotient.eq]

/--
theorem `map_ker_stabilizer_subtype` / 定理 `map_ker_stabilizer_subtype`

English:
theorem map_ker_stabilizer_subtype
  proof: by
  simp [ker_stabilizerHom, Ideal.inertia_le_stabilizer]

中文:
定理 map_ker_stabilizer_subtype
  证明: by
  simp [ker_stabilizerHom, Ideal.inertia_le_stabilizer]

Depends on / 依赖: Ideal.inertia_le_stabilizer, inertia_le_stabilizer, ker_stabilizerHom
-/
theorem map_ker_stabilizer_subtype :
    (stabilizerHom P p G).ker.map (Subgroup.subtype _) = P.inertia G := by
  simp [ker_stabilizerHom, Ideal.inertia_le_stabilizer]

instance (p : Ideal R) (P : Ideal A) [P.IsPrime] [P.LiesOver p] :
    (P.map (Ideal.Quotient.mk <| p.map (algebraMap R A))).IsPrime := by
  apply Ideal.isPrime_map_quotientMk_of_isPrime
  rw [Ideal.map_le_iff_le_comap]; rw [Ideal.LiesOver.over (p := p) (P := P)]

end Quotient

end ideal_liesOver

section primesOver

variable {A : Type*} [CommSemiring A] (p : Ideal A) (B : Type*) [Semiring B] [Algebra A B]

/--
Definition of `primesOver` / `primesOver` 的定义

English:
definition primesOver
  signature: : Set (Ideal B)
  body: { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

中文:
定义 primesOver
  签名: : 集合 (理想 B)
  定义体: { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

Depends on / 依赖: IsPrime, LiesOver, P.IsPrime, P.LiesOver
-/
def primesOver : Set (Ideal B) :=
  { P : Ideal B | P.IsPrime ∧ P.LiesOver p }

variable {B}

/--
Instance `primesOver.isPrime` / 实例 `primesOver.isPrime`

English:
instance primesOver.isPrime
  signature: (Q : primesOver p B)
  body: Q.2.1

中文:
实例 primesOver.isPrime
  签名: (Q : primesOver p B)
  定义体: Q.2.1
-/
instance primesOver.isPrime (Q : primesOver p B) : Q.1.IsPrime :=
  Q.2.1

/--
Instance `primesOver.liesOver` / 实例 `primesOver.liesOver`

English:
instance primesOver.liesOver
  signature: (Q : primesOver p B)
  body: Q.2.2

中文:
实例 primesOver.liesOver
  签名: (Q : primesOver p B)
  定义体: Q.2.2
-/
instance primesOver.liesOver (Q : primesOver p B) : Q.1.LiesOver p :=
  Q.2.2

/--
Definition of `primesOver.mk` / `primesOver.mk` 的定义

English:
abbreviation primesOver.mk
  signature: (P : Ideal B) [hPp : P.IsPrime] [hp : P.LiesOver p]
  body: ⟨P, ⟨hPp, hp⟩⟩

中文:
缩写 primesOver.mk
  签名: (P : 理想 B) [hPp : P.是素] [hp : P.LiesOver p]
  定义体: ⟨P, ⟨hPp, hp⟩⟩
-/
abbrev primesOver.mk (P : Ideal B) [hPp : P.IsPrime] [hp : P.LiesOver p] : primesOver p B :=
  ⟨P, ⟨hPp, hp⟩⟩

variable {p} in
/--
theorem `ne_bot_of_mem_primesOver` / 定理 `ne_bot_of_mem_primesOver`

English:
theorem ne_bot_of_mem_primesOver
  statement: [FaithfulSMul A B] (hp : p != ⊥) {P : Ideal B}
  proof: by
  have : P.LiesOver p := hP.2
  exact ne_bot_of_liesOver_of_ne_bot hp P

中文:
定理 ne_bot_of_mem_primesOver
  结论: [忠实标量乘法 A B] (hp : p != ⊥) {P : 理想 B}
  证明: by
  have : P.LiesOver p := hP.2
  exact ne_bot_of_liesOver_of_ne_bot hp P

Depends on / 依赖: LiesOver, P.LiesOver, ne_bot_of_liesOver_of_ne_bot
-/
theorem ne_bot_of_mem_primesOver [FaithfulSMul A B] (hp : p != ⊥) {P : Ideal B}
    (hP : P in p.primesOver B) : P != ⊥ := by
  have : P.LiesOver p := hP.2
  exact ne_bot_of_liesOver_of_ne_bot hp P

end primesOver

end Ideal
