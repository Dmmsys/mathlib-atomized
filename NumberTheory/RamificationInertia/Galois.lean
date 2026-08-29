/-
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu, Jiedong Jiang
-/
module

public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Ramification theory in Galois extensions of Dedekind domains

In this file, we discuss the ramification theory in Galois extensions of Dedekind domains, which is
  also called Hilbert's Ramification Theory.

Assume `B / A` is a finite extension of Dedekind domains, `K` is the fraction ring of `A`,
  `L` is the fraction ring of `K`, `L / K` is a Galois extension.

## Main definitions

* `Ideal.ramificationIdxIn`: It can be seen from
  the theorem `Ideal.ramificationIdx_eq_of_isGaloisGroup` that all `Ideal.ramificationIdx` over a
  fixed maximal ideal `p` of `A` are the same, which we define as `Ideal.ramificationIdxIn`.

* `Ideal.inertiaDegIn`: It can be seen from
  the theorem `Ideal.inertiaDeg_eq_of_isGaloisGroup` that all `Ideal.inertiaDeg` over a fixed
  maximal ideal `p` of `A` are the same, which we define as `Ideal.inertiaDegIn`.

## Main results

* `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`: Let `p` be a prime of `A`,
  `r` be the number of prime ideals lying over `p`, `e` be the ramification index of `p` in `B`,
  and `f` be the inertia degree of `p` in `B`. Then `r * (e * f) = [L : K]`. It is the form of the
  `Ideal.sum_ramification_inertia` in the case of Galois extension.

* `Ideal.card_inertia_eq_ramificationIdxIn`:
  The cardinality of the inertia group is equal to the ramification index.

## References

* [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

-/

@[expose] public section

open Algebra Module
open scoped Pointwise

attribute [local instance] FractionRing.liftAlgebra

namespace Ideal

open scoped Classical in
/--
Definition of `ramificationIdxIn` / `ramificationIdxIn` 的定义

English:
definition ramificationIdxIn
  signature: {A : Type*} [CommRing A] (p : Ideal A)
  body: if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.ramificationIdx A
  else 0

中文:
定义 ramificationIdxIn
  签名: {A : 类型} [交换环 A] (p : 理想 A)
  定义体: if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.ramificationIdx A
  else 0

Depends on / 依赖: IndepFun, IndepFun.congr, IsPrime, LiesOver, Measure, Measure.ae_ae_of_ae_comp, P.IsPrime, P.LiesOver, ae_ae_of_ae_comp, ae_eq_mk, filter_upwards, h.choose.ramificationIdx, hf_Indep, hf_meas, iIndepFun, iIndepFun.congr, iIndepFun.indepFun_prodMk, indepFun_prodMk, measurable_mk, ramificationIdx
-/
noncomputable def ramificationIdxIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : Nat :=
  if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.ramificationIdx A
  else 0

open scoped Classical in
/--
Definition of `inertiaDegIn` / `inertiaDegIn` 的定义

English:
definition inertiaDegIn
  signature: {A : Type*} [CommRing A] (p : Ideal A)
  body: if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.inertiaDeg A else 0

中文:
定义 inertiaDegIn
  签名: {A : 类型} [交换环 A] (p : 理想 A)
  定义体: if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.inertiaDeg A else 0

Depends on / 依赖: Finset, IsPrime, LiesOver, Measurable, P.IsPrime, P.LiesOver, classical, fun_prop, h.choose.inertiaDeg, hf_indep, hf_indep.indepFun_finset, hf_meas, indepFun_finset, inertiaDeg, mem_insert_of_mem, mem_insert_self, mem_singleton_self
-/
noncomputable def inertiaDegIn {A : Type*} [CommRing A] (p : Ideal A)
    (B : Type*) [CommRing B] [Algebra A B] : Nat :=
  if h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p then h.choose.inertiaDeg A else 0

section MulAction

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] {p : Ideal A}
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (primesOver p B)
  body: primesOver.mk p (σ • Q.1)
  one_smul Q := Subtype.ext (one_smul G Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

@[simp]

中文:
实例 :
  签名: 乘法作用 G (primesOver p B)
  定义体: primesOver.mk p (σ • Q.1)
  one_smul Q := Subtype.ext (one_smul G Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

@[simp]

Depends on / 依赖: IndepFun, IndepFun.congr, Measure, Measure.ae_ae_of_ae_comp, ae_ae_of_ae_comp, ae_eq_mk, filter_upwards, hf_indep, hf_meas, iIndepFun, iIndepFun.congr, iIndepFun.indepFun_prodMk_prodMk, indepFun_prodMk_prodMk, measurable_mk, primesOver, primesOver.mk
-/
instance : MulAction G (primesOver p B) where
  smul σ Q := primesOver.mk p (σ • Q.1)
  one_smul Q := Subtype.ext (one_smul G Q.1)
  mul_smul σ τ Q := Subtype.ext (mul_smul σ τ Q.1)

@[simp]
/--
theorem `coe_smul_primesOver` / 定理 `coe_smul_primesOver`

English:
theorem coe_smul_primesOver
  given: (σ : G) (P : primesOver p B)
  statement: (σ • P).1 = σ • P.1
  proof: rfl

@[simp]

中文:
定理 coe_smul_primesOver
  条件: (σ : G) (P : primesOver p B)
  结论: (σ • P).1 = σ • P.1
  证明: rfl

@[simp]

Depends on / 依赖: IndepFun, hf_indep, hf_indep.indepFun_prodMk, hf_meas, indepFun_prodMk, measurable_fst, measurable_fst.mul, measurable_id, measurable_snd, this.comp
-/
theorem coe_smul_primesOver (σ : G) (P : primesOver p B) : (σ • P).1 = σ • P.1 :=
  rfl

@[simp]
/--
theorem `coe_smul_primesOver_mk` / 定理 `coe_smul_primesOver_mk`

English:
theorem coe_smul_primesOver_mk
  given: (σ : G) (P : Ideal B) [P.IsPrime] [P.LiesOver p]
  proof: rfl

中文:
定理 coe_smul_primesOver_mk
  条件: (σ : G) (P : 理想 B) [P.是素] [P.LiesOver p]
  证明: rfl

Depends on / 依赖: IndepFun, hf_indep, hf_indep.indepFun_prodMk, hf_meas, measurable_fst, measurable_fst.mul, measurable_id, measurable_snd, this.comp
-/
theorem coe_smul_primesOver_mk (σ : G) (P : Ideal B) [P.IsPrime] [P.LiesOver p] :
    (σ • primesOver.mk p P).1 = σ • P :=
  rfl

variable (K L : Type*) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra B L]
  [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [IsIntegralClosure B A L] [FiniteDimensional K L]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction Gal(L/K) (primesOver p B)
  body: primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = Q.1
    simpa only [map_one] using! map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = map _ (map _ Q.1)
    rw [map_mul]
    exact (Q.1.map_map

中文:
实例 :
  签名: 乘法作用 Gal(L/K) (primesOver p B)
  定义体: primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = Q.1
    simpa only [map_one] using! map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = map _ (map _ Q.1)
    rw [map_mul]
    exact (Q.1.map_map

Depends on / 依赖: galRestrict, hf_indep, hf_indep.indepFun_mul_left, hf_meas, hij.symm, hik.symm, indepFun_mul_left, primesOver, primesOver.mk
-/
noncomputable instance : MulAction Gal(L/K) (primesOver p B) where
  smul σ Q := primesOver.mk p (map (galRestrict A K L B σ) Q.1)
  one_smul Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = Q.1
    simpa only [map_one] using! map_id Q.1
  mul_smul σ τ Q := by
    apply Subtype.val_inj.mp
    change map _ Q.1 = map _ (map _ Q.1)
    rw [map_mul]
    exact (Q.1.map_map ((galRestrict A K L B) τ).toRingHom ((galRestrict A K L B) σ).toRingHom).symm

/--
theorem `coe_smul_primesOver_eq_map_galRestrict` / 定理 `coe_smul_primesOver_eq_map_galRestrict`

English:
theorem coe_smul_primesOver_eq_map_galRestrict
  given: (σ : Gal(L/K)) (P : primesOver p B)
  proof: rfl

中文:
定理 coe_smul_primesOver_eq_map_galRestrict
  条件: (σ : Gal(L/K)) (P : primesOver p B)
  证明: rfl

Depends on / 依赖: hf_indep, hf_indep.indepFun_mul_left, hf_meas, hij.symm, hik.symm
-/
theorem coe_smul_primesOver_eq_map_galRestrict (σ : Gal(L/K)) (P : primesOver p B) :
    (σ • P).1 = map (galRestrict A K L B σ) P :=
  rfl

/--
theorem `coe_smul_primesOver_mk_eq_map_galRestrict` / 定理 `coe_smul_primesOver_mk_eq_map_galRestrict`

English:
theorem coe_smul_primesOver_mk_eq_map_galRestrict
  statement: (σ : Gal(L/K)) (P : Ideal B) [P.IsPrime]
  proof: rfl

中文:
定理 coe_smul_primesOver_mk_eq_map_galRestrict
  结论: (σ : Gal(L/K)) (P : 理想 B) [P.是素]
  证明: rfl

Depends on / 依赖: hf_indep, hf_indep.indepFun_prodMk_prodMk, hf_meas, indepFun_prodMk_prodMk, measurable_mul
-/
theorem coe_smul_primesOver_mk_eq_map_galRestrict (σ : Gal(L/K)) (P : Ideal B) [P.IsPrime]
    [P.LiesOver p] : (σ • primesOver.mk p P).1 = map (galRestrict A K L B σ) P :=
  rfl

end MulAction

section RamificationInertia

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) (P Q : Ideal B)
  [hPp : P.IsPrime] [hp : P.LiesOver p] [hQp : Q.IsPrime] [Q.LiesOver p]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

include p in
/--
theorem `exists_smul_eq_of_isGaloisGroup` / 定理 `exists_smul_eq_of_isGaloisGroup`

English:
theorem exists_smul_eq_of_isGaloisGroup
  statement: exists σ : G, σ • P = Q
  proof: by
rcases IsInvariant.exists_smul_of_under_eq A B G P Q
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩

中文:
定理 存在_smul_eq_of_isGaloisGroup
  结论: 存在 σ : G, σ • P = Q
  证明: by
rcases IsInvariant.exists_smul_of_under_eq A B G P Q
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩

Depends on / 依赖: IsInvariant, IsInvariant.exists_smul_of_under_eq, exists_smul_of_under_eq, hf_indep, hf_indep.indepFun_prodMk_prodMk, hf_meas, hs.symm, measurable_mul, over_def, symm.trans
-/
theorem exists_smul_eq_of_isGaloisGroup : exists σ : G, σ • P = Q := by
rcases IsInvariant.exists_smul_of_under_eq A B G P Q
    (over_def P p).symm.trans (over_def Q p) with ⟨σ, hs⟩
  exact ⟨σ, hs.symm⟩

/--
Instance `isPretransitive_of_isGaloisGroup` / 实例 `isPretransitive_of_isGaloisGroup`

English:
instance isPretransitive_of_isGaloisGroup
  signature: : MulAction.IsPretransitive G (primesOver p B) where
  body: by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

include p G in

中文:
实例 isPretransitive_of_isGaloisGroup
  签名: : 乘法作用.是Pretransitive G (primesOver p B) where
  定义体: by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

include p G in

Depends on / 依赖: IndepFun, Subtype, Subtype.val_inj.mp, exists_smul_eq_of_isGaloisGroup, hf_indep, hf_indep.indepFun_prodMk, hf_meas, indepFun_prodMk, measurable_fst, measurable_fst.div, measurable_id, measurable_snd, this.comp, val_inj
-/
instance isPretransitive_of_isGaloisGroup : MulAction.IsPretransitive G (primesOver p B) where
  exists_smul_eq := by
    intro ⟨P, _, _⟩ ⟨Q, _, _⟩
    rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, hs⟩
    exact ⟨σ, Subtype.val_inj.mp hs⟩

include p G in
/--
theorem `ramificationIdx_eq_of_isGaloisGroup` / 定理 `ramificationIdx_eq_of_isGaloisGroup`

English:
theorem ramificationIdx_eq_of_isGaloisGroup
  proof: by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [ramificationIdx_smul]

include p G in

中文:
定理 ramificationIdx_eq_of_isGaloisGroup
  证明: by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [ramificationIdx_smul]

include p G in

Depends on / 依赖: IndepFun, exists_smul_eq_of_isGaloisGroup, hf_indep, hf_indep.indepFun_prodMk, hf_meas, measurable_fst, measurable_fst.div, measurable_id, measurable_snd, ramificationIdx_smul, this.comp
-/
theorem ramificationIdx_eq_of_isGaloisGroup :
    P.ramificationIdx A = Q.ramificationIdx A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [ramificationIdx_smul]

include p G in
/--
theorem `inertiaDeg_eq_of_isGaloisGroup` / 定理 `inertiaDeg_eq_of_isGaloisGroup`

English:
theorem inertiaDeg_eq_of_isGaloisGroup
  proof: by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [inertiaDeg_smul]

include p G in

中文:
定理 inertiaDeg_eq_of_isGaloisGroup
  证明: by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [inertiaDeg_smul]

include p G in

Depends on / 依赖: exists_smul_eq_of_isGaloisGroup, hf_indep, hf_indep.indepFun_div_left, hf_meas, hij.symm, hik.symm, indepFun_div_left, inertiaDeg_smul
-/
theorem inertiaDeg_eq_of_isGaloisGroup :
    P.inertiaDeg A = Q.inertiaDeg A := by
  rcases exists_smul_eq_of_isGaloisGroup p P Q G with ⟨σ, rfl⟩
  rw [inertiaDeg_smul]

include p G in
/--
theorem `ramificationIdxIn_eq_ramificationIdx` / 定理 `ramificationIdxIn_eq_ramificationIdx`

English:
theorem ramificationIdxIn_eq_ramificationIdx
  proof: by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn]; rw [dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in

中文:
定理 ramificationIdxIn_eq_ramificationIdx
  证明: by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn]; rw [dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in

Depends on / 依赖: IsPrime, LiesOver, P.IsPrime, P.LiesOver, choose_spec, dif_pos, h.choose, h.choose_spec, hf_indep, hf_indep.indepFun_div_left, hf_meas, hij.symm, hik.symm, ramificationIdxIn, ramificationIdx_eq_of_isGaloisGroup
-/
theorem ramificationIdxIn_eq_ramificationIdx :
    ramificationIdxIn p B = P.ramificationIdx A := by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [ramificationIdxIn]; rw [dif_pos h]
  exact ramificationIdx_eq_of_isGaloisGroup p h.choose P G

include G in
/--
theorem `ramificationIdxIn_ne_zero` / 定理 `ramificationIdxIn_ne_zero`

English:
theorem ramificationIdxIn_ne_zero
  given: [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime]
  proof: by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact (P.1.ramificationIdx_pos A).ne'

include G in

中文:
定理 ramificationIdxIn_ne_zero
  条件: [模.有限 A B] [忠实标量乘法 A B] {p : 理想 A} [p.是素]
  证明: by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact (P.1.ramificationIdx_pos A).ne'

include G in

Depends on / 依赖: Nonempty, hf_indep, hf_indep.indepFun_prodMk_prodMk, hf_meas, indepFun_prodMk_prodMk, measurable_div, primesOver, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_pos
-/
theorem ramificationIdxIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    p.ramificationIdxIn B != 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [ramificationIdxIn_eq_ramificationIdx p P G]
  exact (P.1.ramificationIdx_pos A).ne'

include G in
/--
theorem `inertiaDegIn_eq_inertiaDeg` / 定理 `inertiaDegIn_eq_inertiaDeg`

English:
theorem inertiaDegIn_eq_inertiaDeg
  proof: by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn]; rw [dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in

中文:
定理 inertiaDegIn_eq_inertiaDeg
  证明: by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn]; rw [dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in

Depends on / 依赖: IsPrime, LiesOver, P.IsPrime, P.LiesOver, choose_spec, dif_pos, h.choose, h.choose_spec, hf_indep, hf_indep.indepFun_prodMk_prodMk, hf_meas, inertiaDegIn, inertiaDeg_eq_of_isGaloisGroup, measurable_div
-/
theorem inertiaDegIn_eq_inertiaDeg :
    inertiaDegIn p B = P.inertiaDeg A := by
  have h : exists P : Ideal B, P.IsPrime ∧ P.LiesOver p := ⟨P, hPp, hp⟩
  obtain ⟨_, _⟩ := h.choose_spec
  rw [inertiaDegIn]; rw [dif_pos h]
  exact inertiaDeg_eq_of_isGaloisGroup p h.choose P G

include G in
/--
theorem `inertiaDegIn_ne_zero` / 定理 `inertiaDegIn_ne_zero`

English:
theorem inertiaDegIn_ne_zero
  given: [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime]
  proof: by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact (P.1.inertiaDeg_pos A).ne'

中文:
定理 inertiaDegIn_ne_zero
  条件: [模.有限 A B] [忠实标量乘法 A B] {p : 理想 A} [p.是素]
  证明: by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact (P.1.inertiaDeg_pos A).ne'

Depends on / 依赖: Finset, Finset.mem_singleton_self, Finset.prod_apply, Finset.prod_c, Function, Function.comp_apply, Measurable, Nonempty, comp_apply, h_left, h_meas_right, h_right, inertiaDegIn_eq_inertiaDeg, inertiaDeg_pos, measurable_pi_apply, mem_singleton_self, primesOver, prod_apply, prod_c
-/
theorem inertiaDegIn_ne_zero [Module.Finite A B] [FaithfulSMul A B] {p : Ideal A} [p.IsPrime] :
    inertiaDegIn p B != 0 := by
  obtain ⟨P⟩ := (inferInstance : Nonempty (primesOver p B))
  rw [inertiaDegIn_eq_inertiaDeg p P G]
  exact (P.1.inertiaDeg_pos A).ne'

section tower

variable (C : Type*) [CommRing C] [Algebra A C] [Algebra B C]
  [Nonempty (P.primesOver C)] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]
  (GBC : Type*) [Group GBC] [Finite GBC] [MulSemiringAction GBC C] [IsGaloisGroup GBC B C]

include G GAC GBC in
/--
theorem `inertiaDegIn_mul_inertiaDegIn` / 定理 `inertiaDegIn_mul_inertiaDegIn`

English:
theorem inertiaDegIn_mul_inertiaDegIn
  proof: by
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P G]; rw [inertiaDegIn_eq_inertiaDeg p Q GAC]; rw [inertiaDegIn_eq_inertiaDeg P Q GBC]; rw [← inertiaDeg_tower P Q]

中文:
定理 inertiaDegIn_mul_inertiaDegIn
  证明: by
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P G]; rw [inertiaDegIn_eq_inertiaDeg p Q GAC]; rw [inertiaDegIn_eq_inertiaDeg P Q GBC]; rw [← inertiaDeg_tower P Q]

Depends on / 依赖: IndepFun, IndepFun.congr, LiesOver, LiesOver.trans, Measure, Measure.ae_ae_of_ae_comp, Nonempty, Q.LiesOver, ae_ae_of_ae_comp, ae_all_i, ae_all_iff, ae_eq_mk, filter_upwards, hf_Indep, hf_meas, iIndepFun, iIndepFun.congr, iIndepFun.indepFun_finsetProd_of_notMem, indepFun_finsetProd_of_notMem, inertiaDegIn_eq_inertiaDeg
-/
theorem inertiaDegIn_mul_inertiaDegIn :
    p.inertiaDegIn B * P.inertiaDegIn C = p.inertiaDegIn C := by
  obtain ⟨⟨Q, _, _⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [inertiaDegIn_eq_inertiaDeg p P G]; rw [inertiaDegIn_eq_inertiaDeg p Q GAC]; rw [inertiaDegIn_eq_inertiaDeg P Q GBC]; rw [← inertiaDeg_tower P Q]

variable {p} in
include G GAC GBC in
/--
theorem `ramificationIdxIn_mul_ramificationIdxIn` / 定理 `ramificationIdxIn_mul_ramificationIdxIn`

English:
theorem ramificationIdxIn_mul_ramificationIdxIn
  given: [Flat B C]
  proof: by
  obtain ⟨⟨Q, _, hQ⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P G]; rw [ramificationIdxIn_eq_ramificationIdx p Q GAC]; rw [ramificationIdxIn_eq_ramificationIdx P Q GBC]; rw [← ramificationIdx_tower P

中文:
定理 ramificationIdxIn_mul_ramificationIdxIn
  条件: [平坦 B C]
  证明: by
  obtain ⟨⟨Q, _, hQ⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P G]; rw [ramificationIdxIn_eq_ramificationIdx p Q GAC]; rw [ramificationIdxIn_eq_ramificationIdx P Q GBC]; rw [← ramificationIdx_tower P

Depends on / 依赖: Finset, Finset.notMem_range_self, LiesOver, LiesOver.trans, Nonempty, Q.LiesOver, hf_Indep, hf_Indep.indepFun_finsetProd_of_notMem, hf_meas, indepFun_finsetProd_of_notMem, notMem_range_self, primesOver, ramificationIdxIn_eq_ramificationIdx, ramificationIdx_tower
-/
theorem ramificationIdxIn_mul_ramificationIdxIn [Flat B C] :
    p.ramificationIdxIn B * P.ramificationIdxIn C = p.ramificationIdxIn C := by
  obtain ⟨⟨Q, _, hQ⟩⟩ := (inferInstance : Nonempty (primesOver P C))
  have : Q.LiesOver p := LiesOver.trans Q P p
  rw [ramificationIdxIn_eq_ramificationIdx p P G]; rw [ramificationIdxIn_eq_ramificationIdx p Q GAC]; rw [ramificationIdxIn_eq_ramificationIdx P Q GBC]; rw [← ramificationIdx_tower P Q]

@[deprecated (since := "2026-06-18")] alias ramificationIdxIn_mul_ramificationIdxIn' :=
  ramificationIdxIn_mul_ramificationIdxIn

end tower

end RamificationInertia

section fundamental_identity

variable {A : Type*} [CommRing A] [IsDomain A] (p : Ideal A) [p.IsPrime]
  (B : Type*) [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B] [Flat A B]
  (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]

/--
theorem `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` / 定理 `ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`

English:
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
  proof: by
  have : Fintype (primesOver p B) := (QuasiFinite.finite_primesOver p).fintype
  rw [← smul_eq_mul]; rw [← Set.fintypeCard_eq_ncard]; rw [← Finset.card_univ]; rw [← Finset.sum_const]; rw [← sum_ramification_inertia_eq_card p B]
  apply Finset.sum_congr rfl
  intro P hp
  rw [ramificationIdxIn_eq_

中文:
定理 ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
  证明: by
  have : Fintype (primesOver p B) := (QuasiFinite.finite_primesOver p).fintype
  rw [← smul_eq_mul]; rw [← Set.fintypeCard_eq_ncard]; rw [← Finset.card_univ]; rw [← Finset.sum_const]; rw [← sum_ramification_inertia_eq_card p B]
  apply Finset.sum_congr rfl
  intro P hp
  rw [ramificationIdxIn_eq_

Depends on / 依赖: Finset, Finset.card_univ, Finset.notMem_range_self, Finset.sum_congr, Finset.sum_const, Fintype, QuasiFinite, QuasiFinite.finite_primesOver, Set.fintypeCard_eq_ncard, card_univ, finite_primesOver, fintype, fintypeCard_eq_ncard, hf_Indep, hf_Indep.indepFun_finsetProd_of_notMem, hf_meas, inertiaDegIn_eq_inertiaDeg, notMem_range_self, primesOver, ramificationIdxIn_eq_ramificationIdx
-/
theorem ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn :
    (primesOver p B).ncard * (ramificationIdxIn p B * inertiaDegIn p B) = Nat.card G := by
  have : Fintype (primesOver p B) := (QuasiFinite.finite_primesOver p).fintype
  rw [← smul_eq_mul]; rw [← Set.fintypeCard_eq_ncard]; rw [← Finset.card_univ]; rw [← Finset.sum_const]; rw [← sum_ramification_inertia_eq_card p B]
  apply Finset.sum_congr rfl
  intro P hp
  rw [ramificationIdxIn_eq_ramificationIdx p P G]; rw [inertiaDegIn_eq_inertiaDeg p P G]

end fundamental_identity

section tower

variable {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B] [FaithfulSMul A B] {p : Ideal A} (P : Ideal B)
  [P.IsPrime] [P.LiesOver p] (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
  [IsGaloisGroup G A B] (C : Type*) [CommRing C] [IsDomain C] [Algebra A C]
  [Algebra B C] [FaithfulSMul B C] [IsScalarTower A B C]
  (GAC : Type*) [Group GAC] [Finite GAC] [MulSemiringAction GAC C] [IsGaloisGroup GAC A C]

include G GAC in
open IsGaloisGroup MulAction in
/--
theorem `ncard_primesOver_mul_ncard_primesOver` / 定理 `ncard_primesOver_mul_ncard_primesOver`

English:
theorem ncard_primesOver_mul_ncard_primesOver
  proof: by
  have : Algebra.IsIntegral A C := isInvariant.isIntegral A C GAC
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let f := restrictHom GAC G A B C
  let H := (stabilizer G P).comap f
  have key (Q Q' : Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg : g • Q = Q') : g in H := by


中文:
定理 ncard_primesOver_mul_ncard_primesOver
  证明: by
  have : Algebra.IsIntegral A C := isInvariant.isIntegral A C GAC
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let f := restrictHom GAC G A B C
  let H := (stabilizer G P).comap f
  have key (Q Q' : Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg : g • Q = Q') : g in H := by


Depends on / 依赖: Algebra, Algebra.IsIntegral, Algebra.IsIntegral.tower_top, IsIntegral, LiesOver, MeasurableSet, MeasurableSet.empty, MeasurableSet.ite, MeasurableSet.union, Nonempty, P.primesOver, Q.LiesOver, Set.indicator_const_preimage_eq_union, Set.mem_singleton, classical, congr_arg, generateFrom, hsi.compl, iIndepFun_iff_measure_inter_preimage_eq_mul, indicator_const_preimage_eq_union
-/
theorem ncard_primesOver_mul_ncard_primesOver :
    (p.primesOver B).ncard * (P.primesOver C).ncard = (p.primesOver C).ncard := by
  have : Algebra.IsIntegral A C := isInvariant.isIntegral A C GAC
  have : Algebra.IsIntegral B C := Algebra.IsIntegral.tower_top A
  let f := restrictHom GAC G A B C
  let H := (stabilizer G P).comap f
  have key (Q Q' : Ideal C) [Q.LiesOver P] [Q'.LiesOver P] g (hg : g • Q = Q') : g in H := by
    simpa [← restrictHom_smul_under GAC G A, ← over_def _ P, H] using congr_arg (under B) hg
  obtain ⟨Q, _, _⟩ := (inferInstance : Nonempty (P.primesOver C))
  have : Q.LiesOver p := .trans Q P p
  have orbit_eq : orbit H Q = P.primesOver C := by
    ext Q'
    constructor
    · rintro ⟨g, rfl : g • Q = Q'⟩
      refine ⟨inferInstance, ?_⟩
      rw [liesOver_iff]; rw [H.smul_def]; rw [← restrictHom_smul_under GAC G A B C]; rw [← Q.over_def P]
      exact g.2.symm
    · rintro ⟨_, _⟩
      have : Q'.LiesOver p := .trans Q' P p
      obtain ⟨g, hg⟩ :=
        IsInvariant.exists_smul_of_under_eq A C GAC Q Q' ((Q.over_def p).symm.trans (Q'.over_def p))
      exact ⟨⟨g, key Q Q' g hg.symm⟩, by simpa [Subgroup.smul_def] using hg.symm⟩
  have stabilizer_eq : stabilizer H Q = (stabilizer GAC Q).subgroupOf H := by
    simp [Subgroup.ext_iff, Subgroup.mem_subgroupOf]
  rw [← IsInvariant.orbit_eq_primesOver A B G p P]; rw [← index_stabilizer]; rw [← orbit_eq]; rw [← index_stabilizer]; rw [stabilizer_eq]; rw [← Subgroup.relIndex]; rw [← IsInvariant.orbit_eq_primesOver A C GAC p Q]; rw [← index_stabilizer]; rw [← (stabilizer G P).index_comap_of_surjective (restrictHom_surjective GAC G A B C)]; rw [mul_comm]; rw [Subgroup.relIndex_mul_index]
  exact key Q Q

end tower

section inertia

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise

open Algebra

attribute [local instance] Ideal.Quotient.field in
/--
theorem `card_stabilizer_eq_card_inertia_mul_finrank` / 定理 `card_stabilizer_eq_card_inertia_mul_finrank`

English:
theorem card_stabilizer_eq_card_inertia_mul_finrank
  statement: (p : Ideal R) [p.IsPrime]
  proof: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((a

中文:
定理 card_stabilizer_eq_card_inertia_mul_finrank
  结论: (p : 理想 R) [p.是素]
  证明: by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((a

Depends on / 依赖: AtPrime, IsScalarTower, IsScalarTower.algebraMap_apply, Localization, Localization.AtPrime.algebraOfLiesOver, P.ResidueField, ResidueField, algebraMap, algebraMap_apply, algebraOfLiesOver, of_algebraMap_eq, p.ResidueField, toAlgebra
-/
theorem card_stabilizer_eq_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [inertiaDeg_eq p P]; rw [← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField]; rw [← this]; rw [← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index]; rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv]; rw [AddSubgroup.subgroupOf_inertia]

/--
lemma `ncard_primesOver_mul_card_inertia_mul_finrank` / 引理 `ncard_primesOver_mul_card_inertia_mul_finrank`

English:
lemma ncard_primesOver_mul_card_inertia_mul_finrank
  statement: (p : Ideal R) [p.IsPrime]
  proof: by
  rw [mul_assoc]; rw [← card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

中文:
引理 ncard_primesOver_mul_card_inertia_mul_finrank
  结论: (p : 理想 R) [p.是素]
  证明: by
  rw [mul_assoc]; rw [← card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

Depends on / 依赖: IsInvariant, IsInvariant.orbit_eq_primesOver, MulAction, MulAction.orbitProdStabilizerEquivGroup, Nat.card_congr, card_congr, card_stabilizer_eq_card_inertia_mul_finrank, mul_assoc, orbitProdStabilizerEquivGroup, orbit_eq_primesOver
-/
lemma ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [PerfectField p.ResidueField] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) * P.inertiaDeg R = Nat.card G := by
  rw [mul_assoc]; rw [← card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [← IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/--
lemma `card_inertia_eq_ramificationIdxIn` / 引理 `card_inertia_eq_ramificationIdxIn`

English:
lemma card_inertia_eq_ramificationIdxIn
  statement: [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
  proof: by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard != 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S != 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul

中文:
引理 card_inertia_eq_ramificationIdxIn
  结论: [是整环 R] [是整环 S] [模.有限 R S] [平坦 R S]
  证明: by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard != 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S != 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul

Depends on / 依赖: Nat.card_pos, card_pos, inertiaDegIn, inertiaDegIn_eq_inertiaDeg, mul_assoc, mul_left_inj, mul_right_inj, ncard_primesOver_mul_card_inertia_mul_finrank, ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn, p.inertiaDegIn, p.primesOver, primesOver
-/
lemma card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard != 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S != 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

/--
lemma `card_stabilizer_eq` / 引理 `card_stabilizer_eq`

English:
lemma card_stabilizer_eq
  statement: [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
  proof: by
  rw [card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [card_inertia_eq_ramificationIdxIn p]; rw [inertiaDegIn_eq_inertiaDeg p P G]

中文:
引理 card_stabilizer_eq
  结论: [是整环 R] [是整环 S] [模.有限 R S] [平坦 R S]
  证明: by
  rw [card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [card_inertia_eq_ramificationIdxIn p]; rw [inertiaDegIn_eq_inertiaDeg p P G]

Depends on / 依赖: card_inertia_eq_ramificationIdxIn, card_stabilizer_eq_card_inertia_mul_finrank, inertiaDegIn_eq_inertiaDeg
-/
lemma card_stabilizer_eq [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [PerfectField p.ResidueField] :
    Nat.card (MulAction.stabilizer G P) = p.ramificationIdxIn S * p.inertiaDegIn S := by
  rw [card_stabilizer_eq_card_inertia_mul_finrank p P]; rw [card_inertia_eq_ramificationIdxIn p]; rw [inertiaDegIn_eq_inertiaDeg p P G]

end inertia

section galRestrict

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra S L]
    [Algebra K L] [Algebra R L] [IsScalarTower R S L] [IsScalarTower R K L]
    [IsIntegralClosure S R L] [FiniteDimensional K L]

/--
lemma `exists_comap_galRestrict_eq` / 引理 `exists_comap_galRestrict_eq`

English:
lemma exists_comap_galRestrict_eq
  statement: [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
  proof: by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := 

中文:
引理 存在_comap_galRestrict_eq
  结论: [是Dedekind整环 R] [是Galois K L] {p : 理想 R}
  证明: by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := 

Depends on / 依赖: Finite, IsDomain, IsFractionRing, IsGaloisGroup, IsIntegralClosure, IsIntegralClosure.MulSemiringAction, IsIntegralClosure.equiv, IsIntegralClosure.finite, IsIntegralClosure.isDedekindDomain, IsIntegralClosure.isFractionRing_of_finite_extension, Module, Module.Finite, MulSemiringAction, finite, integralClosure, isDedekindDomain, isDomain, isFractionRing_of_finite_extension, toMulEquiv, toMulEquiv.isDomain
-/
lemma exists_comap_galRestrict_eq [IsDedekindDomain R] [IsGalois K L] {p : Ideal R}
    {P₁ P₂ : Ideal S} (hP₁ : P₁ in primesOver p S) (hP₂ : P₂ in primesOver p S) :
    exists σ, P₁.comap (galRestrict R K L S σ) = P₂ := by
  have : IsDomain S :=
    (IsIntegralClosure.equiv R S L (integralClosure R L)).toMulEquiv.isDomain (integralClosure R L)
  have := IsIntegralClosure.isDedekindDomain R K L S
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have := hP₁.1
  have := hP₁.2
  have := hP₂.1
  have := hP₂.2
  have : IsFractionRing S L := IsIntegralClosure.isFractionRing_of_finite_extension R K L S
  let : MulSemiringAction Gal(L/K) S := IsIntegralClosure.MulSemiringAction R K L S
  have : IsGaloisGroup Gal(L/K) R S := IsGaloisGroup.of_isFractionRing _ _ _ K L
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup p P₂ P₁ Gal(L/K)
  exact ⟨σ, comap_map_of_bijective _ ((galRestrict R K L S σ).bijective)⟩

end galRestrict

end Ideal
