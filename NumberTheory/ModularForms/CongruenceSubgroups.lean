/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups

/-!
# Congruence subgroups

This defines congruence subgroups of `SL(2, ℤ)` such as `Γ(N)`, `Γ₀(N)` and `Γ₁(N)` for `N` a
natural number.

It also contains basic results about congruence subgroups.

-/

@[expose] public section

open Matrix.SpecialLinearGroup Matrix

open scoped MatrixGroups ModularGroup Real

variable (N : Nat)

local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

@[simp]
/--
theorem `SL_reduction_mod_hom_val` / 定理 `SL_reduction_mod_hom_val`

English:
theorem SL_reduction_mod_hom_val
  given: (γ : SL(2, Int)) (i j : Fin 2)
  proof: rfl

中文:
定理 SL_reduction_mod_hom_val
  条件: (γ : SL(2, 整数)) (i j : Fin 2)
  证明: rfl
-/
theorem SL_reduction_mod_hom_val (γ : SL(2, Int)) (i j : Fin 2) :
    SLMOD(N) γ i j = (γ i j : ZMod N) :=
  rfl

namespace CongruenceSubgroup

/--
Definition of `Gamma` / `Gamma` 的定义

English:
definition Gamma
  signature: : Subgroup SL(2, Int)
  body: SLMOD(N).ker

@[inherit_doc] scoped notation "Γ(" n ")" => Gamma n

中文:
定义 Gamma
  签名: : Subgroup SL(2, 整数)
  定义体: SLMOD(N).ker

@[inherit_doc] scoped notation "Γ(" n ")" => Gamma n
-/
def Gamma : Subgroup SL(2, Int) :=
  SLMOD(N).ker

@[inherit_doc] scoped notation "Γ(" n ")" => Gamma n

/--
theorem `Gamma_mem'` / 定理 `Gamma_mem'`

English:
theorem Gamma_mem'
  given: {N} {γ : SL(2, Int)}
  statement: γ in Gamma N ↔ SLMOD(N) γ = 1
  proof: Iff.rfl

@[simp]

中文:
定理 Gamma_mem'
  条件: {N} {γ : SL(2, 整数)}
  结论: γ in Gamma N ↔ SLMOD(N) γ = 1
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem Gamma_mem' {N} {γ : SL(2, Int)} : γ in Gamma N ↔ SLMOD(N) γ = 1 :=
  Iff.rfl

@[simp]
/--
theorem `Gamma_mem` / 定理 `Gamma_mem`

English:
theorem Gamma_mem
  given: {N} {γ : SL(2, Int)}
  statement: γ in Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
  proof: by
  simp [Gamma_mem', SpecialLinearGroup.ext_iff, and_assoc]

中文:
定理 Gamma_mem
  条件: {N} {γ : SL(2, 整数)}
  结论: γ in Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
  证明: by
  simp [Gamma_mem', SpecialLinearGroup.ext_iff, and_assoc]

Depends on / 依赖: Gamma_mem, SpecialLinearGroup, SpecialLinearGroup.ext_iff, and_assoc, ext_iff
-/
theorem Gamma_mem {N} {γ : SL(2, Int)} : γ in Gamma N ↔ (γ 0 0 : ZMod N) = 1 ∧
    (γ 0 1 : ZMod N) = 0 ∧ (γ 1 0 : ZMod N) = 0 ∧ (γ 1 1 : ZMod N) = 1 := by
  simp [Gamma_mem', SpecialLinearGroup.ext_iff, and_assoc]

/--
theorem `Gamma_normal` / 定理 `Gamma_normal`

English:
theorem Gamma_normal
  statement: Subgroup.Normal (Gamma N)
  proof: SLMOD(N).normal_ker

中文:
定理 Gamma_normal
  结论: Subgroup.Normal (Gamma N)
  证明: SLMOD(N).normal_ker

Depends on / 依赖: normal_ker
-/
theorem Gamma_normal : Subgroup.Normal (Gamma N) :=
  SLMOD(N).normal_ker

/--
theorem `Gamma_one_top` / 定理 `Gamma_one_top`

English:
theorem Gamma_one_top
  statement: Gamma 1 = ⊤
  proof: by
  ext
  simp [eq_iff_true_of_subsingleton]

中文:
定理 Gamma_one_top
  结论: Gamma 1 = ⊤
  证明: by
  ext
  simp [eq_iff_true_of_subsingleton]

Depends on / 依赖: eq_iff_true_of_subsingleton
-/
theorem Gamma_one_top : Gamma 1 = ⊤ := by
  ext
  simp [eq_iff_true_of_subsingleton]

/--
lemma `mem_Gamma_one` / 引理 `mem_Gamma_one`

English:
lemma mem_Gamma_one
  given: (γ : SL(2, Int))
  statement: γ in Γ(1)
  proof: by
  simp only [Gamma_one_top, Subgroup.mem_top]

中文:
引理 mem_Gamma_one
  条件: (γ : SL(2, 整数))
  结论: γ in Γ(1)
  证明: by
  simp only [Gamma_one_top, Subgroup.mem_top]

Depends on / 依赖: Gamma_one_top, Subgroup, Subgroup.mem_top, mem_top
-/
lemma mem_Gamma_one (γ : SL(2, Int)) : γ in Γ(1) := by
  simp only [Gamma_one_top, Subgroup.mem_top]

/--
theorem `Gamma_one_coe_eq_SL` / 定理 `Gamma_one_coe_eq_SL`

English:
theorem Gamma_one_coe_eq_SL
  statement: (↑(Gamma 1) : Subgroup (GL (Fin 2) Real)) = 𝒮ℒ
  proof: by
  simp [Gamma_one_top, MonoidHom.range_eq_map]

中文:
定理 Gamma_one_coe_eq_SL
  结论: (↑(Gamma 1) : Subgroup (GL (Fin 2) 实数)) = 𝒮ℒ
  证明: by
  simp [Gamma_one_top, MonoidHom.range_eq_map]

Depends on / 依赖: Gamma_one_top, MonoidHom, MonoidHom.range_eq_map, range_eq_map
-/
theorem Gamma_one_coe_eq_SL : (↑(Gamma 1) : Subgroup (GL (Fin 2) Real)) = 𝒮ℒ := by
  simp [Gamma_one_top, MonoidHom.range_eq_map]

/--
theorem `Gamma_zero_bot` / 定理 `Gamma_zero_bot`

English:
theorem Gamma_zero_bot
  statement: Gamma 0 = ⊥
  proof: rfl

中文:
定理 Gamma_zero_bot
  结论: Gamma 0 = ⊥
  证明: rfl
-/
theorem Gamma_zero_bot : Gamma 0 = ⊥ := rfl

/--
lemma `ModularGroup_T_pow_mem_Gamma` / 引理 `ModularGroup_T_pow_mem_Gamma`

English:
lemma ModularGroup_T_pow_mem_Gamma
  given: (N M : Int) (hNM : N ∣ M)
  proof: by
  simp [ModularGroup.coe_T_zpow, hNM, ZMod.intCast_zmod_eq_zero_iff_dvd]

中文:
引理 ModularGroup_T_pow_mem_Gamma
  条件: (N M : 整数) (hNM : N ∣ M)
  证明: by
  simp [ModularGroup.coe_T_zpow, hNM, ZMod.intCast_zmod_eq_zero_iff_dvd]

Depends on / 依赖: ModularGroup, ModularGroup.coe_T_zpow, ZMod.intCast_zmod_eq_zero_iff_dvd, coe_T_zpow, intCast_zmod_eq_zero_iff_dvd
-/
lemma ModularGroup_T_pow_mem_Gamma (N M : Int) (hNM : N ∣ M) :
    (ModularGroup.T ^ M) in Gamma (Int.natAbs N) := by
  simp [ModularGroup.coe_T_zpow, hNM, ZMod.intCast_zmod_eq_zero_iff_dvd]

/--
Instance `instFiniteIndexGamma` / 实例 `instFiniteIndexGamma`

English:
instance instFiniteIndexGamma
  signature: [NeZero N]
  body: Subgroup.finiteIndex_ker _

中文:
实例 instFiniteIndexGamma
  签名: [NeZero N]
  定义体: Subgroup.finiteIndex_ker _

Depends on / 依赖: Subgroup, Subgroup.finiteIndex_ker, finiteIndex_ker
-/
instance instFiniteIndexGamma [NeZero N] : (Gamma N).FiniteIndex := Subgroup.finiteIndex_ker _

set_option backward.isDefEq.respectTransparency.types false in
/--
Definition of `Gamma0` / `Gamma0` 的定义

English:
definition Gamma0
  signature: : Subgroup SL(2, Int) where
  body: { g | (g 1 0 : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' {a} {b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_mul, Set.mem_ofPred_eq] at *
    simp [h, ha, hb]
  inv_mem' {a} ha := by
    simpa [SL2_inv_expl a] using ha

@[simp]

中文:
定义 Gamma0
  签名: : Subgroup SL(2, 整数) where
  定义体: { g | (g 1 0 : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' {a} {b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_mul, Set.mem_ofPred_eq] at *
    simp [h, ha, hb]
  inv_mem' {a} ha := by
    simpa [SL2_inv_expl a] using ha

@[simp]
-/
def Gamma0 : Subgroup SL(2, Int) where
  carrier := { g | (g 1 0 : ZMod N) = 0 }
  one_mem' := by simp
  mul_mem' {a} {b} ha hb := by
    have h := (Matrix.two_mul_expl a.1 b.1).2.2.1
    simp only [coe_mul, Set.mem_ofPred_eq] at *
    simp [h, ha, hb]
  inv_mem' {a} ha := by
    simpa [SL2_inv_expl a] using ha

@[simp]
/--
theorem `Gamma0_mem` / 定理 `Gamma0_mem`

English:
theorem Gamma0_mem
  given: {N} {A : SL(2, Int)}
  statement: A in Gamma0 N ↔ (A 1 0 : ZMod N) = 0
  proof: Iff.rfl

中文:
定理 Gamma0_mem
  条件: {N} {A : SL(2, 整数)}
  结论: A in Gamma0 N ↔ (A 1 0 : ZMod N) = 0
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Gamma0_mem {N} {A : SL(2, Int)} : A in Gamma0 N ↔ (A 1 0 : ZMod N) = 0 :=
  Iff.rfl

/--
Definition of `Gamma0Map` / `Gamma0Map` 的定义

English:
definition Gamma0Map
  signature: (N : Nat)
  body: g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]

中文:
定义 Gamma0Map
  签名: (N : 自然数)
  定义体: g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]
-/
def Gamma0Map (N : Nat) : Gamma0 N ->* ZMod N where
  toFun g := g.1 1 1
  map_one' := by simp
  map_mul' := by
    rintro ⟨A, hA⟩ ⟨B, _⟩
    simp only [MulMemClass.mk_mul_mk, Fin.isValue, coe_mul, (two_mul_expl A.1 B).2.2.2,
      Int.cast_add, Int.cast_mul, Gamma0_mem.mp hA, zero_mul, zero_add]

/--
Definition of `Gamma1'` / `Gamma1'` 的定义

English:
definition Gamma1'
  signature: (N : Nat)
  body: (Gamma0Map N).ker

@[simp]

中文:
定义 Gamma1'
  签名: (N : 自然数)
  定义体: (Gamma0Map N).ker

@[simp]

Depends on / 依赖: Gamma0Map
-/
def Gamma1' (N : Nat) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker

@[simp]
/--
theorem `Gamma1_mem'` / 定理 `Gamma1_mem'`

English:
theorem Gamma1_mem'
  given: {N} {γ : Gamma0 N}
  statement: γ in Gamma1' N ↔ Gamma0Map N γ = 1
  proof: Iff.rfl

中文:
定理 Gamma1_mem'
  条件: {N} {γ : Gamma0 N}
  结论: γ in Gamma1' N ↔ Gamma0Map N γ = 1
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem Gamma1_mem' {N} {γ : Gamma0 N} : γ in Gamma1' N ↔ Gamma0Map N γ = 1 :=
  Iff.rfl

/--
theorem `Gamma1_to_Gamma0_mem` / 定理 `Gamma1_to_Gamma0_mem`

English:
theorem Gamma1_to_Gamma0_mem
  given: {N} (A : Gamma0 N)
  proof: by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Ma

中文:
定理 Gamma1_to_Gamma0_mem
  条件: {N} (A : Gamma0 N)
  证明: by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Ma

Depends on / 依赖: A.property, Gamma0Map, Gamma0_mem, Gamma0_mem.mp, Gamma1_mem, Int.cast_mul, Int.cast_one, Int.cast_sub, Matrix, Matrix.det_fin_two, MonoidHom, MonoidHom.coe_mk, OneHom, OneHom.coe_mk, and_self_iff, and_true, cast_mul, cast_one, cast_sub, coe_mk
-/
theorem Gamma1_to_Gamma0_mem {N} (A : Gamma0 N) :
    A in Gamma1' N ↔
    ((A.1 0 0 : Int) : ZMod N) = 1 ∧ ((A.1 1 1 : Int) : ZMod N) = 1
      ∧ ((A.1 1 0 : Int) : ZMod N) = 0 := by
  constructor
  · intro ha
    have adet : (A.1.1.det : ZMod N) = 1 := by simp only [A.1.property, Int.cast_one]
    rw [Matrix.det_fin_two] at adet
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul] at *
    simpa only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, Int.cast_sub,
      Int.cast_mul, ha, Gamma0_mem.mp A.property, and_self_iff, and_true, mul_one, mul_zero,
      sub_zero] using adet
  · intro ha
    simp only [Gamma1_mem', Gamma0Map, MonoidHom.coe_mk]
    exact ha.2.1

/--
Definition of `Gamma1` / `Gamma1` 的定义

English:
definition Gamma1
  signature: (N : Nat)
  body: Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]

中文:
定义 Gamma1
  签名: (N : 自然数)
  定义体: Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]

Depends on / 依赖: Gamma0, Gamma1, Subgroup, Subgroup.map, subtype, subtype.comp
-/
def Gamma1 (N : Nat) : Subgroup SL(2, Int) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

@[simp]
/--
theorem `Gamma1_mem` / 定理 `Gamma1_mem`

English:
theorem Gamma1_mem
  given: (N : Nat) (A : SL(2, Int))
  statement: A in Gamma1 N ↔
  proof: by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert! hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A in Gamma

中文:
定理 Gamma1_mem
  条件: (N : 自然数) (A : SL(2, 整数))
  结论: A in Gamma1 N ↔
  证明: by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert! hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A in Gamma

Depends on / 依赖: Gamma0, Gamma0_mem, Gamma1, Gamma1_to_Gamma0_mem, Subgroup, Subgroup.mem_map, Subgroup.mem_top, convert, ha.right.right, mem_map, mem_top, simp_rw, true_and
-/
theorem Gamma1_mem (N : Nat) (A : SL(2, Int)) : A in Gamma1 N ↔
    (A 0 0 : ZMod N) = 1 ∧ (A 1 1 : ZMod N) = 1 ∧ (A 1 0 : ZMod N) = 0 := by
  constructor
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map] at ha
    obtain ⟨⟨x, hx⟩, hxx⟩ := ha
    rw [Gamma1_to_Gamma0_mem] at hx
    simp only [Subgroup.mem_top, true_and] at hxx
    rw [← hxx]
    convert! hx
  · intro ha
    simp_rw [Gamma1, Subgroup.mem_map]
    have hA : A in Gamma0 N := by simp [ha.right.right, Gamma0_mem]
    have HA : (⟨A, hA⟩ : Gamma0 N) in Gamma1' N := by
      simp only [Gamma1_to_Gamma0_mem]
      exact ha
    refine ⟨(⟨(⟨A, hA⟩ : Gamma0 N), HA⟩ : (Gamma1' N : Subgroup (Gamma0 N))), ?_⟩
    simp

/--
theorem `Gamma1_in_Gamma0` / 定理 `Gamma1_in_Gamma0`

English:
theorem Gamma1_in_Gamma0
  given: (N : Nat)
  statement: Gamma1 N <= Gamma0 N
  proof: by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem] at *
  exact HA.2.2

中文:
定理 Gamma1_in_Gamma0
  条件: (N : 自然数)
  结论: Gamma1 N <= Gamma0 N
  证明: by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem] at *
  exact HA.2.2

Depends on / 依赖: Gamma0_mem, Gamma1_mem
-/
theorem Gamma1_in_Gamma0 (N : Nat) : Gamma1 N <= Gamma0 N := by
  intro x HA
  simp only [Gamma0_mem, Gamma1_mem] at *
  exact HA.2.2

section CongruenceSubgroups

/--
Definition of `IsCongruenceSubgroup` / `IsCongruenceSubgroup` 的定义

English:
definition IsCongruenceSubgroup
  signature: (Γ : Subgroup SL(2, Int))
  body: exists N != 0, Gamma N <= Γ

中文:
定义 IsCongruenceSubgroup
  签名: (Γ : Subgroup SL(2, 整数))
  定义体: exists N != 0, Gamma N <= Γ
-/
def IsCongruenceSubgroup (Γ : Subgroup SL(2, Int)) : Prop :=
  exists N != 0, Gamma N <= Γ

/--
theorem `isCongruenceSubgroup_trans` / 定理 `isCongruenceSubgroup_trans`

English:
theorem isCongruenceSubgroup_trans
  statement: (H K : Subgroup SL(2, Int)) (h : H <= K)
  proof: by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, hN.1, hN.2.trans h⟩

中文:
定理 isCongruenceSubgroup_trans
  结论: (H K : Subgroup SL(2, 整数)) (h : H <= K)
  证明: by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, hN.1, hN.2.trans h⟩
-/
theorem isCongruenceSubgroup_trans (H K : Subgroup SL(2, Int)) (h : H <= K)
    (h2 : IsCongruenceSubgroup H) : IsCongruenceSubgroup K := by
  obtain ⟨N, hN⟩ := h2
  exact ⟨N, hN.1, hN.2.trans h⟩

/--
theorem `Gamma_is_cong_sub` / 定理 `Gamma_is_cong_sub`

English:
theorem Gamma_is_cong_sub
  given: (N : Nat) [NeZero N]
  statement: IsCongruenceSubgroup (Gamma N)
  proof: ⟨N, NeZero.ne _, le_rfl⟩

中文:
定理 Gamma_is_cong_sub
  条件: (N : 自然数) [NeZero N]
  结论: IsCongruenceSubgroup (Gamma N)
  证明: ⟨N, NeZero.ne _, le_rfl⟩

Depends on / 依赖: NeZero, NeZero.ne, le_rfl
-/
theorem Gamma_is_cong_sub (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma N) :=
  ⟨N, NeZero.ne _, le_rfl⟩

/--
theorem `Gamma1_is_congruence` / 定理 `Gamma1_is_congruence`

English:
theorem Gamma1_is_congruence
  given: (N : Nat) [NeZero N]
  statement: IsCongruenceSubgroup (Gamma1 N)
  proof: by
  refine ⟨N, NeZero.ne _, fun A hA => ?_⟩
  simp_all [Gamma1_mem, Gamma_mem]

中文:
定理 Gamma1_is_congruence
  条件: (N : 自然数) [NeZero N]
  结论: IsCongruenceSubgroup (Gamma1 N)
  证明: by
  refine ⟨N, NeZero.ne _, fun A hA => ?_⟩
  simp_all [Gamma1_mem, Gamma_mem]

Depends on / 依赖: Gamma1_mem, Gamma_mem, NeZero, NeZero.ne
-/
theorem Gamma1_is_congruence (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma1 N) := by
  refine ⟨N, NeZero.ne _, fun A hA => ?_⟩
  simp_all [Gamma1_mem, Gamma_mem]

/--
theorem `Gamma0_is_congruence` / 定理 `Gamma0_is_congruence`

English:
theorem Gamma0_is_congruence
  given: (N : Nat) [NeZero N]
  statement: IsCongruenceSubgroup (Gamma0 N)
  proof: isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

中文:
定理 Gamma0_is_congruence
  条件: (N : 自然数) [NeZero N]
  结论: IsCongruenceSubgroup (Gamma0 N)
  证明: isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

Depends on / 依赖: Gamma1_in_Gamma0, Gamma1_is_congruence, isCongruenceSubgroup_trans
-/
theorem Gamma0_is_congruence (N : Nat) [NeZero N] : IsCongruenceSubgroup (Gamma0 N) :=
  isCongruenceSubgroup_trans _ _ (Gamma1_in_Gamma0 N) (Gamma1_is_congruence N)

/--
lemma `IsCongruenceSubgroup.finiteIndex` / 引理 `IsCongruenceSubgroup.finiteIndex`

English:
lemma IsCongruenceSubgroup.finiteIndex
  statement: {Γ : Subgroup SL(2, Int)}
  proof: by
  obtain ⟨N, hN⟩ := h
  have : NeZero N := ⟨hN.1⟩
  exact Subgroup.finiteIndex_of_le hN.2

中文:
引理 IsCongruenceSubgroup.finiteIndex
  结论: {Γ : Subgroup SL(2, 整数)}
  证明: by
  obtain ⟨N, hN⟩ := h
  have : NeZero N := ⟨hN.1⟩
  exact Subgroup.finiteIndex_of_le hN.2

Depends on / 依赖: NeZero, Subgroup, Subgroup.finiteIndex_of_le, finiteIndex_of_le
-/
lemma IsCongruenceSubgroup.finiteIndex {Γ : Subgroup SL(2, Int)}
    (h : IsCongruenceSubgroup Γ) : Γ.FiniteIndex := by
  obtain ⟨N, hN⟩ := h
  have : NeZero N := ⟨hN.1⟩
  exact Subgroup.finiteIndex_of_le hN.2

/--
Instance `instFiniteIndexGamma0` / 实例 `instFiniteIndexGamma0`

English:
instance instFiniteIndexGamma0
  signature: [NeZero N]
  body: (Gamma0_is_congruence N).finiteIndex

中文:
实例 instFiniteIndexGamma0
  签名: [NeZero N]
  定义体: (Gamma0_is_congruence N).finiteIndex

Depends on / 依赖: Gamma0_is_congruence, finiteIndex
-/
instance instFiniteIndexGamma0 [NeZero N] : (Gamma0 N).FiniteIndex :=
  (Gamma0_is_congruence N).finiteIndex

/--
Instance `instFiniteIndexGamma1` / 实例 `instFiniteIndexGamma1`

English:
instance instFiniteIndexGamma1
  signature: [NeZero N]
  body: (Gamma1_is_congruence N).finiteIndex

中文:
实例 instFiniteIndexGamma1
  签名: [NeZero N]
  定义体: (Gamma1_is_congruence N).finiteIndex

Depends on / 依赖: Gamma1_is_congruence, finiteIndex
-/
instance instFiniteIndexGamma1 [NeZero N] : (Gamma1 N).FiniteIndex :=
  (Gamma1_is_congruence N).finiteIndex

end CongruenceSubgroups

section Conjugation

open scoped Pointwise
open ConjAct

/--
Definition of `conjGL` / `conjGL` 的定义

English:
definition conjGL
  signature: (Γ : Subgroup SL(2, Int)) (g : GL (Fin 2) Real)
  body: ((toConjAct g⁻¹) • (Γ.map <| mapGL Real)).comap (mapGL Real)

中文:
定义 conjGL
  签名: (Γ : Subgroup SL(2, 整数)) (g : GL (Fin 2) 实数)
  定义体: ((toConjAct g⁻¹) • (Γ.map <| mapGL Real)).comap (mapGL Real)

Depends on / 依赖: toConjAct
-/
def conjGL (Γ : Subgroup SL(2, Int)) (g : GL (Fin 2) Real) : Subgroup SL(2, Int) :=
  ((toConjAct g⁻¹) • (Γ.map <| mapGL Real)).comap (mapGL Real)

/--
lemma `mem_conjGL` / 引理 `mem_conjGL`

English:
lemma mem_conjGL
  given: {Γ : Subgroup SL(2, Int)} {g : GL (Fin 2) Real} {x : SL(2, Int)}
  proof: by
  simp [conjGL, mapGL, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

@[simp]

中文:
引理 mem_conjGL
  条件: {Γ : Subgroup SL(2, 整数)} {g : GL (Fin 2) 实数} {x : SL(2, 整数)}
  证明: by
  simp [conjGL, mapGL, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

@[simp]
-/
@[simp] lemma mem_conjGL {Γ : Subgroup SL(2, Int)} {g : GL (Fin 2) Real} {x : SL(2, Int)} :
    x in conjGL Γ g ↔ exists y in Γ, y = g * x * g⁻¹ := by
  simp [conjGL, mapGL, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

@[simp]
/--
lemma `conjGL_coe` / 引理 `conjGL_coe`

English:
lemma conjGL_coe
  given: (Γ : Subgroup SL(2, Int)) (g : SL(2, Int))
  proof: by
  ext x
  simp_rw [mem_conjGL, ← map_inv, ← map_mul, toGL_injective.eq_iff, map_intCast_injective.eq_iff,
    exists_eq_right, toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

中文:
引理 conjGL_coe
  条件: (Γ : Subgroup SL(2, 整数)) (g : SL(2, 整数))
  证明: by
  ext x
  simp_rw [mem_conjGL, ← map_inv, ← map_mul, toGL_injective.eq_iff, map_intCast_injective.eq_iff,
    exists_eq_right, toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

Depends on / 依赖: Subgroup, Subgroup.mem_inv_pointwise_smul_iff, eq_iff, exists_eq_right, map_intCast_injective, map_intCast_injective.eq_iff, map_inv, map_mul, mem_conjGL, mem_inv_pointwise_smul_iff, simp_rw, toConjAct_inv, toConjAct_smul, toGL_injective, toGL_injective.eq_iff
-/
lemma conjGL_coe (Γ : Subgroup SL(2, Int)) (g : SL(2, Int)) :
    conjGL Γ g = (toConjAct g⁻¹) • Γ := by
  ext x
  simp_rw [mem_conjGL, ← map_inv, ← map_mul, toGL_injective.eq_iff, map_intCast_injective.eq_iff,
    exists_eq_right, toConjAct_inv, Subgroup.mem_inv_pointwise_smul_iff, toConjAct_smul]

/--
theorem `Gamma_cong_eq_self` / 定理 `Gamma_cong_eq_self`

English:
theorem Gamma_cong_eq_self
  given: (N : Nat) (g : ConjAct SL(2, Int))
  statement: g • Gamma N = Gamma N
  proof: by
  apply Subgroup.Normal.conjAct (Gamma_normal N)

中文:
定理 Gamma_cong_eq_self
  条件: (N : 自然数) (g : ConjAct SL(2, 整数))
  结论: g • Gamma N = Gamma N
  证明: by
  apply Subgroup.Normal.conjAct (Gamma_normal N)

Depends on / 依赖: Gamma_normal, Normal, Subgroup, Subgroup.Normal.conjAct, conjAct
-/
theorem Gamma_cong_eq_self (N : Nat) (g : ConjAct SL(2, Int)) : g • Gamma N = Gamma N := by
  apply Subgroup.Normal.conjAct (Gamma_normal N)

/--
theorem `conj_cong_is_cong` / 定理 `conj_cong_is_cong`

English:
theorem conj_cong_is_cong
  statement: (g : ConjAct SL(2, Int)) (Γ : Subgroup SL(2, Int))
  proof: by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g]; rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

中文:
定理 conj_cong_is_cong
  结论: (g : ConjAct SL(2, 整数)) (Γ : Subgroup SL(2, 整数))
  证明: by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g]; rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

Depends on / 依赖: Gamma_cong_eq_self, Subgroup, Subgroup.pointwise_smul_le_pointwise_smul_iff, pointwise_smul_le_pointwise_smul_iff
-/
theorem conj_cong_is_cong (g : ConjAct SL(2, Int)) (Γ : Subgroup SL(2, Int))
    (h : IsCongruenceSubgroup Γ) : IsCongruenceSubgroup (g • Γ) := by
  obtain ⟨N, HN⟩ := h
  refine ⟨N, ?_⟩
  rw [← Gamma_cong_eq_self N g]; rw [Subgroup.pointwise_smul_le_pointwise_smul_iff]
  exact HN

set_option backward.isDefEq.respectTransparency false in
/--
theorem `exists_Gamma_le_conj` / 定理 `exists_Gamma_le_conj`

English:
theorem exists_Gamma_le_conj
  given: (g : GL (Fin 2) Rat) (M : Nat) [NeZero M]
  proof: by
  -- Give names to the numerators and denominators of `g` and `g⁻¹`
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  -- we take

中文:
定理 exists_Gamma_le_conj
  条件: (g : GL (Fin 2) Rat) (M : 自然数) [NeZero M]
  证明: by
  -- Give names to the numerators and denominators of `g` and `g⁻¹`
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  -- we take
-/
theorem exists_Gamma_le_conj (g : GL (Fin 2) Rat) (M : Nat) [NeZero M] :
    exists N != 0, forall x in Gamma N, g * (mapGL Rat x) * g⁻¹ in (Gamma M).map (mapGL Rat) := by
  -- Give names to the numerators and denominators of `g` and `g⁻¹`
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  -- we take `N = a₁ * a₂`
  refine ⟨a₁ * a₂ * M, mul_ne_zero (mul_ne_zero A₁.den_ne_zero A₂.den_ne_zero) (NeZero.ne _),
    fun ⟨y, hy⟩ hy' => ?_⟩
  -- Show that `y` is of the form `1 + (a₁ * a₂) • k` for some integer matrix `k`.
  obtain ⟨k, hk⟩ : exists k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : Int -> ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem']; rw [Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j => (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp)]; rw [← sub_eq_zero]; rw [← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  -- use this `k` to cook up a new integer matrix, which we will show comes from `SL(2, ℤ)`
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : Int -> Rat) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul Rat (_ * M)]; rw [← mul_smul]; rw [← mul_smul]; rw [mul_comm a₁ a₂]; rw [Nat.cast_mul]; rw [Nat.cast_mul]; rw [mul_assoc _ _ (M : Rat)]; rw [mul_comm _ (M : Rat)]; rw [inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero)]; rw [mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero)]; rw [Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, by simpa only [Subtype.ext_iff, Subgroup.coe_mul, Units.ext_iff,
    Units.val_mul] using! hz_coe⟩
  rw [SetLike.mem_coe]; rw [CongruenceSubgroup.Gamma_mem']; rw [Subtype.ext_iff]
  ext i j
  simp_rw [map_apply_coe, z, map_add, map_one, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.add_apply, map_apply, coe_one, add_eq_left, Matrix.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self M, zero_mul]

/--
theorem `exists_Gamma_le_conj'` / 定理 `exists_Gamma_le_conj'`

English:
theorem exists_Gamma_le_conj'
  given: (g : GL (Fin 2) Rat) (M : Nat) [NeZero M]
  proof: by
  obtain ⟨N, hN, h⟩ := exists_Gamma_le_conj g M
  refine ⟨N, hN, fun y hy => ?_⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    eq_inv_smul_iff] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨z, hz, hz'⟩ := h x hx
  use z, hz
  simpa only [Subtype.ext_iff, Units.ext_i

中文:
定理 exists_Gamma_le_conj'
  条件: (g : GL (Fin 2) Rat) (M : 自然数) [NeZero M]
  证明: by
  obtain ⟨N, hN, h⟩ := exists_Gamma_le_conj g M
  refine ⟨N, hN, fun y hy => ?_⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    eq_inv_smul_iff] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨z, hz, hz'⟩ := h x hx
  use z, hz
  simpa only [Subtype.ext_iff, Units.ext_i

Depends on / 依赖: GeneralLinearGroup, GeneralLinearGroup.map, Rat.castHom, Subgroup, Subgroup.mem_map, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subtype, Subtype.ext_iff, Units.ext_iff, castHom, congr_arg, eq_inv_smul_iff, exists_Gamma_le_conj, ext_iff, map_mul, mem_map, mem_pointwise_smul_iff_inv_smul_mem, simp_rw
-/
theorem exists_Gamma_le_conj' (g : GL (Fin 2) Rat) (M : Nat) [NeZero M] :
    exists N != 0, (toConjAct <| g.map (Rat.castHom Real)) • (Gamma N).map (mapGL Real)
      <= (Gamma M).map (mapGL Real) := by
  obtain ⟨N, hN, h⟩ := exists_Gamma_le_conj g M
  refine ⟨N, hN, fun y hy => ?_⟩
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_map,
    eq_inv_smul_iff] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨z, hz, hz'⟩ := h x hx
  use z, hz
  simpa only [Subtype.ext_iff, Units.ext_iff, map_mul] using!
    congr_arg (GeneralLinearGroup.map (Rat.castHom Real)) hz'

open Subgroup in
/--
lemma `finiteIndex_conjGL` / 引理 `finiteIndex_conjGL`

English:
lemma finiteIndex_conjGL
  given: (g : GL (Fin 2) Rat)
  statement: (conjGL ⊤ (g.map <| Rat.castHom Real)).FiniteIndex
  proof: by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom Real)⁻¹
  suffices (t • 𝒮ℒ ⊓ 𝒮ℒ).relIndex 𝒮ℒ != 0 by
    rwa [conjGL, index_comap, ← inf_relIndex_right, ← MonoidHom.range_eq_map]
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
  rw [Gamma_one_top]; rw [← MonoidHom.range_eq_map] at 

中文:
引理 finiteIndex_conjGL
  条件: (g : GL (Fin 2) Rat)
  结论: (conjGL ⊤ (g.map <| Rat.castHom 实数)).FiniteIndex
  证明: by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom Real)⁻¹
  suffices (t • 𝒮ℒ ⊓ 𝒮ℒ).relIndex 𝒮ℒ != 0 by
    rwa [conjGL, index_comap, ← inf_relIndex_right, ← MonoidHom.range_eq_map]
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
  rw [Gamma_one_top]; rw [← MonoidHom.range_eq_map] at 

Depends on / 依赖: Gamma_one_top, MonoidHom, MonoidHom.range_eq_map, NeZero, Rat.castHom, castHom, conjGL, exists_Gamma_le_conj, finiteIndex_of_le, g.map, index_comap, index_ne_zero, inf_relIndex_right, mem_pointwise_smul_iff_inv_smul_mem, range_eq_map, relIndex, toConjAct
-/
lemma finiteIndex_conjGL (g : GL (Fin 2) Rat) : (conjGL ⊤ (g.map <| Rat.castHom Real)).FiniteIndex := by
  constructor
  let t := (toConjAct <| g.map <| Rat.castHom Real)⁻¹
  suffices (t • 𝒮ℒ ⊓ 𝒮ℒ).relIndex 𝒮ℒ != 0 by
    rwa [conjGL, index_comap, ← inf_relIndex_right, ← MonoidHom.range_eq_map]
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g 1
  rw [Gamma_one_top]; rw [← MonoidHom.range_eq_map] at hN'
  suffices Γ(N) <= (t • 𝒮ℒ ⊓ 𝒮ℒ).comap (mapGL Real) by
    have _ : NeZero N := ⟨hN⟩
    simpa only [index_comap] using! (finiteIndex_of_le this).index_ne_zero
  intro k hk
  simpa [mem_pointwise_smul_iff_inv_smul_mem] using!
hN' smul_mem_pointwise_smul _ _ _ ⟨k, hk, rfl⟩

/--
lemma `isArithmetic_conj_SL2Z` / 引理 `isArithmetic_conj_SL2Z`

English:
lemma isArithmetic_conj_SL2Z
  given: (g : GL (Fin 2) Rat)
  proof: by
  constructor
  rw [MonoidHom.range_eq_map]
  constructor
  · rw [← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g⁻¹).index_ne_zero
  · rw [← Subgroup.relIndex_pointwise_smul (toConjAct (g.map (Rat.castHom Real)))⁻¹,
      inv_smul_smul, ← Subgroup.relIndex_

中文:
引理 isArithmetic_conj_SL2Z
  条件: (g : GL (Fin 2) Rat)
  证明: by
  constructor
  rw [MonoidHom.range_eq_map]
  constructor
  · rw [← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g⁻¹).index_ne_zero
  · rw [← Subgroup.relIndex_pointwise_smul (toConjAct (g.map (Rat.castHom Real)))⁻¹,
      inv_smul_smul, ← Subgroup.relIndex_

Depends on / 依赖: MonoidHom, MonoidHom.range_eq_map, Rat.castHom, Subgroup, Subgroup.relIndex_comap, Subgroup.relIndex_pointwise_smul, Subgroup.relIndex_top_right, castHom, finiteIndex_conjGL, g.map, index_ne_zero, inv_smul_smul, range_eq_map, relIndex_comap, relIndex_pointwise_smul, relIndex_top_right, toConjAct
-/
lemma isArithmetic_conj_SL2Z (g : GL (Fin 2) Rat) :
    (toConjAct (g.map (Rat.castHom Real)) • 𝒮ℒ).IsArithmetic := by
  constructor
  rw [MonoidHom.range_eq_map]
  constructor
  · rw [← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g⁻¹).index_ne_zero
  · rw [← Subgroup.relIndex_pointwise_smul (toConjAct (g.map (Rat.castHom Real)))⁻¹,
      inv_smul_smul, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    exact (finiteIndex_conjGL g).index_ne_zero

/--
lemma `_root_.Subgroup.IsArithmetic.conj` / 引理 `_root_.Subgroup.IsArithmetic.conj`

English:
lemma _root_.Subgroup.IsArithmetic.conj
  statement: (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
  proof: ⟨(Subgroup.IsArithmetic.is_commensurable.conj _).trans
    (isArithmetic_conj_SL2Z g).is_commensurable⟩

中文:
引理 _root_.Subgroup.IsArithmetic.conj
  结论: (𝒢 : Subgroup (GL (Fin 2) 实数)) [𝒢.IsArithmetic]
  证明: ⟨(Subgroup.IsArithmetic.is_commensurable.conj _).trans
    (isArithmetic_conj_SL2Z g).is_commensurable⟩

Depends on / 依赖: IsArithmetic, Subgroup, Subgroup.IsArithmetic.is_commensurable.conj, isArithmetic_conj_SL2Z, is_commensurable
-/
lemma _root_.Subgroup.IsArithmetic.conj (𝒢 : Subgroup (GL (Fin 2) Real)) [𝒢.IsArithmetic]
    (g : GL (Fin 2) Rat) :
    (toConjAct (g.map (Rat.castHom Real)) • 𝒢).IsArithmetic :=
  ⟨(Subgroup.IsArithmetic.is_commensurable.conj _).trans
    (isArithmetic_conj_SL2Z g).is_commensurable⟩

/--
lemma `IsCongruenceSubgroup.conjGL` / 引理 `IsCongruenceSubgroup.conjGL`

English:
lemma IsCongruenceSubgroup.conjGL
  statement: {Γ : Subgroup SL(2, Int)} (hΓ : IsCongruenceSubgroup Γ)
  proof: by
  obtain ⟨M, hN, hΓM⟩ := hΓ
  have _ : NeZero M := ⟨hN⟩
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g M
  rw [Subgroup.pointwise_smul_subset_iff] at hN'
  refine ⟨N, ‹_›, fun x hx => ?_⟩
obtain ⟨y, hy, hy'⟩ := Subgroup.mem_inv_pointwise_smul_iff.mp hN' ⟨x, hx, rfl⟩
  exact mem_conjGL.mpr ⟨y, h

中文:
引理 IsCongruenceSubgroup.conjGL
  结论: {Γ : Subgroup SL(2, 整数)} (hΓ : IsCongruenceSubgroup Γ)
  证明: by
  obtain ⟨M, hN, hΓM⟩ := hΓ
  have _ : NeZero M := ⟨hN⟩
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g M
  rw [Subgroup.pointwise_smul_subset_iff] at hN'
  refine ⟨N, ‹_›, fun x hx => ?_⟩
obtain ⟨y, hy, hy'⟩ := Subgroup.mem_inv_pointwise_smul_iff.mp hN' ⟨x, hx, rfl⟩
  exact mem_conjGL.mpr ⟨y, h

Depends on / 依赖: NeZero, Subgroup, Subgroup.mem_inv_pointwise_smul_iff.mp, Subgroup.pointwise_smul_subset_iff, exists_Gamma_le_conj, mem_conjGL, mem_conjGL.mpr, mem_inv_pointwise_smul_iff, pointwise_smul_subset_iff
-/
lemma IsCongruenceSubgroup.conjGL {Γ : Subgroup SL(2, Int)} (hΓ : IsCongruenceSubgroup Γ)
    (g : GL (Fin 2) Rat) :
    IsCongruenceSubgroup (conjGL Γ (g.map <| Rat.castHom Real)) := by
  obtain ⟨M, hN, hΓM⟩ := hΓ
  have _ : NeZero M := ⟨hN⟩
  obtain ⟨N, hN, hN'⟩ := exists_Gamma_le_conj' g M
  rw [Subgroup.pointwise_smul_subset_iff] at hN'
  refine ⟨N, ‹_›, fun x hx => ?_⟩
obtain ⟨y, hy, hy'⟩ := Subgroup.mem_inv_pointwise_smul_iff.mp hN' ⟨x, hx, rfl⟩
  exact mem_conjGL.mpr ⟨y, hΓM hy, hy'⟩

end Conjugation

end CongruenceSubgroup
