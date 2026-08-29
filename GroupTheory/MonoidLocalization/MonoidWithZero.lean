/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Maps
public import Mathlib.RingTheory.OreLocalization.Basic

/-!
# Localizations of commutative monoids with zeroes

-/

@[expose] public section

open Function

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

variable {S N}

/--
theorem `LocalizationMap.subsingleton` / 定理 `LocalizationMap.subsingleton`

English:
theorem LocalizationMap.subsingleton
  given: (f : LocalizationMap S N) (h : 0 in S)
  statement: Subsingleton N where
  proof: by
    rw [← f.mk'_sec a]; rw [← f.mk'_sec b]; rw [f.eq]
    exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

中文:
定理 Localization映射.subsingleton
  条件: (f : Localization映射 S N) (h : 0 in S)
  结论: 子单例 N where
  证明: by
    rw [← f.mk'_sec a]; rw [← f.mk'_sec b]; rw [f.eq]
    exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

Depends on / 依赖: _sec, f.eq, f.mk, zero_mul
-/
theorem LocalizationMap.subsingleton (f : LocalizationMap S N) (h : 0 in S) : Subsingleton N where
  allEq a b := by
    rw [← f.mk'_sec a]; rw [← f.mk'_sec b]; rw [f.eq]
    exact ⟨⟨0, h⟩, by simp only [zero_mul]⟩

/--
theorem `LocalizationMap.subsingleton_iff` / 定理 `LocalizationMap.subsingleton_iff`

English:
theorem LocalizationMap.subsingleton_iff
  given: (f : LocalizationMap S N)
  statement: Subsingleton N ↔ 0 in S
  proof: ⟨fun _ => have ⟨c, eq⟩ := f.exists_of_eq (Subsingleton.elim (f 0) (f 1))
    by rw [mul_zero, mul_one] at eq; exact eq ▸ c.2, f.subsingleton⟩

中文:
定理 Localization映射.subsingleton_iff
  条件: (f : Localization映射 S N)
  结论: 子单例 N ↔ 0 in S
  证明: ⟨fun _ => have ⟨c, eq⟩ := f.exists_of_eq (Subsingleton.elim (f 0) (f 1))
    by rw [mul_zero, mul_one] at eq; exact eq ▸ c.2, f.subsingleton⟩

Depends on / 依赖: Subsingleton, Subsingleton.elim, exists_of_eq, f.exists_of_eq, f.subsingleton, mul_one, mul_zero, subsingleton
-/
theorem LocalizationMap.subsingleton_iff (f : LocalizationMap S N) : Subsingleton N ↔ 0 in S :=
  ⟨fun _ => have ⟨c, eq⟩ := f.exists_of_eq (Subsingleton.elim (f 0) (f 1))
    by rw [mul_zero, mul_one] at eq; exact eq ▸ c.2, f.subsingleton⟩

/--
theorem `LocalizationMap.nontrivial` / 定理 `LocalizationMap.nontrivial`

English:
theorem LocalizationMap.nontrivial
  given: (f : LocalizationMap S N) (h : 0 ∉ S)
  statement: Nontrivial N
  proof: by
  rwa [← not_subsingleton_iff_nontrivial, f.subsingleton_iff]

中文:
定理 Localization映射.nontrivial
  条件: (f : Localization映射 S N) (h : 0 ∉ S)
  结论: 非平凡 N
  证明: by
  rwa [← not_subsingleton_iff_nontrivial, f.subsingleton_iff]

Depends on / 依赖: f.subsingleton_iff, not_subsingleton_iff_nontrivial, subsingleton_iff
-/
theorem LocalizationMap.nontrivial (f : LocalizationMap S N) (h : 0 ∉ S) : Nontrivial N := by
  rwa [← not_subsingleton_iff_nontrivial, f.subsingleton_iff]

/--
theorem `LocalizationMap.map_zero` / 定理 `LocalizationMap.map_zero`

English:
theorem LocalizationMap.map_zero
  given: (f : LocalizationMap S N)
  statement: f 0 = 0
  proof: by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]

中文:
定理 Localization映射.map_zero
  条件: (f : Localization映射 S N)
  结论: f 0 = 0
  证明: by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]
-/
protected theorem LocalizationMap.map_zero (f : LocalizationMap S N) : f 0 = 0 := by
  have ⟨ms, eq⟩ := f.surj 0
  rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]

/--
theorem `IsLocalizationMap.map_zero` / 定理 `IsLocalizationMap.map_zero`

English:
theorem IsLocalizationMap.map_zero
  statement: {F} [FunLike F M N] [MulHomClass F M N] {f : F}
  proof: LocalizationMap.map_zero ⟨MulHomClass.toMulHom f, hf⟩

中文:
定理 是Localization映射.map_zero
  结论: {F} [函数状 F M N] [乘法态射类 F M N] {f : F}
  证明: LocalizationMap.map_zero ⟨MulHomClass.toMulHom f, hf⟩
-/
protected theorem IsLocalizationMap.map_zero {F} [FunLike F M N] [MulHomClass F M N] {f : F}
    (hf : IsLocalizationMap S f) : f 0 = 0 :=
  LocalizationMap.map_zero ⟨MulHomClass.toMulHom f, hf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidWithZeroHomClass (LocalizationMap S N) M N
  body: by
    have ⟨ms, eq⟩ := f.surj 0
    rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]

中文:
实例 :
  签名: 带零幺半群态射类 (Localization映射 S N) M N
  定义体: by
    have ⟨ms, eq⟩ := f.surj 0
    rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]

Depends on / 依赖: f.surj, map_mul, mul_zero, zero_mul
-/
instance : MonoidWithZeroHomClass (LocalizationMap S N) M N where
  map_zero f := by
    have ⟨ms, eq⟩ := f.surj 0
    rw [← zero_mul]; rw [map_mul]; rw [← eq]; rw [zero_mul]; rw [mul_zero]

end Submonoid

namespace Localization

variable {S}

/--
theorem `mk_zero` / 定理 `mk_zero`

English:
theorem mk_zero
  given: (x : S)
  statement: mk 0 (x : S) = 0
  proof: OreLocalization.zero_oreDiv' _

中文:
定理 mk_zero
  条件: (x : S)
  结论: mk 0 (x : S) = 0
  证明: OreLocalization.zero_oreDiv' _

Depends on / 依赖: OreLocalization, OreLocalization.zero_oreDiv, zero_oreDiv
-/
theorem mk_zero (x : S) : mk 0 (x : S) = 0 := OreLocalization.zero_oreDiv' _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommMonoidWithZero (Localization S)
  body: fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, r_of_eq]

中文:
实例 :
  签名: 带零交换幺半群 (Localization S)
  定义体: fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, r_of_eq]

Depends on / 依赖: Localization, Localization.induction_on, Localization.mk_zero, induction_on, mk_eq_mk_iff, mk_mul, mk_zero, mul_zero, r_of_eq, zero_mul
-/
instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
  mul_zero := fun x => Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, r_of_eq]

/--
theorem `liftOn_zero` / 定理 `liftOn_zero`

English:
theorem liftOn_zero
  given: {p : Type*} (f : M -> S -> p) (H)
  statement: liftOn 0 f H = f 0 1
  proof: by
  rw [← mk_zero 1]; rw [liftOn_mk]

中文:
定理 liftOn_zero
  条件: {p : 类型} (f : M -> S -> p) (H)
  结论: liftOn 0 f H = f 0 1
  证明: by
  rw [← mk_zero 1]; rw [liftOn_mk]

Depends on / 依赖: liftOn_mk, mk_zero
-/
theorem liftOn_zero {p : Type*} (f : M -> S -> p) (H) : liftOn 0 f H = f 0 1 := by
  rw [← mk_zero 1]; rw [liftOn_mk]

end Localization

variable {S N}

namespace Submonoid

@[simp]
/--
theorem `LocalizationMap.sec_zero_fst` / 定理 `LocalizationMap.sec_zero_fst`

English:
theorem LocalizationMap.sec_zero_fst
  given: {f : LocalizationMap S N}
  statement: f (f.sec 0).fst = 0
  proof: by
  rw [LocalizationMap.sec_spec']; rw [mul_zero]

中文:
定理 Localization映射.sec_zero_fst
  条件: {f : Localization映射 S N}
  结论: f (f.sec 0).fst = 0
  证明: by
  rw [LocalizationMap.sec_spec']; rw [mul_zero]

Depends on / 依赖: LocalizationMap, LocalizationMap.sec_spec, mul_zero, sec_spec
-/
theorem LocalizationMap.sec_zero_fst {f : LocalizationMap S N} : f (f.sec 0).fst = 0 := by
  rw [LocalizationMap.sec_spec']; rw [mul_zero]

namespace LocalizationMap

/--
Definition of `lift₀` / `lift₀` 的定义

English:
definition lift₀
  signature: (f : LocalizationMap S N) (g : M ->*₀ P)
  body: { @LocalizationMap.lift _ _ _ _ _ _ _ f g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f hg 0 0]; rw [mul_zero]; rw [← map_zero g]; rw [← g.toMonoidHom_coe]
      refine f.eq_of_eq hg ?_
      rw [Localizat

中文:
定义 lift₀
  签名: (f : Localization映射 S N) (g : M ->*₀ P)
  定义体: { @LocalizationMap.lift _ _ _ _ _ _ _ f g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f hg 0 0]; rw [mul_zero]; rw [← map_zero g]; rw [← g.toMonoidHom_coe]
      refine f.eq_of_eq hg ?_
      rw [Localizat

Depends on / 依赖: LocalizationMap, LocalizationMap.lift, LocalizationMap.lift_spec, LocalizationMap.sec_zero_fst, MonoidHom, MonoidHom.toOneHom_coe, OneHom, OneHom.toFun_eq_coe, eq_of_eq, f.eq_of_eq, g.toMonoidHom, g.toMonoidHom_coe, lift_spec, map_zero, mul_zero, sec_zero_fst, toFun_eq_coe, toMonoidHom, toMonoidHom_coe, toOneHom_coe
-/
noncomputable def lift₀ (f : LocalizationMap S N) (g : M ->*₀ P)
    (hg : forall y : S, IsUnit (g y)) : N ->*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f g.toMonoidHom hg with
    map_zero' := by
      dsimp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      rw [LocalizationMap.lift_spec f hg 0 0]; rw [mul_zero]; rw [← map_zero g]; rw [← g.toMonoidHom_coe]
      refine f.eq_of_eq hg ?_
      rw [LocalizationMap.sec_zero_fst]
      exact (map_zero f).symm }

/--
lemma `lift₀_def` / 引理 `lift₀_def`

English:
lemma lift₀_def
  given: (f : LocalizationMap S N) (g : M ->*₀ P) (hg : forall y : S, IsUnit (g y))
  proof: rfl

中文:
引理 lift₀_def
  条件: (f : Localization映射 S N) (g : M ->*₀ P) (hg : 对任意 y : S, 是单位 (g y))
  证明: rfl
-/
lemma lift₀_def (f : LocalizationMap S N) (g : M ->*₀ P) (hg : forall y : S, IsUnit (g y)) :
    ⇑(f.lift₀ g hg) = f.lift (g := g) hg := rfl

/--
lemma `lift₀_apply` / 引理 `lift₀_apply`

English:
lemma lift₀_apply
  given: (f : LocalizationMap S N) (g : M ->*₀ P) (hg : forall y : S, IsUnit (g y)) (x)
  proof: rfl

中文:
引理 lift₀_apply
  条件: (f : Localization映射 S N) (g : M ->*₀ P) (hg : 对任意 y : S, 是单位 (g y)) (x)
  证明: rfl
-/
lemma lift₀_apply (f : LocalizationMap S N) (g : M ->*₀ P) (hg : forall y : S, IsUnit (g y)) (x) :
    f.lift₀ g hg x = g (f.sec x).1 * (IsUnit.liftRight (g.domRestrict S) hg (f.sec x).2)⁻¹ := rfl

/--
theorem `isCancelMulZero` / 定理 `isCancelMulZero`

English:
theorem isCancelMulZero
  given: (f : LocalizationMap S N) [IsCancelMulZero M]
  statement: IsCancelMulZero N
  proof: by
  simp_rw [isCancelMulZero_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n hn
  have ⟨ms, eq⟩ := f.surj n
  refine (eq ▸ f.map_isRegular (isCancelMulZero_iff_forall_isRegular.mp ‹_› ?_)).2.of_mul
  refine fun h => hn ?_
  rw

中文:
定理 isCancelMulZero
  条件: (f : Localization映射 S N) [是乘零消去 M]
  结论: 是乘零消去 N
  证明: by
  simp_rw [isCancelMulZero_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n hn
  have ⟨ms, eq⟩ := f.surj n
  refine (eq ▸ f.map_isRegular (isCancelMulZero_iff_forall_isRegular.mp ‹_› ?_)).2.of_mul
  refine fun h => hn ?_
  rw

Depends on / 依赖: Commute, Commute.all, Commute.isRegular_iff, Commute.isRightRegular_iff, f.map_isRegular, f.map_units, f.surj, isCancelMulZero_iff_forall_isRegular, isCancelMulZero_iff_forall_isRegular.mp, isRegular_iff, isRightRegular_iff, map_isRegular, map_units, map_zero, mul_left_eq_zero, of_mul, simp_rw
-/
theorem isCancelMulZero (f : LocalizationMap S N) [IsCancelMulZero M] : IsCancelMulZero N := by
  simp_rw [isCancelMulZero_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n hn
  have ⟨ms, eq⟩ := f.surj n
  refine (eq ▸ f.map_isRegular (isCancelMulZero_iff_forall_isRegular.mp ‹_› ?_)).2.of_mul
  refine fun h => hn ?_
  rwa [h, map_zero, (f.map_units _).mul_left_eq_zero] at eq

/--
theorem `map_eq_zero_iff` / 定理 `map_eq_zero_iff`

English:
theorem map_eq_zero_iff
  given: (f : LocalizationMap S N) {m : M}
  statement: f m = 0 ↔ exists s : S, s * m = 0
  proof: by
  simp_rw [← f.map_zero, eq_iff_exists, mul_zero]

中文:
定理 map_eq_zero_iff
  条件: (f : Localization映射 S N) {m : M}
  结论: f m = 0 ↔ 存在 s : S, s * m = 0
  证明: by
  simp_rw [← f.map_zero, eq_iff_exists, mul_zero]

Depends on / 依赖: eq_iff_exists, f.map_zero, map_zero, mul_zero, simp_rw
-/
theorem map_eq_zero_iff (f : LocalizationMap S N) {m : M} : f m = 0 ↔ exists s : S, s * m = 0 := by
  simp_rw [← f.map_zero, eq_iff_exists, mul_zero]

/--
theorem `mk'_eq_zero_iff` / 定理 `mk'_eq_zero_iff`

English:
theorem mk'_eq_zero_iff
  given: (f : LocalizationMap S N) (m : M) (s : S)
  proof: by
  rw [← (f.map_units s).mul_left_inj]; rw [mk'_spec]; rw [zero_mul]; rw [map_eq_zero_iff]

中文:
定理 mk'_eq_zero_iff
  条件: (f : Localization映射 S N) (m : M) (s : S)
  证明: by
  rw [← (f.map_units s).mul_left_inj]; rw [mk'_spec]; rw [zero_mul]; rw [map_eq_zero_iff]
-/
theorem mk'_eq_zero_iff (f : LocalizationMap S N) (m : M) (s : S) :
    f.mk' m s = 0 ↔ exists s : S, s * m = 0 := by
  rw [← (f.map_units s).mul_left_inj]; rw [mk'_spec]; rw [zero_mul]; rw [map_eq_zero_iff]

/--
theorem `mk'_zero` / 定理 `mk'_zero`

English:
theorem mk'_zero
  given: (f : LocalizationMap S N) (s : S)
  statement: f.mk' 0 s = 0
  proof: by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [zero_mul]; rw [f.map_zero]

中文:
定理 mk'_zero
  条件: (f : Localization映射 S N) (s : S)
  结论: f.mk' 0 s = 0
  证明: by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [zero_mul]; rw [f.map_zero]
-/
@[simp] theorem mk'_zero (f : LocalizationMap S N) (s : S) : f.mk' 0 s = 0 := by
  rw [eq_comm]; rw [eq_mk'_iff_mul_eq]; rw [zero_mul]; rw [f.map_zero]

/--
theorem `nonZeroDivisors_le_comap` / 定理 `nonZeroDivisors_le_comap`

English:
theorem nonZeroDivisors_le_comap
  given: (f : LocalizationMap S N)
  proof: by
  refine fun m hm => nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := N) ▸ fun n h0 => ?_
  have ⟨ms, eq⟩ := f.surj n
  rw [← (f.map_units ms.2).mul_left_eq_zero]; rw [mul_right_comm]; rw [eq]; rw [← map_mul]; rw [map_eq_zero_iff] at h0
  simp_rw [← mul_assoc, mul_right_mem_nonZeroDivisorsRight_eq_

中文:
定理 nonZeroDivisors_le_comap
  条件: (f : Localization映射 S N)
  证明: by
  refine fun m hm => nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := N) ▸ fun n h0 => ?_
  have ⟨ms, eq⟩ := f.surj n
  rw [← (f.map_units ms.2).mul_left_eq_zero]; rw [mul_right_comm]; rw [eq]; rw [← map_mul]; rw [map_eq_zero_iff] at h0
  simp_rw [← mul_assoc, mul_right_mem_nonZeroDivisorsRight_eq_

Depends on / 依赖: f.map_units, f.surj, map_eq_zero_iff, map_mul, map_units, mul_assoc, mul_left_eq_zero, mul_right_comm, mul_right_mem_nonZeroDivisorsRight_eq_zero_iff, nonZeroDivisorsRight_eq_nonZeroDivisors, simp_rw
-/
theorem nonZeroDivisors_le_comap (f : LocalizationMap S N) :
    nonZeroDivisors M <= (nonZeroDivisors N).comap f := by
  refine fun m hm => nonZeroDivisorsRight_eq_nonZeroDivisors (M₀ := N) ▸ fun n h0 => ?_
  have ⟨ms, eq⟩ := f.surj n
  rw [← (f.map_units ms.2).mul_left_eq_zero]; rw [mul_right_comm]; rw [eq]; rw [← map_mul]; rw [map_eq_zero_iff] at h0
  simp_rw [← mul_assoc, mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hm.2] at h0
  rwa [← (f.map_units ms.2).mul_left_eq_zero, eq, map_eq_zero_iff]

/--
theorem `map_nonZeroDivisors_le` / 定理 `map_nonZeroDivisors_le`

English:
theorem map_nonZeroDivisors_le
  given: (f : LocalizationMap S N)
  proof: map_le_iff_le_comap.mpr f.nonZeroDivisors_le_comap

中文:
定理 map_nonZeroDivisors_le
  条件: (f : Localization映射 S N)
  证明: map_le_iff_le_comap.mpr f.nonZeroDivisors_le_comap

Depends on / 依赖: f.nonZeroDivisors_le_comap, map_le_iff_le_comap, map_le_iff_le_comap.mpr, nonZeroDivisors_le_comap
-/
theorem map_nonZeroDivisors_le (f : LocalizationMap S N) :
    (nonZeroDivisors M).map f <= nonZeroDivisors N :=
  map_le_iff_le_comap.mpr f.nonZeroDivisors_le_comap

/--
theorem `noZeroDivisors` / 定理 `noZeroDivisors`

English:
theorem noZeroDivisors
  given: (f : LocalizationMap S N) [NoZeroDivisors M]
  statement: NoZeroDivisors N
  proof: by
  refine noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr fun n hn => ?_
  have ⟨ms, eq⟩ := f.surj n
  have hs : ms.1 != 0 := fun h => hn (by rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq)
exact And.left mul_mem_nonZeroDivisors.mp
    (eq ▸ f.map_nonZeroDivisors_le ⟨_, mem_nonZeroD

中文:
定理 noZeroDivisors
  条件: (f : Localization映射 S N) [无零因子 M]
  结论: 无零因子 N
  证明: by
  refine noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr fun n hn => ?_
  have ⟨ms, eq⟩ := f.surj n
  have hs : ms.1 != 0 := fun h => hn (by rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq)
exact And.left mul_mem_nonZeroDivisors.mp
    (eq ▸ f.map_nonZeroDivisors_le ⟨_, mem_nonZeroD

Depends on / 依赖: And.left, f.map_nonZeroDivisors_le, f.map_units, f.map_zero, f.surj, map_nonZeroDivisors_le, map_units, map_zero, mem_nonZeroDivisors_of_ne_zero, mul_left_eq_zero, mul_mem_nonZeroDivisors, mul_mem_nonZeroDivisors.mp, noZeroDivisors_iff_forall_mem_nonZeroDivisors, noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr
-/
theorem noZeroDivisors (f : LocalizationMap S N) [NoZeroDivisors M] : NoZeroDivisors N := by
  refine noZeroDivisors_iff_forall_mem_nonZeroDivisors.mpr fun n hn => ?_
  have ⟨ms, eq⟩ := f.surj n
  have hs : ms.1 != 0 := fun h => hn (by rwa [h, f.map_zero, (f.map_units _).mul_left_eq_zero] at eq)
exact And.left mul_mem_nonZeroDivisors.mp
    (eq ▸ f.map_nonZeroDivisors_le ⟨_, mem_nonZeroDivisors_of_ne_zero hs, rfl⟩)

end LocalizationMap

end Submonoid

end CommMonoidWithZero
