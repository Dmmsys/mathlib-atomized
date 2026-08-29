/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Judith Ludwig, Christian Merten, Jiedong Jiang
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.Tactic.SuppressCompilation

/-!
# Completion of a module with respect to an ideal.

In this file we define the notions of Hausdorff, precomplete, and complete for an `R`-module `M`
with respect to an ideal `I`:

## Main definitions

- `IsHausdorff I M`: this says that the intersection of `I^n M` is `0`.
- `IsPrecomplete I M`: this says that every Cauchy sequence converges.
- `IsAdicComplete I M`: this says that `M` is Hausdorff and precomplete.
- `Hausdorffification I M`: this is the universal Hausdorff module with a map from `M`.
- `AdicCompletion I M`: if `I` is finitely generated, then this is the universal complete module
  with a linear map `AdicCompletion.lift` from `M`. This map is injective iff `M` is Hausdorff
  and surjective iff `M` is precomplete.
- `IsAdicComplete.lift`: if `N` is `I`-adically complete, then a compatible family of
  linear maps `M →ₗ[R] N ⧸ (I ^ n • ⊤)` can be lifted to a unique linear map `M →ₗ[R] N`.
  Together with `mk_lift_apply` and `eq_lift`, it gives the universal property of being
  `I`-adically complete.
-/

@[expose] public section

suppress_compilation

open Submodule Ideal Quotient

variable {R S T : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

/--
Definition of `IsHausdorff` / `IsHausdorff` 的定义

English:
class IsHausdorff
  parameters: : Prop where
  axioms and operations (1):
    - haus' : forall x : M, (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0

中文:
类 是豪斯多夫
  参数: : 命题 where
  公理与运算 (1 个):
    - haus' : 对任意 x : M, (对任意 n : 自然数, x ≡ 0 [SMOD (I ^ n • ⊤ : 子模 R M)]) -> x = 0
-/
class IsHausdorff : Prop where
  haus' : forall x : M, (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0

/--
Definition of `IsPrecomplete` / `IsPrecomplete` 的定义

English:
class IsPrecomplete
  parameters: : Prop where
  axioms and operations (1):
    - prec' : forall f : Nat -> M, (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) -> exists L : M, forall n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

中文:
类 是Precomplete
  参数: : 命题 where
  公理与运算 (1 个):
    - prec' : 对任意 f : 自然数 -> M, (对任意 {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : 子模 R M)]) -> 存在 L : M, 对任意 n, f n ≡ L [SMOD (I ^ n • ⊤ : 子模 R M)]
-/
class IsPrecomplete : Prop where
  prec' : forall f : Nat -> M, (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) ->
    exists L : M, forall n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)]

/-- A module `M` is `I`-adically complete if it is Hausdorff and precomplete. -/
@[mk_iff, stacks 0317 "see also `IsAdicComplete.of_bijective_iff`"]
/--
Definition of `IsAdicComplete` / `IsAdicComplete` 的定义

English:
class IsAdicComplete
  parameters: : Prop extends IsHausdorff I M, IsPrecomplete I M
  extends: IsHausdorff I M, IsPrecomplete I M
  (no additional axioms)

中文:
类 是AdicComplete
  参数: : 命题 extends 是豪斯多夫 I M, 是Precomplete I M
  继承: 是豪斯多夫 I M, 是Precomplete I M
  (无附加公理)
-/
class IsAdicComplete : Prop extends IsHausdorff I M, IsPrecomplete I M

variable {I M}

/--
theorem `IsHausdorff.haus` / 定理 `IsHausdorff.haus`

English:
theorem IsHausdorff.haus
  given: (_ : IsHausdorff I M)
  proof: IsHausdorff.haus'

中文:
定理 是豪斯多夫.haus
  条件: (_ : 是豪斯多夫 I M)
  证明: IsHausdorff.haus'

Depends on / 依赖: IsHausdorff, IsHausdorff.haus
-/
theorem IsHausdorff.haus (_ : IsHausdorff I M) :
    forall x : M, (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0 :=
  IsHausdorff.haus'

/--
theorem `isHausdorff_iff` / 定理 `isHausdorff_iff`

English:
theorem isHausdorff_iff
  proof: ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

中文:
定理 isHausdorff_iff
  证明: ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

Depends on / 依赖: IsHausdorff, IsHausdorff.haus
-/
theorem isHausdorff_iff :
    IsHausdorff I M ↔ forall x : M, (forall n : Nat, x ≡ 0 [SMOD (I ^ n • ⊤ : Submodule R M)]) -> x = 0 :=
  ⟨IsHausdorff.haus, fun h => ⟨h⟩⟩

/--
theorem `IsHausdorff.eq_iff_smodEq` / 定理 `IsHausdorff.eq_iff_smodEq`

English:
theorem IsHausdorff.eq_iff_smodEq
  given: [IsHausdorff I M] {x y : M}
  proof: by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h

中文:
定理 是豪斯多夫.eq_iff_smodEq
  条件: [是豪斯多夫 I M] {x y : M}
  证明: by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h

Depends on / 依赖: IsHausdorff, IsHausdorff.haus, SModEq, SModEq.sub_mem, sub_eq_zero, sub_mem
-/
theorem IsHausdorff.eq_iff_smodEq [IsHausdorff I M] {x y : M} :
    x = y ↔ forall n, x ≡ y [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  refine ⟨fun h _ => h ▸ rfl, fun h => ?_⟩
  rw [← sub_eq_zero]
  apply IsHausdorff.haus' (I := I) (x - y)
  simpa [SModEq.sub_mem] using h

/--
theorem `IsHausdorff.map_algebraMap_iff` / 定理 `IsHausdorff.map_algebraMap_iff`

English:
theorem IsHausdorff.map_algebraMap_iff
  statement: [CommRing S] [Module S M] [Algebra R S]
  proof: by
  simp [isHausdorff_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

中文:
定理 是豪斯多夫.map_algebraMap_iff
  结论: [交换环 S] [模 S M] [代数 R S]
  证明: by
  simp [isHausdorff_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

Depends on / 依赖: Ideal.map_pow, SModEq, SModEq.restrictScalars, isHausdorff_iff, map_pow, restrictScalars, restrictScalars_map_smul_eq
-/
theorem IsHausdorff.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsHausdorff (I.map (algebraMap R S)) M ↔ IsHausdorff I M := by
  simp [isHausdorff_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

/--
theorem `IsHausdorff.of_map` / 定理 `IsHausdorff.of_map`

English:
theorem IsHausdorff.of_map
  statement: [CommRing S] [Module S M] {J : Ideal S} [Algebra R S]
  proof: by
  refine ⟨fun x h => IsHausdorff.haus ‹_› x fun n => ?_⟩
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid]
    rw [AddS

中文:
定理 是豪斯多夫.of_map
  结论: [交换环 S] [模 S M] {J : 理想 S} [代数 R S]
  证明: by
  refine ⟨fun x h => IsHausdorff.haus ‹_› x fun n => ?_⟩
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid]
    rw [AddS

Depends on / 依赖: AddSubgroup, AddSubgroup.toAddSubmonoid_le, AddSubmonoid, AddSubmonoid.smul_le, AddSubmonoid.smul_mem_smul, Ideal.map_pow, Ideal.mem_map_of_mem, Ideal.pow_right_mono, IsHausdorff, IsHausdorff.haus, SModEq, SModEq.of_toAddSubgroup_le, Submodule, Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid, algebraMap, algebraMap_smul, map_pow, mem_map_of_mem, of_toAddSubgroup_le
-/
theorem IsHausdorff.of_map [CommRing S] [Module S M] {J : Ideal S} [Algebra R S]
    [IsScalarTower R S M] (hIJ : I.map (algebraMap R S) <= J) [IsHausdorff J M] :
    IsHausdorff I M := by
  refine ⟨fun x h => IsHausdorff.haus ‹_› x fun n => ?_⟩
  apply SModEq.of_toAddSubgroup_le
      (U := (I ^ n • ⊤ : Submodule R M)) (V := (J ^ n • ⊤ : Submodule S M))
  · rw [← AddSubgroup.toAddSubmonoid_le]
    simp only [Submodule.smul_toAddSubmonoid, Submodule.top_toAddSubmonoid]
    rw [AddSubmonoid.smul_le]
    intro r hr m hm
    rw [← algebraMap_smul S r m]
    apply AddSubmonoid.smul_mem_smul ?_ hm
    have := Ideal.mem_map_of_mem (algebraMap R S) hr
    simp only [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hIJ n this
  · exact h n

variable (I) in
/--
theorem `IsHausdorff.funext` / 定理 `IsHausdorff.funext`

English:
theorem IsHausdorff.funext
  statement: {M : Type*} [IsHausdorff I N] {f g : M -> N}
  proof: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  exact h n m

中文:
定理 是豪斯多夫.funext
  结论: {M : 类型} [是豪斯多夫 I N] {f g : M -> N}
  证明: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  exact h n m

Depends on / 依赖: Submodule
-/
theorem IsHausdorff.funext {M : Type*} [IsHausdorff I N] {f g : M -> N}
    (h : forall n m, Submodule.Quotient.mk (p := (I ^ n • ⊤ : Submodule R N)) (f m) =
    Submodule.Quotient.mk (g m)) :
    f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  exact h n m

variable (I) in
/--
theorem `IsHausdorff.StrictMono.funext` / 定理 `IsHausdorff.StrictMono.funext`

English:
theorem IsHausdorff.StrictMono.funext
  statement: {M : Type*} [IsHausdorff I N] {f g : M -> N} {a : Nat -> Nat}
  proof: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I N ha.le_apply)
  exact h n m

中文:
定理 是豪斯多夫.严格递增.funext
  结论: {M : 类型} [是豪斯多夫 I N] {f g : M -> N} {a : 自然数 -> 自然数}
  证明: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I N ha.le_apply)
  exact h n m

Depends on / 依赖: Submodule
-/
theorem IsHausdorff.StrictMono.funext {M : Type*} [IsHausdorff I N] {f g : M -> N} {a : Nat -> Nat}
    (ha : StrictMono a) (h : forall n m, Submodule.Quotient.mk (p := (I ^ a n • ⊤ : Submodule R N))
    (f m) = Submodule.Quotient.mk (g m)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I N ha.le_apply)
  exact h n m

/--
theorem `IsHausdorff.funext'` / 定理 `IsHausdorff.funext'`

English:
theorem IsHausdorff.funext'
  statement: {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
  proof: by
  ext r
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using! h n r

中文:
定理 是豪斯多夫.funext'
  结论: {R S : 类型} [交换环 S] (I : 理想 S) [是豪斯多夫 I S]
  证明: by
  ext r
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using! h n r

Depends on / 依赖: IsHausdorff, IsHausdorff.eq_iff_smodEq, eq_iff_smodEq
-/
theorem IsHausdorff.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R -> S} (h : forall n r, Ideal.Quotient.mk (I ^ n) (f r) = Ideal.Quotient.mk (I ^ n) (g r)) :
    f = g := by
  ext r
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  simpa using! h n r

/--
theorem `IsHausdorff.StrictMono.funext'` / 定理 `IsHausdorff.StrictMono.funext'`

English:
theorem IsHausdorff.StrictMono.funext'
  statement: {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
  proof: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I S ha.le_apply)
  simpa using! h n m

中文:
定理 是豪斯多夫.严格递增.funext'
  结论: {R S : 类型} [交换环 S] (I : 理想 S) [是豪斯多夫 I S]
  证明: by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I S ha.le_apply)
  simpa using! h n m

Depends on / 依赖: IsHausdorff, IsHausdorff.eq_iff_smodEq, SModEq, SModEq.mono, Submodule, Submodule.pow_smul_top_le, eq_iff_smodEq, ha.le_apply, le_apply, pow_smul_top_le
-/
theorem IsHausdorff.StrictMono.funext' {R S : Type*} [CommRing S] (I : Ideal S) [IsHausdorff I S]
    {f g : R -> S} {a : Nat -> Nat} (ha : StrictMono a) (h : forall n r, Ideal.Quotient.mk (I ^ a n) (f r) =
    Ideal.Quotient.mk (I ^ a n) (g r)) : f = g := by
  ext m
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro n
  apply SModEq.mono (Submodule.pow_smul_top_le I S ha.le_apply)
  simpa using! h n m

/--
theorem `IsPrecomplete.prec` / 定理 `IsPrecomplete.prec`

English:
theorem IsPrecomplete.prec
  given: (_ : IsPrecomplete I M) {f : Nat -> M}
  proof: IsPrecomplete.prec' _

中文:
定理 是Precomplete.prec
  条件: (_ : 是Precomplete I M) {f : 自然数 -> M}
  证明: IsPrecomplete.prec' _

Depends on / 依赖: IsPrecomplete, IsPrecomplete.prec
-/
theorem IsPrecomplete.prec (_ : IsPrecomplete I M) {f : Nat -> M} :
    (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) ->
      exists L : M, forall n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  IsPrecomplete.prec' _

/--
theorem `isPrecomplete_iff` / 定理 `isPrecomplete_iff`

English:
theorem isPrecomplete_iff
  proof: ⟨fun h => h.1, fun h => ⟨h⟩⟩

中文:
定理 isPrecomplete_iff
  证明: ⟨fun h => h.1, fun h => ⟨h⟩⟩
-/
theorem isPrecomplete_iff :
    IsPrecomplete I M ↔
      forall f : Nat -> M,
        (forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]) ->
          exists L : M, forall n, f n ≡ L [SMOD (I ^ n • ⊤ : Submodule R M)] :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/--
theorem `IsPrecomplete.map_algebraMap_iff` / 定理 `IsPrecomplete.map_algebraMap_iff`

English:
theorem IsPrecomplete.map_algebraMap_iff
  statement: [CommRing S] [Module S M] [Algebra R S]
  proof: by
  simp [isPrecomplete_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

中文:
定理 是Precomplete.map_algebraMap_iff
  结论: [交换环 S] [模 S M] [代数 R S]
  证明: by
  simp [isPrecomplete_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

Depends on / 依赖: Ideal.map_pow, SModEq, SModEq.restrictScalars, isPrecomplete_iff, map_pow, restrictScalars, restrictScalars_map_smul_eq
-/
theorem IsPrecomplete.map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsPrecomplete (I.map (algebraMap R S)) M ↔ IsPrecomplete I M := by
  simp [isPrecomplete_iff, ← Ideal.map_pow, ← SModEq.restrictScalars R,
    restrictScalars_map_smul_eq]

variable (I M)

/--
Definition of `Hausdorffification` / `Hausdorffification` 的定义

English:
abbreviation Hausdorffification
  signature: : Type _
  body: M ⧸ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M)

中文:
缩写 Hausdorffification
  签名: : 类型 _
  定义体: M ⧸ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M)

Depends on / 依赖: Submodule
-/
abbrev Hausdorffification : Type _ :=
  M ⧸ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M)

/--
Definition of `AdicCompletion.transitionMap` / `AdicCompletion.transitionMap` 的定义

English:
abbreviation AdicCompletion.transitionMap
  signature: {m n : Nat} (hmn : m <= n)
  body: factorPow I M hmn

中文:
缩写 AdicCompletion.transitionMap
  签名: {m n : 自然数} (hmn : m <= n)
  定义体: factorPow I M hmn

Depends on / 依赖: factorPow
-/
abbrev AdicCompletion.transitionMap {m n : Nat} (hmn : m <= n) := factorPow I M hmn

/--
Definition of `AdicCompletion` / `AdicCompletion` 的定义

English:
definition AdicCompletion
  signature: : Type _
  body: { f : forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }

中文:
定义 AdicCompletion
  签名: : 类型 _
  定义体: { f : forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }

Depends on / 依赖: AdicCompletion, AdicCompletion.transitionMap, Submodule, transitionMap
-/
def AdicCompletion : Type _ :=
  { f : forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M) //
    forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }

namespace IsHausdorff

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : IsHausdorff (⊥ : Ideal R) M
  body: ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

中文:
实例 bot
  签名: : 是豪斯多夫 (⊥ : 理想 R) M
  定义体: ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

Depends on / 依赖: SModEq, SModEq.bot, bot_smul, pow_one
-/
instance bot : IsHausdorff (⊥ : Ideal R) M :=
  ⟨fun x hx => by simpa only [pow_one ⊥, bot_smul, SModEq.bot] using hx 1⟩

variable {M} in
/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (h : IsHausdorff (⊤ : Ideal R) M)
  statement: Subsingleton M
  proof: ⟨fun x y => eq_of_sub_eq_zero h.haus (x - y) fun n => by
    rw [Ideal.top_pow]; rw [top_smul]
    exact SModEq.top⟩

中文:
定理 subsingleton
  条件: (h : 是豪斯多夫 (⊤ : 理想 R) M)
  结论: 子单例 M
  证明: ⟨fun x y => eq_of_sub_eq_zero h.haus (x - y) fun n => by
    rw [Ideal.top_pow]; rw [top_smul]
    exact SModEq.top⟩
-/
protected theorem subsingleton (h : IsHausdorff (⊤ : Ideal R) M) : Subsingleton M :=
⟨fun x y => eq_of_sub_eq_zero h.haus (x - y) fun n => by
    rw [Ideal.top_pow]; rw [top_smul]
    exact SModEq.top⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsHausdorff I M :=
  ⟨fun _ _ => Subsingleton.elim _ _⟩

variable {I M}

/--
theorem `iInf_pow_smul` / 定理 `iInf_pow_smul`

English:
theorem iInf_pow_smul
  given: (h : IsHausdorff I M)
  statement: (⨅ n : Nat, I ^ n • ⊤ : Submodule R M) = ⊥
  proof: eq_bot_iff.2 fun x hx =>
(mem_bot _).2 h.haus x fun n => SModEq.zero.2 (mem_iInf fun n : Nat => I ^ n • ⊤).1 hx n

中文:
定理 iInf_pow_smul
  条件: (h : 是豪斯多夫 I M)
  结论: (⨅ n : 自然数, I ^ n • ⊤ : 子模 R M) = ⊥
  证明: eq_bot_iff.2 fun x hx =>
(mem_bot _).2 h.haus x fun n => SModEq.zero.2 (mem_iInf fun n : Nat => I ^ n • ⊤).1 hx n

Depends on / 依赖: SModEq, SModEq.zero, eq_bot_iff, h.haus, mem_bot, mem_iInf
-/
theorem iInf_pow_smul (h : IsHausdorff I M) : (⨅ n : Nat, I ^ n • ⊤ : Submodule R M) = ⊥ :=
  eq_bot_iff.2 fun x hx =>
(mem_bot _).2 h.haus x fun n => SModEq.zero.2 (mem_iInf fun n : Nat => I ^ n • ⊤).1 hx n

end IsHausdorff

namespace Hausdorffification

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : M ->ₗ[R] Hausdorffification I M
  body: mkQ _

中文:
定义 of
  签名: : M ->ₗ[R] Hausdorffification I M
  定义体: mkQ _
-/
def of : M ->ₗ[R] Hausdorffification I M :=
  mkQ _

variable {I M}

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {C : Hausdorffification I M -> Prop} (x : Hausdorffification I M)
  proof: Quotient.inductionOn' x ih

中文:
定理 induction_on
  结论: {C : Hausdorffification I M -> 命题} (x : Hausdorffification I M)
  证明: Quotient.inductionOn' x ih

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem induction_on {C : Hausdorffification I M -> Prop} (x : Hausdorffification I M)
    (ih : forall x, C (of I M x)) : C x :=
  Quotient.inductionOn' x ih

variable (I M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsHausdorff I (Hausdorffification I M)
  body: ⟨fun x => Quotient.inductionOn' x fun x hx =>
(Quotient.mk_eq_zero _).2 (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this]; rw [map_sm

中文:
实例 :
  签名: 是豪斯多夫 I (Hausdorffification I M)
  定义体: ⟨fun x => Quotient.inductionOn' x fun x hx =>
(Quotient.mk_eq_zero _).2 (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this]; rw [map_sm

Depends on / 依赖: Quotient, Quotient.inductionOn, Quotient.mk_eq_zero, SModEq, SModEq.zero, Submodule, Submodule.map_top, Submodule.mem_comap, comap_map_mkQ, iInf_le, inductionOn, map_smul, map_top, mem_comap, mem_iInf, mk_eq_zero, range_mkQ, sup_of_le_right
-/
instance : IsHausdorff I (Hausdorffification I M) :=
  ⟨fun x => Quotient.inductionOn' x fun x hx =>
(Quotient.mk_eq_zero _).2 (mem_iInf _).2 fun n => by
      have := comap_map_mkQ (⨅ n : Nat, I ^ n • ⊤ : Submodule R M) (I ^ n • ⊤)
      simp only [sup_of_le_right (iInf_le (fun n => (I ^ n • ⊤ : Submodule R M)) n)] at this
      rw [← this]; rw [map_smul'']; rw [Submodule.mem_comap]; rw [Submodule.map_top]; rw [range_mkQ]; rw [← SModEq.zero]
      exact hx n⟩

variable {M} [h : IsHausdorff I N]

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : M ->ₗ[R] N)
  body: liftQ _ f map_le_iff_le_comap.1 h.iInf_pow_smul ▸ le_iInf fun n =>
le_trans (map_mono <| iInf_le _ n) by
      rw [map_smul'']
      exact smul_mono le_rfl le_top

中文:
定义 lift
  签名: (f : M ->ₗ[R] N)
  定义体: liftQ _ f map_le_iff_le_comap.1 h.iInf_pow_smul ▸ le_iInf fun n =>
le_trans (map_mono <| iInf_le _ n) by
      rw [map_smul'']
      exact smul_mono le_rfl le_top

Depends on / 依赖: h.iInf_pow_smul, iInf_le, iInf_pow_smul, le_iInf, le_rfl, le_top, le_trans, map_le_iff_le_comap, map_mono, map_smul, smul_mono
-/
def lift (f : M ->ₗ[R] N) : Hausdorffification I M ->ₗ[R] N :=
liftQ _ f map_le_iff_le_comap.1 h.iInf_pow_smul ▸ le_iInf fun n =>
le_trans (map_mono <| iInf_le _ n) by
      rw [map_smul'']
      exact smul_mono le_rfl le_top

/--
theorem `lift_of` / 定理 `lift_of`

English:
theorem lift_of
  given: (f : M ->ₗ[R] N) (x : M)
  statement: lift I f (of I M x) = f x
  proof: rfl

中文:
定理 lift_of
  条件: (f : M ->ₗ[R] N) (x : M)
  结论: lift I f (of I M x) = f x
  证明: rfl
-/
theorem lift_of (f : M ->ₗ[R] N) (x : M) : lift I f (of I M x) = f x :=
  rfl

/--
theorem `lift_comp_of` / 定理 `lift_comp_of`

English:
theorem lift_comp_of
  given: (f : M ->ₗ[R] N)
  statement: (lift I f).comp (of I M) = f
  proof: LinearMap.ext fun _ => rfl

中文:
定理 lift_comp_of
  条件: (f : M ->ₗ[R] N)
  结论: (lift I f).comp (of I M) = f
  证明: LinearMap.ext fun _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext
-/
theorem lift_comp_of (f : M ->ₗ[R] N) : (lift I f).comp (of I M) = f :=
  LinearMap.ext fun _ => rfl

/--
theorem `lift_eq` / 定理 `lift_eq`

English:
theorem lift_eq
  given: (f : M ->ₗ[R] N) (g : Hausdorffification I M ->ₗ[R] N) (hg : g.comp (of I M) = f)
  proof: LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

中文:
定理 lift_eq
  条件: (f : M ->ₗ[R] N) (g : Hausdorffification I M ->ₗ[R] N) (hg : g.comp (of I M) = f)
  证明: LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, LinearMap.ext, comp_apply, induction_on, lift_of
-/
theorem lift_eq (f : M ->ₗ[R] N) (g : Hausdorffification I M ->ₗ[R] N) (hg : g.comp (of I M) = f) :
    g = lift I f :=
  LinearMap.ext fun x => induction_on x fun x => by rw [lift_of, ← hg, LinearMap.comp_apply]

end Hausdorffification

namespace IsPrecomplete

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : IsPrecomplete (⊥ : Ideal R) M
  body: by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one]; rw [bot_smul]; rw [SModEq.bot] at hf; rw [hf]

中文:
实例 bot
  签名: : 是Precomplete (⊥ : 理想 R) M
  定义体: by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one]; rw [bot_smul]; rw [SModEq.bot] at hf; rw [hf]

Depends on / 依赖: Ideal.one_eq_top, Nat.le_add_left, SModEq, SModEq.bot, SModEq.top, bot_smul, le_add_left, one_eq_top, pow_one, pow_zero, specialize, top_smul
-/
instance bot : IsPrecomplete (⊥ : Ideal R) M := by
  refine ⟨fun f hf => ⟨f 1, fun n => ?_⟩⟩
  rcases n with - | n
  · rw [pow_zero, Ideal.one_eq_top, top_smul]
    exact SModEq.top
  specialize hf (Nat.le_add_left 1 n)
  rw [pow_one]; rw [bot_smul]; rw [SModEq.bot] at hf; rw [hf]

/--
Instance `top` / 实例 `top`

English:
instance top
  signature: : IsPrecomplete (⊤ : Ideal R) M
  body: ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow]; rw [top_smul]
      exact SModEq.top⟩⟩

中文:
实例 top
  签名: : 是Precomplete (⊤ : 理想 R) M
  定义体: ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow]; rw [top_smul]
      exact SModEq.top⟩⟩

Depends on / 依赖: Ideal.top_pow, SModEq, SModEq.top, top_pow, top_smul
-/
instance top : IsPrecomplete (⊤ : Ideal R) M :=
  ⟨fun f _ =>
    ⟨0, fun n => by
      rw [Ideal.top_pow]; rw [top_smul]
      exact SModEq.top⟩⟩

instance (priority := 100) of_subsingleton [Subsingleton M] : IsPrecomplete I M :=
  ⟨fun f _ => ⟨0, fun n => by rw [Subsingleton.elim (f n) 0]⟩⟩

end IsPrecomplete

namespace AdicCompletion

/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: : Submodule R (forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  body: { f | forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply]; rw [Pi.add_apply]; rw [map_add]; rw [hf hmn]; rw [hg hmn]
  smul_mem' c f hf m n hmn := by rw 

中文:
定义 submodule
  签名: : 子模 R (对任意 n : 自然数, M ⧸ (I ^ n • ⊤ : 子模 R M)) where
  定义体: { f | forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply]; rw [Pi.add_apply]; rw [map_add]; rw [hf hmn]; rw [hg hmn]
  smul_mem' c f hf m n hmn := by rw 

Depends on / 依赖: AdicCompletion, AdicCompletion.transitionMap, transitionMap
-/
def submodule : Submodule R (forall n : Nat, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  carrier := { f | forall {m n} (hmn : m <= n), AdicCompletion.transitionMap I M hmn (f n) = f m }
  zero_mem' hmn := by rw [Pi.zero_apply, Pi.zero_apply, map_zero]
  add_mem' hf hg m n hmn := by
    rw [Pi.add_apply]; rw [Pi.add_apply]; rw [map_add]; rw [hf hmn]; rw [hg hmn]
  smul_mem' c f hf m n hmn := by rw [Pi.smul_apply, Pi.smul_apply, map_smul, hf hmn]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (AdicCompletion I M)
  body: ⟨0, by simp⟩

中文:
实例 :
  签名: 零 (AdicCompletion I M)
  定义体: ⟨0, by simp⟩
-/
instance : Zero (AdicCompletion I M) where
  zero := ⟨0, by simp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (AdicCompletion I M)
  body: ⟨x.val + y.val, by simp [x.property, y.property]⟩

中文:
实例 :
  签名: 加法 (AdicCompletion I M)
  定义体: ⟨x.val + y.val, by simp [x.property, y.property]⟩

Depends on / 依赖: property, x.property, x.val, y.property, y.val
-/
instance : Add (AdicCompletion I M) where
  add x y := ⟨x.val + y.val, by simp [x.property, y.property]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (AdicCompletion I M)
  body: ⟨- x.val, by simp [x.property]⟩

中文:
实例 :
  签名: 取负 (AdicCompletion I M)
  定义体: ⟨- x.val, by simp [x.property]⟩

Depends on / 依赖: property, x.property, x.val
-/
instance : Neg (AdicCompletion I M) where
  neg x := ⟨- x.val, by simp [x.property]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (AdicCompletion I M)
  body: ⟨x.val - y.val, by simp [x.property, y.property]⟩

中文:
实例 :
  签名: 减法 (AdicCompletion I M)
  定义体: ⟨x.val - y.val, by simp [x.property, y.property]⟩

Depends on / 依赖: property, x.property, x.val, y.property, y.val
-/
instance : Sub (AdicCompletion I M) where
  sub x y := ⟨x.val - y.val, by simp [x.property, y.property]⟩

/--
Instance `instSMul` / 实例 `instSMul`

English:
instance instSMul
  signature: [SMul S R] [SMul S M] [IsScalarTower S R M]
  body: ⟨r • x.val, by simp [x.property]⟩

中文:
实例 instSMul
  签名: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M]
  定义体: ⟨r • x.val, by simp [x.property]⟩

Depends on / 依赖: property, x.property, x.val
-/
instance instSMul [SMul S R] [SMul S M] [IsScalarTower S R M] : SMul S (AdicCompletion I M) where
  smul r x := ⟨r • x.val, by simp [x.property]⟩

/--
lemma `val_zero` / 引理 `val_zero`

English:
lemma val_zero
  statement: (0 : AdicCompletion I M).val = 0
  proof: rfl

中文:
引理 val_zero
  结论: (0 : AdicCompletion I M).val = 0
  证明: rfl
-/
@[simp, norm_cast] lemma val_zero : (0 : AdicCompletion I M).val = 0 := rfl

/--
lemma `val_zero_apply` / 引理 `val_zero_apply`

English:
lemma val_zero_apply
  given: (n : Nat)
  statement: (0 : AdicCompletion I M).val n = 0
  proof: rfl

中文:
引理 val_zero_apply
  条件: (n : 自然数)
  结论: (0 : AdicCompletion I M).val n = 0
  证明: rfl
-/
lemma val_zero_apply (n : Nat) : (0 : AdicCompletion I M).val n = 0 := rfl

variable {I M}

/--
lemma `val_add` / 引理 `val_add`

English:
lemma val_add
  given: (f g : AdicCompletion I M)
  statement: (f + g).val = f.val + g.val
  proof: rfl

中文:
引理 val_add
  条件: (f g : AdicCompletion I M)
  结论: (f + g).val = f.val + g.val
  证明: rfl
-/
@[simp, norm_cast] lemma val_add (f g : AdicCompletion I M) : (f + g).val = f.val + g.val := rfl
/--
lemma `val_sub` / 引理 `val_sub`

English:
lemma val_sub
  given: (f g : AdicCompletion I M)
  statement: (f - g).val = f.val - g.val
  proof: rfl

中文:
引理 val_sub
  条件: (f g : AdicCompletion I M)
  结论: (f - g).val = f.val - g.val
  证明: rfl
-/
@[simp, norm_cast] lemma val_sub (f g : AdicCompletion I M) : (f - g).val = f.val - g.val := rfl
/--
lemma `val_neg` / 引理 `val_neg`

English:
lemma val_neg
  given: (f : AdicCompletion I M)
  statement: (-f).val = -f.val
  proof: rfl

中文:
引理 val_neg
  条件: (f : AdicCompletion I M)
  结论: (-f).val = -f.val
  证明: rfl
-/
@[simp, norm_cast] lemma val_neg (f : AdicCompletion I M) : (-f).val = -f.val := rfl

/--
lemma `val_add_apply` / 引理 `val_add_apply`

English:
lemma val_add_apply
  given: (f g : AdicCompletion I M) (n : Nat)
  statement: (f + g).val n = f.val n + g.val n
  proof: rfl

中文:
引理 val_add_apply
  条件: (f g : AdicCompletion I M) (n : 自然数)
  结论: (f + g).val n = f.val n + g.val n
  证明: rfl
-/
lemma val_add_apply (f g : AdicCompletion I M) (n : Nat) : (f + g).val n = f.val n + g.val n := rfl
/--
lemma `val_sub_apply` / 引理 `val_sub_apply`

English:
lemma val_sub_apply
  given: (f g : AdicCompletion I M) (n : Nat)
  statement: (f - g).val n = f.val n - g.val n
  proof: rfl

中文:
引理 val_sub_apply
  条件: (f g : AdicCompletion I M) (n : 自然数)
  结论: (f - g).val n = f.val n - g.val n
  证明: rfl
-/
lemma val_sub_apply (f g : AdicCompletion I M) (n : Nat) : (f - g).val n = f.val n - g.val n := rfl
/--
lemma `val_neg_apply` / 引理 `val_neg_apply`

English:
lemma val_neg_apply
  given: (f : AdicCompletion I M) (n : Nat)
  statement: (-f).val n = -f.val n
  proof: rfl

中文:
引理 val_neg_apply
  条件: (f : AdicCompletion I M) (n : 自然数)
  结论: (-f).val n = -f.val n
  证明: rfl
-/
lemma val_neg_apply (f : AdicCompletion I M) (n : Nat) : (-f).val n = -f.val n := rfl

/- No `simp` attribute, since it causes `simp` unification timeouts when considering
the `Module (AdicCompletion I R) (AdicCompletion I M)` instance (see `AdicCompletion/Algebra`). -/
@[norm_cast]
/--
lemma `val_smul` / 引理 `val_smul`

English:
lemma val_smul
  given: [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
  proof: rfl

中文:
引理 val_smul
  条件: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M] (s : S) (f : AdicCompletion I M)
  证明: rfl
-/
lemma val_smul [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M) :
    (s • f).val = s • f.val := rfl

/--
lemma `val_smul_apply` / 引理 `val_smul_apply`

English:
lemma val_smul_apply
  statement: [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
  proof: rfl

@[ext]

中文:
引理 val_smul_apply
  结论: [标量乘法 S R] [标量乘法 S M] [标量塔 S R M] (s : S) (f : AdicCompletion I M)
  证明: rfl

@[ext]
-/
lemma val_smul_apply [SMul S R] [SMul S M] [IsScalarTower S R M] (s : S) (f : AdicCompletion I M)
    (n : Nat) : (s • f).val n = s • f.val n := rfl

@[ext]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {x y : AdicCompletion I M} (h : forall n, x.val n = y.val n)
  statement: x = y
  proof: Subtype.ext funext h

中文:
引理 ext
  条件: {x y : AdicCompletion I M} (h : 对任意 n, x.val n = y.val n)
  结论: x = y
  证明: Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext
-/
lemma ext {x y : AdicCompletion I M} (h : forall n, x.val n = y.val n) : x = y := Subtype.ext funext h

variable (I M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (AdicCompletion I M)
  body: let f : AdicCompletion I M -> forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ => val_smul ..)
    (fun _ _ => val_smul ..)

中文:
实例 :
  签名: 加法交换群 (AdicCompletion I M)
  定义体: let f : AdicCompletion I M -> forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ => val_smul ..)
    (fun _ _ => val_smul ..)

Depends on / 依赖: AdicCompletion, Submodule, Subtype, Subtype.val, Subtype.val_injective.addCommGroup, addCommGroup, val_add, val_injective, val_neg, val_smul, val_sub
-/
instance : AddCommGroup (AdicCompletion I M) :=
  let f : AdicCompletion I M -> forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) := Subtype.val
  Subtype.val_injective.addCommGroup f rfl val_add val_neg val_sub (fun _ _ => val_smul ..)
    (fun _ _ => val_smul ..)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [SMul S R] [Module S M] [IsScalarTower S R M] :
  body: let f : AdicCompletion I M ->+ forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module S f val_smul

中文:
实例 [半环
  签名: S] [标量乘法 S R] [模 S M] [标量塔 S R M] :
  定义体: let f : AdicCompletion I M ->+ forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module S f val_smul

Depends on / 依赖: AdicCompletion, Submodule, Subtype, Subtype.val, Subtype.val_injective.module, map_add, map_zero, module, val_injective, val_smul
-/
instance [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (AdicCompletion I M) :=
  let f : AdicCompletion I M ->+ forall n, M ⧸ (I ^ n • ⊤ : Submodule R M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module S f val_smul

/--
Instance `instIsScalarTower` / 实例 `instIsScalarTower`

English:
instance instIsScalarTower
  signature: [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M]
  body: by ext; simp [val_smul]

中文:
实例 instIsScalarTower
  签名: [标量乘法 S T] [标量乘法 S R] [标量乘法 T R] [标量乘法 S M] [标量乘法 T M]
  定义体: by ext; simp [val_smul]

Depends on / 依赖: val_smul
-/
instance instIsScalarTower [SMul S T] [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [IsScalarTower S T M] :
    IsScalarTower S T (AdicCompletion I M) where
  smul_assoc s t f := by ext; simp [val_smul]

/--
Instance `instSMulCommClass` / 实例 `instSMulCommClass`

English:
instance instSMulCommClass
  signature: [SMul S R] [SMul T R] [SMul S M] [SMul T M]
  body: by ext; simp [val_smul, smul_comm]

中文:
实例 instSMulCommClass
  签名: [标量乘法 S R] [标量乘法 T R] [标量乘法 S M] [标量乘法 T M]
  定义体: by ext; simp [val_smul, smul_comm]

Depends on / 依赖: smul_comm, val_smul
-/
instance instSMulCommClass [SMul S R] [SMul T R] [SMul S M] [SMul T M]
    [IsScalarTower S R M] [IsScalarTower T R M] [SMulCommClass S T M] :
    SMulCommClass S T (AdicCompletion I M) where
  smul_comm s t f := by ext; simp [val_smul, smul_comm]

/--
Instance `instIsCentralScalar` / 实例 `instIsCentralScalar`

English:
instance instIsCentralScalar
  signature: [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M]
  body: by ext; simp [val_smul, op_smul_eq_smul]

中文:
实例 instIsCentralScalar
  签名: [标量乘法 S R] [标量乘法 Sᵐᵒᵖ R] [标量乘法 S M] [标量乘法 Sᵐᵒᵖ M]
  定义体: by ext; simp [val_smul, op_smul_eq_smul]

Depends on / 依赖: op_smul_eq_smul, val_smul
-/
instance instIsCentralScalar [SMul S R] [SMul Sᵐᵒᵖ R] [SMul S M] [SMul Sᵐᵒᵖ M]
    [IsScalarTower S R M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (AdicCompletion I M) where
  op_smul_eq_smul s f := by ext; simp [val_smul, op_smul_eq_smul]

/-- The canonical inclusion from the completion to the product. -/
@[simps]
/--
Definition of `incl` / `incl` 的定义

English:
definition incl
  signature: : AdicCompletion I M ->ₗ[R] (forall n, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  body: x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 incl
  签名: : AdicCompletion I M ->ₗ[R] (对任意 n, M ⧸ (I ^ n • ⊤ : 子模 R M)) where
  定义体: x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: x.val
-/
def incl : AdicCompletion I M ->ₗ[R] (forall n, M ⧸ (I ^ n • ⊤ : Submodule R M)) where
  toFun x := x.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable {I M}

@[simp, norm_cast]
/--
lemma `val_sum` / 引理 `val_sum`

English:
lemma val_sum
  given: {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M)
  proof: by
  simp_rw [← funext (incl_apply _ _ _), map_sum]

中文:
引理 val_sum
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> AdicCompletion I M)
  证明: by
  simp_rw [← funext (incl_apply _ _ _), map_sum]

Depends on / 依赖: incl_apply, map_sum, simp_rw
-/
lemma val_sum {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M) :
    (∑ i in s, f i).val = ∑ i in s, (f i).val := by
  simp_rw [← funext (incl_apply _ _ _), map_sum]

/--
lemma `val_sum_apply` / 引理 `val_sum_apply`

English:
lemma val_sum_apply
  given: {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M) (n : Nat)
  proof: by simp

中文:
引理 val_sum_apply
  条件: {ι : 类型} (s : 有限集 ι) (f : ι -> AdicCompletion I M) (n : 自然数)
  证明: by simp
-/
lemma val_sum_apply {ι : Type*} (s : Finset ι) (f : ι -> AdicCompletion I M) (n : Nat) :
    (∑ i in s, f i).val n = ∑ i in s, (f i).val n := by simp

variable (I M)

/--
Definition of `of` / `of` 的定义

English:
definition of
  signature: : M ->ₗ[R] AdicCompletion I M where
  body: ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 of
  签名: : M ->ₗ[R] AdicCompletion I M where
  定义体: ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

Depends on / 依赖: Submodule
-/
def of : M ->ₗ[R] AdicCompletion I M where
  toFun x := ⟨fun n => mkQ (I ^ n • ⊤ : Submodule R M) x, fun _ => rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `of_apply` / 定理 `of_apply`

English:
theorem of_apply
  given: (x : M) (n : Nat)
  statement: (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x
  proof: rfl

中文:
定理 of_apply
  条件: (x : M) (n : 自然数)
  结论: (of I M x).1 n = mkQ (I ^ n • ⊤ : 子模 R M) x
  证明: rfl
-/
theorem of_apply (x : M) (n : Nat) : (of I M x).1 n = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (n : Nat)
  body: f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]

中文:
定义 eval
  签名: (n : 自然数)
  定义体: f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
-/
def eval (n : Nat) : AdicCompletion I M ->ₗ[R] M ⧸ (I ^ n • ⊤ : Submodule R M) where
  toFun f := f.1 n
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
/--
theorem `coe_eval` / 定理 `coe_eval`

English:
theorem coe_eval
  given: (n : Nat)
  proof: rfl

中文:
定理 coe_eval
  条件: (n : 自然数)
  证明: rfl
-/
theorem coe_eval (n : Nat) :
    (eval I M n : AdicCompletion I M -> M ⧸ (I ^ n • ⊤ : Submodule R M)) = fun f => f.1 n :=
  rfl

/--
theorem `eval_apply` / 定理 `eval_apply`

English:
theorem eval_apply
  given: (n : Nat) (f : AdicCompletion I M)
  statement: eval I M n f = f.1 n
  proof: rfl

中文:
定理 eval_apply
  条件: (n : 自然数) (f : AdicCompletion I M)
  结论: eval I M n f = f.1 n
  证明: rfl
-/
theorem eval_apply (n : Nat) (f : AdicCompletion I M) : eval I M n f = f.1 n :=
  rfl

/--
theorem `eval_of` / 定理 `eval_of`

English:
theorem eval_of
  given: (n : Nat) (x : M)
  statement: eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x
  proof: rfl

@[simp]

中文:
定理 eval_of
  条件: (n : 自然数) (x : M)
  结论: eval I M n (of I M x) = mkQ (I ^ n • ⊤ : 子模 R M) x
  证明: rfl

@[simp]
-/
theorem eval_of (n : Nat) (x : M) : eval I M n (of I M x) = mkQ (I ^ n • ⊤ : Submodule R M) x :=
  rfl

@[simp]
/--
theorem `eval_comp_of` / 定理 `eval_comp_of`

English:
theorem eval_comp_of
  given: (n : Nat)
  statement: (eval I M n).comp (of I M) = mkQ _
  proof: rfl

中文:
定理 eval_comp_of
  条件: (n : 自然数)
  结论: (eval I M n).comp (of I M) = mkQ _
  证明: rfl
-/
theorem eval_comp_of (n : Nat) : (eval I M n).comp (of I M) = mkQ _ :=
  rfl

/--
theorem `eval_surjective` / 定理 `eval_surjective`

English:
theorem eval_surjective
  given: (n : Nat)
  statement: Function.Surjective (eval I M n)
  proof: fun x =>
  Quotient.inductionOn' x fun x => ⟨of I M x, rfl⟩

@[simp]

中文:
定理 eval_surjective
  条件: (n : 自然数)
  结论: 函数.满射 (eval I M n)
  证明: fun x =>
  Quotient.inductionOn' x fun x => ⟨of I M x, rfl⟩

@[simp]
-/
theorem eval_surjective (n : Nat) : Function.Surjective (eval I M n) := fun x =>
  Quotient.inductionOn' x fun x => ⟨of I M x, rfl⟩

@[simp]
/--
theorem `range_eval` / 定理 `range_eval`

English:
theorem range_eval
  given: (n : Nat)
  statement: LinearMap.range (eval I M n) = ⊤
  proof: LinearMap.range_eq_top.2 (eval_surjective I M n)

中文:
定理 range_eval
  条件: (n : 自然数)
  结论: 线性映射.range (eval I M n) = ⊤
  证明: LinearMap.range_eq_top.2 (eval_surjective I M n)

Depends on / 依赖: LinearMap, LinearMap.range_eq_top, eval_surjective, range_eq_top
-/
theorem range_eval (n : Nat) : LinearMap.range (eval I M n) = ⊤ :=
  LinearMap.range_eq_top.2 (eval_surjective I M n)

variable {I M}

variable (I M)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsHausdorff I (AdicCompletion I M)
  body: ext fun n => by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · simp only [val_smul_apply, val_zero]
      induction x.val n using Quotient.inductionOn' with | _ a
exact SModEq.zero.2 smul_mem_smul hr mem_top
    · simp only [val_add_apply, hx, va

中文:
实例 :
  签名: 是豪斯多夫 I (AdicCompletion I M)
  定义体: ext fun n => by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · simp only [val_smul_apply, val_zero]
      induction x.val n using Quotient.inductionOn' with | _ a
exact SModEq.zero.2 smul_mem_smul hr mem_top
    · simp only [val_add_apply, hx, va

Depends on / 依赖: Quotient, Quotient.inductionOn, SModEq, SModEq.zero, add_zero, inductionOn, mem_top, smul_induction_on, smul_mem_smul, val_add_apply, val_smul_apply, val_zero, val_zero_apply, x.val
-/
instance : IsHausdorff I (AdicCompletion I M) where
  haus' x h := ext fun n => by
    refine smul_induction_on (SModEq.zero.1 <| h n) (fun r hr x _ => ?_) (fun x y hx hy => ?_)
    · simp only [val_smul_apply, val_zero]
      induction x.val n using Quotient.inductionOn' with | _ a
exact SModEq.zero.2 smul_mem_smul hr mem_top
    · simp only [val_add_apply, hx, val_zero_apply, hy, add_zero]

@[simp]
/--
theorem `transitionMap_comp_eval_apply` / 定理 `transitionMap_comp_eval_apply`

English:
theorem transitionMap_comp_eval_apply
  given: {m n : Nat} (hmn : m <= n) (x : AdicCompletion I M)
  proof: x.property hmn

@[simp]

中文:
定理 transitionMap_comp_eval_apply
  条件: {m n : 自然数} (hmn : m <= n) (x : AdicCompletion I M)
  证明: x.property hmn

@[simp]

Depends on / 依赖: property, x.property
-/
theorem transitionMap_comp_eval_apply {m n : Nat} (hmn : m <= n) (x : AdicCompletion I M) :
    transitionMap I M hmn (x.val n) = x.val m :=
  x.property hmn

@[simp]
/--
theorem `transitionMap_comp_eval` / 定理 `transitionMap_comp_eval`

English:
theorem transitionMap_comp_eval
  given: {m n : Nat} (hmn : m <= n)
  proof: by
  ext x
  simp

中文:
定理 transitionMap_comp_eval
  条件: {m n : 自然数} (hmn : m <= n)
  证明: by
  ext x
  simp
-/
theorem transitionMap_comp_eval {m n : Nat} (hmn : m <= n) :
    transitionMap I M hmn ∘ₗ eval I M n = eval I M m := by
  ext x
  simp

/--
Definition of `IsAdicCauchy` / `IsAdicCauchy` 的定义

English:
definition IsAdicCauchy
  signature: (f : Nat -> M)
  body: forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

中文:
定义 IsAdicCauchy
  签名: (f : 自然数 -> M)
  定义体: forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

Depends on / 依赖: Submodule
-/
def IsAdicCauchy (f : Nat -> M) : Prop :=
  forall {m n}, m <= n -> f m ≡ f n [SMOD (I ^ m • ⊤ : Submodule R M)]

/--
Definition of `AdicCauchySequence` / `AdicCauchySequence` 的定义

English:
definition AdicCauchySequence
  signature: : Type _
  body: { f : Nat -> M // IsAdicCauchy I M f }

中文:
定义 AdicCauchySequence
  签名: : 类型 _
  定义体: { f : Nat -> M // IsAdicCauchy I M f }

Depends on / 依赖: IsAdicCauchy
-/
def AdicCauchySequence : Type _ := { f : Nat -> M // IsAdicCauchy I M f }

namespace AdicCauchySequence

/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: : Submodule R (Nat -> M) where
  body: { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

中文:
定义 submodule
  签名: : 子模 R (自然数 -> M) where
  定义体: { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

Depends on / 依赖: IsAdicCauchy
-/
def submodule : Submodule R (Nat -> M) where
  carrier := { f | IsAdicCauchy I M f }
  add_mem' := by
    intro f g hf hg m n hmn
    exact SModEq.add (hf hmn) (hg hmn)
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r f hf m n hmn
    exact SModEq.smul (hf hmn) r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (AdicCauchySequence I M)
  body: ⟨0, fun _ => rfl⟩

中文:
实例 :
  签名: 零 (AdicCauchySequence I M)
  定义体: ⟨0, fun _ => rfl⟩
-/
instance : Zero (AdicCauchySequence I M) where
  zero := ⟨0, fun _ => rfl⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (AdicCauchySequence I M)
  body: ⟨x.val + y.val, fun hmn => SModEq.add (x.property hmn) (y.property hmn)⟩

中文:
实例 :
  签名: 加法 (AdicCauchySequence I M)
  定义体: ⟨x.val + y.val, fun hmn => SModEq.add (x.property hmn) (y.property hmn)⟩

Depends on / 依赖: SModEq, SModEq.add, property, x.property, x.val, y.property, y.val
-/
instance : Add (AdicCauchySequence I M) where
  add x y := ⟨x.val + y.val, fun hmn => SModEq.add (x.property hmn) (y.property hmn)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (AdicCauchySequence I M)
  body: ⟨- x.val, fun hmn => SModEq.neg (x.property hmn)⟩

中文:
实例 :
  签名: 取负 (AdicCauchySequence I M)
  定义体: ⟨- x.val, fun hmn => SModEq.neg (x.property hmn)⟩

Depends on / 依赖: SModEq, SModEq.neg, property, x.property, x.val
-/
instance : Neg (AdicCauchySequence I M) where
  neg x := ⟨- x.val, fun hmn => SModEq.neg (x.property hmn)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (AdicCauchySequence I M)
  body: ⟨x.val - y.val, fun hmn => SModEq.sub (x.property hmn) (y.property hmn)⟩

中文:
实例 :
  签名: 减法 (AdicCauchySequence I M)
  定义体: ⟨x.val - y.val, fun hmn => SModEq.sub (x.property hmn) (y.property hmn)⟩

Depends on / 依赖: SModEq, SModEq.sub, property, x.property, x.val, y.property, y.val
-/
instance : Sub (AdicCauchySequence I M) where
  sub x y := ⟨x.val - y.val, fun hmn => SModEq.sub (x.property hmn) (y.property hmn)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (AdicCauchySequence I M)
  body: ⟨n • x.val, fun hmn => SModEq.nsmul (x.property hmn) n⟩

中文:
实例 :
  签名: 标量乘法 自然数 (AdicCauchySequence I M)
  定义体: ⟨n • x.val, fun hmn => SModEq.nsmul (x.property hmn) n⟩

Depends on / 依赖: SModEq, SModEq.nsmul, property, x.property, x.val
-/
instance : SMul Nat (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn => SModEq.nsmul (x.property hmn) n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (AdicCauchySequence I M)
  body: ⟨n • x.val, fun hmn => SModEq.zsmul (x.property hmn) n⟩

中文:
实例 :
  签名: 标量乘法 整数 (AdicCauchySequence I M)
  定义体: ⟨n • x.val, fun hmn => SModEq.zsmul (x.property hmn) n⟩

Depends on / 依赖: SModEq, SModEq.zsmul, property, x.property, x.val
-/
instance : SMul Int (AdicCauchySequence I M) where
  smul n x := ⟨n • x.val, fun hmn => SModEq.zsmul (x.property hmn) n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (AdicCauchySequence I M)
  body: by
  let f : AdicCauchySequence I M -> (Nat -> M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 :
  签名: 加法交换群 (AdicCauchySequence I M)
  定义体: by
  let f : AdicCauchySequence I M -> (Nat -> M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: AdicCauchySequence, Subtype, Subtype.val, Subtype.val_injective.addCommGroup, addCommGroup, val_injective
-/
instance : AddCommGroup (AdicCauchySequence I M) := by
  let f : AdicCauchySequence I M -> (Nat -> M) := Subtype.val
  apply Subtype.val_injective.addCommGroup f rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (AdicCauchySequence I M)
  body: ⟨r • x.val, fun hmn => SModEq.smul (x.property hmn) r⟩

中文:
实例 :
  签名: 标量乘法 R (AdicCauchySequence I M)
  定义体: ⟨r • x.val, fun hmn => SModEq.smul (x.property hmn) r⟩

Depends on / 依赖: SModEq, SModEq.smul, property, x.property, x.val
-/
instance : SMul R (AdicCauchySequence I M) where
  smul r x := ⟨r • x.val, fun hmn => SModEq.smul (x.property hmn) r⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (AdicCauchySequence I M)
  body: let f : AdicCauchySequence I M ->+ (Nat -> M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module R f (fun _ _ => rfl)

中文:
实例 :
  签名: 模 R (AdicCauchySequence I M)
  定义体: let f : AdicCauchySequence I M ->+ (Nat -> M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module R f (fun _ _ => rfl)

Depends on / 依赖: AdicCauchySequence, Subtype, Subtype.val, Subtype.val_injective.module, map_add, map_zero, module, val_injective
-/
instance : Module R (AdicCauchySequence I M) :=
  let f : AdicCauchySequence I M ->+ (Nat -> M) :=
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ => rfl }
  Subtype.val_injective.module R f (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (AdicCauchySequence I M) (fun _ => Nat -> M)
  body: f.val

@[simp]

中文:
实例 :
  签名: CoeFun (AdicCauchySequence I M) (fun _ => 自然数 -> M)
  定义体: f.val

@[simp]

Depends on / 依赖: f.val
-/
instance : CoeFun (AdicCauchySequence I M) (fun _ => Nat -> M) where
  coe f := f.val

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (n : Nat)
  statement: (0 : AdicCauchySequence I M) n = 0
  proof: rfl

中文:
定理 zero_apply
  条件: (n : 自然数)
  结论: (0 : AdicCauchySequence I M) n = 0
  证明: rfl
-/
theorem zero_apply (n : Nat) : (0 : AdicCauchySequence I M) n = 0 :=
  rfl

variable {I M}

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (n : Nat) (f g : AdicCauchySequence I M)
  statement: (f + g) n = f n + g n
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (n : 自然数) (f g : AdicCauchySequence I M)
  结论: (f + g) n = f n + g n
  证明: rfl

@[simp]
-/
theorem add_apply (n : Nat) (f g : AdicCauchySequence I M) : (f + g) n = f n + g n :=
  rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (n : Nat) (f g : AdicCauchySequence I M)
  statement: (f - g) n = f n - g n
  proof: rfl

@[simp]

中文:
定理 sub_apply
  条件: (n : 自然数) (f g : AdicCauchySequence I M)
  结论: (f - g) n = f n - g n
  证明: rfl

@[simp]
-/
theorem sub_apply (n : Nat) (f g : AdicCauchySequence I M) : (f - g) n = f n - g n :=
  rfl

@[simp]
/--
theorem `smul_apply` / 定理 `smul_apply`

English:
theorem smul_apply
  given: (n : Nat) (r : R) (f : AdicCauchySequence I M)
  statement: (r • f) n = r • f n
  proof: rfl

@[ext]

中文:
定理 smul_apply
  条件: (n : 自然数) (r : R) (f : AdicCauchySequence I M)
  结论: (r • f) n = r • f n
  证明: rfl

@[ext]
-/
theorem smul_apply (n : Nat) (r : R) (f : AdicCauchySequence I M) : (r • f) n = r • f n :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {x y : AdicCauchySequence I M} (h : forall n, x n = y n)
  statement: x = y
  proof: Subtype.ext funext h

中文:
定理 ext
  条件: {x y : AdicCauchySequence I M} (h : 对任意 n, x n = y n)
  结论: x = y
  证明: Subtype.ext funext h

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem ext {x y : AdicCauchySequence I M} (h : forall n, x n = y n) : x = y :=
Subtype.ext funext h

/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: {m n : Nat} (hmn : m <= n) (f : AdicCauchySequence I M)
  proof: (f.property hmn).symm

中文:
定理 mk_eq_mk
  条件: {m n : 自然数} (hmn : m <= n) (f : AdicCauchySequence I M)
  证明: (f.property hmn).symm

Depends on / 依赖: Submodule
-/
theorem mk_eq_mk {m n : Nat} (hmn : m <= n) (f : AdicCauchySequence I M) :
    Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f n) =
      Submodule.Quotient.mk (p := (I ^ m • ⊤ : Submodule R M)) (f m) :=
  (f.property hmn).symm

end AdicCauchySequence

/--
theorem `isAdicCauchy_iff` / 定理 `isAdicCauchy_iff`

English:
theorem isAdicCauchy_iff
  given: (f : Nat -> M)
  proof: by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

中文:
定理 isAdicCauchy_iff
  条件: (f : 自然数 -> M)
  证明: by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

Depends on / 依赖: Ideal.pow_le_pow_right, Nat.le_induction, Nat.le_succ, SModEq, SModEq.mono, le_induction, le_succ, pow_le_pow_right, smul_mono
-/
theorem isAdicCauchy_iff (f : Nat -> M) :
    IsAdicCauchy I M f ↔ forall n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)] := by
  constructor
  · intro h n
    exact h (Nat.le_succ n)
  · intro h m n hmn
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ n hmn ih =>
        trans
        · exact ih
        · refine SModEq.mono (smul_mono (Ideal.pow_le_pow_right hmn) (by rfl)) (h n)

/-- Construct `I`-adic Cauchy sequence from sequence satisfying the successive Cauchy condition. -/
@[simps]
/--
Definition of `AdicCauchySequence.mk` / `AdicCauchySequence.mk` 的定义

English:
definition AdicCauchySequence.mk
  signature: (f : Nat -> M)
  body: f
  property := by rwa [isAdicCauchy_iff]

中文:
定义 AdicCauchySequence.mk
  签名: (f : 自然数 -> M)
  定义体: f
  property := by rwa [isAdicCauchy_iff]
-/
def AdicCauchySequence.mk (f : Nat -> M)
    (h : forall n, f n ≡ f (n + 1) [SMOD (I ^ n • ⊤ : Submodule R M)]) : AdicCauchySequence I M where
  val := f
  property := by rwa [isAdicCauchy_iff]

/-- The canonical linear map from Cauchy sequences to the completion. -/
@[simps]
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : AdicCauchySequence I M ->ₗ[R] AdicCompletion I M where
  body: ⟨fun n => Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 mk
  签名: : AdicCauchySequence I M ->ₗ[R] AdicCompletion I M where
  定义体: ⟨fun n => Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: Submodule, Submodule.mkQ, f.property, map_add, map_smul, mkQ_apply, property
-/
def mk : AdicCauchySequence I M ->ₗ[R] AdicCompletion I M where
  toFun f := ⟨fun n => Submodule.mkQ (I ^ n • ⊤ : Submodule R M) (f n), by
    intro m n hmn
    simp only [mkQ_apply]
    exact (f.property hmn).symm⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/--
theorem `mk_zero_of` / 定理 `mk_zero_of`

English:
theorem mk_zero_of
  statement: (f : AdicCauchySequence I M)
  proof: by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by lia)
  rw [mk_apply_coe]; rw [Submodule.mkQ_apply]; rw [val_zero]; rw [← AdicCauchySequence.mk_eq_mk (show n <= m by lia)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hl

中文:
定理 mk_zero_of
  结论: (f : AdicCauchySequence I M)
  证明: by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by lia)
  rw [mk_apply_coe]; rw [Submodule.mkQ_apply]; rw [val_zero]; rw [← AdicCauchySequence.mk_eq_mk (show n <= m by lia)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hl

Depends on / 依赖: AdicCauchySequence, AdicCauchySequence.mk_eq_mk, Ideal.pow_le_pow_right, Submodule, Submodule.mkQ_apply, Submodule.smul_mono_left, mkQ_apply, mk_apply_coe, mk_eq_mk, pow_le_pow_right, smul_mono_left, val_zero
-/
theorem mk_zero_of (f : AdicCauchySequence I M)
    (h : exists k : Nat, forall n >= k, exists m >= n, exists l >= n, f m in (I ^ l • ⊤ : Submodule R M)) :
    AdicCompletion.mk I M f = 0 := by
  obtain ⟨k, h⟩ := h
  ext n
  obtain ⟨m, hnm, l, hnl, hl⟩ := h (n + k) (by lia)
  rw [mk_apply_coe]; rw [Submodule.mkQ_apply]; rw [val_zero]; rw [← AdicCauchySequence.mk_eq_mk (show n <= m by lia)]
  simpa using (Submodule.smul_mono_left (Ideal.pow_le_pow_right (by lia))) hl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mk_surjective` / 定理 `mk_surjective`

English:
theorem mk_surjective
  statement: Function.Surjective (mk I M)
  proof: by
  intro x
  choose a ha using fun n => Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def]; rw [ha m]; rw [← mkQ_apply]; rw [← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n)]; rw [mkQ_apply]; rw [ha n]; rw [x.property 

中文:
定理 mk_surjective
  结论: 函数.满射 (mk I M)
  证明: by
  intro x
  choose a ha using fun n => Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def]; rw [ha m]; rw [← mkQ_apply]; rw [← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n)]; rw [mkQ_apply]; rw [ha n]; rw [x.property 

Depends on / 依赖: Ideal.pow_le_pow_right, Quotient, SModEq, SModEq.def, Submodule, Submodule.Quotient.mk_surjective, Submodule.smul_mono_left, factor_mk, mkQ_apply, mk_surjective, pow_le_pow_right, property, smul_mono_left, x.property, x.val
-/
theorem mk_surjective : Function.Surjective (mk I M) := by
  intro x
  choose a ha using fun n => Submodule.Quotient.mk_surjective _ (x.val n)
  refine ⟨⟨a, ?_⟩, ?_⟩
  · intro m n hmn
    rw [SModEq.def]; rw [ha m]; rw [← mkQ_apply]; rw [← factor_mk (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn)) (a n)]; rw [mkQ_apply]; rw [ha n]; rw [x.property hmn]
  · ext n
    simp [ha n]

/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {p : AdicCompletion I M -> Prop} (x : AdicCompletion I M)
  proof: by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

中文:
定理 induction_on
  结论: {p : AdicCompletion I M -> 命题} (x : AdicCompletion I M)
  证明: by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

Depends on / 依赖: mk_surjective
-/
theorem induction_on {p : AdicCompletion I M -> Prop} (x : AdicCompletion I M)
    (h : forall (f : AdicCauchySequence I M), p (mk I M f)) : p x := by
  obtain ⟨f, rfl⟩ := mk_surjective I M x
  exact h f

variable {M}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  body: fun x => ⟨fun n => f n x, fun hkl => LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]

中文:
定义 lift
  签名: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  定义体: fun x => ⟨fun n => f n x, fun hkl => LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]

Depends on / 依赖: LinearMap, LinearMap.congr_fun, congr_fun
-/
def lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m) :
    M ->ₗ[R] AdicCompletion I N where
  toFun := fun x => ⟨fun n => f n x, fun hkl => LinearMap.congr_fun (h hkl) x⟩
  map_add' x y := by
    simp only [map_add]
    rfl
  map_smul' r x := by
    simp only [LinearMapClass.map_smul, RingHom.id_apply]
    rfl

@[simp]
/--
lemma `eval_lift` / 引理 `eval_lift`

English:
lemma eval_lift
  statement: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  proof: rfl

@[simp]

中文:
引理 eval_lift
  结论: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  证明: rfl

@[simp]
-/
lemma eval_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m)
    (n : Nat) : eval I N n ∘ₗ lift I f h = f n :=
  rfl

@[simp]
/--
lemma `eval_lift_apply` / 引理 `eval_lift_apply`

English:
lemma eval_lift_apply
  statement: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  proof: rfl

中文:
引理 eval_lift_apply
  结论: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  证明: rfl
-/
lemma eval_lift_apply (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), transitionMap I N hle ∘ₗ f n = f m)
    (n : Nat) (x : M) : (lift I f h x).val n = f n x :=
  rfl

section Bijective

variable {I}

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_injective_iff` / 定理 `of_injective_iff`

English:
theorem of_injective_iff
  statement: Function.Injective (of I M) ↔ IsHausdorff I M
  proof: by
  constructor
  · refine fun h => ⟨fun x hx => h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx => h.haus x fun n => ?_, fun hx => by simp [hx]⟩
    rw [Subtype.ext_

中文:
定理 of_injective_iff
  结论: 函数.单射 (of I M) ↔ 是豪斯多夫 I M
  证明: by
  constructor
  · refine fun h => ⟨fun x hx => h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx => h.haus x fun n => ?_, fun hx => by simp [hx]⟩
    rw [Subtype.ext_

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, LinearMap.mem_ker, SModEq, SModEq.zero, Submodule, Submodule.mem_bot, Subtype, Subtype.ext_iff, ext_iff, h.haus, ker_eq_bot, mem_bot, mem_ker
-/
theorem of_injective_iff : Function.Injective (of I M) ↔ IsHausdorff I M := by
  constructor
  · refine fun h => ⟨fun x hx => h ?_⟩
    ext n
    simpa [of, SModEq.zero] using hx n
  · intro h
    rw [← LinearMap.ker_eq_bot]
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    refine ⟨fun hx => h.haus x fun n => ?_, fun hx => by simp [hx]⟩
    rw [Subtype.ext_iff] at hx
    simpa [SModEq.zero] using congrFun hx n

variable (I M) in
/--
theorem `of_injective` / 定理 `of_injective`

English:
theorem of_injective
  given: [IsHausdorff I M]
  statement: Function.Injective (of I M)
  proof: of_injective_iff.mpr ‹_›

@[simp]

中文:
定理 of_injective
  条件: [是豪斯多夫 I M]
  结论: 函数.单射 (of I M)
  证明: of_injective_iff.mpr ‹_›

@[simp]

Depends on / 依赖: of_injective_iff, of_injective_iff.mpr
-/
theorem of_injective [IsHausdorff I M] : Function.Injective (of I M) :=
  of_injective_iff.mpr ‹_›

@[simp]
/--
theorem `of_inj` / 定理 `of_inj`

English:
theorem of_inj
  given: [IsHausdorff I M] {a b : M}
  statement: of I M a = of I M b ↔ a = b
  proof: (of_injective I M).eq_iff

中文:
定理 of_inj
  条件: [是豪斯多夫 I M] {a b : M}
  结论: of I M a = of I M b ↔ a = b
  证明: (of_injective I M).eq_iff

Depends on / 依赖: eq_iff, of_injective
-/
theorem of_inj [IsHausdorff I M] {a b : M} : of I M a = of I M b ↔ a = b :=
  (of_injective I M).eq_iff

set_option backward.isDefEq.respectTransparency false in
/--
theorem `of_surjective_iff` / 定理 `of_surjective_iff`

English:
theorem of_surjective_iff
  statement: Function.Surjective (of I M) ↔ IsPrecomplete I M
  proof: by
  constructor
  · refine fun h => ⟨fun f hmn => ?_⟩
    let u : AdicCompletion I M := ⟨fun n => Submodule.Quotient.mk (f n), fun c => (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n => ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x]; rw [← eval_of]; rw [hx]
    simp [u]
  · intro

中文:
定理 of_surjective_iff
  结论: 函数.满射 (of I M) ↔ 是Precomplete I M
  证明: by
  constructor
  · refine fun h => ⟨fun f hmn => ?_⟩
    let u : AdicCompletion I M := ⟨fun n => Submodule.Quotient.mk (f n), fun c => (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n => ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x]; rw [← eval_of]; rw [hx]
    simp [u]
  · intro

Depends on / 依赖: AdicCompletion, Quotient, SModEq, Submodule, Submodule.Quotient.mk, Submodule.Quotient.mk_surjective, eval_of, h.prec, mkQ_apply, mk_surjective
-/
theorem of_surjective_iff : Function.Surjective (of I M) ↔ IsPrecomplete I M := by
  constructor
  · refine fun h => ⟨fun f hmn => ?_⟩
    let u : AdicCompletion I M := ⟨fun n => Submodule.Quotient.mk (f n), fun c => (hmn c).symm⟩
    obtain ⟨x, hx⟩ := h u
    refine ⟨x, fun n => ?_⟩
    simp only [SModEq]
    rw [← mkQ_apply _ x]; rw [← eval_of]; rw [hx]
    simp [u]
  · intro h u
    choose x hx using (fun n => Submodule.Quotient.mk_surjective (I ^ n • ⊤ : Submodule R M) (u.1 n))
    obtain ⟨a, ha⟩ := h.prec (f := x) (fun hmn => by rw [SModEq, hx, ← u.2 hmn, ← hx]; simp)
    use a
    ext n
    simpa [SModEq, ← eval_of, ha, ← hx] using (ha n).symm

variable (I M) in
/--
theorem `of_surjective` / 定理 `of_surjective`

English:
theorem of_surjective
  given: [IsPrecomplete I M]
  statement: Function.Surjective (of I M)
  proof: of_surjective_iff.mpr ‹_›

中文:
定理 of_surjective
  条件: [是Precomplete I M]
  结论: 函数.满射 (of I M)
  证明: of_surjective_iff.mpr ‹_›

Depends on / 依赖: of_surjective_iff, of_surjective_iff.mpr
-/
theorem of_surjective [IsPrecomplete I M] : Function.Surjective (of I M) :=
  of_surjective_iff.mpr ‹_›

/--
theorem `of_bijective_iff` / 定理 `of_bijective_iff`

English:
theorem of_bijective_iff
  statement: Function.Bijective (of I M) ↔ IsAdicComplete I M
  proof: ⟨fun h =>
    { toIsHausdorff := of_injective_iff.mp h.1,
      toIsPrecomplete := of_surjective_iff.mp h.2 },
   fun h => ⟨of_injective_iff.mpr h.1, of_surjective_iff.mpr h.2⟩⟩

中文:
定理 of_bijective_iff
  结论: 函数.双射 (of I M) ↔ 是AdicComplete I M
  证明: ⟨fun h =>
    { toIsHausdorff := of_injective_iff.mp h.1,
      toIsPrecomplete := of_surjective_iff.mp h.2 },
   fun h => ⟨of_injective_iff.mpr h.1, of_surjective_iff.mpr h.2⟩⟩

Depends on / 依赖: of_injective_iff, of_injective_iff.mp, of_injective_iff.mpr, of_surjective_iff, of_surjective_iff.mp, of_surjective_iff.mpr, toIsHausdorff, toIsPrecomplete
-/
theorem of_bijective_iff : Function.Bijective (of I M) ↔ IsAdicComplete I M :=
  ⟨fun h =>
    { toIsHausdorff := of_injective_iff.mp h.1,
      toIsPrecomplete := of_surjective_iff.mp h.2 },
   fun h => ⟨of_injective_iff.mpr h.1, of_surjective_iff.mpr h.2⟩⟩

variable (I M)

variable [IsAdicComplete I M]

/--
theorem `of_bijective` / 定理 `of_bijective`

English:
theorem of_bijective
  statement: Function.Bijective (of I M)
  proof: of_bijective_iff.mpr ‹_›

中文:
定理 of_bijective
  结论: 函数.双射 (of I M)
  证明: of_bijective_iff.mpr ‹_›

Depends on / 依赖: of_bijective_iff, of_bijective_iff.mpr
-/
theorem of_bijective : Function.Bijective (of I M) :=
  of_bijective_iff.mpr ‹_›

/--
When `M` is `I`-adic complete, the canonical map from `M` to its `I`-adic completion is a linear
equivalence.
-/
@[simps! apply]
/--
Definition of `ofLinearEquiv` / `ofLinearEquiv` 的定义

English:
definition ofLinearEquiv
  signature: : M ≃ₗ[R] AdicCompletion I M
  body: LinearEquiv.ofBijective (of I M) (of_bijective I M)

中文:
定义 ofLinearEquiv
  签名: : M ≃ₗ[R] AdicCompletion I M
  定义体: LinearEquiv.ofBijective (of I M) (of_bijective I M)

Depends on / 依赖: LinearEquiv, LinearEquiv.ofBijective, ofBijective, of_bijective
-/
def ofLinearEquiv : M ≃ₗ[R] AdicCompletion I M :=
  LinearEquiv.ofBijective (of I M) (of_bijective I M)

variable {M}

@[simp]
/--
theorem `ofLinearEquiv_symm_of` / 定理 `ofLinearEquiv_symm_of`

English:
theorem ofLinearEquiv_symm_of
  given: (x : M)
  statement: (ofLinearEquiv I M).symm (of I M x) = x
  proof: by
  simp [ofLinearEquiv]

@[simp]

中文:
定理 ofLinearEquiv_symm_of
  条件: (x : M)
  结论: (ofLinearEquiv I M).symm (of I M x) = x
  证明: by
  simp [ofLinearEquiv]

@[simp]

Depends on / 依赖: ofLinearEquiv
-/
theorem ofLinearEquiv_symm_of (x : M) : (ofLinearEquiv I M).symm (of I M x) = x := by
  simp [ofLinearEquiv]

@[simp]
/--
theorem `of_ofLinearEquiv_symm` / 定理 `of_ofLinearEquiv_symm`

English:
theorem of_ofLinearEquiv_symm
  given: (x : AdicCompletion I M)
  proof: by
  simp [ofLinearEquiv]

中文:
定理 of_ofLinearEquiv_symm
  条件: (x : AdicCompletion I M)
  证明: by
  simp [ofLinearEquiv]

Depends on / 依赖: ofLinearEquiv
-/
theorem of_ofLinearEquiv_symm (x : AdicCompletion I M) :
    of I M ((ofLinearEquiv I M).symm x) = x := by
  simp [ofLinearEquiv]

end Bijective

set_option backward.isDefEq.respectTransparency false in
/--
theorem `pow_smul_top_le_ker_eval` / 定理 `pow_smul_top_le_ker_eval`

English:
theorem pow_smul_top_le_ker_eval
  given: (n : Nat)
  statement: I ^ n • ⊤ <= (eval I M n).ker
  proof: by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n)]; rw [← Quotient.mk_smul]; rw [Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

中文:
定理 pow_smul_top_le_ker_eval
  条件: (n : 自然数)
  结论: I ^ n • ⊤ <= (eval I M n).ker
  证明: by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n)]; rw [← Quotient.mk_smul]; rw [Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Quotient, Quotient.mk_eq_zero, Quotient.mk_smul, Submodule, Submodule.Quotient.mk_out, coe_eval, forall_const, map_smul, mem_ker, mem_top, mk_eq_zero, mk_out, mk_smul, r_in, smul_le, smul_mem_smul, x.val
-/
theorem pow_smul_top_le_ker_eval (n : Nat) : I ^ n • ⊤ <= (eval I M n).ker := by
  simp only [smul_le, mem_top, LinearMap.mem_ker, map_smul, coe_eval, forall_const]
  intro r r_in x
  rw [← Submodule.Quotient.mk_out (x.val n)]; rw [← Quotient.mk_smul]; rw [Quotient.mk_eq_zero]
  exact smul_mem_smul r_in mem_top

set_option backward.isDefEq.respectTransparency false in
/--
lemma `val_apply_mem_smul_top_iff` / 引理 `val_apply_mem_smul_top_iff`

English:
lemma val_apply_mem_smul_top_iff
  statement: {m n : Nat} {x : AdicCompletion I M}
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← x.prop m_ge, transitionMap, Submodule.factorPow, Submodule.factor, mapQ,
      ← LinearMap.mem_ker]
    simpa [ker_liftQ]
  simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge

中文:
引理 val_apply_mem_smul_top_iff
  结论: {m n : 自然数} {x : AdicCompletion I M}
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← x.prop m_ge, transitionMap, Submodule.factorPow, Submodule.factor, mapQ,
      ← LinearMap.mem_ker]
    simpa [ker_liftQ]
  simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge

Depends on / 依赖: LinearMap, LinearMap.mem_ker, Submodule, Submodule.factor, Submodule.factorPow, factor, factorPow, ker_liftQ, m_ge, mem_ker, transitionMap, x.prop
-/
lemma val_apply_mem_smul_top_iff {m n : Nat} {x : AdicCompletion I M}
    (m_ge : n <= m) : x.val m in I ^ n • (⊤ : Submodule R (M ⧸ I ^ m • ⊤)) ↔ x.val n = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← x.prop m_ge, transitionMap, Submodule.factorPow, Submodule.factor, mapQ,
      ← LinearMap.mem_ker]
    simpa [ker_liftQ]
  simpa [mapQ, h, ← LinearMap.mem_ker, ker_liftQ] using x.prop m_ge

end AdicCompletion

namespace IsAdicComplete

open AdicCompletion

/--
theorem `map_algebraMap_iff` / 定理 `map_algebraMap_iff`

English:
theorem map_algebraMap_iff
  statement: [CommRing S] [Module S M] [Algebra R S]
  proof: by
  simp [isAdicComplete_iff, IsPrecomplete.map_algebraMap_iff, IsHausdorff.map_algebraMap_iff]

中文:
定理 map_algebraMap_iff
  结论: [交换环 S] [模 S M] [代数 R S]
  证明: by
  simp [isAdicComplete_iff, IsPrecomplete.map_algebraMap_iff, IsHausdorff.map_algebraMap_iff]

Depends on / 依赖: IsHausdorff, IsHausdorff.map_algebraMap_iff, IsPrecomplete, IsPrecomplete.map_algebraMap_iff, isAdicComplete_iff, map_algebraMap_iff
-/
theorem map_algebraMap_iff [CommRing S] [Module S M] [Algebra R S]
    [IsScalarTower R S M] : IsAdicComplete (I.map (algebraMap R S)) M ↔ IsAdicComplete I M := by
  simp [isAdicComplete_iff, IsPrecomplete.map_algebraMap_iff, IsHausdorff.map_algebraMap_iff]

section lift

variable [IsAdicComplete I N]

variable {M}

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  body: (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]

中文:
定义 lift
  签名: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  定义体: (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]

Depends on / 依赖: AdicCompletion, AdicCompletion.lift, ofLinearEquiv
-/
def lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) :
    M ->ₗ[R] N := (ofLinearEquiv I N).symm ∘ₗ AdicCompletion.lift I f h

@[simp]
/--
theorem `of_lift` / 定理 `of_lift`

English:
theorem of_lift
  statement: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  proof: by
  simp [lift]

@[simp]

中文:
定理 of_lift
  结论: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  证明: by
  simp [lift]

@[simp]
-/
theorem of_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (x : M) :
    of I N (lift I f h x) = AdicCompletion.lift I f h x := by
  simp [lift]

@[simp]
/--
theorem `of_comp_lift` / 定理 `of_comp_lift`

English:
theorem of_comp_lift
  statement: (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
  proof: by
  ext1; simp

中文:
定理 of_comp_lift
  结论: (f : 对任意 (n : 自然数), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : 子模 R N))
  证明: by
  ext1; simp
-/
theorem of_comp_lift (f : forall (n : Nat), M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N))
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) :
    of I N ∘ₗ lift I f h = AdicCompletion.lift I f h := by
  ext1; simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N → N ⧸ (I ^ n • ⊤)` is `f n` .
-/
@[simp]
/--
theorem `mk_lift` / 定理 `mk_lift`

English:
theorem mk_lift
  statement: {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  proof: by
  simp only [lift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp

中文:
定理 mk_lift
  结论: {f : (n : 自然数) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  证明: by
  simp only [lift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, comp_apply, eval_of, mkQ_apply
-/
theorem mk_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n : Nat) (x : M) :
    Submodule.Quotient.mk (lift I f h x) = f n x := by
  simp only [lift, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp

/--
The composition of lift linear map `lift I f h : M →ₗ[R] N` with the canonical
projection `N →ₗ[R] N ⧸ (I ^ n • ⊤)` is `f n`.
-/
@[simp]
/--
theorem `mkQ_comp_lift` / 定理 `mkQ_comp_lift`

English:
theorem mkQ_comp_lift
  statement: {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  proof: by
  ext; simp

中文:
定理 mkQ_comp_lift
  结论: {f : (n : 自然数) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  证明: by
  ext; simp
-/
theorem mkQ_comp_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) (n : Nat) :
    mkQ (I ^ n • ⊤ : Submodule R N) ∘ₗ lift I f h = f n := by
  ext; simp

/--
theorem `eq_lift` / 定理 `eq_lift`

English:
theorem eq_lift
  statement: {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  proof: by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n m
  simp [← hF n]

中文:
定理 eq_lift
  结论: {f : (n : 自然数) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
  证明: by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n m
  simp [← hF n]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, IsHausdorff, IsHausdorff.funext, coe_injective
-/
theorem eq_lift {f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ n • ⊤)}
    (h : forall {m n : Nat} (hle : m <= n), factorPow I N hle ∘ₗ f n = f m) {F : M ->ₗ[R] N}
    (hF : forall n, mkQ _ ∘ₗ F = f n) : F = lift I f h := by
  apply DFunLike.coe_injective
  apply IsHausdorff.funext I
  intro n m
  simp [← hF n]

end lift

namespace StrictMono

variable {a : Nat -> Nat} (ha : StrictMono a)
    (f : (n : Nat) -> M ->ₗ[R] N ⧸ (I ^ (a n) • ⊤ : Submodule R N))

variable {I M}
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (n : Nat)
  body: factorPow I N (ha.id_le n) ∘ₗ f n

中文:
定义 extend
  签名: (n : 自然数)
  定义体: factorPow I N (ha.id_le n) ∘ₗ f n

Depends on / 依赖: factorPow, ha.id_le, id_le
-/
def extend (n : Nat) :
    M ->ₗ[R] N ⧸ (I ^ n • ⊤ : Submodule R N) :=
  factorPow I N (ha.id_le n) ∘ₗ f n

variable (hf : forall {m}, factorPow I N (ha.monotone m.le_succ) ∘ₗ (f (m + 1)) = f m)

include hf in
/--
theorem `factorPow_comp_eq_of_factorPow_comp_succ_eq` / 定理 `factorPow_comp_eq_of_factorPow_comp_succ_eq`

English:
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
  proof: by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in

中文:
定理 factorPow_comp_eq_of_factorPow_comp_succ_eq
  证明: by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in

Depends on / 依赖: Ideal.pow_le_pow_right, LinearMap, LinearMap.ext_iff, Submodule, Submodule.eq_factor_of_eq_factor_succ, eq_factor_of_eq_factor_succ, ext_iff, ha.monotone, monotone, pow_le_pow_right, smul_mono_left
-/
theorem factorPow_comp_eq_of_factorPow_comp_succ_eq
    {m n : Nat} (hle : m <= n) : factorPow I N (ha.monotone hle) ∘ₗ f n = f m := by
  ext x
  symm
  refine Submodule.eq_factor_of_eq_factor_succ ?_ (fun n => f n x) ?_ hle
  · exact fun _ _ le => smul_mono_left (Ideal.pow_le_pow_right (ha.monotone le))
  · intro s
    simp only [LinearMap.ext_iff] at hf
    simpa using (hf x).symm

include hf in
/--
theorem `extend_eq` / 定理 `extend_eq`

English:
theorem extend_eq
  given: (n : Nat)
  statement: extend ha f (a n) = f n
  proof: factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in

中文:
定理 extend_eq
  条件: (n : 自然数)
  结论: extend ha f (a n) = f n
  证明: factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in

Depends on / 依赖: factorPow_comp_eq_of_factorPow_comp_succ_eq, ha.id_le, id_le
-/
theorem extend_eq (n : Nat) : extend ha f (a n) = f n :=
  factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf (ha.id_le n)

include hf in
/--
theorem `factorPow_comp_extend` / 定理 `factorPow_comp_extend`

English:
theorem factorPow_comp_extend
  given: {m n : Nat} (hle : m <= n)
  proof: by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

中文:
定理 factorPow_comp_extend
  条件: {m n : 自然数} (hle : m <= n)
  证明: by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

Depends on / 依赖: extend, factorPow_comp_eq_of_factorPow_comp_succ_eq
-/
theorem factorPow_comp_extend {m n : Nat} (hle : m <= n) :
    factorPow I N hle ∘ₗ extend ha f n = extend ha f m := by
  ext
  simp [extend, ← factorPow_comp_eq_of_factorPow_comp_succ_eq ha f hf hle]

variable [IsAdicComplete I N]

variable (I)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : M ->ₗ[R] N
  body: IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

中文:
定义 lift
  签名: : M ->ₗ[R] N
  定义体: IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

Depends on / 依赖: IsAdicComplete, IsAdicComplete.lift, extend, factorPow_comp_extend
-/
def lift : M ->ₗ[R] N :=
  IsAdicComplete.lift I (extend ha f) (factorPow_comp_extend ha f hf)

/--
theorem `of_lift` / 定理 `of_lift`

English:
theorem of_lift
  given: (x : M)
  proof: IsAdicComplete.of_lift I (extend ha f) (factorPow_comp_extend ha f hf) x

中文:
定理 of_lift
  条件: (x : M)
  证明: IsAdicComplete.of_lift I (extend ha f) (factorPow_comp_extend ha f hf) x

Depends on / 依赖: IsAdicComplete, IsAdicComplete.of_lift, extend, factorPow_comp_extend, of_lift
-/
theorem of_lift (x : M) :
    of I N (lift I ha f hf x) =
    AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) x :=
  IsAdicComplete.of_lift I (extend ha f) (factorPow_comp_extend ha f hf) x

/--
theorem `of_comp_lift` / 定理 `of_comp_lift`

English:
theorem of_comp_lift
  proof: IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]

中文:
定理 of_comp_lift
  证明: IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]

Depends on / 依赖: IsAdicComplete, IsAdicComplete.of_comp_lift, extend, factorPow_comp_extend, of_comp_lift
-/
theorem of_comp_lift :
    of I N ∘ₗ lift I ha f hf =
      AdicCompletion.lift I (extend ha f) (factorPow_comp_extend ha f hf) :=
  IsAdicComplete.of_comp_lift I (extend ha f) (factorPow_comp_extend ha f hf)

@[simp]
/--
theorem `mk_lift` / 定理 `mk_lift`

English:
theorem mk_lift
  given: {n : Nat} (x : M)
  proof: by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp [extend_eq ha f hf]

@[simp]

中文:
定理 mk_lift
  条件: {n : 自然数} (x : M)
  证明: by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp [extend_eq ha f hf]

@[simp]

Depends on / 依赖: Function, Function.comp_apply, IsAdicComplete, IsAdicComplete.lift, LinearEquiv, LinearEquiv.coe_coe, LinearMap, LinearMap.coe_comp, coe_coe, coe_comp, comp_apply, eval_of, extend_eq, mkQ_apply, ofLinearEquiv
-/
theorem mk_lift {n : Nat} (x : M) :
    (Submodule.Quotient.mk (lift I ha f hf x)) = f n x := by
  simp only [lift, IsAdicComplete.lift, ofLinearEquiv, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply]
  rw [← mkQ_apply]; rw [← eval_of]
  simp [extend_eq ha f hf]

@[simp]
/--
theorem `mkQ_comp_lift` / 定理 `mkQ_comp_lift`

English:
theorem mkQ_comp_lift
  given: {n : Nat}
  proof: by
  ext; simp

中文:
定理 mkQ_comp_lift
  条件: {n : 自然数}
  证明: by
  ext; simp
-/
theorem mkQ_comp_lift {n : Nat} :
    mkQ (I ^ (a n) • ⊤ : Submodule R N) ∘ₗ (lift I ha f hf) = f n := by
  ext; simp

/--
theorem `eq_lift` / 定理 `eq_lift`

English:
theorem eq_lift
  statement: {F : M ->ₗ[R] N}
  proof: by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n m
  simp [← hF n]

中文:
定理 eq_lift
  结论: {F : M ->ₗ[R] N}
  证明: by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n m
  simp [← hF n]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, IsHausdorff, IsHausdorff.StrictMono.funext, StrictMono, coe_injective
-/
theorem eq_lift {F : M ->ₗ[R] N}
    (hF : forall n, mkQ _ ∘ₗ F = f n) : F = lift I ha f hf := by
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext I ha
  intro n m
  simp [← hF n]

end StrictMono

/--
Instance `bot` / 实例 `bot`

English:
instance bot
  signature: : IsAdicComplete (⊥ : Ideal R) M where

中文:
实例 bot
  签名: : 是AdicComplete (⊥ : 理想 R) M where

Depends on / 依赖: subsingleton
-/
instance bot : IsAdicComplete (⊥ : Ideal R) M where

/--
theorem `subsingleton` / 定理 `subsingleton`

English:
theorem subsingleton
  given: (h : IsAdicComplete (⊤ : Ideal R) M)
  statement: Subsingleton M
  proof: h.1.subsingleton

中文:
定理 subsingleton
  条件: (h : 是AdicComplete (⊤ : 理想 R) M)
  结论: 子单例 M
  证明: h.1.subsingleton
-/
protected theorem subsingleton (h : IsAdicComplete (⊤ : Ideal R) M) : Subsingleton M :=
  h.1.subsingleton

instance (priority := 100) of_subsingleton [Subsingleton M] : IsAdicComplete I M where

open Finset

/--
theorem `le_jacobson_bot` / 定理 `le_jacobson_bot`

English:
theorem le_jacobson_bot
  given: [IsAdicComplete I R]
  statement: I <= (⊥ : Ideal R).jacobson
  proof: by
  intro x hx
  rw [← Ideal.neg_mem_iff]; rw [Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : Nat -> R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : forall m n, m <= n -> f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, smul_eq_mul, Ideal.mul_t

中文:
定理 le_jacobson_bot
  条件: [是AdicComplete I R]
  结论: I <= (⊥ : 理想 R).jacobson
  证明: by
  intro x hx
  rw [← Ideal.neg_mem_iff]; rw [Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : Nat -> R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : forall m n, m <= n -> f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, smul_eq_mul, Ideal.mul_t

Depends on / 依赖: Finset, Finset.sum_range_add, Ideal.mem_jacobson_bot, Ideal.mul_top, Ideal.neg_mem_iff, SModEq, SModEq.sub_mem, Submodule, Submodule.sum_mem, add_comm, add_tsub_cancel_of_le, mem_jacobson_bot, mul_assoc, mul_pow, mul_top, neg_mem_iff, pow_add, smul_eq_mul, sub_mem, sub_self
-/
theorem le_jacobson_bot [IsAdicComplete I R] : I <= (⊥ : Ideal R).jacobson := by
  intro x hx
  rw [← Ideal.neg_mem_iff]; rw [Ideal.mem_jacobson_bot]
  intro y
  rw [add_comm]
  let f : Nat -> R := fun n => ∑ i in range n, (x * y) ^ i
  have hf : forall m n, m <= n -> f m ≡ f n [SMOD I ^ m • (⊤ : Submodule R R)] := by
    intro m n h
    simp only [f, smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    rw [← add_tsub_cancel_of_le h]; rw [Finset.sum_range_add]; rw [← sub_sub]; rw [sub_self]; rw [zero_sub]; rw [@neg_mem_iff]
    apply Submodule.sum_mem
    intro n _
    rw [mul_pow]; rw [pow_add]; rw [mul_assoc]
    exact Ideal.mul_mem_right _ (I ^ m) (Ideal.pow_mem_pow hx m)
  obtain ⟨L, hL⟩ := IsPrecomplete.prec toIsPrecomplete @hf
  rw [isUnit_iff_exists_inv]
  use L
  rw [← sub_eq_zero]; rw [neg_mul]
  apply IsHausdorff.haus (toIsHausdorff : IsHausdorff I R)
  intro n
  specialize hL n
  rw [SModEq.sub_mem]; rw [smul_eq_mul]; rw [Ideal.mul_top] at hL ⊢
  rw [sub_zero]
  suffices (1 - x * y) * f n - 1 in I ^ n by
    convert! Ideal.sub_mem _ this (Ideal.mul_mem_left _ (1 + -(x * y)) hL) using 1
    ring
  cases n
  · simp only [Ideal.one_eq_top, pow_zero, mem_top]
  · rw [← neg_sub _ (1 : R), neg_mul, mul_geom_sum, neg_sub, sub_sub, add_comm (_ ^ _), ← sub_sub,
      sub_self, zero_sub, @neg_mem_iff, mul_pow]
    exact Ideal.mul_mem_right _ (I ^ _) (Ideal.pow_mem_pow hx _)

end IsAdicComplete
