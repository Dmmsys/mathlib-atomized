/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.GradedMonoid
public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Ring.Int.Defs
/-!
# The filtration on abelian groups and rings

In this file, we define the concept of filtration for abelian groups, rings, and modules.

## Main definitions

* `IsFiltration` : For a family of subsets `σ` of `A`, an increasing series of `F` in `σ` is a
  filtration if there is another series `F_lt` in `σ` equal to the
  supremum of `F` with smaller index.

* `IsRingFiltration` : For a family of subsets `σ` of semiring `R`, an increasing series `F` in `σ`
  is a ring filtration if `IsFiltration F F_lt` and the pointwise multiplication of `F i` and `F j`
  is in `F (i + j)`.

* `IsModuleFiltration` : For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM` a
  family of subsets of an `R`-module `M`, an increasing series `FM` in `σM` is a module filtration
  if `IsFiltration F F_lt` and the pointwise scalar multiplication of `F i` and `FM j`
  is in `F (i +ᵥ j)`.

-/

public section

section GeneralFiltration

variable {ι A σ : Type*} [Preorder ι] [Preorder σ] [SetLike σ A]

/--
Definition of `IsFiltration` / `IsFiltration` 的定义

English:
class IsFiltration
  parameters: (F : ι -> σ) (F_lt : outParam <| ι -> σ)
  axioms and operations (3):
    - mono : Monotone F
    - is_le({i j}) : i < j -> F i <= F_lt j
    - is_sup((B : σ) (j : ι)) : (forall i < j, F i <= B) -> F_lt j <= B

中文:
类 是滤子
  参数: (F : ι -> σ) (F_lt : outParam <| ι -> σ)
  公理与运算 (3 个):
    - mono : 递增 F
    - is_le({i j}) : i < j -> F i <= F_lt j
    - is_sup((B : σ) (j : ι)) : (对任意 i < j, F i <= B) -> F_lt j <= B
-/
class IsFiltration (F : ι -> σ) (F_lt : outParam <| ι -> σ) : Prop where
  mono : Monotone F
  is_le {i j} : i < j -> F i <= F_lt j
  is_sup (B : σ) (j : ι) : (forall i < j, F i <= B) -> F_lt j <= B

/--
lemma `IsFiltration.F_lt_le_F` / 引理 `IsFiltration.F_lt_le_F`

English:
lemma IsFiltration.F_lt_le_F
  given: (F : ι -> σ) (F_lt : outParam <| ι -> σ) (i : ι) [IsFiltration F F_lt]
  proof: is_sup (F i) i (fun _ hi => IsFiltration.mono (le_of_lt hi))

中文:
引理 是滤子.F_lt_le_F
  条件: (F : ι -> σ) (F_lt : outParam <| ι -> σ) (i : ι) [是滤子 F F_lt]
  证明: is_sup (F i) i (fun _ hi => IsFiltration.mono (le_of_lt hi))

Depends on / 依赖: IsFiltration, IsFiltration.mono, is_sup, le_of_lt
-/
lemma IsFiltration.F_lt_le_F (F : ι -> σ) (F_lt : outParam <| ι -> σ) (i : ι) [IsFiltration F F_lt] :
    F_lt i <= F i :=
  is_sup (F i) i (fun _ hi => IsFiltration.mono (le_of_lt hi))

/--
lemma `IsFiltration.mk_int` / 引理 `IsFiltration.mk_int`

English:
lemma IsFiltration.mk_int
  given: (F : Int -> σ) (mono : Monotone F)
  proof: mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)

中文:
引理 是滤子.mk_int
  条件: (F : 整数 -> σ) (mono : 递增 F)
  证明: mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)
-/
lemma IsFiltration.mk_int (F : Int -> σ) (mono : Monotone F) :
    IsFiltration F (fun n => F (n - 1)) where
  mono := mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)

end GeneralFiltration

section FilteredRing

variable {ι R σ : Type*} [AddMonoid ι] [PartialOrder ι] [Preorder σ]
  [Semiring R] [SetLike σ R]

/--
Definition of `IsRingFiltration` / `IsRingFiltration` 的定义

English:
class IsRingFiltration
  parameters: (F : ι -> σ) (F_lt : outParam <| ι -> σ)
  extends: IsFiltration F F_lt, SetLike.GradedMonoid F
  (no additional axioms)

中文:
类 是RingFiltration
  参数: (F : ι -> σ) (F_lt : outParam <| ι -> σ)
  继承: 是滤子 F F_lt, 集合状.分次幺半群 F
  (无附加公理)
-/
class IsRingFiltration (F : ι -> σ) (F_lt : outParam <| ι -> σ) : Prop
    extends IsFiltration F F_lt, SetLike.GradedMonoid F

/--
lemma `IsRingFiltration.mk_int` / 引理 `IsRingFiltration.mk_int`

English:
lemma IsRingFiltration.mk_int
  given: (F : Int -> σ) (mono : Monotone F) [SetLike.GradedMonoid F]
  proof: IsFiltration.mk_int F mono

中文:
引理 是RingFiltration.mk_int
  条件: (F : 整数 -> σ) (mono : 递增 F) [集合状.分次幺半群 F]
  证明: IsFiltration.mk_int F mono

Depends on / 依赖: IsFiltration, IsFiltration.mk_int, mk_int
-/
lemma IsRingFiltration.mk_int (F : Int -> σ) (mono : Monotone F) [SetLike.GradedMonoid F] :
    IsRingFiltration F (fun n => F (n - 1)) where
  __ := IsFiltration.mk_int F mono

end FilteredRing

section FilteredModule

variable {ι ιM R M σ σM : Type*} [AddMonoid ι] [PartialOrder ι] [PartialOrder ιM] [VAdd ι ιM]
variable [Preorder σ] [Semiring R] [SetLike σ R]
variable [Preorder σM] [AddCommMonoid M] [Module R M] [SetLike σM M]

/--
Definition of `IsModuleFiltration` / `IsModuleFiltration` 的定义

English:
class IsModuleFiltration
  parameters: (F : ι -> σ) (F_lt : outParam <| ι -> σ) [IsRingFiltration F F_lt]
  extends: IsFiltration F' F'_lt, SetLike.GradedSMul F F'
  (no additional axioms)

中文:
类 是ModuleFiltration
  参数: (F : ι -> σ) (F_lt : outParam <| ι -> σ) [是RingFiltration F F_lt]
  继承: 是滤子 F' F'_lt, 集合状.分次标量乘法 F F'
  (无附加公理)
-/
class IsModuleFiltration (F : ι -> σ) (F_lt : outParam <| ι -> σ) [IsRingFiltration F F_lt]
    (F' : ιM -> σM) (F'_lt : outParam <| ιM -> σM) : Prop
    extends IsFiltration F' F'_lt, SetLike.GradedSMul F F'

/--
lemma `IsModuleFiltration.mk_int` / 引理 `IsModuleFiltration.mk_int`

English:
lemma IsModuleFiltration.mk_int
  statement: (F : Int -> σ) (mono : Monotone F) [SetLike.GradedMonoid F]
  proof: IsRingFiltration.mk_int F mono
    IsModuleFiltration F (fun n => F (n - 1)) F' (fun n => F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono
  { IsFiltration.mk_int F' mono' with }

中文:
引理 是ModuleFiltration.mk_int
  结论: (F : 整数 -> σ) (mono : 递增 F) [集合状.分次幺半群 F]
  证明: IsRingFiltration.mk_int F mono
    IsModuleFiltration F (fun n => F (n - 1)) F' (fun n => F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono
  { IsFiltration.mk_int F' mono' with }

Depends on / 依赖: IsRingFiltration, IsRingFiltration.mk_int, mk_int
-/
lemma IsModuleFiltration.mk_int (F : Int -> σ) (mono : Monotone F) [SetLike.GradedMonoid F]
    (F' : Int -> σM) (mono' : Monotone F') [SetLike.GradedSMul F F'] :
    letI := IsRingFiltration.mk_int F mono
    IsModuleFiltration F (fun n => F (n - 1)) F' (fun n => F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono
  { IsFiltration.mk_int F' mono' with }

end FilteredModule
