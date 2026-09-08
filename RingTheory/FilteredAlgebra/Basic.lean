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

/-- For a family of subsets `σ` of `A`, an increasing series of `F` in `σ` is a filtration if
there is another series `F_lt` in `σ` equal to the supremum of `F` with smaller index.

In the intended applications, `σ` is a complete lattice, and `F_lt` is uniquely-determined as
`F_lt j = ⨆ i < j, F i`. Thus `F_lt` is an implementation detail which allows us defer depending
on a complete lattice structure on `σ`. It also provides the ancillary benefit of giving us better
definition control. This is convenient e.g., when the index is `ℤ`. -/
/-
**IsFiltration** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} → {σ : Type u_3} → [Preorder ι] → [Preorder σ] → (ι → σ) → 
outParam (ι → σ) → Prop
参数：ι → σ；ι → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a family of subsets `σ` of `A`, an increasing series of `F` in `σ` is a filt
ration if
there is another series `F_lt` in `σ` equal to the supremum of `F` with smaller 
index.

In the intended applications, `σ` is a complete lattice, and `F_lt` is uniquely-
determined as
`F_lt j = ⨆ i < j, F i`. Thus `F_lt` is an implementation detail which allows us
 defer depending
on a complete lattice structure on `σ`. It also provides the ancillary benefit o
f giving us better
definition control. This is convenient e.g., when the index is `ℤ`.
-/
class IsFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) : Prop where
  mono : Monotone F
  is_le {i j} : i < j → F i ≤ F_lt j
  is_sup (B : σ) (j : ι) : (∀ i < j, F i ≤ B) → F_lt j ≤ B
/-
**IsFiltration.F_lt_le_F** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsFiltration.F_lt_le_F (F : ι -> σ) (F_lt : outParam <| ι -> σ) (i : ι) [I
sFiltration F F_lt] : F_lt i <= F i
参数：F : ι -> σ；F_lt : outParam <| ι -> σ；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFiltration.is_sup`：∀ {ι : Type u_1} {σ : Type u_3} {inst : Preorder ι}
 {inst_1 : Preorder σ} {F : ι → σ} {F_lt : outParam (ι → σ)}   [self : IsFiltrat
ion F F_l…
· 使用定理 `IsFiltration.mono`：∀ {ι : Type u_1} {σ : Type u_3} {inst : Preorder ι} {
inst_1 : Preorder σ} {F : ι → σ} {F_lt : outParam (ι → σ)}   [self : IsFiltratio
n F F_l…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma IsFiltration.F_lt_le_F (F : ι → σ) (F_lt : outParam <| ι → σ) (i : ι) [IsFiltration F F_lt] :
    F_lt i ≤ F i :=
  is_sup (F i) i (fun _ hi ↦ IsFiltration.mono (le_of_lt hi))

/-- A convenience constructor for `IsFiltration` when the index is the integers. -/
/-
**IsFiltration.mk_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsFiltration.mk_int (F : Int -> σ) (mono : Monotone F) : IsFiltration F (f
un n => F (n - 1)) where mono
参数：F : Int -> σ；mono : Monotone F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.le_sub_one_of_lt`：∀ {a b : ℤ}, a < b → a ≤ b - 1
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
A convenience constructor for `IsFiltration` when the index is the integers.
-/
lemma IsFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) :
    IsFiltration F (fun n ↦ F (n - 1)) where
  mono := mono
  is_le lt := mono (Int.le_sub_one_of_lt lt)
  is_sup _ j hi := hi (j - 1) (sub_one_lt j)

end GeneralFiltration

section FilteredRing

variable {ι R σ : Type*} [AddMonoid ι] [PartialOrder ι] [Preorder σ]
  [Semiring R] [SetLike σ R]

/-- For a family of subsets `σ` of semiring `R`, an increasing series `F` in `σ` is
a ring filtration if `IsFiltration F F_lt` and the pointwise multiplication of `F i` and `F j`
is in `F (i + j)`. -/
/-
**IsRingFiltration** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {σ : Type u_3} →       [AddMonoid 
ι] → [PartialOrder ι] → [Preorder σ] → [Semiring R] → [SetLike σ R] → (ι → σ) → 
outParam (ι → σ) → Prop
参数：ι → σ；ι → σ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a family of subsets `σ` of semiring `R`, an increasing series `F` in `σ` is
a ring filtration if `IsFiltration F F_lt` and the pointwise multiplication of `
F i` and `F j`
is in `F (i + j)`.
-/
class IsRingFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) : Prop
    extends IsFiltration F F_lt, SetLike.GradedMonoid F

/-- A convenience constructor for `IsRingFiltration` when the index is the integers. -/
/-
**IsRingFiltration.mk_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsRingFiltration.mk_int (F : Int -> σ) (mono : Monotone F) [SetLike.Graded
Monoid F] : IsRingFiltration F (fun n => F (n - 1)) where __
参数：F : Int -> σ；mono : Monotone F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsFiltration.mk_int`：IsFiltration.mk_int (F : Int -> σ) (mono : Monotone
 F) : IsFiltration F (fun n => F (n - 1)) where mono

--- 原说明 ---
A convenience constructor for `IsRingFiltration` when the index is the integers.
-/
lemma IsRingFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) [SetLike.GradedMonoid F] :
    IsRingFiltration F (fun n ↦ F (n - 1)) where
  __ := IsFiltration.mk_int F mono

end FilteredRing

section FilteredModule

variable {ι ιM R M σ σM : Type*} [AddMonoid ι] [PartialOrder ι] [PartialOrder ιM] [VAdd ι ιM]
variable [Preorder σ] [Semiring R] [SetLike σ R]
variable [Preorder σM] [AddCommMonoid M] [Module R M] [SetLike σM M]

/-- For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM` a family of subsets of
an `R`-module `M`, an increasing series `FM` in `σM` is a module filtration if `IsFiltration F F_lt`
and the pointwise scalar multiplication of `F i` and `FM j` is in `F (i +ᵥ j)`.

The index set `ιM` for the module can be more general, however usually we take `ιM = ι`. -/
/-
**IsModuleFiltration** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {ιM : Type u_2} →     {R : Type u_3} →       {M : Type 
u_4} →         {σ : Type u_5} →           {σM : Type u_6} →             [inst : 
AddMonoid ι] →               [inst_1 : PartialOrder ι] →                 [Partia
lOrder ιM] →                   [VAdd ι ιM] →                     [inst_4 : Preor
der σ] →                       [inst_5 : Semiring R] →                         [
inst_6 : SetLike σ R] →                           [Preorder σM] →               
              [inst_8 : AddCommMonoid M] →                               [_root_
.Module R M] →                                 [SetLike σM M] →                 
                  (F : ι → σ) →                                     (F_lt : outP
aram (ι → σ)) →                                       [IsRingFiltration F F_lt] 
→ (ιM → σM) → outParam (ιM → σM) → Prop
参数：F : ι → σ；F_lt : outParam (ι → σ)；ιM → σM；ιM → σM。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `F` satisfying `IsRingFiltration F F_lt` in a semiring `R` and `σM` a family
 of subsets of
an `R`-module `M`, an increasing series `FM` in `σM` is a module filtration if `
IsFiltration F F_lt`
and the pointwise scalar multiplication of `F i` and `FM j` is in `F (i +ᵥ j)`.

The index set `ιM` for the module can be more general, however usually we take `
ιM = ι`.
-/
class IsModuleFiltration (F : ι → σ) (F_lt : outParam <| ι → σ) [IsRingFiltration F F_lt]
    (F' : ιM → σM) (F'_lt : outParam <| ιM → σM) : Prop
    extends IsFiltration F' F'_lt, SetLike.GradedSMul F F'

/-- A convenience constructor for `IsModuleFiltration` when the index is the integers. -/
/-
**IsModuleFiltration.mk_int** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsModuleFiltration.mk_int (F : Int -> σ) (mono : Monotone F) [SetLike.Grad
edMonoid F] (F' : Int -> σM) (mono' : Monotone F') [SetLike.GradedSMul F F'] : l
etI
参数：F : Int -> σ；mono : Monotone F；F' : Int -> σM；mono' : Monotone F'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsFiltration.mk_int`：IsFiltration.mk_int (F : Int -> σ) (mono : Monotone
 F) : IsFiltration F (fun n => F (n - 1)) where mono
· 使用引理 `IsRingFiltration.mk_int`：IsRingFiltration.mk_int (F : Int -> σ) (mono : 
Monotone F) [SetLike.GradedMonoid F] : IsRingFiltration F (fun n => F (n - 1)) w
here __

--- 原说明 ---
A convenience constructor for `IsModuleFiltration` when the index is the integer
s.
-/
lemma IsModuleFiltration.mk_int (F : ℤ → σ) (mono : Monotone F) [SetLike.GradedMonoid F]
    (F' : ℤ → σM) (mono' : Monotone F') [SetLike.GradedSMul F F'] :
    letI := IsRingFiltration.mk_int F mono
    IsModuleFiltration F (fun n ↦ F (n - 1)) F' (fun n ↦ F' (n - 1)) :=
  letI := IsRingFiltration.mk_int F mono
  { IsFiltration.mk_int F' mono' with }

end FilteredModule

