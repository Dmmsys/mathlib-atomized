/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Field.Canonical
public import Mathlib.Algebra.Order.Nonneg.Floor
public import Mathlib.Data.Real.Pointwise
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Group
public import Mathlib.Order.Lattice.Nat

/-!
# Basic results on nonnegative real numbers

This file contains all results on `NNReal` that do not directly follow from its basic structure.
As a consequence, it is a bit of a random collection of results, and is a good target for cleanup.

## Notation

This file uses `ℝ≥0` as a localized notation for `NNReal`.
-/

public section

assert_not_exists TrivialStar

open Function Set
open scoped BigOperators

namespace NNReal
variable {M : Type*} [Zero M]

/-
**NNReal.** 是 Mathlib 中的一个实例，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : FloorSemiring ℝ≥0 := inferInstanceAs <| FloorSemiring (Subtype _)

@[simp, norm_cast]
/-
**NNReal.coe_mulIndicator** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_mulIndicator {α} (s : Set α) (f : α -> Real>=0) (a : α) : ((s.mulIndic
ator f a : Real>=0) : Real) = s.mulIndicator (fun x => ↑(f x)) a
参数：s : Set α；f : α -> Real>=0；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mulIndicator`：map_mulIndicator {M N F : Type*} [One M] [One N] [FunL
ike F M N] [OneHomClass F M N] (f : F) (s : Set α) (g : α -> M) (x : α) : f (s.m
ulIndi…
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_mulIndicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.mulIndicator f a : ℝ≥0) : ℝ) = s.mulIndicator (fun x => ↑(f x)) a :=
  map_mulIndicator toRealHom _ _ _

@[simp, norm_cast]
/-
**NNReal.coe_indicator** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_indicator {α} (s : Set α) (f : α -> Real>=0) (a : α) : ((s.indicator f
 a : Real>=0) : Real) = s.indicator (fun x => ↑(f x)) a
参数：s : Set α；f : α -> Real>=0；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_indicator`：∀ {α : Type u_1} {M : Type u_6} {N : Type u_7} {F : Type 
u_8} [inst : Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass 
F M…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_indicator {α} (s : Set α) (f : α → ℝ≥0) (a : α) :
    ((s.indicator f a : ℝ≥0) : ℝ) = s.indicator (fun x => ↑(f x)) a :=
  map_indicator toRealHom _ _ _

@[simp, norm_cast]
/-
**NNReal.coe_mulSingle** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_mulSingle {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α) : ((Pi.mul
Single a b : α -> Real>=0) c : Real) = (Pi.mulSingle a b : α -> Real) c
参数：a : α；b : Real>=0；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.mulIndicator_singleton`：mulIndicator_singleton (i : ι) (f : ι -> M) 
: Set.mulIndicator {i} f = Pi.mulSingle i (f i)
· 使用定理 `NNReal.coe_mulIndicator`：coe_mulIndicator {α} (s : Set α) (f : α -> Real
>=0) (a : α) : ((s.mulIndicator f a : Real>=0) : Real) = s.mulIndicator (fun x =
> ↑(f x)) a
-/
theorem coe_mulSingle {α} [DecidableEq α] (a : α) (b : ℝ≥0) (c : α) :
    ((Pi.mulSingle a b : α → ℝ≥0) c : ℝ) = (Pi.mulSingle a b : α → ℝ) c := by
  simpa using coe_mulIndicator {a} (fun _ ↦ b) c

@[simp, norm_cast]
/-
**NNReal.coe_single** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_single {α} [DecidableEq α] (a : α) (b : Real>=0) (c : α) : ((Pi.single
 a b : α -> Real>=0) c : Real) = (Pi.single a b : α -> Real) c
参数：a : α；b : Real>=0；c : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Set.indicator_singleton`：∀ {ι : Type u_6} [inst : DecidableEq ι] {M : Ty
pe u_7} [inst_1 : Zero M] (i : ι) (f : ι → M),   {i}.indicator f = Pi.single i (
f i)
· 使用定理 `NNReal.coe_indicator`：coe_indicator {α} (s : Set α) (f : α -> Real>=0) (
a : α) : ((s.indicator f a : Real>=0) : Real) = s.indicator (fun x => ↑(f x)) a
-/
theorem coe_single {α} [DecidableEq α] (a : α) (b : ℝ≥0) (c : α) :
    ((Pi.single a b : α → ℝ≥0) c : ℝ) = (Pi.single a b : α → ℝ) c := by
  simpa using coe_indicator {a} (fun _ ↦ b) c

@[norm_cast]
/-
**NNReal.coe_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_list_sum (l : List Real>=0) : ((l.sum : Real>=0) : Real) = (l.map (↑))
.sum
参数：l : List Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
theorem coe_list_sum (l : List ℝ≥0) : ((l.sum : ℝ≥0) : ℝ) = (l.map (↑)).sum :=
  map_list_sum toRealHom l

@[norm_cast]
/-
**NNReal.coe_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_list_prod (l : List Real>=0) : ((l.prod : Real>=0) : Real) = (l.map (↑
)).prod
参数：l : List Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_list_prod (l : List ℝ≥0) : ((l.prod : ℝ≥0) : ℝ) = (l.map (↑)).prod :=
  map_list_prod toRealHom l

@[norm_cast]
/-
**NNReal.coe_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_multiset_sum (s : Multiset Real>=0) : ((s.sum : Real>=0) : Real) = (s.
map (↑)).sum
参数：s : Multiset Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
theorem coe_multiset_sum (s : Multiset ℝ≥0) : ((s.sum : ℝ≥0) : ℝ) = (s.map (↑)).sum :=
  map_multiset_sum toRealHom s

@[norm_cast]
/-
**NNReal.coe_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_multiset_prod (s : Multiset Real>=0) : ((s.prod : Real>=0) : Real) = (
s.map (↑)).prod
参数：s : Multiset Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_prod`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst 
: CommMonoid M] [inst_1 : CommMonoid N] [inst_2 : FunLike F M N]   [MonoidHomCla
ss F M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_multiset_prod (s : Multiset ℝ≥0) : ((s.prod : ℝ≥0) : ℝ) = (s.map (↑)).prod :=
  map_multiset_prod toRealHom s

variable {ι : Type*} {s : Finset ι} {f : ι → ℝ}

@[simp, norm_cast]
/-
**NNReal.coe_sum** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_sum (s : Finset ι) (f : ι -> Real>=0) : ∑ i in s, f i = ∑ i in s, (f i
 : Real)
参数：s : Finset ι；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
theorem coe_sum (s : Finset ι) (f : ι → ℝ≥0) : ∑ i ∈ s, f i = ∑ i ∈ s, (f i : ℝ) :=
  map_sum toRealHom _ _

@[simp, norm_cast]
/-
**NNReal.toReal_finsuppSum** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：toReal_finsuppSum (f : ι ->₀ M) (g : ι -> M -> Real>=0) : f.sum g = f.sum 
(fun i m => toReal (g i m))
参数：f : ι ->₀ M；g : ι -> M -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma toReal_finsuppSum (f : ι →₀ M) (g : ι → M → ℝ≥0) :
    f.sum g = f.sum (fun i m ↦ toReal (g i m)) := map_finsuppSum toRealHom ..

@[simp, norm_cast]
/-
**NNReal.toReal_finsuppProd** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：toReal_finsuppProd (f : ι ->₀ M) (g : ι -> M -> Real>=0) : f.prod g = f.pr
od (fun i m => toReal (g i m))
参数：f : ι ->₀ M；g : ι -> M -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finsuppProd`：map_finsuppProd [Zero M] [CommMonoid N] [CommMonoid P] 
{H : Type*} [FunLike H N P] [MonoidHomClass H N P] (h : H) (f : α ->₀ M) (g : α 
-> M …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
lemma toReal_finsuppProd (f : ι →₀ M) (g : ι → M → ℝ≥0) :
    f.prod g = f.prod (fun i m ↦ toReal (g i m)) := map_finsuppProd toRealHom ..

@[simp, norm_cast]
/-
**NNReal.coe_expect** 是 Mathlib 中的一个引理，位于命名空间 `NNReal`。
形式化陈述：coe_expect (s : Finset ι) (f : ι -> Real>=0) : 𝔼 i in s, f i = 𝔼 i in s, (
f i : Real)
参数：s : Finset ι；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_expect`：∀ {ι : Type u_1} {M : Type u_4} {N : Type u_5} [inst : AddCo
mmMonoid M] [inst_1 : _root_.Module ℚ≥0 M]   [inst_2 : AddCommMonoid N] [inst_3 
…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `RingHomClass.toLinearMapClassNNRat`：∀ {F : Type u_1} {R : Type u_2} {S :
 Type u_3} [inst : DivisionSemiring R] [inst_1 : CharZero R]   [inst_2 : Divisio
nSemiring S] [inst_3 : C…
-/
lemma coe_expect (s : Finset ι) (f : ι → ℝ≥0) : 𝔼 i ∈ s, f i = 𝔼 i ∈ s, (f i : ℝ) :=
  map_expect toRealHom ..
/-
**NNReal._root_.Real.toNNReal_sum_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_sum_of_nonneg (hf : ∀ i ∈ s, 0 ≤ f i) :
    Real.toNNReal (∑ a ∈ s, f a) = ∑ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_sum, Real.coe_toNNReal _ (Finset.sum_nonneg hf)]
  exact Finset.sum_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]

@[simp, norm_cast]
/-
**NNReal.coe_prod** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：coe_prod (s : Finset ι) (f : ι -> Real>=0) : ↑(∏ a in s, f a) = ∏ a in s, 
(f a : Real)
参数：s : Finset ι；f : ι -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem coe_prod (s : Finset ι) (f : ι → ℝ≥0) : ↑(∏ a ∈ s, f a) = ∏ a ∈ s, (f a : ℝ) :=
  map_prod toRealHom _ _
/-
**NNReal._root_.Real.toNNReal_prod_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Real.toNNReal_prod_of_nonneg (hf : ∀ a, a ∈ s → 0 ≤ f a) :
    Real.toNNReal (∏ a ∈ s, f a) = ∏ a ∈ s, Real.toNNReal (f a) := by
  rw [← coe_inj, NNReal.coe_prod, Real.coe_toNNReal _ (Finset.prod_nonneg hf)]
  exact Finset.prod_congr rfl fun x hxs => by rw [Real.coe_toNNReal _ (hf x hxs)]
/-
**NNReal.le_iInf_add_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι -> Real>
=0} {g : ι' -> Real>=0} {a : Real>=0} (h : forall i j, a <= f i + g j) : a <= (⨅
 i, f i) + ⨅ j, g j
参数：h : forall i j, a <= f i + g j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `NNReal.coe_add`：∀ (r₁ r₂ : NNReal), ↑(r₁ + r₂) = ↑r₁ + ↑r₂
· 使用定理 `NNReal.coe_iInf`：coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) 
: Real) = ⨅ i, ↑(s i)
· 使用定理 `le_ciInf_add_ciInf`：∀ {α : Type u_1} {ι : Sort u_2} {ι' : Sort u_3} [Non
empty ι] [Nonempty ι'] [inst : ConditionallyCompleteLattice α]   [inst_1 : AddGr
oup α] […
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem le_iInf_add_iInf {ι ι' : Sort*} [Nonempty ι] [Nonempty ι'] {f : ι → ℝ≥0} {g : ι' → ℝ≥0}
    {a : ℝ≥0} (h : ∀ i j, a ≤ f i + g j) : a ≤ (⨅ i, f i) + ⨅ j, g j := by
  rw [← NNReal.coe_le_coe, NNReal.coe_add, coe_iInf, coe_iInf]
  exact le_ciInf_add_ciInf h
/-
**NNReal.mul_finset_sup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_finset_sup {α} (r : Real>=0) (s : Finset α) (f : α -> Real>=0) : r * s
.sup f = s.sup fun a => r * f a
参数：r : Real>=0；s : Finset α；f : α -> Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `NNReal.mul_sup`：mul_sup (a b c : Real>=0) : a * (b ⊔ c) = a * b ⊔ a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem mul_finset_sup {α} (r : ℝ≥0) (s : Finset α) (f : α → ℝ≥0) :
    r * s.sup f = s.sup fun a => r * f a :=
  Finset.apply_sup_eq_sup_comp _ (NNReal.mul_sup r) (mul_zero r)
/-
**NNReal.finset_sup_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：finset_sup_mul {α} (s : Finset α) (f : α -> Real>=0) (r : Real>=0) : s.sup
 f * r = s.sup fun a => f a * r
参数：s : Finset α；f : α -> Real>=0；r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.apply_sup_eq_sup_comp`：apply_sup_eq_sup_comp [SemilatticeSup γ] [
OrderBot γ] {s : Finset β} {f : β -> α} (g : α -> γ) (g_sup : forall x y, g (x ⊔
 y) = g x ⊔ g y) (…
· 使用定理 `NNReal.sup_mul`：sup_mul (a b c : Real>=0) : (a ⊔ b) * c = a * c ⊔ b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem finset_sup_mul {α} (s : Finset α) (f : α → ℝ≥0) (r : ℝ≥0) :
    s.sup f * r = s.sup fun a => f a * r :=
  Finset.apply_sup_eq_sup_comp (· * r) (fun x y => NNReal.sup_mul x y r) (zero_mul r)
/-
**NNReal.finset_sup_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：finset_sup_div {α} {f : α -> Real>=0} {s : Finset α} (r : Real>=0) : s.sup
 f / r = s.sup fun a => f a / r
参数：r : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `NNReal.mul_finset_sup`：mul_finset_sup {α} (r : Real>=0) (s : Finset α) (
f : α -> Real>=0) : r * s.sup f = s.sup fun a => r * f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finset_sup_div {α} {f : α → ℝ≥0} {s : Finset α} (r : ℝ≥0) :
    s.sup f / r = s.sup fun a => f a / r := by simp only [div_eq_inv_mul, mul_finset_sup]

section Set

/-
**NNReal.bddAbove_natCast_image_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {s : Set ℕ}, BddAbove (Nat.cast '' s) ↔ BddAbove s
参数：Nat.cast '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp'`：∀ {α : Sort u_2} {p : α → Prop} {β : Sort u_1} {q : β → Pro
p} (f : α → β),   (∀ (a : α), p a → q (f a)) → (∃ a, p a) → ∃ b, q b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
@[simp] lemma bddAbove_natCast_image_iff {s : Set ℕ} : BddAbove ((↑) '' s : Set ℝ≥0) ↔ BddAbove s :=
  ⟨.imp' Nat.floor (by simp [upperBounds, Nat.le_floor_iff]), .imp' (↑) (by simp [upperBounds])⟩
/-
**NNReal.bddAbove_range_natCast_iff** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Sort u_3} (f : ι → ℕ), BddAbove (Set.range fun x => ↑(f x)) ↔ BddAb
ove (Set.range f)
参数：f : ι → ℕ；Set.range fun x => ↑(f x)；Set.range f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.bddAbove_natCast_image_iff`：∀ {s : Set ℕ}, BddAbove (Nat.cast '' 
s) ↔ BddAbove s
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast] lemma bddAbove_range_natCast_iff {ι : Sort*} (f : ι → ℕ) :
    BddAbove (Set.range (f ·) : Set NNReal) ↔ BddAbove (Set.range f) := by
  rw [← bddAbove_natCast_image_iff, ← Set.range_comp]
  rfl

end Set

open Real

section Sub

/-!
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well into any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSub` in the file
`Mathlib/Algebra/Order/Sub/Basic.lean`. See also `mul_tsub` and `tsub_mul`.
-/

/-
**NNReal.sub_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：sub_div (a b c : Real>=0) : (a - b) / c = a / c - b / c
参数：a b c : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsub_div`：tsub_div (a b c : α) : (a - b) / c = a / c - b / c
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.instOrderedSub`：OrderedSub NNReal

--- 原说明 ---
### Lemmas about subtraction

In this section we provide a few lemmas about subtraction that do not fit well i
nto any other
typeclass. For lemmas about subtraction and addition see lemmas about `OrderedSu
b` in the file
`Mathlib/Algebra/Order/Sub/Basic.lean`. See also `mul_tsub` and `tsub_mul`.
-/
theorem sub_div (a b c : ℝ≥0) : (a - b) / c = a / c - b / c :=
  tsub_div _ _ _

/-- This lemma is needed for the `norm_cast` simp set. Outside of this use case `Nat.coe_sub`
should be used. -/
@[norm_cast]
/-
**NNReal.coe_sub_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {a b : NNReal}, a < b → ↑(b - a) = ↑b - ↑a
参数：b - a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.coe_sub`：∀ {r₁ r₂ : NNReal}, r₂ ≤ r₁ → ↑(r₁ - r₂) = ↑r₁ - ↑r₂
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b

--- 原说明 ---
This lemma is needed for the `norm_cast` simp set. Outside of this use case `Nat
.coe_sub`
should be used.
-/
protected theorem coe_sub_of_lt {a b : ℝ≥0} (h : a < b) :
    ((b - a : ℝ≥0) : ℝ) = b - a := NNReal.coe_sub h.le

end Sub

section Csupr

open Set

variable {ι : Sort*} {f : ι → ℝ≥0}

/-
**NNReal.iInf_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iInf_mul (f : ι -> Real>=0) (a : Real>=0) : iInf f * a = ⨅ i, f i * a
参数：f : ι -> Real>=0；a : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.coe_iInf`：coe_iInf {ι : Sort*} (s : ι -> Real>=0) : (↑(⨅ i, s i) 
: Real) = ⨅ i, ↑(s i)
· 使用定理 `Real.iInf_mul_of_nonneg`：Real.iInf_mul_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (⨅ i, f i) * r = ⨅ i, f i * r
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem iInf_mul (f : ι → ℝ≥0) (a : ℝ≥0) : iInf f * a = ⨅ i, f i * a := by
  rw [← coe_inj, NNReal.coe_mul, coe_iInf, coe_iInf]
  exact Real.iInf_mul_of_nonneg (NNReal.coe_nonneg _) _
/-
**NNReal.mul_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_iInf (f : ι -> Real>=0) (a : Real>=0) : a * iInf f = ⨅ i, a * f i
参数：f : ι -> Real>=0；a : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NNReal.iInf_mul`：iInf_mul (f : ι -> Real>=0) (a : Real>=0) : iInf f * a 
= ⨅ i, f i * a
-/
theorem mul_iInf (f : ι → ℝ≥0) (a : ℝ≥0) : a * iInf f = ⨅ i, a * f i := by
  simpa only [mul_comm] using iInf_mul f a
/-
**NNReal.mul_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_iSup (f : ι -> Real>=0) (a : Real>=0) : (a * ⨆ i, f i) = ⨆ i, a * f i
参数：f : ι -> Real>=0；a : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NNReal.coe_inj`：∀ {r₁ r₂ : NNReal}, ↑r₁ = ↑r₂ ↔ r₁ = r₂
· 使用定理 `NNReal.coe_mul`：∀ (r₁ r₂ : NNReal), ↑(r₁ * r₂) = ↑r₁ * ↑r₂
· 使用定理 `NNReal.coe_iSup`：coe_iSup {ι : Sort*} (s : ι -> Real>=0) : (↑(⨆ i, s i) 
: Real) = ⨆ i, ↑(s i)
· 使用定理 `Real.mul_iSup_of_nonneg`：Real.mul_iSup_of_nonneg (ha : 0 <= r) (f : ι ->
 Real) : (r * ⨆ i, f i) = ⨆ i, r * f i
· 使用定理 `NNReal.coe_nonneg`：∀ (r : NNReal), 0 ≤ ↑r
-/
theorem mul_iSup (f : ι → ℝ≥0) (a : ℝ≥0) : (a * ⨆ i, f i) = ⨆ i, a * f i := by
  rw [← coe_inj, NNReal.coe_mul, NNReal.coe_iSup, NNReal.coe_iSup]
  exact Real.mul_iSup_of_nonneg (NNReal.coe_nonneg _) _
/-
**NNReal.iSup_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_mul (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) * a = ⨆ i, f i * a
参数：f : ι -> Real>=0；a : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `NNReal.mul_iSup`：mul_iSup (f : ι -> Real>=0) (a : Real>=0) : (a * ⨆ i, f
 i) = ⨆ i, a * f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_mul (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) * a = ⨆ i, f i * a := by
  rw [mul_comm, mul_iSup]
  simp_rw [mul_comm]
/-
**NNReal.iSup_div** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_div (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) / a = ⨆ i, f i / a
参数：f : ι -> Real>=0；a : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `NNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) 
* a = ⨆ i, f i * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem iSup_div (f : ι → ℝ≥0) (a : ℝ≥0) : (⨆ i, f i) / a = ⨆ i, f i / a := by
  simp only [div_eq_mul_inv, iSup_mul]
/-
**NNReal.mul_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：mul_iSup_le {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, 
g * h j <= a) : g * iSup h <= a
参数：H : forall j, g * h j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mul_iSup`：mul_iSup (f : ι -> Real>=0) (a : Real>=0) : (a * ⨆ i, f
 i) = ⨆ i, a * f i
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
-/
theorem mul_iSup_le {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, g * h j ≤ a) : g * iSup h ≤ a := by
  rw [mul_iSup]
  exact ciSup_le' H
/-
**NNReal.iSup_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_mul_le {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, 
g i * h <= a) : iSup g * h <= a
参数：H : forall i, g i * h <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.iSup_mul`：iSup_mul (f : ι -> Real>=0) (a : Real>=0) : (⨆ i, f i) 
* a = ⨆ i, f i * a
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
-/
theorem iSup_mul_le {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, g i * h ≤ a) : iSup g * h ≤ a := by
  rw [iSup_mul]
  exact ciSup_le' H
/-
**NNReal.iSup_mul_iSup_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：iSup_mul_iSup_le {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, g i *
 h j <= a) : iSup g * iSup h <= a
参数：H : forall i j, g i * h j <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.iSup_mul_le`：iSup_mul_le {a : Real>=0} {g : ι -> Real>=0} {h : Re
al>=0} (H : forall i, g i * h <= a) : iSup g * h <= a
· 使用定理 `NNReal.mul_iSup_le`：mul_iSup_le {a : Real>=0} {g : Real>=0} {h : ι -> Re
al>=0} (H : forall j, g * h j <= a) : g * iSup h <= a
-/
theorem iSup_mul_iSup_le {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, g i * h j ≤ a) :
    iSup g * iSup h ≤ a :=
  iSup_mul_le fun _ => mul_iSup_le <| H _

variable [Nonempty ι]
/-
**NNReal.le_mul_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_mul_iInf {a : Real>=0} {g : Real>=0} {h : ι -> Real>=0} (H : forall j, 
a <= g * h j) : a <= g * iInf h
参数：H : forall j, a <= g * h j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.mul_iInf`：mul_iInf (f : ι -> Real>=0) (a : Real>=0) : a * iInf f 
= ⨅ i, a * f i
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
-/
theorem le_mul_iInf {a : ℝ≥0} {g : ℝ≥0} {h : ι → ℝ≥0} (H : ∀ j, a ≤ g * h j) : a ≤ g * iInf h := by
  rw [mul_iInf]
  exact le_ciInf H
/-
**NNReal.le_iInf_mul** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_iInf_mul {a : Real>=0} {g : ι -> Real>=0} {h : Real>=0} (H : forall i, 
a <= g i * h) : a <= iInf g * h
参数：H : forall i, a <= g i * h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NNReal.iInf_mul`：iInf_mul (f : ι -> Real>=0) (a : Real>=0) : iInf f * a 
= ⨅ i, f i * a
· 使用定理 `le_ciInf`：le_ciInf [Nonempty ι] {f : ι -> α} {c : α} (H : forall x, c <=
 f x) : c <= iInf f
-/
theorem le_iInf_mul {a : ℝ≥0} {g : ι → ℝ≥0} {h : ℝ≥0} (H : ∀ i, a ≤ g i * h) : a ≤ iInf g * h := by
  rw [iInf_mul]
  exact le_ciInf H
/-
**NNReal.le_iInf_mul_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：le_iInf_mul_iInf {a : Real>=0} {g h : ι -> Real>=0} (H : forall i j, a <= 
g i * h j) : a <= iInf g * iInf h
参数：H : forall i j, a <= g i * h j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NNReal.le_iInf_mul`：le_iInf_mul {a : Real>=0} {g : ι -> Real>=0} {h : Re
al>=0} (H : forall i, a <= g i * h) : a <= iInf g * h
· 使用定理 `NNReal.le_mul_iInf`：le_mul_iInf {a : Real>=0} {g : Real>=0} {h : ι -> Re
al>=0} (H : forall j, a <= g * h j) : a <= g * iInf h
-/
theorem le_iInf_mul_iInf {a : ℝ≥0} {g h : ι → ℝ≥0} (H : ∀ i j, a ≤ g i * h j) :
    a ≤ iInf g * iInf h :=
  le_iInf_mul fun i => le_mul_iInf <| H i
/-
**NNReal.natCast_iSup** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Sort u_4} (f : ι → ℕ), ↑(⨆ i, f i) = ⨆ i, ↑(f i)
参数：f : ι → ℕ；⨆ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_forall_ge_iff`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α},
 (∀ (c : α), a ≤ c ↔ b ≤ c) → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `ciSup_of_not_bddAbove`：ciSup_of_not_bddAbove (hf : ¬BddAbove (range f)) 
: ⨆ i, f i = sSup ∅
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `NNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd NNReal
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, norm_cast] lemma natCast_iSup {ι : Sort*} (f : ι → ℕ) :
    ⨆ i, f i = (⨆ i, f i : NNReal) := by
  by_cases h : BddAbove (Set.range f)
  · apply eq_of_forall_ge_iff
    simp [ciSup_le_iff', ← Nat.le_floor_iff, *]
  · simp [*]
/-
**NNReal.natCast_iInf** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ {ι : Sort u_4} (f : ι → ℕ), ↑(⨅ i, f i) = ⨅ i, ↑(f i)
参数：f : ι → ℕ；⨅ i, f i；f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.iInf_of_empty`：iInf_of_empty {ι : Sort*} [IsEmpty ι] (f : ι -> Nat) 
: iInf f = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `NNReal.iInf_empty`：iInf_empty [IsEmpty ι] (f : ι -> Real>=0) : ⨅ i, f i 
= 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `eq_of_forall_le_iff`：eq_of_forall_le_iff (H : forall c, c <= a ↔ c <= b)
 : a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp, norm_cast] lemma natCast_iInf {ι : Sort*} (f : ι → ℕ) :
    ⨅ i, f i = (⨅ i, f i : NNReal) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · simp [iInf_empty]
  apply eq_of_forall_le_iff
  simp [le_ciInf_iff, ← Nat.ceil_le]

end Csupr

section rify

/-
**NNReal.toReal_eq** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a b : NNReal), a = b ↔ ↑a = ↑b
参数：a b : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[rify_simps] lemma toReal_eq (a b : ℝ≥0) : a = b ↔ (a : ℝ) = (b : ℝ) := by simp
/-
**NNReal.toReal_le** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a b : NNReal), a ≤ b ↔ ↑a ≤ ↑b
参数：a b : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[rify_simps] lemma toReal_le (a b : ℝ≥0) : a ≤ b ↔ (a : ℝ) ≤ (b : ℝ) := by simp
/-
**NNReal.toReal_lt** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a b : NNReal), a < b ↔ ↑a < ↑b
参数：a b : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[rify_simps] lemma toReal_lt (a b : ℝ≥0) : a < b ↔ (a : ℝ) < (b : ℝ) := by simp
/-
**NNReal.toReal_ne** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：∀ (a b : NNReal), a ≠ b ↔ ↑a ≠ ↑b
参数：a b : NNReal。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[rify_simps] lemma toReal_ne (a b : ℝ≥0) : a ≠ b ↔ (a : ℝ) ≠ (b : ℝ) := by simp

end rify

@[simp]
/-
**NNReal.range_coe** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：range_coe : range toReal = Ici 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
-/
theorem range_coe : range toReal = Ici 0 := Subtype.range_coe

@[simp]
/-
**NNReal.image_coe_Ici** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Ici (x : Real>=0) : toReal '' Ici x = Ici ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Ici`：image_subtype_val_Ici_Ici {a : α} (b : Ic
i a) : Subtype.val '' Ici b = Ici b.1
-/
theorem image_coe_Ici (x : ℝ≥0) : toReal '' Ici x = Ici ↑x := image_subtype_val_Ici_Ici ..

@[simp]
/-
**NNReal.image_coe_Iic** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Iic (x : Real>=0) : toReal '' Iic x = Icc 0 ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Iic`：image_subtype_val_Ici_Iic {a : α} (b : Ic
i a) : Subtype.val '' Iic b = Icc a b
-/
theorem image_coe_Iic (x : ℝ≥0) : toReal '' Iic x = Icc 0 ↑x := image_subtype_val_Ici_Iic ..

@[simp]
/-
**NNReal.image_coe_Ioi** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Ioi (x : Real>=0) : toReal '' Ioi x = Ioi ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Ioi`：image_subtype_val_Ici_Ioi {a : α} (b : Ic
i a) : Subtype.val '' Ioi b = Ioi b.1
-/
theorem image_coe_Ioi (x : ℝ≥0) : toReal '' Ioi x = Ioi ↑x := image_subtype_val_Ici_Ioi ..

@[simp]
/-
**NNReal.image_coe_Iio** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Iio (x : Real>=0) : toReal '' Iio x = Ico 0 ↑x
参数：x : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ici_Iio`：image_subtype_val_Ici_Iio {a : α} (b : Ic
i a) : Subtype.val '' Iio b = Ico a b
-/
theorem image_coe_Iio (x : ℝ≥0) : toReal '' Iio x = Ico 0 ↑x := image_subtype_val_Ici_Iio ..

@[simp]
/-
**NNReal.image_coe_Icc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Icc (x y : Real>=0) : toReal '' Icc x y = Icc ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Icc`：image_subtype_val_Icc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Icc x y = Icc x.1 y
-/
theorem image_coe_Icc (x y : ℝ≥0) : toReal '' Icc x y = Icc ↑x ↑y :=
  image_subtype_val_Icc (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_Ioc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Ioc (x y : Real>=0) : toReal '' Ioc x y = Ioc ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ioc`：image_subtype_val_Ioc {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioc x y = Ioc x.1 y
-/
theorem image_coe_Ioc (x y : ℝ≥0) : toReal '' Ioc x y = Ioc ↑x ↑y :=
  image_subtype_val_Ioc (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_Ico** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Ico (x y : Real>=0) : toReal '' Ico x y = Ico ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ico`：image_subtype_val_Ico {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ico x y = Ico x.1 y
-/
theorem image_coe_Ico (x y : ℝ≥0) : toReal '' Ico x y = Ico ↑x ↑y :=
  image_subtype_val_Ico (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_Ioo** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_Ioo (x y : Real>=0) : toReal '' Ioo x y = Ioo ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Set.image_subtype_val_Ioo`：image_subtype_val_Ioo {s : Set α} [OrdConnect
ed s] (x y : s) : Subtype.val '' Ioo x y = Ioo x.1 y
-/
theorem image_coe_Ioo (x y : ℝ≥0) : toReal '' Ioo x y = Ioo ↑x ↑y :=
  image_subtype_val_Ioo (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_uIcc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_uIcc (x y : Real>=0) : toReal '' uIcc x y = uIcc ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subtype_val_uIcc`：image_subtype_val_uIcc [OrdConnected s] (a b
 : s) : Subtype.val '' [[a, b]] = [[a.1, b.1]]
-/
theorem image_coe_uIcc (x y : ℝ≥0) : toReal '' uIcc x y = uIcc ↑x ↑y :=
  image_subtype_val_uIcc (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_uIoc** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_uIoc (x y : Real>=0) : toReal '' uIoc x y = uIoc ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subtype_val_uIoc`：image_subtype_val_uIoc [OrdConnected s] (a b
 : s) : Subtype.val '' uIoc a b = uIoc a.1 b.1
-/
theorem image_coe_uIoc (x y : ℝ≥0) : toReal '' uIoc x y = uIoc ↑x ↑y :=
  image_subtype_val_uIoc (s := Ici 0) ..

@[simp]
/-
**NNReal.image_coe_uIoo** 是 Mathlib 中的一个定理，位于命名空间 `NNReal`。
形式化陈述：image_coe_uIoo (x y : Real>=0) : toReal '' uIoo x y = uIoo ↑x ↑y
参数：x y : Real>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_subtype_val_uIoo`：image_subtype_val_uIoo [OrdConnected s] (a b
 : s) : Subtype.val '' uIoo a b = uIoo a.1 b.1
-/
theorem image_coe_uIoo (x y : ℝ≥0) : toReal '' uIoo x y = uIoo ↑x ↑y :=
  image_subtype_val_uIoo (s := Ici 0) ..

end NNReal

