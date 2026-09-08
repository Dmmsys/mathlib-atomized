/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan, Oliver Nash
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Module.Submodule.Invariant
public import Mathlib.LinearAlgebra.PerfectPairing.Restrict
public import Mathlib.LinearAlgebra.RootSystem.Defs

import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Span.TensorProduct
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Root pairings taking values in a subring

This file lays out the basic theory of root pairings over a commutative ring `R`, where `R` is an
`S`-algebra, and the pairing between roots and coroots takes values in `S`. The main application
of this theory is the theory of crystallographic root systems, where `S = ℤ`.

## Main definitions:

* `RootPairing.IsValuedIn`: Given a commutative ring `S` and an `S`-algebra `R`, a root pairing
  over `R` is valued in `S` if all root-coroot pairings lie in the image of `algebraMap S R`.
* `RootPairing.IsCrystallographic`: A root pairing is said to be crystallographic if the pairing
  between a root and coroot is always an integer.
* `RootPairing.pairingIn`: The `S`-valued pairing between roots and coroots.
* `RootPairing.coxeterWeightIn`: The product of `pairingIn i j` and `pairingIn j i`.

-/

@[expose] public section

open Set Function
open Submodule (span)
open Module

noncomputable section

namespace RootPairing

variable {ι R S M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (i j : ι)

/-- If `R` is an `S`-algebra, a root pairing over `R` is said to be valued in `S` if the pairing
between a root and coroot always belongs to `S`.

Of particular interest is the case `S = ℤ`. See `RootPairing.IsCrystallographic`. -/
@[mk_iff]
/-
**RootPairing.IsValuedIn** 是 Mathlib 中的一个类，位于命名空间 `RootPairing`。
形式化陈述：IsValuedIn (S : Type*) [CommRing S] [Algebra S R] : Prop where exists_valu
e : forall i j, exists s, algebraMap S R s = P.pairing i j  protected alias exis
ts_value
参数：S : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `R` is an `S`-algebra, a root pairing over `R` is said to be valued in `S` if
 the pairing
between a root and coroot always belongs to `S`.

Of particular interest is the case `S = ℤ`. See `RootPairing.IsCrystallographic`
.
-/
class IsValuedIn (S : Type*) [CommRing S] [Algebra S R] : Prop where
  exists_value : ∀ i j, ∃ s, algebraMap S R s = P.pairing i j

protected alias exists_value := IsValuedIn.exists_value

/-- A root pairing is said to be crystallographic if the pairing between a root and coroot is
always an integer. -/
/-
**RootPairing.IsCrystallographic** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：IsCrystallographic
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root pairing is said to be crystallographic if the pairing between a root and 
coroot is
always an integer.
-/
abbrev IsCrystallographic := P.IsValuedIn ℤ
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.IsValuedIn R where
  exists_value i j := by simp

variable (S : Type*) [CommRing S] [Algebra S R]

variable {S} in
/-
**RootPairing.isValuedIn_iff_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isValuedIn_iff_mem_range : P.IsValuedIn S ↔ forall i j, P.pairing i j in r
ange (algebraMap S R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isValuedIn_iff_mem_range :
    P.IsValuedIn S ↔ ∀ i j, P.pairing i j ∈ range (algebraMap S R) := by
  simp only [isValuedIn_iff, mem_range]
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsValuedIn S] : P.flip.IsValuedIn S := by
  rw [isValuedIn_iff, forall_comm]
  exact P.exists_value

/-- A variant of `RootPairing.pairing` for root pairings which are valued in a smaller set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., when we have
`[FaithfulSMul S R]`. -/
/-
**RootPairing.pairingIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：pairingIn [P.IsValuedIn S] (i j : ι) : S
参数：i j : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.exists_value`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4}
 {N : Type u_5} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_
.Module R M} {…

--- 原说明 ---
A variant of `RootPairing.pairing` for root pairings which are valued in a small
er set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., w
hen we have
`[FaithfulSMul S R]`.
-/
def pairingIn [P.IsValuedIn S] (i j : ι) : S :=
  (P.exists_value i j).choose

@[simp]
/-
**RootPairing.algebraMap_pairingIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：algebraMap_pairingIn [P.IsValuedIn S] (i j : ι) : algebraMap S R (P.pairin
gIn S i j) = P.pairing i j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `RootPairing.exists_value`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4}
 {N : Type u_5} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_
.Module R M} {…
-/
lemma algebraMap_pairingIn [P.IsValuedIn S] (i j : ι) :
    algebraMap S R (P.pairingIn S i j) = P.pairing i j :=
  (P.exists_value i j).choose_spec

@[simp]
/-
**RootPairing.pairingIn_same** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_same [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) : P.pairingIn S
 i i = 2
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairingIn_same [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    P.pairingIn S i i = 2 :=
  FaithfulSMul.algebraMap_injective S R <| by simp [map_ofNat]

variable {P S} in
/-
**RootPairing.pairingIn_eq_add_of_root_eq_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：pairingIn_eq_add_of_root_eq_add [FaithfulSMul S R] [P.IsValuedIn S] {i j k
 l : ι} (h : P.root k = P.root i + P.root l) : P.pairingIn S k j = P.pairingIn S
 i j + P.pairingIn S l j
参数：h : P.root k = P.root i + P.root l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_eq_add_of_root_eq_add`：pairing_eq_add_of_root_eq_add
 {i j k l : ι} (h : P.root k = P.root i + P.root j) : P.pairing k l = P.pairing 
i l + P.pairing j l
-/
lemma pairingIn_eq_add_of_root_eq_add [FaithfulSMul S R] [P.IsValuedIn S]
    {i j k l : ι} (h : P.root k = P.root i + P.root l) :
    P.pairingIn S k j = P.pairingIn S i j + P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using pairing_eq_add_of_root_eq_add h

variable {P S} in
/-
**RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul** 是 Mathlib 中的一个引理，位于命名空
间 `RootPairing`。
形式化陈述：pairingIn_eq_add_of_root_eq_smul_add_smul [FaithfulSMul S R] [P.IsValuedIn
 S] [Module S M] [IsScalarTower S R M] {i j k l : ι} {x y : S} (h : P.root k = x
 • P.root i + y • P.root l) : P.pairingIn S k j = x • P.pairingIn S i j + y • P.
pairingIn S l j
参数：h : P.root k = x • P.root i + y • P.root l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_eq_add_of_root_eq_smul_add_smul`：pairing_eq_add_of_r
oot_eq_smul_add_smul {i j k l : ι} {x y : R} (h : P.root k = x • P.root i + y • 
P.root l) : P.pairing k j = x • P.pairing…
-/
lemma pairingIn_eq_add_of_root_eq_smul_add_smul
    [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsScalarTower S R M]
    {i j k l : ι} {x y : S} (h : P.root k = x • P.root i + y • P.root l) :
    P.pairingIn S k j = x • P.pairingIn S i j + y • P.pairingIn S l j := by
  apply FaithfulSMul.algebraMap_injective S R
  replace h : P.root k = (algebraMap S R x) • P.root i + (algebraMap S R y) • P.root l := by simpa
  simpa [← P.algebraMap_pairingIn S, -algebraMap_pairingIn] using
    pairing_eq_add_of_root_eq_smul_add_smul h
/-
**RootPairing.pairingIn_reflectionPerm** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_reflectionPerm [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
 P.pairingIn S j (P.reflectionPerm i k) = P.pairingIn S (P.reflectionPerm i j) k
参数：i j k : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_reflectionPerm`：pairing_reflectionPerm (i j k : ι) :
 P.pairing j (P.reflectionPerm i k) = P.pairing (P.reflectionPerm i j) k
-/
lemma pairingIn_reflectionPerm [FaithfulSMul S R] [P.IsValuedIn S] (i j k : ι) :
    P.pairingIn S j (P.reflectionPerm i k) = P.pairingIn S (P.reflectionPerm i j) k := by
  simp only [← (FaithfulSMul.algebraMap_injective S R).eq_iff, algebraMap_pairingIn]
  exact pairing_reflectionPerm P i j k

@[simp]
/-
**RootPairing.pairingIn_reflectionPerm_self_left** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：pairingIn_reflectionPerm_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i 
j : ι) : P.pairingIn S (P.reflectionPerm i i) j = - P.pairingIn S i j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_reflectionPerm_self_left`：pairing_reflectionPerm_sel
f_left (P : RootPairing ι R M N) (i j : ι) : P.pairing (P.reflectionPerm i i) j 
= - P.pairing i j
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairingIn_reflectionPerm_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S (P.reflectionPerm i i) j = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]

@[simp]
/-
**RootPairing.pairingIn_reflectionPerm_self_right** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：pairingIn_reflectionPerm_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i
 j : ι) : P.pairingIn S i (P.reflectionPerm j j) = - P.pairingIn S i j
参数：i j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_reflectionPerm_self_right`：pairing_reflectionPerm_se
lf_right (i j : ι) : P.pairing i (P.reflectionPerm j j) = - P.pairing i j
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairingIn_reflectionPerm_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) :
    P.pairingIn S i (P.reflectionPerm j j) = - P.pairingIn S i j := by
  simp [← (FaithfulSMul.algebraMap_injective S R).eq_iff]
/-
**RootPairing.IsValuedIn.trans** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsValuedIn
`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] (T : Type u_7) [inst_7 : CommRin
g T]   [inst_8 : Algebra T S] [inst_9 : Algebra T R] [IsScalarTower T S R] [P.Is
ValuedIn T], P.IsValuedIn S
参数：P : RootPairing ι R M N；S : Type u_6；T : Type u_7。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsValuedIn.trans (T : Type*) [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R]
    [P.IsValuedIn T] :
    P.IsValuedIn S where
  exists_value i j := by
    use algebraMap T S (P.pairingIn T i j)
    simp [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq T S R]
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsCrystallographic] [Algebra ℚ R] : P.IsValuedIn ℚ :=
  IsValuedIn.trans P (T := ℤ) (S := ℚ)
/-
**RootPairing.algebraMap_pairingIn'** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] (T : Type u_7) [inst_7 : CommRin
g T]   [inst_8 : Algebra T S] [inst_9 : Algebra T R] [IsScalarTower T S R] [inst
_11 : P.IsValuedIn T]   [inst_12 : P.IsValuedIn S] [FaithfulSMul S R] (i j : ι),
 (algebraMap T S) (P.pairingIn T i j) = P.pairingIn S i j
参数：P : RootPairing ι R M N；S : Type u_6；T : Type u_7；i j : ι；algebraMap T S；P.pa
iringIn T i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.comp_apply`：comp_apply (hnp : β ->+* γ) (hmn : α ->+* β) (x : α)
 : (hnp.comp hmn : α -> γ) x = hnp (hmn x)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma algebraMap_pairingIn' (T : Type*)
    [CommRing T] [Algebra T S] [Algebra T R] [IsScalarTower T S R] [P.IsValuedIn T] [P.IsValuedIn S]
    [FaithfulSMul S R] (i j : ι) :
    algebraMap T S (P.pairingIn T i j) = P.pairingIn S i j := by
  apply FaithfulSMul.algebraMap_injective S R
  rw [← RingHom.comp_apply, ← IsScalarTower.algebraMap_eq]
  simp
/-
**RootPairing.pairingIn_rat** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [Nontrivial 
R] [inst_6 : P.IsCrystallographic] [inst_7 : Algebra ℚ R] (i j : ι),   P.pairing
In ℚ i j = ↑(P.pairingIn ℤ i j)
参数：P : RootPairing ι R M N；i j : ι；P.pairingIn ℤ i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `RootPairing.instIsValuedInRatOfIsCrystallographic`：∀ {ι : Type u_1} {R :
 Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGr
oup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.algebraMap_pairingIn'`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pairingIn_rat [Nontrivial R] [P.IsCrystallographic] [Algebra ℚ R] (i j : ι) :
    P.pairingIn ℚ i j = P.pairingIn ℤ i j := by
  simp [← P.algebraMap_pairingIn' ℚ ℤ]
/-
**RootPairing.coroot'_apply_apply_mem_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Roo
tPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Module S M] [Is
ScalarTower S R M]   [P.IsValuedIn S] {x : M},   x ∈ Submodule.span S (Set.range
 ⇑P.root) → ∀ (i : ι), (P.coroot' i) x ∈ Set.range ⇑(algebraMap S R)
参数：P : RootPairing ι R M N；S : Type u_6；Set.range ⇑P.root；i : ι；P.coroot' i；alge
braMap S R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `RootPairing.exists_value`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4}
 {N : Type u_5} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_
.Module R M} {…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubmonoidClass.toAddMemClass`：∀ {S : Type u_3} {M : outParam (Type u_
4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass S
 M], AddMemClass S M
· 使用定理 `LinearMap.map_smul_of_tower`：map_smul_of_tower [CompatibleSMul M M₂ R S]
 (fₗ : M ->ₗ[S] M₂) (c : R) (x : M) : fₗ (c • x) = c • fₗ x
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma coroot'_apply_apply_mem_of_mem_span [Module S M] [IsScalarTower S R M] [P.IsValuedIn S]
    {x : M} (hx : x ∈ span S (range P.root)) (i : ι) :
    P.coroot' i x ∈ range (algebraMap S R) := by
  rw [show range (algebraMap S R) = LinearMap.range (Algebra.linearMap S R) by ext; simp]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    simpa using! RootPairing.exists_value k i
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using! add_mem hx hy
  | smul t x _ hx => simpa only [LinearMap.map_smul_of_tower] using! Submodule.smul_mem _ t hx
/-
**RootPairing.root'_apply_apply_mem_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `RootP
airing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Module S N] [Is
ScalarTower S R N]   [P.IsValuedIn S] {x : N},   x ∈ Submodule.span S (Set.range
 ⇑P.coroot) → ∀ (i : ι), (P.root' i) x ∈ (Algebra.linearMap S R).range
参数：P : RootPairing ι R M N；S : Type u_6；Set.range ⇑P.coroot；i : ι；P.root' i；Alge
bra.linearMap S R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.coroot'_apply_apply_mem_of_mem_span`：∀ {ι : Type u_1} {R : T
ype u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGrou
p M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma root'_apply_apply_mem_of_mem_span [Module S N] [IsScalarTower S R N] [P.IsValuedIn S]
    {x : N} (hx : x ∈ span S (range P.coroot)) (i : ι) :
    P.root' i x ∈ LinearMap.range (Algebra.linearMap S R) :=
  P.flip.coroot'_apply_apply_mem_of_mem_span S hx i

/-- The `S`-span of roots. -/
/-
**RootPairing.rootSpan** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：rootSpan [Module S M]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-span of roots.
-/
abbrev rootSpan [Module S M] := span S (range P.root)

/-- The `S`-span of coroots. -/
/-
**RootPairing.corootSpan** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：corootSpan [Module S N]
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-span of coroots.
-/
abbrev corootSpan [Module S N] := span S (range P.coroot)
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module S M] [Finite ι] :
    Module.Finite S <| P.rootSpan S :=
  Finite.span_of_finite S <| finite_range _
/-
**RootPairing.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module S N] [Finite ι] :
    Module.Finite S <| P.corootSpan S :=
  Finite.span_of_finite S <| finite_range _

/-- A root, seen as an element of the span of roots. -/
/-
**RootPairing.rootSpanMem** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：rootSpanMem [Module S M] (i : ι) : P.rootSpan S
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root, seen as an element of the span of roots.
-/
abbrev rootSpanMem [Module S M] (i : ι) : P.rootSpan S :=
  ⟨P.root i, Submodule.subset_span (mem_range_self i)⟩

/-- A coroot, seen as an element of the span of coroots. -/
/-
**RootPairing.corootSpanMem** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing`。
形式化陈述：corootSpanMem [Module S N] (i : ι) : P.corootSpan S
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coroot, seen as an element of the span of coroots.
-/
abbrev corootSpanMem [Module S N] (i : ι) : P.corootSpan S :=
  ⟨P.coroot i, Submodule.subset_span (mem_range_self i)⟩

omit [Algebra S R] in
/-
**RootPairing.rootSpanMem_reflectionPerm_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：rootSpanMem_reflectionPerm_self [Module S M] (i : ι) : P.rootSpanMem S (P.
reflectionPerm i i) = - P.rootSpanMem S i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rootSpanMem_reflectionPerm_self [Module S M] (i : ι) :
    P.rootSpanMem S (P.reflectionPerm i i) = - P.rootSpanMem S i := by
  ext; simp

omit [Algebra S R] in
/-
**RootPairing.corootSpanMem_reflectionPerm_self** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：corootSpanMem_reflectionPerm_self [Module S N] (i : ι) : P.corootSpanMem S
 (P.reflectionPerm i i) = - P.corootSpanMem S i
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用引理 `RootPairing.coreflection_apply_self`：coreflection_apply_self : P.corefle
ction i (P.coroot i) = - P.coroot i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma corootSpanMem_reflectionPerm_self [Module S N] (i : ι) :
    P.corootSpanMem S (P.reflectionPerm i i) = - P.corootSpanMem S i := by
  ext; simp

/-- The `S`-linear map on the span of coroots given by evaluating at a root. -/
/-
**RootPairing.root'In** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_4} →       {N : Type u
_5} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   (P : RootPairing
 ι R M N) →                     (S : Type u_6) →                       [inst_5 :
 CommRing S] →                         [inst_6 : Algebra S R] →                 
          [inst_7 : _root_.Module S N] →                             [IsScalarTo
wer S R N] →                               [FaithfulSMul S R] → [P.IsValuedIn S]
 → ι → Module.Dual S ↥(P.corootSpan S)
参数：P : RootPairing ι R M N；S : Type u_6；P.corootSpan S。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `S`-linear map on the span of coroots given by evaluating at a root.
-/
def root'In [Module S N] [IsScalarTower S R N] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.corootSpan S) :=
  LinearMap.restrictScalarsRange (P.corootSpan S).subtype (Algebra.linearMap S R)
    (FaithfulSMul.algebraMap_injective S R) (P.root' i)
    (fun m ↦ P.root'_apply_apply_mem_of_mem_span S m.2 i)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**RootPairing.algebraMap_root'In_apply** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Module S N]   [
inst_8 : IsScalarTower S R N] [inst_9 : FaithfulSMul S R] [inst_10 : P.IsValuedI
n S] (i : ι) (x : ↥(P.corootSpan S)),   (algebraMap S R) ((P.root'In S i) x) = (
P.root' i) ↑x
参数：P : RootPairing ι R M N；S : Type u_6；i : ι；x : ↥(P.corootSpan S)；algebraMap S
 R；(P.root'In S i) x；P.root' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.root'In.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4}
 {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_
.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.linearMap_apply`：linearMap_apply (r : R) : Algebra.linearMap R A
 r = algebraMap R A r
· 使用引理 `LinearMap.restrictScalarsRange_apply`：restrictScalarsRange_apply (m : M'
) : k (restrictScalarsRange i k hk f hf m) = f (i m)
· 使用定理 `Submodule.subtype_apply`：subtype_apply (x : p) : p.subtype x = x
-/
lemma algebraMap_root'In_apply [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.corootSpan S) :
    algebraMap S R (P.root'In S i x) = P.root' i x := by
  rw [root'In, ← Algebra.linearMap_apply, LinearMap.restrictScalarsRange_apply,
    Submodule.subtype_apply]

@[simp]
/-
**RootPairing.root'In_corootSpanMem_eq_pairingIn** 是 Mathlib 中的一个定理，位于命名空间 `Root
Pairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι) (S
 : Type u_6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Modul
e S N]   [inst_8 : IsScalarTower S R N] [inst_9 : FaithfulSMul S R] [inst_10 : P
.IsValuedIn S],   (P.root'In S i) (P.corootSpanMem S j) = P.pairingIn S i j
参数：P : RootPairing ι R M N；i j : ι；S : Type u_6；P.root'In S i；P.corootSpanMem S 
j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma root'In_corootSpanMem_eq_pairingIn [Module S N] [IsScalarTower S R N] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.root'In S i (P.corootSpanMem S j) = P.pairingIn S i j :=
  rfl

/-- The `S`-linear map on the span of roots given by evaluating at a coroot. -/
/-
**RootPairing.coroot'In** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_4} →       {N : Type u
_5} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   (P : RootPairing
 ι R M N) →                     (S : Type u_6) →                       [inst_5 :
 CommRing S] →                         [inst_6 : Algebra S R] →                 
          [inst_7 : _root_.Module S M] →                             [IsScalarTo
wer S R M] →                               [FaithfulSMul S R] → [P.IsValuedIn S]
 → ι → Module.Dual S ↥(P.rootSpan S)
参数：P : RootPairing ι R M N；S : Type u_6；P.rootSpan S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […

--- 原说明 ---
The `S`-linear map on the span of roots given by evaluating at a coroot.
-/
def coroot'In [Module S M] [IsScalarTower S R M] [FaithfulSMul S R] [P.IsValuedIn S] (i : ι) :
    Dual S (P.rootSpan S) :=
  P.flip.root'In S i

@[simp]
/-
**RootPairing.algebraMap_coroot'In_apply** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Module S M]   [
inst_8 : IsScalarTower S R M] [inst_9 : FaithfulSMul S R] [inst_10 : P.IsValuedI
n S] (i : ι) (x : ↥(P.rootSpan S)),   (algebraMap S R) ((P.coroot'In S i) x) = (
P.coroot' i) ↑x
参数：P : RootPairing ι R M N；S : Type u_6；i : ι；x : ↥(P.rootSpan S)；algebraMap S R
；(P.coroot'In S i) x；P.coroot' i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.algebraMap_root'In_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma algebraMap_coroot'In_apply [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] (i : ι) (x : P.rootSpan S) :
    algebraMap S R (P.coroot'In S i x) = P.coroot' i x :=
  P.flip.algebraMap_root'In_apply S i x

@[simp]
/-
**RootPairing.coroot'In_rootSpanMem_eq_pairingIn** 是 Mathlib 中的一个定理，位于命名空间 `Root
Pairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (i j : ι) (S
 : Type u_6) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : _root_.Modul
e S M]   [inst_8 : IsScalarTower S R M] [inst_9 : FaithfulSMul S R] [inst_10 : P
.IsValuedIn S],   (P.coroot'In S i) (P.rootSpanMem S j) = P.pairingIn S j i
参数：P : RootPairing ι R M N；i j : ι；S : Type u_6；P.coroot'In S i；P.rootSpanMem S 
j。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coroot'In_rootSpanMem_eq_pairingIn [Module S M] [IsScalarTower S R M] [FaithfulSMul S R]
    [P.IsValuedIn S] :
    P.coroot'In S i (P.rootSpanMem S j) = P.pairingIn S j i :=
  rfl

omit [Algebra S R] in
/-
**RootPairing.rootSpan_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：rootSpan_ne_bot [Module S M] [Nonempty ι] [NeZero (2 : R)] : P.rootSpan S 
!= ⊥
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `RootPairing.exists_ne_zero`：exists_ne_zero [Nonempty ι] [NeZero (2 : R)]
 : exists i, P.root i != 0
-/
lemma rootSpan_ne_bot [Module S M] [Nonempty ι] [NeZero (2 : R)] : P.rootSpan S ≠ ⊥ := by
  simpa [rootSpan] using P.exists_ne_zero

omit [Algebra S R] in
/-
**RootPairing.corootSpan_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：corootSpan_ne_bot [Module S N] [Nonempty ι] [NeZero (2 : R)] : P.corootSpa
n S != ⊥
参数：2 : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.rootSpan_ne_bot`：rootSpan_ne_bot [Module S M] [Nonempty ι] [
NeZero (2 : R)] : P.rootSpan S != ⊥
-/
lemma corootSpan_ne_bot [Module S N] [Nonempty ι] [NeZero (2 : R)] : P.corootSpan S ≠ ⊥ :=
  P.flip.rootSpan_ne_bot S
/-
**RootPairing.rootSpan_mem_invtSubmodule_reflection** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing`。
形式化陈述：rootSpan_mem_invtSubmodule_reflection (i : ι) : P.rootSpan R in Module.End
.invtSubmodule (P.reflection i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.mem_invtSubmodule`：mem_invtSubmodule {p : Submodule R M} : p 
in f.invtSubmodule ↔ p <= p.comap f
· 使用定理 `RootPairing.rootSpan.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4
} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root
_.Module R M] […
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Submodule.mem_comap`：mem_comap {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R₂ M₂
} : x in comap f p ↔ f x in p
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用引理 `RootPairing.reflection_apply_root`：reflection_apply_root : P.reflection 
i (P.root j) = P.root j - (P.pairing j i) • P.root i
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
lemma rootSpan_mem_invtSubmodule_reflection (i : ι) :
    P.rootSpan R ∈ Module.End.invtSubmodule (P.reflection i) := by
  rw [Module.End.mem_invtSubmodule, rootSpan]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    rw [Submodule.mem_comap, LinearEquiv.coe_coe, reflection_apply_root]
    apply Submodule.sub_mem
    · exact Submodule.subset_span <| mem_range_self j
    · exact Submodule.smul_mem _ _ <| Submodule.subset_span <| mem_range_self i
  | zero => simp
  | add y z hy hz hy' hz' => simpa using Submodule.add_mem _ hy' hz'
  | smul y t hy hy' => simpa using Submodule.smul_mem _ _ hy'
/-
**RootPairing.corootSpan_mem_invtSubmodule_coreflection** 是 Mathlib 中的一个引理，位于命名空
间 `RootPairing`。
形式化陈述：corootSpan_mem_invtSubmodule_coreflection (i : ι) : P.corootSpan R in Modu
le.End.invtSubmodule (P.coreflection i)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootSpan_mem_invtSubmodule_reflection`：rootSpan_mem_invtSubm
odule_reflection (i : ι) : P.rootSpan R in Module.End.invtSubmodule (P.reflectio
n i)
-/
lemma corootSpan_mem_invtSubmodule_coreflection (i : ι) :
    P.corootSpan R ∈ Module.End.invtSubmodule (P.coreflection i) :=
  P.flip.rootSpan_mem_invtSubmodule_reflection i
/-
**RootPairing.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'** 是 Mathlib 中的一个引理，
位于命名空间 `RootPairing`。
形式化陈述：rootSpan_dualAnnihilator_map_eq_iInf_ker_root' : (P.rootSpan R).dualAnnihi
lator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ[R] N) = ⨅ i, (P.root' i).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.flip_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Type 
u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _r
oot_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.toPerfPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} {N : Ty
pe u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R] 
  [inst_3 : _root_.Mo…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `Submodule.coe_dualAnnihilator_span`：coe_dualAnnihilator_span (s : Set M)
 : ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s subseteq Linear
Map.ker f}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Submodule.coe_iInf`：coe_iInf {ι} (p : ι -> Submodule R M) : (↑(⨅ i, p i)
 : Set M) = ⋂ i, ↑(p i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rootSpan_dualAnnihilator_map_eq_iInf_ker_root' :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M →ₗ[R] N) =
      ⨅ i, (P.root' i).ker :=
  SetLike.coe_injective <| by ext; simp [LinearEquiv.symm_apply_eq, subset_def]
/-
**RootPairing.corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot'** 是 Mathlib 中的一
个引理，位于命名空间 `RootPairing`。
形式化陈述：corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' : (P.corootSpan R).dual
Annihilator.map (P.toPerfPair.symm : Dual R N ->ₗ[R] M) = ⨅ i, (P.coroot' i).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'`：rootSpan_dua
lAnnihilator_map_eq_iInf_ker_root' : (P.rootSpan R).dualAnnihilator.map (P.flip.
toPerfPair.symm : Dual R M ->ₗ[R] N) = ⨅ i, (P.r…
-/
lemma corootSpan_dualAnnihilator_map_eq_iInf_ker_coroot' :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N →ₗ[R] M) =
      ⨅ i, (P.coroot' i).ker :=
  P.flip.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'
/-
**RootPairing.rootSpan_dualAnnihilator_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：rootSpan_dualAnnihilator_map_eq : (P.rootSpan R).dualAnnihilator.map (P.fl
ip.toPerfPair.symm : Dual R M ->ₗ[R] N) = (span R (range P.root')).dualCoannihil
ator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.flip_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M : Type 
u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _r
oot_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.toPerfPair.congr_simp`：∀ {R : Type u_1} {M : Type u_3} {N : Ty
pe u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R] 
  [inst_3 : _root_.Mo…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `Submodule.coe_dualAnnihilator_span`：coe_dualAnnihilator_span (s : Set M)
 : ((span R s).dualAnnihilator : Set (Module.Dual R M)) = {f | s subseteq Linear
Map.ker f}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Submodule.coe_dualCoannihilator_span`：coe_dualCoannihilator_span (s : Se
t (Module.Dual R M)) : ((span R s).dualCoannihilator : Set M) = {x | forall f in
 s, f x = 0}
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma rootSpan_dualAnnihilator_map_eq :
    (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M →ₗ[R] N) =
      (span R (range P.root')).dualCoannihilator :=
  SetLike.coe_injective <| by ext; simp [LinearEquiv.symm_apply_eq, subset_def]
/-
**RootPairing.corootSpan_dualAnnihilator_map_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：corootSpan_dualAnnihilator_map_eq : (P.corootSpan R).dualAnnihilator.map (
P.toPerfPair.symm : Dual R N ->ₗ[R] M) = (span R (range P.coroot')).dualCoannihi
lator
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.rootSpan_dualAnnihilator_map_eq`：rootSpan_dualAnnihilator_ma
p_eq : (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ
[R] N) = (span R (range P.root'))…
-/
lemma corootSpan_dualAnnihilator_map_eq :
    (P.corootSpan R).dualAnnihilator.map (P.toPerfPair.symm : Dual R N →ₗ[R] M) =
      (span R (range P.coroot')).dualCoannihilator :=
  P.flip.rootSpan_dualAnnihilator_map_eq
/-
**RootPairing.iInf_ker_root'_eq** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⨅ i, Linear
Map.ker (P.root' i) = (Submodule.span R (Set.range P.root')).dualCoannihilator
参数：P : RootPairing ι R M N；P.root' i；Submodule.span R (Set.range P.root')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.rootSpan_dualAnnihilator_map_eq`：rootSpan_dualAnnihilator_ma
p_eq : (P.rootSpan R).dualAnnihilator.map (P.flip.toPerfPair.symm : Dual R M ->ₗ
[R] N) = (span R (range P.root'))…
· 使用引理 `RootPairing.rootSpan_dualAnnihilator_map_eq_iInf_ker_root'`：rootSpan_dua
lAnnihilator_map_eq_iInf_ker_root' : (P.rootSpan R).dualAnnihilator.map (P.flip.
toPerfPair.symm : Dual R M ->ₗ[R] N) = ⨅ i, (P.r…
-/
lemma iInf_ker_root'_eq :
    ⨅ i, LinearMap.ker (P.root' i) = (span R (range P.root')).dualCoannihilator := by
  rw [← rootSpan_dualAnnihilator_map_eq, rootSpan_dualAnnihilator_map_eq_iInf_ker_root']
/-
**RootPairing.iInf_ker_coroot'_eq** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   ⨅ i, Linear
Map.ker (P.coroot' i) = (Submodule.span R (Set.range P.coroot')).dualCoannihilat
or
参数：P : RootPairing ι R M N；P.coroot' i；Submodule.span R (Set.range P.coroot')。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.iInf_ker_root'_eq`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
-/
lemma iInf_ker_coroot'_eq :
    ⨅ i, LinearMap.ker (P.coroot' i) = (span R (range P.coroot')).dualCoannihilator :=
  P.flip.iInf_ker_root'_eq
/-
**RootPairing.rootSpan_map_toPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   Submodule.m
ap (↑P.toPerfPair) (P.rootSpan R) = Submodule.span R (Set.range P.root')
参数：P : RootPairing ι R M N；↑P.toPerfPair；P.rootSpan R；Set.range P.root'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.rootSpan.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4
} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root
_.Module R M] […
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `LinearEquiv.coe_coe`：coe_coe : ⇑(e : M ->ₛₗ[σ] M₂) = e
· 使用定理 `RootPairing.toPerfPair_comp_root`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
-/
@[simp] lemma rootSpan_map_toPerfPair :
    (P.rootSpan R).map (P.toPerfPair : M →ₗ[R] Dual R N) = span R (range P.root') := by
  rw [rootSpan, Submodule.map_span, ← image_univ, ← image_comp, image_univ, LinearEquiv.coe_coe,
    toPerfPair_comp_root]
/-
**RootPairing.corootSpan_map_flip_toPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `RootPair
ing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N),   Submodule.m
ap (↑P.flip.toPerfPair) (P.corootSpan R) = Submodule.span R (Set.range P.coroot'
)
参数：P : RootPairing ι R M N；↑P.flip.toPerfPair；P.corootSpan R；Set.range P.coroot'
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.rootSpan_map_toPerfPair`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
-/
@[simp] lemma corootSpan_map_flip_toPerfPair :
    (P.corootSpan R).map (P.toLinearMap.flip.toPerfPair : N →ₗ[R] Dual R M) =
      span R (range P.coroot') :=
  P.flip.rootSpan_map_toPerfPair
/-
**RootPairing.span_root'_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [P.IsRootSys
tem], Submodule.span R (Set.range P.root') = ⊤
参数：P : RootPairing ι R M N；Set.range P.root'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearEquiv.range`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5} {M₂ :
 Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid 
M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma span_root'_eq_top [P.IsRootSystem] :
    span R (range P.root') = ⊤ := by
  simp [← rootSpan_map_toPerfPair]
/-
**RootPairing.span_coroot'_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [P.IsRootSys
tem], Submodule.span R (Set.range P.coroot') = ⊤
参数：P : RootPairing ι R M N；Set.range P.coroot'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.span_root'_eq_top`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
-/
@[simp] lemma span_coroot'_eq_top [P.IsRootSystem] :
    span R (range P.coroot') = ⊤ :=
  span_root'_eq_top P.flip
/-
**RootPairing.pairingIn_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_eq_zero_iff {S : Type*} [CommRing S] [Algebra S R] [FaithfulSMul
 S R] [P.IsValuedIn S] [IsDomain R] [Module.IsTorsionFree R M] [NeZero (2 : R)] 
{i j : ι} : P.pairingIn S i j = 0 ↔ P.pairingIn S j i = 0
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `FaithfulSMul.algebraMap_eq_zero_iff`：algebraMap_eq_zero_iff {r : R} : al
gebraMap R A r = 0 ↔ r = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.pairing_eq_zero_iff`：pairing_eq_zero_iff [NeZero (2 : R)] [I
sDomain R] [Module.IsTorsionFree R M] : P.pairing i j = 0 ↔ P.pairing j i = 0
-/
lemma pairingIn_eq_zero_iff {S : Type*} [CommRing S] [Algebra S R] [FaithfulSMul S R]
    [P.IsValuedIn S] [IsDomain R] [Module.IsTorsionFree R M] [NeZero (2 : R)] {i j : ι} :
    P.pairingIn S i j = 0 ↔ P.pairingIn S j i = 0 := by
  simpa only [← FaithfulSMul.algebraMap_eq_zero_iff S R, algebraMap_pairingIn] using
    P.pairing_eq_zero_iff

variable {P i j} in
/-
**RootPairing.reflection_apply_root'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：reflection_apply_root' (S : Type*) [CommRing S] [Algebra S R] [Module S M]
 [IsScalarTower S R M] [P.IsValuedIn S] : P.reflection i (P.root j) = P.root j -
 (P.pairingIn S j i) • P.root i
参数：S : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.reflection_apply_root`：reflection_apply_root : P.reflection 
i (P.root j) = P.root j - (P.pairing j i) • P.root i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
lemma reflection_apply_root' (S : Type*) [CommRing S] [Algebra S R]
    [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] :
    P.reflection i (P.root j) = P.root j - (P.pairingIn S j i) • P.root i := by
  rw [reflection_apply_root, ← P.algebraMap_pairingIn S, algebraMap_smul]

/-- A variant of `RootPairing.coxeterWeight` for root pairings which are valued in a smaller set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., when we have
`[FaithfulSMul S R]`. -/
/-
**RootPairing.coxeterWeightIn** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i
 j : ι) : S
参数：S : Type*；i j : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A variant of `RootPairing.coxeterWeight` for root pairings which are valued in a
 smaller set of
coefficients.

Note that it is uniquely-defined only when the map `S → R` is injective, i.e., w
hen we have
`[FaithfulSMul S R]`.
-/
def coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S] (i j : ι) : S :=
  P.pairingIn S i j * P.pairingIn S j i
/-
**RootPairing.algebraMap_coxeterWeightIn** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing`
。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   (S : Type u_
7) [inst_5 : CommRing S] [inst_6 : Algebra S R] [inst_7 : P.IsValuedIn S] (i j :
 ι),   (algebraMap S R) (P.coxeterWeightIn S i j) = P.coxeterWeight i j
参数：P : RootPairing ι R M N；S : Type u_7；i j : ι；algebraMap S R；P.coxeterWeightIn
 S i j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma algebraMap_coxeterWeightIn (S : Type*) [CommRing S] [Algebra S R] [P.IsValuedIn S]
    (i j : ι) :
    algebraMap S R (P.coxeterWeightIn S i j) = P.coxeterWeight i j := by
  simp [coxeterWeightIn, coxeterWeight]
/-
**RootPairing.toLinearMap_apply_apply_mem_range_algebraMap** 是 Mathlib 中的一个引理，位于
命名空间 `RootPairing`。
形式化陈述：toLinearMap_apply_apply_mem_range_algebraMap [P.IsValuedIn S] [Module S M]
 [Module S N] [IsScalarTower S R M] [IsScalarTower S R N] (x : M) (hx : x in P.r
ootSpan S) (y : N) (hy : y in P.corootSpan S) : P.toLinearMap x y in (algebraMap
 S R).range
参数：x : M；hx : x in P.rootSpan S；y : N；hy : y in P.corootSpan S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinMap.apply_apply_mem_of_mem_span`：∀ {R : Type u_9} {M : Ty
pe u_10} {N : Type u_11} {P : Type u_12} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M]   [inst_2 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.restrictScalarsₗ_apply`：∀ (R : Type u_14) (S : Type u_15) (M :
 Type u_16) (N : Type u_17) [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 
: AddCommMonoid M] [in…
· 使用定理 `RootPairing.exists_value`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_4}
 {N : Type u_5} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _root_
.Module R M} {…
-/
lemma toLinearMap_apply_apply_mem_range_algebraMap [P.IsValuedIn S]
    [Module S M] [Module S N] [IsScalarTower S R M] [IsScalarTower S R N]
    (x : M) (hx : x ∈ P.rootSpan S) (y : N) (hy : y ∈ P.corootSpan S) :
    P.toLinearMap x y ∈ (algebraMap S R).range :=
  LinearMap.BilinMap.apply_apply_mem_of_mem_span
    (LinearMap.range (Algebra.linearMap S R)) (range P.root) (range P.coroot)
    (LinearMap.restrictScalarsₗ S R _ _ _ ∘ₗ P.toLinearMap.restrictScalars S)
    (by simpa using RootPairing.exists_value) x y hx hy

section Field

variable (K : Type*) {L : Type*} [Field K] [Field L] [Algebra K L]
  [Module L M] [Module L N] [Module K M] [Module K N] [IsScalarTower K L M] [IsScalarTower K L N]
  (Q : RootPairing ι L M N) [Q.IsRootSystem]

@[simp]
/-
**RootPairing.finrank_rootSpanIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_rootSpanIn [Q.IsValuedIn K] : finrank K (Q.rootSpan K) = finrank L
 M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.finrank_eq_of_isPerfPair`：finrank_eq_of_isPerfPair (M' : Submo
dule K M) (N' : Submodule K N) (hM : span L (M' : Set M) = ⊤) (hN : span L (N' :
 Set N) = ⊤) (hp : foral…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `RootPairing.IsRootSystem.span_root_eq_top`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}  
 {inst_2 : _root_.Module R M} {…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.IsRootSystem.span_coroot_eq_top`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用引理 `RootPairing.toLinearMap_apply_apply_mem_range_algebraMap`：toLinearMap_ap
ply_apply_mem_range_algebraMap [P.IsValuedIn S] [Module S M] [Module S N] [IsSca
larTower S R M] [IsScalarTower S R N] (x : M) …
-/
lemma finrank_rootSpanIn [Q.IsValuedIn K] :
    finrank K (Q.rootSpan K) = finrank L M := by
  rw [LinearMap.finrank_eq_of_isPerfPair Q.toLinearMap (Q.rootSpan K) (Q.corootSpan K)]
  · simp
  · simp
  · exact Q.toLinearMap_apply_apply_mem_range_algebraMap K

@[simp]
/-
**RootPairing.finrank_corootSpanIn** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_corootSpanIn [Q.IsValuedIn K] : finrank K (Q.corootSpan K) = finra
nk L N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.finrank_rootSpanIn`：finrank_rootSpanIn [Q.IsValuedIn K] : fi
nrank K (Q.rootSpan K) = finrank L M
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma finrank_corootSpanIn [Q.IsValuedIn K] :
    finrank K (Q.corootSpan K) = finrank L N :=
  finrank_rootSpanIn K Q.flip

@[simp]
/-
**RootPairing.finrank_rootSpanIn_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_rootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] : fi
nrank Int (Q.rootSpan Int) = finrank L M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.finrank_span_eq_finrank_span`：finrank_span_eq_finrank_span [Is
PrincipalIdealRing R] [IsDomain R] [IsTorsionFree R M] (s : Set M) [Module.Finit
e R (span R s)] : finrank A …
· 使用定理 `Algebra.instIsEpiOfIsDomainOfIsFractionRing`：∀ (R : Type u_1) (A : Type 
u_2) [inst : CommRing R] [IsDomain R] [inst_2 : Field A] [inst_3 : Algebra R A] 
  [IsFractionRing R A], Algebra.I…
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `instIsAddTorsionFreeOfAddLeftStrictMonoOfAddRightStrictMono`：∀ {M : Type
 u_3} [inst : AddMonoid M] [inst_1 : LinearOrder M] [AddLeftStrictMono M] [AddRi
ghtStrictMono M],   IsAddTorsionFree M
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `RootPairing.instFiniteSubtypeMemSubmoduleRootSpanOfFinite`：∀ {ι : Type u
_1} {R : Type u_2} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : A
ddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用引理 `RootPairing.finrank_rootSpanIn`：finrank_rootSpanIn [Q.IsValuedIn K] : fi
nrank K (Q.rootSpan K) = finrank L M
（共 31 条，此处仅展示前 30 条）
-/
lemma finrank_rootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] :
    finrank ℤ (Q.rootSpan ℤ) = finrank L M := by
  let _i : Module ℚ M := .compHom M (algebraMap ℚ L)
  let _i : Module ℚ N := .compHom N (algebraMap ℚ L)
  have _i : IsAddTorsionFree M := .of_isTorsionFree L M
  rw [← Submodule.finrank_span_eq_finrank_span ℤ ℚ, ← Q.finrank_rootSpanIn ℚ]

@[simp]
/-
**RootPairing.finrank_corootSpanIn_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：finrank_corootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] : 
finrank Int (Q.corootSpan Int) = finrank L N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.finrank_rootSpanIn_int`：finrank_rootSpanIn_int [Finite ι] [C
harZero L] [Q.IsCrystallographic] : finrank Int (Q.rootSpan Int) = finrank L M
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
· 使用定理 `RootPairing.instIsValuedInFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
-/
lemma finrank_corootSpanIn_int [Finite ι] [CharZero L] [Q.IsCrystallographic] :
    finrank ℤ (Q.corootSpan ℤ) = finrank L N :=
  Q.flip.finrank_rootSpanIn_int

end Field

end RootPairing

