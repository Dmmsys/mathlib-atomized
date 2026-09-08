/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas

/-!
# Properties of the `𝔤₂` root system.

The `𝔤₂` root pairing is special enough to deserve its own API. We provide one in this file.

As an application we prove the key result that a crystallographic, reduced, irreducible root
pairing containing two roots of Coxeter weight three is spanned by this pair of roots (and thus
is two-dimensional). This result is usually proved only for pairs of roots belonging to a base (as a
corollary of the fact that no node can have degree greater than three) and moreover usually requires
stronger assumptions on the coefficients than here.

## Main results:
* `RootPairing.EmbeddedG2`: a data-bearing typeclass which distinguishes a pair of roots whose
  pairing is `-3` (equivalently, with a distinguished choice of base). This is a sufficient
  condition for the span of this pair of roots to be a `𝔤₂` root system.
* `RootPairing.IsG2`: a prop-valued typeclass characterising the `𝔤₂` root system.
* `RootPairing.IsNotG2`: a prop-valued typeclass stating that a crystallographic, reduced,
  irreducible root system is not `𝔤₂`.
* `RootPairing.EmbeddedG2.shortRoot`: the distinguished short root, which we often donate `α`
* `RootPairing.EmbeddedG2.longRoot`: the distinguished long root, which we often donate `β`
* `RootPairing.EmbeddedG2.shortAddLong`: the short root `α + β`
* `RootPairing.EmbeddedG2.twoShortAddLong`: the short root `2α + β`
* `RootPairing.EmbeddedG2.threeShortAddLong`: the long root `3α + β`
* `RootPairing.EmbeddedG2.threeShortAddTwoLong`: the long root `3α + 2β`
* `RootPairing.EmbeddedG2.span_eq_top`: a crystallographic reduced irreducible root pairing
  containing two roots with pairing `-3` is spanned by this pair (thus two-dimensional).
* `RootPairing.EmbeddedG2.card_index_eq_twelve`: the `𝔤₂` root pairing has twelve roots.

## TODO
Once sufficient API for `RootPairing.Base` has been developed:
* Add `def EmbeddedG2.toBase [P.EmbeddedG2] : P.Base` with `support := {long P, short P}`
* Given `P` satisfying `[P.IsG2]`, distinct elements of a base must pair to `-3` (in one order).

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule
open List hiding mem_toFinset

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N)

namespace RootPairing

/-- A data-bearing typeclass which distinguishes a pair of roots whose pairing is `-3`. This is a
sufficient condition for the span of this pair of roots to be a `𝔤₂` root system. -/
/-
**RootPairing.EmbeddedG2** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A data-bearing typeclass which distinguishes a pair of roots whose pairing is `-
3`. This is a
sufficient condition for the span of this pair of roots to be a `𝔤₂` root system
.
-/
class EmbeddedG2 extends P.IsCrystallographic, P.IsReduced where
  /-- The distinguished long root of an embedded `𝔤₂` root pairing. -/
  long : ι
  /-- The distinguished short root of an embedded `𝔤₂` root pairing. -/
  short : ι
  pairingIn_long_short : P.pairingIn ℤ long short = -3

/-- A prop-valued typeclass characterising the `𝔤₂` root system. -/
/-
**RootPairing.IsG2** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prop-valued typeclass characterising the `𝔤₂` root system.
-/
class IsG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  exists_pairingIn_neg_three : ∃ i j, P.pairingIn ℤ i j = -3

/-- A prop-valued typeclass stating that a crystallographic, reduced, irreducible root system is not
`𝔤₂`. -/
/-
**RootPairing.IsNotG2** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prop-valued typeclass stating that a crystallographic, reduced, irreducible ro
ot system is not
`𝔤₂`.
-/
class IsNotG2 : Prop extends P.IsCrystallographic, P.IsReduced, P.IsIrreducible where
  pairingIn_mem_zero_one_two (i j : ι) : P.pairingIn ℤ i j ∈ ({-2, -1, 0, 1, 2} : Set ℤ)

section IsG2

/-- By making an arbitrary choice of roots pairing to `-3`, we can obtain an embedded `𝔤₂` root
system just from the knowledge that such a pairs exists. -/
@[instance_reducible]
/-
**RootPairing.IsG2.toEmbeddedG2** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.IsG2`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] → (P : RootPairing ι R M N) → [P.IsG
2] → P.EmbeddedG2
参数：P : RootPairing ι R M N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _
root_.Module R M} {…
· 使用定理 `RootPairing.IsG2.toIsReduced`：∀ {ι : Type u_1} {R : Type u_2} {M : Type 
u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _r
oot_.Module R M} {…
· 使用定理 `RootPairing.IsG2.exists_pairingIn_neg_three`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…

--- 原说明 ---
By making an arbitrary choice of roots pairing to `-3`, we can obtain an embedde
d `𝔤₂` root
system just from the knowledge that such a pairs exists.
-/
def IsG2.toEmbeddedG2 [P.IsG2] : P.EmbeddedG2 where
  long := (IsG2.exists_pairingIn_neg_three (P := P)).choose
  short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose
  pairingIn_long_short := (IsG2.exists_pairingIn_neg_three (P := P)).choose_spec.choose_spec
/-
**RootPairing.IsG2.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.IsG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [P.IsG2], No
nempty ι
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _
root_.Module R M} {…
· 使用定理 `RootPairing.IsG2.exists_pairingIn_neg_three`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
-/
lemma IsG2.nonempty [P.IsG2] : Nonempty ι :=
  ⟨(IsG2.exists_pairingIn_neg_three (P := P)).choose⟩

variable [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
/-
**RootPairing.isG2_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isG2_iff : P.IsG2 ↔ exists i j, P.pairingIn Int i j = -3
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsG2.exists_pairingIn_neg_three`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
-/
lemma isG2_iff :
    P.IsG2 ↔ ∃ i j, P.pairingIn ℤ i j = -3 :=
  ⟨fun _ ↦ IsG2.exists_pairingIn_neg_three, fun h ↦ ⟨h⟩⟩
/-
**RootPairing.isNotG2_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isNotG2_iff : P.IsNotG2 ↔ forall i j, P.pairingIn Int i j in ({-2, -1, 0, 
1, 2} : Set Int)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsNotG2.pairingIn_mem_zero_one_two`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup
 M}   {inst_2 : _root_.Module R M} {…
-/
lemma isNotG2_iff :
    P.IsNotG2 ↔ ∀ i j, P.pairingIn ℤ i j ∈ ({-2, -1, 0, 1, 2} : Set ℤ) :=
  ⟨fun _ ↦ IsNotG2.pairingIn_mem_zero_one_two, fun h ↦ ⟨h⟩⟩

variable [Finite ι] [CharZero R] [IsDomain R]

@[simp]
/-
**RootPairing.not_isG2_iff_isNotG2** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：not_isG2_iff_isNotG2 : ¬ P.IsG2 ↔ P.IsNotG2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_left`：pairingIn_reflectionPerm
_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S (P.refl
ectionPerm i i) j = - P.pairingIn S …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma not_isG2_iff_isNotG2 :
    ¬ P.IsG2 ↔ P.IsNotG2 := by
  simp only [isG2_iff, isNotG2_iff, not_exists, Set.mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h i j ↦ ?_, fun h i j ↦ ?_⟩
  · have hij := h (P.reflectionPerm i i) j
    have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
    aesop
  · specialize h i j
    lia

set_option linter.overlappingInstances false in
/-
**RootPairing.IsG2.pairingIn_mem_zero_one_three** 是 Mathlib 中的一个定理，位于命名空间 `RootP
airing.IsG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
IsCrystallographic] [P.IsReduced] [P.IsIrreducible] [Finite ι] [CharZero R] [IsD
omain R] [P.IsG2]   (i j : ι), P.root i ≠ P.root j → P.root i ≠ -P.root j → P.pa
iringIn ℤ i j ∈ {-3, -1, 0, 1, 3}
参数：P : RootPairing ι R M N；i j : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _
root_.Module R M} {…
· 使用定理 `RootPairing.IsG2.exists_pairingIn_neg_three`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用引理 `RootPairing.forall_pairingIn_eq_swap_or`：forall_pairingIn_eq_swap_or [P.
IsReduced] [P.IsIrreducible] : (forall i j, P.pairingIn Int i j = P.pairingIn In
t j i ∨ P.pairingIn Int i j =…
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'`：pairingI
n_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced] (hij : α i != α j) (hij
' : α i != -α j) : (P.pairingIn Int i j, P.pairingIn…
-/
lemma IsG2.pairingIn_mem_zero_one_three [P.IsG2]
    (i j : ι) (h : P.root i ≠ P.root j) (h' : P.root i ≠ -P.root j) :
    P.pairingIn ℤ i j ∈ ({-3, -1, 0, 1, 3} : Set ℤ) := by
  suffices ¬ (∀ i j, P.pairingIn ℤ i j = P.pairingIn ℤ j i ∨
                     P.pairingIn ℤ i j = 2 * P.pairingIn ℤ j i ∨
                     P.pairingIn ℤ j i = 2 * P.pairingIn ℤ i j) by
    have aux₁ := P.forall_pairingIn_eq_swap_or.resolve_left this i j
    have aux₂ := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i j h h'
    simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_eq_zero,
      Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at aux₂ ⊢
    lia
  obtain ⟨k, l, hkl⟩ := exists_pairingIn_neg_three (P := P)
  push Not
  refine ⟨k, l, ?_⟩
  have aux := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed k l
  simp only [mem_insert_iff, mem_singleton_iff, Prod.mk_zero_zero, Prod.mk_eq_zero,
      Prod.mk_one_one, Prod.mk_eq_one, Prod.mk.injEq] at aux
  omega

end IsG2

section IsNotG2

variable {P}
variable [Finite ι] [CharZero R] [IsDomain R] {i j : ι}

variable (i j) in
/-
**RootPairing.chainBotCoeff_add_chainTopCoeff_le_two** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：chainBotCoeff_add_chainTopCoeff_le_two [P.IsNotG2] : P.chainBotCoeff i j +
 P.chainTopCoeff i j <= 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsNotG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `RootPairing.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx`：ch
ainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx : P.chainBotCoeff i j + P
.chainTopCoeff i j = P.pairingIn Int (P.chainTopIdx i j) i
· 使用定理 `RootPairing.IsNotG2.pairingIn_mem_zero_one_two`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup
 M}   {inst_2 : _root_.Module R M} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.chainBotCoeff_of_not_linearIndependent`：chainBotCoeff_of_not
_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) : P.chainBo
tCoeff i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `RootPairing.chainTopCoeff_of_not_linearIndependent`：chainTopCoeff_of_not
_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) : P.chainTo
pCoeff i j = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma chainBotCoeff_add_chainTopCoeff_le_two [P.IsNotG2] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 2 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := IsNotG2.pairingIn_mem_zero_one_two (P := P) (P.chainTopIdx i j) i
  aesop

/-- For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if the sum of two
roots is a root, they cannot make an acute angle.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base. Then the roots
`α + β` and `2α + β` make an angle `π / 3` even though `3α + 2β` is a root. We can even witness as:
```lean
example (P : RootPairing ι R M N) [P.EmbeddedG2] :
    P.pairingIn ℤ (EmbeddedG2.shortAddLong P) (EmbeddedG2.twoShortAddLong P) = 1 := by
  simp
```
-/
/-
**RootPairing.pairingIn_le_zero_of_root_add_mem** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：pairingIn_le_zero_of_root_add_mem [P.IsNotG2] (h : P.root i + P.root j in 
range P.root) : P.pairingIn Int i j <= 0
参数：h : P.root i + P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.linearIndependent_of_add_mem_range_root'`：linearIndependent_
of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι} (h : P.
root i + P.root j in range P.root) : Linea…
· 使用定理 `RootPairing.IsNotG2.toIsReduced`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 :
 _root_.Module R M} {…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `RootPairing.IsNotG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用引理 `RootPairing.chainBotCoeff_add_chainTopCoeff_le_two`：chainBotCoeff_add_ch
ainTopCoeff_le_two [P.IsNotG2] : P.chainBotCoeff i j + P.chainTopCoeff i j <= 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff`：root_add_nsmu
l_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P.root i in range P.
root ↔ n <= P.chainTopCoeff i j
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `RootPairing.chainBotCoeff_sub_chainTopCoeff`：chainBotCoeff_sub_chainTopC
oeff : P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn Int j i

--- 原说明 ---
For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if th
e sum of two
roots is a root, they cannot make an acute angle.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base.
 Then the roots
`α + β` and `2α + β` make an angle `π / 3` even though `3α + 2β` is a root. We c
an even witness as:
```lean
example (P : RootPairing ι R M N) [P.EmbeddedG2] :
    P.pairingIn ℤ (EmbeddedG2.shortAddLong P) (EmbeddedG2.twoShortAddLong P) = 1
 := by
  simp
```
-/
lemma pairingIn_le_zero_of_root_add_mem [P.IsNotG2] (h : P.root i + P.root j ∈ range P.root) :
    P.pairingIn ℤ i j ≤ 0 := by
  have aux₁ := P.linearIndependent_of_add_mem_range_root' <| add_comm (P.root i) (P.root j) ▸ h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two j i
  have aux₃ : 1 ≤ P.chainTopCoeff j i := by
    rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff aux₁, one_smul]
  rw [← P.chainBotCoeff_sub_chainTopCoeff aux₁]
  lia
/-
**RootPairing.zero_le_pairingIn_of_root_sub_mem** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：zero_le_pairingIn_of_root_sub_mem [P.IsNotG2] (h : P.root i - P.root j in 
range P.root) : 0 <= P.pairingIn Int i j
参数：h : P.root i - P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `RootPairing.IsNotG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.pairingIn_le_zero_of_root_add_mem`：pairingIn_le_zero_of_root
_add_mem [P.IsNotG2] (h : P.root i + P.root j in range P.root) : P.pairingIn Int
 i j <= 0
-/
lemma zero_le_pairingIn_of_root_sub_mem [P.IsNotG2] (h : P.root i - P.root j ∈ range P.root) :
    0 ≤ P.pairingIn ℤ i j := by
  replace h : P.root i + P.root (P.reflectionPerm j j) ∈ range P.root := by simpa [← sub_eq_add_neg]
  simpa using P.pairingIn_le_zero_of_root_add_mem h

/-- For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if the sum of two
roots is a root, the bottom chain coefficient is either one or zero according to whether they are
perpendicular.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base. Then the roots
`α` and `α + β` provide a counterexample. -/
/-
**RootPairing.chainBotCoeff_if_one_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_if_one_zero [P.IsNotG2] (h : P.root i + P.root j in range P.
root) : P.chainBotCoeff i j = if P.pairingIn Int i j = 0 then 1 else 0
参数：h : P.root i + P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `RootPairing.linearIndependent_of_add_mem_range_root'`：linearIndependent_
of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι} (h : P.
root i + P.root j in range P.root) : Linea…
· 使用定理 `RootPairing.IsNotG2.toIsReduced`：∀ {ι : Type u_1} {R : Type u_2} {M : Ty
pe u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 :
 _root_.Module R M} {…
· 使用定理 `RootPairing.IsNotG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用引理 `RootPairing.chainBotCoeff_add_chainTopCoeff_le_two`：chainBotCoeff_add_ch
ainTopCoeff_le_two [P.IsNotG2] : P.chainBotCoeff i j + P.chainTopCoeff i j <= 2
· 使用引理 `RootPairing.one_le_chainTopCoeff_of_root_add_mem`：one_le_chainTopCoeff_o
f_root_add_mem [P.IsReduced] (h : P.root i + P.root j in range P.root) : 1 <= P.
chainTopCoeff i j
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `RootPairing.pairingIn_eq_zero_iff`：pairingIn_eq_zero_iff {S : Type*} [Co
mmRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] [IsDomain R] [Module
.IsTorsionFree R M] [Ne…
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.chainBotCoeff_sub_chainTopCoeff`：chainBotCoeff_sub_chainTopC
oeff : P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn Int j i
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b

--- 原说明 ---
For a reduced, crystallographic, irreducible root pairing other than `𝔤₂`, if th
e sum of two
roots is a root, the bottom chain coefficient is either one or zero according to
 whether they are
perpendicular.

To see that this lemma fails for `𝔤₂`, let `α` (short) and `β` (long) be a base.
 Then the roots
`α` and `α + β` provide a counterexample.
-/
lemma chainBotCoeff_if_one_zero [P.IsNotG2] (h : P.root i + P.root j ∈ range P.root) :
    P.chainBotCoeff i j = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have aux₁ := P.linearIndependent_of_add_mem_range_root' h
  have aux₂ := P.chainBotCoeff_add_chainTopCoeff_le_two i j
  have aux₃ : 1 ≤ P.chainTopCoeff i j := P.one_le_chainTopCoeff_of_root_add_mem h
  rcases eq_or_ne (P.chainBotCoeff i j) (P.chainTopCoeff i j) with aux₄ | aux₄ <;>
  simp_rw [P.pairingIn_eq_zero_iff (i := i) (j := j), ← P.chainBotCoeff_sub_chainTopCoeff aux₁,
    sub_eq_zero, Nat.cast_inj, aux₄, reduceIte] <;>
  lia
/-
**RootPairing.chainTopCoeff_if_one_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_if_one_zero [P.IsNotG2] (h : P.root i - P.root j in range P.
root) : P.chainTopCoeff i j = if P.pairingIn Int i j = 0 then 1 else 0
参数：h : P.root i - P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `RootPairing.IsNotG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.chainBotCoeff_reflectionPerm_right`：chainBotCoeff_reflection
Perm_right : P.chainBotCoeff i (P.reflectionPerm j j) = P.chainTopCoeff i j
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.chainBotCoeff_if_one_zero`：chainBotCoeff_if_one_zero [P.IsNo
tG2] (h : P.root i + P.root j in range P.root) : P.chainBotCoeff i j = if P.pair
ingIn Int i j = 0 then 1 el…
-/
lemma chainTopCoeff_if_one_zero [P.IsNotG2] (h : P.root i - P.root j ∈ range P.root) :
    P.chainTopCoeff i j = if P.pairingIn ℤ i j = 0 then 1 else 0 := by
  let := P.indexNeg
  replace h : P.root i + P.root (-j) ∈ range P.root := by simpa [← sub_eq_add_neg] using h
  simpa using P.chainBotCoeff_if_one_zero h

end IsNotG2

namespace EmbeddedG2

/-- A pair of roots which pair to `+3` are also sufficient to distinguish an embedded `𝔤₂`. -/
@[simps, instance_reducible]
/-
**RootPairing.EmbeddedG2.ofPairingInThree** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing
.EmbeddedG2`。
形式化陈述：ofPairingInThree [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long s
hort : ι) (h : P.pairingIn Int long short = 3) : P.EmbeddedG2 where long
参数：long short : ι；h : P.pairingIn Int long short = 3。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pair of roots which pair to `+3` are also sufficient to distinguish an embedde
d `𝔤₂`.
-/
def ofPairingInThree [CharZero R] [P.IsCrystallographic] [P.IsReduced] (long short : ι)
    (h : P.pairingIn ℤ long short = 3) : P.EmbeddedG2 where
  long := P.reflectionPerm long long
  short := short
  pairingIn_long_short := by simp [h]

variable [P.EmbeddedG2]

attribute [simp] pairingIn_long_short
/-
**RootPairing.EmbeddedG2.** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing.EmbeddedG2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsIrreducible] : P.IsG2 where
  exists_pairingIn_neg_three := ⟨long P, short P, by simp⟩

@[simp]
/-
**RootPairing.EmbeddedG2.pairing_long_short** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.EmbeddedG2`。
形式化陈述：pairing_long_short : P.pairing (long P) (short P) = -3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_long_short`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_long_short : P.pairing (long P) (short P) = -3 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_long_short]
  simp

/-- The index of the root `α + β` where `α` is the short root and `β` is the long root. -/
/-
**RootPairing.EmbeddedG2.shortAddLong** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Emb
eddedG2`。
形式化陈述：shortAddLong : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index of the root `α + β` where `α` is the short root and `β` is the long ro
ot.
-/
def shortAddLong : ι := P.reflectionPerm (long P) (short P)

/-- The index of the root `2α + β` where `α` is the short root and `β` is the long root. -/
/-
**RootPairing.EmbeddedG2.twoShortAddLong** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.
EmbeddedG2`。
形式化陈述：twoShortAddLong : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index of the root `2α + β` where `α` is the short root and `β` is the long r
oot.
-/
def twoShortAddLong : ι := P.reflectionPerm (short P) <| P.reflectionPerm (long P) (short P)

/-- The index of the root `3α + β` where `α` is the short root and `β` is the long root. -/
/-
**RootPairing.EmbeddedG2.threeShortAddLong** 是 Mathlib 中的一个定义，位于命名空间 `RootPairin
g.EmbeddedG2`。
形式化陈述：threeShortAddLong : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index of the root `3α + β` where `α` is the short root and `β` is the long r
oot.
-/
def threeShortAddLong : ι := P.reflectionPerm (short P) (long P)

/-- The index of the root `3α + 2β` where `α` is the short root and `β` is the long root. -/
/-
**RootPairing.EmbeddedG2.threeShortAddTwoLong** 是 Mathlib 中的一个定义，位于命名空间 `RootPai
ring.EmbeddedG2`。
形式化陈述：threeShortAddTwoLong : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The index of the root `3α + 2β` where `α` is the short root and `β` is the long 
root.
-/
def threeShortAddTwoLong : ι := P.reflectionPerm (long P) <| P.reflectionPerm (short P) (long P)

/-- The short root `α`. -/
/-
**RootPairing.EmbeddedG2.shortRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.Embe
ddedG2`。
形式化陈述：shortRoot
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short root `α`.
-/
abbrev shortRoot := P.root (short P)

/-- The long root `β`. -/
/-
**RootPairing.EmbeddedG2.longRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.Embed
dedG2`。
形式化陈述：longRoot
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The long root `β`.
-/
abbrev longRoot := P.root (long P)

/-- The short root `α + β`. -/
/-
**RootPairing.EmbeddedG2.shortAddLongRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairi
ng.EmbeddedG2`。
形式化陈述：shortAddLongRoot : M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short root `α + β`.
-/
abbrev shortAddLongRoot : M := P.root (shortAddLong P)

/-- The short root `2α + β`. -/
/-
**RootPairing.EmbeddedG2.twoShortAddLongRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPa
iring.EmbeddedG2`。
形式化陈述：twoShortAddLongRoot : M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short root `2α + β`.
-/
abbrev twoShortAddLongRoot : M := P.root (twoShortAddLong P)

/-- The short root `3α + β`. -/
/-
**RootPairing.EmbeddedG2.threeShortAddLongRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `Root
Pairing.EmbeddedG2`。
形式化陈述：threeShortAddLongRoot : M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short root `3α + β`.
-/
abbrev threeShortAddLongRoot : M := P.root (threeShortAddLong P)

/-- The short root `3α + 2β`. -/
/-
**RootPairing.EmbeddedG2.threeShortAddTwoLongRoot** 是 Mathlib 中的一个缩写定义，位于命名空间 `R
ootPairing.EmbeddedG2`。
形式化陈述：threeShortAddTwoLongRoot : M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The short root `3α + 2β`.
-/
abbrev threeShortAddTwoLongRoot : M := P.root (threeShortAddTwoLong P)

/-- The list of all 12 roots belonging to the embedded `𝔤₂`. -/
/-
**RootPairing.EmbeddedG2.allRoots** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.Embed
dedG2`。
形式化陈述：allRoots : List M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list of all 12 roots belonging to the embedded `𝔤₂`.
-/
abbrev allRoots : List M :=
  [ longRoot P, -longRoot P,
    shortRoot P, -shortRoot P,
    shortAddLongRoot P, -shortAddLongRoot P,
    twoShortAddLongRoot P, -twoShortAddLongRoot P,
    threeShortAddLongRoot P, -threeShortAddLongRoot P,
    threeShortAddTwoLongRoot P, -threeShortAddTwoLongRoot P ]
/-
**RootPairing.EmbeddedG2.allRoots_subset_range_root** 是 Mathlib 中的一个引理，位于命名空间 `R
ootPairing.EmbeddedG2`。
形式化陈述：allRoots_subset_range_root [DecidableEq M] : ↑(allRoots P).toFinset subset
eq range P.root
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.toFinset_cons`：toFinset_cons : toFinset (a :: l) = insert a (toFins
et l)
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma allRoots_subset_range_root [DecidableEq M] :
    ↑(allRoots P).toFinset ⊆ range P.root := by
  intro x hx
  simp only [toFinset_cons, toFinset_nil, insert_empty_eq, Finset.coe_insert,
    Finset.coe_singleton, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

variable [Finite ι] [CharZero R] [IsDomain R]

@[simp]
/-
**RootPairing.EmbeddedG2.pairingIn_short_long** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.EmbeddedG2`。
形式化陈述：pairingIn_short_long : P.pairingIn Int (short P) (long P) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `RootPairing.EmbeddedG2.toIsReduced`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_
2 : _root_.Module R M} {…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_long_short`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma pairingIn_short_long :
    P.pairingIn ℤ (short P) (long P) = -1 := by
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed (long P) (short P)
  aesop

@[simp]
/-
**RootPairing.EmbeddedG2.pairing_short_long** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng.EmbeddedG2`。
形式化陈述：pairing_short_long : P.pairing (short P) (long P) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用引理 `RootPairing.EmbeddedG2.pairingIn_short_long`：pairingIn_short_long : P.pa
iringIn Int (short P) (long P) = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pairing_short_long :
    P.pairing (short P) (long P) = -1 := by
  rw [← P.algebraMap_pairingIn ℤ, pairingIn_short_long]
  simp
/-
**RootPairing.EmbeddedG2.shortAddLongRoot_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.EmbeddedG2`。
形式化陈述：shortAddLongRoot_eq : shortAddLongRoot P = shortRoot P + longRoot P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.EmbeddedG2.pairing_short_long`：pairing_short_long : P.pairin
g (short P) (long P) = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shortAddLongRoot_eq :
    shortAddLongRoot P = shortRoot P + longRoot P := by
  simp [shortAddLongRoot, shortAddLong, reflection_apply_root]
/-
**RootPairing.EmbeddedG2.twoShortAddLongRoot_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.EmbeddedG2`。
形式化陈述：twoShortAddLongRoot_eq : twoShortAddLongRoot P = (2 : R) • shortRoot P + l
ongRoot P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.EmbeddedG2.pairing_short_long`：pairing_short_long : P.pairin
g (short P) (long P) = -1
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用引理 `RootPairing.EmbeddedG2.pairing_long_short`：pairing_long_short : P.pairin
g (long P) (short P) = -3
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
（共 59 条，此处仅展示前 30 条）
-/
lemma twoShortAddLongRoot_eq :
    twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P := by
  simp [twoShortAddLongRoot, twoShortAddLong, reflection_apply_root]
  module

omit [Finite ι] [CharZero R] [IsDomain R] in
/-
**RootPairing.EmbeddedG2.threeShortAddLongRoot_eq** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing.EmbeddedG2`。
形式化陈述：threeShortAddLongRoot_eq : threeShortAddLongRoot P = (3 : R) • shortRoot P
 + longRoot P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.EmbeddedG2.pairing_long_short`：pairing_long_short : P.pairin
g (long P) (short P) = -3
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 35 条，此处仅展示前 30 条）
-/
lemma threeShortAddLongRoot_eq :
    threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P := by
  simp [threeShortAddLongRoot, threeShortAddLong, reflection_apply_root]
  module
/-
**RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.EmbeddedG2`。
形式化陈述：threeShortAddTwoLongRoot_eq : threeShortAddTwoLongRoot P = (3 : R) • short
Root P + (2 : R) • longRoot P
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.EmbeddedG2.pairing_long_short`：pairing_long_short : P.pairin
g (long P) (short P) = -3
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.EmbeddedG2.pairing_short_long`：pairing_short_long : P.pairin
g (short P) (long P) = -1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.neg_eq_eval`：neg_eq_eval [AddCommGroup M] [Semi
ring S] [Module S M] [Ring R] [Module R M] {l : NF R M} {l₀ : NF S M} (hl : l.ev
al = l₀.eval) {x : M} (h :…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 61 条，此处仅展示前 30 条）
-/
lemma threeShortAddTwoLongRoot_eq :
    threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoot P := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong, reflection_apply_root]
  module
/-
**RootPairing.EmbeddedG2.linearIndependent_short_long** 是 Mathlib 中的一个引理，位于命名空间 
`RootPairing.EmbeddedG2`。
形式化陈述：linearIndependent_short_long : LinearIndependent R ![shortRoot P, longRoot
 P]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`：linearIndepen
dent_iff_coxeterWeightIn_ne_four : LinearIndependent R ![P.root i, P.root j] ↔ P
.coxeterWeightIn S i j != 4
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.EmbeddedG2.pairingIn_short_long`：pairingIn_short_long : P.pa
iringIn Int (short P) (long P) = -1
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_long_short`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}
   {inst_2 : _root_.Module R M} {…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma linearIndependent_short_long :
    LinearIndependent R ![shortRoot P, longRoot P] := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  simp [P.linearIndependent_iff_coxeterWeightIn_ne_four ℤ, coxeterWeightIn]

/-- The coefficients of each root in the `𝔤₂` root pairing, relative to the base. -/
/-
**RootPairing.EmbeddedG2.allCoeffs** 是 Mathlib 中的一个缩写定义，位于命名空间 `RootPairing.Embe
ddedG2`。
形式化陈述：allCoeffs : List (Fin 2 -> Int)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coefficients of each root in the `𝔤₂` root pairing, relative to the base.
-/
abbrev allCoeffs : List (Fin 2 → ℤ) :=
  [![0, 1], ![0, -1], ![1, 0], ![-1, 0], ![1, 1], ![-1, -1],
    ![2, 1], ![-2, -1], ![3, 1], ![-3, -1], ![3, 2], ![-3, -2]]
/-
**RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.EmbeddedG2`。
形式化陈述：allRoots_eq_map_allCoeffs : allRoots P = allCoeffs.map (Fintype.linearComb
ination Int ![shortRoot P, longRoot P])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Fin.sum_univ_two`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 2 →
 M), ∑ i, f i = f 0 + f 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.EmbeddedG2.shortAddLongRoot_eq`：shortAddLongRoot_eq : shortA
ddLongRoot P = shortRoot P + longRoot P
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用引理 `RootPairing.EmbeddedG2.twoShortAddLongRoot_eq`：twoShortAddLongRoot_eq : 
twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddLongRoot_eq`：threeShortAddLongRoot_e
q : threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq`：threeShortAddTwoLong
Root_eq : threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoo
t P
（共 31 条，此处仅展示前 30 条）
-/
lemma allRoots_eq_map_allCoeffs :
    allRoots P = allCoeffs.map (Fintype.linearCombination ℤ ![shortRoot P, longRoot P]) := by
  simp [Fintype.linearCombination_apply, neg_add, -neg_add_rev, shortAddLongRoot_eq,
    twoShortAddLongRoot_eq, threeShortAddLongRoot_eq, threeShortAddTwoLongRoot_eq,
    ← Int.cast_smul_eq_zsmul R]
/-
**RootPairing.EmbeddedG2.allRoots_nodup** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.E
mbeddedG2`。
形式化陈述：allRoots_nodup : (allRoots P).Nodup
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndependent_iff_injective_fintypeLinearCombination`：linearIndepend
ent_iff_injective_fintypeLinearCombination [Fintype ι] : LinearIndependent R v ↔
 Injective (Fintype.linearCombination R v)
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `RootPairing.EmbeddedG2.linearIndependent_short_long`：linearIndependent_s
hort_long : LinearIndependent R ![shortRoot P, longRoot P]
· 使用引理 `RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs`：allRoots_eq_map_allCoe
ffs : allRoots P = allCoeffs.map (Fintype.linearCombination Int ![shortRoot P, l
ongRoot P])
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma allRoots_nodup : (allRoots P).Nodup := by
  have hli : Injective (Fintype.linearCombination ℤ ![shortRoot P, longRoot P]) := by
    rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    exact (linearIndependent_short_long P).restrict_scalars' ℤ
  rw [allRoots_eq_map_allCoeffs, nodup_map_iff hli]
  decide
/-
**RootPairing.EmbeddedG2.mem_span_of_mem_allRoots** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing.EmbeddedG2`。
形式化陈述：mem_span_of_mem_allRoots {x : M} (hx : x in allRoots P) : x in span Int {l
ongRoot P, shortRoot P}
参数：hx : x in allRoots P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.EmbeddedG2.allRoots_eq_map_allCoeffs`：allRoots_eq_map_allCoe
ffs : allRoots P = allCoeffs.map (Fintype.linearCombination Int ![shortRoot P, l
ongRoot P])
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma mem_span_of_mem_allRoots {x : M} (hx : x ∈ allRoots P) :
    x ∈ span ℤ {longRoot P, shortRoot P} := by
  have : {longRoot P, shortRoot P} = range ![shortRoot P, longRoot P] := by simp
  simp_rw [this, Submodule.mem_span_range_iff_exists_fun, ← Fintype.linearCombination_apply]
  simp [allRoots_eq_map_allCoeffs] at hx
  tauto

section InvariantForm

variable {P}
variable (B : P.InvariantForm)

/-
**RootPairing.EmbeddedG2.long_eq_three_mul_short** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing.EmbeddedG2`。
形式化陈述：long_eq_three_mul_short : B.form (longRoot P) (longRoot P) = 3 * B.form (s
hortRoot P) (shortRoot P)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.EmbeddedG2.pairing_short_long`：pairing_short_long : P.pairin
g (short P) (long P) = -1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `RootPairing.EmbeddedG2.pairing_long_short`：pairing_long_short : P.pairin
g (long P) (short P) = -3
· 使用引理 `RootPairing.InvariantForm.pairing_mul_eq_pairing_mul_swap`：pairing_mul_e
q_pairing_mul_swap : P.pairing j i * B.form (P.root i) (P.root i) = P.pairing i 
j * B.form (P.root j) (P.root j)
-/
lemma long_eq_three_mul_short :
    B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P) := by
  simpa using B.pairing_mul_eq_pairing_mul_swap (long P) (short P)

omit [Finite ι] [CharZero R] [IsDomain R]

/-- `α + β` is short. -/
/-
**RootPairing.EmbeddedG2.shortAddLongRoot_shortRoot** 是 Mathlib 中的一个定理，位于命名空间 `R
ootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
EmbeddedG2] (B : P.InvariantForm),   (B.form (RootPairing.EmbeddedG2.shortAddLon
gRoot P)) (RootPairing.EmbeddedG2.shortAddLongRoot P) =     (B.form (RootPairing
.EmbeddedG2.shortRoot P)) (RootPairing.EmbeddedG2.shortRoot P)
参数：B : P.InvariantForm；B.form (RootPairing.EmbeddedG2.shortAddLongRoot P)；RootPa
iring.EmbeddedG2.shortAddLongRoot P；B.form (RootPairing.EmbeddedG2.shortRoot P)；
RootPairing.EmbeddedG2.shortRoot P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.InvariantForm.apply_reflection_reflection`：apply_reflection_
reflection (x y : M) : B.form (P.reflection i x) (P.reflection i y) = B.form x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`α + β` is short.
-/
@[simp] lemma shortAddLongRoot_shortRoot :
    B.form (shortAddLongRoot P) (shortAddLongRoot P) = B.form (shortRoot P) (shortRoot P) := by
  simp [shortAddLongRoot, shortAddLong]

/-- `2α + β` is short. -/
/-
**RootPairing.EmbeddedG2.twoShortAddLongRoot_shortRoot** 是 Mathlib 中的一个定理，位于命名空间
 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
EmbeddedG2] (B : P.InvariantForm),   (B.form (RootPairing.EmbeddedG2.twoShortAdd
LongRoot P)) (RootPairing.EmbeddedG2.twoShortAddLongRoot P) =     (B.form (RootP
airing.EmbeddedG2.shortRoot P)) (RootPairing.EmbeddedG2.shortRoot P)
参数：B : P.InvariantForm；B.form (RootPairing.EmbeddedG2.twoShortAddLongRoot P)；Roo
tPairing.EmbeddedG2.twoShortAddLongRoot P；B.form (RootPairing.EmbeddedG2.shortRo
ot P)；RootPairing.EmbeddedG2.shortRoot P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.InvariantForm.apply_reflection_reflection`：apply_reflection_
reflection (x y : M) : B.form (P.reflection i x) (P.reflection i y) = B.form x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`2α + β` is short.
-/
@[simp] lemma twoShortAddLongRoot_shortRoot :
    B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) =
      B.form (shortRoot P) (shortRoot P) := by
  simp [twoShortAddLongRoot, twoShortAddLong]

/-- `3α + β` is long. -/
/-
**RootPairing.EmbeddedG2.threeShortAddLongRoot_longRoot** 是 Mathlib 中的一个定理，位于命名空
间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
EmbeddedG2] (B : P.InvariantForm),   (B.form (RootPairing.EmbeddedG2.threeShortA
ddLongRoot P)) (RootPairing.EmbeddedG2.threeShortAddLongRoot P) =     (B.form (R
ootPairing.EmbeddedG2.longRoot P)) (RootPairing.EmbeddedG2.longRoot P)
参数：B : P.InvariantForm；B.form (RootPairing.EmbeddedG2.threeShortAddLongRoot P)；R
ootPairing.EmbeddedG2.threeShortAddLongRoot P；B.form (RootPairing.EmbeddedG2.lon
gRoot P)；RootPairing.EmbeddedG2.longRoot P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.InvariantForm.apply_reflection_reflection`：apply_reflection_
reflection (x y : M) : B.form (P.reflection i x) (P.reflection i y) = B.form x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`3α + β` is long.
-/
@[simp] lemma threeShortAddLongRoot_longRoot :
    B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddLongRoot, threeShortAddLong]

/-- `3α + 2β` is long. -/
/-
**RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_longRoot** 是 Mathlib 中的一个定理，位于
命名空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   [inst_5 : P.
EmbeddedG2] (B : P.InvariantForm),   (B.form (RootPairing.EmbeddedG2.threeShortA
ddTwoLongRoot P)) (RootPairing.EmbeddedG2.threeShortAddTwoLongRoot P) =     (B.f
orm (RootPairing.EmbeddedG2.longRoot P)) (RootPairing.EmbeddedG2.longRoot P)
参数：B : P.InvariantForm；B.form (RootPairing.EmbeddedG2.threeShortAddTwoLongRoot P
)；RootPairing.EmbeddedG2.threeShortAddTwoLongRoot P；B.form (RootPairing.Embedded
G2.longRoot P)；RootPairing.EmbeddedG2.longRoot P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.InvariantForm.apply_reflection_reflection`：apply_reflection_
reflection (x y : M) : B.form (P.reflection i x) (P.reflection i y) = B.form x y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`3α + 2β` is long.
-/
@[simp] lemma threeShortAddTwoLongRoot_longRoot :
    B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) =
      B.form (longRoot P) (longRoot P) := by
  simp [threeShortAddTwoLongRoot, threeShortAddTwoLong]

end InvariantForm

section Pairing

variable (i : ι)

/-
**RootPairing.EmbeddedG2.pairingIn_shortAddLong_left** 是 Mathlib 中的一个定理，位于命名空间 `
RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ (RootP
airing.EmbeddedG2.shortAddLong P) i =     P.pairingIn ℤ (RootPairing.EmbeddedG2.
short P) i + P.pairingIn ℤ (RootPairing.EmbeddedG2.long P) i
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.shortAddLong P；RootPairi
ng.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_eq_add_of_root_eq_add`：pairingIn_eq_add_of_root_eq
_add [FaithfulSMul S R] [P.IsValuedIn S] {i j k l : ι} (h : P.root k = P.root i 
+ P.root l) : P.pairingIn S k j =…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.EmbeddedG2.shortAddLongRoot_eq`：shortAddLongRoot_eq : shortA
ddLongRoot P = shortRoot P + longRoot P
-/
@[simp] lemma pairingIn_shortAddLong_left :
    P.pairingIn ℤ (shortAddLong P) i = P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_add (shortAddLongRoot_eq P)]
/-
**RootPairing.EmbeddedG2.pairingIn_shortAddLong_right** 是 Mathlib 中的一个定理，位于命名空间 
`RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ i (Roo
tPairing.EmbeddedG2.shortAddLong P) =     P.pairingIn ℤ i (RootPairing.EmbeddedG
2.short P) + 3 * P.pairingIn ℤ i (RootPairing.EmbeddedG2.long P)
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.shortAddLong P；RootPairi
ng.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用引理 `RootPairing.EmbeddedG2.shortAddLongRoot_eq`：shortAddLongRoot_eq : shortA
ddLongRoot P = shortRoot P + longRoot P
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `RootPairing.EmbeddedG2.long_eq_three_mul_short`：long_eq_three_mul_short 
: B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P)
· 使用定理 `RootPairing.EmbeddedG2.shortAddLongRoot_shortRoot`：∀ {ι : Type u_1} {R :
 Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGr
oup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 47 条，此处仅展示前 30 条）
-/
@[simp] lemma pairingIn_shortAddLong_right :
    P.pairingIn ℤ i (shortAddLong P) =
      P.pairingIn ℤ i (short P) + 3 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (shortAddLong P) = P.pairing i (short P) + 3 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero (shortAddLong P))
  calc P.pairing i (shortAddLong P) * B.form (P.root (shortAddLong P)) (P.root (shortAddLong P))
    _ = 2 * B.form (P.root i) (shortAddLongRoot P) := ?_
    _ = 2 * B.form (P.root i) (shortRoot P) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 3 * P.pairing i (long P)) *
          B.form (shortAddLongRoot P) (shortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [shortAddLongRoot_eq, map_add, mul_add]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root]
  · rw [long_eq_three_mul_short, shortAddLongRoot_shortRoot]; ring
/-
**RootPairing.EmbeddedG2.pairingIn_twoShortAddLong_left** 是 Mathlib 中的一个定理，位于命名空
间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ (RootP
airing.EmbeddedG2.twoShortAddLong P) i =     2 * P.pairingIn ℤ (RootPairing.Embe
ddedG2.short P) i + P.pairingIn ℤ (RootPairing.EmbeddedG2.long P) i
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.twoShortAddLong P；RootPa
iring.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul`：pairingIn_eq_add_
of_root_eq_smul_add_smul [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsSca
larTower S R M] {i j k l : ι} {x y : S} (h …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.EmbeddedG2.twoShortAddLongRoot_eq`：twoShortAddLongRoot_eq : 
twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pairingIn_twoShortAddLong_left :
    P.pairingIn ℤ (twoShortAddLong P) i =
      2 * P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 2) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [twoShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast
/-
**RootPairing.EmbeddedG2.pairingIn_twoShortAddLong_right** 是 Mathlib 中的一个定理，位于命名
空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ i (Roo
tPairing.EmbeddedG2.twoShortAddLong P) =     2 * P.pairingIn ℤ i (RootPairing.Em
beddedG2.short P) + 3 * P.pairingIn ℤ i (RootPairing.EmbeddedG2.long P)
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.twoShortAddLong P；RootPa
iring.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用引理 `RootPairing.EmbeddedG2.twoShortAddLongRoot_eq`：twoShortAddLongRoot_eq : 
twoShortAddLongRoot P = (2 : R) • shortRoot P + longRoot P
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `RootPairing.EmbeddedG2.long_eq_three_mul_short`：long_eq_three_mul_short 
: B.form (longRoot P) (longRoot P) = 3 * B.form (shortRoot P) (shortRoot P)
· 使用定理 `RootPairing.EmbeddedG2.twoShortAddLongRoot_shortRoot`：∀ {ι : Type u_1} {
R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCom
mGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 51 条，此处仅展示前 30 条）
-/
@[simp] lemma pairingIn_twoShortAddLong_right :
    P.pairingIn ℤ i (twoShortAddLong P) =
      2 * P.pairingIn ℤ i (short P) + 3 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (twoShortAddLong P) =
      2 * P.pairing i (short P) + 3 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| twoShortAddLong P)
  calc P.pairing i (twoShortAddLong P) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (twoShortAddLongRoot P) := ?_
    _ = 2 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = 2 * P.pairing i (short P) * B.form (shortRoot P) (shortRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (2 * P.pairing i (short P) +
          3 * P.pairing i (long P)) * B.form (twoShortAddLongRoot P) (twoShortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [twoShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, mul_assoc]
  · rw [long_eq_three_mul_short, twoShortAddLongRoot_shortRoot]; ring

omit [Finite ι] [IsDomain R] in
/-
**RootPairing.EmbeddedG2.pairingIn_threeShortAddLong_left** 是 Mathlib 中的一个定理，位于命
名空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [CharZero R] (i : ι),   P.pairingIn ℤ (RootPairing.EmbeddedG2.threeS
hortAddLong P) i =     3 * P.pairingIn ℤ (RootPairing.EmbeddedG2.short P) i + P.
pairingIn ℤ (RootPairing.EmbeddedG2.long P) i
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.threeShortAddLong P；Root
Pairing.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul`：pairingIn_eq_add_
of_root_eq_smul_add_smul [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsSca
larTower S R M] {i j k l : ι} {x y : S} (h …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddLongRoot_eq`：threeShortAddLongRoot_e
q : threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pairingIn_threeShortAddLong_left :
    P.pairingIn ℤ (threeShortAddLong P) i =
      3 * P.pairingIn ℤ (short P) i + P.pairingIn ℤ (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 1) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddLongRoot_eq, one_smul, add_left_inj]
    norm_cast
/-
**RootPairing.EmbeddedG2.pairingIn_threeShortAddLong_right** 是 Mathlib 中的一个定理，位于
命名空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ i (Roo
tPairing.EmbeddedG2.threeShortAddLong P) =     P.pairingIn ℤ i (RootPairing.Embe
ddedG2.short P) + P.pairingIn ℤ i (RootPairing.EmbeddedG2.long P)
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.threeShortAddLong P；Root
Pairing.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddLongRoot_eq`：threeShortAddLongRoot_e
q : threeShortAddLongRoot P = (3 : R) • shortRoot P + longRoot P
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 46 条，此处仅展示前 30 条）
-/
@[simp] lemma pairingIn_threeShortAddLong_right :
    P.pairingIn ℤ i (threeShortAddLong P) =
      P.pairingIn ℤ i (short P) + P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (threeShortAddLong P) =
      P.pairing i (short P) + P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddLong P)
  calc P.pairing i (threeShortAddLong P) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * B.form (P.root i) (longRoot P) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + P.pairing i (long P)) *
          B.form (threeShortAddLongRoot P) (threeShortAddLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · rw [threeShortAddLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddLongRoot_longRoot]; ring
/-
**RootPairing.EmbeddedG2.pairingIn_threeShortAddTwoLong_left** 是 Mathlib 中的一个定理，
位于命名空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ (RootP
airing.EmbeddedG2.threeShortAddTwoLong P) i =     3 * P.pairingIn ℤ (RootPairing
.EmbeddedG2.short P) i + 2 * P.pairingIn ℤ (RootPairing.EmbeddedG2.long P) i
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.threeShortAddTwoLong P；R
ootPairing.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_eq_add_of_root_eq_smul_add_smul`：pairingIn_eq_add_
of_root_eq_smul_add_smul [FaithfulSMul S R] [P.IsValuedIn S] [Module S M] [IsSca
larTower S R M] {i j k l : ι} {x y : S} (h …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq`：threeShortAddTwoLong
Root_eq : threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoo
t P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma pairingIn_threeShortAddTwoLong_left :
    P.pairingIn ℤ (threeShortAddTwoLong P) i =
      3 * P.pairingIn ℤ (short P) i + 2 * P.pairingIn ℤ (long P) i := by
  rw [pairingIn_eq_add_of_root_eq_smul_add_smul (x := 3) (y := 2) (i := short P) (l := long P)]
  · simp
  · simp only [threeShortAddTwoLongRoot_eq]
    norm_cast
/-
**RootPairing.EmbeddedG2.pairingIn_threeShortAddTwoLong_right** 是 Mathlib 中的一个定理
，位于命名空间 `RootPairing.EmbeddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] (i : ι),   P.pairingIn ℤ i (Roo
tPairing.EmbeddedG2.threeShortAddTwoLong P) =     P.pairingIn ℤ i (RootPairing.E
mbeddedG2.short P) + 2 * P.pairingIn ℤ i (RootPairing.EmbeddedG2.long P)
参数：P : RootPairing ι R M N；i : ι；RootPairing.EmbeddedG2.threeShortAddTwoLong P；R
ootPairing.EmbeddedG2.short P；RootPairing.EmbeddedG2.long P。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `mul_right_cancel₀`：mul_right_cancel₀ (hb : b != 0) (h : a * b = c * b) :
 a = c
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `RootPairing.InvariantForm.ne_zero`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.InvariantForm.two_mul_apply_root_root`：two_mul_apply_root_ro
ot : 2 * B.form (P.root i) (P.root j) = P.pairing i j * B.form (P.root j) (P.roo
t j)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.EmbeddedG2.threeShortAddTwoLongRoot_eq`：threeShortAddTwoLong
Root_eq : threeShortAddTwoLongRoot P = (3 : R) • shortRoot P + (2 : R) • longRoo
t P
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 50 条，此处仅展示前 30 条）
-/
@[simp] lemma pairingIn_threeShortAddTwoLong_right :
    P.pairingIn ℤ i (threeShortAddTwoLong P) =
      P.pairingIn ℤ i (short P) + 2 * P.pairingIn ℤ i (long P) := by
  suffices P.pairing i (threeShortAddTwoLong P) =
      P.pairing i (short P) + 2 * P.pairing i (long P) from
    algebraMap_injective ℤ R <| by simpa only [algebraMap_pairingIn, map_add, map_mul, map_ofNat]
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  apply mul_right_cancel₀ (B.ne_zero <| threeShortAddTwoLong P)
  calc P.pairing i (threeShortAddTwoLong P) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P)
    _ = 2 * B.form (P.root i) (threeShortAddTwoLongRoot P) := ?_
    _ = 3 * (2 * B.form (P.root i) (shortRoot P)) + 2 * (2 * B.form (P.root i) (longRoot P)) := ?_
    _ = P.pairing i (short P) * B.form (longRoot P) (longRoot P) +
          2 * P.pairing i (long P) * B.form (longRoot P) (longRoot P) := ?_
    _ = (P.pairing i (short P) + 2 * P.pairing i (long P)) *
          B.form (threeShortAddTwoLongRoot P) (threeShortAddTwoLongRoot P) := ?_
  · rw [B.two_mul_apply_root_root]
  · simp only [threeShortAddTwoLongRoot_eq, map_add, mul_add, map_smul, smul_eq_mul]; ring
  · rw [B.two_mul_apply_root_root, B.two_mul_apply_root_root, long_eq_three_mul_short]; ring
  · rw [threeShortAddTwoLongRoot_longRoot]; ring

end Pairing

/-
**RootPairing.EmbeddedG2.isOrthogonal_short_and_long_aux** 是 Mathlib 中的一个引理，位于命名
空间 `RootPairing.EmbeddedG2`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma isOrthogonal_short_and_long_aux {a b c d e f a' b' c' d' e' f' : ℤ} {S : Set (ℤ × ℤ)}
    (S_def : S = {(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3), (3, 1),
      (-1, -3), (-3, -1)})
    (ha : (a, a') ∈ S)
    (hb : (b, b') ∈ S)
    (hc : (c, c') ∈ S)
    (hd : (d, d') ∈ S)
    (he : (e, e') ∈ S)
    (hf : (f, f') ∈ S)
    (h₁ : c = a + 3 * b)
    (h₂ : c' = a' + b')
    (h₃ : d = 2 * a + 3 * b)
    (h₄ : d' = 2 * a' + b')
    (h₅ : e = a + b)
    (h₆ : e' = 3 * a' + b')
    (h₇ : f = a + 2 * b)
    (h₈ : f' = 3 * a' + 2 * b') :
    a = 0 ∧ b = 0 := by
  simp [S_def] at ha hb hc hd he hf
  omega
/-
**RootPairing.EmbeddedG2.isOrthogonal_short_and_long** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.EmbeddedG2`。
形式化陈述：isOrthogonal_short_and_long {i : ι} (hi : P.root i ∉ allRoots P) : P.IsOrt
hogonal i (short P) ∧ P.IsOrthogonal i (long P)
参数：hi : P.root i ∉ allRoots P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.EmbeddedG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst
_2 : _root_.Module R M} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed'`：pairingI
n_pairingIn_mem_set_of_isCrystal_of_isRed' [P.IsReduced] (hij : α i != α j) (hij
' : α i != -α j) : (P.pairingIn Int i j, P.pairingIn…
· 使用定理 `RootPairing.EmbeddedG2.toIsReduced`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_
2 : _root_.Module R M} {…
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Finite.G2.0.RootPairing.Embedd
edG2.isOrthogonal_short_and_long_aux`：∀ {a b c d e f a' b' c' d' e' f' : ℤ} {S :
 Set (ℤ × ℤ)},   S = {(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -
1), (1, 3), (3, 1)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_shortAddLong_right`：∀ {ι : Type u_1} {R
 : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddComm
Group M]   [inst_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_shortAddLong_left`：∀ {ι : Type u_1} {R 
: Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommG
roup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_twoShortAddLong_right`：∀ {ι : Type u_1}
 {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddC
ommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_twoShortAddLong_left`：∀ {ι : Type u_1} 
{R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCo
mmGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_threeShortAddLong_right`：∀ {ι : Type u_
1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Ad
dCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_threeShortAddLong_left`：∀ {ι : Type u_1
} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_threeShortAddTwoLong_right`：∀ {ι : Type
 u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 :
 AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.EmbeddedG2.pairingIn_threeShortAddTwoLong_left`：∀ {ι : Type 
u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : 
AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
-/
lemma isOrthogonal_short_and_long {i : ι} (hi : P.root i ∉ allRoots P) :
    P.IsOrthogonal i (short P) ∧ P.IsOrthogonal i (long P) := by
  suffices P.pairingIn ℤ i (short P) = 0 ∧ P.pairingIn ℤ i (long P) = 0 by
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    simpa [isOrthogonal_iff_pairing_eq_zero, ← P.algebraMap_pairingIn ℤ]
  simp only [mem_cons, not_mem_nil, or_false, not_or] at hi
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩ := hi
  have ha := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (short P) ‹_› ‹_›
  have hb := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (long P) ‹_› ‹_›
  have hc := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (shortAddLong P) ‹_› ‹_›
  have hd := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (twoShortAddLong P) ‹_› ‹_›
  have he := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddLong P) ‹_› ‹_›
  have hf := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' i (threeShortAddTwoLong P) ‹_› ‹_›
  apply isOrthogonal_short_and_long_aux rfl ha hb hc hd he hf <;> simp

section IsIrreducible

variable [P.IsIrreducible]

/-
**RootPairing.EmbeddedG2.span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Embe
ddedG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   [inst_5 : P.
EmbeddedG2] [Finite ι] [CharZero R] [IsDomain R] [P.IsIrreducible],   Submodule.
span R {RootPairing.EmbeddedG2.longRoot P, RootPairing.EmbeddedG2.shortRoot P} =
 ⊤
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.span_root_image_eq_top_of_forall_orthogonal`：span_root_image
_eq_top_of_forall_orthogonal (s : Set ι) (hne : s.Nonempty) (h : forall j, P.roo
t j ∉ span R (P.root '' s) -> forall i in s, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用引理 `RootPairing.EmbeddedG2.mem_span_of_mem_allRoots`：mem_span_of_mem_allRoot
s {x : M} (hx : x in allRoots P) : x in span Int {longRoot P, shortRoot P}
· 使用引理 `RootPairing.EmbeddedG2.isOrthogonal_short_and_long`：isOrthogonal_short_a
nd_long {i : ι} (hi : P.root i ∉ allRoots P) : P.IsOrthogonal i (short P) ∧ P.Is
Orthogonal i (long P)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
@[simp] lemma span_eq_top :
    span R {longRoot P, shortRoot P} = ⊤ := by
  have := P.span_root_image_eq_top_of_forall_orthogonal {long P, short P} (by simp)
  rw [show P.root '' {long P, short P} = {longRoot P, shortRoot P} by aesop] at this
  refine this fun k hk ij hij ↦ ?_
  replace hk : P.root k ∉ allRoots P :=
    fun contra ↦ hk <| span_subset_span ℤ _ _ <| mem_span_of_mem_allRoots P contra
  have aux := isOrthogonal_short_and_long P hk
  rcases hij with rfl | rfl <;> tauto

/-- The distinguished basis carried by an `EmbeddedG2`.

In fact this is a `RootPairing.Base`. TODO Upgrade to this stronger statement. -/
/-
**RootPairing.EmbeddedG2.basis** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.EmbeddedG2
`。
形式化陈述：basis : Module.Basis (Fin 2) R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The distinguished basis carried by an `EmbeddedG2`.

In fact this is a `RootPairing.Base`. TODO Upgrade to this stronger statement.
-/
def basis : Module.Basis (Fin 2) R M :=
  have : LinearIndependent R ![EmbeddedG2.shortRoot P, EmbeddedG2.longRoot P] := by
    have := pairing_long_short P
    refine (IsReduced.linearIndependent_iff P).mpr ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · norm_num [h] at this
    · simp only [root_eq_neg_iff] at h
      norm_num [h] at this
  Module.Basis.mk this (by simp)
/-
**RootPairing.EmbeddedG2.mem_allRoots** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Emb
eddedG2`。
形式化陈述：mem_allRoots (i : ι) : P.root i in allRoots P
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `RootPairing.EmbeddedG2.isOrthogonal_short_and_long`：isOrthogonal_short_a
nd_long {i : ι} (hi : P.root i ∉ allRoots P) : P.IsOrthogonal i (short P) ∧ P.Is
Orthogonal i (long P)
· 使用定理 `RootPairing.IsG2.toIsValuedIn`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 : _
root_.Module R M} {…
· 使用定理 `RootPairing.EmbeddedG2.instIsG2OfIsIrreducible`：∀ {ι : Type u_1} {R : Ty
pe u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup
 M]   [inst_2 : _root_.Module R M] […
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.EmbeddedG2.span_eq_top`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.InvariantForm.apply_root_root_zero_iff`：apply_root_root_zero
_iff [IsDomain R] [NeZero (2 : R)] : B.form (P.root i) (P.root j) = 0 ↔ P.pairin
g i j = 0
· 使用引理 `RootPairing.isOrthogonal_iff_pairing_eq_zero`：isOrthogonal_iff_pairing_e
q_zero [NeZero (2 : R)] [IsDomain R] [Module.IsTorsionFree R M] : P.IsOrthogonal
 i j ↔ P.pairing i j = 0
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 34 条，此处仅展示前 30 条）
-/
lemma mem_allRoots (i : ι) :
    P.root i ∈ allRoots P := by
  by_contra hi
  obtain ⟨h₁, h₂⟩ := isOrthogonal_short_and_long P hi
  have : Fintype ι := Fintype.ofFinite ι
  have B := (P.posRootForm ℤ).toInvariantForm
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  rw [isOrthogonal_iff_pairing_eq_zero, ← B.apply_root_root_zero_iff] at h₁ h₂
  have key : B.form (P.root i) = 0 := by
    ext x
    have hx : x ∈ span R {longRoot P, shortRoot P} := by simp
    simp only [LinearMap.zero_apply]
    induction hx using Submodule.span_induction with
    | zero => simp
    | mem => grind
    | add => simp_all
    | smul => simp_all
  simpa using LinearMap.congr_fun key (P.root i)

open scoped Classical in
/-- The natural labelling of `RootPairing.EmbeddedG2.allRoots`. -/
/-
**RootPairing.EmbeddedG2.indexEquivAllRoots** 是 Mathlib 中的一个定义，位于命名空间 `RootPairi
ng.EmbeddedG2`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] →                   (P : RootPairing
 ι R M N) →                     [inst_5 : P.EmbeddedG2] →                       
[Finite ι] →                         [CharZero R] →                           [I
sDomain R] → [P.IsIrreducible] → ι ≃ ↥(RootPairing.EmbeddedG2.allRoots P).toFins
et
参数：P : RootPairing ι R M N；RootPairing.EmbeddedG2.allRoots P。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural labelling of `RootPairing.EmbeddedG2.allRoots`.
-/
@[simps] def indexEquivAllRoots : ι ≃ (allRoots P).toFinset :=
  { toFun i := ⟨P.root i, List.mem_toFinset.mpr <| mem_allRoots P i⟩
    invFun x := (allRoots_subset_range_root P x.property).choose
    left_inv i := by simp
    right_inv := by
      rintro ⟨x, hx⟩
      simp only [Subtype.mk.injEq]
      exact (allRoots_subset_range_root P hx).choose_spec }

include P in
/-
**RootPairing.EmbeddedG2.card_index_eq_twelve** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.EmbeddedG2`。
形式化陈述：card_index_eq_twelve : Nat.card ι = 12
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `List.toFinset_card_of_nodup`：List.toFinset_card_of_nodup {l : List α} (h
 : l.Nodup) : #l.toFinset = l.length
· 使用引理 `RootPairing.EmbeddedG2.allRoots_nodup`：allRoots_nodup : (allRoots P).Nod
up
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
-/
lemma card_index_eq_twelve :
    Nat.card ι = 12 := by
  classical
  have : Nat.card (allRoots P).toFinset = 12 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, toFinset_card_of_nodup (allRoots_nodup P)]
    simp
  rw [← this]
  exact Nat.card_congr <| indexEquivAllRoots P
/-
**RootPairing.EmbeddedG2.setOfPred_index_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing.EmbeddedG2`。
形式化陈述：setOfPred_index_eq_univ : letI _i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用引理 `RootPairing.EmbeddedG2.mem_allRoots`：mem_allRoots (i : ι) : P.root i in 
allRoots P
-/
lemma setOfPred_index_eq_univ :
    letI _i := P.indexNeg
    { long P, -long P,
      short P, -short P,
      shortAddLong P, -shortAddLong P,
      twoShortAddLong P, -twoShortAddLong P,
      threeShortAddLong P, -threeShortAddLong P,
      threeShortAddTwoLong P, -threeShortAddTwoLong P } = univ :=
  eq_univ_iff_forall.mpr fun i ↦ by simpa using mem_allRoots P i

@[deprecated (since := "2026-07-09")] alias setOf_index_eq_univ := setOfPred_index_eq_univ

end IsIrreducible

end EmbeddedG2

namespace IsG2

variable {P}
variable [P.IsG2] (b : P.Base) [Finite ι] [CharZero R] [IsDomain R]

/-
**RootPairing.IsG2.card_base_support_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `RootPairi
ng.IsG2`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N} [P.IsG2]   (b 
: P.Base) [Finite ι] [CharZero R] [IsDomain R], b.support.card = 2
参数：b : P.Base。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsG2.nonempty`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root
_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `RootPairing.IsG2.toIsIrreducible`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_2 
: _root_.Module R M} {…
· 使用定理 `RootPairing.instIsRootSystemOfNonemptyOfNeZeroOfNatOfIsIrreducible`：∀ {ι
 : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [i
nst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
-/
@[simp] lemma card_base_support_eq_two :
    b.support.card = 2 := by
  have _i : P.EmbeddedG2 := toEmbeddedG2 P
  have _i : Nonempty ι := IsG2.nonempty P
  rw [← Fintype.card_fin 2, ← Module.finrank_eq_card_basis (EmbeddedG2.basis P),
    Module.finrank_eq_card_basis b.toWeightBasis, Fintype.card_coe]

variable {b} in
/-
**RootPairing.IsG2.span_eq_rootSpan_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.I
sG2`。
形式化陈述：span_eq_rootSpan_int {i j : ι} (hi : i in b.support) (hj : j in b.support)
 (h_ne : i != j) : Submodule.span Int {P.root i, P.root j} = P.rootSpan Int
参数：hi : i in b.support；hj : j in b.support；h_ne : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `Finset.coe_pair`：coe_pair {a b : α} : (({a, b} : Finset α) : Set α) = {a
, b}
· 使用定理 `Finset.eq_of_subset_of_card_le`：eq_of_subset_of_card_le (h : s subseteq 
t) (h₂ : #t <= #s) : s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `RootPairing.IsG2.card_base_support_eq_two`：∀ {ι : Type u_1} {R : Type u_
2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]  
 [inst_2 : _root_.Module R M] […
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `RootPairing.Base.span_int_root_support`：span_int_root_support : span Int
 (P.root '' b.support) = span Int (range P.root)
-/
lemma span_eq_rootSpan_int {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) (h_ne : i ≠ j) :
    Submodule.span ℤ {P.root i, P.root j} = P.rootSpan ℤ := by
  classical
  have : {i, j} ⊆ b.support := by grind
  rw [← image_pair, ← Finset.coe_pair, Finset.eq_of_subset_of_card_le this (by aesop),
    b.span_int_root_support]

end IsG2

end RootPairing

