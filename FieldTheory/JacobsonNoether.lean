/-
Copyright (c) 2024 F. Nuccio, H. Zheng, W. He, S. Wu, Y. Yuan, W. Jiao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio, Huanyu Zheng, Sihan Wu, Wanyi He, Weichen Jiao, Yi Yuan
-/
module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.Algebra.CharP.LinearMaps
public import Mathlib.Algebra.CharP.Subring
public import Mathlib.Algebra.GroupWithZero.Conj
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# The Jacobson-Noether theorem

This file contains a proof of the Jacobson-Noether theorem and some auxiliary lemmas.
Here we discuss different cases of characteristics of
the noncommutative division algebra `D` with center `k`.

## Main Results

- `exists_separable_and_not_isCentral` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being its center `k`), then there exist an element `x` of
  `D \ k` that is separable over its center.
- `exists_separable_and_not_isCentral'` : (Jacobson-Noether theorem) For a
  non-commutative algebraic division algebra `D` (with base ring
  being a field `L`), if the center of `D` over `L` is `L`,
  then there exist an element `x` of `D \ L` that is separable over `L`.

## Notation

- `D` is a noncommutative division algebra
- `k` is the center of `D`

## Implementation Notes

Mathematically, `exists_separable_and_not_isCentral` and `exists_separable_and_not_isCentral'`
are equivalent.

The difference however, is that the former takes `D` as the only variable
and fixing `D` would forces `k`. Whereas the later takes `D` and `L` as
separate variables constrained by certain relations.

## Reference
* <https://ysharifi.wordpress.com/2011/09/30/the-jacobson-noether-theorem/>
-/

public section

namespace JacobsonNoether

variable {D : Type*} [DivisionRing D] [Algebra.IsAlgebraic (Subring.center D) D]

local notation3 "k" => Subring.center D

open Polynomial LinearMap LieAlgebra

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D`, there exists a natural number `n`
  such that `a ^ (p ^ n)` is contained in `k`. -/
/-
**JacobsonNoether.exists_pow_mem_center_of_inseparable** 是 Mathlib 中的一个引理，位于命名空间
 `JacobsonNoether`。
形式化陈述：exists_pow_mem_center_of_inseparable (p : Nat) [hchar : ExpChar D p] (a : 
D) (hinsep : forall x : D, IsSeparable k x -> x in k) : exists n, a ^ (p ^ n) in
 k
参数：p : Nat；a : D；hinsep : forall x : D, IsSeparable k x -> x in k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPurelyInseparable_iff_pow_mem`：isPurelyInseparable_iff_pow_mem : IsPur
elyInseparable F E ↔ forall x : E, exists n : Nat, x ^ q ^ n in (algebraMap F E)
.range
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ExpChar.expChar_center_iff`：expChar_center_iff {R : Type u} [Ring R] {p 
: Nat} : ExpChar (Subring.center R) p ↔ ExpChar R p
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.mem_range`：mem_range {f : R ->+* S} {y : S} : y in f.range ↔ exi
sts x, f x = y
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subalgebra.range_subset`：range_subset : Set.range (algebraMap R A) subse
teq S
· 使用定理 `Set.mem_of_subset_of_mem`：∀ {α : Type u} {s₁ s₂ : Set α} {a : α}, s₁ ⊆ s
₂ → a ∈ s₁ → a ∈ s₂
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x

--- 原说明 ---
If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D`, there exists a natural number `n`
  such that `a ^ (p ^ n)` is contained in `k`.
-/
lemma exists_pow_mem_center_of_inseparable (p : ℕ) [hchar : ExpChar D p] (a : D)
    (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, a ^ (p ^ n) ∈ k := by
  have := (@isPurelyInseparable_iff_pow_mem k D _ _ _ _ p (ExpChar.expChar_center_iff.2 hchar)).1
  have pure : IsPurelyInseparable k D := ⟨Algebra.IsAlgebraic.isIntegral, fun x hx ↦ by
    rw [RingHom.mem_range, Subtype.exists]
    exact ⟨x, ⟨hinsep x hx, rfl⟩⟩⟩
  obtain ⟨n, ⟨m, hm⟩⟩ := this pure a
  have := Subalgebra.range_subset (R := k) ⟨(k).toSubsemiring, fun r ↦ r.2⟩
  exact ⟨n, Set.mem_of_subset_of_mem this <| Set.mem_range.2 ⟨m, hm⟩⟩

/-- If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `n`
  **greater than 0** such that `a ^ (p ^ n)` is contained in `k`. -/
/-
**JacobsonNoether.exists_pow_mem_center_of_inseparable'** 是 Mathlib 中的一个引理，位于命名空
间 `JacobsonNoether`。
形式化陈述：exists_pow_mem_center_of_inseparable' (p : Nat) [ExpChar D p] {a : D} (ha 
: a ∉ k) (hinsep : forall x : D, IsSeparable k x -> x in k) : exists n, 1 <= n ∧
 a ^ (p ^ n) in k
参数：p : Nat；ha : a ∉ k；hinsep : forall x : D, IsSeparable k x -> x in k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `JacobsonNoether.exists_pow_mem_center_of_inseparable`：exists_pow_mem_cen
ter_of_inseparable (p : Nat) [hchar : ExpChar D p] (a : D) (hinsep : forall x : 
D, IsSeparable k x -> x in k) : exists n, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0

--- 原说明 ---
If `D` is a purely inseparable extension of `k` with characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `n`
  **greater than 0** such that `a ^ (p ^ n)` is contained in `k`.
-/
lemma exists_pow_mem_center_of_inseparable' (p : ℕ) [ExpChar D p] {a : D}
    (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) : ∃ n, 1 ≤ n ∧ a ^ (p ^ n) ∈ k := by
  obtain ⟨n, hn⟩ := exists_pow_mem_center_of_inseparable p a hinsep
  have nzero : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, pow_one] at hn
    exact ha hn
  exact ⟨n, ⟨Nat.one_le_iff_ne_zero.mpr nzero, hn⟩⟩

attribute [local instance 100] LieRing.ofAssociativeRing

/-- If `D` is a purely inseparable extension of `k` of characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `m`
  greater than 0 such that `(a * x - x * a) ^ n = 0` (as linear maps) for
  every `n` greater than `(p ^ m)`. -/
/-
**JacobsonNoether.exist_pow_eq_zero_of_le** 是 Mathlib 中的一个引理，位于命名空间 `JacobsonNoe
ther`。
形式化陈述：exist_pow_eq_zero_of_le (p : Nat) [hchar : ExpChar D p] {a : D} (ha : a ∉ 
k) (hinsep : forall x : D, IsSeparable k x -> x in k) : exists m, 1 <= m ∧ foral
l n, p ^ m <= n -> (ad k D a)^[n] = 0
参数：p : Nat；ha : a ∉ k；hinsep : forall x : D, IsSeparable k x -> x in k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `JacobsonNoether.exists_pow_mem_center_of_inseparable'`：exists_pow_mem_ce
nter_of_inseparable' (p : Nat) [ExpChar D p] {a : D} (ha : a ∉ k) (hinsep : fora
ll x : D, IsSeparable k x -> x in k) : exis…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieAlgebra.ad_eq_lmul_left_sub_lmul_right`：LieAlgebra.ad_eq_lmul_left_su
b_lmul_right (A : Type v) [Ring A] [Algebra R A] : (ad R A : A -> Module.End R A
) = LinearMap.mulLeft R - Linea…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.End.pow_apply`：pow_apply (f : End R M) (n : Nat) (m : M) : (f ^ n
) m = f^[n] m
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用引理 `sub_pow_expChar_pow_of_commute`：sub_pow_expChar_pow_of_commute (h : Comm
ute x y) : (x - y) ^ p ^ n = x ^ p ^ n - y ^ p ^ n
· 使用定理 `instExpCharLinearMapSubtypeMemSubringCenterId`：∀ {D : Type u_1} [inst : 
DivisionRing D] {p : ℕ} [ExpChar D p], ExpChar (D →ₗ[↥(Subring.center D)] D) p
· 使用定理 `LinearMap.commute_mulLeft_right`：commute_mulLeft_right (a b : A) : Commu
te (mulLeft R a) (mulRight R b)
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `LinearMap.pow_mulLeft`：pow_mulLeft (a : A) (n : Nat) : mulLeft R a ^ n =
 mulLeft R (a ^ n)
· 使用定理 `LinearMap.mulLeft_apply`：mulLeft_apply (a b : A) : mulLeft R a b = a * b
· 使用定理 `LinearMap.pow_mulRight`：pow_mulRight (a : A) (n : Nat) : mulRight R a ^ 
n = mulRight R (a ^ n)
· 使用定理 `LinearMap.mulRight_apply`：mulRight_apply (a b : A) : mulRight R a b = b 
* a
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.mem_center_iff`：mem_center_iff {R : Type*} [Ring R] {z : R} : z 
in center R ↔ forall g, g * z = z * g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sub_eq_zero_of_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a = b
 → a - b = 0
· 使用定理 `Nat.sub_eq_iff_eq_add`：∀ {b a c : ℕ}, b ≤ a → (a - b = c ↔ a = c + b)
· 使用定理 `Function.iterate_add`：∀ {α : Type u} (f : α → α) (m n : ℕ), f^[m + n] = 
f^[m] ∘ f^[n]
· 使用定理 `Pi.comp_zero`：∀ {α : Type u_2} {β : Type u_3} {M : Type u_7} [inst : Zer
o M] (f : M → β), f ∘ 0 = Function.const α (f 0)
· 使用定理 `iterate_map_zero`：∀ {M : Type u_10} {F : Type u_11} [inst : Zero M] [ins
t_1 : FunLike F M M] [ZeroHomClass F M M] (f : F) (n : ℕ),   (⇑f)^[n] 0 = 0
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If `D` is a purely inseparable extension of `k` of characteristic `p`,
  then for every element `a` of `D \ k`, there exists a natural number `m`
  greater than 0 such that `(a * x - x * a) ^ n = 0` (as linear maps) for
  every `n` greater than `(p ^ m)`.
-/
lemma exist_pow_eq_zero_of_le (p : ℕ) [hchar : ExpChar D p]
    {a : D} (ha : a ∉ k) (hinsep : ∀ x : D, IsSeparable k x → x ∈ k) :
    ∃ m, 1 ≤ m ∧ ∀ n, p ^ m ≤ n → (ad k D a)^[n] = 0 := by
  obtain ⟨m, hm⟩ := exists_pow_mem_center_of_inseparable' p ha hinsep
  refine ⟨m, ⟨hm.1, fun n hn ↦ ?_⟩⟩
  have inter : (ad k D a)^[p ^ m] = 0 := by
    ext x
    rw [ad_eq_lmul_left_sub_lmul_right, ← Module.End.pow_apply, Pi.sub_apply,
      sub_pow_expChar_pow_of_commute p m (commute_mulLeft_right a a), LinearMap.sub_apply,
      pow_mulLeft, mulLeft_apply, pow_mulRight, mulRight_apply, Pi.zero_apply,
      Subring.mem_center_iff.1 hm.2 x]
    exact sub_eq_zero_of_eq rfl
  rw [(Nat.sub_eq_iff_eq_add hn).1 rfl, Function.iterate_add, inter, Pi.comp_zero,
    iterate_map_zero, Function.const_zero]

variable (D) in
/-- Jacobson-Noether theorem: For a non-commutative division algebra
  `D` that is algebraic over its center `k`, there exists an element
  `x` of `D \ k` that is separable over `k`. -/
/-
**JacobsonNoether.exists_separable_and_not_isCentral** 是 Mathlib 中的一个定理，位于命名空间 `
JacobsonNoether`。
形式化陈述：exists_separable_and_not_isCentral (H : k != (⊤ : Subring D)) : exists x :
 D, x ∉ k ∧ IsSeparable k x
参数：H : k != (⊤ : Subring D)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExpChar.exists`：ExpChar.exists [Ring R] [IsDomain R] : exists q, ExpChar
 R q
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subring.eq_top_iff'`：eq_top_iff' (A : Subring R) : A = ⊤ ↔ forall x : R,
 x in A
· 使用定理 `Subring.zero_mem`：∀ {R : Type u} [inst : NonAssocRing R] (s : Subring R)
, 0 ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subring.mem_center_iff`：mem_center_iff {R : Type*} [Ring R] {z : R} : z 
in center R ↔ forall g, g * z = z * g
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `JacobsonNoether.exist_pow_eq_zero_of_le`：exist_pow_eq_zero_of_le (p : Na
t) [hchar : ExpChar D p] {a : D} (ha : a ∉ k) (hinsep : forall x : D, IsSeparabl
e k x -> x in k) : exists m, …
· 使用引理 `expChar_pow_pos`：expChar_pow_pos (q : Nat) [ExpChar R q] (n : Nat) : 0 <
 q ^ n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Nat.find_min`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) {
m : ℕ}, m < Nat.find H → ¬p m
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Mathlib.Tactic.Linarith.eq_of_not_lt_of_not_gt`：eq_of_not_lt_of_not_gt {
α} [LinearOrder α] (a b : α) (h1 : ¬ a < b) (h2 : ¬ b < a) : a = b
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
（共 102 条，此处仅展示前 30 条）

--- 原说明 ---
Jacobson-Noether theorem: For a non-commutative division algebra
  `D` that is algebraic over its center `k`, there exists an element
  `x` of `D \ k` that is separable over `k`.
-/
theorem exists_separable_and_not_isCentral (H : k ≠ (⊤ : Subring D)) :
    ∃ x : D, x ∉ k ∧ IsSeparable k x := by
  obtain ⟨p, hp⟩ := ExpChar.exists D
  by_contra! insep
  replace insep : ∀ x : D, IsSeparable k x → x ∈ k :=
    fun x h ↦ Classical.byContradiction fun hx ↦ insep x hx h
  -- The element `a` below is in `D` but not in `k`.
  obtain ⟨a, ha⟩ := not_forall.mp <| mt (Subring.eq_top_iff' k).mpr H
  have ha₀ : a ≠ 0 := fun nh ↦ nh ▸ ha <| Subring.zero_mem k
  -- We construct another element `b` that does not commute with `a`.
  obtain ⟨b, hb1⟩ : ∃ b : D, ad k D a b ≠ 0 := by
    rw [Subring.mem_center_iff, not_forall] at ha
    use ha.choose
    change a * ha.choose - ha.choose * a ≠ 0
    simpa only [ne_eq, sub_eq_zero] using Ne.symm ha.choose_spec
  -- We find a maximum natural number `n` such that `(a * x - x * a) ^ n b ≠ 0`.
  obtain ⟨n, hn, hb⟩ : ∃ n, 0 < n ∧ (ad k D a)^[n] b ≠ 0 ∧ (ad k D a)^[n + 1] b = 0 := by
    obtain ⟨m, -, hm2⟩ := exist_pow_eq_zero_of_le p ha insep
    have h_exist : ∃ n, 0 < n ∧ (ad k D a)^[n + 1] b = 0 := ⟨p ^ m,
      ⟨expChar_pow_pos D p m, by rw [hm2 (p ^ m + 1) (Nat.le_add_right _ _), Pi.zero_apply]⟩⟩
    classical
    refine ⟨Nat.find h_exist, ⟨(Nat.find_spec h_exist).1, ?_, (Nat.find_spec h_exist).2⟩⟩
    set t := (Nat.find h_exist - 1 : ℕ) with ht
    by_cases! h_pos : 0 < t
    · convert! (ne_eq _ _) ▸ not_and.mp (Nat.find_min h_exist (m := t) (by lia)) h_pos
      lia
    · suffices h_find : Nat.find h_exist = 1 by
        rwa [h_find]
      rw [Nat.le_zero, ht, Nat.sub_eq_zero_iff_le] at h_pos
      linarith [(Nat.find_spec h_exist).1]
  -- We define `c` to be the value that we proved above to be non-zero.
  set c := (ad k D a)^[n] b with hc_def
  let _ : Invertible c := ⟨c⁻¹, inv_mul_cancel₀ hb.1, mul_inv_cancel₀ hb.1⟩
  -- We prove that `c` commutes with `a`.
  have hc : a * c = c * a := by
    apply eq_of_sub_eq_zero
    rw [← mulLeft_apply (R := k), ← mulRight_apply (R := k)]
    suffices ad k D a c = 0 from by
      rw [← this]; simp [LieRing.of_associative_ring_bracket]
    rw [← Function.iterate_succ_apply' (ad k D a) n b, hb.2]
  -- We now make some computation to obtain the final equation.
  set d := c⁻¹ * a * (ad k D a)^[n - 1] b with hd_def
  have hc' : c⁻¹ * a = a * c⁻¹ := by
    apply_fun (c⁻¹ * · * c⁻¹) at hc
    rw [mul_assoc, mul_assoc, mul_inv_cancel₀ hb.1, mul_one, ← mul_assoc,
      inv_mul_cancel₀ hb.1, one_mul] at hc
    exact hc
  have c_eq : a * (ad k D a)^[n - 1] b - (ad k D a)^[n - 1] b * a = c := by
    rw [hc_def, ← Nat.sub_add_cancel hn, Function.iterate_succ_apply' (ad k D a) _ b]; rfl
  have eq1 : c⁻¹ * a * (ad k D a)^[n - 1] b - c⁻¹ * (ad k D a)^[n - 1] b * a = 1 := by
    simp_rw [mul_assoc, (mul_sub_left_distrib c⁻¹ _ _).symm, c_eq, inv_mul_cancel_of_invertible]
  -- We show that `a` commutes with `d`.
  have deq : a * d - d * a = a := by
    nth_rw 3 [← mul_one a]
    rw [hd_def, ← eq1, mul_sub, mul_assoc _ _ a, sub_right_inj, hc',
      ← mul_assoc, ← mul_assoc, ← mul_assoc]
  -- This then yields a contradiction.
  apply_fun (a⁻¹ * ·) at deq
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ ha₀, one_mul, ← mul_assoc, sub_eq_iff_eq_add] at deq
  obtain ⟨r, hr⟩ := exists_pow_mem_center_of_inseparable p d insep
  apply_fun (· ^ (p ^ r)) at deq
  rw [add_pow_expChar_pow_of_commute p r (Commute.one_left _), one_pow,
    GroupWithZero.conj_pow₀ ha₀, ← hr.comm, mul_assoc, inv_mul_cancel₀ ha₀, mul_one,
    right_eq_add] at deq
  exact one_ne_zero deq

open Subring Algebra in
/-- Jacobson-Noether theorem: For a non-commutative division algebra `D`
  that is algebraic over a field `L`, if the center of
  `D` coincides with `L`, then there exist an element `x` of `D \ L`
  that is separable over `L`. -/
/-
**JacobsonNoether.exists_separable_and_not_isCentral'** 是 Mathlib 中的一个定理，位于命名空间 
`JacobsonNoether`。
形式化陈述：exists_separable_and_not_isCentral' {L D : Type*} [Field L] [DivisionRing 
D] [Algebra L D] [Algebra.IsAlgebraic L D] [Algebra.IsCentral L D] (hneq : (⊥ : 
Subalgebra L D) != ⊤) : exists x : D, x ∉ (⊥ : Subalgebra L D) ∧ IsSeparable L x
参数：hneq : (⊥ : Subalgebra L D) != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `Algebra.IsCentral.out`：∀ {K : Type u} {inst : CommSemiring K} {D : Type 
v} {inst_1 : Semiring D} {inst_2 : Algebra K D}   [self : Algebra.IsCentral K D]
, Subalgebr…
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Subalgebra.toSubring_injective`：toSubring_injective {R : Type u} {A : Ty
pe v} [CommRing R] [Ring A] [Algebra R A] : Function.Injective (toSubring : Suba
lgebra R A -> Subrin…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `IsScalarTower.of_algebraMap_eq`：of_algebraMap_eq [Algebra R A] (h : fora
ll x, algebraMap R A x = algebraMap S A (algebraMap R S x)) : IsScalarTower R S 
A
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `Algebra.IsAlgebraic.tower_top`：Algebra.IsAlgebraic.tower_top [Algebra.Is
Algebraic K A] : Algebra.IsAlgebraic L A
· 使用定理 `JacobsonNoether.exists_separable_and_not_isCentral`：exists_separable_and
_not_isCentral (H : k != (⊤ : Subring D)) : exists x : D, x ∉ k ∧ IsSeparable k 
x
· 使用定理 `Subalgebra.center_toSubring`：center_toSubring (R A : Type*) [CommRing R]
 [Ring A] [Algebra R A] : (center R A).toSubring = Subring.center A
· 使用定理 `IsSeparable.tower_top`：IsSeparable.tower_top {x : E} (h : IsSeparable F 
x) : IsSeparable L x

--- 原说明 ---
Jacobson-Noether theorem: For a non-commutative division algebra `D`
  that is algebraic over a field `L`, if the center of
  `D` coincides with `L`, then there exist an element `x` of `D \ L`
  that is separable over `L`.
-/
theorem exists_separable_and_not_isCentral' {L D : Type*} [Field L] [DivisionRing D]
    [Algebra L D] [Algebra.IsAlgebraic L D] [Algebra.IsCentral L D]
    (hneq : (⊥ : Subalgebra L D) ≠ ⊤) :
    ∃ x : D, x ∉ (⊥ : Subalgebra L D) ∧ IsSeparable L x := by
  have hcenter : Subalgebra.center L D = ⊥ := le_bot_iff.mp IsCentral.out
  have ntrivial : Subring.center D ≠ ⊤ :=
    congr(Subalgebra.toSubring $hcenter).trans_ne (Subalgebra.toSubring_injective.ne hneq)
  set φ := Subalgebra.equivOfEq (⊥ : Subalgebra L D) (.center L D) hcenter.symm
  set equiv : L ≃+* (center D) := ((botEquiv L D).symm.trans φ).toRingEquiv
  let _ : Algebra L (center D) := equiv.toRingHom.toAlgebra
  let _ : Algebra (center D) L := equiv.symm.toRingHom.toAlgebra
  have _ : IsScalarTower L (center D) D := .of_algebraMap_eq fun _ ↦ rfl
  have _ : IsScalarTower (center D) L D := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply L (center D)]
    congr
    exact (equiv.apply_symm_apply x).symm
  have _ : Algebra.IsAlgebraic (center D) D := .tower_top (K := L) _
  obtain ⟨x, hxd, hx⟩ := exists_separable_and_not_isCentral D ntrivial
  exact ⟨x, ⟨by rwa [← Subalgebra.center_toSubring L, hcenter] at hxd, IsSeparable.tower_top _ hx⟩⟩

end JacobsonNoether

