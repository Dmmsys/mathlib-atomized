/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Ring.Action.Submonoid

/-!
# More operations on subalgebras

In this file we relate the definitions in `Mathlib/RingTheory/Ideal/Operations.lean` to subalgebras.
The contents of this file are somewhat random since both
`Mathlib/Algebra/Algebra/Subalgebra/Basic.lean` and `Mathlib/RingTheory/Ideal/Operations.lean` are
somewhat of a grab-bag of definitions, and this is whatever ends up in the intersection.
-/

@[expose] public section

assert_not_exists Cardinal

namespace AlgHom

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]

/-
**AlgHom.ker_rangeRestrict** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：ker_rangeRestrict (f : A ->ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom
.ker f
参数：f : A ->ₐ[R] B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem ker_rangeRestrict (f : A →ₐ[R] B) : RingHom.ker f.rangeRestrict = RingHom.ker f :=
  Ideal.ext fun _ ↦ Subtype.ext_iff

end AlgHom

namespace Subalgebra

open Algebra

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
variable (S' : Subalgebra R S)

/-- Suppose we are given `∑ i, lᵢ * sᵢ = 1` ∈ `S`, and `S'` a subalgebra of `S` that contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`. -/
/-
**Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Subalgebra`。
形式化陈述：mem_of_finsetSum_eq_one_of_pow_smul_mem {ι : Type*} (ι' : Finset ι) (s : ι
 -> S) (l : ι -> S) (e : ∑ i in ι', l i * s i = 1) (hs : forall i, s i in S') (h
l : forall i, l i in S') (x : S) (H : forall i, exists n : Nat, (s i ^ n : S) • 
x in S') : x in S'
参数：ι' : Finset ι；s : ι -> S；l : ι -> S；e : ∑ i in ι', l i * s i = 1；hs : forall 
i, s i in S'；hl : forall i, l i in S'；x : S；H : forall i, exists n : Nat, (s i ^
 n : S) • x in S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Ideal.span_pow_eq_top`：span_pow_eq_top (s : Set α) (hs : span s = ⊤) (n 
: Nat) : span ((fun (x : α) => x ^ n) '' s) = ⊤
· 使用定理 `Submodule.mem_of_span_top_of_smul_mem`：mem_of_span_top_of_smul_mem (M' :
 Submodule R M) (s : Set R) (hs : Ideal.span s = ⊤) (x : M) (H : forall r : s, (
r : R) • x in M') : x in M'
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Suppose we are given `∑ i, lᵢ * sᵢ = 1` ∈ `S`, and `S'` a subalgebra of `S` that
 contains
`lᵢ` and `sᵢ`. To check that an `x : S` falls in `S'`, we only need to show that
`sᵢ ^ n • x ∈ S'` for some `n` for each `sᵢ`.
-/
theorem mem_of_finsetSum_eq_one_of_pow_smul_mem
    {ι : Type*} (ι' : Finset ι) (s : ι → S) (l : ι → S)
    (e : ∑ i ∈ ι', l i * s i = 1) (hs : ∀ i, s i ∈ S') (hl : ∀ i, l i ∈ S') (x : S)
    (H : ∀ i, ∃ n : ℕ, (s i ^ n : S) • x ∈ S') : x ∈ S' := by
  suffices x ∈ Subalgebra.toSubmodule (Algebra.ofId S' S).range by
    obtain ⟨x, rfl⟩ := this
    exact x.2
  choose n hn using H
  let s' : ι → S' := fun x => ⟨s x, hs x⟩
  let l' : ι → S' := fun x => ⟨l x, hl x⟩
  have e' : ∑ i ∈ ι', l' i * s' i = 1 := by
    ext
    change S'.subtype (∑ i ∈ ι', l' i * s' i) = 1
    simpa only [map_sum, map_mul] using! e
  have : Ideal.span (s' '' ι') = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← e']
    apply sum_mem
    intro i hi
    exact Ideal.mul_mem_left _ _ <| Ideal.subset_span <| Set.mem_image_of_mem s' hi
  let N := ι'.sup n
  have hN := Ideal.span_pow_eq_top _ this N
  apply (Algebra.ofId S' S).range.toSubmodule.mem_of_span_top_of_smul_mem _ hN
  rintro ⟨_, _, ⟨i, hi, rfl⟩, rfl⟩
  change s' i ^ N • x ∈ _
  rw [← tsub_add_cancel_of_le (show n i ≤ N from Finset.le_sup hi), pow_add, mul_smul]
  refine Submodule.smul_mem _ (⟨_, pow_mem (hs i) _⟩ : S') ?_
  exact ⟨⟨_, hn i⟩, rfl⟩

@[deprecated (since := "2026-04-08")]
alias mem_of_finset_sum_eq_one_of_pow_smul_mem := mem_of_finsetSum_eq_one_of_pow_smul_mem
/-
**Subalgebra.mem_of_span_eq_top_of_smul_pow_mem** 是 Mathlib 中的一个定理，位于命名空间 `Subal
gebra`。
形式化陈述：mem_of_span_eq_top_of_smul_pow_mem (s : Set S) (l : s ->₀ S) (hs : Finsupp
.linearCombination S ((↑) : s -> S) l = 1) (hs' : s subseteq S') (hl : forall i,
 l i in S') (x : S) (H : forall r : s, exists n : Nat, (r : S) ^ n • x in S') : 
x in S'
参数：s : Set S；l : s ->₀ S；hs : Finsupp.linearCombination S ((↑) : s -> S) l = 1；h
s' : s subseteq S'；hl : forall i, l i in S'；x : S；H : forall r : s, exists n : N
at, (r : S) ^ n • x in S'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.mem_of_finsetSum_eq_one_of_pow_smul_mem`：mem_of_finsetSum_eq_
one_of_pow_smul_mem {ι : Type*} (ι' : Finset ι) (s : ι -> S) (l : ι -> S) (e : ∑
 i in ι', l i * s i = 1) (hs : forall i,…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem mem_of_span_eq_top_of_smul_pow_mem
    (s : Set S) (l : s →₀ S) (hs : Finsupp.linearCombination S ((↑) : s → S) l = 1)
    (hs' : s ⊆ S') (hl : ∀ i, l i ∈ S') (x : S) (H : ∀ r : s, ∃ n : ℕ, (r : S) ^ n • x ∈ S') :
    x ∈ S' :=
  mem_of_finsetSum_eq_one_of_pow_smul_mem S' l.support (↑) l hs (fun x => hs' x.2) hl x H

end Subalgebra

section MulSemiringAction

variable (A B B' : Type*) [CommSemiring A] [Ring B] [Semiring B'] [Algebra A B] [Algebra A B']
variable (G : Type*) [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
  [MulSemiringAction G B'] [SMulCommClass G A B']

/-- The set of fixed points under a group action, as a subring. -/
/-
**FixedPoints.subsemiring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.subsemiring : Subsemiring B' where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of fixed points under a group action, as a subring.
-/
def FixedPoints.subsemiring : Subsemiring B' where
  __ := FixedPoints.addSubmonoid G B'
  __ := FixedPoints.submonoid G B'
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass G (FixedPoints.subsemiring B' G) B' :=
  inferInstanceAs (SMulCommClass G (FixedPoints.submonoid G B') B')

/-- The set of fixed points under a group action, as a subring. -/
/-
**FixedPoints.subring** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.subring : Subring B where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of fixed points under a group action, as a subring.
-/
def FixedPoints.subring : Subring B where
  __ := FixedPoints.addSubgroup G B
  __ := FixedPoints.submonoid G B
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass G (FixedPoints.subring B G) B :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subsemiring B G) B)

/-- The set of fixed points under a group action, as a subalgebra. -/
/-
**FixedPoints.subalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：FixedPoints.subalgebra : Subalgebra A B' where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of fixed points under a group action, as a subalgebra.
-/
def FixedPoints.subalgebra : Subalgebra A B' where
  __ := FixedPoints.subsemiring B' G
  algebraMap_mem' r g := smul_algebraMap g r
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMulCommClass G (FixedPoints.subalgebra A B' G) B' :=
  inferInstanceAs (SMulCommClass G (FixedPoints.subsemiring B' G) B')

end MulSemiringAction

