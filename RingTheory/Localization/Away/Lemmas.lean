/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule

/-!
# More lemmas on localization away

This file contains lemmas on localization away from an element requiring more imports.

-/

@[expose] public section

variable {R : Type*} [CommRing R]

namespace IsLocalization.Away

/-- Given a set `s` in a ring `R` and for every `t : s` a set `p t` of fractions in
a localization of `R` at `t`, this is the function sending a pair `(t, y)`, with
`t : s` and `y : t a`, to `t` multiplied with a numerator of `y`. The range
of this function spans the unit ideal, if `s` and every `p t` do. -/
/-
**IsLocalization.Away.mulNumerator** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization.Awa
y`。
形式化陈述：mulNumerator (s : Set R) {Rₜ : s -> Type*} [forall t, CommRing (Rₜ t)] [fo
rall t, Algebra R (Rₜ t)] [forall t, IsLocalization.Away t.val (Rₜ t)] (p : (t :
 s) -> Set (Rₜ t)) (x : (t : s) × p t) : R
参数：s : Set R；Rₜ t；Rₜ t；Rₜ t；p : (t : s) -> Set (Rₜ t)；x : (t : s) × p t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `s` in a ring `R` and for every `t : s` a set `p t` of fractions in
a localization of `R` at `t`, this is the function sending a pair `(t, y)`, with
`t : s` and `y : t a`, to `t` multiplied with a numerator of `y`. The range
of this function spans the unit ideal, if `s` and every `p t` do.
-/
noncomputable def mulNumerator (s : Set R)
    {Rₜ : s → Type*} [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t.val (Rₜ t)]
    (p : (t : s) → Set (Rₜ t)) (x : (t : s) × p t) : R :=
  x.1 * (IsLocalization.Away.sec x.1.1 x.2.1).1
/-
**IsLocalization.Away.span_range_mulNumerator_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `
IsLocalization.Away`。
形式化陈述：span_range_mulNumerator_eq_top {s : Set R} (hsone : Ideal.span s = ⊤) {Rₜ 
: s -> Type*} [forall t, CommRing (Rₜ t)] [forall t, Algebra R (Rₜ t)] [forall t
, IsLocalization.Away t.val (Rₜ t)] {p : (t : s) -> Set (Rₜ t)} (htone : forall 
(r : s), Ideal.span (p r) = ⊤) : Ideal.span (Set.range (IsLocalization.Away.mulN
umerator s p)) = ⊤
参数：hsone : Ideal.span s = ⊤；Rₜ t；Rₜ t；Rₜ t；t : s；Rₜ t；htone : forall (r : s), Id
eal.span (p r) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.radical_eq_top`：radical_eq_top : radical I = ⊤ ↔ I = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.mem_span_map`：mem_span_map {x : S} {a : Set R} : x in Ide
al.span (algebraMap R S '' a) ↔ exists y in Ideal.span a, exists z : M, x = mk' 
S y z
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `IsLocalization.eq_mk'_iff_mul_eq`：∀ {R : Type u_1} [inst : CommSemiring 
R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebr
a R S] [inst_3 : IsLoc…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `IsLocalization.Away.sec_spec`：sec_spec (s : S) : s * (algebraMap R S) (x
 ^ (IsLocalization.Away.sec x s).2) = algebraMap R S (IsLocalization.Away.sec x 
s).1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `IsLocalization.mk'_one`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Su
bmonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [in
st_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `IsLocalization.eq`：∀ {R : Type u_1} [inst : CommSemiring R] {M : Submono
id R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R S] [inst_3 
: IsLoc…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
（共 31 条，此处仅展示前 30 条）
-/
lemma span_range_mulNumerator_eq_top {s : Set R}
    (hsone : Ideal.span s = ⊤) {Rₜ : s → Type*} [∀ t, CommRing (Rₜ t)] [∀ t, Algebra R (Rₜ t)]
    [∀ t, IsLocalization.Away t.val (Rₜ t)]
    {p : (t : s) → Set (Rₜ t)} (htone : ∀ (r : s), Ideal.span (p r) = ⊤) :
    Ideal.span (Set.range (IsLocalization.Away.mulNumerator s p)) = ⊤ := by
  rw [← Ideal.radical_eq_top, eq_top_iff, ← hsone, Ideal.span_le]
  intro a ha
  have : IsLocalization (Submonoid.powers a) (Rₜ ⟨a, ha⟩) :=
    inferInstanceAs <| IsLocalization.Away (⟨a, ha⟩ : s).val (Rₜ ⟨a, ha⟩)
  have h₁ : Ideal.span (p ⟨a, ha⟩) ≤ Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) '' Set.range (IsLocalization.Away.mulNumerator s p)) := by
    rw [Ideal.span_le]
    intro x hx
    rw [SetLike.mem_coe, IsLocalization.mem_span_map (Submonoid.powers a)]
    refine ⟨a * (IsLocalization.Away.sec a x).1, Ideal.subset_span ⟨⟨⟨a, ha⟩, ⟨x, hx⟩⟩, rfl⟩, ?_⟩
    use ⟨a ^ ((IsLocalization.Away.sec a x).2 + 1), _, rfl⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, map_pow, map_mul, ← map_pow, pow_add, map_mul,
      ← mul_assoc, IsLocalization.Away.sec_spec a x, mul_comm, pow_one]
  have h₂ : IsLocalization.mk' (Rₜ ⟨a, ha⟩) 1 (1 : Submonoid.powers a) ∈ Ideal.span
      (algebraMap R (Rₜ ⟨a, ha⟩) ''
        (Set.range <| IsLocalization.Away.mulNumerator s p)) := by
    rw [IsLocalization.mk'_one]
    apply h₁
    simp [htone]
  rw [IsLocalization.mem_span_map (Submonoid.powers a)] at h₂
  obtain ⟨y, hy, ⟨-, m, rfl⟩, hyz⟩ := h₂
  rw [IsLocalization.eq] at hyz
  obtain ⟨⟨-, n, rfl⟩, hc⟩ := hyz
  simp only [OneMemClass.coe_one, one_mul, mul_one] at hc
  use n + m
  simpa [pow_add, hc] using Ideal.mul_mem_left _ _ hy
/-
**IsLocalization.Away.quotient_of_isIdempotentElem** 是 Mathlib 中的一个引理，位于命名空间 `Is
Localization.Away`。
形式化陈述：quotient_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) : IsLocaliz
ation.Away e (R ⧸ Ideal.span {1 - e})
参数：he : IsIdempotentElem e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.away_of_isIdempotentElem`：away_of_isIdempotentElem {R S} 
[CommRing R] [CommRing S] [Algebra R S] {e : R} (he : IsIdempotentElem e) (H : R
ingHom.ker (algebraMap R S) =…
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
lemma quotient_of_isIdempotentElem {e : R} (he : IsIdempotentElem e) :
    IsLocalization.Away e (R ⧸ Ideal.span {1 - e}) :=
  away_of_isIdempotentElem he Ideal.mk_ker Quotient.mk_surjective

end IsLocalization.Away

section saturated

variable {R : Type*} (S : Type*) [CommSemiring R] [CommSemiring S]
  [Algebra R S] (x : R) [IsLocalization.Away x S] {I J : Ideal R}

/-
**Ideal.le_of_map_algebraMap_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.le_of_map_algebraMap_le (hle : I.map (algebraMap R S) <= J.map (alge
braMap R S)) (hxJ : forall y : R, x * y in J -> y in J) : I <= J
参数：hle : I.map (algebraMap R S) <= J.map (algebraMap R S)；hxJ : forall y : R, x 
* y in J -> y in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsLocalization.algebraMap_mem_map_algebraMap_iff`：algebraMap_mem_map_alg
ebraMap_iff (I : Ideal R) (x : R) : algebraMap R S x in I.map (algebraMap R S) ↔
 exists m in M, m * x in I
· 使用定理 `mem_of_le_of_mem`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [
inst_1 : LE A] [IsConcreteLE A B] {S T : A},   S ≤ T → ∀ ⦃x : B⦄, x ∈ S → x ∈ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Ideal.le_of_map_algebraMap_le (hle : I.map (algebraMap R S) ≤ J.map (algebraMap R S))
    (hxJ : ∀ y : R, x * y ∈ J → y ∈ J) : I ≤ J := by
  intro y hy
  have hin : algebraMap R S y ∈ I.map (algebraMap R S) := Ideal.mem_map_of_mem (algebraMap R S) hy
  grw [hle, IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers x)] at hin
  obtain ⟨m, ⟨n, hn, rfl⟩, h⟩ := hin
  dsimp at h
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [add_comm, pow_add, pow_one, mul_assoc] at h
    exact ih <| hxJ _ h
/-
**Ideal.eq_of_map_algebraMap_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.eq_of_map_algebraMap_le (heq : I.map (algebraMap R S) = J.map (algeb
raMap R S)) (hxI : forall y : R, x * y in I -> y in I) (hxJ : forall y : R, x * 
y in J -> y in J) : I = J
参数：heq : I.map (algebraMap R S) = J.map (algebraMap R S)；hxI : forall y : R, x *
 y in I -> y in I；hxJ : forall y : R, x * y in J -> y in J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Ideal.le_of_map_algebraMap_le`：Ideal.le_of_map_algebraMap_le (hle : I.ma
p (algebraMap R S) <= J.map (algebraMap R S)) (hxJ : forall y : R, x * y in J ->
 y in J) : I <= J
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
-/
lemma Ideal.eq_of_map_algebraMap_le (heq : I.map (algebraMap R S) = J.map (algebraMap R S))
    (hxI : ∀ y : R, x * y ∈ I → y ∈ I) (hxJ : ∀ y : R, x * y ∈ J → y ∈ J) : I = J :=
  le_antisymm (le_of_map_algebraMap_le S x heq.le hxJ) (le_of_map_algebraMap_le S x heq.ge hxI)

end saturated

