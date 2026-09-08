/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Data.Fintype.Inv
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Tactic.FieldSimp

/-!
# Integral domains

Assorted theorems about integral domains.

## Main theorems

* `isCyclic_of_subgroup_isDomain`: A finite subgroup of the units of an integral domain is cyclic.
* `Fintype.fieldOfDomain`: A finite integral domain is a field.

## Notes

Wedderburn's little theorem, which shows that all finite division rings are actually fields,
is in `Mathlib/RingTheory/LittleWedderburn.lean`.

## Tags

integral domain, finite integral domain, finite field
-/

@[expose] public section

section

open Finset Polynomial Function

section CancelMonoidWithZero

-- There doesn't seem to be a better home for these right now
variable {M : Type*} [MonoidWithZero M] [Finite M]

/-
**mul_right_bijective_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_right_bijective_of_finite₀ [IsLeftCancelMulZero M] {a : M} (ha : a ≠ 0) :
    Bijective fun b => a * b :=
  Finite.injective_iff_bijective.1 <| mul_right_injective₀ ha
/-
**mul_left_bijective_of_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_left_bijective_of_finite₀ [IsRightCancelMulZero M] {a : M} (ha : a ≠ 0) :
    Bijective fun b => b * a :=
  Finite.injective_iff_bijective.1 <| mul_left_injective₀ ha

/-- Every finite nontrivial cancellative monoid with zero is a group with zero. -/
@[instance_reducible]
/-
**Fintype.groupWithZeroOfCancel** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.groupWithZeroOfCancel (M : Type*) [MonoidWithZero M] [IsLeftCancel
MulZero M] [DecidableEq M] [Fintype M] [Nontrivial M] : GroupWithZero M
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every finite nontrivial cancellative monoid with zero is a group with zero.
-/
def Fintype.groupWithZeroOfCancel (M : Type*) [MonoidWithZero M] [IsLeftCancelMulZero M]
    [DecidableEq M] [Fintype M] [Nontrivial M] : GroupWithZero M :=
  { ‹Nontrivial M›,
    ‹MonoidWithZero M› with
    inv := fun a => if h : a = 0 then 0 else Fintype.bijInv (mul_right_bijective_of_finite₀ h) 1
    mul_inv_cancel := fun a ha => by
      simp only [dif_neg ha]
      exact Fintype.rightInverse_bijInv _ _
    inv_zero := by simp }
/-
**exists_eq_pow_of_mul_eq_pow_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R] [GCDMo
noid R] [Subsingleton Rˣ] {a b c : R} {n : Nat} (cp : IsCoprime a b) (h : a * b 
= c ^ n) : exists d : R, a = d ^ n
参数：cp : IsCoprime a b；h : a * b = c ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_pow_of_mul_eq_pow`：exists_eq_pow_of_mul_eq_pow [GCDMonoid α] [
Subsingleton αˣ] {a b c : α} (hab : IsUnit (gcd a b)) {k : Nat} (h : a * b = c ^
 k) : exists d : …
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_add`：dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣
 c) : a ∣ b + c
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `GCDMonoid.gcd_dvd_left`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} [
self : GCDMonoid α] (a b : α), gcd a b ∣ a
· 使用定理 `GCDMonoid.gcd_dvd_right`：∀ {α : Type u_2} {inst : CommMonoidWithZero α} 
[self : GCDMonoid α] (a b : α), gcd a b ∣ b
-/
theorem exists_eq_pow_of_mul_eq_pow_of_coprime {R : Type*} [CommSemiring R]
    [GCDMonoid R] [Subsingleton Rˣ] {a b c : R} {n : ℕ} (cp : IsCoprime a b) (h : a * b = c ^ n) :
    ∃ d : R, a = d ^ n := by
  refine exists_eq_pow_of_mul_eq_pow (isUnit_of_dvd_one ?_) h
  obtain ⟨x, y, hxy⟩ := cp
  rw [← hxy]
  exact dvd_add (dvd_mul_of_dvd_right (gcd_dvd_left _ _) _)
    (dvd_mul_of_dvd_right (gcd_dvd_right _ _) _)

nonrec
/-
**Finset.exists_eq_pow_of_mul_eq_pow_of_coprime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring 
R] [GCDMonoid R] [Subsingleton Rˣ] {n : Nat} {c : R} {s : Finset ι} {f : ι -> R}
 (h : forall i in s, forall j in s, i != j -> IsCoprime (f i) (f j)) (hprod : ∏ 
i in s, f i = c ^ n) : forall i in s, exists d : R, f i = d ^ n
参数：h : forall i in s, forall j in s, i != j -> IsCoprime (f i) (f j)；hprod : ∏ i
 in s, f i = c ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_pow_of_mul_eq_pow_of_coprime`：exists_eq_pow_of_mul_eq_pow_of_c
oprime {R : Type*} [CommSemiring R] [GCDMonoid R] [Subsingleton Rˣ] {a b c : R} 
{n : Nat} (cp : IsCoprime a …
· 使用定理 `IsCoprime.prod_right`：IsCoprime.prod_right : (forall i in t, IsCoprime x
 (s i)) -> IsCoprime x (∏ i in t, s i)
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
-/
theorem Finset.exists_eq_pow_of_mul_eq_pow_of_coprime {ι R : Type*} [CommSemiring R]
    [GCDMonoid R] [Subsingleton Rˣ] {n : ℕ} {c : R} {s : Finset ι} {f : ι → R}
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → IsCoprime (f i) (f j))
    (hprod : ∏ i ∈ s, f i = c ^ n) : ∀ i ∈ s, ∃ d : R, f i = d ^ n := by
  classical
    intro i hi
    rw [← insert_erase hi, prod_insert (notMem_erase i s)] at hprod
    refine
      exists_eq_pow_of_mul_eq_pow_of_coprime
        (IsCoprime.prod_right fun j hj => h i hi j (erase_subset i s hj) fun hij => ?_) hprod
    rw [hij] at hj
    exact (s.notMem_erase _) hj

end CancelMonoidWithZero

variable {R : Type*} {G : Type*}

section Ring

/-- Every finite domain is a division ring. More generally, they are fields; this can be found in
`Mathlib/RingTheory/LittleWedderburn.lean`. -/
@[instance_reducible]
/-
**Fintype.divisionRingOfIsDomain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [Decidabl
eEq R] [Fintype R] : DivisionRing R where __
参数：R : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GroupWithZero.div_eq_mul_inv`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a b : G₀), a / b = a * b⁻¹
· 使用定理 `GroupWithZero.zpow_zero'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (a :
 G₀), a ^ 0 = 1
· 使用定理 `GroupWithZero.zpow_succ'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n :
 ℕ) (a : G₀), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `GroupWithZero.zpow_neg'`：∀ {G₀ : Type u} [self : GroupWithZero G₀] (n : 
ℕ) (a : G₀), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `GroupWithZero.mul_inv_cancel`：∀ {G₀ : Type u} [self : GroupWithZero G₀] 
(a : G₀), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `GroupWithZero.inv_zero`：∀ {G₀ : Type u} [self : GroupWithZero G₀], 0⁻¹ =
 0

--- 原说明 ---
Every finite domain is a division ring. More generally, they are fields; this ca
n be found in
`Mathlib/RingTheory/LittleWedderburn.lean`.
-/
def Fintype.divisionRingOfIsDomain (R : Type*) [Ring R] [IsDomain R] [DecidableEq R] [Fintype R] :
    DivisionRing R where
  __ := (‹Ring R› :) -- this also works without the `( :)`, but it's slightly slow
  __ := Fintype.groupWithZeroOfCancel R
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

/-- Every finite commutative domain is a field. More generally, commutativity is not required: this
can be found in `Mathlib/RingTheory/LittleWedderburn.lean`. -/
@[instance_reducible]
/-
**Fintype.fieldOfDomain** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Finty
pe R] : Field R
参数：R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommRing.mul_comm`：∀ {α : Type u} [self : CommRing α] (a b : α), a * b =
 b * a
· 使用定理 `DivisionRing.div_eq_mul_inv`：∀ {K : Type u_2} [self : DivisionRing K] (a
 b : K), a / b = a * b⁻¹
· 使用定理 `DivisionRing.zpow_zero'`：∀ {K : Type u_2} [self : DivisionRing K] (a : K
), a ^ 0 = 1
· 使用定理 `DivisionRing.zpow_succ'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ
) (a : K), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivisionRing.zpow_neg'`：∀ {K : Type u_2} [self : DivisionRing K] (n : ℕ)
 (a : K), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `DivisionRing.mul_inv_cancel`：∀ {K : Type u_2} [self : DivisionRing K] (a
 : K), a ≠ 0 → a * a⁻¹ = 1
· 使用定理 `DivisionRing.inv_zero`：∀ {K : Type u_2} [self : DivisionRing K], 0⁻¹ = 0
· 使用定理 `DivisionRing.nnratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q 
: ℚ≥0), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.nnqsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ≥0) (a : K), DivisionRing.nnqsmul q a = ↑q * a
· 使用定理 `DivisionRing.ratCast_def`：∀ {K : Type u_2} [self : DivisionRing K] (q : 
ℚ), ↑q = ↑q.num / ↑q.den
· 使用定理 `DivisionRing.qsmul_def`：∀ {K : Type u_2} [self : DivisionRing K] (a : ℚ)
 (x : K), DivisionRing.qsmul a x = ↑a * x

--- 原说明 ---
Every finite commutative domain is a field. More generally, commutativity is not
 required: this
can be found in `Mathlib/RingTheory/LittleWedderburn.lean`.
-/
def Fintype.fieldOfDomain (R) [CommRing R] [IsDomain R] [DecidableEq R] [Fintype R] : Field R :=
  { Fintype.divisionRingOfIsDomain R, ‹CommRing R› with }
/-
**Finite.isField_of_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsFiel
d R
参数：R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Field.toIsField`：Field.toIsField (R : Type u) [Field R] : IsField R
-/
theorem Finite.isField_of_domain (R) [CommRing R] [IsDomain R] [Finite R] : IsField R := by
  cases nonempty_fintype R
  exact @Field.toIsField R (@Fintype.fieldOfDomain R _ _ (Classical.decEq R) _)

end Ring

variable [CommRing R] [IsDomain R] [Group G]

/-
**card_nthRoots_subgroup_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G ->* R) (hf
 : Injective f) {n : Nat} (hn : 0 < n) (g₀ : G) : #{g | g ^ n = g₀} <= Multiset.
card (nthRoots n (f g₀))
参数：f : G ->* R；hf : Injective f；hn : 0 < n；g₀ : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_le_card_of_injOn`：card_le_card_of_injOn (f : α -> β) (hf : S
et.MapsTo f s t) (f_inj : (s : Set α).InjOn f) : #s <= #t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_filter`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred
 p] (s : Finset α), ↑(Finset.filter p s) = {x | x ∈ s ∧ p x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Multiset.toFinset_card_le`：Multiset.toFinset_card_le : #m.toFinset <= Mu
ltiset.card m
-/
theorem card_nthRoots_subgroup_units [Fintype G] [DecidableEq G] (f : G →* R) (hf : Injective f)
    {n : ℕ} (hn : 0 < n) (g₀ : G) :
    #{g | g ^ n = g₀} ≤ Multiset.card (nthRoots n (f g₀)) := by
  have : DecidableEq R := Classical.decEq _
  calc
    _ ≤ #(nthRoots n (f g₀)).toFinset :=
      card_le_card_of_injOn f (by aesop (add safe unfold Set.MapsTo)) hf.injOn
    _ ≤ _ := (nthRoots n (f g₀)).toFinset_card_le

/-- A finite subgroup of the unit group of an integral domain is cyclic. -/
/-
**isCyclic_of_injective_ringHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCyclic_of_injective_ringHom [Finite G] (f : G ->* R) (hf : Injective f) 
: IsCyclic G
参数：f : G ->* R；hf : Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `isCyclic_of_card_pow_eq_one_le`：isCyclic_of_card_pow_eq_one_le : IsCycli
c α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `card_nthRoots_subgroup_units`：card_nthRoots_subgroup_units [Fintype G] [
DecidableEq G] (f : G ->* R) (hf : Injective f) {n : Nat} (hn : 0 < n) (g₀ : G) 
: #{g | g ^ n = g₀…
· 使用定理 `Polynomial.card_nthRoots`：card_nthRoots (n : Nat) (a : R) : Multiset.car
d (nthRoots n a) <= n

--- 原说明 ---
A finite subgroup of the unit group of an integral domain is cyclic.
-/
theorem isCyclic_of_injective_ringHom [Finite G] (f : G →* R) (hf : Injective f) : IsCyclic G := by
  classical
    cases nonempty_fintype G
    apply isCyclic_of_card_pow_eq_one_le
    intro n hn
    exact le_trans (card_nthRoots_subgroup_units f hf hn 1) (card_nthRoots n (f 1))

@[deprecated (since := "2026-03-04")]
alias isCyclic_of_subgroup_isDomain := isCyclic_of_injective_ringHom

/-- The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this requires only
`Finite Rˣ` rather than deducing it from `Finite R`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The unit group of a finite integral domain is cyclic.

To support `ℤˣ` and other infinite monoids with finite groups of units, this req
uires only
`Finite Rˣ` rather than deducing it from `Finite R`.
-/
instance [Finite Rˣ] : IsCyclic Rˣ :=
  isCyclic_of_injective_ringHom (Units.coeHom R) Units.val_injective

section

variable (S : Subgroup Rˣ) [Finite S]

/-- A finite subgroup of the units of an integral domain is cyclic. -/
/-
**isCyclic_subgroup_units** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：isCyclic_subgroup_units : IsCyclic S
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isCyclic_of_injective_ringHom`：isCyclic_of_injective_ringHom [Finite G] 
(f : G ->* R) (hf : Injective f) : IsCyclic G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Units.val_injective`：∀ {α : Type u} [inst : Monoid α], Function.Injectiv
e Units.val
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
A finite subgroup of the units of an integral domain is cyclic.
-/
instance isCyclic_subgroup_units : IsCyclic S :=
  isCyclic_of_injective_ringHom { toFun s := (s.val : R), map_one' := rfl, map_mul' := by simp }
    (Units.val_injective.comp Subtype.val_injective)

@[deprecated (since := "2026-03-03")] alias subgroup_units_cyclic := isCyclic_subgroup_units

end

-- TODO: find a better home (Mathlib.Algebra.Polynomial.PartialFractions)?
section EuclideanDivision

namespace Polynomial

variable (K : Type*) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

/-
**Polynomial.div_eq_quo_add_rem_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) : exists q r :
 R[X], r.degree < g.degree ∧ (algebraMap R[X] K f) / (algebraMap R[X] K g) = alg
ebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g)
参数：f : R[X]；hg : g.Monic。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero_iff`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst
 : Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] (f 
: F),…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsFractionRing.injective`：∀ (R : Type u_1) [inst : CommRing R] (K : Type
 u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K],   Funct
ion.Injective …
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₃`：div_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval / l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
（共 44 条，此处仅展示前 30 条）
-/
theorem div_eq_quo_add_rem_div (f : R[X]) {g : R[X]} (hg : g.Monic) :
    ∃ q r : R[X], r.degree < g.degree ∧
      (algebraMap R[X] K f) / (algebraMap R[X] K g) =
        algebraMap R[X] K q + (algebraMap R[X] K r) / (algebraMap R[X] K g) := by
  refine ⟨f /ₘ g, f %ₘ g, ?_, ?_⟩
  · exact degree_modByMonic_lt _ hg
  · have hg' : algebraMap R[X] K g ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R[X] K)).mpr (Monic.ne_zero hg)
    field_simp
    rw [add_comm, ← map_mul, ← map_add, modByMonic_add_div]

end Polynomial

end EuclideanDivision

variable [Fintype G]

/-- In an integral domain, a sum indexed by a nontrivial homomorphism from a finite group is zero.
-/
/-
**sum_hom_units_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_hom_units_eq_zero (f : G ->* R) (hf : f != 1) : ∑ g : G, f g = 0
参数：f : G ->* R；hf : f != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCyclic.exists_monoid_generator`：IsCyclic.exists_monoid_generator [Fini
te α] [IsCyclic α] : exists x : α, forall y : α, y in Submonoid.powers x
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} {s : Fin
set ι} [inst : AddCommMonoid M] [inst_1 : DecidableEq κ]   (f : κ → M) (g : ι → 
κ), ∑…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `MonoidHom.card_fiber_eq_of_mem_range`：card_fiber_eq_of_mem_range (f : F)
 {x y : M} (hx : x in Set.range f) (hy : y in Set.range f) : #{g | f g = x} = #{
g | f g = y}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `MonoidHom.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOne M] [in
st_1 : MulOne N] (f : M →* N), f 1 = 1
· 使用定理 `Finset.sum_subtype`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι),   (∀ (x : ι), x ∈ 
s ↔ p x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_nbij`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : ι 
→ κ),…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.coe_range`：coe_range (n : Nat) : (range n : Set Nat) = Set.Iio n
· 使用引理 `pow_injOn_Iio_orderOf`：pow_injOn_Iio_orderOf : (Set.Iio <| orderOf x).In
jOn (x ^ ·)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
In an integral domain, a sum indexed by a nontrivial homomorphism from a finite 
group is zero.
-/
theorem sum_hom_units_eq_zero (f : G →* R) (hf : f ≠ 1) : ∑ g : G, f g = 0 := by
  classical
    obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := MonoidHom.range f.toHomUnits)
    have hx1 : (x.1 : R) - 1 ≠ 0 := by
      rw [sub_ne_zero]
      contrapose hf
      ext g
      obtain ⟨n, hn⟩ := hx ⟨f.toHomUnits g, g, rfl⟩
      simpa [hf, Subtype.ext_iff, Units.ext_iff] using hn.symm
    let c := #{g | f.toHomUnits g = 1}
    calc
      ∑ g : G, f g = ∑ u ∈ univ.image f.toHomUnits, #{g | f.toHomUnits g = u} • (u : R) :=
        sum_comp ((↑) : Rˣ → R) f.toHomUnits
      _ = ∑ u ∈ univ.image f.toHomUnits, c • (u : R) :=
        (sum_congr rfl fun u hu => congr_arg₂ _ ?_ rfl)
      -- remaining goal 1, proven below
      _ = ∑ b : MonoidHom.range f.toHomUnits, c • (b.1 : R) :=
        (Finset.sum_subtype _ (by simp) _)
      _ = c • ∑ b : MonoidHom.range f.toHomUnits, (b.1 : R) := smul_sum.symm
      _ = c • 0 := congr_arg₂ _ rfl ?_
      -- remaining goal 2, proven below
      _ = 0 := smul_zero _
    · -- remaining goal 1
      apply MonoidHom.card_fiber_eq_of_mem_range f.toHomUnits
      · simpa only [mem_image, mem_univ, true_and, Set.mem_range] using hu
      · exact ⟨1, f.toHomUnits.map_one⟩
    -- remaining goal 2
    calc
      (∑ b : MonoidHom.range f.toHomUnits, (b.1 : R))
        = ∑ n ∈ range (orderOf x), (x.1 : R) ^ n :=
        Eq.symm <|
          sum_nbij (x ^ ·) (by simp)
            (by simpa using pow_injOn_Iio_orderOf)
            (fun b _ => let ⟨n, hn⟩ := hx b
              ⟨n % orderOf x, mem_range.2 (Nat.mod_lt _ (orderOf_pos _)), by simp [hn]⟩)
            (by simp)
      _ = 0 := ?_
    rw [← mul_left_inj' hx1, zero_mul, geom_sum_mul]
    norm_cast
    simp [pow_orderOf_eq_one]

/-- In an integral domain, a sum indexed by a homomorphism from a finite group is zero,
unless the homomorphism is trivial, in which case the sum is equal to the cardinality of the group.
-/
/-
**sum_hom_units** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_hom_units (f : G ->* R) [Decidable (f = 1)] : ∑ g : G, f g = if f = 1 
then Fintype.card G else 0
参数：f : G ->* R；f = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `sum_hom_units_eq_zero`：sum_hom_units_eq_zero (f : G ->* R) (hf : f != 1)
 : ∑ g : G, f g = 0

--- 原说明 ---
In an integral domain, a sum indexed by a homomorphism from a finite group is ze
ro,
unless the homomorphism is trivial, in which case the sum is equal to the cardin
ality of the group.
-/
theorem sum_hom_units (f : G →* R) [Decidable (f = 1)] :
    ∑ g : G, f g = if f = 1 then Fintype.card G else 0 := by
  split_ifs with h
  · simp [h]
  · rw [Nat.cast_zero]
    exact sum_hom_units_eq_zero f h

end

