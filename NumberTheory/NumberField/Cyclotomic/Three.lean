/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Pietro Monticone
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Fintype

/-!
# Third Cyclotomic Field

We gather various results about the third cyclotomic field. The following notations are used in this
file: `K` is a number field such that `IsCyclotomicExtension {3} ℚ K`, `ζ` is any primitive `3`-rd
root of unity in `K`, `η` is the element in the units of the ring of integers corresponding to `ζ`
and `λ = η - 1`.

## Main results
* `IsCyclotomicExtension.Rat.Three.Units.mem`: Given a unit `u : (𝓞 K)ˣ`, we have that
  `u ∈ {1, -1, η, -η, η^2, -η^2}`.

* `IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent`: Given a unit
  `u : (𝓞 K)ˣ`, if `u` is congruent to an integer modulo `3`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma* (see for example [washington_cyclotomic],
Theorem 5.36).
-/

public section

open NumberField Units InfinitePlace nonZeroDivisors Polynomial

namespace IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (𝓞 K)ˣ)
local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

/-
**IsCyclotomicExtension.Rat.Three.coe_eta** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomi
cExtension.Rat.Three`。
形式化陈述：coe_eta : (η : 𝓞 K) = hζ.toInteger
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
-/
lemma coe_eta : (η : 𝓞 K) = hζ.toInteger := rfl
/-
**IsCyclotomicExtension.Rat.Three._root_.IsPrimitiveRoot.toInteger_cube_eq_one**
 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsPrimitiveRoot.toInteger_cube_eq_one : hζ.toInteger ^ 3 = 1 :=
  hζ.toInteger_isPrimitiveRoot.pow_eq_one

/-- Let `u` be a unit in `(𝓞 K)ˣ`, then `u ∈ [1, -1, η, -η, η^2, -η^2]`. -/
-- Here `List` is more convenient than `Finset`, even if further from the informal statement.
-- For example, `fin_cases` below does not work with a `Finset`.
/-
**IsCyclotomicExtension.Rat.Three.Units.mem** 是 Mathlib 中的一个定理，位于命名空间 `IsCycloto
micExtension.Rat.Three.Units`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : 
(NumberField.RingOfIntegers K)ˣ)   [inst_1 : NumberField K] [IsCyclotomicExtensi
on {3} ℚ K], u ∈ [1, -1, ⋯.unit, -⋯.unit, ⋯.unit ^ 2, -⋯.unit ^ 2]
参数：hζ : IsPrimitiveRoot ζ 3；u : (NumberField.RingOfIntegers K)ˣ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces`：card
_eq_nrRealPlaces_add_nrComplexPlaces : Fintype.card (InfinitePlace K) = nrRealPl
aces K + nrComplexPlaces K
· 使用定理 `IsCyclotomicExtension.numberField`：numberField [h : NumberField K] [Fini
te S] [IsCyclotomicExtension S K L] : NumberField L
· 使用定理 `Rat.numberField`：NumberField ℚ
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero`：nrRealPlaces_eq_zero [Is
CyclotomicExtension {n} Rat K] (hn : 2 < n) : haveI
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two`：nrComplexP
laces_eq_totient_div_two [h : IsCyclotomicExtension {n} Rat K] : haveI
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `NumberField.Units.exist_unique_eq_mul_prod`：∀ (K : Type u_1) [inst : Fie
ld K] [inst_1 : NumberField K] (x : (NumberField.RingOfIntegers K)ˣ),   ∃! ζe, x
 = ↑ζe.1 * ∏ i, NumberField.Unit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Finset.univ_eq_empty_iff`：univ_eq_empty_iff : (univ : Finset α) = ∅ ↔ Is
Empty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isOfFinOrder_iff_pow_eq_one`：isOfFinOrder_iff_pow_eq_one : IsOfFinOrder 
x ↔ exists n, 0 < n ∧ x ^ n = 1
· 使用定理 `CommGroup.mem_torsion`：mem_torsion (g : G) : g in torsion G ↔ IsOfFinOrd
er g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
（共 54 条，此处仅展示前 30 条）
-/
theorem Units.mem [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] := by
  have hrank : rank K = 0 := by
    dsimp only [rank]
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, nrRealPlaces_eq_zero (n := 3) K (by decide),
      zero_add, nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  obtain ⟨⟨x, e⟩, hxu, -⟩ := exist_unique_eq_mul_prod _ u
  replace hxu : u = x := by
    rw [← mul_one x.1, hxu]
    apply congr_arg
    rw [← Finset.prod_empty]
    congr
    rw [Finset.univ_eq_empty_iff, hrank]
    infer_instance
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (CommGroup.mem_torsion _).1 x.2
  replace hn : (↑u : K) ^ ((⟨n, hnpos⟩ : ℕ+) : ℕ) = 1 := by
    rw [← map_pow]
    convert! map_one (algebraMap (𝓞 K) K)
    rw_mod_cast [hxu, hn]
    simp
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_isOfFinOrder (by decide)
    (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hnpos, hn⟩)
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = η ^ r ∨ ↑u = -η ^ r := by
    rcases hru with h | h
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr <;> rcases hru with h | h <;> simp [h]

set_option backward.isDefEq.respectTransparency.types false in
/-- We have that `λ ^ 2 = -3 * η`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_sq** 是 Mathlib 中的一个引理，位于命名空间 `IsCycloto
micExtension.Rat.Three`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have that `λ ^ 2 = -3 * η`.
-/
private lemma lambda_sq : λ ^ 2 = -3 * η := by
  ext
  calc (λ ^ 2 : K) = η ^ 2 + η + 1 - 3 * η := by
        simp only [IsUnit.unit_spec]; ring
  _ = 0 - 3 * η := by simpa using hζ.isRoot_cyclotomic (by decide)
  _ = -3 * η := by ring

set_option backward.isDefEq.respectTransparency.types false in
/-- We have that `η ^ 2 = -η - 1`. -/
/-
**IsCyclotomicExtension.Rat.Three.eta_sq** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomic
Extension.Rat.Three`。
形式化陈述：eta_sq : (η ^ 2 : 𝓞 K) = -η - 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `add_eq_zero_iff_eq_neg`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ a = -b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `NumberField.RingOfIntegers.ext`：∀ {K : Type u_1} [inst : Field K] {x y :
 NumberField.RingOfIntegers K}, ↑x = ↑y → x = y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Polynomial.cyclotomic_three`：cyclotomic_three (R : Type*) [Ring R] : cyc
lotomic 3 R = X ^ 2 + X + 1
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `IsPrimitiveRoot.isRoot_cyclotomic`：∀ {R : Type u_1} [inst : CommRing R] 
{n : ℕ} [IsDomain R],   0 < n → ∀ {μ : R}, IsPrimitiveRoot μ n → (Polynomial.cyc
lotomic n R).IsRoot μ
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p

--- 原说明 ---
We have that `η ^ 2 = -η - 1`.
-/
lemma eta_sq : (η ^ 2 : 𝓞 K) = -η - 1 := by
  rw [← neg_add', ← add_eq_zero_iff_eq_neg, ← add_assoc]
  ext; simpa using hζ.isRoot_cyclotomic (by decide)

set_option backward.isDefEq.respectTransparency.types false in
/-- If a unit `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or `u = -1`.

This is a special case of the so-called *Kummer's lemma*. -/
/-
**IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent** 是 Mat
hlib 中的一个定理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：eq_one_or_neg_one_of_unit_of_congruent [NumberField K] [IsCyclotomicExtens
ion {3} Rat K] (hcong : exists n : Int, fun ^ 2 ∣ (u - n : 𝓞 K)) : u = 1 ∨ u = -
1
参数：hcong : exists n : Int, fun ^ 2 ∣ (u - n : 𝓞 K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `_private.Mathlib.NumberTheory.NumberField.Cyclotomic.Three.0.IsCyclotomi
cExtension.Rat.Three.lambda_sq`：∀ {K : Type u_1} [inst : Field K] {ζ : K} (hζ : 
IsPrimitiveRoot ζ 3), (hζ.toInteger - 1) ^ 2 = -3 * ↑⋯.unit
· 使用定理 `IsCyclotomicExtension.Rat.Three.Units.mem`：∀ {K : Type u_1} [inst : Fiel
d K] {ζ : K} (hζ : IsPrimitiveRoot ζ 3) (u : (NumberField.RingOfIntegers K)ˣ)   
[inst_1 : NumberField K] [IsCyc…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsPrimitiveRoot.not_exists_int_prime_dvd_sub_of_prime_ne_two'`：not_exist
s_int_prime_dvd_sub_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} Rat K] (
hζ : IsPrimitiveRoot ζ p) (hodd : p != 2) : ¬(exist…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
· 使用定理 `SubringClass.toNegMemClass`：∀ {S : Type u_1} {R : outParam (Type u)} {in
st : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   NegMemC
lass S R
· 使用定理 `Subalgebra.instSubringClass`：∀ {R : Type u_1} {A : Type u_2} [inst : Com
mRing R] [inst_1 : Ring A] [inst_2 : Algebra R A],   SubringClass (Subalgebra R 
A) A
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
If a unit `u` is congruent to an integer modulo `λ ^ 2`, then `u = 1` or `u = -1
`.

This is a special case of the so-called *Kummer's lemma*.
-/
theorem eq_one_or_neg_one_of_unit_of_congruent
    [NumberField K] [IsCyclotomicExtension {3} ℚ K] (hcong : ∃ n : ℤ, λ ^ 2 ∣ (u - n : 𝓞 K)) :
    u = 1 ∨ u = -1 := by
  replace hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K) := by
    obtain ⟨n, x, hx⟩ := hcong
    exact ⟨n, -η * x, by rw [← mul_assoc, mul_neg, ← neg_mul, ← lambda_sq, hx]⟩
  have := Units.mem hζ u
  fin_cases this
  · left; rfl
  · right; rfl
  all_goals exfalso
  · exact hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide) hcong
  · apply hζ.not_exists_int_prime_dvd_sub_of_prime_ne_two' (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    simp only [Nat.cast_ofNat, mul_neg, Int.cast_neg, ← neg_add, ← hx, Units.val_neg,
      IsUnit.unit_spec, RingOfIntegers.neg_mk, neg_neg]
  · exact (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide) hcong
  · apply (hζ.pow_of_coprime 2 (by decide)).not_exists_int_prime_dvd_sub_of_prime_ne_two'
      (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, sub_eq_iff_eq_add.2 ?_⟩
    have : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
    simp only [this, Nat.cast_ofNat, mul_neg, Int.cast_neg, ← neg_add, ← sub_eq_iff_eq_add.1 hx,
      Units.val_neg, val_pow_eq_pow_val, IsUnit.unit_spec, neg_neg]

variable (x : 𝓞 K)

/-- Let `(x : 𝓞 K)`. Then we have that `λ` divides one amongst `x`, `x - 1` and `x + 1`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one** 是 M
athlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：lambda_dvd_or_dvd_sub_one_or_dvd_add_one [NumberField K] [IsCyclotomicExte
nsion {3} Rat K] : fun ∣ x ∨ fun ∣ x - 1 ∨ fun ∣ x + 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `IsPrimitiveRoot.finite_quotient_toInteger_sub_one`：finite_quotient_toInt
eger_sub_one [NumberField K] {k : Nat} (hk : 1 < k) (hζ : IsPrimitiveRoot ζ k) :
 haveI : NeZero k
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `IsPrimitiveRoot.card_quotient_toInteger_sub_one`：card_quotient_toInteger
_sub_one [NumberField K] {k : Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : Nat.c
ard (𝓞 K ⧸ Ideal.span {hζ.toInteger -…
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用引理 `IsPrimitiveRoot.norm_toInteger_sub_one_of_prime_ne_two'`：norm_toInteger_
sub_one_of_prime_ne_two' [hcycl : IsCyclotomicExtension {p} Rat K] (hζ : IsPrimi
tiveRoot ζ p) (h : p != 2) : Algebra.norm Int…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.univ_of_card_le_three`：Finset.univ_of_card_le_three (h : Fintype.
card R <= 3) : (univ : Finset R) = {0, 1, -1}
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `RingHom.map_add`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a + b) = f a + f b
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
Let `(x : 𝓞 K)`. Then we have that `λ` divides one amongst `x`, `x - 1` and `x +
 1`.
-/
lemma lambda_dvd_or_dvd_sub_one_or_dvd_add_one [NumberField K] [IsCyclotomicExtension {3} ℚ K] :
    λ ∣ x ∨ λ ∣ x - 1 ∨ λ ∣ x + 1 := by
  classical
  have := hζ.finite_quotient_toInteger_sub_one (by decide)
  let _ := Fintype.ofFinite (𝓞 K ⧸ Ideal.span {λ})
  let _ : Ring (𝓞 K ⧸ Ideal.span {λ}) := CommRing.toRing -- to speed up instance synthesis
  let _ : AddGroup (𝓞 K ⧸ Ideal.span {λ}) := AddGroupWithOne.toAddGroup -- ditto
  have := Finset.mem_univ (Ideal.Quotient.mk (Ideal.span {λ}) x)
  have h3 : Fintype.card (𝓞 K ⧸ Ideal.span {λ}) = 3 := by
    rw [← Nat.card_eq_fintype_card, hζ.card_quotient_toInteger_sub_one,
      hζ.norm_toInteger_sub_one_of_prime_ne_two' (by decide)]
    simp only [Nat.cast_ofNat, Int.reduceAbs]
  rw [Finset.univ_of_card_le_three h3.le] at this
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h | h | h
  · left
    exact Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 h
  · right; left
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_sub, h, RingHom.map_one, sub_self]
  · right; right
    refine Ideal.mem_span_singleton.1 <| Ideal.Quotient.eq_zero_iff_mem.1 ?_
    rw [RingHom.map_add, h, RingHom.map_one, neg_add_cancel]

/-- We have that `η ^ 2 + η + 1 = 0`. -/
/-
**IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one** 是 Mathlib 中的一个引理，位于命名
空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：eta_sq_add_eta_add_one : (η : 𝓞 K) ^ 2 + η + 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCyclotomicExtension.Rat.Three.eta_sq`：eta_sq : (η ^ 2 : 𝓞 K) = -η - 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
We have that `η ^ 2 + η + 1 = 0`.
-/
lemma eta_sq_add_eta_add_one : (η : 𝓞 K) ^ 2 + η + 1 = 0 := by
  rw [eta_sq]
  ring

/-- We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`. -/
/-
**IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul** 是 Mathlib 中的一个引理，位于命名空间 
`IsCyclotomicExtension.Rat.Three`。
形式化陈述：cube_sub_one_eq_mul : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
We have that `x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)`.
-/
lemma cube_sub_one_eq_mul : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2) := by
  symm
  calc _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + η ^ 3) - η ^ 3 := by ring
  _ = x ^ 3 - x ^ 2 * (η ^ 2 + η + 1) + x * (η ^ 2 + η + 1) - 1 := by
    simp [hζ.toInteger_cube_eq_one]
  _ = x ^ 3 - 1 := by rw [eta_sq_add_eta_add_one hζ]; ring

variable [NumberField K] [IsCyclotomicExtension {3} ℚ K]

/-- We have that `λ` divides `x * (x - 1) * (x - (η + 1))`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_dvd_mul_sub_one_mul_sub_eta_add_one** 是
 Mathlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：lambda_dvd_mul_sub_one_mul_sub_eta_add_one : fun ∣ x * (x - 1) * (x - (η +
 1))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用引理 `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one
`：lambda_dvd_or_dvd_sub_one_or_dvd_add_one [NumberField K] [IsCyclotomicExtensio
n {3} Rat K] : fun ∣ x ∨ fun ∣ x - 1 ∨ fun ∣ x + 1
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `dvd_mul_of_dvd_right`：dvd_mul_of_dvd_right (h : a ∣ b) (c : α) : a ∣ c *
 b
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
We have that `λ` divides `x * (x - 1) * (x - (η + 1))`.
-/
lemma lambda_dvd_mul_sub_one_mul_sub_eta_add_one : λ ∣ x * (x - 1) * (x - (η + 1)) := by
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hζ x with h | h | h
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left h _) _
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right h _) _
  · refine dvd_mul_of_dvd_right ?_ _
    rw [show x - (η + 1) = x + 1 - (η - 1 + 3) by ring]
    exact dvd_sub h <| dvd_add dvd_rfl hζ.toInteger_sub_one_dvd_prime'

/-- If `λ` divides `x - 1`, then `λ ^ 4` divides `x ^ 3 - 1`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_on
e** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : fun ∣ x - 1
) : fun ^ 4 ∣ x ^ 3 - 1
参数：h : fun ∣ x - 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用引理 `IsPrimitiveRoot.toInteger_isPrimitiveRoot`：toInteger_isPrimitiveRoot {k 
: Nat} [NeZero k] (hζ : IsPrimitiveRoot ζ k) : IsPrimitiveRoot hζ.toInteger k
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsCyclotomicExtension.Rat.Three.cube_sub_one_eq_mul`：cube_sub_one_eq_mul
 : x ^ 3 - 1 = (x - 1) * (x - η) * (x - η ^ 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If `λ` divides `x - 1`, then `λ ^ 4` divides `x ^ 3 - 1`.
-/
lemma lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : λ ∣ x - 1) :
    λ ^ 4 ∣ x ^ 3 - 1 := by
  obtain ⟨y, hy⟩ := h
  have : x ^ 3 - 1 = λ ^ 3 * (y * (y - 1) * (y - (η + 1))) := by
    calc _ = (x - 1) * (x - 1 - λ) * (x - 1 - λ * (η + 1)) := by
          simp only [coe_eta, cube_sub_one_eq_mul hζ x]; ring
    _ = _ := by rw [hy]; ring
  rw [this, pow_succ]
  exact mul_dvd_mul_left _ (lambda_dvd_mul_sub_one_mul_sub_eta_add_one hζ y)

/-- If `λ` divides `x + 1`, then `λ ^ 4` divides `x ^ 3 + 1`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_add_one_of_dvd_add_on
e** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : fun ∣ x + 1
) : fun ^ 4 ∣ x ^ 3 + 1
参数：h : fun ∣ x + 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_add'`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α), -
(a + b) = -a - b
· 使用定理 `Dvd.dvd.neg_right`：∀ {α : Type u_1} [inst : Semigroup α] [inst_1 : HasDi
stribNeg α] {a b : α}, a ∣ b → a ∣ -b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
If `λ` divides `x + 1`, then `λ ^ 4` divides `x ^ 3 + 1`.
-/
lemma lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : λ ∣ x + 1) :
    λ ^ 4 ∣ x ^ 3 + 1 := by
  replace h : λ ∣ -x - 1 := by
    convert! h.neg_right using 1
    exact (neg_add' x 1).symm
  convert! (lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ h).neg_right using 1
  ring

/-- If `λ` does not divide `x`, then `λ ^ 4` divides `x ^ 3 - 1` or `x ^ 3 + 1`. -/
/-
**IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_or_add_one_of
_lambda_not_dvd** 是 Mathlib 中的一个引理，位于命名空间 `IsCyclotomicExtension.Rat.Three`。
形式化陈述：lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd {x : 𝓞 K} (h
 : ¬ fun ∣ x) : fun ^ 4 ∣ x ^ 3 - 1 ∨ fun ^ 4 ∣ x ^ 3 + 1
参数：h : ¬ fun ∣ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.to_charZero`：∀ {K : Type u_1} {inst : Field K} [self : Numbe
rField K], CharZero K
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `IsCyclotomicExtension.Rat.Three.lambda_dvd_or_dvd_sub_one_or_dvd_add_one
`：lambda_dvd_or_dvd_sub_one_or_dvd_add_one [NumberField K] [IsCyclotomicExtensio
n {3} Rat K] : fun ∣ x ∨ fun ∣ x - 1 ∨ fun ∣ x + 1
· 使用引理 `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_sub_one_of_dvd_
sub_one`：lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one {x : 𝓞 K} (h : fun ∣ x 
- 1) : fun ^ 4 ∣ x ^ 3 - 1
· 使用引理 `IsCyclotomicExtension.Rat.Three.lambda_pow_four_dvd_cube_add_one_of_dvd_
add_one`：lambda_pow_four_dvd_cube_add_one_of_dvd_add_one {x : 𝓞 K} (h : fun ∣ x 
+ 1) : fun ^ 4 ∣ x ^ 3 + 1

--- 原说明 ---
If `λ` does not divide `x`, then `λ ^ 4` divides `x ^ 3 - 1` or `x ^ 3 + 1`.
-/
lemma lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd {x : 𝓞 K} (h : ¬ λ ∣ x) :
    λ ^ 4 ∣ x ^ 3 - 1 ∨ λ ^ 4 ∣ x ^ 3 + 1 := by
  rcases lambda_dvd_or_dvd_sub_one_or_dvd_add_one hζ x with H | H | H
  · contradiction
  · left
    exact lambda_pow_four_dvd_cube_sub_one_of_dvd_sub_one hζ H
  · right
    exact lambda_pow_four_dvd_cube_add_one_of_dvd_add_one hζ H

end Three

end Rat

end IsCyclotomicExtension

