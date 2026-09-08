/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching, Ashvni Narayanan, Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Lemmas about units in `ZMod`.
-/

@[expose] public section

assert_not_exists TwoSidedIdeal

namespace ZMod

variable {n m : ℕ}
/-- `unitsMap` is a group homomorphism that maps units of `ZMod m` to units of `ZMod n` when `n`
divides `m`. -/
/-
**ZMod.unitsMap** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：unitsMap (hm : n ∣ m) : (ZMod m)ˣ ->* (ZMod n)ˣ
参数：hm : n ∣ m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`unitsMap` is a group homomorphism that maps units of `ZMod m` to units of `ZMod
 n` when `n`
divides `m`.
-/
def unitsMap (hm : n ∣ m) : (ZMod m)ˣ →* (ZMod n)ˣ := Units.map (castHom hm (ZMod n))
/-
**ZMod.unitsMap_def** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n))
参数：hm : n ∣ m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma unitsMap_def (hm : n ∣ m) : unitsMap hm = Units.map (castHom hm (ZMod n)) := rfl
/-
**ZMod.unitsMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：unitsMap_comp {d : Nat} (hm : n ∣ m) (hd : m ∣ d) : (unitsMap hm).comp (un
itsMap hd) = unitsMap (dvd_trans hm hd)
参数：hm : n ∣ m；hd : m ∣ d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.map_comp`：map_comp (f : M ->* N) (g : N ->* P) : map (g.comp f) = 
(map g).comp (map f)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `ZMod.castHom_comp`：castHom_comp {m d : Nat} (hm : n ∣ m) (hd : m ∣ d) : 
(castHom hm (ZMod n)).comp (castHom hd (ZMod m)) = castHom (dvd_trans hm hd) (ZM
od n)
-/
lemma unitsMap_comp {d : ℕ} (hm : n ∣ m) (hd : m ∣ d) :
    (unitsMap hm).comp (unitsMap hd) = unitsMap (dvd_trans hm hd) := by
  simp only [unitsMap_def]
  rw [← Units.map_comp]
  exact congr_arg Units.map <| congr_arg RingHom.toMonoidHom <| castHom_comp hm hd

@[simp]
/-
**ZMod.unitsMap_self** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：unitsMap_self (n : Nat) : unitsMap (dvd_refl n) = MonoidHom.id _
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidHomClass.toMonoidHom.congr_simp`：∀ {M : Type u_4} {N : Type u_5} {
F : Type u_9} [inst : MulOne M] [inst_1 : MulOne N] [inst_2 : FunLike F M N]   [
inst_3 : MonoidHomClass F M…
· 使用引理 `ZMod.castHom_self`：castHom_self : ZMod.castHom dvd_rfl (ZMod n) = RingHo
m.id (ZMod n)
· 使用定理 `Units.map_id`：map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma unitsMap_self (n : ℕ) : unitsMap (dvd_refl n) = MonoidHom.id _ := by
  simp [unitsMap, castHom_self]

/-- `unitsMap_val` shows that coercing from `(ZMod m)ˣ` to `ZMod n` gives the same result
when going via `(ZMod n)ˣ` and `ZMod m`. -/
/-
**ZMod.unitsMap_val** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：unitsMap_val (h : n ∣ m) (a : (ZMod m)ˣ) : ↑(unitsMap h a) = ((a : ZMod m)
.cast : ZMod n)
参数：h : n ∣ m；a : (ZMod m)ˣ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`unitsMap_val` shows that coercing from `(ZMod m)ˣ` to `ZMod n` gives the same r
esult
when going via `(ZMod n)ˣ` and `ZMod m`.
-/
lemma unitsMap_val (h : n ∣ m) (a : (ZMod m)ˣ) :
    ↑(unitsMap h a) = ((a : ZMod m).cast : ZMod n) := rfl
/-
**ZMod.isUnit_cast_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：isUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) : IsUnit (cast (a : Z
Mod m) : ZMod n)
参数：hm : n ∣ m；a : Units (ZMod m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
-/
lemma isUnit_cast_of_dvd (hm : n ∣ m) (a : Units (ZMod m)) : IsUnit (cast (a : ZMod m) : ZMod n) :=
  Units.isUnit (unitsMap hm a)
/-
**ZMod.unitsMap_surjective** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：unitsMap_surjective [hm : NeZero m] (h : n ∣ m) : Function.Surjective (uni
tsMap h)
参数：h : n ∣ m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.coprime_of_dvd`：coprime_of_dvd {m n : Nat} (H : forall k, Prime k ->
 k ∣ m -> ¬k ∣ n) : Coprime m n
· 使用定理 `Nat.dvd_sub`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m - n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_mul`：∀ {p m n : ℕ}, Nat.Prime p → (p ∣ m * n ↔ p ∣ m ∨ p ∣
 n)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Prime.dvd_finsetProd_iff`：Prime.dvd_finsetProd_iff {S : Finset M₀} {p : 
M} (pp : Prime p) (g : M₀ -> M) : p ∣ S.prod g ↔ exists a in S, p ∣ g a
· 使用定理 `Nat.Prime.prime`：∀ {p : ℕ}, Nat.Prime p → Prime p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.prime_dvd_prime_iff_eq`：prime_dvd_prime_iff_eq {p q : Nat} (pp : p.P
rime) (qp : q.Prime) : p ∣ q ↔ p = q
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.mem_primeFactors`：∀ {n p : ℕ}, p ∈ n.primeFactors ↔ Nat.Prime p ∧ p 
∣ n ∧ n ≠ 0
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.not_coprime_iff_dvd`：∀ {m n : ℕ}, ¬m.Coprime n ↔ ∃ p, Nat.Prim
e p ∧ p ∣ m ∧ p ∣ n
· 使用定理 `NeZero.out`：∀ {R : Type u_1} {inst : Zero R} {n : R} [self : NeZero n], 
n ≠ 0
· 使用定理 `Dvd.dvd.mul_right`：∀ {α : Type u_1} [inst : Semigroup α] {a b : α}, a ∣ 
b → ∀ (c : α), a ∣ b * c
· 使用定理 `Finset.dvd_prod_of_mem`：dvd_prod_of_mem (f : ι -> M) {a : ι} {s : Finset
 ι} (ha : a in s) : f a ∣ ∏ i in s, f i
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `eq_zero_of_zero_dvd`：eq_zero_of_zero_dvd (h : 0 ∣ a) : a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 44 条，此处仅展示前 30 条）
-/
theorem unitsMap_surjective [hm : NeZero m] (h : n ∣ m) :
    Function.Surjective (unitsMap h) := by
  suffices ∀ x : ℕ, x.Coprime n → ∃ k : ℕ, (x + k * n).Coprime m by
    intro x
    have ⟨k, hk⟩ := this x.val.val (val_coe_unit_coprime x)
    refine ⟨unitOfCoprime _ hk, Units.ext ?_⟩
    have : NeZero n := ⟨fun hn ↦ hm.out (eq_zero_of_zero_dvd (hn ▸ h))⟩
    simp [unitsMap_def, -castHom_apply]
  intro x hx
  let ps : Finset ℕ := {p ∈ m.primeFactors | ¬p ∣ x}
  use ps.prod id
  apply Nat.coprime_of_dvd
  intro p pp hp hpn
  by_cases hpx : p ∣ x
  · have h := Nat.dvd_sub hp hpx
    rw [add_comm, Nat.add_sub_cancel] at h
    rcases pp.dvd_mul.mp h with h | h
    · have ⟨q, hq, hq'⟩ := (pp.prime.dvd_finsetProd_iff id).mp h
      rw [Finset.mem_filter, Nat.mem_primeFactors,
        ← (Nat.prime_dvd_prime_iff_eq pp hq.1.1).mp hq'] at hq
      exact hq.2 hpx
    · exact Nat.Prime.not_coprime_iff_dvd.mpr ⟨p, pp, hpx, h⟩ hx
  · have pps : p ∈ ps := Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨pp, hpn, hm.out⟩, hpx⟩
    have h := Nat.dvd_sub hp ((Finset.dvd_prod_of_mem id pps).mul_right n)
    rw [Nat.add_sub_cancel] at h
    contradiction

-- This needs `Nat.primeFactors`, so cannot go into `Mathlib/Data/ZMod/Basic.lean`.
open Nat in
/-
**ZMod.not_isUnit_of_mem_primeFactors** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：not_isUnit_of_mem_primeFactors {n p : Nat} (h : p in n.primeFactors) : ¬ I
sUnit (p : ZMod n)
参数：h : p in n.primeFactors。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.Prime.dvd_iff_not_coprime`：∀ {p n : ℕ}, Nat.Prime p → (p ∣ n ↔ ¬p.Co
prime n)
· 使用引理 `Nat.prime_of_mem_primeFactors`：prime_of_mem_primeFactors (hp : p in n.pr
imeFactors) : p.Prime
· 使用引理 `Nat.dvd_of_mem_primeFactors`：dvd_of_mem_primeFactors (hp : p in n.primeF
actors) : p ∣ n
-/
lemma not_isUnit_of_mem_primeFactors {n p : ℕ} (h : p ∈ n.primeFactors) :
    ¬ IsUnit (p : ZMod n) := by
  rw [isUnit_iff_coprime]
  exact (Prime.dvd_iff_not_coprime <| prime_of_mem_primeFactors h).mp <| dvd_of_mem_primeFactors h

set_option backward.isDefEq.respectTransparency false in
/-- Any element of `ZMod N` has the form `u * d` where `u` is a unit and `d` is a divisor of `N`. -/
/-
**ZMod.eq_unit_mul_divisor** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：eq_unit_mul_divisor {N : Nat} (a : ZMod N) : exists d : Nat, d ∣ N ∧ exist
s (u : ZMod N), IsUnit u ∧ a = u * d
参数：a : ZMod N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `lt_or_gt_of_ne`：lt_or_gt_of_ne (h : a != b) : a < b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.sign_eq_neg_one_of_neg`：∀ {a : ℤ}, a < 0 → a.sign = -1
· 使用定理 `Int.sign_eq_one_of_pos`：∀ {a : ℤ}, 0 < a → a.sign = 1
· 使用定理 `Int.sign_mul_natAbs`：∀ (a : ℤ), a.sign * ↑a.natAbs = a
· 使用定理 `Nat.gcd_ne_zero_right`：∀ {n m : ℕ}, n ≠ 0 → m.gcd n ≠ 0
· 使用定理 `Nat.gcd_dvd_left`：∀ (m n : ℕ), m.gcd n ∣ m
· 使用定理 `Nat.gcd_dvd_right`：∀ (m n : ℕ), m.gcd n ∣ n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ZMod.isUnit_iff_coprime`：isUnit_iff_coprime (m n : Nat) : IsUnit (m : ZM
od n) ↔ m.Coprime n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.isCoprime_iff_coprime`：Nat.isCoprime_iff_coprime {m n : Nat} : IsCop
rime (m : Int) n ↔ Nat.Coprime m n
· 使用定理 `Nat.gcd_eq_gcd_ab`：gcd_eq_gcd_ab : (gcd x y : Int) = x * gcdA x y + y * 
gcdB x y
· 使用定理 `Int.eq_one_of_mul_eq_self_right`：∀ {a b : ℤ}, b ≠ 0 → b * a = b → a = 1
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `ZMod.unitsMap_surjective`：unitsMap_surjective [hm : NeZero m] (h : n ∣ m
) : Function.Surjective (unitsMap h)
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Any element of `ZMod N` has the form `u * d` where `u` is a unit and `d` is a di
visor of `N`.
-/
lemma eq_unit_mul_divisor {N : ℕ} (a : ZMod N) :
    ∃ d : ℕ, d ∣ N ∧ ∃ (u : ZMod N), IsUnit u ∧ a = u * d := by
  rcases eq_or_ne N 0 with rfl | hN
  -- Silly special case : N = 0. Of no mathematical interest, but true, so let's prove it.
  · change ℤ at a
    rcases eq_or_ne a 0 with rfl | ha
    · refine ⟨0, dvd_zero _, 1, isUnit_one, by rw [Nat.cast_zero, mul_zero]⟩
    refine ⟨a.natAbs, dvd_zero _, Int.sign a, ?_, (Int.sign_mul_natAbs a).symm⟩
    rcases lt_or_gt_of_ne ha with h | h
    · simp only [Int.sign_eq_neg_one_of_neg h, IsUnit.neg_iff, isUnit_one]
    · simp only [Int.sign_eq_one_of_pos h, isUnit_one]
  -- now the interesting case
  have : NeZero N := ⟨hN⟩
  -- Define `d` as the GCD of a lift of `a` and `N`.
  let d := a.val.gcd N
  have hd : d ≠ 0 := Nat.gcd_ne_zero_right hN
  obtain ⟨a₀, (ha₀ : _ = d * _)⟩ := a.val.gcd_dvd_left N
  obtain ⟨N₀, (hN₀ : _ = d * _)⟩ := a.val.gcd_dvd_right N
  refine ⟨d, ⟨N₀, hN₀⟩, ?_⟩
  -- Show `a` is a unit mod `N / d`.
  have hu₀ : IsUnit (a₀ : ZMod N₀) := by
    refine (isUnit_iff_coprime _ _).mpr (Nat.isCoprime_iff_coprime.mp ?_)
    obtain ⟨p, q, hpq⟩ : ∃ (p q : ℤ), d = a.val * p + N * q := ⟨_, _, Nat.gcd_eq_gcd_ab _ _⟩
    rw [ha₀, hN₀, Nat.cast_mul, Nat.cast_mul, mul_assoc, mul_assoc, ← mul_add, eq_comm,
      mul_comm _ p, mul_comm _ q] at hpq
    exact ⟨p, q, Int.eq_one_of_mul_eq_self_right (Nat.cast_ne_zero.mpr hd) hpq⟩
  -- Lift it arbitrarily to a unit mod `N`.
  obtain ⟨u, hu⟩ := (unitsMap_surjective (⟨d, mul_comm d N₀ ▸ hN₀⟩ : N₀ ∣ N)) hu₀.unit
  rw [unitsMap_def, ← Units.val_inj, Units.coe_map, IsUnit.unit_spec, MonoidHom.coe_coe] at hu
  refine ⟨u.val, u.isUnit, ?_⟩
  rw [← natCast_zmod_val a, ← natCast_zmod_val u.1, ha₀, ← Nat.cast_mul,
    natCast_eq_natCast_iff, mul_comm _ d, Nat.ModEq]
  simp only [hN₀, Nat.mul_mod_mul_left, Nat.mul_right_inj hd]
  rw [← Nat.ModEq, ← natCast_eq_natCast_iff, ← hu, natCast_val, castHom_apply]
/-
**ZMod.coe_int_mul_inv_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_int_mul_inv_eq_one {n : Nat} {x : Int} (h : IsCoprime x n) : (x : ZMod
 n) * (x : ZMod n)⁻¹ = 1
参数：h : IsCoprime x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Int.isUnit_eq_one_or`：isUnit_eq_one_or (hu : IsUnit u) : u = 1 ∨ u = -1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `ZMod.inv_one`：∀ (n : ℕ), 1⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `ZMod.inv_neg_one`：inv_neg_one (n : Nat) : (-1 : ZMod n)⁻¹ = -1
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `ZMod.coe_mul_inv_eq_one`：coe_mul_inv_eq_one {n : Nat} (x : Nat) (h : Nat
.Coprime x n) : ((x : ZMod n) * (x : ZMod n)⁻¹) = 1
· 使用定理 `ZMod.val_intCast`：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMo
d n).val = a % n
· 使用定理 `Int.gcd_emod`：gcd_emod (m n : Int) : (m % n).gcd n = m.gcd n
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
-/
theorem coe_int_mul_inv_eq_one {n : ℕ} {x : ℤ} (h : IsCoprime x n) :
    (x : ZMod n) * (x : ZMod n)⁻¹ = 1 := by
  by_cases hn : n = 0
  · simp only [hn, Nat.cast_zero, isCoprime_zero_right] at h
    rcases Int.isUnit_eq_one_or h with h | h <;> simp [h]
  have : NeZero n := ⟨hn⟩
  rw [← natCast_zmod_val x]
  apply coe_mul_inv_eq_one
  rwa [Int.isCoprime_iff_gcd_eq_one, ← Int.gcd_emod, ← val_intCast] at h
/-
**ZMod.coe_int_inv_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_int_inv_mul_eq_one {n : Nat} {x : Int} (h : IsCoprime x n) : (x : ZMod
 n)⁻¹ * (x : ZMod n) = 1
参数：h : IsCoprime x n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ZMod.coe_int_mul_inv_eq_one`：coe_int_mul_inv_eq_one {n : Nat} {x : Int} 
(h : IsCoprime x n) : (x : ZMod n) * (x : ZMod n)⁻¹ = 1
-/
theorem coe_int_inv_mul_eq_one {n : ℕ} {x : ℤ} (h : IsCoprime x n) :
    (x : ZMod n)⁻¹ * (x : ZMod n) = 1 := by
  rw [mul_comm, coe_int_mul_inv_eq_one h]
/-
**ZMod.coe_int_mul_val_inv** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：coe_int_mul_val_inv {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n) : (
m * (m⁻¹ : ZMod n).val : ZMod n) = 1
参数：h : IsCoprime m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZMod.natCast_zmod_val`：natCast_zmod_val {n : Nat} [NeZero n] (a : ZMod n
) : (a.val : ZMod n) = a
· 使用定理 `ZMod.coe_int_mul_inv_eq_one`：coe_int_mul_inv_eq_one {n : Nat} {x : Int} 
(h : IsCoprime x n) : (x : ZMod n) * (x : ZMod n)⁻¹ = 1
-/
lemma coe_int_mul_val_inv {n : ℕ} [NeZero n] {m : ℤ} (h : IsCoprime m n) :
    (m * (m⁻¹ : ZMod n).val : ZMod n) = 1 := by
  rw [natCast_zmod_val, coe_int_mul_inv_eq_one h]
/-
**ZMod.coe_int_val_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `ZMod`。
形式化陈述：coe_int_val_inv_mul {n : Nat} [NeZero n] {m : Int} (h : IsCoprime m n) : (
(m⁻¹ : ZMod n).val : ZMod n) * m = 1
参数：h : IsCoprime m n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `ZMod.coe_int_mul_val_inv`：coe_int_mul_val_inv {n : Nat} [NeZero n] {m : 
Int} (h : IsCoprime m n) : (m * (m⁻¹ : ZMod n).val : ZMod n) = 1
-/
lemma coe_int_val_inv_mul {n : ℕ} [NeZero n] {m : ℤ} (h : IsCoprime m n) :
    ((m⁻¹ : ZMod n).val : ZMod n) * m = 1 := by
  rw [mul_comm, coe_int_mul_val_inv h]

/-- The unit of `ZMod m` associated with an integer prime to `n`. -/
/-
**ZMod.unitOfIsCoprime** 是 Mathlib 中的一个定义，位于命名空间 `ZMod`。
形式化陈述：unitOfIsCoprime {m : Nat} (n : Int) (h : IsCoprime n (m : Int)) : (ZMod m)
ˣ where val
参数：n : Int；h : IsCoprime n (m : Int)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.coe_int_mul_inv_eq_one`：coe_int_mul_inv_eq_one {n : Nat} {x : Int} 
(h : IsCoprime x n) : (x : ZMod n) * (x : ZMod n)⁻¹ = 1
· 使用定理 `ZMod.coe_int_inv_mul_eq_one`：coe_int_inv_mul_eq_one {n : Nat} {x : Int} 
(h : IsCoprime x n) : (x : ZMod n)⁻¹ * (x : ZMod n) = 1

--- 原说明 ---
The unit of `ZMod m` associated with an integer prime to `n`.
-/
def unitOfIsCoprime {m : ℕ} (n : ℤ)
    (h : IsCoprime n (m : ℤ)) : (ZMod m)ˣ where
  val := n
  inv := n⁻¹
  val_inv := coe_int_mul_inv_eq_one h
  inv_val := coe_int_inv_mul_eq_one h

@[simp]
/-
**ZMod.coe_unitOfIsCoprime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_unitOfIsCoprime {m : Nat} (n : Int) (h : IsCoprime n ↑m) : (unitOfIsCo
prime n h : ZMod m) = n
参数：n : Int；h : IsCoprime n ↑m。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_unitOfIsCoprime {m : ℕ} (n : ℤ) (h : IsCoprime n ↑m) :
    (unitOfIsCoprime n h : ZMod m) = n := rfl
/-
**ZMod.isUnit_inv** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：isUnit_inv {m : Nat} {n : Int} (h : IsUnit (n : ZMod m)) : IsUnit (n : ZMo
d m)⁻¹
参数：h : IsUnit (n : ZMod m)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `isUnit_iff_exists`：isUnit_iff_exists [Monoid M] {x : M} : IsUnit x ↔ exi
sts b, x * b = 1 ∧ b * x = 1
· 使用定理 `ZMod.inv_mul_of_unit`：inv_mul_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a⁻¹ * a = 1
· 使用定理 `ZMod.mul_inv_of_unit`：mul_inv_of_unit {n : Nat} (a : ZMod n) (h : IsUnit
 a) : a * a⁻¹ = 1
-/
theorem isUnit_inv {m : ℕ} {n : ℤ} (h : IsUnit (n : ZMod m)) :
    IsUnit (n : ZMod m)⁻¹ := by
  rw [isUnit_iff_exists]
  exact ⟨n, inv_mul_of_unit _ h, mul_inv_of_unit _ h⟩
/-
**ZMod.coe_int_isUnit_iff_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：coe_int_isUnit_iff_isCoprime (n : Int) (m : Nat) : IsUnit (n : ZMod m) ↔ I
sCoprime (m : Int) n
参数：n : Int；m : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `isCoprime_zero_left`：isCoprime_zero_left : IsCoprime 0 x ↔ IsUnit x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n
· 使用定理 `isCoprime_comm`：isCoprime_comm : IsCoprime x y ↔ IsCoprime y x
· 使用定理 `Int.isCoprime_iff_gcd_eq_one`：Int.isCoprime_iff_gcd_eq_one {m n : Int} :
 IsCoprime m n ↔ Int.gcd m n = 1
· 使用定理 `Int.gcd_emod`：gcd_emod (m n : Int) : (m % n).gcd n = m.gcd n
· 使用定理 `ZMod.val_intCast`：val_intCast {n : Nat} (a : Int) [NeZero n] : ↑(a : ZMo
d n).val = a % n
· 使用定理 `Int.gcd_natCast_natCast`：∀ (a b : ℕ), (↑a).gcd ↑b = a.gcd b
· 使用定理 `Nat.coprime_iff_gcd_eq_one`：∀ {m n : ℕ}, m.Coprime n ↔ m.gcd n = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_int_isUnit_iff_isCoprime (n : ℤ) (m : ℕ) :
    IsUnit (n : ZMod m) ↔ IsCoprime (m : ℤ) n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨unitOfIsCoprime n (isCoprime_comm.mp h), by simp⟩⟩
  obtain rfl | hm := eq_or_ne m 0
  · rw [Nat.cast_zero, isCoprime_zero_left]
    exact_mod_cast h
  · have : NeZero m := ⟨hm⟩
    obtain ⟨u, hu⟩ := h
    have h_coprime := val_coe_unit_coprime u
    rw [hu, Nat.coprime_iff_gcd_eq_one, ← Int.gcd_natCast_natCast,
      val_intCast, Int.gcd_emod] at h_coprime
    rwa [isCoprime_comm, Int.isCoprime_iff_gcd_eq_one]

/-- For each `n ≥ 0`, the unit group of `ZMod n` is finite. -/
/-
**ZMod.instFiniteZModUnits** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：∀ (n : ℕ), Finite (ZMod n)ˣ
参数：n : ℕ；ZMod n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
For each `n ≥ 0`, the unit group of `ZMod n` is finite.
-/
instance instFiniteZModUnits : (n : ℕ) → Finite (ZMod n)ˣ
  | 0 => Finite.of_fintype ℤˣ
  | _ + 1 => inferInstance

end ZMod

