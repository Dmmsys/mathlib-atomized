/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.LocalRing.Defs
public import Mathlib.RingTheory.Ideal.Nonunits

/-!

# Local rings

We prove basic properties of local rings.

-/

public section

variable {R S : Type*}

namespace IsLocalRing

section Semiring

variable [Semiring R]

/-
**IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLoc
alRing`。
形式化陈述：of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R] (h : forall a b : R, IsUn
it (a + b) -> IsUnit a ∨ IsUnit b) : IsLocalRing R
参数：h : forall a b : R, IsUnit (a + b) -> IsUnit a ∨ IsUnit b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem of_isUnit_or_isUnit_of_isUnit_add [Nontrivial R]
    (h : ∀ a b : R, IsUnit (a + b) → IsUnit a ∨ IsUnit b) : IsLocalRing R :=
  ⟨fun {a b} hab => h a b <| hab.symm ▸ isUnit_one⟩

/-- A semiring is local if it is nontrivial and the set of nonunits is closed under the addition. -/
/-
**IsLocalRing.of_nonunits_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_nonunits_add [Nontrivial R] (h : forall a b : R, a in nonunits R -> b i
n nonunits R -> a + b in nonunits R) : IsLocalRing R where isUnit_or_isUnit_of_a
dd_one {a b} hab
参数：h : forall a b : R, a in nonunits R -> b in nonunits R -> a + b in nonunits R
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `or_iff_not_and_not`：or_iff_not_and_not : a ∨ b ↔ ¬(¬a ∧ ¬b)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A semiring is local if it is nontrivial and the set of nonunits is closed under 
the addition.
-/
theorem of_nonunits_add [Nontrivial R]
    (h : ∀ a b : R, a ∈ nonunits R → b ∈ nonunits R → a + b ∈ nonunits R) : IsLocalRing R where
  isUnit_or_isUnit_of_add_one {a b} hab :=
    or_iff_not_and_not.2 fun H => h a b H.1 H.2 <| hab.symm ▸ isUnit_one

variable [IsLocalRing R]
/-
**IsLocalRing.isUnit_or_isUnit_of_isUnit_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalR
ing`。
形式化陈述：isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨
 IsUnit b
参数：h : IsUnit (a + b)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Units.isUnit_units_mul`：Units.isUnit_units_mul {M : Type*} [Monoid M] (u
 : Mˣ) (a : M) : IsUnit (↑u * a) ↔ IsUnit a
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_add_one`：∀ {R : Type u_1} {inst : Semiri
ng R} [self : IsLocalRing R] {a b : R}, a + b = 1 → IsUnit a ∨ IsUnit b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Units.inv_mul_eq_one`：inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a
-/
theorem isUnit_or_isUnit_of_isUnit_add {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b := by
  rcases h with ⟨u, hu⟩
  rw [← Units.inv_mul_eq_one, mul_add] at hu
  apply Or.imp _ _ (isUnit_or_isUnit_of_add_one hu) <;> exact (u⁻¹.isUnit_units_mul _).mp
/-
**IsLocalRing.nonunits_add** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：nonunits_add {a b : R} (ha : a in nonunits R) (hb : b in nonunits R) : a +
 b in nonunits R
参数：ha : a in nonunits R；hb : b in nonunits R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_intro`：∀ {a b : Prop}, ¬a → ¬b → ¬(a ∨ b)
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`：isUnit_or_isUnit_of_isUnit_a
dd {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b
-/
theorem nonunits_add {a b : R} (ha : a ∈ nonunits R) (hb : b ∈ nonunits R) : a + b ∈ nonunits R :=
  fun H ↦ not_or_intro ha hb (isUnit_or_isUnit_of_isUnit_add H)

variable (R) in
/-- The nonunits of a local semiring form an additive submonoid. -/
/-
**IsLocalRing.nonunitsAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalRing`。
形式化陈述：(R : Type u_1) → [inst : Semiring R] → [IsLocalRing R] → AddSubmonoid R
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.nonunits_add`：nonunits_add {a b : R} (ha : a in nonunits R) 
(hb : b in nonunits R) : a + b in nonunits R

--- 原说明 ---
The nonunits of a local semiring form an additive submonoid.
-/
@[expose] def nonunitsAddSubmonoid : AddSubmonoid R where
  carrier := nonunits R
  zero_mem' := by simp
  add_mem' := nonunits_add
/-
**IsLocalRing.exists_of_isUnit_sum** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：exists_of_isUnit_sum {ι : Type*} {s : Finset ι} {f : ι -> R} (h : IsUnit (
∑ i in s, f i)) : exists i in s, IsUnit (f i)
参数：h : IsUnit (∑ i in s, f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `AddSubmonoid.sum_mem`：∀ {M : Type u_4} [inst : AddCommMonoid M] (S : Add
Submonoid M) {ι : Type u_5} {t : Finset ι} {f : ι → M},   (∀ c ∈ t, f c ∈ S) → ∑
 c ∈ t, f …
-/
theorem exists_of_isUnit_sum {ι : Type*} {s : Finset ι} {f : ι → R}
    (h : IsUnit (∑ i ∈ s, f i)) : ∃ i ∈ s, IsUnit (f i) := by
  contrapose! h; exact (nonunitsAddSubmonoid R).sum_mem h

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- A semiring is local if it has a unique maximal ideal. -/
/-
**IsLocalRing.of_unique_max_ideal** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_unique_max_ideal (h : exists! I : Ideal R, I.IsMaximal) : IsLocalRing R
参数：h : exists! I : Ideal R, I.IsMaximal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_nonunits_add`：of_nonunits_add [Nontrivial R] (h : forall 
a b : R, a in nonunits R -> b in nonunits R -> a + b in nonunits R) : IsLocalRin
g R where isUnit_…
· 使用定理 `nontrivial_of_ne`：nontrivial_of_ne (x y : α) (h : x != y) : Nontrivial α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `exists_max_ideal_of_mem_nonunits`：exists_max_ideal_of_mem_nonunits [Comm
Semiring α] (h : a in nonunits α) : exists I : Ideal α, I.IsMaximal ∧ a in I
· 使用定理 `Ideal.eq_top_of_isUnit_mem`：eq_top_of_isUnit_mem {x} (hx : x in I) (h : 
IsUnit x) : I = ⊤
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I

--- 原说明 ---
A semiring is local if it has a unique maximal ideal.
-/
theorem of_unique_max_ideal (h : ∃! I : Ideal R, I.IsMaximal) : IsLocalRing R :=
  @of_nonunits_add _ _
    (nontrivial_of_ne (0 : R) 1 <|
      let ⟨I, Imax, _⟩ := h
      fun H : 0 = 1 => Imax.1.1 <| I.eq_top_iff_one.2 <| H ▸ I.zero_mem)
    fun x y hx hy H =>
    let ⟨I, Imax, Iuniq⟩ := h
    let ⟨Ix, Ixmax, Hx⟩ := exists_max_ideal_of_mem_nonunits hx
    let ⟨Iy, Iymax, Hy⟩ := exists_max_ideal_of_mem_nonunits hy
    have xmemI : x ∈ I := Iuniq Ix Ixmax ▸ Hx
    have ymemI : y ∈ I := Iuniq Iy Iymax ▸ Hy
    Imax.1.1 <| I.eq_top_of_isUnit_mem (I.add_mem xmemI ymemI) H
/-
**IsLocalRing.of_unique_nonzero_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_unique_nonzero_prime (h : exists! P : Ideal R, P != ⊥ ∧ Ideal.IsPrime P
) : IsLocalRing R
参数：h : exists! P : Ideal R, P != ⊥ ∧ Ideal.IsPrime P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_unique_max_ideal`：of_unique_max_ideal (h : exists! I : Id
eal R, I.IsMaximal) : IsLocalRing R
· 使用定理 `Ideal.maximal_of_no_maximal`：maximal_of_no_maximal {P : Ideal α} (hmax :
 forall m : Ideal α, P < m -> ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_bot_of_gt`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
-/
theorem of_unique_nonzero_prime (h : ∃! P : Ideal R, P ≠ ⊥ ∧ Ideal.IsPrime P) : IsLocalRing R :=
  of_unique_max_ideal
    (by
      rcases h with ⟨P, ⟨hPnonzero, hPnot_top, _⟩, hPunique⟩
      refine ⟨P, ⟨⟨hPnot_top, ?_⟩⟩, fun M hM => hPunique _ ⟨?_, Ideal.IsMaximal.isPrime hM⟩⟩
      · refine Ideal.maximal_of_no_maximal fun M hPM hM => ne_of_lt hPM ?_
        exact (hPunique _ ⟨ne_bot_of_gt hPM, Ideal.IsMaximal.isPrime hM⟩).symm
      · rintro rfl
        exact hPnot_top (hM.1.2 P (bot_lt_iff_ne_bot.2 hPnonzero)))

end CommSemiring

section Ring

variable [Ring R]

/-
**IsLocalRing.of_isUnit_or_isUnit_one_sub_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLoca
lRing`。
形式化陈述：of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : forall a : R, IsUnit 
a ∨ IsUnit (1 - a)) : IsLocalRing R
参数：h : forall a : R, IsUnit a ∨ IsUnit (1 - a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem of_isUnit_or_isUnit_one_sub_self [Nontrivial R] (h : ∀ a : R, IsUnit a ∨ IsUnit (1 - a)) :
    IsLocalRing R :=
  ⟨fun {a b} hab => add_sub_cancel_left a b ▸ hab.symm ▸ h a⟩

end Ring

section CommRing

variable [CommRing R] [IsLocalRing R]

/-
**IsLocalRing.isUnit_or_isUnit_one_sub_self** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRi
ng`。
形式化陈述：isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a)
参数：a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.isUnit_or_isUnit_of_isUnit_add`：isUnit_or_isUnit_of_isUnit_a
dd {a b : R} (h : IsUnit (a + b)) : IsUnit a ∨ IsUnit b
· 使用定理 `isUnit_one`：isUnit_one [Monoid M] : IsUnit (1 : M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
-/
theorem isUnit_or_isUnit_one_sub_self (a : R) : IsUnit a ∨ IsUnit (1 - a) :=
  isUnit_or_isUnit_of_isUnit_add <| (add_sub_cancel a 1).symm ▸ isUnit_one
/-
**IsLocalRing.isUnit_of_mem_nonunits_one_sub_self** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocalRing`。
形式化陈述：isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a in nonunits R) : Is
Unit a
参数：a : R；h : 1 - a in nonunits R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `IsLocalRing.isUnit_or_isUnit_one_sub_self`：isUnit_or_isUnit_one_sub_self
 (a : R) : IsUnit a ∨ IsUnit (1 - a)
-/
theorem isUnit_of_mem_nonunits_one_sub_self (a : R) (h : 1 - a ∈ nonunits R) : IsUnit a :=
  or_iff_not_imp_right.1 (isUnit_or_isUnit_one_sub_self a) h
/-
**IsLocalRing.isUnit_one_sub_self_of_mem_nonunits** 是 Mathlib 中的一个定理，位于命名空间 `IsL
ocalRing`。
形式化陈述：isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a in nonunits R) : IsUnit
 (1 - a)
参数：a : R；h : a in nonunits R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `IsLocalRing.isUnit_or_isUnit_one_sub_self`：isUnit_or_isUnit_one_sub_self
 (a : R) : IsUnit a ∨ IsUnit (1 - a)
-/
theorem isUnit_one_sub_self_of_mem_nonunits (a : R) (h : a ∈ nonunits R) : IsUnit (1 - a) :=
  or_iff_not_imp_left.1 (isUnit_or_isUnit_one_sub_self a) h
/-
**IsLocalRing.of_surjective'** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：of_surjective' [Ring S] [Nontrivial S] (f : R ->+* S) (hf : Function.Surje
ctive f) : IsLocalRing S
参数：f : R ->+* S；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`：of_isUnit_or_isUnit_one_su
b_self [Nontrivial R] (h : forall a : R, IsUnit a ∨ IsUnit (1 - a)) : IsLocalRin
g R
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `IsLocalRing.isUnit_or_isUnit_one_sub_self`：isUnit_or_isUnit_one_sub_self
 (a : R) : IsUnit a ∨ IsUnit (1 - a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_sub`：∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocRing α]
 [inst_1 : NonAssocRing β] (f : α →+* β) (x y : α),   f (x - y) = f x - f y
-/
theorem of_surjective' [Ring S] [Nontrivial S] (f : R →+* S) (hf : Function.Surjective f) :
    IsLocalRing S :=
  of_isUnit_or_isUnit_one_sub_self (by
    intro b
    obtain ⟨a, rfl⟩ := hf b
    apply (isUnit_or_isUnit_one_sub_self a).imp <| RingHom.isUnit_map _
    rw [← f.map_one, ← f.map_sub]
    apply f.isUnit_map)

end CommRing

end IsLocalRing

namespace Field

variable (K : Type*) [Field K]

-- see Note [lower instance priority]
/-
**Field.** 是 Mathlib 中的一个实例，位于命名空间 `Field`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : IsLocalRing K := by
  classical exact IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a =>
    if h : a = 0 then Or.inr (by rw [h, sub_zero]; exact isUnit_one)
    else Or.inl <| IsUnit.mk0 a h

end Field

