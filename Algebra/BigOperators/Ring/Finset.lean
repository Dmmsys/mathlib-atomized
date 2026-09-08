/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Pi
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.Cast.Lemmas

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/

public section

assert_not_exists Field

open Fintype

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

namespace Finset

/-
**Finset.prod_neg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι -> M) : ∏ x in s, -f x = 
(-1) ^ #s * ∏ x in s, f x
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.prod_map_neg`：∀ {M : Type u_2} [inst : CommMonoid M] [inst_1 : 
HasDistribNeg M] (s : Multiset M),   (Multiset.map Neg.neg s).prod = (-1) ^ s.ca
rd * s.prod
-/
lemma prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι → M) :
    ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x := by
  simpa using (s.1.map f).prod_map_neg

section AddCommMonoidWithOne
variable [AddCommMonoidWithOne R]

/-
**Finset.natCast_card_filter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：natCast_card_filter (p) [DecidablePred p] (s : Finset ι) : (#{x in s | p x
} : R) = ∑ a in s, if p a then (1 : R) else 0
参数：p；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
-/
lemma natCast_card_filter (p) [DecidablePred p] (s : Finset ι) :
    (#{x ∈ s | p x} : R) = ∑ a ∈ s, if p a then (1 : R) else 0 := by
  rw [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_one]
/-
**Finset.sum_boole** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidWithOne R] (p : ι → P
rop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, if p x then 1 else 0
) = ↑{x ∈ s | p x}.card
参数：p : ι → Prop；s : Finset ι；∑ x ∈ s, if p x then 1 else 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.natCast_card_filter`：natCast_card_filter (p) [DecidablePred p] (s
 : Finset ι) : (#{x in s | p x} : R) = ∑ a in s, if p a then (1 : R) else 0
-/
@[simp] lemma sum_boole (p) [DecidablePred p] (s : Finset ι) :
    (∑ x ∈ s, if p x then 1 else 0 : R) = #{x ∈ s | p x} :=
  (natCast_card_filter _ _).symm
/-
**Finset.card_eq_sum_ite** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_eq_sum_ite {s t : Finset ι} [DecidablePred (· in s)] (hst : s subsete
q t) : s.card = ∑ i in t, if i in s then 1 else 0
参数：· in s；hst : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_boole`：∀ {ι : Type u_1} {R : Type u_4} [inst : AddCommMonoidW
ithOne R] (p : ι → Prop) [inst_1 : DecidablePred p]   (s : Finset ι), (∑ x ∈ s, 
if p x…
· 使用定理 `Finset.filter_mem_eq_of_subset`：∀ {α : Type u_1} {s t : Finset α} [inst 
: DecidablePred fun x => x ∈ s], s ⊆ t → {x ∈ t | x ∈ s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_eq_sum_ite {s t : Finset ι} [DecidablePred (· ∈ s)] (hst : s ⊆ t) :
    s.card = ∑ i ∈ t, if i ∈ s then 1 else 0 := by simp [hst]

end AddCommMonoidWithOne

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

/-
**Finset.sum_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s, f i) * a = ∑ i in
 s, f i * a
参数：s : Finset ι；f : ι -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma sum_mul (s : Finset ι) (f : ι → R) (a : R) :
    (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := map_sum (AddMonoidHom.mulRight a) _ s
/-
**Finset.mul_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in s, f i = ∑ i in s
, a * f i
参数：s : Finset ι；f : ι -> R；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma mul_sum (s : Finset ι) (f : ι → R) (a : R) :
    a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i := map_sum (AddMonoidHom.mulLeft a) _ s
/-
**Finset.sum_mul_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι -> R) (g : κ -> R) : (∑ i
 in s, f i) * ∑ j in t, g j = ∑ i in s, ∑ j in t, f i * g j
参数：s : Finset ι；t : Finset κ；f : ι -> R；g : κ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_mul_sum (s : Finset ι) (t : Finset κ) (f : ι → R) (g : κ → R) :
    (∑ i ∈ s, f i) * ∑ j ∈ t, g j = ∑ i ∈ s, ∑ j ∈ t, f i * g j := by
  simp_rw [sum_mul, ← mul_sum]
/-
**Finset._root_.Fintype.sum_mul_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Fintype.sum_mul_sum [Fintype ι] [Fintype κ] (f : ι → R) (g : κ → R) :
    (∑ i, f i) * ∑ j, g j = ∑ i, ∑ j, f i * g j :=
  Finset.sum_mul_sum _ _ _ _
/-
**Finset._root_.Commute.sum_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Commute.sum_right (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute b (f i)) : Commute b (∑ i ∈ s, f i) :=
  (Commute.multiset_sum_right _ _) fun b hb => by
    obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hb
    exact h _ hi
/-
**Finset._root_.Commute.sum_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Commute.sum_left (s : Finset ι) (f : ι → R) (b : R)
    (h : ∀ i ∈ s, Commute (f i) b) : Commute (∑ i ∈ s, f i) b :=
  ((Commute.sum_right _ _ _) fun _i hi => (h _ hi).symm).symm
/-
**Finset.sum_range_succ_mul_sum_range_succ** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_range_succ_mul_sum_range_succ (m n : Nat) (f g : Nat -> R) : (∑ i in r
ange (m + 1), f i) * ∑ i in range (n + 1), g i = (∑ i in range m, f i) * ∑ i in 
range n, g i + f m * ∑ i in range n, g i + (∑ i in range m, f i) * g n + f m * g
 n
参数：m n : Nat；f g : Nat -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_range_succ_mul_sum_range_succ (m n : ℕ) (f g : ℕ → R) :
    (∑ i ∈ range (m + 1), f i) * ∑ i ∈ range (n + 1), g i =
      (∑ i ∈ range m, f i) * ∑ i ∈ range n, g i +
        f m * ∑ i ∈ range n, g i + (∑ i ∈ range m, f i) * g n + f m * g n := by
  simp only [add_mul, mul_add, add_assoc, sum_range_succ]

end NonUnitalNonAssocSemiring

section NonUnitalSemiring
variable [NonUnitalSemiring R] {f : ι → R} {a : R}

/-
**Finset.dvd_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
参数：h : forall i in s, a ∣ f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Multiset.dvd_sum`：dvd_sum : (forall x in s, a ∣ x) -> a ∣ s.sum
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
lemma dvd_sum (h : ∀ i ∈ s, a ∣ f i) : a ∣ ∑ i ∈ s, f i :=
  Multiset.dvd_sum fun y hy => by rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩; exact h x hx

end NonUnitalSemiring

section NonAssocSemiring
variable [NonAssocSemiring R] [DecidableEq ι]

/-
**Finset.sum_mul_boole** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_mul_boole (s : Finset ι) (f : ι -> R) (i : ι) : ∑ j in s, f j * ite (i
 = j) 1 0 = ite (i in s) (f i) 0
参数：s : Finset ι；f : ι -> R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_mul_boole (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, f j * ite (i = j) 1 0 = ite (i ∈ s) (f i) 0 := by simp
/-
**Finset.sum_boole_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_boole_mul (s : Finset ι) (f : ι -> R) (i : ι) : ∑ j in s, ite (i = j) 
1 0 * f j = ite (i in s) (f i) 0
参数：s : Finset ι；f : ι -> R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_boole_mul (s : Finset ι) (f : ι → R) (i : ι) :
    ∑ j ∈ s, ite (i = j) 1 0 * f j = ite (i ∈ s) (f i) 0 := by simp

end NonAssocSemiring

section CommSemiring
variable [CommSemiring R]

/-- If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product of `f` over `s`
  is the sum of the products of `g` and `h`. -/
/-
**Finset.prod_add_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_add_prod_eq {s : Finset ι} {i : ι} {f g h : ι -> R} (hi : i in s) (h1
 : g i + h i = f i) (h2 : forall j in s, j != i -> g j = f j) (h3 : forall j in 
s, j != i -> h j = f j) : (∏ i in s, g i) + ∏ i in s, h i = ∏ i in s, f i
参数：hi : i in s；h1 : g i + h i = f i；h2 : forall j in s, j != i -> g j = f j；h3 :
 forall j in s, j != i -> h j = f j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_eq_mul_prod_sdiff_singleton_of_mem`：prod_eq_mul_prod_sdiff_s
ingleton_of_mem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i in s) (f : ι -> M)
 : ∏ x in s, f x = f i * ∏ x in s \ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If `f = g = h` everywhere but at `i`, where `f i = g i + h i`, then the product 
of `f` over `s`
  is the sum of the products of `g` and `h`.
-/
theorem prod_add_prod_eq {s : Finset ι} {i : ι} {f g h : ι → R} (hi : i ∈ s)
    (h1 : g i + h i = f i) (h2 : ∀ j ∈ s, j ≠ i → g j = f j) (h3 : ∀ j ∈ s, j ≠ i → h j = f j) :
    (∏ i ∈ s, g i) + ∏ i ∈ s, h i = ∏ i ∈ s, f i := by
  classical
    simp_rw [prod_eq_mul_prod_sdiff_singleton_of_mem hi, ← h1, right_distrib]
    congr 2 <;> apply prod_congr rfl <;> simpa

section DecidableEq
variable [DecidableEq ι]

/-- The product over a sum can be written as a sum over the product of sets, `Finset.Pi`.
  `Finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
/-
**Finset.prod_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sum {κ : ι -> Type*} (s : Finset ι) (t : forall i, Finset (κ i)) (f :
 forall i, κ i -> R) : ∏ a in s, ∑ b in t a, f a b = ∑ p in s.pi t, ∏ x in s.att
ach, f x.1 (p x.1 x.2)
参数：s : Finset ι；t : forall i, Finset (κ i)；f : forall i, κ i -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.Pi.cons_same`：∀ {α : Type u_1} {δ : α → Sort v} [inst : Decidable
Eq α] (s : Finset α) (a : α) (b : δ a) (f : (a : α) → a ∈ s → δ a)   (h : a ∈ in
sert a s)…
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.pi_insert`：pi_insert [forall a, DecidableEq (β a)] {s : Finset α}
 {t : forall a : α, Finset (β a)} {a : α} (ha : a ∉ s) : pi (insert a s) t = (t 
a).biU…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_biUnion`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst
 : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {t : κ
 → Finse…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.Pi.cons_injective`：∀ {α : Type u_1} {δ : α → Sort v} [inst : Deci
dableEq α] {a : α} {b : δ a} {s : Finset α},   a ∉ s → Function.Injective (Finse
t.Pi.cons s a …
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.attach_insert`：attach_insert [DecidableEq α] (s : Finset α) (a : 
α) : attach (insert a s) = insert (⟨a, mem_insert_self a s⟩ : { x // x in insert
 a s }) ((…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
The product over a sum can be written as a sum over the product of sets, `Finset
.Pi`.
  `Finset.prod_univ_sum` is an alternative statement when the product is over `u
niv`.
-/
lemma prod_sum {κ : ι → Type*} (s : Finset ι) (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) :
    ∏ a ∈ s, ∑ b ∈ t a, f a b = ∑ p ∈ s.pi t, ∏ x ∈ s.attach, f x.1 (p x.1 x.2) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    have h₁ : ∀ x ∈ t a, ∀ y ∈ t a, x ≠ y →
      Disjoint (image (Pi.cons s a x) (pi s t)) (image (Pi.cons s a y) (pi s t)) := by
      intro x _ y _ h
      simp only [disjoint_iff_ne, mem_image]
      rintro _ ⟨p₂, _, eq₂⟩ _ ⟨p₃, _, eq₃⟩ eq
      have : Pi.cons s a x p₂ a (mem_insert_self _ _)
              = Pi.cons s a y p₃ a (mem_insert_self _ _) := by rw [eq₂, eq₃, eq]
      rw [Pi.cons_same, Pi.cons_same] at this
      exact h this
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_biUnion h₁]
    refine sum_congr rfl fun b _ => ?_
    have h₂ : ∀ p₁ ∈ pi s t, ∀ p₂ ∈ pi s t, Pi.cons s a b p₁ = Pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ _ p₂ _ eq => Pi.cons_injective ha eq
    rw [sum_image h₂, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [attach_insert, prod_insert, prod_image]
    · simp only [Pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact (Pi.cons_ne (by rintro rfl; exact ha hv)).symm
    · exact fun _ _ _ _ => Subtype.ext ∘ Subtype.mk.inj
    · simpa only [mem_image, mem_attach, Subtype.mk.injEq, true_and,
        Subtype.exists, exists_prop, exists_eq_right] using ha

/-- The product over `univ` of a sum can be written as a sum over the product of sets,
`Fintype.piFinset`. `Finset.prod_sum` is an alternative statement when the product is not
over `univ`. -/
/-
**Finset.prod_univ_sum** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : forall i, Finset (κ i)) (f
 : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in piFinset t, ∏ i, f i (x
 i)
参数：t : forall i, Finset (κ i)；f : forall i, κ i -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `Finset.prod_sum`：prod_sum {κ : ι -> Type*} (s : Finset ι) (t : forall i,
 Finset (κ i)) (f : forall i, κ i -> R) : ∏ a in s, ∑ b in t a, f a b = ∑ p in s
.pi t…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.prod_attach_univ`：prod_attach_univ [Fintype ι] (f : {i // i in @u
niv ι _} -> M) : ∏ i in univ.attach, f i = ∏ i, f ⟨i, mem_univ _⟩
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sum_univ_pi`：∀ {ι : Type u_1} {β : Type u_2} [inst : AddCommMonoi
d β] [inst_1 : DecidableEq ι] [inst_2 : Fintype ι]   {κ : ι → Type u_3} (t : (i 
: ι) → F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The product over `univ` of a sum can be written as a sum over the product of set
s,
`Fintype.piFinset`. `Finset.prod_sum` is an alternative statement when the produ
ct is not
over `univ`.
-/
lemma prod_univ_sum {κ : ι → Type*} [Fintype ι] (t : ∀ i, Finset (κ i)) (f : ∀ i, κ i → R) :
    ∏ i, ∑ j ∈ t i, f i j = ∑ x ∈ piFinset t, ∏ i, f i (x i) := by
  simp only [prod_attach_univ, prod_sum, Finset.sum_univ_pi]
/-
**Finset.sum_prod_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι -> κ -> R) : ∑ f in pi
Finset fun _ : ι => s, ∏ i, g i (f i) = ∏ i, ∑ j in s, g i j
参数：s : Finset κ；g : ι -> κ -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.prod_univ_sum`：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : fo
rall i, Finset (κ i)) (f : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in
 piFinset …
-/
lemma sum_prod_piFinset [Fintype ι] (s : Finset κ) (g : ι → κ → R) :
    ∑ f ∈ piFinset fun _ : ι ↦ s, ∏ i, g i (f i) = ∏ i, ∑ j ∈ s, g i j := by
  rw [← prod_univ_sum]
/-
**Finset.sum_pow'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sum_pow' (s : Finset κ) (f : κ -> R) (n : Nat) : (∑ a in s, f a) ^ n = ∑ p
 in piFinset fun _i : Fin n => s, ∏ i, f (p i)
参数：s : Finset κ；f : κ -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.prod_univ_sum`：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : fo
rall i, Finset (κ i)) (f : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in
 piFinset …
-/
lemma sum_pow' (s : Finset κ) (f : κ → R) (n : ℕ) :
    (∑ a ∈ s, f a) ^ n = ∑ p ∈ piFinset fun _i : Fin n ↦ s, ∏ i, f (p i) := by
  convert! @prod_univ_sum (Fin n) _ _ _ _ _ (fun _i ↦ s) fun _i d ↦ f d; simp

/-- The product of `f a + g a` over all of `s` is the sum over the powerset of `s` of the product of
`f` over a subset `t` times the product of `g` over the complement of `t` -/
/-
**Finset.prod_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i + g i) = ∑ t in s.
powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
参数：f g : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Finset.prod_sum`：prod_sum {κ : ι -> Type*} (s : Finset ι) (t : forall i,
 Finset (κ i)) (f : forall i, κ i -> R) : ∏ a in s, ∑ b in t a, f a b = ∑ p in s
.pi t…
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.prod_ite`：prod_ite {s : Finset ι} {p : ι -> Prop} [DecidablePred 
p] (f g : ι -> M) : ∏ x in s, (if p x then f x else g x) = (∏ x in s with p x, f
 x) *…
· 使用定理 `Finset.filter_subset`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidableP
red p] (s : Finset α), Finset.filter p s ⊆ s
· 使用定理 `Subtype.map_injective`：map_injective {p : α -> Prop} {q : β -> Prop} {f 
: α -> β} (h : forall a, p a -> q (f a)) (hf : Injective f) : Injective (map f h
)
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用引理 `Finset.filter_attach'`：filter_attach' [DecidableEq α] (s : Finset α) (p 
: s -> Prop) [DecidablePred p] : s.attach.filter p = (s.filter fun x => exists h
, p ⟨x, h⟩)…
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
The product of `f a + g a` over all of `s` is the sum over the powerset of `s` o
f the product of
`f` over a subset `t` times the product of `g` over the complement of `t`
-/
theorem prod_add (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i + g i) = ∑ t ∈ s.powerset, (∏ i ∈ t, f i) * ∏ i ∈ s \ t, g i := by
  classical
  calc
    ∏ i ∈ s, (f i + g i) =
        ∏ i ∈ s, ∑ p ∈ ({True, False} : Finset Prop), if p then f i else g i := by simp
    _ = ∑ p ∈ (s.pi fun _ => {True, False} : Finset (∀ a ∈ s, Prop)),
          ∏ a ∈ s.attach, if p a.1 a.2 then f a.1 else g a.1 := prod_sum _ _ _
    _ = ∑ t ∈ s.powerset, (∏ a ∈ t, f a) * ∏ a ∈ s \ t, g a :=
      sum_bij'
        (fun f _ ↦ {a ∈ s | ∃ h : a ∈ s, f a h})
        (fun t _ a _ => a ∈ t)
        (by simp)
        (by simp [Classical.em])
        (by simp_rw [mem_filter, funext_iff, eq_iff_iff, mem_pi, mem_insert]; tauto)
        (by simp_rw [Finset.ext_iff, mem_filter, mem_powerset]; tauto)
        (fun a _ ↦ by
          simp only [prod_ite, filter_attach', prod_map, Function.Embedding.coeFn_mk,
            Subtype.map_coe, id_eq, prod_attach]
          congr 2 with x
          simp only [mem_filter, mem_sdiff, not_and, not_exists, and_congr_right_iff]
          tauto)

end DecidableEq

/-
**Finset.prod_one_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_one_add {f : ι -> R} (s : Finset ι) : ∏ i in s, (1 + f i) = ∑ t in s.
powerset, ∏ i in t, f i
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_one_add {f : ι → R} (s : Finset ι) :
    ∏ i ∈ s, (1 + f i) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  classical simp only [add_comm (1 : R), prod_add, prod_const_one, mul_one]
/-
**Finset.prod_add_one** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_add_one {f : ι -> R} (s : Finset ι) : ∏ i in s, (f i + 1) = ∑ t in s.
powerset, ∏ i in t, f i
参数：s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_add_one {f : ι → R} (s : Finset ι) :
    ∏ i ∈ s, (f i + 1) = ∑ t ∈ s.powerset, ∏ i ∈ t, f i := by
  classical simp only [prod_add, prod_const_one, mul_one]

/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
/-
**Finset.prod_add_ordered** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_add_ordered [LinearOrder ι] (s : Finset ι) (f g : ι -> R) : ∏ i in s,
 (f i + g i) = (∏ i in s, f i) + ∑ i in s, g i * (∏ j in s with j < i, (f j + g 
j)) * ∏ j in s with i < j, f j
参数：s : Finset ι；f g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on_max`：induction_on_max [DecidableEq α] {motive : Fins
et α -> Prop} (s : Finset α) (empty : motive ∅) (insert : forall a s, (forall x 
in s, x < a) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.filter_insert`：filter_insert (a : α) (s : Finset α) : (insert a s
).filter p = if p a then insert a (s.filter p) else s.filter p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.forall_mem_insert`：forall_mem_insert (a : α) (s : Finset α) (p : 
α -> Prop) : (forall x, x in insert a s -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `LT.lt.not_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
`∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j
)`.
-/
theorem prod_add_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i + g i) =
      (∏ i ∈ s, f i) +
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j + g j)) * ∏ j ∈ s with i < j, f j := by
  refine Finset.induction_on_max s (by simp) ?_
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => lt_irrefl a (ha a ha')
  rw [prod_insert ha', prod_insert ha', sum_insert ha', filter_insert, if_neg (lt_irrefl a),
    filter_true_of_mem ha, ihs, add_mul, mul_add, mul_add, add_assoc]
  congr 1
  rw [add_comm]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_one]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irrefl a, fun i hi => (ha i hi).not_gt⟩
  · rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    rw [filter_insert, if_neg (ha i hi).not_gt, filter_insert, if_pos (ha i hi), prod_insert,
      mul_left_comm]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'
/-
**Finset.prod_one_add_ordered** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_one_add_ordered [LinearOrder ι] (s : Finset ι) (f : ι -> R) : ∏ i in 
s, (1 + f i) = 1 + ∑ i in s, f i * ∏ j in s with j < i, (1 + f j)
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_add_ordered`：prod_add_ordered [LinearOrder ι] (s : Finset ι)
 (f g : ι -> R) : ∏ i in s, (f i + g i) = (∏ i in s, f i) + ∑ i in s, g i * (∏ j
 in s with j …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_one_add_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 + f i) = 1 + ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 + f j) := by
  rw [prod_add_ordered]
  simp

/-- Summing `a ^ #t * b ^ (n - #t)` over all finite subsets `t` of a finset `s`
gives `(a + b) ^ #s`. -/
/-
**Finset.sum_pow_mul_eq_add_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) : (∑ t in s.powerset, a ^ 
#t * b ^ (#s - #t)) = (a + b) ^ #s
参数：a b : R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_powerset`：mem_powerset {s t : Finset α} : s in powerset t ↔ s
 subseteq t

--- 原说明 ---
Summing `a ^ #t * b ^ (n - #t)` over all finite subsets `t` of a finset `s`
gives `(a + b) ^ #s`.
-/
theorem sum_pow_mul_eq_add_pow (a b : R) (s : Finset ι) :
    (∑ t ∈ s.powerset, a ^ #t * b ^ (#s - #t)) = (a + b) ^ #s := by
  classical
  rw [← prod_const, prod_add]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [prod_const, prod_const, ← card_sdiff_of_subset (mem_powerset.1 ht)]

/-- Summing `a^#s * b^(n-#s)` over all finite subsets `s` of a fintype of cardinality `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates using the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so we give instead
a proof reducing to the usual binomial theorem to have a result over semirings. -/
/-
**Finset._root_.Fintype.sum_pow_mul_eq_add_pow** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Summing `a^#s * b^(n-#s)` over all finite subsets `s` of a fintype of cardinalit
y `n`
gives `(a + b)^n`. The "good" proof involves expanding along all coordinates usi
ng the fact that
`x^n` is multilinear, but multilinear maps are only available now over rings, so
 we give instead
a proof reducing to the usual binomial theorem to have a result over semirings.
-/
lemma _root_.Fintype.sum_pow_mul_eq_add_pow (ι : Type*) [Fintype ι] (a b : R) :
    ∑ s : Finset ι, a ^ #s * b ^ (Fintype.card ι - #s) = (a + b) ^ Fintype.card ι :=
  Finset.sum_pow_mul_eq_add_pow _ _ _

@[norm_cast]
/-
**Finset.prod_natCast** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i in s, f i : Nat) = ∏ i 
in s, (f i : R)
参数：s : Finset ι；f : ι -> Nat。
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
theorem prod_natCast (s : Finset ι) (f : ι → ℕ) : ↑(∏ i ∈ s, f i : ℕ) = ∏ i ∈ s, (f i : R) :=
  map_prod (Nat.castRingHom R) f s

end CommSemiring

section CommRing
variable [CommRing R]

/-- The product of `f i - g i` over all of `s` is the sum over the powerset of `s` of the product of
`g` over a subset `t` times the product of `f` over the complement of `t` times `(-1) ^ #t`. -/
/-
**Finset.prod_sub** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sub [DecidableEq ι] (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i - 
g i) = ∑ t in s.powerset, (-1) ^ #t * (∏ i in s \ t, f i) * ∏ i in t, g i
参数：f g : ι -> R；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Finset.prod_neg`：prod_neg [CommMonoid M] [HasDistribNeg M] (f : ι -> M) 
: ∏ x in s, -f x = (-1) ^ #s * ∏ x in s, f x
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The product of `f i - g i` over all of `s` is the sum over the powerset of `s` o
f the product of
`g` over a subset `t` times the product of `f` over the complement of `t` times 
`(-1) ^ #t`.
-/
lemma prod_sub [DecidableEq ι] (f g : ι → R) (s : Finset ι) :
    ∏ i ∈ s, (f i - g i) = ∑ t ∈ s.powerset, (-1) ^ #t * (∏ i ∈ s \ t, f i) * ∏ i ∈ t, g i := by
  simp [sub_eq_neg_add, prod_add, prod_neg, mul_right_comm]

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
/-
**Finset.prod_sub_ordered** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι -> R) : ∏ i in s,
 (f i - g i) = (∏ i in s, f i) - ∑ i in s, g i * (∏ j in s with j < i, (f j - g 
j)) * ∏ j in s with i < j, f j
参数：s : Finset ι；f g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_add_ordered`：prod_add_ordered [LinearOrder ι] (s : Finset ι)
 (f g : ι -> R) : ∏ i in s, (f i + g i) = (∏ i in s, f i) + ∑ i in s, g i * (∏ j
 in s with j …

--- 原说明 ---
`∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j
)`.
-/
lemma prod_sub_ordered [LinearOrder ι] (s : Finset ι) (f g : ι → R) :
    ∏ i ∈ s, (f i - g i) =
      (∏ i ∈ s, f i) -
        ∑ i ∈ s, g i * (∏ j ∈ s with j < i, (f j - g j)) * ∏ j ∈ s with i < j, f j := by
  simp only [sub_eq_add_neg]
  convert! prod_add_ordered s f fun i => -g i
  simp

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions. -/
/-
**Finset.prod_one_sub_ordered** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι -> R) : ∏ i in 
s, (1 - f i) = 1 - ∑ i in s, f i * ∏ j in s with j < i, (1 - f j)
参数：s : Finset ι；f : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.prod_sub_ordered`：prod_sub_ordered [LinearOrder ι] (s : Finset ι)
 (f g : ι -> R) : ∏ i in s, (f i - g i) = (∏ i in s, f i) - ∑ i in s, g i * (∏ j
 in s with j …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in 
construction of
a partition of unity from a collection of “bump” functions.
-/
theorem prod_one_sub_ordered [LinearOrder ι] (s : Finset ι) (f : ι → R) :
    ∏ i ∈ s, (1 - f i) = 1 - ∑ i ∈ s, f i * ∏ j ∈ s with j < i, (1 - f j) := by
  rw [prod_sub_ordered]
  simp
/-
**Finset.prod_range_natCast_sub** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_range_natCast_sub (n k : Nat) : ∏ i in range k, (n - i : R) = (∏ i in
 range k, (n - i) : Nat)
参数：n k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_natCast`：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i 
in s, f i : Nat) = ∏ i in s, (f i : R)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用引理 `Finset.prod_eq_zero`：prod_eq_zero (hi : i in s) (h : f i = 0) : ∏ j in s
, f j = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem prod_range_natCast_sub (n k : ℕ) :
    ∏ i ∈ range k, (n - i : R) = (∏ i ∈ range k, (n - i) : ℕ) := by
  rw [prod_natCast]
  rcases le_or_gt k n with hkn | hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp

end CommRing
end Finset

open Finset

namespace Fintype
variable {ι κ R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]

/-
**Fintype.sum_pow** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：sum_pow (f : ι -> R) (n : Nat) : (∑ a, f a) ^ n = ∑ p : Fin n -> ι, ∏ i, f
 (p i)
参数：f : ι -> R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.sum_pow'`：sum_pow' (s : Finset κ) (f : κ -> R) (n : Nat) : (∑ a i
n s, f a) ^ n = ∑ p in piFinset fun _i : Fin n => s, ∏ i, f (p i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sum_pow (f : ι → R) (n : ℕ) : (∑ a, f a) ^ n = ∑ p : Fin n → ι, ∏ i, f (p i) := by
  simp [sum_pow']

variable [DecidableEq ι]

/-- A product of sums can be written as a sum of products. -/
/-
**Fintype.prod_sum** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_sum {κ : ι -> Type*} [forall i, Fintype (κ i)] (f : forall i, κ i -> 
R) : ∏ i, ∑ j, f i j = ∑ x : forall i, κ i, ∏ i, f i (x i)
参数：κ i；f : forall i, κ i -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.prod_univ_sum`：prod_univ_sum {κ : ι -> Type*} [Fintype ι] (t : fo
rall i, Finset (κ i)) (f : forall i, κ i -> R) : ∏ i, ∑ j in t i, f i j = ∑ x in
 piFinset …

--- 原说明 ---
A product of sums can be written as a sum of products.
-/
lemma prod_sum {κ : ι → Type*} [∀ i, Fintype (κ i)] (f : ∀ i, κ i → R) :
    ∏ i, ∑ j, f i j = ∑ x : ∀ i, κ i, ∏ i, f i (x i) := Finset.prod_univ_sum _ _
/-
**Fintype.prod_add** 是 Mathlib 中的一个引理，位于命名空间 `Fintype`。
形式化陈述：prod_add (f g : ι -> R) : ∏ a, (f a + g a) = ∑ t, (∏ a in t, f a) * ∏ a in
 tᶜ, g a
参数：f g : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.powerset_univ`：∀ {α : Type u_1} [inst : Fintype α], Finset.univ.p
owerset = Finset.univ
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
-/
lemma prod_add (f g : ι → R) : ∏ a, (f a + g a) = ∑ t, (∏ a ∈ t, f a) * ∏ a ∈ tᶜ, g a := by
  simpa [compl_eq_univ_sdiff] using Finset.prod_add f g univ

end Fintype

namespace Nat
variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

/-
**Nat.sum_div** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：∀ {ι : Type u_5} {s : Finset ι} {f : ι → ℕ} {n : ℕ}, (∀ i ∈ s, n ∣ f i) → 
(∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n
参数：∀ i ∈ s, n ∣ f i；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.div_zero`：∀ (n : ℕ), n / 0 = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.div_eq_iff_eq_mul_left`：∀ {a b c : ℕ}, 0 < b → b ∣ a → (a / b = c ↔ 
a = c * b)
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Nat.div_mul_cancel`：∀ {n m : ℕ}, n ∣ m → m / n * n = m
-/
protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simp
  rw [Nat.div_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [Nat.div_mul_cancel (hf _ hs)]

@[simp, norm_cast]
/-
**Nat.cast_list_sum** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_list_sum [AddMonoidWithOne R] (s : List Nat) : (↑s.sum : R) = (s.map 
(↑)).sum
参数：s : List Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_list_sum [AddMonoidWithOne R] (s : List ℕ) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddMonoidHom R) _

@[simp, norm_cast]
/-
**Nat.cast_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_list_prod [Semiring R] (s : List Nat) : (↑s.prod : R) = (s.map (↑)).p
rod
参数：s : List Nat。
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
lemma cast_list_prod [Semiring R] (s : List ℕ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
/-
**Nat.cast_multiset_sum** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_multiset_sum [AddCommMonoidWithOne R] (s : Multiset Nat) : (↑s.sum : 
R) = (s.map (↑)).sum
参数：s : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_multiset_sum [AddCommMonoidWithOne R] (s : Multiset ℕ) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddMonoidHom R) _

@[simp, norm_cast]
/-
**Nat.cast_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_multiset_prod [CommSemiring R] (s : Multiset Nat) : (↑s.prod : R) = (
s.map (↑)).prod
参数：s : Multiset Nat。
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
lemma cast_multiset_prod [CommSemiring R] (s : Multiset ℕ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
/-
**Nat.cast_sum** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι -> Nat) : ↑(∑ x in
 s, f x : Nat) = ∑ x in s, (f x : R)
参数：s : Finset ι；f : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι → ℕ) :
    ↑(∑ x ∈ s, f x : ℕ) = ∑ x ∈ s, (f x : R) :=
  map_sum (castAddMonoidHom R) _ _

@[simp, norm_cast]
/-
**Nat.cast_prod** 是 Mathlib 中的一个引理，位于命名空间 `Nat`。
形式化陈述：cast_prod [CommSemiring R] (f : ι -> Nat) (s : Finset ι) : (↑(∏ i in s, f 
i) : R) = ∏ i in s, (f i : R)
参数：f : ι -> Nat；s : Finset ι。
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
lemma cast_prod [CommSemiring R] (f : ι → ℕ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) :=
  map_prod (castRingHom R) _ _

end Nat

namespace Int
variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

/-
**Int.sum_div** 是 Mathlib 中的一个定理，位于命名空间 `Int`。
形式化陈述：∀ {ι : Type u_5} {s : Finset ι} {f : ι → ℤ} {n : ℤ}, (∀ i ∈ s, n ∣ f i) → 
(∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n
参数：∀ i ∈ s, n ∣ f i；∑ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ediv_zero`：∀ (a : ℤ), a / 0 = 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ediv_eq_iff_eq_mul_left`：∀ {a b c : ℤ}, b ≠ 0 → b ∣ a → (a / b = c ↔
 a = c * b)
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Int.ediv_mul_cancel`：∀ {a b : ℤ}, b ∣ a → a / b * b = a
-/
protected lemma sum_div (hf : ∀ i ∈ s, n ∣ f i) : (∑ i ∈ s, f i) / n = ∑ i ∈ s, f i / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [Int.ediv_eq_iff_eq_mul_left hn (dvd_sum hf), sum_mul]
  refine sum_congr rfl fun s hs ↦ ?_
  rw [Int.ediv_mul_cancel (hf _ hs)]

@[simp, norm_cast]
/-
**Int.cast_list_sum** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_list_sum [AddGroupWithOne R] (s : List Int) : (↑s.sum : R) = (s.map (
↑)).sum
参数：s : List Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_list_sum [AddGroupWithOne R] (s : List ℤ) : (↑s.sum : R) = (s.map (↑)).sum :=
  map_list_sum (castAddHom R) _

@[simp, norm_cast]
/-
**Int.cast_list_prod** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_list_prod [Ring R] (s : List Int) : (↑s.prod : R) = (s.map (↑)).prod
参数：s : List Int。
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
lemma cast_list_prod [Ring R] (s : List ℤ) : (↑s.prod : R) = (s.map (↑)).prod :=
  map_list_prod (castRingHom R) _

@[simp, norm_cast]
/-
**Int.cast_multiset_sum** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_multiset_sum [AddCommGroupWithOne R] (s : Multiset Int) : (↑s.sum : R
) = (s.map (↑)).sum
参数：s : Multiset Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_multiset_sum [AddCommGroupWithOne R] (s : Multiset ℤ) :
    (↑s.sum : R) = (s.map (↑)).sum :=
  map_multiset_sum (castAddHom R) _

@[simp, norm_cast]
/-
**Int.cast_multiset_prod** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset Int) : (↑s.prod 
: R) = (s.map (↑)).prod
参数：s : Multiset Int。
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
lemma cast_multiset_prod {R : Type*} [CommRing R] (s : Multiset ℤ) :
    (↑s.prod : R) = (s.map (↑)).prod :=
  map_multiset_prod (castRingHom R) _

@[simp, norm_cast]
/-
**Int.cast_sum** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι -> Int) : ↑(∑ x in 
s, f x : Int) = ∑ x in s, (f x : R)
参数：s : Finset ι；f : ι -> Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι → ℤ) :
    ↑(∑ x ∈ s, f x : ℤ) = ∑ x ∈ s, (f x : R) :=
  map_sum (castAddHom R) _ _

@[simp, norm_cast]
/-
**Int.cast_prod** 是 Mathlib 中的一个引理，位于命名空间 `Int`。
形式化陈述：cast_prod {R : Type*} [CommRing R] (f : ι -> Int) (s : Finset ι) : (↑(∏ i 
in s, f i) : R) = ∏ i in s, (f i : R)
参数：f : ι -> Int；s : Finset ι。
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
lemma cast_prod {R : Type*} [CommRing R] (f : ι → ℤ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) :=
  map_prod (Int.castRingHom R) _ _

end Int

