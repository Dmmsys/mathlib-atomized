/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Junyan Xu
-/
module

public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.Finsupp.Multiset

/-! # Results on the cardinality of finitely supported functions and multisets. -/

public section

universe u v

namespace Cardinal

@[simp]
/-
**Cardinal.mk_finsupp_lift_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] 
: #(α ->₀ β) = lift.{u} #β ^ Fintype.card α
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
· 使用定理 `Cardinal.prod_const`：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod 
fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
theorem mk_finsupp_lift_of_fintype (α : Type u) (β : Type v) [Fintype α] [Zero β] :
    #(α →₀ β) = lift.{u} #β ^ Fintype.card α := by
  simpa using (@Finsupp.equivFunOnFinite α β _ _).cardinal_eq
/-
**Cardinal.mk_finsupp_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] : #(α ->₀ β) = #
β ^ Fintype.card α
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_finsupp_lift_of_fintype`：mk_finsupp_lift_of_fintype (α : Typ
e u) (β : Type v) [Fintype α] [Zero β] : #(α ->₀ β) = lift.{u} #β ^ Fintype.card
 α
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_finsupp_of_fintype (α β : Type u) [Fintype α] [Zero β] :
    #(α →₀ β) = #β ^ Fintype.card α := by simp

@[simp]
/-
**Cardinal.mk_finsupp_lift_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β
] [Nontrivial β] : #(α ->₀ β) = max (lift.{v} #α) (lift.{u} #β)
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Cardinal.mk_le_of_injective`：mk_le_of_injective {α β : Type u} {f : α ->
 β} (hf : Injective f) : #α <= #β
· 使用定理 `Finsupp.graph_injective`：graph_injective (α M) [Zero M] : Injective (@gr
aph α M _)
· 使用定理 `Cardinal.mk_finset_of_infinite`：mk_finset_of_infinite (α : Type u) [Infi
nite α] : #(Finset α) = #α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_prod`：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v
, u} #α * lift.{u, v} #β
· 使用定理 `Cardinal.mul_eq_max_of_aleph0_le_left`：mul_eq_max_of_aleph0_le_left {a b
 : Cardinal} (h : ℵ₀ <= a) (h' : b != 0) : a * b = max a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_le`：lift_mk_le {α : Type v} {β : Type w} : lift.{max u 
w} #α <= lift.{max u v} #β ↔ Nonempty (α ↪ β)
· 使用定理 `Finsupp.single_left_injective`：single_left_injective (h : b != 0) : Func
tion.Injective fun a : α => single a b
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `Finsupp.single_injective`：single_injective (a : α) : Function.Injective 
(single a : M -> α ->₀ M)
-/
theorem mk_finsupp_lift_of_infinite (α : Type u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  apply le_antisymm
  · calc
      #(α →₀ β) ≤ #(Finset (α × β)) := mk_le_of_injective (Finsupp.graph_injective α β)
      _ = #(α × β) := mk_finset_of_infinite _
      _ = max (lift.{v} #α) (lift.{u} #β) := by
        rw [mk_prod, mul_eq_max_of_aleph0_le_left] <;> simp
  · apply max_le <;> rw [← lift_id #(α →₀ β), ← lift_umax]
    · obtain ⟨b, hb⟩ := exists_ne (0 : β)
      exact lift_mk_le.{v}.2 ⟨⟨_, Finsupp.single_left_injective hb⟩⟩
    · inhabit α
      exact lift_mk_le.{u}.2 ⟨⟨_, Finsupp.single_injective default⟩⟩
/-
**Cardinal.mk_finsupp_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β]
 : #(α ->₀ β) = max #α #β
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite`：mk_finsupp_lift_of_infinite (α : T
ype u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_finsupp_of_infinite (α β : Type u) [Infinite α] [Zero β] [Nontrivial β] :
    #(α →₀ β) = max #α #β := by simp

@[simp]
/-
**Cardinal.mk_finsupp_lift_of_infinite'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero 
β] [Infinite β] : #(α ->₀ β) = max (lift.{v} #α) (lift.{u} #β)
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_finsupp_lift_of_fintype`：mk_finsupp_lift_of_fintype (α : Typ
e u) (β : Type v) [Fintype α] [Zero β] : #(α ->₀ β) = lift.{u} #β ^ Fintype.card
 α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.aleph0_le_lift`：aleph0_le_lift {c : Cardinal.{u}} : ℵ₀ <= lift.
{v} c ↔ ℵ₀ <= c
· 使用定理 `Cardinal.aleph0_le_mk`：aleph0_le_mk (α : Type u) [Infinite α] : ℵ₀ <= #α
· 使用定理 `max_eq_right`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, a ≤ b →
 max a b = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Cardinal.lift_le_aleph0`：lift_le_aleph0 {c : Cardinal.{u}} : lift.{v} c 
<= ℵ₀ ↔ c <= ℵ₀
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Cardinal.power_nat_eq`：power_nat_eq {c : Cardinal.{u}} {n : Nat} (h1 : ℵ
₀ <= c) (h2 : 1 <= n) : c ^ n = c
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite`：mk_finsupp_lift_of_infinite (α : T
ype u) (β : Type v) [Infinite α] [Zero β] [Nontrivial β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
-/
theorem mk_finsupp_lift_of_infinite' (α : Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max (lift.{v} #α) (lift.{u} #β) := by
  cases fintypeOrInfinite α
  · rw [mk_finsupp_lift_of_fintype]
    have : ℵ₀ ≤ (#β).lift := aleph0_le_lift.2 (aleph0_le_mk β)
    rw [max_eq_right (le_trans _ this), power_nat_eq this]
    exacts [Fintype.card_pos, lift_le_aleph0.2 (lt_aleph0_of_finite _).le]
  · apply mk_finsupp_lift_of_infinite
/-
**Cardinal.mk_finsupp_of_infinite'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] 
: #(α ->₀ β) = max #α #β
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_finsupp_of_infinite' (α β : Type u) [Nonempty α] [Zero β] [Infinite β] :
    #(α →₀ β) = max #α #β := by simp
/-
**Cardinal.mk_finsupp_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_finsupp_nat (α : Type u) [Nonempty α] : #(α ->₀ Nat) = max #α ℵ₀
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_finsupp_lift_of_infinite'`：mk_finsupp_lift_of_infinite' (α :
 Type u) (β : Type v) [Nonempty α] [Zero β] [Infinite β] : #(α ->₀ β) = max (lif
t.{v} #α) (lift.{u} #β)
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `Cardinal.mk_eq_aleph0`：mk_eq_aleph0 (α : Type*) [Countable α] [Infinite 
α] : #α = ℵ₀
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_finsupp_nat (α : Type u) [Nonempty α] : #(α →₀ ℕ) = max #α ℵ₀ := by simp
/-
**Cardinal.mk_multiset_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : #(Multiset α) = 1
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_multiset_of_isEmpty (α : Type u) [IsEmpty α] : #(Multiset α) = 1 :=
  Multiset.toFinsupp.toEquiv.cardinal_eq.trans (by simp)

@[simp]
/-
**Cardinal.mk_multiset_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_multiset_of_nonempty (α : Type u) [Nonempty α] : #(Multiset α) = max #α
 ℵ₀
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_finsupp_nat`：mk_finsupp_nat (α : Type u) [Nonempty α] : #(α 
->₀ Nat) = max #α ℵ₀
-/
theorem mk_multiset_of_nonempty (α : Type u) [Nonempty α] : #(Multiset α) = max #α ℵ₀ := by
  classical
  exact Multiset.toFinsupp.toEquiv.cardinal_eq.trans (mk_finsupp_nat α)
/-
**Cardinal.mk_multiset_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_multiset_of_infinite (α : Type u) [Infinite α] : #(Multiset α) = #α
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_multiset_of_nonempty`：mk_multiset_of_nonempty (α : Type u) [
Nonempty α] : #(Multiset α) = max #α ℵ₀
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Infinite.instNontrivial`：∀ (α : Type u_4) [Infinite α], Nontrivial α
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mk_multiset_of_infinite (α : Type u) [Infinite α] : #(Multiset α) = #α := by simp

end Cardinal

