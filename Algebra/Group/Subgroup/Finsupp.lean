/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-! # Connection between `Subgroup.closure` and `Finsupp.prod` -/

public section

assert_not_exists Field

namespace Subgroup

variable {M : Type*} [CommGroup M] {ι : Type*} (f : ι → M) (x : M)

@[to_additive]
/-
**Subgroup.exists_finsupp_of_mem_closure_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgro
up`。
形式化陈述：exists_finsupp_of_mem_closure_range (hx : x in closure (Set.range f)) : ex
ists a : ι ->₀ Int, x = a.prod (f · ^ ·)
参数：hx : x in closure (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.closure_induction`：closure_induction {p : (g : G) -> g in closu
re k -> Prop} (mem : forall x (hx : x in k), p x (subset_closure hx)) (one : p 1
 (one_mem _)) (m…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_single_index`：prod_single_index {a : α} {b : M} {h : α -> M
 -> N} (h_zero : h a 0 = 1) : (single a b).prod h = h a b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_ofNat`：zpow_ofNat (a : G) (n : Nat) : a ^ (ofNat(n) : Int) = a ^ Of
Nat.ofNat n
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Finsupp.prod_add_index`：prod_add_index [DecidableEq α] [AddZeroClass M] 
[CommMonoid N] {f g : α ->₀ M} {h : α -> M -> N} (h_zero : forall a in f.support
 union g.sup…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.prod_neg_index`：prod_neg_index [SubtractionMonoid G] [CommMonoid
 M] {g : α ->₀ G} {h : α -> G -> M} (h0 : forall a, h a 0 = 1) : (-g).prod h = g
.prod fun a …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `Finsupp.prod_inv`：prod_inv [Zero M] [CommGroup G] {f : α ->₀ M} {h : α -
> M -> G} : (f.prod fun a b => (h a b)⁻¹) = (f.prod h)⁻¹
-/
theorem exists_finsupp_of_mem_closure_range (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  classical
  induction hx using closure_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; exact ⟨Finsupp.single i 1, by simp⟩
  | one => use 0; simp
  | mul x y hx hy hx' hy' =>
    obtain ⟨⟨v, rfl⟩, w, rfl⟩ := And.intro hx' hy'
    use v + w
    rw [Finsupp.prod_add_index]
    · simp
    · simp [zpow_add]
  | inv x hx hx' =>
    obtain ⟨a, rfl⟩ := hx'
    use -a
    rw [Finsupp.prod_neg_index]
    · simp
    · simp

@[to_additive]
/-
**Subgroup.exists_of_mem_closure_range** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：exists_of_mem_closure_range [Fintype ι] (hx : x in closure (Set.range f)) 
: exists a : ι -> Int, x = ∏ i, f i ^ a i
参数：hx : x in closure (Set.range f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.exists_finsupp_of_mem_closure_range`：exists_finsupp_of_mem_clos
ure_range (hx : x in closure (Set.range f)) : exists a : ι ->₀ Int, x = a.prod (
f · ^ ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.prod_zpow`：prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f :
 α ->₀ Int) (g : α -> N) : (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_of_mem_closure_range [Fintype ι] (hx : x ∈ closure (Set.range f)) :
    ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  obtain ⟨a, rfl⟩ := exists_finsupp_of_mem_closure_range f x hx
  exact ⟨a, by simp⟩

variable {f x}

@[to_additive]
/-
**Subgroup.mem_closure_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_closure_range_iff : x in closure (Set.range f) ↔ exists a : ι ->₀ Int,
 x = a.prod (f · ^ ·)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.exists_finsupp_of_mem_closure_range`：exists_finsupp_of_mem_clos
ure_range (hx : x in closure (Set.range f)) : exists a : ι ->₀ Int, x = a.prod (
f · ^ ·)
· 使用定理 `Submonoid.prod_mem`：prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M
) {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c i
n t, f c…
· 使用定理 `zpow_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : DivInvMonoid M] [inst_
1 : SetLike S M] [hSM : SubgroupClass S M] {K : S}   {x : M}, x ∈ K → ∀ (n : ℤ…
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Subgroup.subset_closure`：subset_closure : k subseteq closure k
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mem_closure_range_iff :
    x ∈ closure (Set.range f) ↔ ∃ a : ι →₀ ℤ, x = a.prod (f · ^ ·) := by
  refine ⟨exists_finsupp_of_mem_closure_range f x, ?_⟩
  rintro ⟨a, rfl⟩
  exact Submonoid.prod_mem _ fun i hi ↦ zpow_mem (subset_closure (Set.mem_range_self i)) _

@[to_additive]
/-
**Subgroup.mem_closure_range_iff_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`
。
形式化陈述：mem_closure_range_iff_of_fintype [Fintype ι] : x in closure (Set.range f) 
↔ exists a : ι -> Int, x = ∏ i, f i ^ a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.exists_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∃ a, p a) ↔ ∃ b, p (e.symm b)
· 使用定理 `Subgroup.mem_closure_range_iff`：mem_closure_range_iff : x in closure (Se
t.range f) ↔ exists a : ι ->₀ Int, x = a.prod (f · ^ ·)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finsupp.prod_zpow`：prod_zpow {N} [DivisionCommMonoid N] [Fintype α] (f :
 α ->₀ Int) (g : α -> N) : (f.prod fun a b => g a ^ b) = ∏ a, g a ^ f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finsupp.equivFunOnFinite_apply`：∀ {α : Type u_1} {M : Type u_4} [inst : 
Zero M] [inst_1 : Finite α] (a : α →₀ M) (a_1 : α),   Finsupp.equivFunOnFinite a
 a_1 = a a_1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_range_iff_of_fintype [Fintype ι] :
    x ∈ closure (Set.range f) ↔ ∃ a : ι → ℤ, x = ∏ i, f i ^ a i := by
  rw [Finsupp.equivFunOnFinite.symm.exists_congr_left, mem_closure_range_iff]
  simp

@[to_additive]
/-
**Subgroup.mem_closure_iff_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：mem_closure_iff_of_fintype {s : Set M} [Fintype s] : x in closure s ↔ exis
ts a : s -> Int, x = ∏ i : s, i.1 ^ a i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `Subgroup.mem_closure_range_iff_of_fintype`：mem_closure_range_iff_of_fint
ype [Fintype ι] : x in closure (Set.range f) ↔ exists a : ι -> Int, x = ∏ i, f i
 ^ a i
-/
theorem mem_closure_iff_of_fintype {s : Set M} [Fintype s] :
    x ∈ closure s ↔ ∃ a : s → ℤ, x = ∏ i : s, i.1 ^ a i := by
  conv_lhs => rw [← Subtype.range_coe (s := s)]
  exact mem_closure_range_iff_of_fintype

end Subgroup

