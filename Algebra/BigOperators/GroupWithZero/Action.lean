/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Data.Finset.Basic
public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Units.Equiv

/-!
# Lemmas about group actions on big operators

This file contains results about two kinds of actions:

* sums over `DistribSMul`: `r • ∑ x ∈ s, f x = ∑ x ∈ s, r • f x`
* products over `MulDistribMulAction` (with primed name): `r • ∏ x ∈ s, f x = ∏ x ∈ s, r • f x`
* products over `SMulCommClass` (with unprimed name):
  `b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x`

Note that analogous lemmas for `Module`s like `Finset.sum_smul` appear in other files.
-/

public section


variable {M N γ : Type*}

section

variable [AddMonoid N] [DistribSMul M N]

/-
**List.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem List.smul_sum {r : M} {l : List N} : r • l.sum = (l.map (r • ·)).sum :=
  map_list_sum (DistribSMul.toAddMonoidHom N r) l

end

section

variable [Monoid M] [Monoid N] [MulDistribMulAction M N]

/-
**List.smul_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem List.smul_prod' {r : M} {l : List N} : r • l.prod = (l.map (r • ·)).prod :=
  map_list_prod (MulDistribMulAction.toMonoidHom N r) l

end

section

variable [AddCommMonoid N] [DistribSMul M N] {r : M}

/-
**Multiset.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_multiset_sum`：∀ {M : Type u_5} {N : Type u_6} [inst : A
ddCommMonoid M] [inst_1 : AddCommMonoid N] (f : M →+ N) (s : Multiset M),   f s.
sum = (Multiset.map…
-/
theorem Multiset.smul_sum {s : Multiset N} : r • s.sum = (s.map (r • ·)).sum :=
  (DistribSMul.toAddMonoidHom N r).map_multiset_sum s
/-
**Finset.smul_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x in s, f x) = ∑ x in
 s, r • f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem Finset.smul_sum {f : γ → N} {s : Finset γ} :
    (r • ∑ x ∈ s, f x) = ∑ x ∈ s, r • f x :=
  map_sum (DistribSMul.toAddMonoidHom N r) f s
/-
**smul_finsum_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_finsum_mem {f : γ -> N} {s : Set γ} (hs : s.Finite) : r • ∑ᶠ x in s, 
f x = ∑ᶠ x in s, r • f x
参数：hs : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_finsum_mem`：∀ {α : Type u_1} {M : Type u_5} {N : Type u
_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N] {s : Set α}   (f : α → M
) (g : M →+ N), s…
-/
theorem smul_finsum_mem {f : γ → N} {s : Set γ} (hs : s.Finite) :
    r • ∑ᶠ x ∈ s, f x = ∑ᶠ x ∈ s, r • f x :=
  (DistribSMul.toAddMonoidHom N r).map_finsum_mem f hs

end

section

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

/-
**Multiset.smul_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)
).prod
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
-/
theorem Multiset.smul_prod' {r : M} {s : Multiset N} : r • s.prod = (s.map (r • ·)).prod :=
  (MulDistribMulAction.toMonoidHom N r).map_multiset_prod s
/-
**Finset.smul_prod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.smul_prod' {r : M} {f : γ -> N} {s : Finset γ} : (r • ∏ x in s, f x
) = ∏ x in s, r • f x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem Finset.smul_prod' {r : M} {f : γ → N} {s : Finset γ} :
    (r • ∏ x ∈ s, f x) = ∏ x ∈ s, r • f x :=
  map_prod (MulDistribMulAction.toMonoidHom N r) f s
/-
**smul_finprod'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_finprod' {ι : Sort*} [Finite ι] {f : ι -> N} (r : M) : r • ∏ᶠ x : ι, 
f x = ∏ᶠ x : ι, r • (f x)
参数：r : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `instFinitePLift`：∀ {α : Sort u_1} [Finite α], Finite (PLift α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_plift_of_mulSupport_subset`：finprod_eq_prod_plift_of_mul
Support_subset {f : α -> M} {s : Finset (PLift α)} (hs : mulSupport (f ∘ PLift.d
own) subseteq s) : ∏ᶠ i, f i = ∏…
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Finset.smul_prod'`：Finset.smul_prod' {r : M} {f : γ -> N} {s : Finset γ}
 : (r • ∏ x in s, f x) = ∏ x in s, r • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_finprod' {ι : Sort*} [Finite ι] {f : ι → N} (r : M) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

variable {G : Type*} [Group G] [MulDistribMulAction G N]
/-
**Finset.smul_prod_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finset.smul_prod_perm [Fintype G] (b : N) (g : G) : (g • ∏ h : G, h • b) =
 ∏ h : G, h • b
参数：b : N；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.smul_prod'`：Finset.smul_prod' {r : M} {f : γ -> N} {s : Finset γ}
 : (r • ∏ x in s, f x) = ∏ x in s, r • f x
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `Finset.prod_bijective`：prod_bijective (e : ι -> κ) (he : e.Bijective) (h
st : forall i, i in s ↔ e i in t) (hfg : forall i in s, f i = g (e i)) : ∏ i in 
s, f i = ∏ …
· 使用定理 `Group.mulLeft_bijective`：∀ {G : Type u_5} [inst : Group G] (a : G), Func
tion.Bijective fun x => a * x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem Finset.smul_prod_perm [Fintype G] (b : N) (g : G) :
    (g • ∏ h : G, h • b) = ∏ h : G, h • b := by
  simp only [smul_prod', smul_smul]
  exact Finset.prod_bijective (g * ·) (Group.mulLeft_bijective g) (by simp) (fun _ _ ↦ rfl)
/-
**smul_finprod_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_finprod_perm [Finite G] (b : N) (g : G) : (g • ∏ᶠ h : G, h • b) = ∏ᶠ 
h : G, h • b
参数：b : N；g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finprod_eq_prod_of_fintype`：finprod_eq_prod_of_fintype [Fintype α] (f : 
α -> M) : ∏ᶠ i : α, f i = ∏ i, f i
· 使用定理 `Finset.smul_prod_perm`：Finset.smul_prod_perm [Fintype G] (b : N) (g : G)
 : (g • ∏ h : G, h • b) = ∏ h : G, h • b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_finprod_perm [Finite G] (b : N) (g : G) :
    (g • ∏ᶠ h : G, h • b) = ∏ᶠ h : G, h • b := by
  cases nonempty_fintype G
  simp only [finprod_eq_prod_of_fintype, Finset.smul_prod_perm]

end

namespace List

@[to_additive]
/-
**List.smul_prod** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
 [SMulCommClass M N N] (l : List N) (m : M) : m ^ l.length • l.prod = (l.map (m 
• ·)).prod
参数：l : List N；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
-/
theorem smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (l : List N) (m : M) :
    m ^ l.length • l.prod = (l.map (m • ·)).prod := by
  induction l with
  | nil => simp
  | cons head tail ih => simp [← ih, smul_mul_smul_comm, pow_succ']

end List

namespace Multiset

@[to_additive]
/-
**Multiset.smul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：smul_prod [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N] 
[SMulCommClass M N N] (s : Multiset N) (b : M) : b ^ card s • s.prod = (s.map (b
 • ·)).prod
参数：s : Multiset N；b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.smul_prod`：smul_prod [Monoid M] [MulOneClass N] [MulAction M N] [Is
ScalarTower M N N] [SMulCommClass M N N] (l : List N) (m : M) : m ^ l.length • l
.pro…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem smul_prod [Monoid M] [CommMonoid N] [MulAction M N] [IsScalarTower M N N]
    [SMulCommClass M N N] (s : Multiset N) (b : M) :
    b ^ card s • s.prod = (s.map (b • ·)).prod :=
  Quot.induction_on s <| by simp [List.smul_prod]

end Multiset

namespace Finset

variable {ι : Type*}

/-
**Finset.smul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：smul_prod [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] 
[SMulCommClass M N N] (s : Finset ι) (b : M) (f : ι -> N) : b ^ s.card • ∏ x in 
s, f x = ∏ x in s, b • f x
参数：s : Finset ι；b : M；f : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.smul_prod`：smul_prod [Monoid M] [CommMonoid N] [MulAction M N] 
[IsScalarTower M N N] [SMulCommClass M N N] (s : Multiset N) (b : M) : b ^ card 
s • s.pr…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
-/
theorem smul_prod
    [CommMonoid N] [Monoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : M) (f : ι → N) :
    b ^ s.card • ∏ x ∈ s, f x = ∏ x ∈ s, b • f x := by
  have : Multiset.map (fun (x : ι) ↦ b • f x) s.val =
      Multiset.map (fun x ↦ b • x) (Multiset.map f s.val) := by
    simp only [Multiset.map_map, Function.comp_apply]
  simp_rw [prod_eq_multiset_prod, card_def, this, ← Multiset.smul_prod _ b, Multiset.card_map]
/-
**Finset.prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：prod_smul [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N
 N] [SMulCommClass M N N] (s : Finset ι) (b : ι -> M) (f : ι -> N) : ∏ i in s, b
 i • f i = (∏ i in s, b i) • ∏ i in s, f i
参数：s : Finset ι；b : ι -> M；f : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction_on`：cons_induction_on {α : Type*} {motive : Finset
 α -> Prop} (s : Finset α) (empty : motive ∅) (cons : forall (a : α) (s : Finset
 α) (h : a ∉ s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用引理 `smul_mul_smul_comm`：smul_mul_smul_comm [Mul α] [Mul β] [SMul α β] [IsSca
larTower α β β] [IsScalarTower α α β] [SMulCommClass α β β] (a : α) (b : β) (c :
 α) (d :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_smul
    [CommMonoid N] [CommMonoid M] [MulAction M N] [IsScalarTower M N N] [SMulCommClass M N N]
    (s : Finset ι) (b : ι → M) (f : ι → N) :
    ∏ i ∈ s, b i • f i = (∏ i ∈ s, b i) • ∏ i ∈ s, f i := by
  induction s using Finset.cons_induction_on with
  | empty => simp
  | cons _ _ hj ih => rw [prod_cons, ih, smul_mul_smul_comm, ← prod_cons hj, ← prod_cons hj]

end Finset

