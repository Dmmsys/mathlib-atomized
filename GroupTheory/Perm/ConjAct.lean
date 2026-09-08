/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.GroupTheory.Perm.Cycle.Factors

/-!
# Some lemmas pertaining to the action of `ConjAct (Perm α)` on `Perm α`

We prove some lemmas related to the action of `ConjAct (Perm α)` on `Perm α`:

Let `α` be a decidable fintype.

* `conj_support_eq` relates the support of `k • g` with that of `g`

* `cycleFactorsFinset_conj_eq`, `mem_cycleFactorsFinset_conj'`
  and `cycleFactorsFinset_conj` relate the set of cycles of `g`, `g.cycleFactorsFinset`,
  with that for `k • g`

-/

public section

namespace Equiv.Perm

open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- `a : α` belongs to the support of `k • g` iff
  `k⁻¹ * a` belongs to the support of `g` -/
/-
**Equiv.Perm.mem_conj_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：mem_conj_support (k : ConjAct (Perm α)) (g : Perm α) (a : α) : a in (k • g
).support ↔ ConjAct.ofConjAct k⁻¹ a in g.support
参数：k : ConjAct (Perm α)；g : Perm α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.Perm.eq_inv_iff_eq`：eq_inv_iff_eq {f : Perm α} {x y : α} : x = f⁻¹
 y ↔ f x = y

--- 原说明 ---
`a : α` belongs to the support of `k • g` iff
  `k⁻¹ * a` belongs to the support of `g`
-/
theorem mem_conj_support (k : ConjAct (Perm α)) (g : Perm α) (a : α) :
    a ∈ (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a ∈ g.support := by
  simp only [mem_support, ConjAct.smul_def, not_iff_not, coe_mul,
    Function.comp_apply, ConjAct.ofConjAct_inv]
  exact eq_inv_iff_eq.symm
/-
**Equiv.Perm.support_conj_eq_smul_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：support_conj_eq_smul_support (k : ConjAct (Perm α)) (g : Equiv.Perm α) : (
k • g).support = k.ofConjAct • g.support
参数：k : ConjAct (Perm α)；g : Equiv.Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.mem_conj_support`：mem_conj_support (k : ConjAct (Perm α)) (g 
: Perm α) (a : α) : a in (k • g).support ↔ ConjAct.ofConjAct k⁻¹ a in g.support
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.smul_def`：∀ {α : Type u_6} (f : Equiv.Perm α) (a : α), f • a 
= f a
· 使用定理 `ConjAct.ofConjAct_inv`：ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (
ofConjAct x)⁻¹
· 使用定理 `Finset.inv_smul_mem_iff`：inv_smul_mem_iff : a⁻¹ • b in s ↔ b in a • s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem support_conj_eq_smul_support (k : ConjAct (Perm α)) (g : Equiv.Perm α) :
    (k • g).support = k.ofConjAct • g.support := by
  ext
  rw [mem_conj_support, ← Perm.smul_def, ConjAct.ofConjAct_inv, Finset.inv_smul_mem_iff]
/-
**Equiv.Perm.support_toConjAct_eq_smul_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm`。
形式化陈述：support_toConjAct_eq_smul_support (k g : Perm α) : (ConjAct.toConjAct k • 
g).support = k • g.support
参数：k g : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.support_conj_eq_smul_support`：support_conj_eq_smul_support (k
 : ConjAct (Perm α)) (g : Equiv.Perm α) : (k • g).support = k.ofConjAct • g.supp
ort
· 使用定理 `ConjAct.ofConjAct_toConjAct`：ofConjAct_toConjAct (x : G) : ofConjAct (to
ConjAct x) = x
-/
theorem support_toConjAct_eq_smul_support (k g : Perm α) :
    (ConjAct.toConjAct k • g).support = k • g.support := by
  rw [Equiv.Perm.support_conj_eq_smul_support, ConjAct.ofConjAct_toConjAct]
/-
**Equiv.Perm.cycleFactorsFinset_conj** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactorsFinset_conj (g k : Perm α) : (ConjAct.toConjAct k • g).cycleFa
ctorsFinset = Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinse
t
参数：g k : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.smul_def`：smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g
 * h * (ofConjAct g)⁻¹
· 使用定理 `ConjAct.ofConjAct_toConjAct`：ofConjAct_toConjAct (x : G) : ofConjAct (to
ConjAct x) = x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.mem_map_equiv`：mem_map_equiv {f : α ≃ β} {b : β} : b in s.map f.t
oEmbedding ↔ f.symm b in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_conj`：mem_cycleFactorsFinset_conj (g k
 c : Perm α) : k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset ↔ c in g.cycleFac
torsFinset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem cycleFactorsFinset_conj (g k : Perm α) :
    (ConjAct.toConjAct k • g).cycleFactorsFinset =
      Finset.map (MulAut.conj k).toEquiv.toEmbedding g.cycleFactorsFinset := by
  ext c
  rw [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, Finset.mem_map_equiv,
    ← mem_cycleFactorsFinset_conj g k]
  -- We avoid `group` here to minimize imports while low in the hierarchy;
  -- typically it would be better to invoke the tactic.
  simp [mul_assoc]

/-- A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g` -/
@[simp]
/-
**Equiv.Perm.mem_cycleFactorsFinset_conj'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`
。
形式化陈述：mem_cycleFactorsFinset_conj' (k : ConjAct (Perm α)) (g c : Perm α) : k • c
 in (k • g).cycleFactorsFinset ↔ c in g.cycleFactorsFinset
参数：k : ConjAct (Perm α)；g c : Perm α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_conj`：mem_cycleFactorsFinset_conj (g k
 c : Perm α) : k * c * k⁻¹ in (k * g * k⁻¹).cycleFactorsFinset ↔ c in g.cycleFac
torsFinset

--- 原说明 ---
A permutation `c` is a cycle of `g` iff `k • c` is a cycle of `k • g`
-/
theorem mem_cycleFactorsFinset_conj'
    (k : ConjAct (Perm α)) (g c : Perm α) :
    k • c ∈ (k • g).cycleFactorsFinset ↔ c ∈ g.cycleFactorsFinset := by
  simp only [ConjAct.smul_def]
  apply mem_cycleFactorsFinset_conj g k
/-
**Equiv.Perm.cycleFactorsFinset_conj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：cycleFactorsFinset_conj_eq (k : ConjAct (Perm α)) (g : Perm α) : cycleFact
orsFinset (k • g) = k • cycleFactorsFinset g
参数：k : ConjAct (Perm α)；g : Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_conj'`：mem_cycleFactorsFinset_conj' (k
 : ConjAct (Perm α)) (g c : Perm α) : k • c in (k • g).cycleFactorsFinset ↔ c in
 g.cycleFactorsFinset
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Finset.inv_smul_mem_iff`：inv_smul_mem_iff : a⁻¹ • b in s ↔ b in a • s
-/
theorem cycleFactorsFinset_conj_eq
    (k : ConjAct (Perm α)) (g : Perm α) :
    cycleFactorsFinset (k • g) = k • cycleFactorsFinset g := by
  ext c
  rw [← mem_cycleFactorsFinset_conj' k⁻¹ (k • g) c]
  simp only [inv_smul_smul]
  exact Finset.inv_smul_mem_iff

omit [Fintype α] in
/-
**Equiv.Perm.conj_smul_range_ofSubtype** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) : ConjAct
.toConjAct g • (ofSubtype (p
参数：g : Perm α；s : Finset α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.support_conj_eq_smul_support`：support_conj_eq_smul_support (k
 : ConjAct (Perm α)) (g : Equiv.Perm α) : (k • g).support = k.ofConjAct • g.supp
ort
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem conj_smul_range_ofSubtype [Finite α] (g : Perm α) (s : Finset α) :
    ConjAct.toConjAct g • (ofSubtype (p := (· ∈ s))).range =
      (ofSubtype (p := (· ∈ g • s))).range := by
  have : Fintype α := Fintype.ofFinite α
  ext k
  simp_rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_range_ofSubtype_iff]
  simp [support_conj_eq_smul_support, Set.subset_smul_set_iff]

end Equiv.Perm

