/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.Perm.ConjAct
public import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
public import Mathlib.GroupTheory.Perm.DomMulAct
public import Mathlib.GroupTheory.Rank

/-!
# Centralizer of a permutation and cardinality of conjugacy classes in the symmetric groups

Let `α : Type` with `Fintype α` (and `DecidableEq α`).
The main goal of this file is to compute the cardinality of
conjugacy classes in `Equiv.Perm α`.
Every `g : Equiv.Perm α` has a `g.cycleType : Multiset ℕ`.
By `Equiv.Perm.isConj_iff_cycleType_eq`,
two permutations are conjugate in `Equiv.Perm α` iff
their cycle types are equal.
To compute the cardinality of the conjugacy classes, we could use
a purely combinatorial approach and compute the number of permutations
with given cycle type but we resorted to a more algebraic approach
based on the study of the centralizer of a permutation `g`.

Given `g : Equiv.Perm α`, the conjugacy class of `g` is the orbit
of `g` under the action `ConjAct (Equiv.Perm α)`, and we use the
orbit-stabilizer theorem
(`MulAction.card_orbit_mul_card_stabilizer_eq_card_group`) to reduce
the computation to the computation of the centralizer of `g`, the
subgroup of `Equiv.Perm α` consisting of all permutations which
commute with `g`. It is accessed here as `MulAction.stabilizer
(ConjAct (Equiv.Perm α)) g` and `Subgroup.centralizer_eq_comap_stabilizer`.

We compute this subgroup as follows.

* If `h : Subgroup.centralizer {g}`, then the action of `ConjAct.toConjAct h`
  by conjugation on `Equiv.Perm α` stabilizes `g.cycleFactorsFinset`.
  That induces an action of `Subgroup.centralizer {g}` on
  `g.cycleFactorsFinset` which is defined as an instance.

* This action defines a group morphism `Equiv.Perm.OnCycleFactors.toPermHom g`
  from `Subgroup.centralizer {g}` to `Equiv.Perm g.cycleFactorsFinset`.

* `Equiv.Perm.OnCycleFactors.range_toPermHom'` is the subgroup of
  `Equiv.Perm g.cycleFactorsFinset` consisting of permutations that
  preserve the cardinality of the support.

* `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'` shows that
  the range of `Equiv.Perm.OnCycleFactors.toPermHom g`
  is the subgroup `Equiv.Perm.OnCycleFactors.toPermHom_range' g`
  of `Equiv.Perm g.cycleFactorsFinset`.

This is shown by constructing a right inverse
`Equiv.Perm.Basis.toCentralizer`, as established by
`Equiv.Perm.Basis.toPermHom_apply_toCentralizer`.

* `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom` computes the
  cardinality of `(Equiv.Perm.OnCycleFactors.toPermHom g).range`
  as a product of factorials.

* `Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff` proves that
  `k : Subgroup.centralizer {g}` belongs to the kernel of
  `Equiv.Perm.OnCycleFactors.toPermHom g` if and only if it commutes with
  each cycle of `g`.  This is equivalent to the conjunction of two properties:
  * `k` preserves the set of fixed points of `g`;
  * on each cycle `c`, `k` acts as a power of that cycle.

This allows to give a description of the kernel of
`Equiv.Perm.OnCycleFactors.toPermHom g` as the product of a
symmetric group and of a product of cyclic groups.  This analysis
starts with the morphism `Equiv.Perm.OnCycleFactors.kerParam`, its
injectivity `Equiv.Perm.OnCycleFactors.kerParam_injective`, its range
`Equiv.Perm.OnCycleFactors.kerParam_range_eq`, and its cardinality
`Equiv.Perm.OnCycleFactors.kerParam_range_card`.

* `Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply` computes the signature
  of the permutation induced given by `Equiv.Perm.OnCycleFactors.kerParam`.

* `Equiv.Perm.nat_card_centralizer g` computes the cardinality
  of the centralizer of `g`.

* `Equiv.Perm.card_isConj_mul_eq g` computes the cardinality
  of the conjugacy class of `g`.

* We now can compute the cardinality of the set of permutations with given cycle type.
  The condition for this cardinality to be zero is given by
  `Equiv.Perm.card_of_cycleType_eq_zero_iff`
  which is itself derived from `Equiv.Perm.exists_with_cycleType_iff`.

* `Equiv.Perm.card_of_cycleType_mul_eq m` and `Equiv.Perm.card_of_cycleType m`
  compute this cardinality.

-/

@[expose] public section

open scoped Finset Pointwise

namespace Equiv.Perm

open MulAction Equiv Subgroup

variable {α : Type*} [DecidableEq α] [Fintype α] {g : Equiv.Perm α}

namespace OnCycleFactors

variable (g)

variable {g} in
/-
**Equiv.Perm.OnCycleFactors.Subgroup.Centralizer.toConjAct_smul_mem_cycleFactors
Finset** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.OnCycleFactors.Subgroup.Centralizer
`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {g k c : Equi
v.Perm α},   k ∈ Subgroup.centralizer {g} → c ∈ g.cycleFactorsFinset → ConjAct.t
oConjAct k • c ∈ g.cycleFactorsFinset
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycleFactorsFinset_conj_eq`：cycleFactorsFinset_conj_eq (k : C
onjAct (Perm α)) (g : Perm α) : cycleFactorsFinset (k • g) = k • cycleFactorsFin
set g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_inv_cancel`：mul_inv_cancel (a : G) : a * a⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Subgroup.mem_centralizer_singleton_iff`：mem_centralizer_singleton_iff {g
 k : G} : k in Subgroup.centralizer {g} ↔ k * g = g * k
· 使用定理 `ConjAct.toConjAct_smul`：toConjAct_smul (g h : G) : toConjAct g • h = g *
 h * g⁻¹
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset {k c : Perm α}
    (k_mem : k ∈ centralizer {g}) (c_mem : c ∈ g.cycleFactorsFinset) :
    ConjAct.toConjAct k • c ∈ g.cycleFactorsFinset := by
  suffices (g.cycleFactorsFinset : Set (Perm α)) =
    (ConjAct.toConjAct k) • g.cycleFactorsFinset by
    rw [← Finset.mem_coe, this]
    simp only [Set.smul_mem_smul_set_iff, Finset.mem_coe, c_mem]
  have := cycleFactorsFinset_conj_eq (ConjAct.toConjAct (k : Perm α)) g
  rw [ConjAct.toConjAct_smul, mem_centralizer_singleton_iff.mp k_mem, mul_assoc] at this
  simp only [mul_inv_cancel, mul_one] at this
  conv_lhs => rw [this]
  simp only [Finset.coe_smul_finset]

/-- The action by conjugation of `Subgroup.centralizer {g}`
  on the cycles of a given permutation -/
@[instance_reducible]
/-
**Equiv.Perm.OnCycleFactors.Subgroup.Centralizer.cycleFactorsFinset_mulAction** 
是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.OnCycleFactors.Subgroup.Centralizer`。
形式化陈述：{α : Type u_1} →   [inst : DecidableEq α] →     [inst_1 : Fintype α] → (g 
: Equiv.Perm α) → MulAction ↥(Subgroup.centralizer {g}) ↥g.cycleFactorsFinset
参数：g : Equiv.Perm α；Subgroup.centralizer {g}。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action by conjugation of `Subgroup.centralizer {g}`
  on the cycles of a given permutation
-/
def Subgroup.Centralizer.cycleFactorsFinset_mulAction :
    MulAction (centralizer {g}) g.cycleFactorsFinset where
  smul k c := ⟨ConjAct.toConjAct (k : Perm α) • c.val,
    Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩
  one_smul c := by
    rw [← Subtype.coe_inj]
    change ConjAct.toConjAct (1 : Perm α) • c.val = c
    simp only [map_one, one_smul]
  mul_smul k l c := by
    simp only [← Subtype.coe_inj]
    change ConjAct.toConjAct (k * l : Perm α) • c.val =
      ConjAct.toConjAct (k : Perm α) • (ConjAct.toConjAct (l : Perm α)) • c.val
    simp only [map_mul, mul_smul]

/-- The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset` -/
/-
**Equiv.Perm.OnCycleFactors.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm.OnCycleFactor
s`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The conjugation action of `Subgroup.centralizer {g}` on `g.cycleFactorsFinset`
-/
scoped instance : MulAction (centralizer {g}) (g.cycleFactorsFinset) :=
  (Subgroup.Centralizer.cycleFactorsFinset_mulAction g)

/-- The canonical morphism from `Subgroup.centralizer {g}`
  to the group of permutations of `g.cycleFactorsFinset` -/
/-
**Equiv.Perm.OnCycleFactors.toPermHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.OnCy
cleFactors`。
形式化陈述：toPermHom
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical morphism from `Subgroup.centralizer {g}`
  to the group of permutations of `g.cycleFactorsFinset`
-/
def toPermHom := MulAction.toPermHom (centralizer {g}) g.cycleFactorsFinset
/-
**Equiv.Perm.OnCycleFactors.centralizer_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm.OnCycleFactors`。
形式化陈述：centralizer_smul_def (k : centralizer {g}) (c : g.cycleFactorsFinset) : k 
• c = ⟨k * c * k⁻¹, Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k
.prop c.prop⟩
参数：k : centralizer {g}；c : g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem centralizer_smul_def (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    k • c = ⟨k * c * k⁻¹,
      Subgroup.Centralizer.toConjAct_smul_mem_cycleFactorsFinset k.prop c.prop⟩ :=
  rfl

@[simp]
/-
**Equiv.Perm.OnCycleFactors.val_centralizer_smul** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm.OnCycleFactors`。
形式化陈述：val_centralizer_smul (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFin
set) : ((k • c :) : Perm α) = k * c * k⁻¹
参数：k : Subgroup.centralizer {g}；c : g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem val_centralizer_smul (k : Subgroup.centralizer {g}) (c : g.cycleFactorsFinset) :
    ((k • c :) : Perm α) = k * c * k⁻¹ :=
  rfl
/-
**Equiv.Perm.OnCycleFactors.toPermHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Per
m.OnCycleFactors`。
形式化陈述：toPermHom_apply (k : centralizer {g}) (c : g.cycleFactorsFinset) : (toPerm
Hom g k c) = k • c
参数：k : centralizer {g}；c : g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPermHom_apply (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c) = k • c := rfl
/-
**Equiv.Perm.OnCycleFactors.coe_toPermHom** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
OnCycleFactors`。
形式化陈述：coe_toPermHom (k : centralizer {g}) (c : g.cycleFactorsFinset) : (toPermHo
m g k c : Perm α) = k * c * (k : Perm α)⁻¹
参数：k : centralizer {g}；c : g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toPermHom (k : centralizer {g}) (c : g.cycleFactorsFinset) :
    (toPermHom g k c : Perm α) = k * c * (k : Perm α)⁻¹ := rfl

/-- The range of `Equiv.Perm.OnCycleFactors.toPermHom`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'`. -/
/-
**Equiv.Perm.OnCycleFactors.range_toPermHom'** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Pe
rm.OnCycleFactors`。
形式化陈述：range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of `Equiv.Perm.OnCycleFactors.toPermHom`.

The equality is proved by `Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_to
PermHom'`.
-/
def range_toPermHom' : Subgroup (Perm g.cycleFactorsFinset) where
  carrier := {τ | ∀ c, #(τ c).val.support = #c.val.support}
  one_mem' := by simp
  mul_mem' hσ hτ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq, coe_mul, Function.comp_apply]
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ hτ
    intro c hc
    rw [hσ, hτ]
  inv_mem' hσ := by
    simp only [Subtype.forall, Set.mem_ofPred_eq] at hσ ⊢
    intro c hc
    rw [← hσ _ (by simp)]
    simp

variable {g} in
/-
**Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.OnCycleFactors`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : Fintype α] {g : Equiv.Pe
rm α} {τ : Equiv.Perm ↥g.cycleFactorsFinset},   τ ∈ Equiv.Perm.OnCycleFactors.ra
nge_toPermHom' g ↔     ∀ (c : ↥g.cycleFactorsFinset), (↑(τ c)).support.card = (↑
c).support.card
参数：c : ↥g.cycleFactorsFinset；↑(τ c)；↑c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_range_toPermHom'_iff {τ : Perm g.cycleFactorsFinset} :
    τ ∈ range_toPermHom' g ↔ ∀ c, #(τ c).val.support = #c.val.support :=
  Iff.rfl

variable (k : centralizer {g})

/-- `k : Subgroup.centralizer {g}` belongs to the kernel of `toPermHom g`
  iff it commutes with each cycle of `g` -/
/-
**Equiv.Perm.OnCycleFactors.mem_ker_toPermHom_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equ
iv.Perm.OnCycleFactors`。
形式化陈述：mem_ker_toPermHom_iff : k in (toPermHom g).ker ↔ forall c in g.cycleFactor
sFinset, Commute (k : Perm α) c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`k : Subgroup.centralizer {g}` belongs to the kernel of `toPermHom g`
  iff it commutes with each cycle of `g`
-/
theorem mem_ker_toPermHom_iff :
    k ∈ (toPermHom g).ker ↔ ∀ c ∈ g.cycleFactorsFinset, Commute (k : Perm α) c := by
  simp only [toPermHom, MonoidHom.mem_ker, DFunLike.ext_iff, Subtype.forall]
  refine forall₂_congr (fun _ _ ↦ ?_)
  simp [← Subtype.coe_inj, commute_iff_eq, mul_inv_eq_iff_eq_mul]

end OnCycleFactors

open OnCycleFactors

/-- A `Basis` of a permutation is a choice of an element in each of its cycles -/
/-
**Equiv.Perm.Basis** 是 Mathlib 中的一个归纳类型，位于命名空间 `Equiv.Perm`。
形式化陈述：{α : Type u_1} → [DecidableEq α] → [Fintype α] → Equiv.Perm α → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Basis` of a permutation is a choice of an element in each of its cycles
-/
structure Basis (g : Equiv.Perm α) where
  /-- A choice of elements in each cycle -/
  (toFun : g.cycleFactorsFinset → α)
  /-- For each cycle, the chosen element belongs to the cycle -/
  (mem_support_self' : ∀ (c : g.cycleFactorsFinset), toFun c ∈ c.val.support)
/-
**Equiv.Perm.** 是 Mathlib 中的一个实例，位于命名空间 `Equiv.Perm`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (g : Perm α) : FunLike (Basis g) g.cycleFactorsFinset α where
  coe a := a.toFun
  coe_injective a a' _ := by cases a; cases a'; congr

namespace Basis

/-
**Equiv.Perm.Basis.nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：nonempty (g : Perm α) : Nonempty (Basis g)
参数：g : Perm α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.IsCycle.nonempty_support`：∀ {α : Type u_2} [inst : Fintype α]
 [inst_1 : DecidableEq α] {g : Equiv.Perm α}, g.IsCycle → g.support.Nonempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
theorem nonempty (g : Perm α) : Nonempty (Basis g) := by
  have (c : g.cycleFactorsFinset) : c.val.support.Nonempty :=
    IsCycle.nonempty_support (mem_cycleFactorsFinset_iff.mp c.prop).1
  exact ⟨fun c ↦ (this c).choose, fun c ↦ (this c).choose_spec⟩

variable (a : Basis g) (c : g.cycleFactorsFinset)
/-
**Equiv.Perm.Basis.mem_support_self** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`
。
形式化陈述：mem_support_self : a c in c.val.support
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.mem_support_self'`：∀ {α : Type u_1} [inst : DecidableEq
 α] [inst_1 : Fintype α] {g : Equiv.Perm α} (self : g.Basis)   (c : ↥g.cycleFact
orsFinset), self.toFun c…
-/
theorem mem_support_self :
    a c ∈ c.val.support := a.mem_support_self' c
/-
**Equiv.Perm.Basis.injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：injective : Function.Injective a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem injective : Function.Injective a := by
  intro c d h
  rw [← Subtype.coe_inj]
  apply g.cycleFactorsFinset_pairwise_disjoint.eq c.prop d.prop
  simp only [Disjoint, not_forall, not_or]
  use a c
  conv_rhs => rw [h]
  simp only [← Perm.mem_support, a.mem_support_self c, a.mem_support_self d, and_self]
/-
**Equiv.Perm.Basis.cycleOf_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：cycleOf_eq : g.cycleOf (a c) = c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycle_is_cycleOf`：cycle_is_cycleOf {f c : Equiv.Perm α} {a : 
α} (ha : a in c.support) (hc : c in f.cycleFactorsFinset) : c = f.cycleOf a
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem cycleOf_eq : g.cycleOf (a c) = c :=
  (cycle_is_cycleOf (a.mem_support_self c) c.prop).symm
/-
**Equiv.Perm.Basis.sameCycle** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：sameCycle {x : α} (hx : g.cycleOf x in g.cycleFactorsFinset) : g.SameCycle
 (a ⟨g.cycleOf x, hx⟩) x
参数：hx : g.cycleOf x in g.cycleFactorsFinset。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.SameCycle.symm`：∀ {α : Type u_2} {f : Equiv.Perm α} {x y : α}
, f.SameCycle x y → f.SameCycle y x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support_cycleOf_iff`：mem_support_cycleOf_iff [DecidableEq
 α] [Fintype α] : y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
-/
theorem sameCycle {x : α} (hx : g.cycleOf x ∈ g.cycleFactorsFinset) :
    g.SameCycle (a ⟨g.cycleOf x, hx⟩) x :=
  (mem_support_cycleOf_iff.mp (a.mem_support_self ⟨g.cycleOf x, hx⟩)).1.symm

variable (τ : range_toPermHom' g)

/-- The function that will provide a right inverse `toCentralizer` to `toPermHom` -/
/-
**Equiv.Perm.Basis.ofPermHomFun** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：ofPermHomFun (x : α) : α
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function that will provide a right inverse `toCentralizer` to `toPermHom`
-/
def ofPermHomFun (x : α) : α :=
  if hx : g.cycleOf x ∈ g.cycleFactorsFinset
  then
    (g ^ (Nat.find (a.sameCycle hx).exists_nat_pow_eq))
      (a ((τ : Perm g.cycleFactorsFinset) ⟨g.cycleOf x, hx⟩))
  else x
/-
**Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.Basis`。
形式化陈述：mem_fixedPoints_or_exists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ 
exists (c : g.cycleFactorsFinset) (_ : x in c.val.support) (m : Int), (g ^ m) (a
 c) = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Equiv.Perm.mem_support_cycleOf_iff`：mem_support_cycleOf_iff [DecidableEq
 α] [Fintype α] : y in support (f.cycleOf x) ↔ SameCycle f x y ∧ x in support f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Equiv.Perm.Basis.sameCycle`：sameCycle {x : α} (hx : g.cycleOf x in g.cyc
leFactorsFinset) : g.SameCycle (a ⟨g.cycleOf x, hx⟩) x
-/
theorem mem_fixedPoints_or_exists_zpow_eq (x : α) :
    x ∈ Function.fixedPoints g ∨
      ∃ (c : g.cycleFactorsFinset) (_ : x ∈ c.val.support) (m : ℤ), (g ^ m) (a c) = x := by
  rw [Classical.or_iff_not_imp_left]
  intro hx
  rw [Function.mem_fixedPoints_iff, ← ne_eq, ← mem_support,
    ← cycleOf_mem_cycleFactorsFinset_iff] at hx
  refine ⟨⟨g.cycleOf x, hx⟩, ?_, (a.sameCycle hx)⟩
  rw [mem_support_cycleOf_iff, ← cycleOf_mem_cycleFactorsFinset_iff]
  simp [SameCycle.rfl, hx, and_self]
/-
**Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.Basis`。
形式化陈述：ofPermHomFun_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx :
 x in c.val.support) {m : Int} (hm : (g ^ m) (a c) = x) : ofPermHomFun a τ x = (
g ^ m) (a ((τ : Perm g.cycleFactorsFinset) c))
参数：hx : x in c.val.support；hm : (g ^ m) (a c) = x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.cycle_is_cycleOf`：cycle_is_cycleOf {f c : Equiv.Perm α} {a : 
α} (ha : a in c.support) (hc : c in f.cycleFactorsFinset) : c = f.cycleOf a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Equiv.Perm.SameCycle.exists_nat_pow_eq`：∀ {α : Type u_2} {f : Equiv.Perm
 α} {x y : α} [Finite α], f.SameCycle x y → ∃ i, (f ^ i) x = y
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Equiv.Perm.Basis.sameCycle`：sameCycle {x : α} (hx : g.cycleOf x in g.cyc
leFactorsFinset) : g.SameCycle (a ⟨g.cycleOf x, hx⟩) x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subtype.coe_inj`：coe_inj {a b : Subtype p} : (a : α) = b ↔ a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Equiv.Perm.IsCycleOn.zpow_apply_eq_zpow_apply`：∀ {α : Type u_2} {f : Equ
iv.Perm α} {a : α} {s : Finset α},   f.IsCycleOn ↑s → a ∈ s → ∀ {m n : ℤ}, (f ^ 
m) a = (f ^ n) a ↔ m ≡ n [ZMOD ↑s.c…
· 使用定理 `Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset`：isCycleOn_suppor
t_of_mem_cycleFactorsFinset {g c : Equiv.Perm α} (hc : c in g.cycleFactorsFinset
) : IsCycleOn g c.support
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
-/
theorem ofPermHomFun_apply_of_cycleOf_mem {x : α} {c : g.cycleFactorsFinset}
    (hx : x ∈ c.val.support) {m : ℤ} (hm : (g ^ m) (a c) = x) :
    ofPermHomFun a τ x = (g ^ m) (a ((τ : Perm g.cycleFactorsFinset) c)) := by
  have hx' : c = g.cycleOf x := cycle_is_cycleOf hx (Subtype.prop c)
  have hx'' : g.cycleOf x ∈ g.cycleFactorsFinset := hx' ▸ c.prop
  set n := Nat.find (a.sameCycle hx'').exists_nat_pow_eq
  have hn : (g ^ (n : ℤ)) (a c) = x := by
    rw [← Nat.find_spec (a.sameCycle hx'').exists_nat_pow_eq, zpow_natCast]
    congr
    rw [← Subtype.coe_inj, hx']
  suffices ofPermHomFun a τ x = (g ^ (n : ℤ)) (a ((τ : Perm g.cycleFactorsFinset) c)) by
    rw [this, IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset ((τ : Perm g.cycleFactorsFinset) c).prop)
      (mem_support_self a ((τ : Perm g.cycleFactorsFinset) c))]
    simp only [τ.prop c]
    rw [← IsCycleOn.zpow_apply_eq_zpow_apply
      (isCycleOn_support_of_mem_cycleFactorsFinset c.prop) (mem_support_self a c)]
    rw [hn, hm]
  simp only [ofPermHomFun, dif_pos hx'']
  congr
  exact hx'.symm
/-
**Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints** 是 Mathlib 中的一个定理，位于命名
空间 `Equiv.Perm.Basis`。
形式化陈述：ofPermHomFun_apply_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoi
nts g) : ofPermHomFun a τ x = x
参数：hx : x in Function.fixedPoints g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun.eq_1`：∀ {α : Type u_1} [inst : DecidableEq
 α] [inst_1 : Fintype α] {g : Equiv.Perm α} (a : g.Basis)   (τ : ↥(Equiv.Perm.On
CycleFactors.range_toPer…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
-/
theorem ofPermHomFun_apply_of_mem_fixedPoints {x : α} (hx : x ∈ Function.fixedPoints g) :
    ofPermHomFun a τ x = x := by
  rw [ofPermHomFun, dif_neg]
  rw [cycleOf_mem_cycleFactorsFinset_iff, notMem_support]
  exact hx
/-
**Equiv.Perm.Basis.ofPermHomFun_apply_mem_support_cycle_iff** 是 Mathlib 中的一个定理，位
于命名空间 `Equiv.Perm.Basis`。
形式化陈述：ofPermHomFun_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset
} : ofPermHomFun a τ x in ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
 x in c.val.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq`：mem_fixedPoints_or_e
xists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ exists (c : g.cycleFactors
Finset) (_ : x in c.val.support) (m : In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints`：ofPermHomFun_app
ly_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) : ofPermHomFun 
a τ x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem`：ofPermHomFun_apply_o
f_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx : x in c.val.support) {m : 
Int} (hm : (g ^ m) (a c) = x) : ofPermHo…
· 使用定理 `Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff`：zpow_ap
ply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α} {x : α} {m : Int} {c 
: g.cycleFactorsFinset} : (g ^ m) x in (c : Perm α).s…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
-/
theorem ofPermHomFun_apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} :
    ofPermHomFun a τ x ∈ ((τ : Perm g.cycleFactorsFinset) c : Perm α).support ↔
      x ∈ c.val.support := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨d, hd, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx]
    suffices ∀ (d : g.cycleFactorsFinset), x ∉ (d : Perm α).support by
      simp only [this]
    intro d hx'
    rw [Function.mem_fixedPoints_iff, ← notMem_support] at hx
    apply hx
    exact mem_cycleFactorsFinset_support_le d.prop hx'
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hd hm] --
    rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
    by_cases h : c = d
    · simp only [h, hd, mem_support_self]
    · have H : Disjoint c.val d.val :=
        cycleFactorsFinset_pairwise_disjoint g c.prop d.prop (Subtype.coe_ne_coe.mpr h)
      have H' : Disjoint ((τ : Perm g.cycleFactorsFinset) c : Perm α)
        ((τ : Perm g.cycleFactorsFinset) d : Perm α) :=
        cycleFactorsFinset_pairwise_disjoint g ((τ : Perm g.cycleFactorsFinset) c).prop
          ((τ : Perm g.cycleFactorsFinset) d).prop (by
          intro h'; apply h
          simpa only [Subtype.coe_inj, EmbeddingLike.apply_eq_iff_eq] using h')
      rw [disjoint_iff_disjoint_support, Finset.disjoint_right] at H H'
      simp only [H hd, H' (mem_support_self a _)]
/-
**Equiv.Perm.Basis.ofPermHomFun_commute_zpow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Eq
uiv.Perm.Basis`。
形式化陈述：ofPermHomFun_commute_zpow_apply (x : α) (j : Int) : ofPermHomFun a τ ((g ^
 j) x) = (g ^ j) (ofPermHomFun a τ x)
参数：x : α；j : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq`：mem_fixedPoints_or_e
xists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ exists (c : g.cycleFactors
Finset) (_ : x in c.val.support) (m : In…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints`：ofPermHomFun_app
ly_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) : ofPermHomFun 
a τ x = x
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `zpow_add_one`：∀ {G : Type u_3} [inst : Group G] (a : G) (n : ℤ), a ^ (n 
+ 1) = a ^ n * a
· 使用引理 `zpow_add`：zpow_add (a : G) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem`：ofPermHomFun_apply_o
f_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx : x in c.val.support) {m : 
Int} (hm : (g ^ m) (a c) = x) : ofPermHo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff`：zpow_ap
ply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α} {x : α} {m : Int} {c 
: g.cycleFactorsFinset} : (g ^ m) x in (c : Perm α).s…
-/
theorem ofPermHomFun_commute_zpow_apply (x : α) (j : ℤ) :
    ofPermHomFun a τ ((g ^ j) x) = (g ^ j) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | hx)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ofPermHomFun_apply_of_mem_fixedPoints]
    rw [Function.mem_fixedPoints_iff]
    simp only [← mul_apply, ← zpow_one_add, add_comm]
    conv_rhs => rw [← hx, ← mul_apply, ← zpow_add_one]
  · obtain ⟨c, hc, m, hm⟩ := hx
    have hm' : (g ^ (j + m)) (a c) = (g ^ j) x := by rw [zpow_add, mul_apply, hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm, ofPermHomFun_apply_of_cycleOf_mem a τ _ hm',
      ← mul_apply, ← zpow_add]
    exact zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff.mpr hc
/-
**Equiv.Perm.Basis.ofPermHomFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`
。
形式化陈述：ofPermHomFun_mul (σ τ : range_toPermHom' g) (x) : ofPermHomFun a (σ * τ) x
 = (ofPermHomFun a σ) (ofPermHomFun a τ x)
参数：σ τ : range_toPermHom' g；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq`：mem_fixedPoints_or_e
xists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ exists (c : g.cycleFactors
Finset) (_ : x in c.val.support) (m : In…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints`：ofPermHomFun_app
ly_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) : ofPermHomFun 
a τ x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem`：ofPermHomFun_apply_o
f_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx : x in c.val.support) {m : 
Int} (hm : (g ^ m) (a c) = x) : ofPermHo…
· 使用定理 `Equiv.Perm.zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff`：zpow_ap
ply_mem_support_of_mem_cycleFactorsFinset_iff {g : Perm α} {x : α} {m : Int} {c 
: g.cycleFactorsFinset} : (g ^ m) x in (c : Perm α).s…
· 使用定理 `Equiv.Perm.Basis.mem_support_self`：mem_support_self : a c in c.val.suppo
rt
-/
theorem ofPermHomFun_mul (σ τ : range_toPermHom' g) (x) :
    ofPermHomFun a (σ * τ) x = (ofPermHomFun a σ) (ofPermHomFun a τ x) := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · simp only [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm]
    rw [ofPermHomFun_apply_of_cycleOf_mem a _ _ rfl]
    · rfl
    · rw [zpow_apply_mem_support_of_mem_cycleFactorsFinset_iff]
      apply mem_support_self
/-
**Equiv.Perm.Basis.ofPermHomFun_one** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`
。
形式化陈述：ofPermHomFun_one (x : α) : (ofPermHomFun a 1) x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq`：mem_fixedPoints_or_e
xists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ exists (c : g.cycleFactors
Finset) (_ : x in c.val.support) (m : In…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints`：ofPermHomFun_app
ly_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) : ofPermHomFun 
a τ x = x
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem`：ofPermHomFun_apply_o
f_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx : x in c.val.support) {m : 
Int} (hm : (g ^ m) (a c) = x) : ofPermHo…
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `OneMemClass.coe_one`：coe_one : ((1 : S') : M₁) = 1
· 使用定理 `Equiv.Perm.coe_one`：∀ {α : Type u_4}, ⇑1 = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
-/
theorem ofPermHomFun_one (x : α) : (ofPermHomFun a 1) x = x := by
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · rw [ofPermHomFun_apply_of_mem_fixedPoints a _ hx]
  · rw [ofPermHomFun_apply_of_cycleOf_mem a _ hc hm, OneMemClass.coe_one, coe_one, id_eq, hm]

set_option backward.isDefEq.respectTransparency false in
/-- Given `a : g.Basis` and a permutation of `g.cycleFactorsFinset` that
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g` -/
/-
**Equiv.Perm.Basis.ofPermHom** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：ofPermHom : range_toPermHom' g ->* Perm α where toFun τ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `a : g.Basis` and a permutation of `g.cycleFactorsFinset` that
  preserve the lengths of the cycles, a permutation of `α` that
  moves the `Basis` and commutes with `g`
-/
noncomputable def ofPermHom : range_toPermHom' g →* Perm α where
  toFun τ := {
    toFun := ofPermHomFun a τ
    invFun := ofPermHomFun a τ⁻¹
    left_inv := fun x ↦ by rw [← ofPermHomFun_mul, inv_mul_cancel, ofPermHomFun_one]
    right_inv := fun x ↦ by rw [← ofPermHomFun_mul, mul_inv_cancel, ofPermHomFun_one] }
  map_one' := ext fun x ↦ ofPermHomFun_one a x
  map_mul' := fun σ τ ↦ ext fun x ↦ by simp [mul_apply, ofPermHomFun_mul a σ τ x]
/-
**Equiv.Perm.Basis.ofPermHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：ofPermHom_apply (τ) (x) : a.ofPermHom τ x = a.ofPermHomFun τ x
参数：τ；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofPermHom_apply (τ) (x) : a.ofPermHom τ x = a.ofPermHomFun τ x := rfl
/-
**Equiv.Perm.Basis.ofPermHom_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Basis
`。
形式化陈述：ofPermHom_support : (ofPermHom a τ).support = (τ : Perm g.cycleFactorsFins
et).support.biUnion (fun c => c.val.support)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.Basis.mem_fixedPoints_or_exists_zpow_eq`：mem_fixedPoints_or_e
xists_zpow_eq (x : α) : x in Function.fixedPoints g ∨ exists (c : g.cycleFactors
Finset) (_ : x in c.val.support) (m : In…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_mem_fixedPoints`：ofPermHomFun_app
ly_of_mem_fixedPoints {x : α} (hx : x in Function.fixedPoints g) : ofPermHomFun 
a τ x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_of_cycleOf_mem`：ofPermHomFun_apply_o
f_cycleOf_mem {x : α} {c : g.cycleFactorsFinset} (hx : x in c.val.support) {m : 
Int} (hm : (g ^ m) (a c) = x) : ofPermHo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.Perm.Basis.injective`：injective : Function.Injective a
· 使用定理 `not_iff_comm`：not_iff_comm : (¬a ↔ b) ↔ (¬b ↔ a)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
（共 32 条，此处仅展示前 30 条）
-/
theorem ofPermHom_support :
    (ofPermHom a τ).support =
      (τ : Perm g.cycleFactorsFinset).support.biUnion (fun c ↦ c.val.support) := by
  ext x
  simp only [mem_support, Finset.mem_biUnion, ofPermHom_apply]
  rcases mem_fixedPoints_or_exists_zpow_eq a x with (hx | ⟨c, hc, m, hm⟩)
  · simp only [ofPermHomFun_apply_of_mem_fixedPoints a τ hx, ne_eq, not_true_eq_false, false_iff,
      ← mem_support]
    rintro ⟨c, -, hc⟩
    rw [Function.mem_fixedPoints_iff] at hx
    exact mem_support.mp ((mem_cycleFactorsFinset_support_le c.prop) hc) hx
  · rw [ofPermHomFun_apply_of_cycleOf_mem a τ hc hm]
    conv_lhs => rw [← hm]
    rw [(g ^ m).injective.ne_iff, a.injective.ne_iff, not_iff_comm]
    by_cases H : (τ : Perm g.cycleFactorsFinset) c = c
    · simp only [H, iff_true]
      push Not
      intro d hd
      rw [← notMem_support]
      have := g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop
      rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at this
      exact this (by lia) hc
    · simpa only [H, iff_false, not_not] using ⟨c, H, mem_support.mp hc⟩
/-
**Equiv.Perm.Basis.card_ofPermHom_support** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.
Basis`。
形式化陈述：card_ofPermHom_support : #(ofPermHom a τ).support = ∑ c in (τ : Perm g.cyc
leFactorsFinset).support, #c.val.support
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.Basis.ofPermHom_support`：ofPermHom_support : (ofPermHom a τ).
support = (τ : Perm g.cycleFactorsFinset).support.biUnion (fun c => c.val.suppor
t)
· 使用定理 `Finset.card_biUnion`：card_biUnion [DecidableEq M] {t : ι -> Finset M} (h
 : (s : Set ι).PairwiseDisjoint t) : #(s.biUnion t) = ∑ u in s, #(t u)
· 使用定理 `Equiv.Perm.Disjoint.disjoint_support`：∀ {α : Type u_1} [inst : Decidable
Eq α] [inst_1 : Fintype α] {f g : Equiv.Perm α},   f.Disjoint g → Disjoint f.sup
port g.support
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
-/
theorem card_ofPermHom_support :
    #(ofPermHom a τ).support = ∑ c ∈ (τ : Perm g.cycleFactorsFinset).support, #c.val.support := by
  rw [ofPermHom_support, Finset.card_biUnion]
  intro c _ d _ h
  apply Equiv.Perm.Disjoint.disjoint_support
  apply g.cycleFactorsFinset_pairwise_disjoint c.prop d.prop (Subtype.coe_ne_coe.mpr h)
/-
**Equiv.Perm.Basis.ofPermHom_mem_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm.Basis`。
形式化陈述：ofPermHom_mem_centralizer : a.ofPermHom τ in centralizer {g}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subgroup.mem_centralizer_singleton_iff`：mem_centralizer_singleton_iff {g
 k : G} : k in Subgroup.centralizer {g} ↔ k * g = g * k
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_commute_zpow_apply`：ofPermHomFun_commute_z
pow_apply (x : α) (j : Int) : ofPermHomFun a τ ((g ^ j) x) = (g ^ j) (ofPermHomF
un a τ x)
-/
theorem ofPermHom_mem_centralizer :
    a.ofPermHom τ ∈ centralizer {g} := by
  rw [mem_centralizer_singleton_iff]
  ext x
  simp only [mul_apply]
  exact ofPermHomFun_commute_zpow_apply a τ x 1

/-- Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g` -/
/-
**Equiv.Perm.Basis.toCentralizer** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.Basis`。
形式化陈述：toCentralizer : range_toPermHom' g ->* centralizer {g} where toFun τ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.Basis.ofPermHom_mem_centralizer`：ofPermHom_mem_centralizer : 
a.ofPermHom τ in centralizer {g}

--- 原说明 ---
Given `a : Equiv.Perm.Basis g`,
we define a right inverse of `Equiv.Perm.OnCycleFactors.toPermHom`,
on `range_toPermHom' g`
-/
noncomputable def toCentralizer :
    range_toPermHom' g →* centralizer {g} where
  toFun τ := ⟨ofPermHom a τ, ofPermHom_mem_centralizer a τ⟩
  map_one' := by simp only [map_one, mk_eq_one]
  map_mul' σ τ := by simp only [map_mul, MulMemClass.mk_mul_mk]
/-
**Equiv.Perm.Basis.toCentralizer_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm.Bas
is`。
形式化陈述：toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = ofPermHomFun a 
τ x
参数：x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCentralizer_apply (x) : (toCentralizer a τ : Perm α) x = ofPermHomFun a τ x := rfl
/-
**Equiv.Perm.Basis.toCentralizer_equivariant** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Pe
rm.Basis`。
形式化陈述：toCentralizer_equivariant : (toCentralizer a τ) • c = (τ : Perm g.cycleFac
torsFinset) c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_commute_zpow_apply`：ofPermHomFun_commute_z
pow_apply (x : α) (j : Int) : ofPermHomFun a τ ((g ^ j) x) = (g ^ j) (ofPermHomF
un a τ x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `zpow_one`：zpow_one (a : G) : a ^ (1 : Int) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Basis.ofPermHomFun_apply_mem_support_cycle_iff`：ofPermHomFun_
apply_mem_support_cycle_iff {x : α} {c : g.cycleFactorsFinset} : ofPermHomFun a 
τ x in ((τ : Perm g.cycleFactorsFinset) c : Per…
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
-/
theorem toCentralizer_equivariant :
    (toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c := by
  simp only [← Subtype.coe_inj, val_centralizer_smul, InvMemClass.coe_inv, mul_inv_eq_iff_eq_mul]
  ext x
  simp only [mul_apply, toCentralizer_apply]
  by_cases hx : x ∈ c.val.support
  · rw [(mem_cycleFactorsFinset_iff.mp c.prop).2 x hx]
    have := ofPermHomFun_commute_zpow_apply a τ x 1
    simp only [zpow_one] at this
    rw [this, ← (mem_cycleFactorsFinset_iff.mp ((τ : Perm g.cycleFactorsFinset) c).prop).2]
    rw [ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx
  · rw [notMem_support.mp hx, eq_comm, ← notMem_support,
      ofPermHomFun_apply_mem_support_cycle_iff]
    exact hx
/-
**Equiv.Perm.Basis.toPermHom_apply_toCentralizer** 是 Mathlib 中的一个定理，位于命名空间 `Equi
v.Perm.Basis`。
形式化陈述：toPermHom_apply_toCentralizer : (toPermHom g) (toCentralizer a τ) = (τ : P
erm g.cycleFactorsFinset)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.toPermHom_apply`：toPermHom_apply (k : centrali
zer {g}) (c : g.cycleFactorsFinset) : (toPermHom g k c) = k • c
· 使用定理 `Equiv.Perm.Basis.toCentralizer_equivariant`：toCentralizer_equivariant : 
(toCentralizer a τ) • c = (τ : Perm g.cycleFactorsFinset) c
-/
theorem toPermHom_apply_toCentralizer :
    (toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset) := by
  apply ext
  intro c
  rw [OnCycleFactors.toPermHom_apply, toCentralizer_equivariant]

end Basis

namespace OnCycleFactors

open Basis Nat

/-
**Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff** 是 Mathlib 中的一个定理，位于命名空间 `E
quiv.Perm.OnCycleFactors`。
形式化陈述：mem_range_toPermHom_iff {τ} : τ in (toPermHom g).range ↔ forall c, #(τ c).
val.support = #c.val.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.coe_toPermHom`：coe_toPermHom (k : centralizer 
{g}) (c : g.cycleFactorsFinset) : (toPermHom g k c : Perm α) = k * c * (k : Perm
 α)⁻¹
· 使用定理 `Equiv.Perm.support_conj`：support_conj : (σ * τ * σ⁻¹).support = τ.suppor
t.map σ.toEmbedding
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Equiv.Perm.Basis.nonempty`：nonempty (g : Perm α) : Nonempty (Basis g)
· 使用定理 `Equiv.Perm.Basis.toPermHom_apply_toCentralizer`：toPermHom_apply_toCentra
lizer : (toPermHom g) (toCentralizer a τ) = (τ : Perm g.cycleFactorsFinset)
-/
theorem mem_range_toPermHom_iff {τ} : τ ∈ (toPermHom g).range ↔
    ∀ c, #(τ c).val.support = #c.val.support := by
  constructor
  · rintro ⟨k, rfl⟩ c
    rw [coe_toPermHom, Equiv.Perm.support_conj]
    apply Finset.card_map
  · obtain ⟨a⟩ := Basis.nonempty g
    exact fun hτ ↦ ⟨toCentralizer a ⟨τ, hτ⟩, toPermHom_apply_toCentralizer a ⟨τ, hτ⟩⟩

/-- Unapplied variant of `Equiv.Perm.mem_range_toPermHom_iff` -/
/-
**Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff'** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.OnCycleFactors`。
形式化陈述：mem_range_toPermHom_iff' {τ} : τ in (toPermHom g).range ↔ (fun (c : g.cycl
eFactorsFinset) => #c.val.support) ∘ τ = fun (c : g.cycleFactorsFinset) => #c.va
l.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff`：mem_range_toPermHom_i
ff {τ} : τ in (toPermHom g).range ↔ forall c, #(τ c).val.support = #c.val.suppor
t
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Unapplied variant of `Equiv.Perm.mem_range_toPermHom_iff`
-/
theorem mem_range_toPermHom_iff' {τ} : τ ∈ (toPermHom g).range ↔
    (fun (c : g.cycleFactorsFinset) ↦ #c.val.support) ∘ τ =
      fun (c : g.cycleFactorsFinset) ↦ #c.val.support := by
  rw [mem_range_toPermHom_iff, funext_iff]
  simp only [Subtype.forall, Function.comp_apply]

/-- Computes the range of `Equiv.Perm.toPermHom g` -/
/-
**Equiv.Perm.OnCycleFactors.range_toPermHom_eq_range_toPermHom'** 是 Mathlib 中的一个
定理，位于命名空间 `Equiv.Perm.OnCycleFactors`。
形式化陈述：range_toPermHom_eq_range_toPermHom' : (toPermHom g).range = range_toPermHo
m' g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff`：mem_range_toPermHom_i
ff {τ} : τ in (toPermHom g).range ↔ forall c, #(τ c).val.support = #c.val.suppor
t
· 使用定理 `Equiv.Perm.OnCycleFactors.mem_range_toPermHom'_iff`：∀ {α : Type u_1} [in
st : DecidableEq α] [inst_1 : Fintype α] {g : Equiv.Perm α} {τ : Equiv.Perm ↥g.c
ycleFactorsFinset},   τ ∈ Equiv.Perm.OnC…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Computes the range of `Equiv.Perm.toPermHom g`
-/
theorem range_toPermHom_eq_range_toPermHom' :
    (toPermHom g).range = range_toPermHom' g := by
  ext τ
  rw [mem_range_toPermHom_iff, mem_range_toPermHom'_iff]

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom** 是 Mathlib 中的一个定理，位于命名空间 `
Equiv.Perm.OnCycleFactors`。
形式化陈述：nat_card_range_toPermHom : Nat.card (toPermHom g).range = ∏ n in g.cycleTy
pe.toFinset, (g.cycleType.count n)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.Perm.OnCycleFactors.mem_range_toPermHom_iff'`：mem_range_toPermHom_
iff' {τ} : τ in (toPermHom g).range ↔ (fun (c : g.cycleFactorsFinset) => #c.val.
support) ∘ τ = fun (c : g.cycleFactorsFi…
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `DomMulAct.stabilizer_card'`：stabilizer_card' : Fintype.card {g : Perm α 
// f ∘ g = f} = ∏ i in Finset.univ.image f, (Fintype.card ({a // f a = i}))!
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nat_card_range_toPermHom :
    Nat.card (toPermHom g).range =
      ∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)! := by
  classical
  set sc := fun (c : g.cycleFactorsFinset) ↦ #c.val.support with hsc
  suffices Fintype.card (toPermHom g).range =
    Fintype.card { k : Perm g.cycleFactorsFinset | sc ∘ k = sc } by
    simp only [Nat.card_eq_fintype_card, this, Set.coe_ofPred, DomMulAct.stabilizer_card', hsc,
      Finset.univ_eq_attach]
    simp_rw [← CycleType.count_def]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    ext n
    simp only [Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists, exists_prop, Multiset.mem_toFinset]
    simp only [cycleType_def, Function.comp_apply, Multiset.mem_map, Finset.mem_val]
  simp only [Fintype.card_eq_nat_card]
  congr
  ext
  rw [mem_range_toPermHom_iff', Set.mem_ofPred_eq]

section Kernel
/- Here, we describe the kernel of `g.OnCycleFactors.toPermHom` -/

variable (g) in
/-- The parametrization of the kernel of `toPermHom` -/
/-
**Equiv.Perm.OnCycleFactors.kerParam** 是 Mathlib 中的一个定义，位于命名空间 `Equiv.Perm.OnCyc
leFactors`。
形式化陈述：kerParam : (Perm (Function.fixedPoints g)) × ((c : g.cycleFactorsFinset) -
> Subgroup.zpowers c.val) ->* Perm α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …

--- 原说明 ---
The parametrization of the kernel of `toPermHom`
-/
def kerParam : (Perm (Function.fixedPoints g)) ×
    ((c : g.cycleFactorsFinset) → Subgroup.zpowers c.val) →* Perm α :=
  MonoidHom.noncommCoprod ofSubtype (Subgroup.noncommPiCoprod g.pairwise_commute_of_mem_zpowers)
    g.commute_ofSubtype_noncommPiCoprod

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.OnCycleFactors.kerParam_apply** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
.OnCycleFactors`。
形式化陈述：kerParam_apply {u : Perm (Function.fixedPoints g)} {v : (c : g.cycleFactor
sFinset) -> Subgroup.zpowers c.val} {x : α} : kerParam g (u, v) x = if hx : g.cy
cleOf x in g.cycleFactorsFinset then (v ⟨g.cycleOf x, hx⟩ : Perm α) x else ofSub
type u x
参数：Function.fixedPoints g；c : g.cycleFactorsFinset。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam.eq_1`：∀ {α : Type u_1} [inst : Decida
bleEq α] [inst_1 : Fintype α] (g : Equiv.Perm α),   Equiv.Perm.OnCycleFactors.ke
rParam g = Equiv.Perm.ofSubty…
· 使用定理 `MonoidHom.noncommCoprod_apply'`：noncommCoprod_apply' (comm) (mn : M × N)
 : (f.noncommCoprod g comm) mn = g mn.2 * f mn.1
· 使用定理 `Equiv.Perm.mul_apply`：mul_apply (f g : Perm α) (x) : (f * g) x = f (g x)
· 使用定理 `Equiv.Perm.ofSubtype_apply_of_not_mem`：ofSubtype_apply_of_not_mem (f : P
erm (Subtype p)) (ha : ¬p a) : ofSubtype f a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.mem_fixedPoints_iff`：mem_fixedPoints_iff {α : Type*} {f : α -> 
α} {x : α} : x in fixedPoints f ↔ f x = x
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Equiv.Perm.mem_support`：mem_support {x : α} : x in f.support ↔ f x != x
· 使用定理 `Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff`：cycleOf_mem_cycleFactorsF
inset_iff {f : Perm α} {x : α} : cycleOf f x in cycleFactorsFinset f ↔ x in f.su
pport
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Subgroup.noncommPiCoprod_apply`：noncommPiCoprod_apply (comm) (u : (i : ι
) -> H i) : Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fu
n i => u i) (fun i _…
· 使用定理 `Finset.noncommProd_erase_mul`：noncommProd_erase_mul [DecidableEq α] (s :
 Finset α) {a : α} (h : a in s) (f : α -> β) (comm) (comm'
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `Equiv.Perm.notMem_support`：notMem_support {x : α} : x ∉ f.support ↔ f x 
= x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Equiv.Perm.mem_support_of_mem_noncommProd_support`：mem_support_of_mem_no
ncommProd_support {α β : Type*} [DecidableEq β] [Fintype β] {s : Finset α} {f : 
α -> Perm β} {comm : (s : Set α).Pairwi…
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subgroup.mem_zpowers_iff`：mem_zpowers_iff {g h : G} : h in zpowers g ↔ e
xists k : Int, g ^ k = h
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
（共 37 条，此处仅展示前 30 条）
-/
theorem kerParam_apply {u : Perm (Function.fixedPoints g)}
    {v : (c : g.cycleFactorsFinset) → Subgroup.zpowers c.val} {x : α} :
    kerParam g (u, v) x =
    if hx : g.cycleOf x ∈ g.cycleFactorsFinset
    then (v ⟨g.cycleOf x, hx⟩ : Perm α) x
    else ofSubtype u x := by
  split_ifs with hx
  · have hx' := hx
    rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support, Ne, ← Function.mem_fixedPoints_iff] at hx'
    rw [kerParam, MonoidHom.noncommCoprod_apply', mul_apply, ofSubtype_apply_of_not_mem u hx',
      noncommPiCoprod_apply, ← Finset.noncommProd_erase_mul _ (Finset.mem_univ ⟨g.cycleOf x, hx⟩),
      mul_apply, ← notMem_support]
    contrapose hx'
    obtain ⟨a, ha1, ha2⟩ := mem_support_of_mem_noncommProd_support hx'
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Ne, Subtype.ext_iff] at ha1
    have key := cycleFactorsFinset_pairwise_disjoint g a.2 hx ha1
    rw [disjoint_iff_disjoint_support, Finset.disjoint_left] at key
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v a).2
    replace ha2 := key (support_zpow_le a.1 k (hk ▸ ha2))
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (v ⟨g.cycleOf x, hx⟩).2
    rwa [← hk, zpow_apply_mem_support, notMem_support, cycleOf_apply_self] at ha2
  · rw [cycleOf_mem_cycleFactorsFinset_iff] at hx
    rw [kerParam, MonoidHom.noncommCoprod_apply, mul_apply, Equiv.apply_eq_iff_eq,
      ← notMem_support]
    contrapose hx
    obtain ⟨a, -, ha⟩ := mem_support_of_mem_noncommProd_support
      (comm := fun a ha b hb h ↦ g.pairwise_commute_of_mem_zpowers h (v a) (v b) (v a).2 (v b).2) hx
    exact support_zpowers_of_mem_cycleFactorsFinset_le (v a) ha
/-
**Equiv.Perm.OnCycleFactors.kerParam_injective** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.
Perm.OnCycleFactors`。
形式化陈述：kerParam_injective (g : Perm α) : Function.Injective (kerParam g)
参数：g : Perm α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam.eq_1`：∀ {α : Type u_1} [inst : Decida
bleEq α] [inst_1 : Fintype α] (g : Equiv.Perm α),   Equiv.Perm.OnCycleFactors.ke
rParam g = Equiv.Perm.ofSubty…
· 使用引理 `MonoidHom.noncommCoprod_injective`：noncommCoprod_injective {M N P : Type
*} [Group M] [Group N] [Group P] (f : M ->* P) (g : N ->* P) (comm : forall (m :
 M) (n : N), Commute (f…
· 使用定理 `Equiv.Perm.ofSubtype_injective`：ofSubtype_injective : Function.Injective
 (ofSubtype : Perm (Subtype p) -> Perm α)
· 使用定理 `MonoidHom.injective_noncommPiCoprod_of_iSupIndep`：injective_noncommPiCop
rod_of_iSupIndep [Fintype ι] {hcomm : Pairwise fun i j : ι => forall (x : H i) (
y : H j), Commute (ϕ i x) (ϕ j y)} (hi…
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Subgroup.range_subtype`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup 
G), H.subtype.range = H
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Subgroup.zpowers_eq_closure`：zpowers_eq_closure (g : G) : zpowers g = cl
osure {g}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Equiv.Perm.disjoint_closure_of_disjoint_support`：disjoint_closure_of_dis
joint_support {S T : Set (Perm α)} (h : forall a in S, forall b in T, _root_.Dis
joint a.support b.support) : _root_.D…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用引理 `Subgroup.subtype_injective`：subtype_injective (s : Subgroup G) : Functio
n.Injective s.subtype
· 使用定理 `Subgroup.noncommPiCoprod_range`：noncommPiCoprod_range {hcomm : Pairwise 
fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y} : (noncommPi
Coprod hcomm).range …
· 使用定理 `Subgroup.closure_eq`：closure_eq : closure (K : Set G) = K
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
· 使用引理 `Equiv.Perm.ofSubtype_support_disjoint`：ofSubtype_support_disjoint {σ : P
erm α} (x : Perm (Function.fixedPoints σ)) : _root_.Disjoint x.ofSubtype.support
 σ.support
-/
theorem kerParam_injective (g : Perm α) : Function.Injective (kerParam g) := by
  rw [kerParam, MonoidHom.noncommCoprod_injective]
  refine ⟨ofSubtype_injective, ?_, ?_⟩
  · apply MonoidHom.injective_noncommPiCoprod_of_iSupIndep
    · intro a
      simp only [range_subtype, ne_eq]
      simp only [zpowers_eq_closure, ← closure_iUnion]
      apply disjoint_closure_of_disjoint_support
      rintro - ⟨-⟩ - ⟨-, ⟨b, rfl⟩, -, ⟨h, rfl⟩, ⟨-⟩⟩
      rw [← disjoint_iff_disjoint_support]
      apply cycleFactorsFinset_pairwise_disjoint g a.2 b.2
      simp only [ne_eq, ← Subtype.ext_iff]
      exact ne_comm.mp h
    · exact fun i ↦ subtype_injective _
  · rw [noncommPiCoprod_range, ← ofSubtype.range.closure_eq]
    simp only [zpowers_eq_closure, ← closure_iUnion]
    apply disjoint_closure_of_disjoint_support
    rintro - ⟨a, rfl⟩ - ⟨-, ⟨b, rfl⟩, ⟨-⟩⟩
    exact (ofSubtype_support_disjoint a).mono_right (mem_cycleFactorsFinset_support_le b.2)
/-
**Equiv.Perm.OnCycleFactors.kerParam_range_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.P
erm.OnCycleFactors`。
形式化陈述：kerParam_range_eq : (kerParam g).range = (toPermHom g).ker.map (Subgroup.s
ubtype _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam.eq_1`：∀ {α : Type u_1} [inst : Decida
bleEq α] [inst_1 : Fintype α] (g : Equiv.Perm α),   Equiv.Perm.OnCycleFactors.ke
rParam g = Equiv.Perm.ofSubty…
· 使用引理 `MonoidHom.noncommCoprod_range`：noncommCoprod_range {M N P : Type*} [Grou
p M] [Group N] [Group P] (f : M ->* P) (g : N ->* P) (comm : forall (m : M) (n :
 N), Commute (f m) …
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `Subgroup.noncommPiCoprod_range`：noncommPiCoprod_range {hcomm : Pairwise 
fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y} : (noncommPi
Coprod hcomm).range …
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Subgroup.mem_centralizer_singleton_iff`：mem_centralizer_singleton_iff {g
 k : G} : k in Subgroup.centralizer {g} ↔ k * g = g * k
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.disjoint_iff_disjoint_support`：disjoint_iff_disjoint_support 
: Disjoint f g ↔ _root_.Disjoint f.support g.support
· 使用引理 `Equiv.Perm.ofSubtype_support_disjoint`：ofSubtype_support_disjoint {σ : P
erm α} (x : Perm (Function.fixedPoints σ)) : _root_.Disjoint x.ofSubtype.support
 σ.support
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Commute.mul_inv_cancel`：∀ {G : Type u_1} [inst : Group G] {a b : G}, Com
mute a b → a * b * a⁻¹ = b
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_support_le`：mem_cycleFactorsFinset_sup
port_le {p f : Perm α} (h : p in cycleFactorsFinset f) : p.support <= f.support
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Equiv.Perm.self_mem_cycle_factors_commute`：self_mem_cycle_factors_commut
e {g c : Perm α} (hc : c in g.cycleFactorsFinset) : Commute c g
· 使用定理 `Equiv.Perm.cycleFactorsFinset_mem_commute'`：cycleFactorsFinset_mem_commu
te' {g1 g2 : Perm α} (h1 : g1 in f.cycleFactorsFinset) (h2 : g2 in f.cycleFactor
sFinset) : Commute g1 g2
· 使用定理 `Equiv.Perm.apply_mem_fixedPoints_iff_mem_of_mem_centralizer`：apply_mem_f
ixedPoints_iff_mem_of_mem_centralizer {g p : Perm α} (hp : p in Subgroup.central
izer {g}) {x : α} : p x in Function.fixedPoints g…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_apply`：kerParam_apply {u : Perm (Func
tion.fixedPoints g)} {v : (c : g.cycleFactorsFinset) -> Subgroup.zpowers c.val} 
{x : α} : kerParam g (u, v) x …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
（共 38 条，此处仅展示前 30 条）
-/
theorem kerParam_range_eq :
    (kerParam g).range = (toPermHom g).ker.map (Subgroup.subtype _) := by
  apply le_antisymm
  · rw [kerParam, MonoidHom.noncommCoprod_range, sup_le_iff, noncommPiCoprod_range, iSup_le_iff]
    simp only [zpowers_le]
    constructor
    · rintro - ⟨a, rfl⟩
      refine ⟨⟨ofSubtype a, ?_⟩, ?_, rfl⟩
      · rw [mem_centralizer_singleton_iff]
        exact Disjoint.commute (disjoint_iff_disjoint_support.mpr (ofSubtype_support_disjoint a))
      · exact Perm.ext fun x ↦ Subtype.ext (disjoint_iff_disjoint_support.mpr
          ((ofSubtype_support_disjoint a).mono_right
            (mem_cycleFactorsFinset_support_le x.2))).commute.mul_inv_cancel
    · intro i
      refine ⟨⟨i, mem_centralizer_singleton_iff.mpr (self_mem_cycle_factors_commute i.2)⟩, ?_, rfl⟩
      exact Perm.ext fun x ↦ Subtype.ext (cycleFactorsFinset_mem_commute' g i.2 x.2).mul_inv_cancel
  · rintro - ⟨p, hp, rfl⟩
    simp only [coe_subtype]
    set u : Perm (Function.fixedPoints g) :=
      subtypePerm p (fun x ↦ apply_mem_fixedPoints_iff_mem_of_mem_centralizer p.2)
    simp only [SetLike.mem_coe, mem_ker_toPermHom_iff, IsCycle.forall_commute_iff] at hp
    set v : (c : g.cycleFactorsFinset) → (Subgroup.zpowers c.val) :=
      fun c => ⟨ofSubtype
          (p.1.subtypePerm (Classical.choose (hp c.val c.prop))),
            Classical.choose_spec (hp c.val c.prop)⟩
    use (u, v)
    ext x
    rw [kerParam_apply]
    split_ifs with hx
    · rw [cycleOf_mem_cycleFactorsFinset_iff, mem_support] at hx
      rw [ofSubtype_apply_of_mem, subtypePerm_apply]
      rwa [mem_support, cycleOf_apply_self, ne_eq]
    · rw [cycleOf_mem_cycleFactorsFinset_iff, notMem_support] at hx
      rwa [ofSubtype_apply_of_mem, subtypePerm_apply]
/-
**Equiv.Perm.OnCycleFactors.kerParam_range_le_centralizer** 是 Mathlib 中的一个定理，位于命
名空间 `Equiv.Perm.OnCycleFactors`。
形式化陈述：kerParam_range_le_centralizer : (kerParam g).range <= Subgroup.centralizer
 {g}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_eq`：kerParam_range_eq : (kerPar
am g).range = (toPermHom g).ker.map (Subgroup.subtype _)
· 使用定理 `Subgroup.map_subtype_le`：map_subtype_le {H : Subgroup G} (K : Subgroup H
) : K.map H.subtype <= H
-/
theorem kerParam_range_le_centralizer :
    (kerParam g).range ≤ Subgroup.centralizer {g} := by
  rw [kerParam_range_eq]
  exact map_subtype_le (toPermHom g).ker
/-
**Equiv.Perm.OnCycleFactors.kerParam_range_card** 是 Mathlib 中的一个定理，位于命名空间 `Equiv
.Perm.OnCycleFactors`。
形式化陈述：kerParam_range_card (g : Equiv.Perm α) : Fintype.card (kerParam g).range =
 (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod
参数：g : Equiv.Perm α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_coeSort_range`：∀ {G : Type u_1} [inst : Group G] {N : Type 
u_3} [inst_1 : Group N] [inst_2 : Fintype G] [inst_3 : DecidableEq N]   {f : G →
* N}, Function.I…
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_injective`：kerParam_injective (g : Pe
rm α) : Function.Injective (kerParam g)
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!
· 使用定理 `Fintype.card_pi`：∀ {ι : Type u_4} {α : ι → Type u_6} [inst : DecidableEq
 ι] [inst_1 : Fintype ι] [inst_2 : (i : ι) → Fintype (α i)],   Fintype.card ((i 
: ι) …
· 使用定理 `Equiv.Perm.card_fixedPoints`：card_fixedPoints (σ : Equiv.Perm α) : Finty
pe.card (Function.fixedPoints σ) = Fintype.card α - σ.cycleType.sum
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用引理 `Finset.prod_attach`：prod_attach (s : Finset ι) (f : ι -> M) : ∏ x in s.a
ttach, f x = ∏ x in s, f x
· 使用定理 `Equiv.Perm.cycleType.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 :
 DecidableEq α] (σ : Equiv.Perm α),   σ.cycleType = Multiset.map (Finset.card ∘ 
Equiv.Perm.supp…
· 使用引理 `Finset.prod_map_val`：prod_map_val [CommMonoid M] (s : Finset ι) (f : ι -
> M) : (s.1.map f).prod = ∏ a in s, f a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Fintype.card_zpowers`：Fintype.card_zpowers : Fintype.card (zpowers x) = 
orderOf x
· 使用定理 `Equiv.Perm.IsCycle.orderOf`：∀ {α : Type u_2} {f : Equiv.Perm α} [inst : 
DecidableEq α] [inst_1 : Fintype α], f.IsCycle → orderOf f = f.support.card
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Equiv.Perm.mem_cycleFactorsFinset_iff`：mem_cycleFactorsFinset_iff {f p :
 Perm α} : p in cycleFactorsFinset f ↔ p.IsCycle ∧ forall a in p.support, p a = 
f a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
theorem kerParam_range_card (g : Equiv.Perm α) :
    Fintype.card (kerParam g).range = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod := by
  rw [Fintype.card_coeSort_range (kerParam_injective g)]
  rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_pi, card_fixedPoints]
  apply congr_arg
  rw [Finset.univ_eq_attach, g.cycleFactorsFinset.prod_attach (fun i ↦ Fintype.card (zpowers i)),
    cycleType, Finset.prod_map_val]
  refine Finset.prod_congr rfl (fun x hx ↦ ?_)
  rw [Fintype.card_zpowers, (mem_cycleFactorsFinset_iff.mp hx).1.orderOf, Function.comp_apply]

end Kernel

section Sign

open Function

variable {a : Type*} (g : Perm α) (k : Perm (fixedPoints g))
    (v : (c : g.cycleFactorsFinset) → Subgroup.zpowers (c : Perm α))

set_option backward.isDefEq.respectTransparency false in
/-
**Equiv.Perm.OnCycleFactors.sign_kerParam_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 
`Equiv.Perm.OnCycleFactors`。
形式化陈述：sign_kerParam_apply_apply : sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign 
(v c).val
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam.eq_1`：∀ {α : Type u_1} [inst : Decida
bleEq α] [inst_1 : Fintype α] (g : Equiv.Perm α),   Equiv.Perm.OnCycleFactors.ke
rParam g = Equiv.Perm.ofSubty…
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prod.fst_mul_snd`：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N
) : (p.fst, 1) * (1, p.snd) = p
· 使用定理 `Prod.mk_mul_mk`：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) 
= (a₁ * a₂, b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Equiv.Perm.sign_ofSubtype`：sign_ofSubtype {p : α -> Prop} [DecidablePred
 p] [Fintype (Subtype p)] (f : Equiv.Perm (Subtype p)) : sign (ofSubtype f) = si
gn f
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `mul_right_inj`：mul_right_inj (a : G) {b c : G} : a * b = a * c ↔ b = c
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `Subgroup.commute_subtype_of_commute`：commute_subtype_of_commute (hcomm :
 Pairwise fun i j : ι => forall x y : G, x in H i -> y in H j -> Commute x y) (i
 j : ι) (hne : i != j) : …
· 使用定理 `Subgroup.noncommPiCoprod.eq_1`：∀ {G : Type u_1} [inst : Group G] {ι : Ty
pe u_2} {H : ι → Subgroup G} [inst_1 : Fintype ι]   (hcomm : Pairwise fun i j =>
 ∀ (x y : G), x ∈ H…
· 使用定理 `Pairwise.mono`：Pairwise.mono (h : t subseteq s) (hs : s.Pairwise r) : t.
Pairwise r
· 使用定理 `forall_imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∀ (a : α), p a) → ∀ (a : α), q a
· 使用定理 `MonoidHom.comp_noncommPiCoprod`：comp_noncommPiCoprod {P : Type*} [Monoid
 P] {f : M ->* P} (hcomm' : Pairwise fun i j => forall x y, Commute (f.comp (ϕ i
) x) (f.comp (ϕ j) y…
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
· 使用引理 `MonoidHom.noncommPiCoprod_apply`：noncommPiCoprod_apply (h : (i : ι) -> N
 i) : MonoidHom.noncommPiCoprod ϕ hcomm h = Finset.noncommProd Finset.univ (fun 
i => ϕ i (h i)) (Pair…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Finset.noncommProd_eq_prod`：noncommProd_eq_prod {β : Type*} [CommMonoid 
β] (s : Finset α) (f : α -> β) : (noncommProd s f fun _ _ _ _ _ => Commute.all _
 _) = s.prod f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
（共 31 条，此处仅展示前 30 条）
-/
theorem sign_kerParam_apply_apply :
    sign (kerParam g ⟨k, v⟩) = sign k * ∏ c, sign (v c).val := by
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, map_mul, sign_ofSubtype, Finset.univ_eq_attach, mul_right_inj, ← MonoidHom.comp_apply,
    Subgroup.noncommPiCoprod, MonoidHom.comp_noncommPiCoprod _, MonoidHom.noncommPiCoprod_apply,
    Finset.univ_eq_attach, Finset.noncommProd_eq_prod]
  simp
/-
**Equiv.Perm.OnCycleFactors.cycleType_kerParam_apply_apply** 是 Mathlib 中的一个定理，位于
命名空间 `Equiv.Perm.OnCycleFactors`。
形式化陈述：cycleType_kerParam_apply_apply : cycleType (kerParam g ⟨k, v⟩) = cycleType
 k + ∑ c, (v c).val.cycleType
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.Disjoint.zpow_disjoint_zpow`：∀ {α : Type u_1} {σ τ : Equiv.Pe
rm α}, σ.Disjoint τ → ∀ (m n : ℤ), (σ ^ m).Disjoint (τ ^ n)
· 使用定理 `Equiv.Perm.cycleFactorsFinset_pairwise_disjoint`：cycleFactorsFinset_pair
wise_disjoint : (cycleFactorsFinset f : Set (Perm α)).Pairwise Disjoint
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用引理 `Equiv.Perm.pairwise_commute_of_mem_zpowers`：pairwise_commute_of_mem_zpow
ers : Pairwise fun (i j : f.cycleFactorsFinset) => forall (x y : Perm α), x in S
ubgroup.zpowers ↑i -> y in Subgr…
· 使用引理 `Equiv.Perm.commute_ofSubtype_noncommPiCoprod`：commute_ofSubtype_noncommP
iCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFactors
Finset }) -> (Subgroup.zpowers (c …
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam.eq_1`：∀ {α : Type u_1} [inst : Decida
bleEq α] [inst_1 : Fintype α] (g : Equiv.Perm α),   Equiv.Perm.OnCycleFactors.ke
rParam g = Equiv.Perm.ofSubty…
· 使用定理 `MonoidHom.noncommCoprod_apply`：∀ {M : Type u_1} {N : Type u_2} {P : Type
 u_3} [inst : MulOneClass M] [inst_1 : MulOneClass N] [inst_2 : Monoid P]   (f :
 M →* P) (g : N →* …
· 使用定理 `Prod.fst_mul_snd`：fst_mul_snd [MulOneClass M] [MulOneClass N] (p : M × N
) : (p.fst, 1) * (1, p.snd) = p
· 使用定理 `Prod.mk_mul_mk`：mk_mul_mk (a₁ a₂ : M) (b₁ b₂ : N) : (a₁, b₁) * (a₂, b₂) 
= (a₁ * a₂, b₁ * b₂)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Equiv.Perm.Disjoint.cycleType_mul`：∀ {α : Type u_1} [inst : Fintype α] [
inst_1 : DecidableEq α] {σ τ : Equiv.Perm α},   σ.Disjoint τ → (σ * τ).cycleType
 = σ.cycleType + τ.cycl…
· 使用引理 `Equiv.Perm.disjoint_ofSubtype_noncommPiCoprod`：disjoint_ofSubtype_noncom
mPiCoprod (u : Perm (Function.fixedPoints f)) (v : (c : { x // x in f.cycleFacto
rsFinset }) -> (Subgroup.zpowers (c…
· 使用定理 `Subgroup.noncommPiCoprod_apply`：noncommPiCoprod_apply (comm) (u : (i : ι
) -> H i) : Subgroup.noncommPiCoprod comm u = Finset.noncommProd Finset.univ (fu
n i => u i) (fun i _…
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Equiv.Perm.Disjoint.commute`：∀ {α : Type u_1} {f g : Equiv.Perm α}, f.Di
sjoint g → Commute f g
· 使用定理 `Equiv.Perm.Disjoint.cycleType_noncommProd`：∀ {α : Type u_1} [inst : Fint
ype α] [inst_1 : DecidableEq α] {ι : Type u_2} {k : ι → Equiv.Perm α} {s : Finse
t ι}   (hs : (↑s).Pairwise fun …
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Equiv.Perm.cycleType_ofSubtype`：cycleType_ofSubtype {p : α -> Prop} [Dec
idablePred p] [Fintype (Subtype p)] {g : Perm (Subtype p)} : cycleType (ofSubtyp
e g) = cycleType g
-/
theorem cycleType_kerParam_apply_apply :
    cycleType (kerParam g ⟨k, v⟩) = cycleType k + ∑ c, (v c).val.cycleType := by
  let U := SetLike.coe (Finset.univ : Finset { x // x ∈ g.cycleFactorsFinset })
  have hU : U.Pairwise fun i j ↦ (v i).val.Disjoint (v j).val := fun c _ d _ h ↦ by
    obtain ⟨m, hm⟩ := (v c).prop
    obtain ⟨n, hn⟩ := (v d).prop
    simp only [← hm, ← hn]
    apply Disjoint.zpow_disjoint_zpow
    apply cycleFactorsFinset_pairwise_disjoint g c.prop d.prop
    exact Subtype.coe_ne_coe.mpr h
  rw [kerParam, MonoidHom.noncommCoprod_apply, ← Prod.fst_mul_snd ⟨k, v⟩, Prod.mk_mul_mk, mul_one,
    one_mul, Finset.univ_eq_attach,
    Disjoint.cycleType_mul (disjoint_ofSubtype_noncommPiCoprod g k v),
    Subgroup.noncommPiCoprod_apply, Disjoint.cycleType_noncommProd hU, Finset.univ_eq_attach]
  exact congr_arg₂ _ cycleType_ofSubtype rfl

end Sign

end OnCycleFactors

open Nat

variable (g : Perm α)

-- Should one parenthesize the product ?
/-- Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleType` -/
/-
**Equiv.Perm.nat_card_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：nat_card_centralizer : Nat.card (centralizer {g}) = (Fintype.card α - g.cy
cleType.sum)! * g.cycleType.prod * (∏ n in g.cycleType.toFinset, (g.cycleType.co
unt n)!)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.card_mul_index`：card_mul_index : Nat.card H * H.index = Nat.car
d G
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `Equiv.Perm.OnCycleFactors.nat_card_range_toPermHom`：nat_card_range_toPer
mHom : Nat.card (toPermHom g).range = ∏ n in g.cycleType.toFinset, (g.cycleType.
count n)!
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_card`：kerParam_range_card (g : 
Equiv.Perm α) : Fintype.card (kerParam g).range = (Fintype.card α - g.cycleType.
sum)! * g.cycleType.prod
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Equiv.Perm.OnCycleFactors.kerParam_range_eq`：kerParam_range_eq : (kerPar
am g).range = (toPermHom g).ker.map (Subgroup.subtype _)
· 使用定理 `Subgroup.card_subtype`：card_subtype (K : Subgroup G) (L : Subgroup K) : 
Nat.card (map K.subtype L) = Nat.card L

--- 原说明 ---
Cardinality of the centralizer in `Equiv.Perm α` of a permutation given `cycleTy
pe`
-/
theorem nat_card_centralizer :
    Nat.card (centralizer {g}) =
      (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod *
        (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!) := by
  rw [← (toPermHom g).ker.card_mul_index, index_ker, nat_card_range_toPermHom,
    ← kerParam_range_card, ← Nat.card_eq_fintype_card, kerParam_range_eq, card_subtype]
/-
**Equiv.Perm.card_isConj_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_isConj_mul_eq : Nat.card {h : Perm α | IsConj g h} * ((Fintype.card α
 - g.cycleType.sum)! * g.cycleType.prod * (∏ n in g.cycleType.toFinset, (g.cycle
Type.count n)!)) = (Fintype.card α)!
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.nat_card_centralizer`：nat_card_centralizer : Nat.card (centra
lizer {g}) = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod * (∏ n in g.
cycleType.toFinset, (…
· 使用引理 `Subgroup.nat_card_centralizer_nat_card_stabilizer`：nat_card_centralizer_
nat_card_stabilizer (g : G) : Nat.card (centralizer {g}) = Nat.card (MulAction.s
tabilizer (ConjAct G) g)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `ConjAct.card`：card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card
 G
· 使用定理 `Fintype.card_perm`：Fintype.card_perm [Fintype α] : Fintype.card (Perm α)
 = (Fintype.card α)!
· 使用定理 `MulAction.card_orbit_mul_card_stabilizer_eq_card_group`：card_orbit_mul_c
ard_stabilizer_eq_card_group (b : X) [Fintype G] [Fintype <| orbit G b] [Fintype
 <| stabilizer G b] : Fintype.card (orbit G …
-/
theorem card_isConj_mul_eq :
    Nat.card {h : Perm α | IsConj g h} *
      ((Fintype.card α - g.cycleType.sum)! *
      g.cycleType.prod *
      (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) =
    (Fintype.card α)! := by
  classical
  rw [Nat.card_eq_fintype_card, ← nat_card_centralizer g]
  rw [Subgroup.nat_card_centralizer_nat_card_stabilizer, Nat.card_eq_fintype_card]
  convert! MulAction.card_orbit_mul_card_stabilizer_eq_card_group (ConjAct (Perm α)) g
  · ext h
    simp only [Set.mem_ofPred_eq, ConjAct.mem_orbit_conjAct, isConj_comm]
  · rw [ConjAct.card, Fintype.card_perm]

/-- Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType` -/
/-
**Equiv.Perm.card_isConj_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_isConj_eq : Nat.card {h : Perm α | IsConj g h} = (Fintype.card α)! / 
((Fintype.card α - g.cycleType.sum)! * g.cycleType.prod * (∏ n in g.cycleType.to
Finset, (g.cycleType.count n)!))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.card_isConj_mul_eq`：card_isConj_mul_eq : Nat.card {h : Perm α
 | IsConj g h} * ((Fintype.card α - g.cycleType.sum)! * g.cycleType.prod * (∏ n 
in g.cycleType.toFi…
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用定理 `Equiv.Perm.nat_card_centralizer`：nat_card_centralizer : Nat.card (centra
lizer {g}) = (Fintype.card α - g.cycleType.sum)! * g.cycleType.prod * (∏ n in g.
cycleType.toFinset, (…
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `One.instNonempty`：∀ {α : Type u} [One α], Nonempty α
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
Cardinality of a conjugacy class in `Equiv.Perm α` of a given `cycleType`
-/
theorem card_isConj_eq :
    Nat.card {h : Perm α | IsConj g h} =
      (Fintype.card α)! /
        ((Fintype.card α - g.cycleType.sum)! *
          g.cycleType.prod *
          (∏ n ∈ g.cycleType.toFinset, (g.cycleType.count n)!)) := by
  rw [← card_isConj_mul_eq g, Nat.div_eq_of_eq_mul_left _]
  · rfl
  -- This is the cardinal of the centralizer
  · rw [← nat_card_centralizer g]
    apply Nat.card_pos

variable (α)
/-
**Equiv.Perm.card_of_cycleType_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm
`。
形式化陈述：card_of_cycleType_eq_zero_iff {m : Multiset Nat} : #({g | g.cycleType = m}
 : Finset (Perm α)) = 0 ↔ ¬ ((m.sum <= Fintype.card α ∧ forall a in m, 2 <= a))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.Perm.exists_with_cycleType_iff`：Equiv.Perm.exists_with_cycleType_i
ff {m : Multiset Nat} : (exists g : Equiv.Perm α, g.cycleType = m) ↔ (m.sum <= F
intype.card α ∧ forall a i…
· 使用定理 `not_exists`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, p x) ↔ ∀ (x : α), ¬p
 x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem card_of_cycleType_eq_zero_iff {m : Multiset ℕ} :
    #({g | g.cycleType = m} : Finset (Perm α)) = 0
      ↔ ¬ ((m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a)) := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff,
    ← exists_with_cycleType_iff, not_exists]
  simp
/-
**Equiv.Perm.card_of_cycleType_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_of_cycleType_mul_eq (m : Multiset Nat) : #({g | g.cycleType = m} : Fi
nset (Perm α)) * ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.co
unt n)!)) = if (m.sum <= Fintype.card α ∧ forall a in m, 2 <= a) then (Fintype.c
ard α)! else 0
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.exists_with_cycleType_iff`：Equiv.Perm.exists_with_cycleType_i
ff {m : Multiset Nat} : (exists g : Equiv.Perm α, g.cycleType = m) ↔ (m.sum <= F
intype.card α ∧ forall a i…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `isConj_comm`：isConj_comm {g h : α} : IsConj g h ↔ IsConj h g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Equiv.Perm.card_isConj_mul_eq`：card_isConj_mul_eq : Nat.card {h : Perm α
 | IsConj g h} * ((Fintype.card α - g.cycleType.sum)! * g.cycleType.prod * (∏ n 
in g.cycleType.toFi…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Equiv.Perm.card_of_cycleType_eq_zero_iff`：card_of_cycleType_eq_zero_iff 
{m : Multiset Nat} : #({g | g.cycleType = m} : Finset (Perm α)) = 0 ↔ ¬ ((m.sum 
<= Fintype.card α ∧ forall a i…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem card_of_cycleType_mul_eq (m : Multiset ℕ) :
    #({g | g.cycleType = m} : Finset (Perm α)) *
      ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!)) =
      if (m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a) then (Fintype.card α)! else 0 := by
  split_ifs with hm
  · -- nonempty case
    classical
    obtain ⟨g, rfl⟩ := (exists_with_cycleType_iff α).mpr hm
    convert! card_isConj_mul_eq g
    simp_rw [Set.coe_ofPred, Nat.card_eq_fintype_card, ← Fintype.card_coe, Finset.mem_filter,
      Finset.mem_univ, true_and, ← isConj_iff_cycleType_eq, isConj_comm (g := g)]
  · -- empty case
    rw [(card_of_cycleType_eq_zero_iff α).mpr hm, zero_mul]

/-- Cardinality of the `Finset` of `Equiv.Perm α` of given `cycleType` -/
/-
**Equiv.Perm.card_of_cycleType** 是 Mathlib 中的一个定理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_of_cycleType (m : Multiset Nat) : #({g | g.cycleType = m} : Finset (P
erm α)) = if m.sum <= Fintype.card α ∧ forall a in m, 2 <= a then (Fintype.card 
α)! / ((Fintype.card α - m.sum)! * m.prod * (∏ n in m.toFinset, (m.count n)!)) e
lse 0
参数：m : Multiset Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Nat.div_eq_of_eq_mul_left`：∀ {n m k : ℕ}, 0 < n → m = k * n → m / n = k
· 使用引理 `Multiset.prod_pos`：prod_pos {s : Multiset R} (h : forall a in s, 0 < a) 
: 0 < s.prod
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用引理 `Finset.prod_pos`：prod_pos (h0 : forall i in s, 0 < f i) : 0 < ∏ i in s, 
f i
· 使用定理 `Equiv.Perm.card_of_cycleType_mul_eq`：card_of_cycleType_mul_eq (m : Multi
set Nat) : #({g | g.cycleType = m} : Finset (Perm α)) * ((Fintype.card α - m.sum
)! * m.prod * (∏ n in m.t…
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.card_of_cycleType_eq_zero_iff`：card_of_cycleType_eq_zero_iff 
{m : Multiset Nat} : #({g | g.cycleType = m} : Finset (Perm α)) = 0 ↔ ¬ ((m.sum 
<= Fintype.card α ∧ forall a i…

--- 原说明 ---
Cardinality of the `Finset` of `Equiv.Perm α` of given `cycleType`
-/
theorem card_of_cycleType (m : Multiset ℕ) :
    #({g | g.cycleType = m} : Finset (Perm α)) =
      if m.sum ≤ Fintype.card α ∧ ∀ a ∈ m, 2 ≤ a then
        (Fintype.card α)! /
          ((Fintype.card α - m.sum)! * m.prod * (∏ n ∈ m.toFinset, (m.count n)!))
      else 0 := by
  split_ifs with hm
  · -- nonempty case
    apply symm
    apply Nat.div_eq_of_eq_mul_left
    · have : 0 < m.prod := Multiset.prod_pos <| fun a ha => zero_lt_two.trans_le (hm.2 a ha)
      positivity
    rw [card_of_cycleType_mul_eq, if_pos hm]
  · -- empty case
    exact (card_of_cycleType_eq_zero_iff α).mpr hm

open Fintype in
variable {α} in
/-- The number of cycles of given length -/
/-
**Equiv.Perm.card_of_cycleType_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Equiv.Perm`。
形式化陈述：card_of_cycleType_singleton {n : Nat} (hn' : 2 <= n) (hα : n <= card α) : 
#({g | g.cycleType = {n}} : Finset (Perm α)) = (n - 1)! * (choose (card α) n)
参数：hn' : 2 <= n；hα : n <= card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Nat.mul_factorial_pred`：mul_factorial_pred (hn : n != 0) : n * (n - 1)! 
= n !
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.mul_left_inj`：∀ {a b c : ℕ}, a ≠ 0 → (b * a = c * a ↔ b = c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Nat.choose_mul_factorial_mul_factorial`：choose_mul_factorial_mul_factori
al : forall {n k}, k <= n -> choose n k * k ! * (n - k)! = n ! | 0, _, hk => by 
simp [Nat.eq_zero_of_le_zero…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.sum_singleton`：∀ {M : Type u_3} [inst : AddCommMonoid M] (a : M
), {a}.sum = a
· 使用定理 `Multiset.prod_singleton`：prod_singleton (a : M) : prod {a} = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_and`：ite_and : ite (P ∧ Q) a b = ite P (ite Q a b) b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Equiv.Perm.card_of_cycleType_mul_eq`：card_of_cycleType_mul_eq (m : Multi
set Nat) : #({g | g.cycleType = m} : Finset (Perm α)) * ((Fintype.card α - m.sum
)! * m.prod * (∏ n in m.t…

--- 原说明 ---
The number of cycles of given length
-/
lemma card_of_cycleType_singleton {n : ℕ} (hn' : 2 ≤ n) (hα : n ≤ card α) :
    #({g | g.cycleType = {n}} : Finset (Perm α)) = (n - 1)! * (choose (card α) n) := by
  have hn₀ : n ≠ 0 := by lia
  have aux : n ! = (n - 1)! * n := by rw [mul_comm, mul_factorial_pred hn₀]
  rw [mul_comm, ← Nat.mul_left_inj hn₀, mul_assoc, ← aux, ← Nat.mul_left_inj (factorial_ne_zero _),
    Nat.choose_mul_factorial_mul_factorial hα, mul_assoc]
  simpa [ite_and, if_pos hα, if_pos hn', mul_comm _ n, mul_assoc]
    using card_of_cycleType_mul_eq α {n}

end Equiv.Perm

