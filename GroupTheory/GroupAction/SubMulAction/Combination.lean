/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.GroupTheory.SpecificGroups.Alternating.MaximalSubgroups

/-! # Combinations

Combinations in a type are finite subsets of given cardinality.
This file provides some API for handling them in the context of a group action.

* `Set.powersetCard.subMulAction`:
  When a group `G` acts on `α`, the `SubMulAction` of `G` on `powersetCard α n`.

This induces a `MulAction G (powersetCard α n)` instance. Then:

* `Set.powerSetCard.mulActionHom_of_embedding`:
  the equivariant map from `Fin n ↪ α` to `powersetCard α n`.

* `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`
  shows the pretransitivity of that action if the action of `G` on `α` is `n`-pretransitive.

* `Set.powersetCard.isPretransitive` shows that `Equiv.Perm α`
  acts pretransitively on `powersetCard α n`, for all `n`.

* `Set.powersetCard.compl`: Given an equality `m + n = Fintype.card α`,
  the complement of an `n`-combination, as an `m`-combination.
  This map is an equivariant map with respect to a group action on `α`.

* `Set.powersetCard.mulActionHom_singleton`:
  The obvious map from `α` to `powersetCard α 1`, as an equivariant map.

-/

@[expose] public section

namespace Set.powersetCard

open scoped Pointwise

open MulAction Finset Set Equiv Equiv.Perm

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]
  {n : ℕ} {s t : powersetCard α n}

section

variable [DecidableEq α]

variable (α n) in
/-- `Set.powersetCard α n` as a `SubMulAction` of `Finset α`. -/
@[to_additive /--`Set.powersetCard α n` as a `SubAddAction` of `Finsetα`.-/]
/-
**Set.powersetCard.subMulAction** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCard`。
形式化陈述：subMulAction : SubMulAction G (Finset α) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Set.powersetCard α n` as a `SubMulAction` of `Finset α`.
-/
def subMulAction : SubMulAction G (Finset α) where
  carrier := powersetCard α n
  smul_mem' g s := (card_smul_finset g s).trans

@[to_additive]
/-
**Set.powersetCard.** 是 Mathlib 中的一个实例，位于命名空间 `Set.powersetCard`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction G (powersetCard α n) :=
  inferInstanceAs <| MulAction G (subMulAction G α n)

variable {G}

@[to_additive (attr := simp)]
/-
**Set.powersetCard.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：coe_smul {n : Nat} {g : G} {s : powersetCard α n} : ((g • s : powersetCard
 α n) : Finset α) = g • s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubMulAction.val_smul`：val_smul (r : R) (x : p) : (↑(r • x) : M) = r • (
x : M)
-/
theorem coe_smul {n : ℕ} {g : G} {s : powersetCard α n} :
    ((g • s : powersetCard α n) : Finset α) = g • s :=
  SubMulAction.val_smul (p := subMulAction G α n) g s

@[to_additive addAction_stabilizer_coe]
/-
**Set.powersetCard.stabilizer_coe** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：stabilizer_coe {n : Nat} (s : powersetCard α n) : stabilizer G s = stabili
zer G (s : Set α)
参数：s : powersetCard α n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.powersetCard.coe_smul`：coe_smul {n : Nat} {g : G} {s : powersetCard 
α n} : ((g • s : powersetCard α n) : Finset α) = g • s
· 使用引理 `Finset.coe_smul_finset`：coe_smul_finset (a : α) (s : Finset β) : ↑(a • s
) = a • (↑s : Set β)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stabilizer_coe {n : ℕ} (s : powersetCard α n) :
    stabilizer G s = stabilizer G (s : Set α) := by
  ext g
  simp [mem_stabilizer_iff, ← Subtype.coe_inj, ← coe_inj]
/-
**Set.powersetCard.addAction_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCar
d`。
形式化陈述：addAction_faithful {G : Type*} [AddGroup G] [AddAction G α] {n : Nat} (hn 
: 1 <= n) (hα : n < ENat.card α) {g : G} : AddAction.toPerm g = (1 : Perm (power
setCard α n)) ↔ AddAction.toPerm g = (1 : Perm α)
参数：hn : 1 <= n；hα : n < ENat.card α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : AddGroup
 α] [inst_1 : AddAction α β] (a : α) (x : β),   (AddAction.toPerm a) x = a +ᵥ x
· 使用定理 `Set.powersetCard.exists_mem_notMem`：exists_mem_notMem (hn : 1 <= n) (hα 
: n < ENat.card α) {a b : α} (hab : a != b) : exists s : powersetCard α n, a in 
s ∧ b ∉ s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.ext_iff`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g ↔ ∀ (x :
 α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.Perm.coe_one`：∀ {α : Type u_4}, ⇑1 = id
· 使用定理 `Set.powersetCard.coe_vadd`：∀ {G : Type u_1} [inst : AddGroup G] {α : Typ
e u_2} [inst_1 : AddAction G α] [inst_2 : DecidableEq α] {n : ℕ} {g : G}   {s : 
↑(Set.powersetC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem addAction_faithful {G : Type*} [AddGroup G] [AddAction G α] {n : ℕ}
    (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    AddAction.toPerm g = (1 : Perm (powersetCard α n)) ↔ AddAction.toPerm g = (1 : Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g +ᵥ a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose has'
    simp only [AddAction.toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa [← mem_coe_iff]
  · simp only [Equiv.ext_iff, AddAction.toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_vadd_finset, h]

/-- If an additive group `G` acts faithfully on `α`,
then it acts faithfully on `powersetCard α n`,
provided `1 ≤ n < ENat.card α`. -/
/-
**Set.powersetCard.faithfulVAdd** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：faithfulVAdd {G : Type*} [AddGroup G] [AddAction G α] {n : Nat} (hn : 1 <=
 n) (hα : n < ENat.card α) [FaithfulVAdd G α] : FaithfulVAdd G (powersetCard α n
)
参数：hn : 1 <= n；hα : n < ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `faithfulVAdd_iff`：∀ {G : Type u_2} {α : Type u_3} [inst : AddGroup G] [i
nst_1 : AddAction G α],   FaithfulVAdd G α ↔ ∀ (g : G), (∀ (a : α), g +ᵥ a = a) 
→ g = …
· 使用定理 `AddAction.toPerm_injective`：∀ {α : Type u_5} {β : Type u_6} [inst : AddG
roup α] [inst_1 : AddAction α β] [FaithfulVAdd α β],   Function.Injective AddAct
ion.toPerm
· 使用定理 `AddAction.toPerm_zero`：AddAction.toPerm_zero : (AddAction.toPerm (0 : G)
) = (1 : Equiv.Perm α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powersetCard.addAction_faithful`：addAction_faithful {G : Type*} [Add
Group G] [AddAction G α] {n : Nat} (hn : 1 <= n) (hα : n < ENat.card α) {g : G} 
: AddAction.toPerm g = (1…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x

--- 原说明 ---
If an additive group `G` acts faithfully on `α`,
then it acts faithfully on `powersetCard α n`,
provided `1 ≤ n < ENat.card α`.
-/
theorem faithfulVAdd {G : Type*} [AddGroup G] [AddAction G α] {n : ℕ}
    (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulVAdd G α] :
    FaithfulVAdd G (powersetCard α n) := by
  rw [faithfulVAdd_iff]
  intro g hg
  apply AddAction.toPerm_injective (α := G) (β := α)
  rw [AddAction.toPerm_zero, ← addAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg
/-
**Set.powersetCard.mulAction_faithful** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCar
d`。
形式化陈述：mulAction_faithful (hn : 1 <= n) (hα : n < ENat.card α) {g : G} : toPerm g
 = (1 : Perm (powersetCard α n)) ↔ toPerm g = (1 : Perm α)
参数：hn : 1 <= n；hα : n < ENat.card α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `Set.powersetCard.exists_mem_notMem`：exists_mem_notMem (hn : 1 <= n) (hα 
: n < ENat.card α) {a b : α} (hab : a != b) : exists s : powersetCard α n, a in 
s ∧ b ∉ s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Equiv.ext_iff`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g ↔ ∀ (x :
 α), f x = g x
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Equiv.Perm.coe_one`：∀ {α : Type u_4}, ⇑1 = id
· 使用定理 `Set.powersetCard.coe_smul`：coe_smul {n : Nat} {g : G} {s : powersetCard 
α n} : ((g • s : powersetCard α n) : Finset α) = g • s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem mulAction_faithful (hn : 1 ≤ n) (hα : n < ENat.card α) {g : G} :
    toPerm g = (1 : Perm (powersetCard α n)) ↔ toPerm g = (1 : Perm α) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose h with h
    have : ∃ a, (g • a : α) ≠ a := by simpa [Equiv.ext_iff] using h
    obtain ⟨a, ha⟩ := this
    obtain ⟨s, has, has'⟩ := exists_mem_notMem hn hα (Ne.symm ha)
    rw [Equiv.ext_iff, not_forall]
    use s
    contrapose! has'
    simp only [toPerm_apply, coe_one, id_eq] at has'
    rw [← has']
    simpa only [coe_smul, smul_mem_smul_finset_iff, ← mem_coe_iff]
  · simp only [Equiv.ext_iff, toPerm_apply] at h ⊢
    simp [Subtype.ext_iff, Finset.ext_iff, mem_smul_finset, h]

/-- If a group `G` acts faithfully on `α`, then
it acts faithfully on `powersetCard α n` provided `1 ≤ n < ENat.card α`. -/
/-
**Set.powersetCard.faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：faithfulSMul (hn : 1 <= n) (hα : n < ENat.card α) [FaithfulSMul G α] : Fai
thfulSMul G (powersetCard α n)
参数：hn : 1 <= n；hα : n < ENat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `faithfulSMul_iff`：faithfulSMul_iff [Group G] [MulAction G α] : FaithfulS
Mul G α ↔ (forall g : G, (forall a : α, g • a = a) -> g = 1)
· 使用引理 `MulAction.toPerm_injective`：MulAction.toPerm_injective [FaithfulSMul α β
] : Function.Injective (MulAction.toPerm : α -> Equiv.Perm β)
· 使用引理 `MulAction.toPerm_one`：MulAction.toPerm_one : (MulAction.toPerm (1 : G)) 
= (1 : Equiv.Perm α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.powersetCard.mulAction_faithful`：mulAction_faithful (hn : 1 <= n) (h
α : n < ENat.card α) {g : G} : toPerm g = (1 : Perm (powersetCard α n)) ↔ toPerm
 g = (1 : Perm α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.Perm.ext_iff`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, σ = τ ↔ ∀ (x : 
α), σ x = τ x

--- 原说明 ---
If a group `G` acts faithfully on `α`, then
it acts faithfully on `powersetCard α n` provided `1 ≤ n < ENat.card α`.
-/
theorem faithfulSMul (hn : 1 ≤ n) (hα : n < ENat.card α) [FaithfulSMul G α] :
    FaithfulSMul G (powersetCard α n) := by
  rw [faithfulSMul_iff]
  intro g hg
  apply toPerm_injective (α := G) (β := α)
  rw [toPerm_one, ← mulAction_faithful hn hα]
  exact Perm.ext_iff.mpr hg

attribute [to_additive existing] faithfulSMul

variable (α G)

set_option backward.isDefEq.respectTransparency false in
variable (n) in
/-- The equivariant map from embeddings of `Fin n` (aka arrangement) to combinations. -/
@[to_additive /-- The equivariant map from embeddings of `Fin n`
  (aka arrangements) to combinations. -/]
/-
**Set.powersetCard.mulActionHom_of_embedding** 是 Mathlib 中的一个定义，位于命名空间 `Set.powe
rsetCard`。
形式化陈述：mulActionHom_of_embedding : (Fin n ↪ α) ->[G] powersetCard α n where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def mulActionHom_of_embedding : (Fin n ↪ α) →[G] powersetCard α n where
  toFun := ofFinEmb n α
  map_smul' g f := by
    rw [← Subtype.coe_inj, coe_smul, f.smul_def, val_ofFinEmb, val_ofFinEmb,
      smul_finset_def, ← map_map, map_eq_image]
    simp [toPerm]

@[to_additive]
/-
**Set.powersetCard.coe_mulActionHom_of_embedding** 是 Mathlib 中的一个定理，位于命名空间 `Set.
powersetCard`。
形式化陈述：coe_mulActionHom_of_embedding (f : Fin n ↪ α) : ↑((mulActionHom_of_embeddi
ng G α n).toFun f) = Finset.univ.map f
参数：f : Fin n ↪ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulActionHom_of_embedding (f : Fin n ↪ α) :
    ↑((mulActionHom_of_embedding G α n).toFun f) = Finset.univ.map f :=
  rfl

@[to_additive]
/-
**Set.powersetCard.mulActionHom_of_embedding_surjective** 是 Mathlib 中的一个定理，位于命名空
间 `Set.powersetCard`。
形式化陈述：mulActionHom_of_embedding_surjective : Function.Surjective (mulActionHom_o
f_embedding G α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.Embedding.exists_of_card_eq_finset`：exists_of_card_eq_finset [F
intype α] {s : Finset β} (hsn : Fintype.card α = s.card) : exists f : α ↪ β, Fin
set.univ.map f = s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem mulActionHom_of_embedding_surjective :
    Function.Surjective (mulActionHom_of_embedding G α n) := by
  intro ⟨s, hs⟩
  obtain ⟨f : Fin n ↪ α, hf⟩ :=
    Function.Embedding.exists_of_card_eq_finset (by rw [hs, Fintype.card_fin])
  exact ⟨f, Subtype.ext hf⟩

end

variable [DecidableEq α]

@[to_additive isPretransitive_of_isMultiplyPretransitive']
/-
**Set.powersetCard.isPretransitive_of_isMultiplyPretransitive** 是 Mathlib 中的一个定理
，位于命名空间 `Set.powersetCard`。
形式化陈述：isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G 
α n) : IsPretransitive G (powersetCard α n)
参数：h : IsMultiplyPretransitive G α n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `Set.powersetCard.mulActionHom_of_embedding_surjective`：mulActionHom_of_e
mbedding_surjective : Function.Surjective (mulActionHom_of_embedding G α n)
-/
theorem isPretransitive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) :
    IsPretransitive G (powersetCard α n) :=
  IsPretransitive.of_surjective_map (mulActionHom_of_embedding_surjective G α) h
/-
**Set.powersetCard.isPretransitive** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCard`。
形式化陈述：isPretransitive : IsPretransitive (Perm α) (powersetCard α n)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`：isPretransi
tive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) : IsPretrans
itive G (powersetCard α n)
· 使用定理 `Equiv.Perm.isMultiplyPretransitive`：∀ (α : Type u_1) (n : ℕ), MulAction.
IsMultiplyPretransitive (Equiv.Perm α) α n
-/
theorem isPretransitive : IsPretransitive (Perm α) (powersetCard α n) :=
  isPretransitive_of_isMultiplyPretransitive _ (isMultiplyPretransitive α n)

section compl

variable (α)

variable [Fintype α] {m : ℕ} (hm : m + n = Fintype.card α)
include hm

/-- The complement of a combination, as an equivariant map. -/
/-
**Set.powersetCard.mulActionHom_compl** 是 Mathlib 中的一个定义，位于命名空间 `Set.powersetCar
d`。
形式化陈述：mulActionHom_compl : powersetCard α n ->[G] powersetCard α m where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complement of a combination, as an equivariant map.
-/
def mulActionHom_compl : powersetCard α n →[G] powersetCard α m where
  toFun := compl hm
  map_smul' g s := by ext; simp [← inv_smul_mem_iff]

variable {hm} in
/-
**Set.powersetCard.coe_mulActionHom_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.powerse
tCard`。
形式化陈述：coe_mulActionHom_compl {s : powersetCard α n} : (mulActionHom_compl G α hm
 s : Finset α) = (s : Finset α)ᶜ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mulActionHom_compl {s : powersetCard α n} :
    (mulActionHom_compl G α hm s : Finset α) = (s : Finset α)ᶜ :=
  rfl

variable {hm} in
/-
**Set.powersetCard.mem_mulActionHom_compl** 是 Mathlib 中的一个定理，位于命名空间 `Set.powerse
tCard`。
形式化陈述：mem_mulActionHom_compl {s : powersetCard α n} {a : α} : a in mulActionHom_
compl G α hm s ↔ a ∉ s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.powersetCard.mem_compl`：mem_compl {s : powersetCard α n} {a : α} : a
 in compl hm s ↔ a ∉ s
-/
theorem mem_mulActionHom_compl {s : powersetCard α n} {a : α} :
    a ∈ mulActionHom_compl G α hm s ↔ a ∉ s :=
  mem_compl
/-
**Set.powersetCard.mulActionHom_compl_mulActionHom_compl** 是 Mathlib 中的一个定理，位于命名
空间 `Set.powersetCard`。
形式化陈述：mulActionHom_compl_mulActionHom_compl : (mulActionHom_compl G α <| (n.add_
comm m).trans hm).comp (mulActionHom_compl G α hm) = .id G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mulActionHom_compl_mulActionHom_compl :
    (mulActionHom_compl G α <| (n.add_comm m).trans hm).comp
    (mulActionHom_compl G α hm) = .id G := by
  ext s a
  change a ∈ (mulActionHom_compl G α _).comp (mulActionHom_compl G α hm) s ↔ a ∈ s
  simp [MulActionHom.comp_apply, mem_mulActionHom_compl]
/-
**Set.powersetCard.mulActionHom_compl_bijective** 是 Mathlib 中的一个定理，位于命名空间 `Set.p
owersetCard`。
形式化陈述：mulActionHom_compl_bijective : Function.Bijective (mulActionHom_compl G α 
hm)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompTriple.instIsIdId`：∀ {M : Type u_1}, CompTriple.IsId id
· 使用定理 `DFunLike.ext_iff`：ext_iff {f g : F} : f = g ↔ forall x, f x = g x
· 使用定理 `Set.powersetCard.mulActionHom_compl_mulActionHom_compl`：mulActionHom_com
pl_mulActionHom_compl : (mulActionHom_compl G α <| (n.add_comm m).trans hm).comp
 (mulActionHom_compl G α hm) = .id G
-/
theorem mulActionHom_compl_bijective :
    Function.Bijective (mulActionHom_compl G α hm) :=
  Function.bijective_iff_has_inverse.mpr ⟨mulActionHom_compl G α ((n.add_comm m).trans hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α hm),
    DFunLike.ext_iff.mp (mulActionHom_compl_mulActionHom_compl G α _)⟩

end compl

variable {G} in
/-
**Set.powersetCard.fixedPoints_ne_univ_of_faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间
 `Set.powersetCard`。
形式化陈述：fixedPoints_ne_univ_of_faithfulSMul [Nontrivial G] [FaithfulSMul G α] {n :
 Nat} (hn : 0 < n) (hn' : n < Nat.card α) : fixedPoints G (powersetCard α n) != 
univ
参数：hn : 0 < n；hn' : n < Nat.card α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Equiv.Perm.ext`：∀ {α : Sort u} {σ τ : Equiv.Perm α}, (∀ (x : α), σ x = τ
 x) → σ = τ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Set.powersetCard.faithfulSMul`：faithfulSMul (hn : 1 <= n) (hα : n < ENat
.card α) [FaithfulSMul G α] : FaithfulSMul G (powersetCard α n)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ENat.card_eq_coe_natCard`：card_eq_coe_natCard (α : Type*) [Finite α] : c
ard α = Nat.card α
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `ne_zero_of_lt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a < b → b ≠ 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `MulAction.toPerm_injective`：MulAction.toPerm_injective [FaithfulSMul α β
] : Function.Injective (MulAction.toPerm : α -> Equiv.Perm β)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
-/
theorem fixedPoints_ne_univ_of_faithfulSMul
    [Nontrivial G] [FaithfulSMul G α]
    {n : ℕ} (hn : 0 < n) (hn' : n < Nat.card α) :
    fixedPoints G (powersetCard α n) ≠ univ := by
  obtain ⟨g, h⟩ := exists_ne (1 : G)
  contrapose! h
  replace h : (toPerm g : Perm (powersetCard α n)) = 1 := by
    ext1 s
    exact eq_univ_iff_forall.mp h s g
  rwa [← toPermHom_apply, map_eq_one_iff] at h
  have := powersetCard.faithfulSMul (G := G) (α := α) hn ?_
  · exact MulAction.toPerm_injective
  ·   simpa [ENat.card_eq_coe_natCard, Nat.cast_lt, Nat.finite_of_card_ne_zero (ne_zero_of_lt hn')]

variable (α)

/-- The obvious map from a type to its 1-combinations, as an equivariant map. -/
@[to_additive /-- The obvious map from a type to its 1-combinations, as an equivariant map. -/]
/-
**Set.powersetCard.mulActionHom_singleton** 是 Mathlib 中的一个定义，位于命名空间 `Set.powerse
tCard`。
形式化陈述：mulActionHom_singleton : α ->[G] powersetCard α 1 where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The obvious map from a type to its 1-combinations, as an equivariant map.
-/
noncomputable def mulActionHom_singleton : α →[G] powersetCard α 1 where
  toFun := ofSingleton
  map_smul' _ _ := rfl

@[to_additive]
/-
**Set.powersetCard.mulActionHom_singleton_bijective** 是 Mathlib 中的一个定理，位于命名空间 `S
et.powersetCard`。
形式化陈述：mulActionHom_singleton_bijective : Function.Bijective (mulActionHom_single
ton G α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.singleton_injective`：singleton_injective : Injective (singleton :
 α -> Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_one`：card_eq_one : #s = 1 ↔ exists a, s = {a}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mulActionHom_singleton_bijective :
    Function.Bijective (mulActionHom_singleton G α) := by
  refine ⟨fun a b h ↦ Finset.singleton_injective congr($h.1), fun ⟨s, hs⟩ ↦ ?_⟩
  obtain ⟨a, rfl⟩ := card_eq_one.mp hs
  exact ⟨a, rfl⟩

variable {α}

/-- The action of `Equiv.Perm α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`.

This is a consequence that the stabilizer of such a combination
is a maximal subgroup. -/
/-
**Set.powersetCard.isPreprimitive_perm** 是 Mathlib 中的一个定理，位于命名空间 `Set.powersetCa
rd`。
形式化陈述：isPreprimitive_perm {n : Nat} (h_one_le : 1 <= n) (hn : n < Nat.card α) (h
α : Nat.card α != 2 * n) : IsPreprimitive (Perm α) (powersetCard α n)
参数：h_one_le : 1 <= n；hn : n < Nat.card α；hα : Nat.card α != 2 * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Set.powersetCard.isPretransitive`：isPretransitive : IsPretransitive (Per
m α) (powersetCard α n)
· 使用定理 `Set.powersetCard.nontrivial'`：nontrivial' (h1 : 0 < n) (h2 : n < Nat.car
d α) : Nontrivial (powersetCard α n)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.isCoatom_stabilizer_iff_preprimitive`：isCoatom_stabilizer_iff_
preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) : IsCoatom (stabilizer
 G a) ↔ IsPreprimitive G X
· 使用定理 `Set.powersetCard.stabilizer_coe`：stabilizer_coe {n : Nat} (s : powersetC
ard α n) : stabilizer G s = stabilizer G (s : Set α)
· 使用定理 `Equiv.Perm.isCoatom_stabilizer`：isCoatom_stabilizer {s : Set α} (hs_none
mpty : s.Nonempty) (hsc_nonempty : sᶜ.Nonempty) (hα : Nat.card α != 2 * s.ncard)
 : IsCoatom (stabili…
· 使用定理 `Set.powersetCard.coe_nonempty_iff`：coe_nonempty_iff {s : Set.powersetCar
d α n} : (s : Set α).Nonempty ↔ 1 <= n
· 使用定理 `Set.nonempty_compl`：nonempty_compl : sᶜ.Nonempty ↔ s != univ
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Set.eq_univ_iff_ncard`：eq_univ_iff_ncard [Finite α] (s : Set α) : s = un
iv ↔ ncard s = Nat.card α
· 使用定理 `Set.powersetCard.ncard_eq`：ncard_eq (s : Set.powersetCard α n) : (s : Se
t α).ncard = n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
The action of `Equiv.Perm α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`.

This is a consequence that the stabilizer of such a combination
is a maximal subgroup.
-/
theorem isPreprimitive_perm {n : ℕ} (h_one_le : 1 ≤ n) (hn : n < Nat.card α)
    (hα : Nat.card α ≠ 2 * n) :
    IsPreprimitive (Perm α) (powersetCard α n) := by
  -- The finiteness of `α` follows from the assumptions of the theorem.
  have : Finite α := Nat.finite_of_card_ne_zero (Nat.ne_zero_of_lt hn)
  have : Fintype α := Fintype.ofFinite α
  -- The action is pretransitive.
  have : IsPretransitive (Perm α) (powersetCard α n) := powersetCard.isPretransitive
  -- The type on which the group acts is nontrivial.
  have : Nontrivial (powersetCard α n) := powersetCard.nontrivial' h_one_le hn
  obtain ⟨s⟩ := this.to_nonempty
  -- It remains to prove that stabilizer of some point is maximal.
  rw [← isCoatom_stabilizer_iff_preprimitive _ s]
  -- The stabilizer of a combination is the stabilizer of the underlying set.
  rw [stabilizer_coe]
  -- We conclude by `Equiv.Perm.isCoatom_stabilizer`
  apply isCoatom_stabilizer
  -- `s` is nonempty because `n ≠ 0`.
  · rwa [powersetCard.coe_nonempty_iff]
  -- `sᶜ` is nonempty because `n < Nat.card α`.
  · rw [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq]
    exact hn.ne
  -- `Nat.card α ≠ 2 * s.ncard` because `Nat.card α ≠ 2 * s`.
  · rwa [ncard_eq]

set_option backward.isDefEq.respectTransparency false in
/-- If `3 ≤ Nat.card α`, then `alternatingGroup α` acts transitively on `Set.powersetCard α n`.

If `Nat.card α ≤ 2`, then `alternatingGroup α` is trivial, and
the result only holds in the trivial case where `powersetCard α n` is a subsingleton,
that is, when `n = 0` or `Nat.card α ≤ n`. -/
/-
**Set.powersetCard.isPretransitive_alternatingGroup** 是 Mathlib 中的一个定理，位于命名空间 `S
et.powersetCard`。
形式化陈述：isPretransitive_alternatingGroup [Fintype α] (hα : 3 <= Nat.card α) : IsPr
etransitive (alternatingGroup α) (powersetCard α n)
参数：hα : 3 <= Nat.card α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Set.powersetCard.isPretransitive_of_isMultiplyPretransitive`：isPretransi
tive_of_isMultiplyPretransitive (h : IsMultiplyPretransitive G α n) : IsPretrans
itive G (powersetCard α n)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.is_one_pretransitive_iff`：is_one_pretransitive_iff : IsMultipl
yPretransitive G α 1 ↔ IsPretransitive G α
· 使用定理 `alternatingGroup.isPretransitive_of_three_le_card`：∀ (α : Type u_1) [ins
t : Fintype α] [inst_1 : DecidableEq α],   3 ≤ Nat.card α → MulAction.IsPretrans
itive (↥(alternatingGroup α)) α
· 使用定理 `alternatingGroup.isMultiplyPretransitive`：∀ (α : Type u_1) [inst : Finty
pe α] [inst_1 : DecidableEq α],   MulAction.IsMultiplyPretransitive (↥(alternati
ngGroup α)) α (Nat.card α - 2)
· 使用定理 `MulAction.isMultiplyPretransitive_of_le`：isMultiplyPretransitive_of_le {
m n : Nat} [IsMultiplyPretransitive G α n] (hmn : m <= n) (hα : n <= Nat.card α)
 [Finite α] : IsMultiplyPretr…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `MulAction.IsPretransitive.of_surjective_map`：∀ {M : Type u_3} {N : Type 
u_4} {α : Type u_5} {β : Type u_6} [inst : Monoid M] [inst_1 : Monoid N]   [inst
_2 : MulAction M α] [inst_3 : Mul…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `Set.powersetCard.mulActionHom_compl_bijective`：mulActionHom_compl_biject
ive : Function.Bijective (mulActionHom_compl G α hm)
· 使用定理 `Finite.card_le_one_iff_subsingleton`：card_le_one_iff_subsingleton [Finit
e α] : Nat.card α <= 1 ↔ Subsingleton α
· 使用定理 `Set.powersetCard.instFiniteElemFinset`：∀ (α : Type u_1) (n : ℕ) [Finite 
α], Finite ↑(Set.powersetCard α n)
· 使用定理 `Set.powersetCard.card`：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powerset
Card α n) = (Nat.card α).choose n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.choose_eq_zero_iff`：choose_eq_zero_iff {n k : Nat} : n.choose k = 0 
↔ n < k
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
If `3 ≤ Nat.card α`, then `alternatingGroup α` acts transitively on `Set.powerse
tCard α n`.

If `Nat.card α ≤ 2`, then `alternatingGroup α` is trivial, and
the result only holds in the trivial case where `powersetCard α n` is a subsingl
eton,
that is, when `n = 0` or `Nat.card α ≤ n`.
-/
theorem isPretransitive_alternatingGroup [Fintype α] (hα : 3 ≤ Nat.card α) :
    IsPretransitive (alternatingGroup α) (powersetCard α n) := by
  wlog! hn : 2 * n ≤ Nat.card α
  · have : IsPretransitive (alternatingGroup α) (powersetCard α (Nat.card α - n)) := by
      apply this hα
      grind
    by_cases hn' : n ≤ Nat.card α
    · apply IsPretransitive.of_surjective_map
        (mulActionHom_compl_bijective (alternatingGroup α) α _).surjective this
      aesop
    · suffices Subsingleton (powersetCard α n) by infer_instance
      rw [not_le] at hn'
      rw [← Finite.card_le_one_iff_subsingleton, powersetCard.card,
        Nat.choose_eq_zero_iff.mpr hn']
      simp
  apply isPretransitive_of_isMultiplyPretransitive
  rcases eq_or_ne n 0 with rfl | hn0
  · infer_instance
  rcases eq_or_ne n 1 with rfl | hn1
  · rw [is_one_pretransitive_iff]
    exact alternatingGroup.isPretransitive_of_three_le_card α hα
  have := alternatingGroup.isMultiplyPretransitive α
  apply isMultiplyPretransitive_of_le (n := Nat.card α - 2) <;> grind

set_option backward.isDefEq.respectTransparency false in
/-- The action of `alternatingGroup α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`. -/
/-
**Set.powersetCard.isPreprimitive_alternatingGroup** 是 Mathlib 中的一个定理，位于命名空间 `Se
t.powersetCard`。
形式化陈述：isPreprimitive_alternatingGroup [Fintype α] {n : Nat} (h_three_le : 3 <= n
) (hn : n < Nat.card α) (hα : Nat.card α != 2 * n) : IsPreprimitive (alternating
Group α) (powersetCard α n)
参数：h_three_le : 3 <= n；hn : n < Nat.card α；hα : Nat.card α != 2 * n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.powersetCard.isPretransitive_alternatingGroup`：isPretransitive_alter
natingGroup [Fintype α] (hα : 3 <= Nat.card α) : IsPretransitive (alternatingGro
up α) (powersetCard α n)
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.powersetCard.nontrivial`：nontrivial (h1 : 0 < n) (h2 : n < ENat.card
 α) : Nontrivial (powersetCard α n)
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENat.card_eq_coe_fintype_card`：card_eq_coe_fintype_card [Fintype α] : ca
rd α = Fintype.card α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.isCoatom_stabilizer_iff_preprimitive`：isCoatom_stabilizer_iff_
preprimitive [IsPretransitive G X] [Nontrivial X] (a : X) : IsCoatom (stabilizer
 G a) ↔ IsPreprimitive G X
· 使用定理 `Set.powersetCard.stabilizer_coe`：stabilizer_coe {n : Nat} (s : powersetC
ard α n) : stabilizer G s = stabilizer G (s : Set α)
· 使用定理 `alternatingGroup.isCoatom_stabilizer`：isCoatom_stabilizer {s : Set α} (h
0 : s.Nonempty) (h1 : sᶜ.Nonempty) (hs : Nat.card α != 2 * ncard s) : IsCoatom (
stabilizer (alternatingGro…
· 使用定理 `Set.powersetCard.coe_nonempty_iff`：coe_nonempty_iff {s : Set.powersetCar
d α n} : (s : Set α).Nonempty ↔ 1 <= n
· 使用定理 `Mathlib.Meta.NormNum.isNat_le_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] {a b : α} {a' b' : ℕ},   Mathlib.Me
ta.NormNum.IsNat a a' → …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.powersetCard.ncard_eq`：ncard_eq (s : Set.powersetCard α n) : (s : Se
t α).ncard = n
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b

--- 原说明 ---
The action of `alternatingGroup α` on `Set.powersetCard α n` is preprimitive
provided `1 ≤ n < Nat.card α` and `Nat.card α ≠ 2 * n`.
-/
theorem isPreprimitive_alternatingGroup [Fintype α] {n : ℕ}
    (h_three_le : 3 ≤ n) (hn : n < Nat.card α) (hα : Nat.card α ≠ 2 * n) :
    IsPreprimitive (alternatingGroup α) (powersetCard α n) := by
  have : IsPretransitive (alternatingGroup α) (powersetCard α n) :=
    isPretransitive_alternatingGroup (le_trans h_three_le hn.le)
  have : Nontrivial (powersetCard α n) := nontrivial (by positivity) (by simpa using hn)
  obtain ⟨s⟩ := this.to_nonempty
  rw [← isCoatom_stabilizer_iff_preprimitive _ s, stabilizer_coe]
  apply alternatingGroup.isCoatom_stabilizer
  · rw [powersetCard.coe_nonempty_iff]
    exact le_trans (by norm_num) h_three_le
  · simpa [nonempty_compl, ne_eq, eq_univ_iff_ncard, ncard_eq] using ne_of_lt hn
  · simpa only [ncard_eq]

end Set.powersetCard

