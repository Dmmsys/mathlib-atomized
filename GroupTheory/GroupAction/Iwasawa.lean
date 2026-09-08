/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.GroupTheory.Subgroup.Simple

/-! # Iwasawa criterion for simplicity

- `IwasawaStructure` : the structure underlying the Iwasawa criterion.
  For a group `G`, this consists of an action of `G` on a type `α` and,
  for every `a : α`, of a subgroup `T a`, such that the following properties hold:
  - for all `a`, `T a` is commutative
  - for all `g : G` and `a : α`, `T (g • a) = MulAut.conj g • T a`
  - the subgroups `T a` generate `G`

We then prove two versions of the Iwasawa criterion when
there is an Iwasawa structure.

- `IwasawaStructure.commutator_le` asserts that if the action of `G` on `α`
  is quasiprimitive, then every normal subgroup that acts nontrivially
  contains `commutator G`.

- `IwasawaStructure.isSimpleGroup` : the Iwasawa criterion for simplicity.
  If the action of `G` on `α` is quasiprimitive and faithful,
  and `G` is nontrivial and perfect, then `G` is simple.

## TODO

Additivize. The issue is that it requires to additivize `commutator`
(which, moreover, lives in the root namespace)
-/

public section

namespace MulAction

open scoped Pointwise

variable (M : Type*) [Group M] (α : Type*) [MulAction M α]

/-- The structure underlying the Iwasawa criterion -/
/-
**MulAction.IwasawaStructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(M : Type u_1) → [inst : Group M] → (α : Type u_2) → [MulAction M α] → Typ
e (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The structure underlying the Iwasawa criterion
-/
structure IwasawaStructure where
  /-- The subgroups of the Iwasawa structure -/
  T : α → Subgroup M
  /-- The commutativity property of the subgroups -/
  is_comm : ∀ x : α, IsMulCommutative (T x)
  /-- The conjugacy property of the subgroups -/
  is_conj : ∀ g : M, ∀ x : α, T (g • x) = MulAut.conj g • T x
  /-- The subgroups generate the group -/
  is_generator : iSup T = ⊤

variable {M α}

namespace IwasawaStructure

/-- The Iwasawa criterion : If a quasiprimitive action of a group G on X
  has an Iwasawa structure, then any normal subgroup that acts nontrivially
  contains the group of commutators. -/
/-
**MulAction.IwasawaStructure.commutator_le** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IwasawaStructure`。
形式化陈述：commutator_le (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α] (N :
 Subgroup M) [nN : N.Normal] (hNX : MulAction.fixedPoints N α != .univ) : commut
ator M <= N
参数：IwaS : IwasawaStructure M α；N : Subgroup M；hNX : MulAction.fixedPoints N α !=
 .univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsQuasiPreprimitive.isPretransitive_of_normal`：∀ {G : Type u_1
} {X : Type u_2} {inst : Group G} {inst_1 : MulAction G X} [self : MulAction.IsQ
uasiPreprimitive G X]   {N : Subgroup G} [N.N…
· 使用定理 `MulAction.nontrivial_of_fixedPoints_ne_univ`：nontrivial_of_fixedPoints_n
e_univ (h : fixedPoints G α != .univ) : Nontrivial α
· 使用定理 `Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top`：Subgroup.N
ormal.commutator_le_of_self_sup_commutative_eq_top {N : Subgroup G} [N.Normal] {
H : Subgroup G} (hHN : N ⊔ H = ⊤) (hH : IsMulCommu…
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulAction.IwasawaStructure.is_generator`：∀ {M : Type u_1} [inst : Group 
M] {α : Type u_2} [inst_1 : MulAction M α] (self : MulAction.IwasawaStructure M 
α),   iSup self.T = ⊤
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Subgroup.smul_def`：∀ {G : Type u_1} {α : Type u_2} [inst : Group G] [ins
t_1 : MulAction G α] {S : Subgroup G} (g : ↥S) (m : α),   g • m = ↑g • m
· 使用定理 `MulAction.IwasawaStructure.is_conj`：∀ {M : Type u_1} [inst : Group M] {α
 : Type u_2} [inst_1 : MulAction M α] (self : MulAction.IwasawaStructure M α)   
(g : M) (x : α), self.T …
· 使用定理 `Subgroup.mem_sup_left`：mem_sup_left {S T : Subgroup G} : forall {x : G},
 x in S -> x in S ⊔ T
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
· 使用定理 `Subgroup.mem_sup_right`：mem_sup_right {S T : Subgroup G} : forall {x : G
}, x in T -> x in S ⊔ T
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `MulAction.IwasawaStructure.is_comm`：∀ {M : Type u_1} [inst : Group M] {α
 : Type u_2} [inst_1 : MulAction M α] (self : MulAction.IwasawaStructure M α)   
(x : α), IsMulCommutativ…

--- 原说明 ---
The Iwasawa criterion : If a quasiprimitive action of a group G on X
  has an Iwasawa structure, then any normal subgroup that acts nontrivially
  contains the group of commutators.
-/
theorem commutator_le (IwaS : IwasawaStructure M α) [IsQuasiPreprimitive M α]
    (N : Subgroup M) [nN : N.Normal] (hNX : MulAction.fixedPoints N α ≠ .univ) :
    commutator M ≤ N := by
  have is_transN := IsQuasiPreprimitive.isPretransitive_of_normal hNX
  have ntα : Nontrivial α := nontrivial_of_fixedPoints_ne_univ hNX
  obtain a : α := Nontrivial.to_nonempty.some
  apply nN.commutator_le_of_self_sup_commutative_eq_top ?_ (IwaS.is_comm a)
  -- We have to prove that N ⊔ IwaS.T x = ⊤
  rw [eq_top_iff, ← IwaS.is_generator, iSup_le_iff]
  intro x
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq N a x
  rw [Subgroup.smul_def, IwaS.is_conj g a]
  rintro _ ⟨k, hk, rfl⟩
  have hg' : ↑g ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_left (Subtype.mem g)
  have hk' : k ∈ N ⊔ IwaS.T a := Subgroup.mem_sup_right hk
  exact (N ⊔ IwaS.T a).mul_mem ((N ⊔ IwaS.T a).mul_mem hg' hk') ((N ⊔ IwaS.T a).inv_mem hg')

/-- The Iwasawa criterion for simplicity -/
/-
**MulAction.IwasawaStructure.isSimpleGroup** 是 Mathlib 中的一个定理，位于命名空间 `MulAction.
IwasawaStructure`。
形式化陈述：isSimpleGroup [Nontrivial M] (is_perfect : commutator M = ⊤) [IsQuasiPrepr
imitive M α] (IwaS : IwasawaStructure M α) (is_faithful : FaithfulSMul M α) : Is
SimpleGroup M
参数：is_perfect : commutator M = ⊤；IwaS : IwasawaStructure M α；is_faithful : Faith
fulSMul M α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `MulAction.IwasawaStructure.commutator_le`：commutator_le (IwaS : IwasawaS
tructure M α) [IsQuasiPreprimitive M α] (N : Subgroup M) [nN : N.Normal] (hNX : 
MulAction.fixedPoints N α != .…
· 使用定理 `Subgroup.eq_bot_iff_forall`：eq_bot_iff_forall : H = ⊥ ↔ forall x in H, x
 = (1 : G)
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `ge_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a

--- 原说明 ---
The Iwasawa criterion for simplicity
-/
theorem isSimpleGroup [Nontrivial M] (is_perfect : commutator M = ⊤)
    [IsQuasiPreprimitive M α] (IwaS : IwasawaStructure M α) (is_faithful : FaithfulSMul M α) :
    IsSimpleGroup M := by
  apply IsSimpleGroup.mk
  intro N nN
  cases or_iff_not_imp_left.mpr (IwaS.commutator_le N) with
  | inl h =>
    refine Or.inl (N.eq_bot_iff_forall.mpr fun n hn => ?_)
    apply is_faithful.eq_of_smul_eq_smul
    intro x
    rw [one_smul]
    exact Set.eq_univ_iff_forall.mp h x ⟨n, hn⟩
  | inr h => exact Or.inr (top_le_iff.mp (le_trans (ge_of_eq is_perfect) h))

end MulAction.IwasawaStructure

