/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Cofinality.Enum
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.Order.IsNormal
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.SuccPred

/-!
# Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

## Main results

* `Ordinal.isClosed_iff_iSup`: A set of ordinals is closed iff it's
  closed under suprema.
* `Ordinal.enumOrd_isNormal_iff_isClosed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.

## Todo

Most things in this file should be generalized to other well-orders, or to Scott-Hausdorff
topologies.
-/

@[expose] public noncomputable section

universe u v

open Cardinal Order Topology

namespace Ordinal

variable {s : Set Ordinal.{u}} {a : Ordinal.{u}}

/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : TopologicalSpace Ordinal.{u} := Preorder.topology Ordinal.{u}
/-
**Ordinal.** 是 Mathlib 中的一个实例，位于命名空间 `Ordinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderTopology Ordinal.{u} := ⟨rfl⟩

@[deprecated SuccOrder.isOpen_singleton_iff (since := "2026-01-20")]
/-
**Ordinal.isOpen_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.isOpen_singleton_iff`：isOpen_singleton_iff : IsOpen {a} ↔ ¬ Is
SuccLimit a
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a :=
  SuccOrder.isOpen_singleton_iff

@[deprecated SuccOrder.nhds_eq_pure (since := "2026-01-20")]
/-
**Ordinal.nhds_eq_pure** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：nhds_eq_pure : 𝓝 a = pure a ↔ ¬ IsSuccLimit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.nhds_eq_pure`：nhds_eq_pure {a : α} : 𝓝 a = pure a ↔ ¬ IsSuccLi
mit a
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  SuccOrder.nhds_eq_pure

@[deprecated SuccOrder.isOpen_iff (since := "2026-01-20")]
/-
**Ordinal.isOpen_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isOpen_iff : IsOpen s ↔ forall o in s, IsSuccLimit o -> exists a < o, Set.
Ioo a o subseteq s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.isOpen_iff`：isOpen_iff {s : Set α} : IsOpen s ↔ forall o in s,
 IsSuccLimit o -> exists a < o, Ioo a o subseteq s
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsSuccLimit o → ∃ a < o, Set.Ioo a o ⊆ s :=
  SuccOrder.isOpen_iff

open List Set in
/-
**Ordinal.mem_closure_tfae** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) : TFAE [a in closure 
s, a in closure (s inter Iic a), (s inter Iic a).Nonempty ∧ sSup (s inter Iic a)
 = a, exists t, t subseteq s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a, exists (ι :
 Type u), Nonempty ι ∧ exists f : ι -> Ordinal, (forall i, f i in s) ∧ ⨆ i, f i 
= a]
参数：a : Ordinal.{u}；s : Set Ordinal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `nhdsWithin_inter'`：nhdsWithin_inter' (a : α) (s t : Set α) : 𝓝[s inter t
] a = 𝓝[s] a ⊓ 𝓟 t
· 使用定理 `SuccOrder.nhdsLE_eq_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [in
st_1 : LinearOrder α] [ClosedIciTopology α] [SuccOrder α] (a : α),   nhdsWithin 
a (Set.Iic a) …
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `OrderClosedTopology.to_t2Space`：∀ {α : Type u} [inst : TopologicalSpace 
α] [inst_1 : PartialOrder α] [t : OrderClosedTopology α], T2Space α
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `isLUB_of_mem_closure`：isLUB_of_mem_closure {s : Set α} {a : α} (hsa : a 
in upperBounds s) (hsf : a in closure s) : IsLUB s a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `BddAbove.mono`：BddAbove.mono ⦃s t : Set α⦄ (h : s subseteq t) : BddAbove
 t -> BddAbove s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用定理 `bddAbove_Iic`：bddAbove_Iic : BddAbove (Iic a)
· 使用定理 `Ordinal.bddAbove_iff_small`：bddAbove_iff_small {s : Set Ordinal.{u}} : B
ddAbove s ↔ Small.{u} s
· 使用定理 `Set.Nonempty.to_subtype`：∀ {α : Type u} {s : Set α}, s.Nonempty → Nonemp
ty ↑s
· 使用定理 `Equiv.nonempty`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Nonempty β], No
nempty α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `Equiv.iSup_comp`：Equiv.iSup_comp {g : ι' -> α} (e : ι ≃ ι') : ⨆ x, g (e 
x) = ⨆ y, g y
（共 39 条，此处仅展示前 30 条）
-/
theorem mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) :
    TFAE [a ∈ closure s,
      a ∈ closure (s ∩ Iic a),
      (s ∩ Iic a).Nonempty ∧ sSup (s ∩ Iic a) = a,
      ∃ t, t ⊆ s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a,
      ∃ (ι : Type u), Nonempty ι ∧ ∃ f : ι → Ordinal, (∀ i, f i ∈ s) ∧ ⨆ i, f i = a] := by
  tfae_have 1 → 2 := by
    simpa only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter',
      SuccOrder.nhdsLE_eq_nhds] using! id
  tfae_have 2 → 3
  | h => by
    rcases (s ∩ Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      exact fun x hx => hx.2
  tfae_have 3 → 4
  | h => ⟨_, inter_subset_left, h.1, bddAbove_Iic.mono inter_subset_right, h.2⟩
  tfae_have 4 → 5 := by
    rintro ⟨t, ht, ht₀, ht₁, rfl⟩
    rw [bddAbove_iff_small] at ht₁
    refine ⟨Shrink t, ?_, Subtype.val ∘ (equivShrink _).symm, ?_, ?_⟩
    · have := ht₀.to_subtype
      exact (equivShrink _).symm.nonempty
    · simpa [← (equivShrink t).forall_congr_left (p := (·.1 ∈ s))]
    · simp [(equivShrink t).symm.iSup_comp, ← sSup_eq_iSup']
  tfae_have 5 → 1 := by
    rintro ⟨ι, hne, f, hfs, rfl⟩
    exact closure_mono (range_subset_iff.2 hfs) <| csSup_mem_closure (range_nonempty f)
      bddAbove_of_small
  tfae_finish
/-
**Ordinal.mem_closure_iff_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_closure_iff_iSup : a in closure s ↔ exists (ι : Type u) (_ : Nonempty 
ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ i, f i = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Ordinal.mem_closure_tfae`：mem_closure_tfae (a : Ordinal.{u}) (s : Set Or
dinal) : TFAE [a in closure s, a in closure (s inter Iic a), (s inter Iic a).Non
empty ∧ sSup (…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_closure_iff_iSup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]
/-
**Ordinal.mem_iff_iSup_of_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_iff_iSup_of_isClosed (hs : IsClosed s) : a in s ↔ exists (ι : Type u) 
(_hι : Nonempty ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ i, f i = a
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mem_closure_iff_iSup`：mem_closure_iff_iSup : a in closure s ↔ ex
ists (ι : Type u) (_ : Nonempty ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ 
i, f i = a
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_iff_iSup_of_isClosed (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  rw [← mem_closure_iff_iSup, hs.closure_eq]

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
/-
**Ordinal.mem_closure_iff_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_closure_iff_bsup : a in closure s ↔ exists (o : Ordinal) (_ho : o != 0
) (f : forall a < o, Ordinal), (forall i hi, f i hi in s) ∧ bsup.{u, u} o f = a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.mem_closure_iff_iSup`：mem_closure_iff_iSup : a in closure s ↔ ex
ists (ι : Type u) (_ : Nonempty ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ 
i, f i = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Ordinal.bsup_eq_iSup`：bsup_eq_iSup {ι} (f : ι -> Ordinal) : bsup _ (bfam
ilyOfFamily f) = iSup f
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Ordinal.iSup_eq_bsup`：iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordi
nal) : iSup (familyOfBFamily o f) = bsup o f
-/
theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  rw [mem_closure_iff_iSup]
  constructor
  · rintro ⟨ι, _, f, hf, rfl⟩
    exact ⟨_, by simp, bfamilyOfFamily f, fun i hi ↦ hf .., bsup_eq_iSup f⟩
  · rintro ⟨o, ho, f, hf, rfl⟩
    exact ⟨_, by simpa, familyOfBFamily _ f, fun i ↦ hf .., iSup_eq_bsup f⟩

@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
/-
**Ordinal.mem_closed_iff_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：mem_closed_iff_bsup (hs : IsClosed s) : a in s ↔ exists (o : Ordinal) (_ho
 : o != 0) (f : forall a < o, Ordinal), (forall i hi, f i hi in s) ∧ bsup.{u, u}
 o f = a
参数：hs : IsClosed s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.mem_closure_iff_bsup`：mem_closure_iff_bsup : a in closure s ↔ ex
ists (o : Ordinal) (_ho : o != 0) (f : forall a < o, Ordinal), (forall i hi, f i
 hi in s) ∧ bsup.{…
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a ∈ s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  rw [← mem_closure_iff_bsup, hs.closure_eq]
/-
**Ordinal.isClosed_iff_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isClosed_iff_iSup : IsClosed s ↔ forall {ι : Type u}, Nonempty ι -> forall
 f : ι -> Ordinal, (forall i, f i in s) -> ⨆ i, f i in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.mem_iff_iSup_of_isClosed`：mem_iff_iSup_of_isClosed (hs : IsClose
d s) : a in s ↔ exists (ι : Type u) (_hι : Nonempty ι) (f : ι -> Ordinal), (fora
ll i, f i in s) ∧ ⨆ i,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `closure_subset_iff_isClosed`：closure_subset_iff_isClosed : closure s sub
seteq s ↔ IsClosed s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.mem_closure_iff_iSup`：mem_closure_iff_iSup : a in closure s ↔ ex
ists (ι : Type u) (_ : Nonempty ι) (f : ι -> Ordinal), (forall i, f i in s) ∧ ⨆ 
i, f i = a
-/
theorem isClosed_iff_iSup :
    IsClosed s ↔
      ∀ {ι : Type u}, Nonempty ι → ∀ f : ι → Ordinal, (∀ i, f i ∈ s) → ⨆ i, f i ∈ s := by
  use fun hs ι hι f hf => (mem_iff_iSup_of_isClosed hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_iSup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

@[deprecated isClosed_iff_iSup (since := "2026-04-05")]
/-
**Ordinal.isClosed_iff_bsup** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isClosed_iff_bsup : IsClosed s ↔ forall {o : Ordinal}, o != 0 -> forall f 
: forall a < o, Ordinal, (forall i hi, f i hi in s) -> bsup.{u, u} o f in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isClosed_iff_iSup`：isClosed_iff_iSup : IsClosed s ↔ forall {ι : 
Type u}, Nonempty ι -> forall f : ι -> Ordinal, (forall i, f i in s) -> ⨆ i, f i
 in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.nonempty_toType_iff`：nonempty_toType_iff {o : Ordinal} : Nonempt
y o.ToType ↔ o != 0
· 使用定理 `Ordinal.type_toType`：type_toType (o : Ordinal) : typeLT o.ToType = o
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.bsup_eq_iSup`：bsup_eq_iSup {ι} (f : ι -> Ordinal) : bsup _ (bfam
ilyOfFamily f) = iSup f
· 使用定理 `Ordinal.type_ne_zero_iff_nonempty`：type_ne_zero_iff_nonempty [IsWellOrde
r α r] : type r != 0 ↔ Nonempty α
-/
theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal}, o ≠ 0 → ∀ f : ∀ a < o, Ordinal,
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s := by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (nonempty_toType_iff.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_iSup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

@[deprecated SuccOrder.isSuccLimit_of_mem_frontier (since := "2026-01-20")]
/-
**Ordinal.isSuccLimit_of_mem_frontier** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isSuccLimit_of_mem_frontier (ha : a in frontier s) : IsSuccLimit a
参数：ha : a in frontier s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SuccOrder.isSuccLimit_of_mem_frontier`：isSuccLimit_of_mem_frontier {a : 
α} {s : Set α} (ha : a in frontier s) : IsSuccLimit a
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem isSuccLimit_of_mem_frontier (ha : a ∈ frontier s) : IsSuccLimit a :=
  SuccOrder.isSuccLimit_of_mem_frontier ha

@[deprecated isNormal_enum_iff_dirSupClosed (since := "2026-05-25")]
/-
**Ordinal.enumOrd_isNormal_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：enumOrd_isNormal_iff_isClosed (hs : ¬ BddAbove s) : IsNormal (enumOrd s) ↔
 IsClosed s
参数：hs : ¬ BddAbove s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.enumOrd_strictMono`：enumOrd_strictMono (hs : ¬ BddAbove s) : Str
ictMono (enumOrd s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ordinal.isClosed_iff_iSup`：isClosed_iff_iSup : IsClosed s ↔ forall {ι : 
Type u}, Nonempty ι -> forall f : ι -> Ordinal, (forall i, f i in s) -> ⨆ i, f i
 in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Order.IsNormal.map_iSup`：map_iSup {ι} [Nonempty ι] {g : ι -> α} (hf : Is
Normal f) (hg : BddAbove (range g)) : f (⨆ i, g i) = ⨆ i, f (g i)
· 使用定理 `Ordinal.bddAbove_of_small`：bddAbove_of_small {s : Set Ordinal.{u}} [Smal
l.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ordinal.enumOrd_mem`：enumOrd_mem (hs : ¬ BddAbove s) (o : Ordinal) : enu
mOrd s o in s
· 使用定理 `Order.isNormal_iff`：isNormal_iff [LinearOrder α] [LinearOrder β] {f : α 
-> β} : IsNormal f ↔ StrictMono f ∧ forall o, IsSuccLimit o -> forall a, (forall
 b < o, …
· 使用定理 `csSup_mem_closure`：csSup_mem_closure {s : Set α} (hs : s.Nonempty) (B : 
BddAbove s) : sSup s in closure s
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Order.IsSuccLimit.nonempty_Iio`：∀ {α : Type u_1} {a : α} [inst : Preorde
r α], Order.IsSuccLimit a → (Set.Iio a).Nonempty
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Ordinal.range_enumOrd`：range_enumOrd (hs : ¬ BddAbove s) : range (enumOr
d s) = s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Ordinal.enumOrd_le_of_forall_lt`：enumOrd_le_of_forall_lt (ha : a in s) (
H : forall b < o, enumOrd s b < a) : enumOrd s o <= a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Order.IsSuccLimit.add_one_lt`：∀ {α : Type u_1} {x y : α} [inst : Partial
Order α] [inst_1 : Add α] [inst_2 : One α] [SuccAddOrder α],   Order.IsSuccLimit
 x → y < x → y + 1…
（共 31 条，此处仅展示前 30 条）
-/
theorem enumOrd_isNormal_iff_isClosed (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      isNormal_iff.2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← this]
      exact enumOrd_mem hs _
    rw [h.map_iSup bddAbove_of_small]
    congr
    ext x
    change (enumOrdOrderIso s hs _).val = f x
    rw [OrderIso.apply_symm_apply]
  · have := csSup_mem_closure (ha.nonempty_Iio.image (enumOrd s)) bddAbove_of_small
    have := h.closure_eq ▸ closure_mono (t := s) ?_ this
    · apply (Set.image_subset_range ..).trans_eq
      rw [range_enumOrd hs]
    · apply (enumOrd_le_of_forall_lt this _).trans
      · apply csSup_le'
        grind [upperBounds]
      · exact fun b hb ↦ (enumOrd_strictMono hs (lt_add_one b)).trans_le <|
          le_csSup bddAbove_of_small <| Set.mem_image_of_mem _ (ha.add_one_lt hb)

open Set Filter Set.Notation

/-- An ordinal is an accumulation point of a set of ordinals if it is positive and there
are elements in the set arbitrarily close to the ordinal from below. -/
@[deprecated AccPt (since := "2026-05-24")]
/-
**Ordinal.IsAcc** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：IsAcc (o : Ordinal) (S : Set Ordinal) : Prop
参数：o : Ordinal；S : Set Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordinal is an accumulation point of a set of ordinals if it is positive and t
here
are elements in the set arbitrarily close to the ordinal from below.
-/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  AccPt o (𝓟 S)

/-- A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal. -/
@[deprecated IsClosed (since := "2026-05-24")]
/-
**Ordinal.IsClosedBelow** 是 Mathlib 中的一个定义，位于命名空间 `Ordinal`。
形式化陈述：IsClosedBelow (S : Set Ordinal) (o : Ordinal) : Prop
参数：S : Set Ordinal；o : Ordinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal.
-/
def IsClosedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed (Iio o ↓∩ S)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/-
**Ordinal.isAcc_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S ↔ o != 0 ∧ forall p 
< o, (S inter Ioo p o).Nonempty
参数：o : Ordinal；S : Set Ordinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SuccOrder.accPt_principal`：accPt_principal {a : α} {s : Set α} : AccPt a
 (𝓟 s) ↔ ¬ IsMin a ∧ forall b < a, (s inter Ioo b a).Nonempty
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_eq_zero'`：∀ {α : Type u} [inst : AddMonoid α] [inst_1 : LinearOrder 
α] [CanonicallyOrderedAdd α] [inst_3 : OrderBot α], ⊥ = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S ↔
    o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty := by
  apply SuccOrder.accPt_principal.trans
  simp

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/-
**Ordinal.IsAcc.forall_lt** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsAcc`。
形式化陈述：∀ {o : Ordinal.{u_1}} {S : Set Ordinal.{u_1}}, o.IsAcc S → ∀ p < o, (S ∩ S
et.Ioo p o).Nonempty
参数：S ∩ Set.Ioo p o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isAcc_iff`：isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S
 ↔ o != 0 ∧ forall p < o, (S inter Ioo p o).Nonempty
-/
theorem IsAcc.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := ((isAcc_iff _ _).mp h).2

@[deprecated AccPt.not_isMin (since := "2026-05-24")]
/-
**Ordinal.IsAcc.pos** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsAcc`。
形式化陈述：∀ {o : Ordinal.{u_1}} {S : Set Ordinal.{u_1}}, o.IsAcc S → 0 < o
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ordinal.isAcc_iff`：isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S
 ↔ o != 0 ∧ forall p < o, (S inter Ioo p o).Nonempty
-/
theorem IsAcc.pos {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    0 < o := pos_iff_ne_zero.mpr ((isAcc_iff _ _).mp h).1

@[deprecated AccPt.isSuccLimit (since := "2026-05-24")]
/-
**Ordinal.IsAcc.isSuccLimit** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsAcc`。
形式化陈述：∀ {o : Ordinal.{u_1}} {S : Set Ordinal.{u_1}}, o.IsAcc S → Order.IsSuccLim
it o
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AccPt.isSuccLimit`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Top
ologicalSpace α] [OrderTopology α] [SuccOrder α] [NoMaxOrder α]   {a : α} {s : S
et α}, …
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Ordinal.instNoMaxOrder`：NoMaxOrder Ordinal.{u_1}
-/
theorem IsAcc.isSuccLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) : IsSuccLimit o :=
  AccPt.isSuccLimit h

@[deprecated AccPt.mono (since := "2026-05-24")]
/-
**Ordinal.IsAcc.mono** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsAcc`。
形式化陈述：∀ {o : Ordinal.{u_1}} {S T : Set Ordinal.{u_1}}, S ⊆ T → o.IsAcc S → o.IsA
cc T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
-/
theorem IsAcc.mono {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) : o.IsAcc T :=
  AccPt.mono ho (monotone_principal h)

@[deprecated SuccOrder.accPt_principal (since := "2026-05-24")]
/-
**Ordinal.IsAcc.inter_Ioo_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsAcc`。
形式化陈述：∀ {o : Ordinal.{u_1}} {S : Set Ordinal.{u_1}}, o.IsAcc S → ∀ {p : Ordinal.
{u_1}}, p < o → (S ∩ Set.Ioo p o).Nonempty
参数：S ∩ Set.Ioo p o。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsAcc.forall_lt`：∀ {o : Ordinal.{u_1}} {S : Set Ordinal.{u_1}}, 
o.IsAcc S → ∀ p < o, (S ∩ Set.Ioo p o).Nonempty
-/
theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := hS.forall_lt p hp

@[deprecated IsOpenEmbedding.accPt_comap_iff (since := "2026-03-30")]
/-
**Ordinal.accPt_subtype** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：accPt_subtype {p o : Ordinal} (S : Set Ordinal) (hpo : p < o) : AccPt p (𝓟
 S) ↔ AccPt ⟨p, hpo⟩ (𝓟 (Iio o ↓inter S))
参数：S : Set Ordinal；hpo : p < o。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.comap_principal`：comap_principal {t : Set β} : comap m (𝓟 t) = 𝓟 
(m ⁻¹' t)
· 使用定理 `Topology.IsOpenEmbedding.accPt_comap_iff`：∀ {X : Type u_1} {Y : Type u_2
} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topol
ogy.IsOpenEmbedding f → ∀ {x :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem accPt_subtype {p o : Ordinal} (S : Set Ordinal) (hpo : p < o) :
    AccPt p (𝓟 S) ↔ AccPt ⟨p, hpo⟩ (𝓟 (Iio o ↓∩ S)) := by
  rw [← comap_principal, isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
/-
**Ordinal.isClosedBelow_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal`。
形式化陈述：isClosedBelow_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelow S o ↔ fo
rall p < o, IsAcc p S -> p in S
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Topology.IsOpenEmbedding.accPt_comap_iff`：∀ {X : Type u_1} {Y : Type u_2
} {f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topol
ogy.IsOpenEmbedding f → ∀ {x :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `isOpen_Iio`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : LinearO
rder α] [ClosedIciTopology α] {a : α}, IsOpen (Set.Iio a)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `Ordinal.instOrderTopology`：OrderTopology Ordinal.{u}
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isClosedBelow_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelow S o ↔
    ∀ p < o, IsAcc p S → p ∈ S := by
  simp [IsClosedBelow, IsAcc, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

@[deprecated isClosed_iff_accPt (since := "2026-05-24")]
alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff

@[deprecated isClosed_sInter (since := "2026-05-24")]
/-
**Ordinal.IsClosedBelow.sInter** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsClosedBelow`
。
形式化陈述：∀ {o : Ordinal.{u_1}} {S : Set (Set Ordinal.{u_1})},   (∀ C ∈ S, Ordinal.I
sClosedBelow C o) → Ordinal.IsClosedBelow (⋂₀ S) o
参数：Set Ordinal.{u_1}；∀ C ∈ S, Ordinal.IsClosedBelow C o；⋂₀ S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ordinal.isClosedBelow_iff`：isClosedBelow_iff {S : Set Ordinal} {o : Ordi
nal} : IsClosedBelow S o ↔ forall p < o, IsAcc p S -> p in S
· 使用定理 `Ordinal.IsClosedBelow.forall_lt`：∀ {S : Set Ordinal.{u_1}} {o : Ordinal.
{u_1}}, Ordinal.IsClosedBelow S o → ∀ p < o, p.IsAcc S → p ∈ S
· 使用定理 `AccPt.mono`：AccPt.mono {F G : Filter X} (h : AccPt x F) (hFG : F <= G) :
 AccPt x G
· 使用定理 `Filter.monotone_principal`：monotone_principal : Monotone (𝓟 : Set α -> F
ilter α)
· 使用定理 `Set.sInter_subset_of_mem`：sInter_subset_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : ⋂₀ S subseteq t
-/
theorem IsClosedBelow.sInter {o : Ordinal} {S : Set (Set Ordinal)}
    (h : ∀ C ∈ S, IsClosedBelow C o) : IsClosedBelow (⋂₀ S) o := by
  rw [isClosedBelow_iff]
  exact fun p plto pAcc C CmemS ↦ (h C CmemS).forall_lt p plto <|
    AccPt.mono pAcc (monotone_principal (sInter_subset_of_mem CmemS))

@[deprecated isClosed_iInter (since := "2026-05-24")]
/-
**Ordinal.IsClosedBelow.iInter** 是 Mathlib 中的一个定理，位于命名空间 `Ordinal.IsClosedBelow`
。
形式化陈述：∀ {ι : Type u} {f : ι → Set Ordinal.{u_1}} {o : Ordinal.{u_1}},   (∀ (i : 
ι), Ordinal.IsClosedBelow (f i) o) → Ordinal.IsClosedBelow (⋂ i, f i) o
参数：∀ (i : ι), Ordinal.IsClosedBelow (f i) o；⋂ i, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ordinal.IsClosedBelow.sInter`：∀ {o : Ordinal.{u_1}} {S : Set (Set Ordina
l.{u_1})},   (∀ C ∈ S, Ordinal.IsClosedBelow C o) → Ordinal.IsClosedBelow (⋂₀ S)
 o
-/
theorem IsClosedBelow.iInter {ι : Type u} {f : ι → Set Ordinal} {o : Ordinal}
    (h : ∀ i, IsClosedBelow (f i) o) : IsClosedBelow (⋂ i, f i) o :=
  IsClosedBelow.sInter fun _ ⟨i, hi⟩ ↦ hi ▸ (h i)

end Ordinal

