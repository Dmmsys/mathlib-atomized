/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Data.List.AList

/-!
# Connections between `Finsupp` and `AList`

## Main definitions

* `Finsupp.toAList`
* `AList.lookupFinsupp`: converts an association list into a finitely supported function
  via `AList.lookup`, sending absent keys to zero.

-/

@[expose] public section


namespace Finsupp

variable {α M : Type*} [Zero M]

/-- Produce an association list for the finsupp over its support using choice. -/
@[simps]
/-
**Finsupp.toAList** 是 Mathlib 中的一个定义，位于命名空间 `Finsupp`。
形式化陈述：toAList (f : α ->₀ M) : AList fun _x : α => M
参数：f : α ->₀ M。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produce an association list for the finsupp over its support using choice.
-/
noncomputable def toAList (f : α →₀ M) : AList fun _x : α => M :=
  ⟨f.graph.toList.map Prod.toSigma,
    by
      rw [List.NodupKeys, List.keys, List.map_map, Prod.fst_comp_toSigma, List.nodup_map_iff_inj_on]
      · rintro ⟨b, m⟩ hb ⟨c, n⟩ hc (rfl : b = c)
        rw [Finset.mem_toList, Finsupp.mem_graph_iff] at hb hc
        dsimp at hb hc
        rw [← hc.1, hb.1]
      · apply Finset.nodup_toList⟩

@[simp]
/-
**Finsupp.toAList_keys_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：toAList_keys_toFinset [DecidableEq α] (f : α ->₀ M) : f.toAList.keys.toFin
set = f.support
参数：f : α ->₀ M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toAList_keys_toFinset [DecidableEq α] (f : α →₀ M) :
    f.toAList.keys.toFinset = f.support := by
  ext
  simp [toAList, AList.keys, List.keys]

@[simp]
/-
**Finsupp.mem_toAlist** 是 Mathlib 中的一个定理，位于命名空间 `Finsupp`。
形式化陈述：mem_toAlist {f : α ->₀ M} {x : α} : x in f.toAList ↔ f x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.mem_keys`：mem_keys {a : α} {s : AList β} : a in s ↔ a in s.keys
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.mem_toFinset`：mem_toFinset : a in l.toFinset ↔ a in l
· 使用定理 `Finsupp.toAList_keys_toFinset`：toAList_keys_toFinset [DecidableEq α] (f 
: α ->₀ M) : f.toAList.keys.toFinset = f.support
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toAlist {f : α →₀ M} {x : α} : x ∈ f.toAList ↔ f x ≠ 0 := by
  classical rw [AList.mem_keys, ← List.mem_toFinset, toAList_keys_toFinset, mem_support_iff]

end Finsupp

namespace AList

variable {α M : Type*} [Zero M]

open List

/-- Converts an association list into a finitely supported function via `AList.lookup`, sending
absent keys to zero. -/
/-
**AList.lookupFinsupp** 是 Mathlib 中的一个定义，位于命名空间 `AList`。
形式化陈述：lookupFinsupp (l : AList fun _x : α => M) : α ->₀ M where support
参数：l : AList fun _x : α => M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts an association list into a finitely supported function via `AList.looku
p`, sending
absent keys to zero.
-/
noncomputable def lookupFinsupp (l : AList fun _x : α => M) : α →₀ M where
  support := by
    haveI := Classical.decEq α; haveI := Classical.decEq M
    exact (l.1.filter fun x => Sigma.snd x ≠ 0).keys.toFinset
  toFun a :=
    haveI := Classical.decEq α
    (l.lookup a).getD 0
  mem_support_toFun a := by
    classical
      simp_rw [mem_toFinset, List.mem_keys, List.mem_filter, ← mem_lookup_iff]
      cases lookup a l <;> simp

@[simp]
/-
**AList.lookupFinsupp_apply** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookupFinsupp_apply [DecidableEq α] (l : AList fun _x : α => M) (a : α) : 
l.lookupFinsupp a = (l.lookup a).getD 0
参数：l : AList fun _x : α => M；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
-/
theorem lookupFinsupp_apply [DecidableEq α] (l : AList fun _x : α => M) (a : α) :
    l.lookupFinsupp a = (l.lookup a).getD 0 := by
  simp only [lookupFinsupp, ne_eq, Finsupp.coe_mk]
  congr

@[simp]
/-
**AList.lookupFinsupp_support** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookupFinsupp_support [DecidableEq α] [DecidableEq M] (l : AList fun _x : 
α => M) : l.lookupFinsupp.support = (l.1.filter fun x => Sigma.snd x != 0).keys.
toFinset
参数：l : AList fun _x : α => M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Lean.Meta.instFastSubsingletonForall`：∀ {α : Sort u} {β : α → Sort v} [i
nst : ∀ (x : α), Meta.FastSubsingleton (β x)], Meta.FastSubsingleton ((x : α) → 
β x)
· 使用定理 `Lean.Meta.instFastSubsingletonDecidable`：∀ {p : Prop}, Meta.FastSubsingl
eton (Decidable p)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lookupFinsupp_support [DecidableEq α] [DecidableEq M] (l : AList fun _x : α => M) :
    l.lookupFinsupp.support = (l.1.filter fun x => Sigma.snd x ≠ 0).keys.toFinset := by
  dsimp only [lookupFinsupp]
  congr!
/-
**AList.lookupFinsupp_eq_iff_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookupFinsupp_eq_iff_of_ne_zero [DecidableEq α] {l : AList fun _x : α => M
} {a : α} {x : M} (hx : x != 0) : l.lookupFinsupp a = x ↔ x in l.lookup a
参数：hx : x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.lookupFinsupp_apply`：lookupFinsupp_apply [DecidableEq α] (l : ALis
t fun _x : α => M) (a : α) : l.lookupFinsupp a = (l.lookup a).getD 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem lookupFinsupp_eq_iff_of_ne_zero [DecidableEq α] {l : AList fun _x : α => M} {a : α} {x : M}
    (hx : x ≠ 0) : l.lookupFinsupp a = x ↔ x ∈ l.lookup a := by
  rw [lookupFinsupp_apply]
  rcases lookup a l with - | m <;> simp [hx.symm]
/-
**AList.lookupFinsupp_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookupFinsupp_eq_zero_iff [DecidableEq α] {l : AList fun _x : α => M} {a :
 α} : l.lookupFinsupp a = 0 ↔ a ∉ l ∨ (0 : M) in l.lookup a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.lookupFinsupp_apply`：lookupFinsupp_apply [DecidableEq α] (l : ALis
t fun _x : α => M) (a : α) : l.lookupFinsupp a = (l.lookup a).getD 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AList.lookup_eq_none`：lookup_eq_none {a : α} {s : AList β} : lookup a s 
= none ↔ a ∉ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
theorem lookupFinsupp_eq_zero_iff [DecidableEq α] {l : AList fun _x : α => M} {a : α} :
    l.lookupFinsupp a = 0 ↔ a ∉ l ∨ (0 : M) ∈ l.lookup a := by
  rw [lookupFinsupp_apply, ← lookup_eq_none]
  rcases lookup a l with - | m <;> simp

@[simp]
/-
**AList.empty_lookupFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：empty_lookupFinsupp : lookupFinsupp (∅ : AList fun _x : α => M) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem empty_lookupFinsupp : lookupFinsupp (∅ : AList fun _x : α => M) = 0 := rfl

@[simp]
/-
**AList.insert_lookupFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：insert_lookupFinsupp [DecidableEq α] (l : AList fun _x : α => M) (a : α) (
m : M) : (l.insert a m).lookupFinsupp = l.lookupFinsupp.update a m
参数：l : AList fun _x : α => M；a : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.lookupFinsupp_apply`：lookupFinsupp_apply [DecidableEq α] (l : ALis
t fun _x : α => M) (a : α) : l.lookupFinsupp a = (l.lookup a).getD 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AList.lookup_insert`：lookup_insert {a} {b : β a} (s : AList β) : lookup 
a (insert a b s) = some b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Finsupp.coe_update`：coe_update [DecidableEq α] : (f.update a b : α -> M)
 = Function.update f a b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AList.lookup_insert_ne`：lookup_insert_ne {a a'} {b' : β a'} {s : AList β
} (h : a != a') : lookup a (insert a' b' s) = lookup a s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
-/
theorem insert_lookupFinsupp [DecidableEq α] (l : AList fun _x : α => M) (a : α) (m : M) :
    (l.insert a m).lookupFinsupp = l.lookupFinsupp.update a m := by
  ext b
  by_cases h : b = a <;> simp [h]

@[simp]
/-
**AList.singleton_lookupFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：singleton_lookupFinsupp (a : α) (m : M) : (singleton a m).lookupFinsupp = 
Finsupp.single a m
参数：a : α；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AList.insert_lookupFinsupp`：insert_lookupFinsupp [DecidableEq α] (l : AL
ist fun _x : α => M) (a : α) (m : M) : (l.insert a m).lookupFinsupp = l.lookupFi
nsupp.update a m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem singleton_lookupFinsupp (a : α) (m : M) :
    (singleton a m).lookupFinsupp = Finsupp.single a m := by
  classical
  simp [← AList.insert_empty]

@[simp]
/-
**AList._root_.Finsupp.toAList_lookupFinsupp** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Finsupp.toAList_lookupFinsupp (f : α →₀ M) : f.toAList.lookupFinsupp = f := by
  ext a
  classical
    by_cases h : f a = 0
    · suffices f.toAList.lookup a = none by simp [h, this]
      simp [lookup_eq_none, h]
    · suffices f.toAList.lookup a = some (f a) by simp [this]
      apply mem_lookup_iff.2
      simpa using h
/-
**AList.lookupFinsupp_surjective** 是 Mathlib 中的一个定理，位于命名空间 `AList`。
形式化陈述：lookupFinsupp_surjective : Function.Surjective (@lookupFinsupp α M _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.toAList_lookupFinsupp`：∀ {α : Type u_1} {M : Type u_2} [inst : Z
ero M] (f : α →₀ M), f.toAList.lookupFinsupp = f
-/
theorem lookupFinsupp_surjective : Function.Surjective (@lookupFinsupp α M _) := fun f =>
  ⟨_, Finsupp.toAList_lookupFinsupp f⟩

end AList

