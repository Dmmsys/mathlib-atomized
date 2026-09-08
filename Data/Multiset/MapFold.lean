/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Multiset.Replicate
public import Mathlib.Data.Set.List

/-!
# Mapping and folding multisets

## Main definitions

* `Multiset.map`: `map f s` applies `f` to each element of `s`.
* `Multiset.foldl`: `foldl f b s` picks elements out of `s` and applies `f (f ... b x₁) x₂`.
* `Multiset.foldr`: `foldr f b s` picks elements out of `s` and applies `f x₁ (f ... x₂ b)`.

## TODO

Many lemmas about `Multiset.map` are proven in `Mathlib/Data/Multiset/Filter.lean`:
should we switch the import direction?

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.map` -/


/-- `map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`. -/
/-
**Multiset.map** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：map (f : α -> β) (s : Multiset α) : Multiset β
参数：f : α -> β；s : Multiset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map f s` is the lift of the list `map` operation. The multiplicity
  of `b` in `map f s` is the number of `a ∈ s` (counting multiplicity)
  such that `f a = b`.
-/
def map (f : α → β) (s : Multiset α) : Multiset β :=
  Quot.liftOn s (fun l : List α => (l.map f : Multiset β)) fun _l₁ _l₂ p => Quot.sound (p.map f)

@[congr]
/-
**Multiset.map_congr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_congr {f g : α -> β} {s t : Multiset α} : s = t -> (forall x in t, f x
 = g x) -> map f s = map g t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
-/
theorem map_congr {f g : α → β} {s t : Multiset α} :
    s = t → (∀ x ∈ t, f x = g x) → map f s = map g t := by
  rintro rfl h
  induction s using Quot.inductionOn
  exact congr_arg _ (List.map_congr_left h)
/-
**Multiset.map_hcongr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_hcongr {β' : Type v} {m : Multiset α} {f : α -> β} {f' : α -> β'} (h :
 β = β') (hf : forall a in m, f a ≍ f' a) : map f m ≍ map f' m
参数：h : β = β'；hf : forall a in m, f a ≍ f' a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_hcongr {β' : Type v} {m : Multiset α} {f : α → β} {f' : α → β'} (h : β = β')
    (hf : ∀ a ∈ m, f a ≍ f' a) : map f m ≍ map f' m := by
  subst h; simp at hf
  simp [map_congr rfl hf]
/-
**Multiset.forall_mem_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：forall_mem_map_iff {f : α -> β} {p : β -> Prop} {s : Multiset α} : (forall
 y in s.map f, p y) ↔ forall x in s, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `List.forall_mem_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : Li
st α} {P : β → Prop}, (∀ i ∈ List.map f l, P i) ↔ ∀ j ∈ l, P (f j)
-/
theorem forall_mem_map_iff {f : α → β} {p : β → Prop} {s : Multiset α} :
    (∀ y ∈ s.map f, p y) ↔ ∀ x ∈ s, p (f x) :=
  Quotient.inductionOn' s fun _L => List.forall_mem_map
/-
**Multiset.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α), Multiset.map f ↑l 
= ↑(List.map f l)
参数：f : α → β；l : List α；List.map f l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma map_coe (f : α → β) (l : List α) : map f l = l.map f := rfl

@[simp]
/-
**Multiset.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_zero (f : α -> β) : map f 0 = 0
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_zero (f : α → β) : map f 0 = 0 :=
  rfl

@[simp]
/-
**Multiset.map_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s
参数：f : α -> β；a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem map_cons (f : α → β) (a s) : map f (a ::ₘ s) = f a ::ₘ map f s :=
  Quot.inductionOn s fun _l => rfl
/-
**Multiset.map_comp_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_comp_cons (f : α -> β) (t) : map f ∘ cons t = cons (f t) ∘ map f
参数：f : α -> β；t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_cons (f : α → β) (t) : map f ∘ cons t = cons (f t) ∘ map f := by
  ext
  simp

@[simp]
/-
**Multiset.map_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_singleton (f : α -> β) (a : α) : ({a} : Multiset α).map f = {f a}
参数：f : α -> β；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_singleton (f : α → β) (a : α) : ({a} : Multiset α).map f = {f a} :=
  rfl

@[simp]
/-
**Multiset.map_replicate** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_replicate (f : α -> β) (k : Nat) (a : α) : (replicate k a).map f = rep
licate k (f a)
参数：f : α -> β；k : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {α_1 : Type u_2} {f
 : α → α_1},   List.map f (List.replicate n a) = List.replicate n (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_replicate (f : α → β) (k : ℕ) (a : α) : (replicate k a).map f = replicate k (f a) := by
  simp only [← coe_replicate, map_coe, List.map_replicate]

@[simp]
/-
**Multiset.map_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_add (f : α -> β) (s t) : map f (s + t) = map f s + map f t
参数：f : α -> β；s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l₁ l₂ : Li
st α}, List.map f (l₁ ++ l₂) = List.map f l₁ ++ List.map f l₂
-/
theorem map_add (f : α → β) (s t) : map f (s + t) = map f s + map f t :=
  Quotient.inductionOn₂ s t fun _l₁ _l₂ => congr_arg _ map_append

/-- If each element of `s : Multiset α` can be lifted to `β`, then `s` can be lifted to
`Multiset β`. -/
/-
**Multiset.canLift** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：canLift (c) (p) [CanLift α β c p] : CanLift (Multiset α) (Multiset β) (map
 c) fun s => forall x in s, p x where prf
参数：c；p。
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)

--- 原说明 ---
If each element of `s : Multiset α` can be lifted to `β`, then `s` can be lifted
 to
`Multiset β`.
-/
instance canLift (c) (p) [CanLift α β c p] :
    CanLift (Multiset α) (Multiset β) (map c) fun s => ∀ x ∈ s, p x where
  prf := by
    rintro ⟨l⟩ hl
    lift l to List β using hl
    exact ⟨l, map_coe _ _⟩

@[simp]
/-
**Multiset.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in map f s ↔ exists a, a
 in s ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
-/
theorem mem_map {f : α → β} {b : β} {s : Multiset α} : b ∈ map f s ↔ ∃ a, a ∈ s ∧ f a = b :=
  Quot.inductionOn s fun _l => List.mem_map

@[simp]
/-
**Multiset.card_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_map (f : α -> β) (s) : card (map f s) = card s
参数：f : α -> β；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
-/
theorem card_map (f : α → β) (s) : card (map f s) = card s :=
  Quot.inductionOn s fun _ => length_map _

@[simp]
/-
**Multiset.map_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_eq_zero {s : Multiset α} {f : α -> β} : s.map f = 0 ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_eq_zero {s : Multiset α} {f : α → β} : s.map f = 0 ↔ s = 0 := by
  rw [← Multiset.card_eq_zero, Multiset.card_map, Multiset.card_eq_zero]

@[simp]
/-
**Multiset.zero_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：zero_eq_map {s : Multiset α} {f : α -> β} : 0 = s.map f ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Multiset.map_eq_zero`：map_eq_zero {s : Multiset α} {f : α -> β} : s.map 
f = 0 ↔ s = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem zero_eq_map {s : Multiset α} {f : α → β} : 0 = s.map f ↔ s = 0 := by
  rw [eq_comm, map_eq_zero]
/-
**Multiset.mem_map_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_map_of_mem (f : α -> β) {a : α} {s : Multiset α} (h : a in s) : f a in
 map f s
参数：f : α -> β；h : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem mem_map_of_mem (f : α → β) {a : α} {s : Multiset α} (h : a ∈ s) : f a ∈ map f s :=
  mem_map.2 ⟨_, h, rfl⟩
/-
**Multiset.map_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_eq_singleton {f : α -> β} {s : Multiset α} {b : β} : map f s = {b} ↔ e
xists a : α, s = {a} ∧ f a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_eq_one`：card_eq_one {s : Multiset α} : card s = 1 ↔ exists
 a, s = {a}
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
· 使用定理 `Multiset.map_singleton`：map_singleton (f : α -> β) (a : α) : ({a} : Mult
iset α).map f = {f a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_eq_singleton {f : α → β} {s : Multiset α} {b : β} :
    map f s = {b} ↔ ∃ a : α, s = {a} ∧ f a = b := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ : ∃ a, s = {a} := by rw [← card_eq_one, ← card_map, h, card_singleton]
    refine ⟨a, ha, ?_⟩
    rw [← mem_singleton, ← h, ha, map_singleton, mem_singleton]
  · rintro ⟨a, rfl, rfl⟩
    simp
/-
**Multiset.map_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_eq_cons [DecidableEq α] (f : α -> β) (s : Multiset α) (t : Multiset β)
 (b : β) : (exists a in s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t
参数：f : α -> β；s : Multiset α；t : Multiset β；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.cons_erase`：cons_erase {s : Multiset α} {a : α} : a in s -> a :
:ₘ s.erase a = s
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Multiset.exists_cons_of_mem`：exists_cons_of_mem {s : Multiset α} {a : α}
 : a in s -> exists t, s = a ::ₘ t
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `Multiset.cons_inj_right`：cons_inj_right (a : α) : forall {s t : Multiset
 α}, a ::ₘ s = a ::ₘ t ↔ s = t
-/
theorem map_eq_cons [DecidableEq α] (f : α → β) (s : Multiset α) (t : Multiset β) (b : β) :
    (∃ a ∈ s, f a = b ∧ (s.erase a).map f = t) ↔ s.map f = b ::ₘ t := by
  constructor
  · rintro ⟨a, ha, rfl, rfl⟩
    rw [← map_cons, Multiset.cons_erase ha]
  · intro h
    have : b ∈ s.map f := by
      rw [h]
      exact mem_cons_self _ _
    obtain ⟨a, h1, rfl⟩ := mem_map.mp this
    obtain ⟨u, rfl⟩ := exists_cons_of_mem h1
    rw [map_cons, cons_inj_right] at h
    refine ⟨a, mem_cons_self _ _, rfl, ?_⟩
    rw [Multiset.erase_cons_head, h]

@[simp 1100]
/-
**Multiset.mem_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_map_of_injective {f : α -> β} (H : Function.Injective f) {a : α} {s : 
Multiset α} : f a in map f s ↔ a in s
参数：H : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `List.mem_map_of_injective`：mem_map_of_injective {f : α -> β} (H : Inject
ive f) {a : α} {l : List α} : f a in map f l ↔ a in l
-/
theorem mem_map_of_injective {f : α → β} (H : Function.Injective f) {a : α} {s : Multiset α} :
    f a ∈ map f s ↔ a ∈ s :=
  Quot.inductionOn s fun _l => List.mem_map_of_injective H

@[simp]
/-
**Multiset.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : map g (map f s) = map
 (g ∘ f) s
参数：g : β -> γ；f : α -> β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
-/
theorem map_map (g : β → γ) (f : α → β) (s : Multiset α) : map g (map f s) = map (g ∘ f) s :=
  Quot.inductionOn s fun _l => congr_arg _ List.map_map
/-
**Multiset.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_id (s : Multiset α) : map id s = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_id`：∀ {α : Type u_1} (l : List α), List.map id l = l
-/
theorem map_id (s : Multiset α) : map id s = s :=
  Quot.inductionOn s fun _l => congr_arg _ <| List.map_id _

@[simp]
/-
**Multiset.map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_id' (s : Multiset α) : map (fun x => x) s = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem map_id' (s : Multiset α) : map (fun x => x) s = s :=
  map_id s

-- `simp`-normal form lemma is `map_const'`
/-
**Multiset.map_const** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_const (s : Multiset α) (b : β) : map (const α b) s = replicate (card s
) b
参数：s : Multiset α；b : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
-/
theorem map_const (s : Multiset α) (b : β) : map (const α b) s = replicate (card s) b :=
  Quot.inductionOn s fun _ => congr_arg _ List.map_const'
/-
**Multiset.map_const'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b : β), Multiset.map (fun 
x => b) s = Multiset.replicate s.card b
参数：s : Multiset α；b : β；fun x => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_const`：map_const (s : Multiset α) (b : β) : map (const α b)
 s = replicate (card s) b
-/
@[simp] theorem map_const' (s : Multiset α) (b : β) : map (fun _ ↦ b) s = replicate (card s) b :=
  map_const _ _
/-
**Multiset.eq_of_mem_map_const** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ in map (Function.cons
t α b₂) l) : b₁ = b₂
参数：h : b₁ in map (Function.const α b₂) l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_const`：map_const (s : Multiset α) (b : β) : map (const α b)
 s = replicate (card s) b
-/
theorem eq_of_mem_map_const {b₁ b₂ : β} {l : List α} (h : b₁ ∈ map (Function.const α b₂) l) :
    b₁ = b₂ :=
  eq_of_mem_replicate (n := card (l : Multiset α)) <| by rwa [map_const] at h

@[simp, gcongr]
/-
**Multiset.map_le_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_le_map {f : α -> β} {s t : Multiset α} (h : s <= t) : map f s <= map f
 t
参数：h : s <= t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.leInductionOn`：leInductionOn {C : Multiset α -> Multiset α -> P
rop} {s t : Multiset α} (h : s <= t) (H : forall {l₁ l₂ : List α}, l₁ <+ l₂ -> C
 l₁ l₂) : C …
· 使用定理 `List.Sublist.subperm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.Subperm l₂
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
-/
theorem map_le_map {f : α → β} {s t : Multiset α} (h : s ≤ t) : map f s ≤ map f t :=
  leInductionOn h fun h => (h.map f).subperm

@[simp, gcongr]
/-
**Multiset.map_lt_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_lt_map {f : α -> β} {s t : Multiset α} (h : s < t) : s.map f < t.map f
参数：h : s < t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.lt_of_not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ 
b → ¬b ≤ a → a < b
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Multiset.eq_of_le_of_card_le`：eq_of_le_of_card_le {s t : Multiset α} (h 
: s <= t) : card t <= card s -> s = t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.card_le_card`：card_le_card {s t : Multiset α} (h : s <= t) : ca
rd s <= card t
-/
theorem map_lt_map {f : α → β} {s t : Multiset α} (h : s < t) : s.map f < t.map f := by
  refine (map_le_map h.le).lt_of_not_ge fun H => h.ne <| eq_of_le_of_card_le h.le ?_
  rw [← s.card_map f, ← t.card_map f]
  exact card_le_card H

@[gcongr]
/-
**Multiset.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_mono (f : α -> β) : Monotone (map f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_le_map`：map_le_map {f : α -> β} {s t : Multiset α} (h : s <
= t) : map f s <= map f t
-/
theorem map_mono (f : α → β) : Monotone (map f) := fun _ _ => map_le_map

@[gcongr]
/-
**Multiset.map_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_strictMono (f : α -> β) : StrictMono (map f)
参数：f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_lt_map`：map_lt_map {f : α -> β} {s t : Multiset α} (h : s <
 t) : s.map f < t.map f
-/
theorem map_strictMono (f : α → β) : StrictMono (map f) := fun _ _ => map_lt_map

@[simp, gcongr]
/-
**Multiset.map_subset_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_subset_map {f : α -> β} {s t : Multiset α} (H : s subseteq t) : map f 
s subseteq map f t
参数：H : s subseteq t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem map_subset_map {f : α → β} {s t : Multiset α} (H : s ⊆ t) : map f s ⊆ map f t := fun _b m =>
  let ⟨a, h, e⟩ := mem_map.1 m
  mem_map.2 ⟨a, H h, e⟩
/-
**Multiset.map_erase** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_erase [DecidableEq α] [DecidableEq β] (f : α -> β) (hf : Function.Inje
ctive f) (x : α) (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x)
参数：f : α -> β；hf : Function.Injective f；x : α；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.erase_cons_tail`：erase_cons_tail {a b : α} (s : Multiset α) (h 
: b != a) : (b ::ₘ s).erase a = b ::ₘ s.erase a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
-/
theorem map_erase [DecidableEq α] [DecidableEq β] (f : α → β) (hf : Function.Injective f) (x : α)
    (s : Multiset α) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  by_cases hxy : y = x
  · cases hxy
    simp
  · rw [s.erase_cons_tail hxy, map_cons, map_cons, (s.map f).erase_cons_tail (hf.ne hxy), ih]
/-
**Multiset.map_erase_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_erase_of_mem [DecidableEq α] [DecidableEq β] (f : α -> β) (s : Multise
t α) {x : α} (h : x in s) : (s.erase x).map f = (s.map f).erase (f x)
参数：f : α -> β；s : Multiset α；h : x in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.erase_of_notMem`：erase_of_notMem {a : α} {s : Multiset α} : a ∉
 s -> s.erase a = s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Multiset.erase_cons_head`：erase_cons_head (a : α) (s : Multiset α) : (a 
::ₘ s).erase a = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Multiset.erase_cons_tail`：erase_cons_tail {a b : α} (s : Multiset α) (h 
: b != a) : (b ::ₘ s).erase a = b ::ₘ s.erase a
· 使用定理 `Multiset.erase_cons_tail_of_mem`：erase_cons_tail_of_mem (h : a in s) : (
b ::ₘ s).erase a = b ::ₘ s.erase a
· 使用定理 `Multiset.mem_map_of_mem`：mem_map_of_mem (f : α -> β) {a : α} {s : Multis
et α} (h : a in s) : f a in map f s
-/
theorem map_erase_of_mem [DecidableEq α] [DecidableEq β] (f : α → β)
    (s : Multiset α) {x : α} (h : x ∈ s) : (s.erase x).map f = (s.map f).erase (f x) := by
  induction s using Multiset.induction_on with | empty => simp | cons y s ih => ?_
  rcases eq_or_ne y x with rfl | hxy
  · simp
  replace h : x ∈ s := by simpa [hxy.symm] using h
  rw [s.erase_cons_tail hxy, map_cons, map_cons, ih h, erase_cons_tail_of_mem (mem_map_of_mem f h)]
/-
**Multiset.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_surjective_of_surjective {f : α -> β} (hf : Function.Surjective f) : F
unction.Surjective (map f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem map_surjective_of_surjective {f : α → β} (hf : Function.Surjective f) :
    Function.Surjective (map f) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, map_zero _⟩
  | cons x s ih =>
    obtain ⟨y, rfl⟩ := hf x
    obtain ⟨t, rfl⟩ := ih
    exact ⟨y ::ₘ t, map_cons _ _ _⟩

/-! ### `Multiset.fold` -/


section foldl

/-- `foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commutative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`. -/
/-
**Multiset.foldl** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：foldl (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α) : β
参数：f : β -> α -> β；b : β；s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldl_eq`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {l₁ 
l₂ : List α} [rcomm : RightCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldl 
f b l₁ =…

--- 原说明 ---
`foldl f H b s` is the lift of the list operation `foldl f b l`,
  which folds `f` over the multiset. It is well defined when `f` is right-commut
ative,
  that is, `f (f b a₁) a₂ = f (f b a₂) a₁`.
-/
def foldl (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldl f b l) fun _l₁ _l₂ p => p.foldl_eq b

variable (f : β → α → β) [RightCommutative f]

@[simp]
/-
**Multiset.foldl_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_zero (b) : foldl f b 0 = b
参数：b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldl_zero (b) : foldl f b 0 = b :=
  rfl

@[simp]
/-
**Multiset.foldl_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f (f b a) s
参数：b a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem foldl_cons (b a s) : foldl f b (a ::ₘ s) = foldl f (f b a) s :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/-
**Multiset.foldl_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_add (b s t) : foldl f b (s + t) = foldl f (foldl f b s) t
参数：b s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.foldl_append`：∀ {α : Type u_1} {β : Type u_2} {f : β → α → β} {b : 
β} {l l' : List α},   List.foldl f b (l ++ l') = List.foldl f (List.foldl f b l)
 l'
-/
theorem foldl_add (b s t) : foldl f b (s + t) = foldl f (foldl f b s) t :=
  Quotient.inductionOn₂ s t fun _ _ => foldl_append

end foldl

section foldr

/-- `foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commutative,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`. -/
/-
**Multiset.foldr** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：foldr (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α) : β
参数：f : α -> β -> β；b : β；s : Multiset α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.foldr_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ 
l₂ : List α} [lcomm : LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f
 b l₁ = …

--- 原说明 ---
`foldr f H b s` is the lift of the list operation `foldr f b l`,
  which folds `f` over the multiset. It is well defined when `f` is left-commuta
tive,
  that is, `f a₁ (f a₂ b) = f a₂ (f a₁ b)`.
-/
def foldr (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) : β :=
  Quot.liftOn s (fun l => List.foldr f b l) fun _l₁ _l₂ p => p.foldr_eq b

variable (f : α → β → β) [LeftCommutative f]

@[simp]
/-
**Multiset.foldr_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_zero (b) : foldr f b 0 = b
参数：b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_zero (b) : foldr f b 0 = b :=
  rfl

@[simp]
/-
**Multiset.foldr_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (foldr f b s)
参数：b a s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
theorem foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (foldr f b s) :=
  Quot.inductionOn s fun _l => rfl

@[simp]
/-
**Multiset.foldr_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_singleton (b a) : foldr f b ({a} : Multiset α) = f a b
参数：b a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem foldr_singleton (b a) : foldr f b ({a} : Multiset α) = f a b :=
  rfl

@[simp]
/-
**Multiset.foldr_add** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_add (b s t) : foldr f b (s + t) = foldr f (foldr f b t) s
参数：b s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `List.foldr_append`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {b : 
β} {l l' : List α},   List.foldr f b (l ++ l') = List.foldr f (List.foldr f b l'
) l
-/
theorem foldr_add (b s t) : foldr f b (s + t) = foldr f (foldr f b t) s :=
  Quotient.inductionOn₂ s t fun _ _ => foldr_append

end foldr

@[simp]
/-
**Multiset.coe_foldr** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_foldr (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α) : fol
dr f b l = l.foldr f b
参数：f : α -> β -> β；b : β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_foldr (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldr f b :=
  rfl

@[simp]
/-
**Multiset.coe_foldl** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_foldl (f : β -> α -> β) [RightCommutative f] (b : β) (l : List α) : fo
ldl f b l = l.foldl f b
参数：f : β -> α -> β；b : β；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_foldl (f : β → α → β) [RightCommutative f] (b : β) (l : List α) :
    foldl f b l = l.foldl f b :=
  rfl
/-
**Multiset.coe_foldr_swap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_foldr_swap (f : α -> β -> β) [LeftCommutative f] (b : β) (l : List α) 
: foldr f b l = l.foldl (fun x y => f y x) b
参数：f : α -> β -> β；b : β；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.coe_reverse`：coe_reverse (l : List α) : (reverse l : Multiset α
) = l
· 使用定理 `List.foldr_reverse`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α 
→ β → β} {b : β},   List.foldr f b l.reverse = List.foldl (fun x y => f y x) b l
-/
theorem coe_foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (l : List α) :
    foldr f b l = l.foldl (fun x y => f y x) b :=
  (congr_arg (foldr f b) (coe_reverse l)).symm.trans foldr_reverse
/-
**Multiset.foldr_swap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_swap (f : α -> β -> β) [LeftCommutative f] (b : β) (s : Multiset α) 
: foldr f b s = foldl (fun x y => f y x) b s
参数：f : α -> β -> β；b : β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `instRightCommutativeOfLeftCommutative`：∀ {α : Sort u} {β : Sort v} {f : 
α → β → β} [h : LeftCommutative f], RightCommutative fun x y => f y x
· 使用定理 `Multiset.coe_foldr_swap`：coe_foldr_swap (f : α -> β -> β) [LeftCommutati
ve f] (b : β) (l : List α) : foldr f b l = l.foldl (fun x y => f y x) b
-/
theorem foldr_swap (f : α → β → β) [LeftCommutative f] (b : β) (s : Multiset α) :
    foldr f b s = foldl (fun x y => f y x) b s :=
  Quot.inductionOn s fun _l => coe_foldr_swap _ _ _
/-
**Multiset.foldl_swap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_swap (f : β -> α -> β) [RightCommutative f] (b : β) (s : Multiset α)
 : foldl f b s = foldr (fun x y => f y x) b s
参数：f : β -> α -> β；b : β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instLeftCommutativeOfRightCommutative`：∀ {α : Sort u} {β : Sort v} {f : 
β → α → β} [h : RightCommutative f], LeftCommutative fun x y => f y x
· 使用定理 `instRightCommutativeOfLeftCommutative`：∀ {α : Sort u} {β : Sort v} {f : 
α → β → β} [h : LeftCommutative f], RightCommutative fun x y => f y x
· 使用定理 `Multiset.foldr_swap`：foldr_swap (f : α -> β -> β) [LeftCommutative f] (b
 : β) (s : Multiset α) : foldr f b s = foldl (fun x y => f y x) b s
-/
theorem foldl_swap (f : β → α → β) [RightCommutative f] (b : β) (s : Multiset α) :
    foldl f b s = foldr (fun x y => f y x) b s :=
  (foldr_swap _ _ _).symm
/-
**Multiset.foldr_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_induction' (f : α -> β -> β) [LeftCommutative f] (x : β) (q : α -> P
rop) (p : β -> Prop) (s : Multiset α) (hpqf : forall a b, q a -> p b -> p (f a b
)) (px : p x) (q_s : forall a in s, q a) : p (foldr f x s)
参数：f : α -> β -> β；x : β；q : α -> Prop；p : β -> Prop；s : Multiset α；hpqf : foral
l a b, q a -> p b -> p (f a b)；px : p x；q_s : forall a in s, q a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction`：∀ {α : Type u_1} {p : Multiset α → Prop},   p 0 → (∀
 (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → ∀ (s : Multiset α), p s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.foldr_cons`：foldr_cons (b a s) : foldr f b (a ::ₘ s) = f a (fol
dr f b s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem foldr_induction' (f : α → β → β) [LeftCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f a b)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldr f x s) := by
  induction s using Multiset.induction with
  | empty => simpa
  | cons a s ihs =>
    simp only [forall_mem_cons, foldr_cons] at q_s ⊢
    exact hpqf _ _ q_s.1 (ihs q_s.2)
/-
**Multiset.foldr_induction** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldr_induction (f : α -> α -> α) [LeftCommutative f] (x : α) (p : α -> Pr
op) (s : Multiset α) (p_f : forall a b, p a -> p b -> p (f a b)) (px : p x) (p_s
 : forall a in s, p a) : p (foldr f x s)
参数：f : α -> α -> α；x : α；p : α -> Prop；s : Multiset α；p_f : forall a b, p a -> p
 b -> p (f a b)；px : p x；p_s : forall a in s, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.foldr_induction'`：foldr_induction' (f : α -> β -> β) [LeftCommu
tative f] (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset α) (hpqf : foral
l a b, q a -> p…
-/
theorem foldr_induction (f : α → α → α) [LeftCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f a b)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldr f x s) :=
  foldr_induction' f x p p s p_f px p_s
/-
**Multiset.foldl_induction'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_induction' (f : β -> α -> β) [RightCommutative f] (x : β) (q : α -> 
Prop) (p : β -> Prop) (s : Multiset α) (hpqf : forall a b, q a -> p b -> p (f b 
a)) (px : p x) (q_s : forall a in s, q a) : p (foldl f x s)
参数：f : β -> α -> β；x : β；q : α -> Prop；p : β -> Prop；s : Multiset α；hpqf : foral
l a b, q a -> p b -> p (f b a)；px : p x；q_s : forall a in s, q a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLeftCommutativeOfRightCommutative`：∀ {α : Sort u} {β : Sort v} {f : 
β → α → β} [h : RightCommutative f], LeftCommutative fun x y => f y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.foldl_swap`：foldl_swap (f : β -> α -> β) [RightCommutative f] (
b : β) (s : Multiset α) : foldl f b s = foldr (fun x y => f y x) b s
· 使用定理 `Multiset.foldr_induction'`：foldr_induction' (f : α -> β -> β) [LeftCommu
tative f] (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset α) (hpqf : foral
l a b, q a -> p…
-/
theorem foldl_induction' (f : β → α → β) [RightCommutative f] (x : β) (q : α → Prop)
    (p : β → Prop) (s : Multiset α) (hpqf : ∀ a b, q a → p b → p (f b a)) (px : p x)
    (q_s : ∀ a ∈ s, q a) : p (foldl f x s) := by
  rw [foldl_swap]
  exact foldr_induction' (fun x y => f y x) x q p s hpqf px q_s
/-
**Multiset.foldl_induction** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：foldl_induction (f : α -> α -> α) [RightCommutative f] (x : α) (p : α -> P
rop) (s : Multiset α) (p_f : forall a b, p a -> p b -> p (f b a)) (px : p x) (p_
s : forall a in s, p a) : p (foldl f x s)
参数：f : α -> α -> α；x : α；p : α -> Prop；s : Multiset α；p_f : forall a b, p a -> p
 b -> p (f b a)；px : p x；p_s : forall a in s, p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.foldl_induction'`：foldl_induction' (f : β -> α -> β) [RightComm
utative f] (x : β) (q : α -> Prop) (p : β -> Prop) (s : Multiset α) (hpqf : fora
ll a b, q a -> …
-/
theorem foldl_induction (f : α → α → α) [RightCommutative f] (x : α) (p : α → Prop)
    (s : Multiset α) (p_f : ∀ a b, p a → p b → p (f b a)) (px : p x) (p_s : ∀ a ∈ s, p a) :
    p (foldl f x s) :=
  foldl_induction' f x p p s p_f px p_s

/-! ### Map for partial functions -/

/-
**Multiset.pmap_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Multiset α) : forall H, @pma
p _ _ p (fun a _ => f a) s H = map f s
参数：p : α -> Prop；f : α -> β；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l

--- 原说明 ---
### Map for partial functions
-/
theorem pmap_eq_map (p : α → Prop) (f : α → β) (s : Multiset α) :
    ∀ H, @pmap _ _ p (fun a _ => f a) s H = map f s :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.pmap_eq_map H
/-
**Multiset.map_pmap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_pmap {p : α -> Prop} (g : β -> γ) (f : forall a, p a -> β) (s) : foral
l H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H
参数：g : β -> γ；f : forall a, p a -> β；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.map_pmap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → P
rop} {g : β → γ} {f : (a : α) → p a → β} {l : List α}   (H : ∀ a ∈ l, p a), List
.ma…
-/
theorem map_pmap {p : α → Prop} (g : β → γ) (f : ∀ a, p a → β) (s) :
    ∀ H, map g (pmap f s H) = pmap (fun a h => g (f a h)) s H :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.map_pmap H
/-
**Multiset.pmap_eq_map_attach** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pmap_eq_map_attach {p : α -> Prop} (f : forall a, p a -> β) (s) : forall H
, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2)
参数：f : forall a, p a -> β；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.pmap_eq_map_attach`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} 
{f : (a : α) → p a → β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap f l H = Lis
t.map (fun x …
-/
theorem pmap_eq_map_attach {p : α → Prop} (f : ∀ a, p a → β) (s) :
    ∀ H, pmap f s H = s.attach.map fun x => f x.1 (H _ x.2) :=
  Quot.inductionOn s fun _ H => congr_arg _ <| List.pmap_eq_map_attach H

@[simp]
/-
**Multiset.attach_map_val'** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_map_val' (s : Multiset α) (f : α -> β) : (s.attach.map fun i => f i
.val) = s.map f
参数：s : Multiset α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `List.attach_map_val`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α
 → β}, List.map (fun i => f ↑i) l.attach = List.map f l
-/
theorem attach_map_val' (s : Multiset α) (f : α → β) : (s.attach.map fun i => f i.val) = s.map f :=
  Quot.inductionOn s fun _ => congr_arg _ List.attach_map_val

@[simp]
/-
**Multiset.attach_map_val** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.attach_map_val'`：attach_map_val' (s : Multiset α) (f : α -> β) 
: (s.attach.map fun i => f i.val) = s.map f
· 使用定理 `Multiset.map_id`：map_id (s : Multiset α) : map id s = s
-/
theorem attach_map_val (s : Multiset α) : s.attach.map Subtype.val = s :=
  (attach_map_val' _ _).trans s.map_id

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.attach_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：attach_cons (a : α) (m : Multiset α) : (a ::ₘ m).attach = ⟨a, mem_cons_sel
f a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩
参数：a : α；m : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_pmap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {p : α → P
rop} {g : β → γ} {f : (a : α) → p a → β} {l : List α}   (H : ∀ a ∈ l, p a), List
.ma…
· 使用定理 `List.pmap_congr_left`：∀ {α : Type u_1} {β : Type u_2} {p q : α → Prop} {
f : (a : α) → p a → β} {g : (a : α) → q a → β} (l : List α)   {H₁ : ∀ a ∈ l, p a
} {H₂ : ∀ …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem attach_cons (a : α) (m : Multiset α) :
    (a ::ₘ m).attach =
      ⟨a, mem_cons_self a m⟩ ::ₘ m.attach.map fun p => ⟨p.1, mem_cons_of_mem p.2⟩ :=
  Quotient.inductionOn m fun l =>
    congr_arg _ <|
      congr_arg (List.cons _) <| by
        rw [List.map_pmap]; exact List.pmap_congr_left _ fun _ _ _ _ => Subtype.ext rfl

section

variable [DecidableEq α] {s t u : Multiset α}

/-
**Multiset.erase_attach_map_val** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：erase_attach_map_val (s : Multiset α) (x : {x // x in s}) : (s.attach.eras
e x).map (↑) = s.erase x
参数：s : Multiset α；x : {x // x in s}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_erase`：map_erase [DecidableEq α] [DecidableEq β] (f : α -> 
β) (hf : Function.Injective f) (x : α) (s : Multiset α) : (s.erase x).map f = (s
.map f).…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Multiset.attach_map_val`：attach_map_val (s : Multiset α) : s.attach.map 
Subtype.val = s
-/
lemma erase_attach_map_val (s : Multiset α) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (↑) = s.erase x := by
  rw [Multiset.map_erase _ val_injective, attach_map_val]
/-
**Multiset.erase_attach_map** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：erase_attach_map (s : Multiset α) (f : α -> β) (x : {x // x in s}) : (s.at
tach.erase x).map (fun j : {x // x in s} => f j) = (s.erase x).map f
参数：s : Multiset α；f : α -> β；x : {x // x in s}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用引理 `Multiset.erase_attach_map_val`：erase_attach_map_val (s : Multiset α) (x 
: {x // x in s}) : (s.attach.erase x).map (↑) = s.erase x
-/
lemma erase_attach_map (s : Multiset α) (f : α → β) (x : {x // x ∈ s}) :
    (s.attach.erase x).map (fun j : {x // x ∈ s} ↦ f j) = (s.erase x).map f := by
  simp only [← Function.comp_apply (f := f)]
  rw [← map_map, erase_attach_map_val]

end

/-! ### Subtraction -/

section sub
variable [DecidableEq α] {s t u : Multiset α} {a : α}

/-
**Multiset.sub_eq_fold_erase** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase s t
参数：s t : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn₂`：∀ {α : Sort uA} {β : Sort uB} {s₁ : Setoid α} {s₂
 : Setoid β} {motive : Quotient s₁ → Quotient s₂ → Prop}   (q₁ : Quotient s₁) (q
₂ : Quotien…
· 使用定理 `Multiset.instRightCommutativeErase`：∀ {α : Type u_1} [inst : DecidableEq
 α], RightCommutative Multiset.erase
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.diff_eq_foldl`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (l₁ l₂
 : List α), l₁.diff l₂ = List.foldl List.erase l₁ l₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.foldl_hom`：∀ {α₁ : Type u_1} {α₂ : Type u_2} {β : Type u_3} (f : α₁
 → α₂) {g₁ : α₁ → β → α₁} {g₂ : α₂ → β → α₂} {l : List β}   {init : α₁}, (∀ (x :
 α₁)…
-/
lemma sub_eq_fold_erase (s t : Multiset α) : s - t = foldl erase s t :=
  Quotient.inductionOn₂ s t fun l₁ l₂ => by
    change ofList (l₁.diff l₂) = foldl erase l₁ l₂
    rw [diff_eq_foldl l₁ l₂]
    symm
    exact foldl_hom _ fun x y => rfl

end sub

/-! ### Lift a relation to `Multiset`s -/


section Rel

variable {δ : Type*} {r : α → β → Prop} {p : γ → δ → Prop}

/-
**Multiset.rel_map_left** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_map_left {s : Multiset γ} {f : γ -> α} : forall {t}, Rel r (s.map f) t
 ↔ Rel (fun a b => r (f a) b) s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem rel_map_left {s : Multiset γ} {f : γ → α} :
    ∀ {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t :=
  @(Multiset.induction_on s (by simp) (by simp +contextual [rel_cons_left]))
/-
**Multiset.rel_map_right** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ -> β} : Rel r s (t.
map f) ↔ Rel (fun a b => r a (f b)) s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_flip`：rel_flip {s t} : Rel (flip r) s t ↔ Rel r t s
· 使用定理 `Multiset.rel_map_left`：rel_map_left {s : Multiset γ} {f : γ -> α} : fora
ll {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_map_right {s : Multiset α} {t : Multiset γ} {f : γ → β} :
    Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t := by
  rw [← rel_flip, rel_map_left, ← rel_flip]; rfl
/-
**Multiset.rel_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ} {g : β -> δ} : Rel 
p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Multiset.rel_map_left`：rel_map_left {s : Multiset γ} {f : γ -> α} : fora
ll {t}, Rel r (s.map f) t ↔ Rel (fun a b => r (f a) b) s t
· 使用定理 `Multiset.rel_map_right`：rel_map_right {s : Multiset α} {t : Multiset γ} 
{f : γ -> β} : Rel r s (t.map f) ↔ Rel (fun a b => r a (f b)) s t
-/
theorem rel_map {s : Multiset α} {t : Multiset β} {f : α → γ} {g : β → δ} :
    Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t :=
  rel_map_left.trans rel_map_right

end Rel

section Map

/-
**Multiset.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_eq_map {f : α -> β} (hf : Function.Injective f) {s t : Multiset α} : s
.map f = t.map f ↔ s = t
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.rel_eq`：rel_eq {s t : Multiset α} : Rel (· = ·) s t ↔ s = t
· 使用定理 `Multiset.rel_map`：rel_map {s : Multiset α} {t : Multiset β} {f : α -> γ}
 {g : β -> δ} : Rel p (s.map f) (t.map g) ↔ Rel (fun a b => p (f a) (g b)) s t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_eq_map {f : α → β} (hf : Function.Injective f) {s t : Multiset α} :
    s.map f = t.map f ↔ s = t := by
  rw [← rel_eq, ← rel_eq, rel_map]
  simp only [hf.eq_iff]
/-
**Multiset.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_injective {f : α -> β} (hf : Function.Injective f) : Function.Injectiv
e (Multiset.map f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.map_eq_map`：map_eq_map {f : α -> β} (hf : Function.Injective f)
 {s t : Multiset α} : s.map f = t.map f ↔ s = t
-/
theorem map_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (Multiset.map f) := fun _x _y => (map_eq_map hf).1

end Map

section Quot

/-
**Multiset.map_mk_eq_map_mk_of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_mk_eq_map_mk_of_rel {r : α -> α -> Prop} {s t : Multiset α} (hst : s.R
el r t) : s.map (Quot.mk r) = t.map (Quot.mk r)
参数：hst : s.Rel r t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mk_eq_map_mk_of_rel {r : α → α → Prop} {s t : Multiset α} (hst : s.Rel r t) :
    s.map (Quot.mk r) = t.map (Quot.mk r) :=
  Rel.recOn hst rfl fun hab _hst ih => by simp [ih, Quot.sound hab]
/-
**Multiset.exists_multiset_eq_map_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：exists_multiset_eq_map_quot_mk {r : α -> α -> Prop} (s : Multiset (Quot r)
) : exists t : Multiset α, s = t.map (Quot.mk r)
参数：s : Multiset (Quot r)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
-/
theorem exists_multiset_eq_map_quot_mk {r : α → α → Prop} (s : Multiset (Quot r)) :
    ∃ t : Multiset α, s = t.map (Quot.mk r) :=
  Multiset.induction_on s ⟨0, rfl⟩ fun a _s ⟨t, ht⟩ =>
    Quot.inductionOn a fun a => ht.symm ▸ ⟨a ::ₘ t, (map_cons _ _ _).symm⟩
/-
**Multiset.induction_on_multiset_quot** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：induction_on_multiset_quot {r : α -> α -> Prop} {p : Multiset (Quot r) -> 
Prop} (s : Multiset (Quot r)) : (forall s : Multiset α, p (s.map (Quot.mk r))) -
> p s
参数：Quot r；s : Multiset (Quot r)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.exists_multiset_eq_map_quot_mk`：exists_multiset_eq_map_quot_mk 
{r : α -> α -> Prop} (s : Multiset (Quot r)) : exists t : Multiset α, s = t.map 
(Quot.mk r)
-/
theorem induction_on_multiset_quot {r : α → α → Prop} {p : Multiset (Quot r) → Prop}
    (s : Multiset (Quot r)) : (∀ s : Multiset α, p (s.map (Quot.mk r))) → p s :=
  match s, exists_multiset_eq_map_quot_mk s with
  | _, ⟨_t, rfl⟩ => fun h => h _

end Quot

section Nodup

variable {s : Multiset α}

/-
**Multiset.Nodup.of_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f : α → β), (Multiset.map 
f s).Nodup → s.Nodup
参数：f : α → β；Multiset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
-/
theorem Nodup.of_map (f : α → β) : Nodup (map f s) → Nodup s :=
  Quot.induction_on s fun _ => List.Nodup.of_map f
/-
**Multiset.Nodup.map_on** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f : α → β},   (∀ x ∈ s, ∀ 
y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s).Nodup
参数：∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y；Multiset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Nodup.map_on`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β},
   (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (List.map f l).Nodup
-/
theorem Nodup.map_on {f : α → β} :
    (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → Nodup s → Nodup (map f s) :=
  Quot.induction_on s fun _ => List.Nodup.map_on
/-
**Multiset.Nodup.map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multiset α}, Function.Injec
tive f → s.Nodup → (Multiset.map f s).Nodup
参数：Multiset.map f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.map_on`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f
 : α → β},   (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s
).Nodup
-/
theorem Nodup.map {f : α → β} {s : Multiset α} (hf : Injective f) : Nodup s → Nodup (map f s) :=
  Nodup.map_on fun _ _ _ _ h => hf h
/-
**Multiset.nodup_map_iff_of_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_map_iff_of_inj_on {f : α -> β} (d : forall x in s, forall y in s, f 
x = f y -> x = y) : Nodup (map f s) ↔ Nodup s
参数：d : forall x in s, forall y in s, f x = f y -> x = y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.of_map`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f
 : α → β), (Multiset.map f s).Nodup → s.Nodup
· 使用定理 `Multiset.Nodup.map_on`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f
 : α → β},   (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s
).Nodup
-/
theorem nodup_map_iff_of_inj_on {f : α → β} (d : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map_on d⟩
/-
**Multiset.nodup_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_map_iff_of_injective {f : α -> β} (d : Function.Injective f) : Nodup
 (map f s) ↔ Nodup s
参数：d : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Nodup.of_map`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} (f
 : α → β), (Multiset.map f s).Nodup → s.Nodup
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
-/
theorem nodup_map_iff_of_injective {f : α → β} (d : Function.Injective f) :
    Nodup (map f s) ↔ Nodup s :=
  ⟨Nodup.of_map _, fun h => h.map d⟩
/-
**Multiset.inj_on_of_nodup_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：inj_on_of_nodup_map {f : α -> β} {s : Multiset α} : Nodup (map f s) -> for
all x in s, forall y in s, f x = f y -> x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.inj_on_of_nodup_map`：inj_on_of_nodup_map {f : α -> β} {l : List α} 
(d : Nodup (map f l)) : forall ⦃x⦄, x in l -> forall ⦃y⦄, y in l -> f x = f y ->
 x = y
-/
theorem inj_on_of_nodup_map {f : α → β} {s : Multiset α} :
    Nodup (map f s) → ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  Quot.induction_on s fun _ => List.inj_on_of_nodup_map
/-
**Multiset.nodup_map_iff_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_map_iff_inj_on {f : α -> β} {s : Multiset α} (d : Nodup s) : Nodup (
map f s) ↔ forall x in s, forall y in s, f x = f y -> x = y
参数：d : Nodup s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.inj_on_of_nodup_map`：inj_on_of_nodup_map {f : α -> β} {s : Mult
iset α} : Nodup (map f s) -> forall x in s, forall y in s, f x = f y -> x = y
· 使用定理 `Multiset.Nodup.map_on`：∀ {α : Type u_1} {β : Type v} {s : Multiset α} {f
 : α → β},   (∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y) → s.Nodup → (Multiset.map f s
).Nodup
-/
theorem nodup_map_iff_inj_on {f : α → β} {s : Multiset α} (d : Nodup s) :
    Nodup (map f s) ↔ ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩
/-
**Multiset.Nodup.pmap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {s : 
Multiset α} {H : ∀ a ∈ s, p a},   (∀ (a : α) (ha : p a) (b : α) (hb : p b), f a 
ha = f b hb → a = b) → s.Nodup → (Multiset.pmap f s H).Nodup
参数：a : α；∀ (a : α) (ha : p a) (b : α) (hb : p b), f a ha = f b hb → a = b；Multis
et.pmap f s H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.Nodup.pmap`：∀ {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α)
 → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (∀ (a : α) (ha : p a) (b : α) (hb
 : p …
-/
theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {s : Multiset α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) : Nodup s → Nodup (pmap f s H) :=
  Quot.induction_on s (fun _ _ => List.Nodup.pmap hf) H

@[simp]
/-
**Multiset.nodup_attach** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.induction_on`：∀ {α : Sort u_4} {r : α → α → Prop} {β : Quot r → Pro
p} (q : Quot r), (∀ (a : α), β (Quot.mk r a)) → β q
· 使用定理 `List.nodup_attach`：nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup 
l
-/
theorem nodup_attach {s : Multiset α} : Nodup (attach s) ↔ Nodup s :=
  Quot.induction_on s fun _ => List.nodup_attach

protected alias ⟨_, Nodup.attach⟩ := nodup_attach
/-
**Multiset.map_eq_map_of_bij_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_eq_map_of_bij_of_nodup (f : α -> γ) (g : β -> γ) {s : Multiset α} {t :
 Multiset β} (hs : s.Nodup) (ht : t.Nodup) (i : forall a in s, β) (hi : forall a
 ha, i a ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂)
 (i_surj : forall b in t, exists a ha, i a ha = b) (h : forall a ha, f a = g (i 
a ha)) : s.map f = t.map g
参数：f : α -> γ；g : β -> γ；hs : s.Nodup；ht : t.Nodup；i : forall a in s, β；hi : for
all a ha, i a ha in t；i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = 
a₂；i_surj : forall b in t, exists a ha, i a ha = b；h : forall a ha, f a = g (i a
 ha)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Nodup.ext`：∀ {α : Type u_1} {s t : Multiset α}, s.Nodup → t.Nod
up → (s = t ↔ ∀ (a : α), a ∈ s ↔ a ∈ t)
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Multiset.Nodup.attach`：∀ {α : Type u_1} {s : Multiset α}, s.Nodup → s.at
tach.Nodup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Multiset.pmap_eq_map`：pmap_eq_map (p : α -> Prop) (f : α -> β) (s : Mult
iset α) : forall H, @pmap _ _ p (fun a _ => f a) s H = map f s
· 使用定理 `Multiset.pmap_eq_map_attach`：pmap_eq_map_attach {p : α -> Prop} (f : for
all a, p a -> β) (s) : forall H, pmap f s H = s.attach.map fun x => f x.1 (H _ x
.2)
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
-/
theorem map_eq_map_of_bij_of_nodup (f : α → γ) (g : β → γ) {s : Multiset α} {t : Multiset β}
    (hs : s.Nodup) (ht : t.Nodup) (i : ∀ a ∈ s, β) (hi : ∀ a ha, i a ha ∈ t)
    (i_inj : ∀ a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ → a₁ = a₂)
    (i_surj : ∀ b ∈ t, ∃ a ha, i a ha = b) (h : ∀ a ha, f a = g (i a ha)) : s.map f = t.map g := by
  have : t = s.attach.map fun x => i x.1 x.2 := by
    rw [ht.ext]
    · aesop
    · exact hs.attach.map fun x y hxy ↦ Subtype.ext <| i_inj _ x.2 _ y.2 hxy
  calc
    s.map f = s.pmap (fun x _ => f x) fun _ => id := by rw [pmap_eq_map]
    _ = s.attach.map fun x => f x.1 := by rw [pmap_eq_map_attach]
    _ = t.map g := by rw [this, Multiset.map_map]; exact map_congr rfl fun x _ => h _ _

end Nodup

end Multiset

