/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Algebra.Order.Sub.Defs
public import Mathlib.Data.Multiset.Fold

/-!
# Multisets form an ordered monoid

This file contains the ordered monoid instance on multisets, and lemmas related to it.

See note [foundational algebra order theory].
-/

@[expose] public section

open List Nat

variable {α β : Type*}

namespace Multiset

/-! ### Additive monoid -/

/-
**Multiset.instAddLeftMono** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instAddLeftMono : AddLeftMono (Multiset α) where elim _s _t _u
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, t ≤ u →
 s + t ≤ s + u

--- 原说明 ---
### Additive monoid
-/
instance instAddLeftMono : AddLeftMono (Multiset α) where elim _s _t _u := Multiset.add_le_add_left
/-
**Multiset.instAddLeftReflectLE** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instAddLeftReflectLE : AddLeftReflectLE (Multiset α) where le_of_add_le_ad
d_left
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.le_of_add_le_add_left`：∀ {α : Type u_1} {s t u : Multiset α}, s
 + t ≤ s + u → t ≤ u
-/
instance instAddLeftReflectLE : AddLeftReflectLE (Multiset α) where
  le_of_add_le_add_left := Multiset.le_of_add_le_add_left
/-
**Multiset.instAddCancelCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：instAddCancelCommMonoid : AddCancelCommMonoid (Multiset α) where add_comm
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.add_assoc`：∀ {α : Type u_1} (s t u : Multiset α), s + t + u = s
 + (t + u)
· 使用定理 `Multiset.zero_add`：∀ {α : Type u_1} (s : Multiset α), 0 + s = s
· 使用定理 `Multiset.add_zero`：∀ {α : Type u_1} (s : Multiset α), s + 0 = s
· 使用定理 `Multiset.add_comm`：∀ {α : Type u_1} (s t : Multiset α), s + t = t + s
-/
instance instAddCancelCommMonoid : AddCancelCommMonoid (Multiset α) where
  add_comm := Multiset.add_comm
  add_assoc := Multiset.add_assoc
  zero_add := Multiset.zero_add
  add_zero := Multiset.add_zero
  add_left_cancel _ _ _ := Multiset.add_right_inj.1
  nsmul := nsmulRec
/-
**Multiset.mem_of_mem_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_of_mem_nsmul {a : α} {s : Multiset α} {n : Nat} (h : a in n • s) : a i
n s
参数：h : a in n • s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
-/
lemma mem_of_mem_nsmul {a : α} {s : Multiset α} {n : ℕ} (h : a ∈ n • s) : a ∈ s := by
  induction n with
  | zero =>
    rw [zero_nsmul] at h
    exact absurd h (notMem_zero _)
  | succ n ih =>
    rw [succ_nsmul, mem_add] at h
    exact h.elim ih id

@[simp]
/-
**Multiset.mem_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_nsmul {a : α} {s : Multiset α} {n : Nat} : a in n • s ↔ n != 0 ∧ a in 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Multiset.mem_of_mem_nsmul`：mem_of_mem_nsmul {a : α} {s : Multiset α} {n 
: Nat} (h : a in n • s) : a in s
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Multiset.mem_add`：mem_add {a : α} {s t : Multiset α} : a in s + t ↔ a in
 s ∨ a in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma mem_nsmul {a : α} {s : Multiset α} {n : ℕ} : a ∈ n • s ↔ n ≠ 0 ∧ a ∈ s := by
  refine ⟨fun ha ↦ ⟨?_, mem_of_mem_nsmul ha⟩, fun h ↦ ?_⟩
  · rintro rfl
    simp [zero_nsmul] at ha
  obtain ⟨n, rfl⟩ := exists_eq_succ_of_ne_zero h.1
  rw [succ_nsmul, mem_add]
  exact Or.inr h.2
/-
**Multiset.mem_nsmul_of_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：mem_nsmul_of_ne_zero {a : α} {s : Multiset α} {n : Nat} (h0 : n != 0) : a 
in n • s ↔ a in s
参数：h0 : n != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_nsmul_of_ne_zero {a : α} {s : Multiset α} {n : ℕ} (h0 : n ≠ 0) : a ∈ n • s ↔ a ∈ s := by
  simp [*]
/-
**Multiset.smul_subset_self** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：smul_subset_self (s : Multiset α) (n : Nat) : n • s subseteq s
参数：s : Multiset α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.subset_iff`：subset_iff {s t : Multiset α} : s subseteq t ↔ fora
ll ⦃x⦄, x in s -> x in t
· 使用引理 `Multiset.mem_of_mem_nsmul`：mem_of_mem_nsmul {a : α} {s : Multiset α} {n 
: Nat} (h : a in n • s) : a in s
-/
theorem smul_subset_self (s : Multiset α) (n : ℕ) : n • s ⊆ s :=
  subset_iff.mpr fun _ ↦ mem_of_mem_nsmul
/-
**Multiset.subset_smul_self_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：subset_smul_self_of_ne_zero (s : Multiset α) {n : Nat} (hn : n != 0) : s s
ubseteq n • s
参数：s : Multiset α；hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.subset_iff`：subset_iff {s t : Multiset α} : s subseteq t ↔ fora
ll ⦃x⦄, x in s -> x in t
· 使用引理 `Multiset.mem_nsmul_of_ne_zero`：mem_nsmul_of_ne_zero {a : α} {s : Multise
t α} {n : Nat} (h0 : n != 0) : a in n • s ↔ a in s
-/
theorem subset_smul_self_of_ne_zero (s : Multiset α) {n : ℕ} (hn : n ≠ 0) : s ⊆ n • s :=
  subset_iff.mpr fun _ ↦ mem_nsmul_of_ne_zero hn |>.mpr
/-
**Multiset.nsmul_cons** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：nsmul_cons {s : Multiset α} (n : Nat) (a : α) : n • (a ::ₘ s) = n • ({a} :
 Multiset α) + n • s
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.singleton_add`：singleton_add (a : α) (s : Multiset α) : {a} + s
 = a ::ₘ s
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
-/
lemma nsmul_cons {s : Multiset α} (n : ℕ) (a : α) :
    n • (a ::ₘ s) = n • ({a} : Multiset α) + n • s := by
  rw [← singleton_add, nsmul_add]

/-! ### Cardinality -/

/-- `Multiset.card` bundled as a group hom. -/
@[simps]
/-
**Multiset.cardHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：cardHom : Multiset α ->+ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.card_zero`：card_zero : @card α 0 = 0
· 使用定理 `Multiset.card_add`：card_add (s t : Multiset α) : card (s + t) = card s +
 card t

--- 原说明 ---
`Multiset.card` bundled as a group hom.
-/
def cardHom : Multiset α →+ ℕ where
  toFun := card
  map_zero' := card_zero
  map_add' := card_add

@[simp]
/-
**Multiset.card_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：card_nsmul (s : Multiset α) (n : Nat) : card (n • s) = n * card s
参数：s : Multiset α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
lemma card_nsmul (s : Multiset α) (n : ℕ) : card (n • s) = n * card s := cardHom.map_nsmul ..

/-! ### `Multiset.replicate` -/

/-- `Multiset.replicate` as an `AddMonoidHom`. -/
@[simps]
/-
**Multiset.replicateAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：replicateAddMonoidHom (a : α) : Nat ->+ Multiset α where toFun n
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.replicate_zero`：∀ {α : Type u_1} (a : α), Multiset.replicate 0 
a = 0
· 使用定理 `Multiset.replicate_add`：replicate_add (m n : Nat) (a : α) : replicate (m
 + n) a = replicate m a + replicate n a

--- 原说明 ---
`Multiset.replicate` as an `AddMonoidHom`.
-/
def replicateAddMonoidHom (a : α) : ℕ →+ Multiset α where
  toFun n := replicate n a
  map_zero' := replicate_zero a
  map_add' _ _ := replicate_add _ _ a
/-
**Multiset.nsmul_replicate** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：nsmul_replicate {a : α} (n m : Nat) : n • replicate m a = replicate (n * m
) a
参数：n m : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
lemma nsmul_replicate {a : α} (n m : ℕ) : n • replicate m a = replicate (n * m) a :=
  ((replicateAddMonoidHom a).map_nsmul _ _).symm
/-
**Multiset.nsmul_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a
参数：a : α；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.replicate_one`：replicate_one (a : α) : replicate 1 a = {a}
· 使用引理 `Multiset.nsmul_replicate`：nsmul_replicate {a : α} (n m : Nat) : n • repl
icate m a = replicate (n * m) a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma nsmul_singleton (a : α) (n) : n • ({a} : Multiset α) = replicate n a := by
  rw [← replicate_one, nsmul_replicate, mul_one]

/-! ### `Multiset.map` -/

/-- `Multiset.map` as an `AddMonoidHom`. -/
@[simps]
/-
**Multiset.mapAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：mapAddMonoidHom (f : α -> β) : Multiset α ->+ Multiset β where toFun
参数：f : α -> β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.map_zero`：map_zero (f : α -> β) : map f 0 = 0
· 使用定理 `Multiset.map_add`：map_add (f : α -> β) (s t) : map f (s + t) = map f s +
 map f t

--- 原说明 ---
`Multiset.map` as an `AddMonoidHom`.
-/
def mapAddMonoidHom (f : α → β) : Multiset α →+ Multiset β where
  toFun := map f
  map_zero' := map_zero _
  map_add' := map_add _

@[simp]
/-
**Multiset.coe_mapAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_mapAddMonoidHom (f : α -> β) : (mapAddMonoidHom f : Multiset α -> Mult
iset β) = map f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mapAddMonoidHom (f : α → β) : (mapAddMonoidHom f : Multiset α → Multiset β) = map f := rfl
/-
**Multiset.map_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：map_nsmul (f : α -> β) (n : Nat) (s) : map f (n • s) = n • map f s
参数：f : α -> β；n : Nat；s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
-/
lemma map_nsmul (f : α → β) (n : ℕ) (s) : map f (n • s) = n • map f s :=
  (mapAddMonoidHom f).map_nsmul _ _

/-! ### Subtraction -/

section
variable [DecidableEq α]

/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderedSub (Multiset α) where tsub_le_iff_right _n _m _k := Multiset.sub_le_iff_le_add
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ExistsAddOfLE (Multiset α) where
  exists_add_of_le h := leInductionOn h fun s ↦
      let ⟨l, p⟩ := s.exists_perm_append; ⟨l, Quot.sound p⟩

end

/-! ### `Multiset.filter` -/

section
variable (p : α → Prop) [DecidablePred p]

/-
**Multiset.filter_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：filter_nsmul (s : Multiset α) (n : Nat) : filter p (n • s) = n • filter p 
s
参数：s : Multiset α；n : Nat。
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
· 使用定理 `Multiset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p
_1 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Multis
et α),       s =…
· 使用定理 `nsmul_zero`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ), n • 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Multiset.nsmul_cons`：nsmul_cons {s : Multiset α} (n : Nat) (a : α) : n •
 (a ::ₘ s) = n • ({a} : Multiset α) + n • s
· 使用定理 `Multiset.filter_add`：filter_add (s t : Multiset α) : filter p (s + t) = 
filter p s + filter p t
· 使用定理 `Multiset.filter_cons`：filter_cons {a : α} (s : Multiset α) : filter p (a
 ::ₘ s) = (if p a then {a} else 0) + filter p s
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Multiset α
) ↔ b = a
· 使用引理 `Multiset.mem_of_mem_nsmul`：mem_of_mem_nsmul {a : α} {s : Multiset α} {n 
: Nat} (h : a in n • s) : a in s
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma filter_nsmul (s : Multiset α) (n : ℕ) : filter p (n • s) = n • filter p s := by
  refine s.induction_on ?_ ?_
  · simp only [filter_zero, nsmul_zero]
  · intro a ha ih
    rw [nsmul_cons, filter_add, ih, filter_cons, nsmul_add]
    congr
    split_ifs with hp <;>
      · simp only [filter_eq_self, nsmul_zero, filter_eq_nil]
        intro b hb
        rwa [mem_singleton.mp (mem_of_mem_nsmul hb)]

/-! ### countP -/

@[simp]
/-
**Multiset.countP_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：countP_nsmul (s) (n : Nat) : countP p (n • s) = n * countP p s
参数：s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.countP_congr`：countP_congr {s s' : Multiset α} (hs : s = s') {p
 p' : α -> Prop} [DecidablePred p] [DecidablePred p'] (hp : forall x in s, p x =
 p' x) : s.…
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Multiset.countP_add`：countP_add (s t) : countP p (s + t) = countP p s + 
countP p t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m

--- 原说明 ---
### countP
-/
lemma countP_nsmul (s) (n : ℕ) : countP p (n • s) = n * countP p s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

/-- `countP p`, the number of elements of a multiset satisfying `p`, promoted to an
`AddMonoidHom`. -/
/-
**Multiset.countPAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：countPAddMonoidHom : Multiset α ->+ Nat where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.countP_zero`：countP_zero : countP p 0 = 0
· 使用定理 `Multiset.countP_add`：countP_add (s t) : countP p (s + t) = countP p s + 
countP p t

--- 原说明 ---
`countP p`, the number of elements of a multiset satisfying `p`, promoted to an
`AddMonoidHom`.
-/
def countPAddMonoidHom : Multiset α →+ ℕ where
  toFun := countP p
  map_zero' := countP_zero _
  map_add' := countP_add _
/-
**Multiset.coe_countPAddMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePred p], ⇑(Multiset.count
PAddMonoidHom p) = Multiset.countP p
参数：p : α → Prop；Multiset.countPAddMonoidHom p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_countPAddMonoidHom : (countPAddMonoidHom p : Multiset α → ℕ) = countP p := rfl

end

/-
**Multiset.dedup_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multiset α} {n : ℕ}, n ≠ 0 → 
(n • s).dedup = s.dedup
参数：n • s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_one_of_mem`：count_eq_one_of_mem [DecidableEq α] {a : α
} {s : Multiset α} (d : Nodup s) (h : a in s) : count a s = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
@[simp] lemma dedup_nsmul [DecidableEq α] {s : Multiset α} {n : ℕ} (hn : n ≠ 0) :
    (n • s).dedup = s.dedup := by ext a; by_cases h : a ∈ s <;> simp [h, hn]
/-
**Multiset.Nodup.le_nsmul_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} {s t : Multiset α} {n : ℕ}, s.Nodup → n ≠ 0 → (s ≤ n • t 
↔ s ≤ t)
参数：s ≤ n • t ↔ s ≤ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.Nodup.le_dedup_iff_le`：∀ {α : Type u_1} [inst : DecidableEq α] 
{s t : Multiset α}, s.Nodup → (s ≤ t.dedup ↔ s ≤ t)
· 使用定理 `Multiset.dedup_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Multi
set α} {n : ℕ}, n ≠ 0 → (n • s).dedup = s.dedup
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.dedup_idem`：dedup_idem {m : Multiset α} : m.dedup.dedup = m.ded
up
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Nodup.le_nsmul_iff_le {s t : Multiset α} {n : ℕ} (h : s.Nodup) (hn : n ≠ 0) :
    s ≤ n • t ↔ s ≤ t := by
  classical simp [← h.le_dedup_iff_le, hn]

/-! ### Multiplicity of an element -/

section
variable [DecidableEq α] {s : Multiset α}

/-- `count a`, the multiplicity of `a` in a multiset, promoted to an `AddMonoidHom`. -/
/-
**Multiset.countAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：countAddMonoidHom (a : α) : Multiset α ->+ Nat
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`count a`, the multiplicity of `a` in a multiset, promoted to an `AddMonoidHom`.
-/
def countAddMonoidHom (a : α) : Multiset α →+ ℕ :=
  countPAddMonoidHom (a = ·)

@[simp]
/-
**Multiset.coe_countAddMonoidHom** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：coe_countAddMonoidHom (a : α) : (countAddMonoidHom a : Multiset α -> Nat) 
= count a
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_countAddMonoidHom (a : α) : (countAddMonoidHom a : Multiset α → ℕ) = count a := rfl

@[simp]
/-
**Multiset.count_nsmul** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：count_nsmul (a : α) (n s) : count a (n • s) = n * count a s
参数：a : α；n s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.zero_mul`：∀ (n : ℕ), 0 * n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `succ_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n + 
1) • a = n • a + a
· 使用定理 `Multiset.count_add`：count_add (a : α) : forall s t, count a (s + t) = co
unt a s + count a t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
-/
lemma count_nsmul (a : α) (n s) : count a (n • s) = n * count a s := by
  induction n <;> simp [*, succ_nsmul, succ_mul, zero_nsmul]

end

/-
**Multiset.le_card_smul_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_card_smul_iff_subset {s t : Multiset α} : s <= s.card • t ↔ s subseteq 
t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.Subset.trans`：∀ {α : Type u_1} {s t u : Multiset α}, s ⊆ t → t 
⊆ u → s ⊆ u
· 使用定理 `Multiset.subset_of_le`：subset_of_le : s <= t -> s subseteq t
· 使用定理 `Multiset.smul_subset_self`：smul_subset_self (s : Multiset α) (n : Nat) :
 n • s subseteq s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_iff_count`：le_iff_count {s t : Multiset α} : s <= t ↔ forall
 a, count a s <= count a t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Multiset.count_le_card`：count_le_card (a : α) (s) : count a s <= card s
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Multiset.one_le_count_iff_mem`：one_le_count_iff_mem {a : α} {s : Multise
t α} : 1 <= count a s ↔ a in s
· 使用定理 `Multiset.mem_of_subset`：mem_of_subset {s t : Multiset α} {a : α} (h : s 
subseteq t) : a in s -> a in t
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem le_card_smul_iff_subset {s t : Multiset α} : s ≤ s.card • t ↔ s ⊆ t := by
  classical
  refine ⟨fun hle ↦ Subset.trans (subset_of_le hle) (t.smul_subset_self s.card), ?_⟩
  refine fun hsub ↦ le_iff_count.mpr fun a ↦ ?_
  by_cases! has : a ∉ s
  · simp [count_eq_zero_of_notMem has]
  grw [count_le_card, count_nsmul, ← one_le_count_iff_mem.mpr <| mem_of_subset hsub has, mul_one]

-- TODO: This should be `addMonoidHom_ext`
@[ext]
/-
**Multiset.addHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：addHom_ext [AddZeroClass β] ⦃f g : Multiset α ->+ β⦄ (h : forall x, f {x} 
= g {x}) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.ext`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M] [in
st_1 : AddZero N] ⦃f g : M →+ N⦄, (∀ (x : M), f x = g x) → f = g
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
-/
lemma addHom_ext [AddZeroClass β] ⦃f g : Multiset α →+ β⦄ (h : ∀ x, f {x} = g {x}) : f = g := by
  ext s
  induction s using Multiset.induction_on with
  | empty => simp only [_root_.map_zero]
  | cons a s ih => simp only [← singleton_add, _root_.map_add, ih, h]
/-
**Multiset.le_smul_dedup** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：le_smul_dedup [DecidableEq α] (s : Multiset α) : exists n : Nat, s <= n • 
dedup s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.le_card_smul_iff_subset`：le_card_smul_iff_subset {s t : Multise
t α} : s <= s.card • t ↔ s subseteq t
· 使用定理 `Multiset.subset_dedup`：subset_dedup (s : Multiset α) : s subseteq dedup 
s
-/
theorem le_smul_dedup [DecidableEq α] (s : Multiset α) : ∃ n : ℕ, s ≤ n • dedup s :=
  ⟨s.card, le_card_smul_iff_subset.mpr s.subset_dedup⟩

end Multiset

