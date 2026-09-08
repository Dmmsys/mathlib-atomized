/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Data.Set.Image

/-!
# Support of a function

In this file we define `Function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `Function.mulSupport f = {x | f x ≠ 1}`.
-/

@[expose] public section

assert_not_exists Monoid CompleteLattice

open Function Set

variable {ι κ M N P : Type*}

namespace Function
variable [One M] [One N] [One P] {f g : ι → M} {s : Set ι} {x : ι}

/-- `mulSupport` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive /-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/]
/-
**Function.mulSupport** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：mulSupport (f : ι -> M) : Set ι
参数：f : ι -> M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`mulSupport` of a function is the set of points `x` such that `f x ≠ 1`.
-/
def mulSupport (f : ι → M) : Set ι := {x | f x ≠ 1}

@[to_additive]
/-
**Function.mulSupport_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_eq_preimage (f : ι -> M) : mulSupport f = f ⁻¹' {1}ᶜ
参数：f : ι -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulSupport_eq_preimage (f : ι → M) : mulSupport f = f ⁻¹' {1}ᶜ := rfl

@[to_additive]
/-
**Function.notMem_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：notMem_mulSupport : x ∉ mulSupport f ↔ f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
-/
lemma notMem_mulSupport : x ∉ mulSupport f ↔ f x = 1 := not_not

@[to_additive]
/-
**Function.compl_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：compl_mulSupport : (mulSupport f)ᶜ = {x | f x = 1}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
-/
lemma compl_mulSupport : (mulSupport f)ᶜ = {x | f x = 1} := ext fun _ ↦ notMem_mulSupport

@[to_additive (attr := simp)]
/-
**Function.mem_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mem_mulSupport : x in mulSupport f ↔ f x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_mulSupport : x ∈ mulSupport f ↔ f x ≠ 1 := .rfl

@[to_additive (attr := simp)]
/-
**Function.mulSupport_subset_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_subset_iff : mulSupport f subseteq s ↔ forall x, f x != 1 -> x 
in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulSupport_subset_iff : mulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s := .rfl

@[to_additive]
/-
**Function.mulSupport_subset_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_subset_iff' : mulSupport f subseteq s ↔ forall x ∉ s, f x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
-/
lemma mulSupport_subset_iff' : mulSupport f ⊆ s ↔ ∀ x ∉ s, f x = 1 :=
  forall_congr' fun _ ↦ not_imp_comm

@[to_additive]
/-
**Function.mulSupport_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_eq_iff : mulSupport f = s ↔ (forall x, x in s -> f x != 1) ∧ fo
rall x, x ∉ s -> f x = 1
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_eq_iff : mulSupport f = s ↔ (∀ x, x ∈ s → f x ≠ 1) ∧ ∀ x, x ∉ s → f x = 1 := by
  simp +contextual only [Set.ext_iff, mem_mulSupport, ne_eq, iff_def,
    not_imp_comm, and_comm, forall_and]

@[to_additive]
/-
**Function.ext_iff_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：ext_iff_mulSupport : f = g ↔ f.mulSupport = g.mulSupport ∧ forall x in f.m
ulSupport, f x = g x where mp h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
lemma ext_iff_mulSupport : f = g ↔ f.mulSupport = g.mulSupport ∧ ∀ x ∈ f.mulSupport, f x = g x where
  mp h := h ▸ ⟨rfl, fun _ _ ↦ rfl⟩
  mpr := fun ⟨h₁, h₂⟩ ↦ funext fun x ↦ by
    if hx : x ∈ f.mulSupport then exact h₂ x hx
    else rw [notMem_mulSupport.1 hx, notMem_mulSupport.1 (mt (Set.ext_iff.1 h₁ x).2 hx)]

@[to_additive]
/-
**Function.mulSupport_update_of_ne_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_update_of_ne_one [DecidableEq ι] (f : ι -> M) (x : ι) {y : M} (
hy : y != 1) : mulSupport (update f x y) = insert x (mulSupport f)
参数：f : ι -> M；x : ι；hy : y != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
-/
lemma mulSupport_update_of_ne_one [DecidableEq ι] (f : ι → M) (x : ι) {y : M} (hy : y ≠ 1) :
    mulSupport (update f x y) = insert x (mulSupport f) := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
/-
**Function.mulSupport_update_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_update_one [DecidableEq ι] (f : ι -> M) (x : ι) : mulSupport (u
pdate f x 1) = mulSupport f \ {x}
参数：f : ι -> M；x : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mulSupport_update_one [DecidableEq ι] (f : ι → M) (x : ι) :
    mulSupport (update f x 1) = mulSupport f \ {x} := by
  ext a; obtain rfl | hne := eq_or_ne a x <;> simp [*]

@[to_additive]
/-
**Function.mulSupport_update_eq_ite** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_update_eq_ite [DecidableEq ι] [DecidableEq M] (f : ι -> M) (x :
 ι) (y : M) : mulSupport (update f x y) = if y = 1 then mulSupport f \ {x} else 
insert x (mulSupport f)
参数：f : ι -> M；x : ι；y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_update_one`：mulSupport_update_one [DecidableEq ι] (f
 : ι -> M) (x : ι) : mulSupport (update f x 1) = mulSupport f \ {x}
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.mulSupport_update_of_ne_one`：mulSupport_update_of_ne_one [Decid
ableEq ι] (f : ι -> M) (x : ι) {y : M} (hy : y != 1) : mulSupport (update f x y)
 = insert x (mulSupport f)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
-/
lemma mulSupport_update_eq_ite [DecidableEq ι] [DecidableEq M] (f : ι → M) (x : ι) (y : M) :
    mulSupport (update f x y) = if y = 1 then mulSupport f \ {x} else insert x (mulSupport f) := by
  rcases eq_or_ne y 1 with rfl | hy <;> simp [mulSupport_update_one, mulSupport_update_of_ne_one, *]

@[to_additive]
/-
**Function.mulSupport_extend_one_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_extend_one_subset {f : ι -> κ} {g : ι -> N} : mulSupport (f.ext
end g 1) subseteq f '' mulSupport g
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.extend.eq_1`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f 
: α → β) (g : α → γ) (j : β → γ) (b : β),   Function.extend f g j b = if h : ∃ a
, f a = b …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.notMem_mulSupport`：notMem_mulSupport : x ∉ mulSupport f ↔ f x =
 1
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Function.extend_apply'`：extend_apply' (g : α -> γ) (e' : β -> γ) (b : β)
 (hb : ¬exists a, f a = b) : extend f g e' b = e' b
-/
lemma mulSupport_extend_one_subset {f : ι → κ} {g : ι → N} :
    mulSupport (f.extend g 1) ⊆ f '' mulSupport g :=
  mulSupport_subset_iff'.mpr fun x hfg ↦ by
    by_cases hf : ∃ a, f a = x
    · rw [extend, dif_pos hf, ← notMem_mulSupport]
      rw [← Classical.choose_spec hf] at hfg
      exact fun hg ↦ hfg ⟨_, hg, rfl⟩
    · rw [extend_apply' _ _ _ hf]; rfl

@[to_additive]
/-
**Function.mulSupport_extend_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_extend_one {f : ι -> κ} {g : ι -> N} (hf : f.Injective) : mulSu
pport (f.extend g 1) = f '' mulSupport g
参数：hf : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Function.mulSupport_extend_one_subset`：mulSupport_extend_one_subset {f :
 ι -> κ} {g : ι -> N} : mulSupport (f.extend g 1) subseteq f '' mulSupport g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
-/
lemma mulSupport_extend_one {f : ι → κ} {g : ι → N} (hf : f.Injective) :
    mulSupport (f.extend g 1) = f '' mulSupport g :=
  mulSupport_extend_one_subset.antisymm <| by
    rintro _ ⟨x, hx, rfl⟩; rwa [mem_mulSupport, hf.extend_apply]

@[to_additive]
/-
**Function.mulSupport_disjoint_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_disjoint_iff : Disjoint (mulSupport f) s ↔ EqOn f 1 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_disjoint_iff : Disjoint (mulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mulSupport_subset_iff', notMem_compl_iff, EqOn,
    Pi.one_apply]

@[to_additive]
/-
**Function.disjoint_mulSupport_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：disjoint_mulSupport_iff : Disjoint s (mulSupport f) ↔ EqOn f 1 s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `Function.mulSupport_disjoint_iff`：mulSupport_disjoint_iff : Disjoint (mu
lSupport f) s ↔ EqOn f 1 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma disjoint_mulSupport_iff : Disjoint s (mulSupport f) ↔ EqOn f 1 s := by
  rw [disjoint_comm, mulSupport_disjoint_iff]

@[to_additive (attr := simp)]
/-
**Function.mulSupport_eq_empty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_eq_empty_iff : mulSupport f = ∅ ↔ f = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.subset_empty_iff`：subset_empty_iff {s : Set α} : s subseteq ∅ ↔ s = 
∅
· 使用引理 `Function.mulSupport_subset_iff'`：mulSupport_subset_iff' : mulSupport f s
ubseteq s ↔ forall x ∉ s, f x = 1
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_eq_empty_iff : mulSupport f = ∅ ↔ f = 1 := by
  rw [← subset_empty_iff, mulSupport_subset_iff', funext_iff]
  simp

@[to_additive (attr := simp)]
/-
**Function.mulSupport_nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_nonempty_iff : (mulSupport f).Nonempty ↔ f != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `Function.mulSupport_eq_empty_iff`：mulSupport_eq_empty_iff : mulSupport f
 = ∅ ↔ f = 1
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulSupport_nonempty_iff : (mulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [nonempty_iff_ne_empty, Ne, mulSupport_eq_empty_iff]

@[to_additive]
/-
**Function._root_.Subsingleton.mulSupport_eq** 是 Mathlib 中的一个定理，位于命名空间 `Function
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subsingleton.mulSupport_eq [Subsingleton M] (f : ι → M) : mulSupport f = ∅ :=
  mulSupport_eq_empty_iff.mpr <| Subsingleton.elim f 1

@[to_additive]
/-
**Function.range_subset_insert_image_mulSupport** 是 Mathlib 中的一个引理，位于命名空间 `Funct
ion`。
形式化陈述：range_subset_insert_image_mulSupport (f : ι -> M) : range f subseteq inser
t 1 (f '' mulSupport f)
参数：f : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
lemma range_subset_insert_image_mulSupport (f : ι → M) :
    range f ⊆ insert 1 (f '' mulSupport f) := by
  simpa only [range_subset_iff, mem_insert_iff, or_iff_not_imp_left] using!
    fun x (hx : x ∈ mulSupport f) ↦ mem_image_of_mem f hx

@[to_additive]
/-
**Function.range_eq_image_or_of_mulSupport_subset** 是 Mathlib 中的一个引理，位于命名空间 `Fun
ction`。
形式化陈述：range_eq_image_or_of_mulSupport_subset {k : Set ι} (h : mulSupport f subse
teq k) : range f = f '' k ∨ range f = insert 1 (f '' k)
参数：h : mulSupport f subseteq k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `Function.range_subset_insert_image_mulSupport`：range_subset_insert_image
_mulSupport (f : ι -> M) : range f subseteq insert 1 (f '' mulSupport f)
· 使用定理 `Set.insert_subset_insert`：insert_subset_insert (h : s subseteq t) : inse
rt a s subseteq insert a t
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t
-/
lemma range_eq_image_or_of_mulSupport_subset {k : Set ι} (h : mulSupport f ⊆ k) :
    range f = f '' k ∨ range f = insert 1 (f '' k) := by
  have : range f ⊆ insert 1 (f '' k) :=
    (range_subset_insert_image_mulSupport f).trans (insert_subset_insert (image_mono h))
  grind

@[to_additive (attr := simp)]
/-
**Function.mulSupport_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_one : mulSupport (1 : ι -> M) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Function.mulSupport_eq_empty_iff`：mulSupport_eq_empty_iff : mulSupport f
 = ∅ ↔ f = 1
-/
lemma mulSupport_one : mulSupport (1 : ι → M) = ∅ := mulSupport_eq_empty_iff.2 rfl

@[to_additive (attr := simp)]
/-
**Function.mulSupport_fun_one** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_fun_one : mulSupport (fun _ => 1 : ι -> M) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_one`：mulSupport_one : mulSupport (1 : ι -> M) = ∅
-/
lemma mulSupport_fun_one : mulSupport (fun _ ↦ 1 : ι → M) = ∅ := mulSupport_one

@[to_additive]
/-
**Function.mulSupport_const** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_const {c : M} (hc : c != 1) : (mulSupport fun _ : ι => c) = Set
.univ
参数：hc : c != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_const {c : M} (hc : c ≠ 1) : (mulSupport fun _ : ι ↦ c) = Set.univ := by
  ext x; simp [hc]

/-- The multiplicative support of a function that is everywhere non-one is the whole space. -/
@[to_additive /-- The support of a function that is everywhere nonzero is the whole space. -/]
/-
**Function.mulSupport_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_eq_univ (hf : forall x, f x != 1) : mulSupport f = Set.univ
参数：hf : forall x, f x != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_univ_of_forall`：eq_univ_of_forall {s : Set α} : (forall x, x in s
) -> s = univ

--- 原说明 ---
The multiplicative support of a function that is everywhere non-one is the whole
 space.
-/
lemma mulSupport_eq_univ (hf : ∀ x, f x ≠ 1) : mulSupport f = Set.univ :=
  Set.eq_univ_of_forall hf

@[to_additive]
/-
**Function.mulSupport_binop_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_binop_subset (op : M -> N -> P) (op1 : op 1 1 = 1) (f : ι -> M)
 (g : ι -> N) : mulSupport (fun x => op (f x) (g x)) subseteq mulSupport f union
 mulSupport g
参数：op : M -> N -> P；op1 : op 1 1 = 1；f : ι -> M；g : ι -> N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_or_of_imp`：not_or_of_imp : (a -> b) -> ¬a ∨ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : ι → M) (g : ι → N) :
    mulSupport (fun x ↦ op (f x) (g x)) ⊆ mulSupport f ∪ mulSupport g := fun x hx ↦
  not_or_of_imp fun hf hg ↦ hx <| by simp only [hf, hg, op1]

@[to_additive]
/-
**Function.mulSupport_comp_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_comp_subset {g : M -> N} (hg : g 1 = 1) (f : ι -> M) : mulSuppo
rt (g ∘ f) subseteq mulSupport f
参数：hg : g 1 = 1；f : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_comp_subset {g : M → N} (hg : g 1 = 1) (f : ι → M) :
    mulSupport (g ∘ f) ⊆ mulSupport f := fun x ↦ mt fun h ↦ by simp only [(· ∘ ·), *]

@[to_additive]
/-
**Function.mulSupport_subset_comp** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_subset_comp {g : M -> N} (hg : forall {x}, g x = 1 -> x = 1) (f
 : ι -> M) : mulSupport f subseteq mulSupport (g ∘ f)
参数：hg : forall {x}, g x = 1 -> x = 1；f : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
lemma mulSupport_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : ι → M) :
    mulSupport f ⊆ mulSupport (g ∘ f) := fun _ ↦ mt hg

@[to_additive]
/-
**Function.mulSupport_comp_eq** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_comp_eq (g : M -> N) (hg : forall {x}, g x = 1 ↔ x = 1) (f : ι 
-> M) : mulSupport (g ∘ f) = mulSupport f
参数：g : M -> N；hg : forall {x}, g x = 1 ↔ x = 1；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
lemma mulSupport_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : ι → M) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun _ ↦ not_congr hg

@[to_additive]
/-
**Function.mulSupport_comp_eq_of_range_subset** 是 Mathlib 中的一个引理，位于命名空间 `Functio
n`。
形式化陈述：mulSupport_comp_eq_of_range_subset {g : M -> N} {f : ι -> M} (hg : forall 
{x}, x in range f -> (g x = 1 ↔ x = 1)) : mulSupport (g ∘ f) = mulSupport f
参数：hg : forall {x}, x in range f -> (g x = 1 ↔ x = 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp.eq_1`：∀ {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ)
 (g : α → β) (x : α), (f ∘ g) x = f (g x)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulSupport_comp_eq_of_range_subset {g : M → N} {f : ι → M}
    (hg : ∀ {x}, x ∈ range f → (g x = 1 ↔ x = 1)) :
    mulSupport (g ∘ f) = mulSupport f :=
  Set.ext fun x ↦ not_congr <| by rw [Function.comp, hg (mem_range_self x)]

@[to_additive]
/-
**Function.mulSupport_comp_eq_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_comp_eq_preimage (g : κ -> M) (f : ι -> κ) : mulSupport (g ∘ f)
 = f ⁻¹' mulSupport g
参数：g : κ -> M；f : ι -> κ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mulSupport_comp_eq_preimage (g : κ → M) (f : ι → κ) :
    mulSupport (g ∘ f) = f ⁻¹' mulSupport g := rfl

@[to_additive support_prodMk]
/-
**Function.mulSupport_prodMk** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_prodMk (f : ι -> M) (g : ι -> N) : mulSupport (fun x => (f x, g
 x)) = mulSupport f union mulSupport g
参数：f : ι -> M；g : ι -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mulSupport_prodMk (f : ι → M) (g : ι → N) :
    mulSupport (fun x ↦ (f x, g x)) = mulSupport f ∪ mulSupport g :=
  Set.ext fun x ↦ by
    simp only [mulSupport, not_and_or, mem_union, mem_ofPred_eq, Prod.mk_eq_one, Ne]

@[to_additive support_prodMk']
/-
**Function.mulSupport_prodMk'** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_prodMk' (f : ι -> M × N) : mulSupport f = (mulSupport fun x => 
(f x).1) union mulSupport fun x => (f x).2
参数：f : ι -> M × N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_prodMk' (f : ι → M × N) :
    mulSupport f = (mulSupport fun x ↦ (f x).1) ∪ mulSupport fun x ↦ (f x).2 := by
  simp only [← mulSupport_prodMk]

@[to_additive]
/-
**Function.mulSupport_along_fiber_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_along_fiber_subset (f : ι × κ -> M) (i : ι) : (mulSupport fun j
 => f (i, j)) subseteq (mulSupport f).image Prod.snd
参数：f : ι × κ -> M；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma mulSupport_along_fiber_subset (f : ι × κ → M) (i : ι) :
    (mulSupport fun j ↦ f (i, j)) ⊆ (mulSupport f).image Prod.snd :=
  fun j hj ↦ ⟨(i, j), by simpa using hj⟩

@[to_additive]
/-
**Function.mulSupport_curry** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_curry (f : ι × κ -> M) : (mulSupport f.curry) = (mulSupport f).
image Prod.fst
参数：f : ι × κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_curry (f : ι × κ → M) : (mulSupport f.curry) = (mulSupport f).image Prod.fst := by
  simp [mulSupport, funext_iff, image]

@[to_additive]
/-
**Function.mulSupport_fun_curry** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：mulSupport_fun_curry (f : ι × κ -> M) : mulSupport (fun i j => f (i, j)) =
 (mulSupport f).image Prod.fst
参数：f : ι × κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.mulSupport_curry`：mulSupport_curry (f : ι × κ -> M) : (mulSuppo
rt f.curry) = (mulSupport f).image Prod.fst
-/
lemma mulSupport_fun_curry (f : ι × κ → M) :
    mulSupport (fun i j ↦ f (i, j)) = (mulSupport f).image Prod.fst := mulSupport_curry f

end Function

namespace Set
variable [One M] {f : ι → M} {s : Set κ} {g : κ → ι}

@[to_additive]
/-
**Set.image_inter_mulSupport_eq** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：image_inter_mulSupport_eq : g '' s inter mulSupport f = g '' (s inter mulS
upport (f ∘ g))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mulSupport_comp_eq_preimage`：mulSupport_comp_eq_preimage (g : κ
 -> M) (f : ι -> κ) : mulSupport (g ∘ f) = f ⁻¹' mulSupport g
· 使用定理 `Set.image_inter_preimage`：image_inter_preimage (f : α -> β) (s : Set α) 
(t : Set β) : f '' (s inter f ⁻¹' t) = f '' s inter t
-/
lemma image_inter_mulSupport_eq : g '' s ∩ mulSupport f = g '' (s ∩ mulSupport (f ∘ g)) := by
  rw [mulSupport_comp_eq_preimage f g, image_inter_preimage]

end Set

namespace Pi
variable [DecidableEq ι] [One M] {i j : ι} {a b : M}

@[to_additive]
/-
**Pi.mulSupport_mulSingle_subset** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSupport_mulSingle_subset : mulSupport (mulSingle i a) subseteq {i}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contra`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
-/
lemma mulSupport_mulSingle_subset : mulSupport (mulSingle i a) ⊆ {i} := fun _ hx ↦
  by_contra fun hx' ↦ hx <| mulSingle_eq_of_ne hx' _

@[to_additive]
/-
**Pi.mulSupport_mulSingle_one** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSupport_mulSingle_one : mulSupport (mulSingle i (1 : M)) = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_one`：mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1
· 使用引理 `Function.mulSupport_one`：mulSupport_one : mulSupport (1 : ι -> M) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mulSupport_mulSingle_one : mulSupport (mulSingle i (1 : M)) = ∅ := by simp

@[to_additive (attr := simp)]
/-
**Pi.mulSupport_mulSingle_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSupport_mulSingle_of_ne (h : a != 1) : mulSupport (mulSingle i a) = {i}
参数：h : a != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用引理 `Pi.mulSupport_mulSingle_subset`：mulSupport_mulSingle_subset : mulSupport
 (mulSingle i a) subseteq {i}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.mem_mulSupport`：mem_mulSupport : x in mulSupport f ↔ f x != 1
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
-/
lemma mulSupport_mulSingle_of_ne (h : a ≠ 1) : mulSupport (mulSingle i a) = {i} :=
  mulSupport_mulSingle_subset.antisymm fun x hx ↦ by rwa [mem_mulSupport, hx, mulSingle_eq_same]

@[to_additive]
/-
**Pi.mulSupport_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSupport_mulSingle [DecidableEq M] : mulSupport (mulSingle i a) = if a =
 1 then ∅ else {i}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Pi.mulSingle_one`：mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1
· 使用引理 `Function.mulSupport_one`：mulSupport_one : mulSupport (1 : ι -> M) = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用引理 `Pi.mulSupport_mulSingle_of_ne`：mulSupport_mulSingle_of_ne (h : a != 1) :
 mulSupport (mulSingle i a) = {i}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma mulSupport_mulSingle [DecidableEq M] :
    mulSupport (mulSingle i a) = if a = 1 then ∅ else {i} := by split_ifs with h <;> simp [h]

@[to_additive]
/-
**Pi.subsingleton_mulSupport_mulSingle** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：subsingleton_mulSupport_mulSingle : (mulSupport (mulSingle i a)).Subsingle
ton
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSupport_mulSingle`：mulSupport_mulSingle [DecidableEq M] : mulSuppo
rt (mulSingle i a) = if a = 1 then ∅ else {i}
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma subsingleton_mulSupport_mulSingle : (mulSupport (mulSingle i a)).Subsingleton := by
  classical
  rw [mulSupport_mulSingle]
  split_ifs with h <;> simp

@[to_additive]
/-
**Pi.mulSupport_mulSingle_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Pi`。
形式化陈述：mulSupport_mulSingle_disjoint (ha : a != 1) (hb : b != 1) : Disjoint (mulS
upport (mulSingle i a)) (mulSupport (mulSingle j b)) ↔ i != j
参数：ha : a != 1；hb : b != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSupport_mulSingle_of_ne`：mulSupport_mulSingle_of_ne (h : a != 1) :
 mulSupport (mulSingle i a) = {i}
· 使用引理 `Set.disjoint_singleton`：disjoint_singleton : Disjoint ({a} : Set α) {b} 
↔ a != b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mulSupport_mulSingle_disjoint (ha : a ≠ 1) (hb : b ≠ 1) :
    Disjoint (mulSupport (mulSingle i a)) (mulSupport (mulSingle j b)) ↔ i ≠ j := by
  rw [mulSupport_mulSingle_of_ne ha, mulSupport_mulSingle_of_ne hb, disjoint_singleton]

end Pi

