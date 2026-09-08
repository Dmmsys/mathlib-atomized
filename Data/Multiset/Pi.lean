/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Multiset.Bind

/-!
# The Cartesian product of multisets

## Main definitions

* `Multiset.pi`: Cartesian product of multisets indexed by a multiset.
-/

@[expose] public section


namespace Multiset

section Pi

open Function

namespace Pi
variable {α : Type*} [DecidableEq α] {δ : α → Sort*}

/-- Given `δ : α → Sort*`, `Pi.empty δ` is the trivial dependent function out of the empty
multiset. -/
/-
**Multiset.Pi.empty** 是 Mathlib 中的一个定义，位于命名空间 `Multiset.Pi`。
形式化陈述：empty (δ : α -> Sort*) : forall a in (0 : Multiset α), δ a
参数：δ : α -> Sort*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `δ : α → Sort*`, `Pi.empty δ` is the trivial dependent function out of the
 empty
multiset.
-/
def empty (δ : α → Sort*) : ∀ a ∈ (0 : Multiset α), δ a :=
  nofun

variable (m : Multiset α) (a : α)

/-- Given `δ : α → Sort*`, a multiset `m` and a term `a`, as well as a term `b : δ a` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `Pi.cons m a b f` is a function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`. -/
/-
**Multiset.Pi.cons** 是 Mathlib 中的一个定义，位于命名空间 `Multiset.Pi`。
形式化陈述：cons (b : δ a) (f : forall a in m, δ a) : forall a' in a ::ₘ m, δ a'
参数：b : δ a；f : forall a in m, δ a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given `δ : α → Sort*`, a multiset `m` and a term `a`, as well as a term `b : δ a
` and a
function `f` such that `f a' : δ a'` for all `a'` in `m`, `Pi.cons m a b f` is a
 function `g` such
that `g a'' : δ a''` for all `a''` in `a ::ₘ m`.
-/
def cons (b : δ a) (f : ∀ a ∈ m, δ a) : ∀ a' ∈ a ::ₘ m, δ a' :=
  fun a' ha' => if h : a' = a then Eq.ndrec b h.symm else f a' <| (mem_cons.1 ha').resolve_left h

variable {m a}
/-
**Multiset.Pi.cons_same** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_same {b : δ a} {f : forall a in m, δ a} (h : a in a ::ₘ m) : cons m a
 b f a h = b
参数：h : a in a ::ₘ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_same {b : δ a} {f : ∀ a ∈ m, δ a} (h : a ∈ a ::ₘ m) :
    cons m a b f a h = b :=
  dif_pos rfl
/-
**Multiset.Pi.cons_ne** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ a} (h' : a' in a ::ₘ m)
 (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h)
参数：h' : a' in a ::ₘ m；h : a' != a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem cons_ne {a a' : α} {b : δ a} {f : ∀ a ∈ m, δ a} (h' : a' ∈ a ::ₘ m)
    (h : a' ≠ a) : Pi.cons m a b f a' h' = f a' ((mem_cons.1 h').resolve_left h) :=
  dif_neg h
/-
**Multiset.Pi.cons_swap** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : forall a 
in m, δ a} (h : a != a') : Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f) ≍ Pi.cons 
(a ::ₘ m) a' b' (Pi.cons m a b f)
参数：h : a != a'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.hfunext`：hfunext {α α' : Sort u} {β : α -> Sort v} {β' : α' -> 
Sort v} {f : forall a, β a} {f' : forall a, β' a} (hα : α = α') (h : forall a a'
, a ≍ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.cons_swap`：cons_swap (a b : α) (s : Multiset α) : a ::ₘ b ::ₘ s
 = b ::ₘ a ::ₘ s
· 使用定理 `Decidable.ne_or_eq`：Decidable.ne_or_eq {α : Sort*} (x y : α) [Decidable 
(x = y)] : x != y ∨ x = y
· 使用定理 `Decidable.eq_or_ne`：Decidable.eq_or_ne {α : Sort*} (x y : α) [Decidable 
(x = y)] : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Multiset.Pi.cons_ne`：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ 
a} (h' : a' in a ::ₘ m) (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.
1 h').res…
· 使用定理 `Multiset.Pi.cons_same`：cons_same {b : δ a} {f : forall a in m, δ a} (h :
 a in a ::ₘ m) : cons m a b f a h = b
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_swap {a a' : α} {b : δ a} {b' : δ a'} {m : Multiset α} {f : ∀ a ∈ m, δ a}
    (h : a ≠ a') : Pi.cons (a' ::ₘ m) a b (Pi.cons m a' b' f) ≍
      Pi.cons (a ::ₘ m) a' b' (Pi.cons m a b f) := by
  apply hfunext rfl
  simp only [heq_iff_eq]
  rintro a'' _ rfl
  refine hfunext (by rw [Multiset.cons_swap]) fun ha₁ ha₂ _ => ?_
  rcases Decidable.ne_or_eq a'' a with (h₁ | rfl)
  on_goal 1 => rcases Decidable.eq_or_ne a'' a' with (rfl | h₂)
  all_goals simp [*, Pi.cons_same, Pi.cons_ne]

@[simp]
/-
**Multiset.Pi.cons_eta** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_eta {m : Multiset α} {a : α} (f : forall a' in a ::ₘ m, δ a') : (cons
 m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f
参数：f : forall a' in a ::ₘ m, δ a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Pi.cons_same`：cons_same {b : δ a} {f : forall a in m, δ a} (h :
 a in a ::ₘ m) : cons m a b f a h = b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Multiset.Pi.cons_ne`：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ 
a} (h' : a' in a ::ₘ m) (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.
1 h').res…
-/
theorem cons_eta {m : Multiset α} {a : α} (f : ∀ a' ∈ a ::ₘ m, δ a') :
    (cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_cons_of_mem ha')) = f := by
  ext a' h'
  by_cases h : a' = a
  · subst h
    rw [Pi.cons_same]
  · rw [Pi.cons_ne _ h]
/-
**Multiset.Pi.cons_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_map (b : δ a) (f : forall a' in m, δ a') {δ' : α -> Sort*} (φ : foral
l ⦃a'⦄, δ a' -> δ' a') : Pi.cons _ _ (φ b) (fun a' ha' => φ (f a' ha')) = (fun a
' ha' => φ ((cons _ _ b f) a' ha'))
参数：b : δ a；f : forall a' in m, δ a'；φ : forall ⦃a'⦄, δ a' -> δ' a'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
-/
theorem cons_map (b : δ a) (f : ∀ a' ∈ m, δ a')
    {δ' : α → Sort*} (φ : ∀ ⦃a'⦄, δ a' → δ' a') :
    Pi.cons _ _ (φ b) (fun a' ha' ↦ φ (f a' ha')) = (fun a' ha' ↦ φ ((cons _ _ b f) a' ha')) := by
  ext a' ha'
  refine (congrArg₂ _ ?_ rfl).trans (apply_dite (@φ _) (a' = a) _ _).symm
  ext rfl
  rfl
/-
**Multiset.Pi.forall_rel_cons_ext** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：forall_rel_cons_ext {r : forall ⦃a⦄, δ a -> δ a -> Prop} {b₁ b₂ : δ a} {f₁
 f₂ : forall a' in m, δ a'} (hb : r b₁ b₂) (hf : forall (a : α) (ha : a in m), r
 (f₁ a ha) (f₂ a ha)) : forall a ha, r (cons _ _ b₁ f₁ a ha) (cons _ _ b₂ f₂ a h
a)
参数：hb : r b₁ b₂；hf : forall (a : α) (ha : a in m), r (f₁ a ha) (f₂ a ha)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem forall_rel_cons_ext {r : ∀ ⦃a⦄, δ a → δ a → Prop} {b₁ b₂ : δ a} {f₁ f₂ : ∀ a' ∈ m, δ a'}
    (hb : r b₁ b₂) (hf : ∀ (a : α) (ha : a ∈ m), r (f₁ a ha) (f₂ a ha)) :
    ∀ a ha, r (cons _ _ b₁ f₁ a ha) (cons _ _ b₂ f₂ a ha) := by
  intro a ha
  dsimp [cons]
  split_ifs with H
  · cases H
    exact hb
  · exact hf _ _
/-
**Multiset.Pi.cons_injective** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Pi`。
形式化陈述：cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) : Function.
Injective (Pi.cons s a b)
参数：hs : a ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.Pi.cons_ne`：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ 
a} (h' : a' in a ::ₘ m) (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.
1 h').res…
-/
theorem cons_injective {a : α} {b : δ a} {s : Multiset α} (hs : a ∉ s) :
    Function.Injective (Pi.cons s a b) := fun f₁ f₂ eq =>
  funext fun a' =>
    funext fun h' =>
      have ne : a ≠ a' := fun h => hs <| h.symm ▸ h'
      have : a' ∈ a ::ₘ s := mem_cons_of_mem h'
      calc
        f₁ a' h' = Pi.cons s a b f₁ a' this := by rw [Pi.cons_ne this ne.symm]
               _ = Pi.cons s a b f₂ a' this := by rw [eq]
               _ = f₂ a' h' := by rw [Pi.cons_ne this ne.symm]

end Pi

section
variable {α : Type*} [DecidableEq α] {β : α → Type*}

/-- `pi m t` constructs the Cartesian product over `t` indexed by `m`. -/
/-
**Multiset.pi** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：pi (m : Multiset α) (t : forall a, Multiset (β a)) : Multiset (forall a in
 m, β a)
参数：m : Multiset α；t : forall a, Multiset (β a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`pi m t` constructs the Cartesian product over `t` indexed by `m`.
-/
def pi (m : Multiset α) (t : ∀ a, Multiset (β a)) : Multiset (∀ a ∈ m, β a) :=
  m.recOn {Pi.empty β}
    (fun a m (p : Multiset (∀ a ∈ m, β a)) => (t a).bind fun b => p.map <| Pi.cons m a b)
    (by
      intro a a' m n
      by_cases eq : a = a'
      · subst eq; rfl
      · simp only [map_bind, map_map, comp_apply, bind_bind (t a') (t a)]
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b _
        apply bind_hcongr
        · rw [cons_swap a a']
        intro b' _
        apply map_hcongr
        · rw [cons_swap a a']
        intro f _
        exact Pi.cons_swap eq)

@[simp]
/-
**Multiset.pi_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pi_zero (t : forall a, Multiset (β a)) : pi 0 t = {Pi.empty β}
参数：t : forall a, Multiset (β a)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_zero (t : ∀ a, Multiset (β a)) : pi 0 t = {Pi.empty β} :=
  rfl

@[simp]
/-
**Multiset.pi_cons** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pi_cons (m : Multiset α) (t : forall a, Multiset (β a)) (a : α) : pi (a ::
ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b
参数：m : Multiset α；t : forall a, Multiset (β a)；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.recOn_cons`：recOn_cons (a : α) (m : Multiset α) : (a ::ₘ m).rec
On C_0 C_cons C_cons_heq = C_cons a m (m.recOn C_0 C_cons C_cons_heq)
-/
theorem pi_cons (m : Multiset α) (t : ∀ a, Multiset (β a)) (a : α) :
    pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map <| Pi.cons m a b :=
  recOn_cons a m
/-
**Multiset.card_pi** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：card_pi (m : Multiset α) (t : forall a, Multiset (β a)) : card (pi m t) = 
prod (m.map fun a => card (t a))
参数：m : Multiset α；t : forall a, Multiset (β a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.card_singleton`：card_singleton (a : α) : card ({a} : Multiset α
) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.pi_cons`：pi_cons (m : Multiset α) (t : forall a, Multiset (β a)
) (a : α) : pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b
· 使用定理 `Multiset.card_bind`：card_bind : card (s.bind f) = (s.map (card ∘ f)).sum
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `Multiset.map_const'`：∀ {α : Type u_1} {β : Type v} (s : Multiset α) (b :
 β), Multiset.map (fun x => b) s = Multiset.replicate s.card b
· 使用定理 `Multiset.sum_replicate`：∀ {M : Type u_3} [inst : AddCommMonoid M] (n : ℕ
) (a : M), (Multiset.replicate n a).sum = n • a
· 使用定理 `Multiset.map_cons`：map_cons (f : α -> β) (a s) : map f (a ::ₘ s) = f a :
:ₘ map f s
· 使用定理 `Multiset.prod_cons`：prod_cons (a : M) (s) : prod (a ::ₘ s) = a * prod s
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem card_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) :
    card (pi m t) = prod (m.map fun a => card (t a)) :=
  Multiset.induction_on m (by simp) (by simp +contextual)
/-
**Multiset.Nodup.pi** 是 Mathlib 中的一个定理，位于命名空间 `Multiset.Nodup`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] {β : α → Type u_2} {s : Multiset α
} {t : (a : α) → Multiset (β a)},   s.Nodup → (∀ a ∈ s, (t a).Nodup) → (s.pi t).
Nodup
参数：a : α；β a；∀ a ∈ s, (t a).Nodup；s.pi t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `Multiset.nodup_singleton`：nodup_singleton : forall a : α, Nodup ({a} : M
ultiset α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.pi_cons`：pi_cons (m : Multiset α) (t : forall a, Multiset (β a)
) (a : α) : pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b
· 使用定理 `Multiset.Nodup.map`：∀ {α : Type u_1} {β : Type v} {f : α → β} {s : Multi
set α}, Function.Injective f → s.Nodup → (Multiset.map f s).Nodup
· 使用定理 `Multiset.Pi.cons_injective`：cons_injective {a : α} {b : δ a} {s : Multis
et α} (hs : a ∉ s) : Function.Injective (Pi.cons s a b)
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Multiset.Nodup.pairwise`：∀ {α : Type u_1} {r : α → α → Prop} {s : Multis
et α},   (∀ a ∈ s, ∀ b ∈ s, a ≠ b → r a b) → s.Nodup → Multiset.Pairwise r s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.disjoint_map_map`：disjoint_map_map {f : α -> γ} {g : β -> γ} {s
 : Multiset α} {t : Multiset β} : Disjoint (s.map f) (t.map g) ↔ forall a in s, 
forall b in t, …
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.Pi.cons_same`：cons_same {b : δ a} {f : forall a in m, δ a} (h :
 a in a ::ₘ m) : cons m a b f a h = b
-/
protected theorem Nodup.pi {s : Multiset α} {t : ∀ a, Multiset (β a)} :
    Nodup s → (∀ a ∈ s, Nodup (t a)) → Nodup (pi s t) :=
  Multiset.induction_on s (fun _ _ => nodup_singleton _)
    (by
      intro a s ih hs ht
      have has : a ∉ s := by simp only [nodup_cons] at hs; exact hs.1
      have hs : Nodup s := by simp only [nodup_cons] at hs; exact hs.2
      simp only [pi_cons, nodup_bind]
      refine
        ⟨fun b _ => ((ih hs) fun a' h' => ht a' <| mem_cons_of_mem h').map (Pi.cons_injective has),
          ?_⟩
      refine (ht a <| mem_cons_self _ _).pairwise ?_
      exact fun b₁ _ b₂ _ neb =>
        disjoint_map_map.2 fun f _ g _ eq =>
          have : Pi.cons s a b₁ f a (mem_cons_self _ _) =
            Pi.cons s a b₂ g a (mem_cons_self _ _) := by rw [eq]
          neb <| show b₁ = b₂ by rwa [Pi.cons_same, Pi.cons_same] at this)
/-
**Multiset.mem_pi** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_pi (m : Multiset α) (t : forall a, Multiset (β a)) (f : forall a in m,
 β a) : f in pi m t ↔ forall (a) (h : a in m), f a h in t a
参数：m : Multiset α；t : forall a, Multiset (β a)；f : forall a in m, β a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Multiset.notMem_zero`：notMem_zero (a : α) : a ∉ (0 : Multiset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.pi_cons`：pi_cons (m : Multiset α) (t : forall a, Multiset (β a)
) (a : α) : pi (a ::ₘ m) t = (t a).bind fun b => (pi m t).map Pi.cons m a b
· 使用定理 `Multiset.Pi.cons_same`：cons_same {b : δ a} {f : forall a in m, δ a} (h :
 a in a ::ₘ m) : cons m a b f a h = b
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_cons`：mem_cons {a b : α} {s : Multiset α} : a in b ::ₘ s ↔ 
a = b ∨ a in s
· 使用定理 `Multiset.Pi.cons_ne`：cons_ne {a a' : α} {b : δ a} {f : forall a in m, δ 
a} (h' : a' in a ::ₘ m) (h : a' != a) : Pi.cons m a b f a' h' = f a' ((mem_cons.
1 h').res…
· 使用定理 `Multiset.mem_cons_self`：mem_cons_self (a : α) (s : Multiset α) : a in a 
::ₘ s
· 使用定理 `Multiset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Multiset α} (h 
: a in s) : a in b ::ₘ s
· 使用定理 `Multiset.Pi.cons_eta`：cons_eta {m : Multiset α} {a : α} (f : forall a' i
n a ::ₘ m, δ a') : (cons m a (f _ (mem_cons_self _ _)) fun a' ha' => f a' (mem_c
ons_of_mem…
-/
theorem mem_pi (m : Multiset α) (t : ∀ a, Multiset (β a)) (f : ∀ a ∈ m, β a) :
    f ∈ pi m t ↔ ∀ (a) (h : a ∈ m), f a h ∈ t a := by
  induction m using Multiset.induction_on with
  | empty =>
    have : f = Pi.empty β := funext (fun _ => funext fun h => (notMem_zero _ h).elim)
    simp only [this, pi_zero, mem_singleton, true_iff]
    intro _ h; exact (notMem_zero _ h).elim
  | cons a m ih => ?_
  simp_rw [pi_cons, mem_bind, mem_map, ih]
  constructor
  · rintro ⟨b, hb, f', hf', rfl⟩ a' ha'
    by_cases h : a' = a
    · subst h
      rwa [Pi.cons_same]
    · rw [Pi.cons_ne _ h]
      apply hf'
  · intro hf
    refine ⟨_, hf a (mem_cons_self _ _), _, fun a ha => hf a (mem_cons_of_mem ha), ?_⟩
    rw [Pi.cons_eta]

end

end Pi

end Multiset

