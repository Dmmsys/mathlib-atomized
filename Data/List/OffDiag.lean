/-
Copyright (c) 2026 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

import Mathlib.Data.List.Count
import Mathlib.Data.List.Enum
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Perm.Basic
public import Mathlib.Data.Nat.Notation

/-!
# Definition and basic properties of `List.offDiag`

In this file we define `List.offDiag l` to be the product `l.product l`
with the diagonal removed.
The actual definition is more complicated to avoid assuming that equality on `α` is decidable.
-/

@[expose] public section

assert_not_exists Preorder

namespace List

variable {α : Type*} {l : List α}

/-- `List.offDiag l` is the product `l.product l` with the diagonal removed. -/
/-
**List.offDiag** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：offDiag (l : List α) : List (α × α)
参数：l : List α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`List.offDiag l` is the product `l.product l` with the diagonal removed.
-/
def offDiag (l : List α) : List (α × α) :=
  l.zipIdx.flatMap fun (x, n) ↦ map (Prod.mk x) <| l.eraseIdx n

@[simp]
/-
**List.offDiag_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：offDiag_nil : offDiag ([] : List α) = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem offDiag_nil : offDiag ([] : List α) = [] := rfl
/-
**List.offDiag_cons_perm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：offDiag_cons_perm (a : α) (l : List α) : offDiag (a :: l) ~ map (a, ·) l +
+ map (·, a) l ++ l.offDiag
参数：a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipIdx_cons'`：∀ {α : Type u_1} {i : ℕ} {x : α} {xs : List α},   (x 
:: xs).zipIdx i = (x, i) :: List.map (Prod.map id fun x => x + 1) (xs.zipIdx i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.zipIdx_map_fst`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.map Pro
d.fst (l.zipIdx i) = l
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.flatMap_cons`：∀ {α : Type u} {β : Type v} {x : α} {xs : List α} {f 
: α → List β}, List.flatMap f (x :: xs) = f x ++ List.flatMap f xs
· 使用定理 `List.eraseIdx_zero`：∀ {α : Type u_1} {l : List α}, l.eraseIdx 0 = l.tail
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.append_assoc`：∀ {α : Type u} (as bs cs : List α), as ++ bs ++ cs = 
as ++ (bs ++ cs)
· 使用定理 `List.Perm.congr_left`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → ∀ 
(l₃ : List α), l₁.Perm l₃ ↔ l₂.Perm l₃
· 使用定理 `List.map_append_flatMap_perm`：map_append_flatMap_perm (l : List α) (f : 
α -> β) (g : α -> List β) : l.map f ++ l.flatMap g ~ l.flatMap fun x => f x :: g
 x
-/
theorem offDiag_cons_perm (a : α) (l : List α) :
    offDiag (a :: l) ~ map (a, ·) l ++ map (·, a) l ++ l.offDiag := by
  simp only [offDiag, zipIdx_cons']
  have : map (fun x ↦ (x.fst, a)) l.zipIdx = map (·, a) l := by
    conv_rhs => rw [← zipIdx_map_fst 0 l, map_map, Function.comp_def]
  simp [append_assoc, perm_append_left_iff, flatMap_map,
    ← (map_append_flatMap_perm _ _ _).congr_left, this]

@[simp]
/-
**List.offDiag_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：offDiag_singleton (a : α) : offDiag [a] = []
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem offDiag_singleton (a : α) : offDiag [a] = [] := rfl
/-
**List.length_offDiag'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_offDiag' (l : List α) : length l.offDiag = length l * (length l - 1
)
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.length_eraseIdx_of_lt`：∀ {α : Type u_1} {l : List α} {i : ℕ}, i < l
.length → (l.eraseIdx i).length = l.length - 1
· 使用定理 `List.snd_lt_of_mem_zipIdx`：∀ {α : Type u_1} {x : α × ℕ} {l : List α} {k 
: ℕ}, x ∈ l.zipIdx k → x.2 < l.length + k
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_flatMap`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {f : α
 → List β},   (List.flatMap f l).length = (List.map (fun a => (f a).length) l).s
um
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.map_congr_left`：∀ {α : Type u_1} {l : List α} {α_1 : Type u_2} {f g
 : α → α_1}, (∀ a ∈ l, f a = g a) → List.map f l = List.map g l
· 使用定理 `List.map_const'`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {b : β}, L
ist.map (fun x => b) l = List.replicate l.length b
· 使用定理 `List.length_zipIdx`：∀ {α : Type u_1} {l : List α} {i : ℕ}, (l.zipIdx i).
length = l.length
· 使用定理 `List.sum_replicate_nat`：∀ {n a : ℕ}, (List.replicate n a).sum = n * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_offDiag' (l : List α) : length l.offDiag = length l * (length l - 1) := by
  have : ∀ x ∈ l.zipIdx, length (eraseIdx l x.2) = length l - 1 := fun x hx ↦
    length_eraseIdx_of_lt <| snd_lt_of_mem_zipIdx hx
  simp [offDiag, map_congr_left this]

@[simp]
/-
**List.length_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_offDiag'`：length_offDiag' (l : List α) : length l.offDiag = 
length l * (length l - 1)
· 使用定理 `Nat.mul_sub`：∀ (n m k : ℕ), n * (m - k) = n * m - n * k
· 使用定理 `Nat.mul_one`：∀ (n : ℕ), n * 1 = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.pow_two`：∀ (a : ℕ), a ^ 2 = a * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_offDiag (l : List α) : length l.offDiag = length l ^ 2 - length l := by
  simp [length_offDiag', Nat.mul_sub, Nat.pow_two]
/-
**List.mem_offDiag_iff_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_offDiag_iff_getElem {x : α × α} : x in l.offDiag ↔ exists (i : Nat) (_
 : i < l.length) (j : Nat) (_ : j < l.length), i != j ∧ l[i] = x.1 ∧ l[j] = x.2
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∃ a b,
 p a b) ↔ ∃ b a, p a b
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_offDiag_iff_getElem {x : α × α} :
    x ∈ l.offDiag ↔ ∃ (i : ℕ) (_ : i < l.length) (j : ℕ) (_ : j < l.length),
      i ≠ j ∧ l[i] = x.1 ∧ l[j] = x.2 := by
  rcases x with ⟨x, y⟩
  simp only [offDiag, exists_mem_zipIdx, mem_eraseIdx_iff_getElem, mem_flatMap, mem_map,
    Nat.zero_add, Prod.ext_iff, ← exists_and_right, exists_and_left, @exists_comm α, and_assoc,
    exists_eq_left', ne_comm]
/-
**List.count_offDiag_eq_mul_sub_ite** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_offDiag_eq_mul_sub_ite [DecidableEq α] (l : List α) (a b : α) : coun
t (a, b) l.offDiag = count a l * count b l - if a = b then count a l else 0
参数：l : List α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `List.count_map_of_injective`：count_map_of_injective [BEq β] [LawfulBEq β
] (l : List α) (f : α -> β) (hf : Function.Injective f) (x : α) : count (f x) (m
ap f l) = count x…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `Prod.instLawfulBEq`：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [inst
_1 : BEq β] [LawfulBEq α] [LawfulBEq β], LawfulBEq (α × β)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.Perm.count_eq`：∀ {α : Type u_1} [inst : BEq α] {l₁ l₂ : List α}, l₁
.Perm l₂ → ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `List.offDiag_cons_perm`：offDiag_cons_perm (a : α) (l : List α) : offDiag
 (a :: l) ~ map (a, ·) l ++ map (·, a) l ++ l.offDiag
· 使用定理 `List.count_append`：∀ {α : Type u_1} [inst : BEq α] {a : α} {l₁ l₂ : List
 α}, List.count a (l₁ ++ l₂) = List.count a l₁ + List.count a l₂
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Nat.le_mul_self`：∀ (n : ℕ), n ≤ n * n
（共 32 条，此处仅展示前 30 条）
-/
theorem count_offDiag_eq_mul_sub_ite [DecidableEq α] (l : List α) (a b : α) :
    count (a, b) l.offDiag = count a l * count b l - if a = b then count a l else 0 := by
  induction l with
  | nil => simp
  | cons c l ihl =>
    have H₁ {x y z : α} : count (x, y) (map (z, ·) l) = if z = x then count y l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (x, ·) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    have H₂ {x y z : α} : count (x, y) (map (·, z) l) = if z = y then count x l else 0 := by
      split_ifs with h
      · rw [h, count_map_of_injective l (·, y) (by simp [Function.Injective])]
      · simp [count_eq_zero, h]
    simp only [(offDiag_cons_perm _ _).count_eq, count_append, ihl, H₁, H₂, count_cons, beq_iff_eq]
    have := Nat.le_mul_self (count c l)
    split_ifs <;> simp_all <;> grind

@[gcongr]
/-
**List.Perm.offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.offDiag.Perm l₂.offDiag
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Prod.instLawfulBEq`：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [inst
_1 : BEq β] [LawfulBEq α] [LawfulBEq β], LawfulBEq (α × β)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.count_offDiag_eq_mul_sub_ite`：count_offDiag_eq_mul_sub_ite [Decidab
leEq α] (l : List α) (a b : α) : count (a, b) l.offDiag = count a l * count b l 
- if a = b then count a…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
protected theorem Perm.offDiag {l₁ l₂ : List α} (h : l₁ ~ l₂) : l₁.offDiag ~ l₂.offDiag := by
  classical simp_all [perm_iff_count, count_offDiag_eq_mul_sub_ite]
/-
**List.Nodup.offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l : List α}, l.Nodup → l.offDiag.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `Prod.instLawfulBEq`：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [inst
_1 : BEq β] [LawfulBEq α] [LawfulBEq β], LawfulBEq (α × β)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.count_offDiag_eq_mul_sub_ite`：count_offDiag_eq_mul_sub_ite [Decidab
leEq α] (l : List α) (a b : α) : count (a, b) l.offDiag = count a l * count b l 
- if a = b then count a…
-/
protected theorem Nodup.offDiag (h : l.Nodup) : l.offDiag.Nodup := by
  let := Classical.decEq α
  rw [nodup_iff_count_le_one]
  rintro ⟨x, y⟩
  rw [count_offDiag_eq_mul_sub_ite l x y]
  grind
/-
**List.Nodup.of_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l : List α}, l.offDiag.Nodup → l.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.not_le`：∀ {a b : ℕ}, ¬a ≤ b ↔ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.two_mul`：∀ (n : ℕ), 2 * n = n + n
· 使用定理 `Nat.mul_le_mul_right`：∀ {n m : ℕ} (k : ℕ), n ≤ m → n * k ≤ m * k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Prod.instLawfulBEq`：∀ {α : Type u_1} {β : Type u_2} [inst : BEq α] [inst
_1 : BEq β] [LawfulBEq α] [LawfulBEq β], LawfulBEq (α × β)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `List.count_offDiag_eq_mul_sub_ite`：count_offDiag_eq_mul_sub_ite [Decidab
leEq α] (l : List α) (a b : α) : count (a, b) l.offDiag = count a l * count b l 
- if a = b then count a…
-/
protected theorem Nodup.of_offDiag (h : l.offDiag.Nodup) : l.Nodup := by
  let := Classical.decEq α
  simp only [nodup_iff_count_le_one, Prod.forall, count_offDiag_eq_mul_sub_ite] at *
  intro a
  specialize h a a
  contrapose h
  rw [Nat.not_le] at h
  suffices 1 + l.count a < l.count a * l.count a by simpa
  calc
    1 + l.count a < l.count a + l.count a := by simpa
    _ ≤ l.count a * l.count a := by
      rw [← Nat.two_mul]
      exact Nat.mul_le_mul_right _ h

/-- `List.offDiag l` has no duplicates iff the original list has no duplicates. -/
@[simp]
/-
**List.nodup_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.of_offDiag`：∀ {α : Type u_1} {l : List α}, l.offDiag.Nodup → 
l.Nodup
· 使用定理 `List.Nodup.offDiag`：∀ {α : Type u_1} {l : List α}, l.Nodup → l.offDiag.N
odup

--- 原说明 ---
`List.offDiag l` has no duplicates iff the original list has no duplicates.
-/
theorem nodup_offDiag : l.offDiag.Nodup ↔ l.Nodup := ⟨.of_offDiag, .offDiag⟩

/-- If `l : List α` is a list with no duplicates, then `x : α × α` belongs to `List.offDiag l`
iff both components of `x` belong to `l` and they are not equal. -/
/-
**List.Nodup.mem_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u_1} {l : List α}, l.Nodup → ∀ {x : α × α}, x ∈ l.offDiag ↔ x.
1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Nodup.getElem_inj_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i 
: ℕ} {hi : i < l.length} {j : ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j

--- 原说明 ---
If `l : List α` is a list with no duplicates, then `x : α × α` belongs to `List.
offDiag l`
iff both components of `x` belong to `l` and they are not equal.
-/
theorem Nodup.mem_offDiag (h : l.Nodup) {x : α × α} :
    x ∈ l.offDiag ↔ x.1 ∈ l ∧ x.2 ∈ l ∧ x.1 ≠ x.2 := by
  rcases x with ⟨x, y⟩
  simp_rw [mem_offDiag_iff_getElem, mem_iff_getElem, Ne]
  constructor
  · rintro ⟨i, hi, j, hj, hne, rfl, rfl⟩
    exact ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, mt h.getElem_inj_iff.1 hne⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩, hne⟩
    exact ⟨i, hi, j, hj, mt h.getElem_inj_iff.2 hne, rfl, rfl⟩
/-
**List.map_prodMap_offDiag** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_prodMap_offDiag {β : Type*} (f : α -> β) (l : List α) : map (Prod.map 
f f) l.offDiag = (map f l).offDiag
参数：f : α -> β；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_flatMap`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {f : β 
→ γ} {g : α → List β} {l : List α},   List.map f (List.flatMap g l) = List.flatM
ap (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.eraseIdx_map`：eraseIdx_map (f : α -> β) (l : List α) (n : Nat) : (m
ap f l).eraseIdx n = (l.eraseIdx n).map f
· 使用定理 `List.zipIdx_map`：∀ {α : Type u_1} {β : Type u_2} {l : List α} {k : ℕ} {f
 : α → β},   (List.map f l).zipIdx k = List.map (Prod.map f id) (l.zipIdx k)
· 使用定理 `List.flatMap_map`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (f : α 
→ β) (g : β → List γ) (l : List α),   List.flatMap g (List.map f l) = List.flatM
ap (fu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_prodMap_offDiag {β : Type*} (f : α → β) (l : List α) :
    map (Prod.map f f) l.offDiag = (map f l).offDiag := by
  simp [offDiag, map_flatMap, zipIdx_map, flatMap_map, eraseIdx_map, Function.comp_def]

end List

