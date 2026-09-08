/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau, Kim Morrison, Alex Keizer
-/
module

public import Mathlib.Data.List.OfFn
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.Nodup

/-!
# Lists of elements of `Fin n`

This file develops some results on `finRange n`.
-/

public section

assert_not_exists Monoid

universe u

namespace List

variable {α : Type u}


@[simp]
/-
**List.count_finRange** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：count_finRange {n : Nat} (a : Fin n) : count a (finRange n) = 1
参数：a : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Std.LawfulBEqOrd.lawfulBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord 
α] [Std.LawfulBEqOrd α] [Std.LawfulEqOrd α], LawfulBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Fin.instLawfulEqOrd`：∀ (n : ℕ), Std.LawfulEqOrd (Fin n)
· 使用定理 `List.Nodup.count`：∀ {α : Type u_1} [inst : BEq α] [inst_1 : LawfulBEq α]
 {a : α} {l : List α},   l.Nodup → List.count a l = if a ∈ l then 1 else 0
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma count_finRange {n : ℕ} (a : Fin n) : count a (finRange n) = 1 := by
  simp [List.Nodup.count (nodup_finRange n)]
/-
**List.idxOf_finRange** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {k : ℕ} (i : Fin k), List.idxOf i (List.finRange k) = ↑i
参数：i : Fin k；List.finRange k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `List.getElem_finRange`：∀ {n i : ℕ} (h : i < (List.finRange n).length), (
List.finRange n)[i] = Fin.cast ⋯ ⟨i, h⟩
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `List.Nodup.idxOf_getElem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] 
{xs : List α},   xs.Nodup → ∀ (i : ℕ) (h : i < xs.length), List.idxOf xs[i] xs =
 i
· 使用定理 `Std.LawfulBEqOrd.lawfulBEq`：∀ {α : Type u} [inst : BEq α] [inst_1 : Ord 
α] [Std.LawfulBEqOrd α] [Std.LawfulEqOrd α], LawfulBEq α
· 使用定理 `Std.LawfulBCmp.toLawfulBEqCmp`：∀ {α : Type u_1} {inst : LE α} {inst_1 : 
LT α} {inst_2 : BEq α} {cmp : α → α → Ordering} [self : Std.LawfulBCmp cmp],   S
td.LawfulBEqCmp cmp
· 使用定理 `instLawfulBCmpCompare_mathlib`：∀ {α : Type u_1} [inst : LinearOrder α], 
Std.LawfulBCmp compare
· 使用定理 `Fin.instLawfulEqOrd`：∀ (n : ℕ), Std.LawfulEqOrd (Fin n)
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
-/
@[simp] theorem idxOf_finRange {k : ℕ} (i : Fin k) : (finRange k).idxOf i = i := by
  simpa using (nodup_finRange k).idxOf_getElem i
/-
**List.ofFn_eq_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_eq_pmap {n} {f : Fin n -> α} : ofFn f = pmap (fun i hi => f ⟨i, hi⟩) 
(range n) fun _ => mem_range.1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
-/
theorem ofFn_eq_pmap {n} {f : Fin n → α} :
    ofFn f = pmap (fun i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1 := by
  ext
  grind
/-
**List.ofFn_id** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_id (n) : ofFn id = finRange n
参数：n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofFn_id (n) : ofFn id = finRange n :=
  (rfl)
/-
**List.ofFn_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange n).map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.ofFn_id`：ofFn_id (n) : ofFn id = finRange n
· 使用定理 `List.map_ofFn`：∀ {n : ℕ} {α : Type u_1} {β : Type u_2} {f : Fin n → α} {
g : α → β}, List.map g (List.ofFn f) = List.ofFn (g ∘ f)
· 使用定理 `Function.comp_id`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β), f ∘ id = 
f
-/
theorem ofFn_eq_map {n} {f : Fin n → α} : ofFn f = (finRange n).map f := by
  rw [← ofFn_id, map_ofFn, Function.comp_id]
/-
**List.nodup_ofFn_ofInjective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_ofFn_ofInjective {n} {f : Fin n -> α} (hf : Function.Injective f) : 
Nodup (ofFn f)
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_range`：∀ {m n : ℕ}, m ∈ List.range n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_pmap`：ofFn_eq_pmap {n} {f : Fin n -> α} : ofFn f = pmap (fu
n i hi => f ⟨i, hi⟩) (range n) fun _ => mem_range.1
· 使用定理 `List.Nodup.pmap`：∀ {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α)
 → p a → β} {l : List α} {H : ∀ a ∈ l, p a},   (∀ (a : α) (ha : p a) (b : α) (hb
 : p …
· 使用定理 `Fin.val_eq_of_eq`：∀ {n : ℕ} {i j : Fin n}, i = j → ↑i = ↑j
· 使用定理 `List.nodup_range`：∀ {n : ℕ}, (List.range n).Nodup
-/
theorem nodup_ofFn_ofInjective {n} {f : Fin n → α} (hf : Function.Injective f) :
    Nodup (ofFn f) := by
  rw [ofFn_eq_pmap]
  exact nodup_range.pmap fun _ _ _ _ H => Fin.val_eq_of_eq <| hf H
/-
**List.nodup_ofFn** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_ofFn {n} {f : Fin n -> α} : Nodup (ofFn f) ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.injective_of_subsingleton`：∀ {α : Sort u_1} {β : Sort u_2} [Sub
singleton α] (f : α → β), Function.Injective f
· 使用定理 `Fin.subsingleton_zero`：Subsingleton (Fin 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_injective_iff`：cons_injective_iff {α} {x₀ : α} {x : Fin n -> α}
 : Function.Injective (cons x₀ x : Fin n.succ -> α) ↔ x₀ ∉ Set.range x ∧ Functio
n.Injective …
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `List.ofFn_succ`：∀ {α : Type u_1} {n : ℕ} {f : Fin (n + 1) → α}, List.ofF
n f = f 0 :: List.ofFn fun i => f i.succ
· 使用定理 `List.nodup_ofFn_ofInjective`：nodup_ofFn_ofInjective {n} {f : Fin n -> α}
 (hf : Function.Injective f) : Nodup (ofFn f)
-/
theorem nodup_ofFn {n} {f : Fin n → α} : Nodup (ofFn f) ↔ Function.Injective f := by
  refine ⟨?_, nodup_ofFn_ofInjective⟩
  refine Fin.consInduction ?_ (fun x₀ xs ih => ?_) f
  · intro _
    exact Function.injective_of_subsingleton _
  · intro h
    rw [Fin.cons_injective_iff]
    simp_rw [ofFn_succ, Fin.cons_succ, nodup_cons, Fin.cons_zero, mem_ofFn] at h
    exact h.imp_right ih

end List

open List

/-
**Equiv.Perm.map_finRange_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.map_finRange_perm {n : Nat} (σ : Equiv.Perm (Fin n)) : map σ (f
inRange n) ~ finRange n
参数：σ : Equiv.Perm (Fin n)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.perm_ext_iff_of_nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup 
→ l₂.Nodup → (l₁.Perm l₂ ↔ ∀ (a : α), a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `List.nodup_finRange`：∀ (n : ℕ), (List.finRange n).Nodup
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem Equiv.Perm.map_finRange_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    map σ (finRange n) ~ finRange n := by
  rw [perm_ext_iff_of_nodup ((nodup_finRange n).map σ.injective) <| nodup_finRange n]
  simpa [mem_map, mem_finRange] using! σ.surjective

/-- The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`. -/
/-
**Equiv.Perm.ofFn_comp_perm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equiv.Perm.ofFn_comp_perm {n : Nat} {α : Type u} (σ : Equiv.Perm (Fin n)) 
(f : Fin n -> α) : ofFn (f ∘ σ) ~ ofFn f
参数：σ : Equiv.Perm (Fin n)；f : Fin n -> α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.ofFn_eq_map`：ofFn_eq_map {n} {f : Fin n -> α} : ofFn f = (finRange 
n).map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_map`：∀ {β : Type u_1} {γ : Type u_2} {α : Type u_3} {g : β → γ}
 {f : α → β} {l : List α},   List.map g (List.map f l) = List.map (g ∘ f) l
· 使用定理 `List.Perm.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : List
 α}, l₁.Perm l₂ → (List.map f l₁).Perm (List.map f l₂)
· 使用定理 `Equiv.Perm.map_finRange_perm`：Equiv.Perm.map_finRange_perm {n : Nat} (σ 
: Equiv.Perm (Fin n)) : map σ (finRange n) ~ finRange n

--- 原说明 ---
The list obtained from a permutation of a tuple `f` is permutation equivalent to
the list obtained from `f`.
-/
theorem Equiv.Perm.ofFn_comp_perm {n : ℕ} {α : Type u} (σ : Equiv.Perm (Fin n)) (f : Fin n → α) :
    ofFn (f ∘ σ) ~ ofFn f := by
  rw [ofFn_eq_map, ofFn_eq_map, ← map_map]
  exact σ.map_finRange_perm.map f
