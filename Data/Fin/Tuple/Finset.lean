/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi

/-!
# Fin-indexed tuples of finsets
-/

public section

open Fin Fintype

namespace Fin
variable {n : ℕ} {α : Fin (n + 1) → Type*} {f : ∀ i, α i} {s : ∀ i, Finset (α i)} {p : Fin (n + 1)}

/-
**Fin.mem_piFinset_iff_zero_tail** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：mem_piFinset_iff_zero_tail : f in Fintype.piFinset s ↔ f 0 in s 0 ∧ tail f
 in piFinset (tail s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_piFinset_iff_zero_tail :
    f ∈ Fintype.piFinset s ↔ f 0 ∈ s 0 ∧ tail f ∈ piFinset (tail s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ, tail]
/-
**Fin.mem_piFinset_iff_last_init** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：mem_piFinset_iff_last_init : f in piFinset s ↔ f (last n) in s (last n) ∧ 
init f in piFinset (init s)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_piFinset_iff_last_init :
    f ∈ piFinset s ↔ f (last n) ∈ s (last n) ∧ init f ∈ piFinset (init s) := by
  simp only [Fintype.mem_piFinset, forall_fin_succ', init, and_comm]
/-
**Fin.mem_piFinset_iff_pivot_removeNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：mem_piFinset_iff_pivot_removeNth (p : Fin (n + 1)) : f in piFinset s ↔ f p
 in s p ∧ removeNth p f in piFinset (removeNth p s)
参数：p : Fin (n + 1)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_piFinset_iff_pivot_removeNth (p : Fin (n + 1)) :
    f ∈ piFinset s ↔ f p ∈ s p ∧ removeNth p f ∈ piFinset (removeNth p s) := by
  simp only [Fintype.mem_piFinset, forall_iff_succAbove p, removeNth]
/-
**Fin.cons_mem_piFinset_cons** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：cons_mem_piFinset_cons {x_zero : α 0} {x_tail : (i : Fin n) -> α i.succ} {
s_zero : Finset (α 0)} {s_tail : (i : Fin n) -> Finset (α i.succ)} : cons x_zero
 x_tail in piFinset (cons s_zero s_tail) ↔ x_zero in s_zero ∧ x_tail in piFinset
 s_tail
参数：i : Fin n；α 0；i : Fin n；α i.succ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.tail_cons`：tail_cons : tail (cons x p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cons_mem_piFinset_cons {x_zero : α 0} {x_tail : (i : Fin n) → α i.succ}
    {s_zero : Finset (α 0)} {s_tail : (i : Fin n) → Finset (α i.succ)} :
    cons x_zero x_tail ∈ piFinset (cons s_zero s_tail) ↔
      x_zero ∈ s_zero ∧ x_tail ∈ piFinset s_tail := by
  simp_rw [mem_piFinset_iff_zero_tail, cons_zero, tail_cons]
/-
**Fin.snoc_mem_piFinset_snoc** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：snoc_mem_piFinset_snoc {x_last : α (last n)} {x_init : (i : Fin n) -> α i.
castSucc} {s_last : Finset (α (last n))} {s_init : (i : Fin n) -> Finset (α i.ca
stSucc)} : snoc x_init x_last in piFinset (snoc s_init s_last) ↔ x_last in s_las
t ∧ x_init in piFinset s_init
参数：last n；i : Fin n；α (last n)；i : Fin n；α i.castSucc。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fin.init_snoc`：init_snoc : init (snoc p x) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma snoc_mem_piFinset_snoc {x_last : α (last n)} {x_init : (i : Fin n) → α i.castSucc}
    {s_last : Finset (α (last n))} {s_init : (i : Fin n) → Finset (α i.castSucc)} :
    snoc x_init x_last ∈ piFinset (snoc s_init s_last) ↔
      x_last ∈ s_last ∧ x_init ∈ piFinset s_init := by
  simp_rw [mem_piFinset_iff_last_init, init_snoc, snoc_last]
/-
**Fin.insertNth_mem_piFinset_insertNth** 是 Mathlib 中的一个引理，位于命名空间 `Fin`。
形式化陈述：insertNth_mem_piFinset_insertNth {x_pivot : α p} {x_remove : forall i, α (
succAbove p i)} {s_pivot : Finset (α p)} {s_remove : forall i, Finset (α (succAb
ove p i))} : insertNth p x_pivot x_remove in piFinset (insertNth p s_pivot s_rem
ove) ↔ x_pivot in s_pivot ∧ x_remove in piFinset s_remove
参数：succAbove p i；α p；α (succAbove p i)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Fin.mem_piFinset_iff_pivot_removeNth`：mem_piFinset_iff_pivot_removeNth (
p : Fin (n + 1)) : f in piFinset s ↔ f p in s p ∧ removeNth p f in piFinset (rem
oveNth p s)
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.removeNth_insertNth`：∀ {n : ℕ} {α : Fin (n + 1) → Sort u_1} (p : Fin
 (n + 1)) (a : α p) (f : (i : Fin n) → α (p.succAbove i)),   p.removeNth (p.inse
rtNth a f) = …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma insertNth_mem_piFinset_insertNth {x_pivot : α p} {x_remove : ∀ i, α (succAbove p i)}
    {s_pivot : Finset (α p)} {s_remove : ∀ i, Finset (α (succAbove p i))} :
    insertNth p x_pivot x_remove ∈ piFinset (insertNth p s_pivot s_remove) ↔
      x_pivot ∈ s_pivot ∧ x_remove ∈ piFinset s_remove := by
  simp [mem_piFinset_iff_pivot_removeNth p]

end Fin

namespace Finset
variable {n : ℕ} {α : Fin (n + 1) → Type*} {p : Fin (n + 1)} (S : ∀ i, Finset (α i))

/-
**Finset.map_consEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_consEquiv_filter_piFinset (P : (forall i, α (succ i)) -> Prop) [Decida
blePred P] : {r in piFinset S | P (tail r)}.map (consEquiv α).symm.toEmbedding =
 S 0 ×ˢ {r in piFinset (tail S) | P r}
参数：P : (forall i, α (succ i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.consEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_1) (f : α 0 × (
(i : Fin n) → α i.succ)) (i : Fin (n + 1)),   (Fin.consEquiv α) f i = Fin.cons f
.1 f.2 i
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)}.map (consEquiv α).symm.toEmbedding =
      S 0 ×ˢ {r ∈ piFinset (tail S) | P r} := by
  unfold tail; ext; simp [Fin.forall_iff_succ, and_assoc]
/-
**Finset.map_snocEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_snocEquiv_filter_piFinset (P : (forall i, α (castSucc i)) -> Prop) [De
cidablePred P] : {r in piFinset S | P (init r)}.map (snocEquiv α).symm.toEmbeddi
ng = S (last _) ×ˢ {r in piFinset (init S) | P r}
参数：P : (forall i, α (castSucc i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.snocEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u_2) (f : α (Fin.
last n) × ((i : Fin n) → α i.castSucc)) (x : Fin (n + 1)),   (Fin.snocEquiv α) f
 x = Fin.…
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)}.map (snocEquiv α).symm.toEmbedding =
      S (last _) ×ˢ {r ∈ piFinset (init S) | P r} := by
  unfold init; ext; simp [Fin.forall_iff_castSucc, and_assoc]
/-
**Finset.map_insertNthEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_insertNthEquiv_filter_piFinset (P : (forall i, α (p.succAbove i)) -> P
rop) [DecidablePred P] : {r in piFinset S | P (p.removeNth r)}.map (p.insertNthE
quiv α).symm.toEmbedding = S p ×ˢ {r in piFinset (p.removeNth S) | P r}
参数：P : (forall i, α (p.succAbove i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.insertNthEquiv_apply`：∀ {n : ℕ} (α : Fin (n + 1) → Type u) (p : Fin 
(n + 1)) (f : α p × ((i : Fin n) → α (p.succAbove i))) (j : Fin (n + 1)),   (Fin
.insertNthEqui…
· 使用定理 `Fin.forall_iff_succAbove`：forall_iff_succAbove {P : Fin (n + 1) -> Prop}
 (p : Fin (n + 1)) : (forall i, P i) ↔ P p ∧ forall i, P (p.succAbove i)
· 使用定理 `Fin.insertNth_apply_same`：insertNth_apply_same (i : Fin (n + 1)) (x : α 
i) (p : forall j, α (i.succAbove j)) : insertNth i x p i = x
· 使用定理 `Fin.insertNth_apply_succAbove`：insertNth_apply_succAbove (i : Fin (n + 1
)) (x : α i) (p : forall j, α (i.succAbove j)) (j : Fin n) : insertNth i x p (i.
succAbove j) = p j
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)}.map (p.insertNthEquiv α).symm.toEmbedding =
      S p ×ˢ {r ∈ piFinset (p.removeNth  S) | P r} := by
  unfold removeNth; ext; simp [Fin.forall_iff_succAbove p, and_assoc]
/-
**Finset.filter_piFinset_eq_map_consEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_piFinset_eq_map_consEquiv (P : (forall i, α (succ i)) -> Prop) [Dec
idablePred P] : {r in piFinset S | P (tail r)} = (S 0 ×ˢ {r in piFinset (tail S)
 | P r}).map (consEquiv α).toEmbedding
参数：P : (forall i, α (succ i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_piFinset_eq_map_consEquiv (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)} =
      (S 0 ×ˢ {r ∈ piFinset (tail S) | P r}).map (consEquiv α).toEmbedding := by
  simp [← map_consEquiv_filter_piFinset, map_map]
/-
**Finset.filter_piFinset_eq_map_snocEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：filter_piFinset_eq_map_snocEquiv (P : (forall i, α (castSucc i)) -> Prop) 
[DecidablePred P] : {r in piFinset S | P (init r)} = (S (last _) ×ˢ {r in piFins
et (init S) | P r}).map (snocEquiv α).toEmbedding
参数：P : (forall i, α (castSucc i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_piFinset_eq_map_snocEquiv (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)} =
      (S (last _) ×ˢ {r ∈ piFinset (init S) | P r}).map (snocEquiv α).toEmbedding := by
  simp [← map_snocEquiv_filter_piFinset, map_map]
/-
**Finset.filter_piFinset_eq_map_insertNthEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：filter_piFinset_eq_map_insertNthEquiv (P : (forall i, α (p.succAbove i)) -
> Prop) [DecidablePred P] : {r in piFinset S | P (p.removeNth r)} = (S p ×ˢ {r i
n piFinset (p.removeNth S) | P r}).map (p.insertNthEquiv α).toEmbedding
参数：P : (forall i, α (p.succAbove i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Embedding.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun
 toFun_1 : α → β) (e_toFun : toFun = toFun_1) (inj' : Function.Injective toFun),
   { toFun := toFun, i…
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Finset.map_refl`：map_refl : s.map (Embedding.refl _) = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma filter_piFinset_eq_map_insertNthEquiv (P : (∀ i, α (p.succAbove i)) → Prop)
    [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)} =
      (S p ×ˢ {r ∈ piFinset (p.removeNth  S) | P r}).map (p.insertNthEquiv α).toEmbedding := by
  simp [← map_insertNthEquiv_filter_piFinset, map_map]
/-
**Finset.card_consEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_consEquiv_filter_piFinset (P : (forall i, α (succ i)) -> Prop) [Decid
ablePred P] : {r in piFinset S | P (tail r)}.card = (S 0).card * {r in piFinset 
(tail S) | P r}.card
参数：P : (forall i, α (succ i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Finset.map_consEquiv_filter_piFinset`：map_consEquiv_filter_piFinset (P :
 (forall i, α (succ i)) -> Prop) [DecidablePred P] : {r in piFinset S | P (tail 
r)}.map (consEquiv α).symm…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_consEquiv_filter_piFinset (P : (∀ i, α (succ i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (tail r)}.card = (S 0).card * {r ∈ piFinset (tail S) | P r}.card := by
  rw [← card_product, ← map_consEquiv_filter_piFinset, card_map]
/-
**Finset.card_snocEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_snocEquiv_filter_piFinset (P : (forall i, α (castSucc i)) -> Prop) [D
ecidablePred P] : {r in piFinset S | P (init r)}.card = (S (last _)).card * {r i
n piFinset (init S) | P r}.card
参数：P : (forall i, α (castSucc i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Finset.map_snocEquiv_filter_piFinset`：map_snocEquiv_filter_piFinset (P :
 (forall i, α (castSucc i)) -> Prop) [DecidablePred P] : {r in piFinset S | P (i
nit r)}.map (snocEquiv α).…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_snocEquiv_filter_piFinset (P : (∀ i, α (castSucc i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (init r)}.card =
      (S (last _)).card * {r ∈ piFinset (init S) | P r}.card := by
  rw [← card_product, ← map_snocEquiv_filter_piFinset, card_map]
/-
**Finset.card_insertNthEquiv_filter_piFinset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：card_insertNthEquiv_filter_piFinset (P : (forall i, α (p.succAbove i)) -> 
Prop) [DecidablePred P] : {r in piFinset S | P (p.removeNth r)}.card = (S p).car
d * {r in piFinset (p.removeNth S) | P r}.card
参数：P : (forall i, α (p.succAbove i)) -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Finset.map_insertNthEquiv_filter_piFinset`：map_insertNthEquiv_filter_piF
inset (P : (forall i, α (p.succAbove i)) -> Prop) [DecidablePred P] : {r in piFi
nset S | P (p.removeNth r)}.map…
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
lemma card_insertNthEquiv_filter_piFinset (P : (∀ i, α (p.succAbove i)) → Prop) [DecidablePred P] :
    {r ∈ piFinset S | P (p.removeNth r)}.card =
      (S p).card * {r ∈ piFinset (p.removeNth  S) | P r}.card := by
  rw [← card_product, ← map_insertNthEquiv_filter_piFinset, card_map]

end Finset

