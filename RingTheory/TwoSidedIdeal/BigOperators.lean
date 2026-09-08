/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.Congruence.BigOperators
public import Mathlib.RingTheory.TwoSidedIdeal.Basic

/-!
# Interactions between `∑, ∏` and two-sided ideals

-/

public section

namespace TwoSidedIdeal

section sum

variable {R : Type*} [NonUnitalNonAssocRing R] (I : TwoSidedIdeal R)

/-
**TwoSidedIdeal.listSum_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：listSum_mem {ι : Type*} (l : List ι) (f : ι -> R) (hl : forall x in l, f x
 in I) : (l.map f).sum in I
参数：l : List ι；f : ι -> R；hl : forall x in l, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.sum_map_zero`：∀ {ι : Type u_1} {M : Type u_2} [inst : AddZeroClass 
M] {l : List ι}, (List.map (fun x => 0) l).sum = 0
· 使用定理 `RingCon.listSum`：∀ {ι : Type u_1} {S : Type u_2} [inst : AddMonoid S] [i
nst_1 : Mul S] (t : RingCon S) (l : List ι) {f g : ι → S},   (∀ i ∈ l, t (f i) (
g i))…
-/
lemma listSum_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∀ x ∈ l, f x ∈ I) :
    (l.map f).sum ∈ I := by
  rw [mem_iff, ← List.sum_map_zero]
  exact I.ringCon.listSum l hl
/-
**TwoSidedIdeal.multisetSum_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：multisetSum_mem {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : forall x i
n s, f x in I) : (s.map f).sum in I
参数：s : Multiset ι；f : ι -> R；hs : forall x in s, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.sum_map_zero`：∀ {ι : Type u_2} {M : Type u_3} [inst : AddCommMo
noid M] {m : Multiset ι}, (Multiset.map (fun x => 0) m).sum = 0
· 使用定理 `RingCon.multisetSum`：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMono
id S] [inst_1 : Mul S] (t : RingCon S) (s : Multiset ι)   {f g : ι → S}, (∀ i ∈ 
s, t (f i…
-/
lemma multisetSum_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    (s.map f).sum ∈ I := by
  rw [mem_iff, ← Multiset.sum_map_zero]
  exact I.ringCon.multisetSum s hs
/-
**TwoSidedIdeal.finsetSum_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：finsetSum_mem {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : forall x in s,
 f x in I) : s.sum f in I
参数：s : Finset ι；f : ι -> R；hs : forall x in s, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `TwoSidedIdeal.mem_iff`：mem_iff (x : R) : x in I ↔ I.ringCon x 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `RingCon.finsetSum`：∀ {ι : Type u_1} {S : Type u_2} [inst : AddCommMonoid
 S] [inst_1 : Mul S] (t : RingCon S) (s : Finset ι) {f g : ι → S},   (∀ i ∈ s, t
 (f i) …
-/
lemma finsetSum_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∀ x ∈ s, f x ∈ I) :
    s.sum f ∈ I := by
  rw [mem_iff, ← Finset.sum_const_zero]
  exact I.ringCon.finsetSum s hs
/-
**TwoSidedIdeal.finsuppSum_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：finsuppSum_mem {ι : Type*} {β : Type*} [Zero β] {f : ι ->₀ β} (g : ι -> β 
-> R) (h : forall i in f.support, g i (f i) in I) : f.sum g in I
参数：g : ι -> β -> R；h : forall i in f.support, g i (f i) in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.finsetSum_mem`：finsetSum_mem {ι : Type*} (s : Finset ι) (f
 : ι -> R) (hs : forall x in s, f x in I) : s.sum f in I
-/
lemma finsuppSum_mem {ι : Type*} {β : Type*} [Zero β]
    {f : ι →₀ β} (g : ι → β → R) (h : ∀ i ∈ f.support, g i (f i) ∈ I) :
    f.sum g ∈ I :=
  finsetSum_mem _ _ _ h
/-
**TwoSidedIdeal.dfinsuppSum_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：dfinsuppSum_mem {ι : Type*} {β : ι -> Type*} [DecidableEq ι] [forall i, Ze
ro (β i)] [(i : ι) -> (x : β i) -> Decidable (x != 0)] {f : Π₀ i, β i} (g : (i :
 ι) -> β i -> R) (h : forall i in f.support, g i (f i) in I) : f.sum g in I
参数：β i；i : ι；x : β i；x != 0；g : (i : ι) -> β i -> R；h : forall i in f.support, g
 i (f i) in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.finsetSum_mem`：finsetSum_mem {ι : Type*} (s : Finset ι) (f
 : ι -> R) (hs : forall x in s, f x in I) : s.sum f in I
-/
lemma dfinsuppSum_mem {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [∀ i, Zero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)]
    {f : Π₀ i, β i} (g : (i : ι) → β i → R) (h : ∀ i ∈ f.support, g i (f i) ∈ I) :
    f.sum g ∈ I :=
  finsetSum_mem _ _ _ h

end sum

section prod

section ring

variable {R : Type*} [Ring R] (I : TwoSidedIdeal R)

/-
**TwoSidedIdeal.listProd_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：listProd_mem {ι : Type*} (l : List ι) (f : ι -> R) (hl : exists x in l, f 
x in I) : (l.map f).prod in I
参数：l : List ι；f : ι -> R；hl : exists x in l, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用引理 `TwoSidedIdeal.mul_mem_right`：mul_mem_right (x y) (hx : x in I) : x * y i
n I
· 使用引理 `TwoSidedIdeal.mul_mem_left`：mul_mem_left (x y) (hy : y in I) : x * y in 
I
-/
lemma listProd_mem {ι : Type*} (l : List ι) (f : ι → R) (hl : ∃ x ∈ l, f x ∈ I) :
    (l.map f).prod ∈ I := by
  induction l with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hl
  | cons x l ih =>
    simp only [List.mem_cons, exists_eq_or_imp] at hl
    rcases hl with h | hal
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_right _ _ h
    · simpa only [List.map_cons, List.prod_cons] using I.mul_mem_left _ _ <| ih hal

end ring

section commRing

variable {R : Type*} [CommRing R] (I : TwoSidedIdeal R)

/-
**TwoSidedIdeal.multiSetProd_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：multiSetProd_mem {ι : Type*} (s : Multiset ι) (f : ι -> R) (hs : exists x 
in s, f x in I) : (s.map f).prod in I
参数：s : Multiset ι；f : ι -> R；hs : exists x in s, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.listProd_mem`：listProd_mem {ι : Type*} (l : List ι) (f : ι
 -> R) (hl : exists x in l, f x in I) : (l.map f).prod in I
-/
lemma multiSetProd_mem {ι : Type*} (s : Multiset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
    (s.map f).prod ∈ I := by
  rcases s
  simpa using listProd_mem (hl := hs)
/-
**TwoSidedIdeal.finsetProd_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：finsetProd_mem {ι : Type*} (s : Finset ι) (f : ι -> R) (hs : exists x in s
, f x in I) : s.prod f in I
参数：s : Finset ι；f : ι -> R；hs : exists x in s, f x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.multiSetProd_mem`：multiSetProd_mem {ι : Type*} (s : Multis
et ι) (f : ι -> R) (hs : exists x in s, f x in I) : (s.map f).prod in I
-/
lemma finsetProd_mem {ι : Type*} (s : Finset ι) (f : ι → R) (hs : ∃ x ∈ s, f x ∈ I) :
    s.prod f ∈ I := by
  rcases s
  simpa using multiSetProd_mem (hs := hs)
/-
**TwoSidedIdeal.finsuppProd_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：finsuppProd_mem {ι : Type*} {β : Type*} [Zero β] (h : ι -> β -> R) {f : ι 
->₀ β} (H : exists i in f.support, h i (f i) in I) : f.prod h in I
参数：h : ι -> β -> R；H : exists i in f.support, h i (f i) in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.finsetProd_mem`：finsetProd_mem {ι : Type*} (s : Finset ι) 
(f : ι -> R) (hs : exists x in s, f x in I) : s.prod f in I
-/
lemma finsuppProd_mem {ι : Type*} {β : Type*} [Zero β]
    (h : ι → β → R) {f : ι →₀ β} (H : ∃ i ∈ f.support, h i (f i) ∈ I) : f.prod h ∈ I :=
  finsetProd_mem _ _ _ H
/-
**TwoSidedIdeal.dfinsuppProd_mem** 是 Mathlib 中的一个引理，位于命名空间 `TwoSidedIdeal`。
形式化陈述：dfinsuppProd_mem {ι : Type*} {β : ι -> Type*} [DecidableEq ι] [forall i, Z
ero (β i)] [(i : ι) -> (x : β i) -> Decidable (x != 0)] {f : Π₀ i, β i} (g : (i 
: ι) -> β i -> R) (h : exists i in f.support, g i (f i) in I) : f.prod g in I
参数：β i；i : ι；x : β i；x != 0；g : (i : ι) -> β i -> R；h : exists i in f.support, g
 i (f i) in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TwoSidedIdeal.finsetProd_mem`：finsetProd_mem {ι : Type*} (s : Finset ι) 
(f : ι -> R) (hs : exists x in s, f x in I) : s.prod f in I
-/
lemma dfinsuppProd_mem {ι : Type*} {β : ι → Type*}
    [DecidableEq ι] [∀ i, Zero (β i)] [(i : ι) → (x : β i) → Decidable (x ≠ 0)]
    {f : Π₀ i, β i} (g : (i : ι) → β i → R) (h : ∃ i ∈ f.support, g i (f i) ∈ I) :
    f.prod g ∈ I :=
  finsetProd_mem _ _ _ h

end commRing

end prod

end TwoSidedIdeal

