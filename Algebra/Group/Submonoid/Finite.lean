/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Data.Fintype.Basic

/-!
# Submonoids

This file provides some results on multiplicative and additive submonoids in the finite context.
-/

public section

namespace Submonoid

section Pi
variable {η : Type*} {f : η → Type*} [∀ i, MulOneClass (f i)]
variable {S : Type*} [SetLike S (Π i, f i)] [SubmonoidClass S (Π i, f i)]

open Set

@[to_additive]
/-
**Submonoid.pi_mem_of_mulSingle_mem_aux** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : S} (x : Π 
i, f i) (h1 : forall i, i ∉ I -> x i = 1) (h2 : forall i, i in I -> Pi.mulSingle
 i (x i) in H) : x in H
参数：I : Finset η；x : Π i, f i；h1 : forall i, i ∉ I -> x i = 1；h2 : forall i, i in
 I -> Pi.mulSingle i (x i) in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem pi_mem_of_mulSingle_mem_aux [DecidableEq η] (I : Finset η) {H : S} (x : Π i, f i)
    (h1 : ∀ i, i ∉ I → x i = 1) (h2 : ∀ i, i ∈ I → Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  induction I using Finset.induction_on generalizing x with
  | empty =>
    have : x = 1 := funext fun i => h1 i (Finset.notMem_empty i)
    exact this ▸ one_mem H
  | insert i I hnotMem ih =>
    have : x = Function.update x i 1 * Pi.mulSingle i (x i) := by
      ext j
      by_cases heq : j = i
      · subst heq
        simp
      · simp [heq]
    rw [this]
    clear this
    apply mul_mem (ih _ _ _) (by simp [h2]) <;> clear ih <;> intro j hj
    · by_cases heq : j = i
      · subst heq
        simp
      · simpa [heq] using h1 j (by simpa [heq] using hj)
    · have : j ≠ i := fun h => h ▸ hnotMem <| hj
      simp only [ne_eq, this, not_false_eq_true, Function.update_of_ne]
      exact h2 _ (Finset.mem_insert_of_mem hj)

@[to_additive]
/-
**Submonoid.pi_mem_of_mulSingle_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : S} (x : Π i, f i) 
(h : forall i, Pi.mulSingle i (x i) in H) : x in H
参数：x : Π i, f i；h : forall i, Pi.mulSingle i (x i) in H。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Submonoid.pi_mem_of_mulSingle_mem_aux`：pi_mem_of_mulSingle_mem_aux [Deci
dableEq η] (I : Finset η) {H : S} (x : Π i, f i) (h1 : forall i, i ∉ I -> x i = 
1) (h2 : forall i, i in I -…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem pi_mem_of_mulSingle_mem [Finite η] [DecidableEq η] {H : S} (x : Π i, f i)
    (h : ∀ i, Pi.mulSingle i (x i) ∈ H) : x ∈ H := by
  cases nonempty_fintype η
  exact pi_mem_of_mulSingle_mem_aux Finset.univ x (by simp) fun i _ => h i

/-- For finite index types, the `Submonoid.pi` is generated by the embeddings of the monoids. -/
@[to_additive /-- For finite index types, the `Submonoid.pi` is generated by the embeddings of the
additive monoids. -/]
/-
**Submonoid.pi_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：pi_le_iff [Finite η] [DecidableEq η] {H : Π i, Submonoid (f i)} {J : Submo
noid (Π i, f i)} : pi univ H <= J ↔ forall i : η, map (MonoidHom.mulSingle f i) 
(H i) <= J
参数：f i；Π i, f i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Submonoid.pi_mem_of_mulSingle_mem`：pi_mem_of_mulSingle_mem [Finite η] [D
ecidableEq η] {H : S} (x : Π i, f i) (h : forall i, Pi.mulSingle i (x i) in H) :
 x in H
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.mem_map_of_mem`：mem_map_of_mem (f : F) {S : Submonoid M} {x : 
M} (hx : x in S) : f x in S.map f
· 使用定理 `trivial`：True
-/
theorem pi_le_iff [Finite η] [DecidableEq η] {H : Π i, Submonoid (f i)} {J : Submonoid (Π i, f i)} :
    pi univ H ≤ J ↔ ∀ i : η, map (MonoidHom.mulSingle f i) (H i) ≤ J :=
  ⟨fun h i _ ⟨x, hx, H⟩ => h <| by simpa [← H],
   fun h x hx => pi_mem_of_mulSingle_mem x fun i => h i (mem_map_of_mem _ (hx i trivial))⟩

@[to_additive]
/-
**Submonoid.closure_pi** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：closure_pi [Finite η] {s : Π i, Set (f i)} (hs : forall i, 1 in s i) : clo
sure (univ.pi fun i => s i) = pi univ fun i => closure (s i)
参数：f i；hs : forall i, 1 in s i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submonoid.closure_le`：closure_le : closure s <= S ↔ s subseteq S
· 使用定理 `Set.pi_subset_pi_iff`：pi_subset_pi_iff : pi s t₁ subseteq pi s t₂ ↔ (for
all i in s, t₁ i subseteq t₂ i) ∨ pi s t₁ = ∅
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Submonoid.pi_le_iff`：pi_le_iff [Finite η] [DecidableEq η] {H : Π i, Subm
onoid (f i)} {J : Submonoid (Π i, f i)} : pi univ H <= J ↔ forall i : η, map (Mo
noidHom.m…
· 使用定理 `Submonoid.map_le_of_le_comap`：map_le_of_le_comap {T : Submonoid N} {f : 
F} : S <= T.comap f -> S.map f <= T
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用引理 `Pi.mulSingle_eq_of_ne`：mulSingle_eq_of_ne {i i' : ι} (h : i' != i) (x : 
M i) : mulSingle i x i' = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem closure_pi [Finite η] {s : Π i, Set (f i)} (hs : ∀ i, 1 ∈ s i) :
    closure (univ.pi fun i => s i) = pi univ fun i => closure (s i) :=
  le_antisymm
    (closure_le.2 <| pi_subset_pi_iff.2 <| .inl fun _ _ => subset_closure)
    (by
      classical
      exact pi_le_iff.mpr fun i => map_le_of_le_comap _ <| closure_le.2 fun _x hx =>
          subset_closure <| mem_univ_pi.mpr fun j => by
        by_cases H : j = i
        · subst H
          simpa
        · simpa [H] using hs _)

end Pi

end Submonoid

