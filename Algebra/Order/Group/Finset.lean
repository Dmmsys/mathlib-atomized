/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
module

public import Mathlib.Algebra.Order.Group.OrderIso
public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.MinMax
public import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Data.Finset.Lattice.Prod

/-!
# `Finset.sup` in a group
-/

public section

open scoped Finset

assert_not_exists MonoidWithZero

namespace Multiset
variable {α : Type*} [DecidableEq α]

/-
**Multiset.toFinset_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：∀ {α : Type u_1} [inst : DecidableEq α] (s : Multiset α) (n : ℕ), n ≠ 0 → 
(n • s).toFinset = s.toFinset
参数：s : Multiset α；n : ℕ；n • s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toFinset_nsmul (s : Multiset α) : ∀ n ≠ 0, (n • s).toFinset = s.toFinset
  | 0, h => by contradiction
  | n + 1, _ => by
    by_cases h : n = 0
    · rw [h, zero_add, one_nsmul]
    · rw [add_nsmul, toFinset_add, one_nsmul, toFinset_nsmul s n h, Finset.union_idempotent]
/-
**Multiset.toFinset_eq_singleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：toFinset_eq_singleton_iff (s : Multiset α) (a : α) : s.toFinset = {a} ↔ ca
rd s != 0 ∧ s = card s • {a}
参数：s : Multiset α；a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.empty_ne_singleton`：empty_ne_singleton (a : α) : ∅ != ({a} : Fins
et α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.toFinset_zero`：toFinset_zero : toFinset (0 : Multiset α) = ∅
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.card_eq_zero`：card_eq_zero {s : Multiset α} : card s = 0 ↔ s = 
0
· 使用定理 `Multiset.ext'`：ext' {s t : Multiset α} : (forall a, count a s = count a 
t) -> s = t
· 使用引理 `Multiset.count_nsmul`：count_nsmul (a : α) (n s) : count a (n • s) = n * 
count a s
· 使用定理 `Multiset.count_singleton`：count_singleton (a b : α) : count a ({b} : Mul
tiset α) = if a = b then 1 else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.count.congr_simp`：∀ {α : Type u_1} {inst : DecidableEq α} [inst
_1 : DecidableEq α] (a a_1 : α),   a = a_1 → ∀ (a_2 a_3 : Multiset α), a_2 = a_3
 → Multiset.cou…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Multiset.count_eq_zero_of_notMem`：count_eq_zero_of_notMem {a : α} {s : M
ultiset α} (h : a ∉ s) : count a s = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Multiset.toFinset_nsmul`：∀ {α : Type u_1} [inst : DecidableEq α] (s : Mu
ltiset α) (n : ℕ), n ≠ 0 → (n • s).toFinset = s.toFinset
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.toFinset_singleton`：toFinset_singleton (a : α) : toFinset ({a} 
: Multiset α) = {a}
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma toFinset_eq_singleton_iff (s : Multiset α) (a : α) :
    s.toFinset = {a} ↔ card s ≠ 0 ∧ s = card s • {a} := by
  refine ⟨fun H ↦ ⟨fun h ↦ ?_, ext' fun x ↦ ?_⟩, fun H ↦ ?_⟩
  · rw [card_eq_zero.1 h, toFinset_zero] at H
    exact Finset.empty_ne_singleton _ H
  · rw [count_nsmul, count_singleton]
    by_cases hx : x = a
    · simp_rw [hx, ite_true, mul_one, count_eq_card]
      intro y hy
      rw [← mem_toFinset, H, Finset.mem_singleton] at hy
      exact hy.symm
    have hx' : x ∉ s := fun h' ↦ hx <| by rwa [← mem_toFinset, H, Finset.mem_singleton] at h'
    simp_rw [count_eq_zero_of_notMem hx', hx, ite_false, Nat.mul_zero]
  simpa only [toFinset_nsmul _ _ H.1, toFinset_singleton] using congr($(H.2).toFinset)
/-
**Multiset.toFinset_card_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Multiset`。
形式化陈述：toFinset_card_eq_one_iff (s : Multiset α) : #s.toFinset = 1 ↔ Multiset.car
d s != 0 ∧ exists a : α, s = Multiset.card s • {a}
参数：s : Multiset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toFinset_card_eq_one_iff (s : Multiset α) :
    #s.toFinset = 1 ↔ Multiset.card s ≠ 0 ∧ ∃ a : α, s = Multiset.card s • {a} := by
  simp_rw [Finset.card_eq_one, Multiset.toFinset_eq_singleton_iff, exists_and_left]

end Multiset

namespace Finset
variable {ι κ M G : Type*}

/-
**Finset.fold_max_add** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : 
WithBot M) (f : ι -> M) : s.fold max ⊥ (fun i => ↑(f i) + a) = s.fold max ⊥ ((↑)
 ∘ f) + a
参数：s : Finset ι；a : WithBot M；f : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `instCommutativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Commutati
ve max
· 使用定理 `instAssociativeMax`：∀ {α : Type u} [inst : LinearOrder α], Std.Associati
ve max
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.fold_congr`：fold_congr {g : α -> β} (H : forall x in s, f x = g x
) : s.fold op b f = s.fold op b g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.fold_insert`：fold_insert [DecidableEq α] (h : a ∉ s) : (insert a 
s).fold op b f = f a * s.fold op b f
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `max_add_add_right`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Add
 α] [AddRightMono α] (a b c : α), max (a + c) (b + c) = max a b + c
-/
lemma fold_max_add [LinearOrder M] [Add M] [AddRightMono M] (s : Finset ι) (a : WithBot M)
    (f : ι → M) : s.fold max ⊥ (fun i ↦ ↑(f i) + a) = s.fold max ⊥ ((↑) ∘ f) + a := by
  classical induction s using Finset.induction_on <;> simp [*, max_add_add_right]

@[to_additive nsmul_inf']
/-
**Finset.inf'_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : LinearOrder M] [inst_1 : Monoid M]
 [MulLeftMono M] [MulRightMono M]   (s : Finset ι) (f : ι → M) (n : ℕ) (hs : s.N
onempty), s.inf' hs f ^ n = s.inf' hs fun a => f a ^ n
参数：s : Finset ι；f : ι → M；n : ℕ；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_inf'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
-/
lemma inf'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.inf' hs f ^ n = s.inf' hs fun a ↦ f a ^ n :=
  map_finset_inf' (OrderHom.mk _ <| pow_left_mono n) hs _

@[to_additive nsmul_sup']
/-
**Finset.sup'_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : LinearOrder M] [inst_1 : Monoid M]
 [MulLeftMono M] [MulRightMono M]   (s : Finset ι) (f : ι → M) (n : ℕ) (hs : s.N
onempty), s.sup' hs f ^ n = s.sup' hs fun a => f a ^ n
参数：s : Finset ι；f : ι → M；n : ℕ；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
· 使用定理 `pow_left_mono`：pow_left_mono (n : Nat) : Monotone fun a : M => a ^ n
-/
lemma sup'_pow [LinearOrder M] [Monoid M] [MulLeftMono M] [MulRightMono M] (s : Finset ι)
    (f : ι → M) (n : ℕ) (hs) : s.sup' hs f ^ n = s.sup' hs fun a ↦ f a ^ n :=
  map_finset_sup' (OrderHom.mk _ <| pow_left_mono n) hs _

section Group
variable [Group G] [LinearOrder G]

@[to_additive /-- Also see `Finset.sup'_add'` that works for canonically ordered monoids. -/]
/-
**Finset.sup'_mul** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {G : Type u_4} [inst : Group G] [inst_1 : LinearOrder G] 
[MulRightMono G] (s : Finset ι) (f : ι → G)   (a : G) (hs : s.Nonempty), s.sup' 
hs f * a = s.sup' hs fun i => f i * a
参数：s : Finset ι；f : ι → G；a : G；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
lemma sup'_mul [MulRightMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    s.sup' hs f * a = s.sup' hs fun i ↦ f i * a := map_finset_sup' (OrderIso.mulRight a) hs f

set_option linter.docPrime false in
@[to_additive /-- Also see `Finset.add_sup''` that works for canonically ordered monoids. -/]
/-
**Finset.mul_sup'** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι -> G) (a : G) (hs) : a * s.
sup' hs f = s.sup' hs fun i => a * f i
参数：s : Finset ι；f : ι -> G；a : G；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `LatticeHomClass.toSupHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type
 u_8} {inst : Lattice α} {inst_1 : Lattice β} {inst_2 : FunLike F α β}   [self :
 LatticeHomClass F …
· 使用定理 `OrderHomClass.toLatticeHomClass`：∀ {F : Type u_1} (α : Type u_2) (β : Ty
pe u_3) [inst : FunLike F α β] [inst_1 : LinearOrder α] [inst_2 : Lattice β]   [
OrderHomClass F α β],…
· 使用定理 `RelIso.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r ≃r s) r s
-/
lemma mul_sup' [MulLeftMono G] (s : Finset ι) (f : ι → G) (a : G) (hs) :
    a * s.sup' hs f = s.sup' hs fun i ↦ a * f i := map_finset_sup' (OrderIso.mulLeft a) hs f

end Group

section CanonicallyLinearOrderedAddCommMonoid
variable [AddCommMonoid M] [LinearOrder M] [CanonicallyOrderedAdd M]
  [Sub M] [AddLeftReflectLE M] [OrderedSub M] {s : Finset ι} {t : Finset κ}

/-- Also see `Finset.sup'_add` that works for ordered groups. -/
/-
**Finset.sup'_add'** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : LinearO
rder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftReflectLE M] [Order
edSub M] (s : Finset ι) (f : ι → M) (a : M) (hs : s.Nonempty),   s.sup' hs f + a
 = s.sup' hs fun i => f i + a
参数：s : Finset ι；f : ι → M；a : M；hs : s.Nonempty。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `add_le_of_le_tsub_right_of_le`：add_le_of_le_tsub_right_of_le (h : b <= c
) (h2 : a <= c - b) : a + b <= c
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `CanonicallyOrderedAdd.toAddLeftMono`：∀ {α : Type u} [inst : AddSemigroup
 α] [inst_1 : LE α] [CanonicallyOrderedAdd α], AddLeftMono α
· 使用定理 `Finset.le_sup'_of_le`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilattic
eSup α] {s : Finset β} (f : β → α) {a : α} {b : β} (hb : b ∈ s),   a ≤ f b → a ≤
 s.sup' ⋯ …
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `le_add_self`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [CanonicallyO
rderedAdd α] {a b : α}, a ≤ b + a
· 使用定理 `Finset.sup'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α
] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   (∀ b ∈ s, f b ≤ a) → s.
sup'…
· 使用定理 `le_tsub_of_add_le_right`：le_tsub_of_add_le_right (h : a + b <= c) : a <=
 c - b
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…

--- 原说明 ---
Also see `Finset.sup'_add` that works for ordered groups.
-/
lemma sup'_add' (s : Finset ι) (f : ι → M) (a : M) (hs : s.Nonempty) :
    s.sup' hs f + a = s.sup' hs fun i ↦ f i + a := by
  apply le_antisymm
  · apply add_le_of_le_tsub_right_of_le
    · exact Finset.le_sup'_of_le _ hs.choose_spec le_add_self
    · exact Finset.sup'_le _ _ fun i hi ↦ le_tsub_of_add_le_right (Finset.le_sup' (f · + a) hi)
  · exact Finset.sup'_le _ _ fun i hi ↦ by grw [← Finset.le_sup' _ hi]

/-- Also see `Finset.add_sup'` that works for ordered groups. -/
/-
**Finset.add_sup''** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：add_sup'' (hs : s.Nonempty) (f : ι -> M) (a : M) : a + s.sup' hs f = s.sup
' hs fun i => a + f i
参数：hs : s.Nonempty；f : ι -> M；a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sup'_add'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid 
M] [inst_1 : LinearOrder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLef
tRefle…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Also see `Finset.add_sup'` that works for ordered groups.
-/
lemma add_sup'' (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup' hs f = s.sup' hs fun i ↦ a + f i := by simp_rw [add_comm a, Finset.sup'_add']

variable [OrderBot M]
/-
**Finset.sup_add** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : LinearO
rder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftReflectLE M] [Order
edSub M] {s : Finset ι} [inst_6 : OrderBot M],   s.Nonempty → ∀ (f : ι → M) (a :
 M), s.sup f + a = s.sup fun i => f i + a
参数：f : ι → M；a : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Finset.sup'_add'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid 
M] [inst_1 : LinearOrder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLef
tRefle…
-/
protected lemma sup_add (hs : s.Nonempty) (f : ι → M) (a : M) :
    s.sup f + a = s.sup fun i ↦ f i + a := by
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, sup'_add']
/-
**Finset.add_sup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M] [inst_1 : LinearO
rder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftReflectLE M] [Order
edSub M] {s : Finset ι} [inst_6 : OrderBot M],   s.Nonempty → ∀ (f : ι → M) (a :
 M), a + s.sup f = s.sup fun i => a + f i
参数：f : ι → M；a : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用引理 `Finset.add_sup''`：add_sup'' (hs : s.Nonempty) (f : ι -> M) (a : M) : a +
 s.sup' hs f = s.sup' hs fun i => a + f i
-/
protected lemma add_sup (hs : s.Nonempty) (f : ι → M) (a : M) :
    a + s.sup f = s.sup fun i ↦ a + f i := by
  rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs, add_sup'']
/-
**Finset.sup_add_sup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι -> M) (g : κ -> M) 
: s.sup f + t.sup g = (s ×ˢ t).sup fun ij => f ij.1 + g ij.2
参数：hs : s.Nonempty；ht : t.Nonempty；f : ι -> M；g : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_add`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 [inst_1 : LinearOrder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftR
efle…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.add_sup`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 [inst_1 : LinearOrder M] [CanonicallyOrderedAdd M]   [inst_3 : Sub M] [AddLeftR
efle…
· 使用定理 `Finset.sup_product_left`：sup_product_left (s : Finset β) (t : Finset γ) 
(f : β × γ -> α) : (s ×ˢ t).sup f = s.sup fun i => t.sup fun i' => f ⟨i, i'⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma sup_add_sup (hs : s.Nonempty) (ht : t.Nonempty) (f : ι → M) (g : κ → M) :
    s.sup f + t.sup g = (s ×ˢ t).sup fun ij ↦ f ij.1 + g ij.2 := by
  simp only [Finset.sup_add hs, Finset.add_sup ht, Finset.sup_product_left]

end CanonicallyLinearOrderedAddCommMonoid
end Finset

