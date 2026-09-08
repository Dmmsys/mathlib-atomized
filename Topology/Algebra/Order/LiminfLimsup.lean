/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Group.DenselyOrdered
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Order.LiminfLimsup

/-!
# Lemmas about liminf and limsup in an order topology.

## Main declarations

* `BoundedLENhdsClass`: Typeclass stating that neighborhoods are eventually bounded above.
* `BoundedGENhdsClass`: Typeclass stating that neighborhoods are eventually bounded below.

## Implementation notes

The same lemmas are true in `ℝ`, `ℝ × ℝ`, `ι → ℝ`, `EuclideanSpace ι ℝ`. To avoid code
duplication, we provide an ad hoc axiomatisation of the properties we need.
-/

public section

open Filter TopologicalSpace
open scoped Topology

universe u v

variable {ι α β R S : Type*} {X : ι → Type*}

section LiminfLimsupAdd

variable [AddCommGroup α] [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
  [AddLeftMono α]
  {f : Filter ι} [f.NeBot] {u v : ι → α}

/-
**le_limsup_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_limsup_add (h₁ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isCoboundedUnder_le_add`：isCoboundedUnder_le_add (hu : f.IsBounde
dUnder (fun x1 x2 => x2 <= x1) u) (hv : f.IsCoboundedUnder (· <= ·) v) : f.IsCob
oundedUnder (· <= ·)…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Filter.isBoundedUnder_le_add`：isBoundedUnder_le_add [Add R] [AddLeftMono
 R] [AddRightMono R] {u v : α -> R} (u_bdd_le : f.IsBoundedUnder (· <= ·) u) (v_
bdd_le : f.IsBound…
· 使用定理 `add_le_of_forall_lt`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [AddLeftMono α] [DenselyOrdered α] {a b c : α},   (∀ a' < a, ∀ b'
 < b, a' …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma le_limsup_add (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₂ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    (limsup u f) + liminf v f ≤ limsup (u + v) f := by
  have h := isCoboundedUnder_le_add h₄ h₂ -- These `have` tactic improve performance.
  have h' := isBoundedUnder_le_add h₃ h₁
  rw [add_comm] at h h'
  refine add_le_of_forall_lt fun a a_u b b_v ↦ (le_limsup_iff h h').2 fun c c_ab ↦ ?_
  refine ((frequently_lt_of_lt_limsup h₂ a_u).and_eventually
    (eventually_lt_of_lt_liminf b_v h₄)).mono fun _ ab_x ↦ ?_
  exact c_ab.trans (add_lt_add ab_x.1 ab_x.2)
/-
**limsup_add_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_add_le (h₁ : IsBoundedUnder (fun x1 x2 => x1 >= x2) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isCoboundedUnder_le_add`：isCoboundedUnder_le_add (hu : f.IsBounde
dUnder (fun x1 x2 => x2 <= x1) u) (hv : f.IsCoboundedUnder (· <= ·) v) : f.IsCob
oundedUnder (· <= ·)…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `Filter.isBoundedUnder_le_add`：isBoundedUnder_le_add [Add R] [AddLeftMono
 R] [AddRightMono R] {u v : α -> R} (u_bdd_le : f.IsBoundedUnder (· <= ·) u) (v_
bdd_le : f.IsBound…
· 使用定理 `le_add_of_forall_lt`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [AddLeftMono α] [DenselyOrdered α] {a b c : α},   (∀ a' > a, ∀ b'
 > b, c ≤…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma limsup_add_le (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault)
    (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v := by isBoundedDefault) :
    limsup (u + v) f ≤ (limsup u f) + limsup v f := by
  have h := isCoboundedUnder_le_add h₁ h₃
  have h' := isBoundedUnder_le_add h₂ h₄
  refine le_add_of_forall_lt fun a a_u b b_v ↦ ?_
  rw [limsup_le_iff h h']
  intro c c_ab
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v] with x a_x b_x
  exact (add_lt_add a_x b_x).trans c_ab
/-
**le_liminf_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_liminf_add (h₁ : IsBoundedUnder (fun x1 x2 => x1 >= x2) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.isCoboundedUnder_ge_add`：∀ {α : Type u_5} {R : Type u_6} [inst : 
LinearOrder R] [inst_1 : Add R] {f : Filter α} [f.NeBot] [AddLeftMono R]   [AddR
ightMono R] {u v : α…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.isBoundedUnder_ge_add`：∀ {α : Type u_5} {f : Filter α} {R : Type 
u_6} [inst : Preorder R] [inst_1 : Add R] [AddLeftMono R] [AddRightMono R]   {u 
v : α → R},   Filt…
· 使用定理 `add_le_of_forall_lt`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [AddLeftMono α] [DenselyOrdered α] {a b c : α},   (∀ a' < a, ∀ b'
 < b, a' …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
-/
lemma le_liminf_add (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    (liminf u f) + liminf v f ≤ liminf (u + v) f := by
  have h := isCoboundedUnder_ge_add h₂ h₄
  have h' := isBoundedUnder_ge_add h₁ h₃
  refine add_le_of_forall_lt fun a a_u b b_v ↦ ?_
  rw [le_liminf_iff h h']
  intro c c_ab
  filter_upwards [eventually_lt_of_lt_liminf a_u, eventually_lt_of_lt_liminf b_v] with x a_x b_x
  exact c_ab.trans (add_lt_add a_x b_x)
/-
**liminf_add_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_add_le (h₁ : IsBoundedUnder (fun x1 x2 => x1 >= x2) f u
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.isCoboundedUnder_ge_add`：∀ {α : Type u_5} {R : Type u_6} [inst : 
LinearOrder R] [inst_1 : Add R] {f : Filter α} [f.NeBot] [AddLeftMono R]   [AddR
ightMono R] {u v : α…
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Filter.isBoundedUnder_ge_add`：∀ {α : Type u_5} {f : Filter α} {R : Type 
u_6} [inst : Preorder R] [inst_1 : Add R] [AddLeftMono R] [AddRightMono R]   {u 
v : α → R},   Filt…
· 使用定理 `le_add_of_forall_lt`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : 
LinearOrder α] [AddLeftMono α] [DenselyOrdered α] {a b c : α},   (∀ a' > a, ∀ b'
 > b, c ≤…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.liminf_le_iff`：liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma liminf_add_le (h₁ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f u := by isBoundedDefault)
    (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u := by isBoundedDefault)
    (h₃ : IsBoundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault)
    (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v := by isBoundedDefault) :
    liminf (u + v) f ≤ (limsup u f) + liminf v f := by
  have h := isCoboundedUnder_ge_add h₂ h₄
  have h' := isBoundedUnder_ge_add h₁ h₃
  refine le_add_of_forall_lt fun a a_u b b_v ↦ (liminf_le_iff h h').2 fun _ c_ab ↦ ?_
  refine ((frequently_lt_of_liminf_lt h₄ b_v).and_eventually
    (eventually_lt_of_limsup_lt a_u h₂)).mono fun _ ab_x ↦ ?_
  exact (add_lt_add ab_x.2 ab_x.1).trans c_ab

end LiminfLimsupAdd

section LiminfLimsupMul

open Filter Real

variable {f : Filter ι} {u v : ι → ℝ}

/-
**le_limsup_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_limsup_mul (h₁ : existsᶠ x in f, 0 <= u x) (h₂ : IsBoundedUnder (fun x1
 x2 => x1 <= x2) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 => x1 <=
 x2) f v) : (limsup u f) * liminf v f <= limsup (u * v) f
参数：h₁ : existsᶠ x in f, 0 <= u x；h₂ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f u
；h₃ : 0 <=ᶠ[f] v；h₄ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Filter.isBoundedUnder_le_mul_of_nonneg`：isBoundedUnder_le_mul_of_nonneg 
[Preorder α] [Mul α] [Zero α] [PosMulMono α] [MulPosMono α] {f : Filter ι} {u v 
: ι -> α} (h₁ : existsᶠ x in…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用引理 `mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg {a b c : α}
 (ha : 0 <= a) (hc : 0 <= c) (h : forall a' >= 0, a' < a -> forall b' >= 0, b' <
 b -> a' * b' <= c)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_limsup_iff`：le_limsup_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.frequently_lt_of_lt_limsup`：frequently_lt_of_lt_limsup {b : β} (h
u : f.IsCoboundedUnder (· <= ·) u
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.isBoundedUnder_of_eventually_ge`：∀ {α : Type u_1} {β : Type u_2} 
[inst : Preorder α] {f : Filter β} {u : β → α} {a : α},   (∀ᶠ (x : β) in f, a ≤ 
u x) → Filter.IsBoundedUnder…
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma le_limsup_mul (h₁ : ∃ᶠ x in f, 0 ≤ u x) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    (limsup u f) * liminf v f ≤ limsup (u * v) f := by
  have h := IsCoboundedUnder.of_frequently_ge (a := 0)
    <| (h₁.and_eventually h₃).mono fun x ⟨ux_0, vx_0⟩ ↦ mul_nonneg ux_0 vx_0
  have h' := isBoundedUnder_le_mul_of_nonneg h₁ h₂ h₃ h₄
  have u0 : 0 ≤ limsup u f := le_limsup_of_frequently_le h₁ h₂
  have uv : 0 ≤ limsup (u * v) f :=
    le_limsup_of_frequently_le ((h₁.and_eventually h₃).mono fun _ ⟨hu, hv⟩ ↦ mul_nonneg hu hv) h'
  refine mul_le_of_forall_lt_of_nonneg u0 uv fun a a0 au b b0 bv ↦ ?_
  refine (le_limsup_iff h h').2 fun c c_ab ↦ ?_
  replace h₁ := IsCoboundedUnder.of_frequently_ge h₁ -- Pre-compute it to gain 4 s.
  have h₅ := frequently_lt_of_lt_limsup h₁ au
  have h₆ := eventually_lt_of_lt_liminf bv (isBoundedUnder_of_eventually_ge h₃)
  apply (h₅.and_eventually (h₆.and h₃)).mono
  exact fun x ⟨xa, ⟨xb, _⟩⟩ ↦ c_ab.trans_le <| mul_le_mul xa.le xb.le b0 (a0.trans xa.le)
/-
**limsup_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_mul_le (h₁ : existsᶠ x in f, 0 <= u x) (h₂ : IsBoundedUnder (fun x1
 x2 => x1 <= x2) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 => x1 <=
 x2) f v) : limsup (u * v) f <= (limsup u f) * limsup v f
参数：h₁ : existsᶠ x in f, 0 <= u x；h₂ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f u
；h₃ : 0 <=ᶠ[f] v；h₄ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsCoboundedUnder.of_frequently_ge`：∀ {α : Type u_1} {ι : Type u_4
} [inst : LinearOrder α] {f : Filter ι} {u : ι → α} {a : α},   (∃ᶠ (x : ι) in f,
 a ≤ u x) → Filter.IsCobounded…
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用引理 `Filter.isBoundedUnder_le_mul_of_nonneg`：isBoundedUnder_le_mul_of_nonneg 
[Preorder α] [Mul α] [Zero α] [PosMulMono α] [MulPosMono α] {f : Filter ι} {u v 
: ι -> α} (h₁ : existsᶠ x in…
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `le_mul_of_forall_lt₀`：le_mul_of_forall_lt₀ {a b c : α} (h : forall a' > 
a, forall b' > b, c <= a' * b') : c <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.limsup_le_iff`：limsup_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
<= ·) u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Filter.le_limsup_of_frequently_le`：le_limsup_of_frequently_le (hu : exis
tsᶠ i in f, a <= u i) (hu_le : f.IsBoundedUnder (· <= ·) u
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
-/
lemma limsup_mul_le (h₁ : ∃ᶠ x in f, 0 ≤ u x) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f v) :
    limsup (u * v) f ≤ (limsup u f) * limsup v f := by
  have h := IsCoboundedUnder.of_frequently_ge (a := 0)
    <| (h₁.and_eventually h₃).mono fun x ⟨ux_0, vx_0⟩ ↦ mul_nonneg ux_0 vx_0
  have h' := isBoundedUnder_le_mul_of_nonneg h₁ h₂ h₃ h₄
  refine le_mul_of_forall_lt₀ fun a a_u b b_v ↦ (limsup_le_iff h h').2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_limsup_lt a_u, eventually_lt_of_limsup_lt b_v, h₃]
    with x x_a x_b v_0
  apply lt_of_le_of_lt _ c_ab
  rcases lt_or_ge (u x) 0 with u_0 | u_0
  · apply (mul_nonpos_of_nonpos_of_nonneg u_0.le v_0).trans
    exact mul_nonneg ((le_limsup_of_frequently_le h₁ h₂).trans a_u.le) (v_0.trans x_b.le)
  · exact mul_le_mul x_a.le x_b.le v_0 (u_0.trans x_a.le)
/-
**le_liminf_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：le_liminf_mul [f.NeBot] (h₁ : 0 <=ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 
=> x1 <= x2) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 => x1 >= x
2) f v) : (liminf u f) * liminf v f <= liminf (u * v) f
参数：h₁ : 0 <=ᶠ[f] u；h₂ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f u；h₃ : 0 <=ᶠ[f]
 v；h₄ : IsCoboundedUnder (fun x1 x2 => x1 >= x2) f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isCoboundedUnder_ge_mul_of_nonneg`：isCoboundedUnder_ge_mul_of_non
neg [LinearOrder α] [Mul α] [Zero α] [PosMulMono α] [MulPosMono α] {f : Filter ι
} [f.NeBot] {u v : ι -> α} (h₁…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Filter.isBoundedUnder_of_eventually_ge`：∀ {α : Type u_1} {β : Type u_2} 
[inst : Preorder α] {f : Filter β} {u : β → α} {a : α},   (∀ᶠ (x : β) in f, a ≤ 
u x) → Filter.IsBoundedUnder…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用引理 `mul_le_of_forall_lt_of_nonneg`：mul_le_of_forall_lt_of_nonneg {a b c : α}
 (ha : 0 <= a) (hc : 0 <= c) (h : forall a' >= 0, a' < a -> forall b' >= 0, b' <
 b -> a' * b' <= c)…
· 使用定理 `Filter.le_liminf_of_le`：le_liminf_of_le {f : Filter β} {u : β -> α} {a} 
(hf : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.IsBoundedUnder.isCoboundedUnder_ge`：∀ {α : Type u_1} {γ : Type u_
3} {u : γ → α} {l : Filter γ} [inst : Preorder α] [l.NeBot],   Filter.IsBoundedU
nder (fun x1 x2 => x1 ≤ x2) l u…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.le_liminf_iff`：le_liminf_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_lt_of_lt_liminf`：eventually_lt_of_lt_liminf {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : b < liminf u
 f) (hu : f.IsBoundedUn…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma le_liminf_mul [f.NeBot] (h₁ : 0 ≤ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    (liminf u f) * liminf v f ≤ liminf (u * v) f := by
  have h := isCoboundedUnder_ge_mul_of_nonneg h₁ h₂ h₃ h₄
  have h' := isBoundedUnder_of_eventually_ge (a := 0)
    <| (h₁.and h₃).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0
  apply mul_le_of_forall_lt_of_nonneg (le_liminf_of_le h₂.isCoboundedUnder_ge h₁)
    (le_liminf_of_le h ((h₁.and h₃).mono fun x ⟨u0, v0⟩ ↦ mul_nonneg u0 v0))
  intro a a0 au b b0 bv
  refine (le_liminf_iff h h').2 fun c c_ab ↦ ?_
  filter_upwards [eventually_lt_of_lt_liminf au (isBoundedUnder_of_eventually_ge h₁),
    eventually_lt_of_lt_liminf bv (isBoundedUnder_of_eventually_ge h₃)] with x xa xb
  exact c_ab.trans_le (mul_le_mul xa.le xb.le b0 (a0.trans xa.le))
/-
**liminf_mul_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_mul_le [f.NeBot] (h₁ : 0 <=ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 
=> x1 <= x2) f u) (h₃ : 0 <=ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 => x1 >= x
2) f v) : liminf (u * v) f <= (limsup u f) * liminf v f
参数：h₁ : 0 <=ᶠ[f] u；h₂ : IsBoundedUnder (fun x1 x2 => x1 <= x2) f u；h₃ : 0 <=ᶠ[f]
 v；h₄ : IsCoboundedUnder (fun x1 x2 => x1 >= x2) f v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.isCoboundedUnder_ge_mul_of_nonneg`：isCoboundedUnder_ge_mul_of_non
neg [LinearOrder α] [Mul α] [Zero α] [PosMulMono α] [MulPosMono α] {f : Filter ι
} [f.NeBot] {u v : ι -> α} (h₁…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Filter.isBoundedUnder_of_eventually_ge`：∀ {α : Type u_1} {β : Type u_2} 
[inst : Preorder α] {f : Filter β} {u : β → α} {a : α},   (∀ᶠ (x : β) in f, a ≤ 
u x) → Filter.IsBoundedUnder…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用引理 `le_mul_of_forall_lt₀`：le_mul_of_forall_lt₀ {a b c : α} (h : forall a' > 
a, forall b' > b, c <= a' * b') : c <= a * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.liminf_le_iff`：liminf_le_iff {x : β} (h₁ : f.IsCoboundedUnder (· 
>= ·) u
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_lt_of_liminf_lt`：frequently_lt_of_liminf_lt {b : β} (h
u : f.IsCoboundedUnder (· >= ·) u
· 使用定理 `Filter.eventually_lt_of_limsup_lt`：eventually_lt_of_limsup_lt {f : Filte
r α} [ConditionallyCompleteLinearOrder β] {u : α -> β} {b : β} (h : limsup u f <
 b) (hu : f.IsBoundedUn…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
lemma liminf_mul_le [f.NeBot] (h₁ : 0 ≤ᶠ[f] u) (h₂ : IsBoundedUnder (fun x1 x2 ↦ x1 ≤ x2) f u)
    (h₃ : 0 ≤ᶠ[f] v) (h₄ : IsCoboundedUnder (fun x1 x2 ↦ x1 ≥ x2) f v) :
    liminf (u * v) f ≤ (limsup u f) * liminf v f := by
  have h := isCoboundedUnder_ge_mul_of_nonneg h₁ h₂ h₃ h₄
  have h' := isBoundedUnder_of_eventually_ge (a := 0)
    <| (h₁.and h₃).mono fun x ⟨u_0, v_0⟩ ↦ mul_nonneg u_0 v_0
  refine le_mul_of_forall_lt₀ fun a a_u b b_v ↦ (liminf_le_iff h h').2 fun c c_ab ↦ ?_
  refine ((frequently_lt_of_liminf_lt h₄ b_v).and_eventually ((eventually_lt_of_limsup_lt a_u).and
    (h₁.and h₃))).mono fun x ⟨x_v, x_u, u_0, v_0⟩ ↦ ?_
  exact (mul_le_mul x_u.le x_v.le v_0 (u_0.trans x_u.le)).trans_lt c_ab

end LiminfLimsupMul
section LiminfLimsupAddSub
variable [ConditionallyCompleteLinearOrder R] [TopologicalSpace R] [OrderTopology R]

/-- `liminf (c + xᵢ) = c + liminf xᵢ`. -/
/-
**limsup_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R] [AddLe
ftMono R] (f : ι -> R) (c : R) (bdd_above : F.IsBoundedUnder (· <= ·) f) (cobdd 
: F.IsCoboundedUnder (· <= ·) f) : Filter.limsup (fun i => c + f i) F = c + Filt
er.limsup f F
参数：F : Filter ι；f : ι -> R；c : R；bdd_above : F.IsBoundedUnder (· <= ·) f；cobdd :
 F.IsCoboundedUnder (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsSup_of_continuousAt`：Monotone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => m + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
`liminf (c + xᵢ) = c + liminf xᵢ`.
-/
lemma limsup_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ c + f i) F = c + Filter.limsup f F :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_const_add c).continuousAt bdd_above cobdd).symm

/-- `limsup (xᵢ + c) = (limsup xᵢ) + c`. -/
/-
**limsup_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R] [AddRi
ghtMono R] (f : ι -> R) (c : R) (bdd_above : F.IsBoundedUnder (· <= ·) f) (cobdd
 : F.IsCoboundedUnder (· <= ·) f) : Filter.limsup (fun i => f i + c) F = Filter.
limsup f F + c
参数：F : Filter ι；f : ι -> R；c : R；bdd_above : F.IsBoundedUnder (· <= ·) f；cobdd :
 F.IsCoboundedUnder (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsSup_of_continuousAt`：Monotone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => x + m
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
`limsup (xᵢ + c) = (limsup xᵢ) + c`.
-/
lemma limsup_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddRightMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ f i + c) F = Filter.limsup f F + c :=
  (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_const c).continuousAt bdd_above cobdd).symm

/-- `liminf (c + xᵢ) = c + liminf xᵢ`. -/
/-
**liminf_const_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R] [AddLe
ftMono R] (f : ι -> R) (c : R) (cobdd : F.IsCoboundedUnder (· >= ·) f) (bdd_belo
w : F.IsBoundedUnder (· >= ·) f) : Filter.liminf (fun i => c + f i) F = c + Filt
er.liminf f F
参数：F : Filter ι；f : ι -> R；c : R；cobdd : F.IsCoboundedUnder (· >= ·) f；bdd_below
 : F.IsBoundedUnder (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsInf_of_continuousAt`：Monotone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `add_le_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [AddLe
ftMono α] {b c : α}, b ≤ c → ∀ (a : α), a + b ≤ a + c
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => m + x
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
`liminf (c + xᵢ) = c + liminf xᵢ`.
-/
lemma liminf_const_add (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ c + f i) F = c + Filter.liminf f F :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c + x)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_const_add c).continuousAt cobdd bdd_below).symm

/-- `liminf (xᵢ + c) = (liminf xᵢ) + c`. -/
/-
**liminf_add_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R] [AddRi
ghtMono R] (f : ι -> R) (c : R) (cobdd : F.IsCoboundedUnder (· >= ·) f) (bdd_bel
ow : F.IsBoundedUnder (· >= ·) f) : Filter.liminf (fun i => f i + c) F = Filter.
liminf f F + c
参数：F : Filter ι；f : ι -> R；c : R；cobdd : F.IsCoboundedUnder (· >= ·) f；bdd_below
 : F.IsBoundedUnder (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsInf_of_continuousAt`：Monotone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `add_le_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LE α] [i : Ad
dRightMono α] {b c : α}, b ≤ c → ∀ (a : α), b + a ≤ c + a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] (m : M),   Continuous fun x => x + m
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M

--- 原说明 ---
`liminf (xᵢ + c) = (liminf xᵢ) + c`.
-/
lemma liminf_add_const (F : Filter ι) [NeBot F] [Add R] [ContinuousAdd R]
    [AddRightMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i + c) F = Filter.liminf f F + c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x + c)
    (fun _ _ h ↦ by dsimp; gcongr) (continuous_add_const c).continuousAt cobdd bdd_below).symm

/-- `limsup (c - xᵢ) = c - liminf xᵢ`. -/
/-
**limsup_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_const_sub (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSu
b R] [OrderedSub R] [AddLeftMono R] (f : ι -> R) (c : R) (cobdd : F.IsCoboundedU
nder (· >= ·) f) (bdd_below : F.IsBoundedUnder (· >= ·) f) : Filter.limsup (fun 
i => c - f i) F = c - Filter.liminf f F
参数：F : Filter ι；f : ι -> R；c : R；cobdd : F.IsCoboundedUnder (· >= ·) f；bdd_below
 : F.IsBoundedUnder (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `tsub_le_iff_tsub_le`：tsub_le_iff_tsub_le : a - b <= c ↔ a - c <= b
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `mem_upperBounds`：mem_upperBounds : a in upperBounds s ↔ forall x in s, x
 <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_limsInf_of_continuousAt`：Antitone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_sub_left`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 
: Sub G] [ContinuousSub G] (a : G), Continuous fun x => a - x

--- 原说明 ---
`limsup (c - xᵢ) = c - liminf xᵢ`.
-/
lemma limsup_const_sub (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSub R] [OrderedSub R]
    [AddLeftMono R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.limsup (fun i ↦ c - f i) F = c - Filter.liminf f F := by
  rcases F.eq_or_neBot with rfl | _
  · simp only [liminf, limsInf, limsup, limsSup, map_bot, eventually_bot, Set.ofPred_true]
    simp only [IsCoboundedUnder, IsCobounded, map_bot, eventually_bot, true_implies] at cobdd
    rcases cobdd with ⟨x, hx⟩
    refine (csInf_le ?_ (Set.mem_univ _)).antisymm
      (tsub_le_iff_tsub_le.1 (le_csSup ?_ (Set.mem_univ _)))
    · refine ⟨x - x, mem_lowerBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, true_implies]
      exact tsub_le_iff_tsub_le.1 (hx (x - y))
    · refine ⟨x, mem_upperBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, hx y, implies_true]
  · exact (Antitone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c).continuousAt cobdd bdd_below).symm

/-- `limsup (xᵢ - c) = (limsup xᵢ) - c`. -/
/-
**limsup_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：limsup_sub_const (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSu
b R] [OrderedSub R] (f : ι -> R) (c : R) (bdd_above : F.IsBoundedUnder (· <= ·) 
f) (cobdd : F.IsCoboundedUnder (· <= ·) f) : Filter.limsup (fun i => f i - c) F 
= Filter.limsup f F - c
参数：F : Filter ι；f : ι -> R；c : R；bdd_above : F.IsBoundedUnder (· <= ·) f；cobdd :
 F.IsCoboundedUnder (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eq_or_neBot`：eq_or_neBot (f : Filter α) : f = ⊥ ∨ NeBot f
· 使用定理 `csInf_le`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, BddBelow s → a ∈ s → sInf s ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Filter.map_bot`：∀ {α : Type u_1} {β : Type u_2} {m : α → β}, Filter.map 
m ⊥ = ⊥
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_lowerBounds`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α
}, a ∈ lowerBounds s ↔ ∀ x ∈ s, a ≤ x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `tsub_le_iff_right`：tsub_le_iff_right [LE α] [Add α] [Sub α] [OrderedSub 
α] {a b c : α} : a - b <= c ↔ a <= c + b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsSup_of_continuousAt`：Monotone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_sub_right`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1
 : Sub G] [ContinuousSub G] (a : G), Continuous fun x => x - a

--- 原说明 ---
`limsup (xᵢ - c) = (limsup xᵢ) - c`.
-/
lemma limsup_sub_const (F : Filter ι) [AddCommSemigroup R] [Sub R] [ContinuousSub R] [OrderedSub R]
    (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.limsup (fun i ↦ f i - c) F = Filter.limsup f F - c := by
  rcases F.eq_or_neBot with rfl | _
  · have {a : R} : sInf Set.univ ≤ a := by
      apply csInf_le _ (Set.mem_univ a)
      simp only [IsCoboundedUnder, IsCobounded, map_bot, eventually_bot, true_implies] at cobdd
      rcases cobdd with ⟨x, hx⟩
      refine ⟨x, mem_lowerBounds.2 fun y ↦ ?_⟩
      simp only [Set.mem_univ, hx y, implies_true]
    simp only [limsup, limsSup, map_bot, eventually_bot, Set.ofPred_true]
    exact this.antisymm (tsub_le_iff_right.2 this)
  · apply (Monotone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c) _ _).symm
    · exact fun _ _ h ↦ tsub_le_tsub_right h c
    · exact (continuous_sub_right c).continuousAt

/-- `liminf (c - xᵢ) = c - limsup xᵢ`. -/
/-
**liminf_const_sub** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_const_sub (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [Co
ntinuousSub R] [OrderedSub R] [AddLeftMono R] (f : ι -> R) (c : R) (bdd_above : 
F.IsBoundedUnder (· <= ·) f) (cobdd : F.IsCoboundedUnder (· <= ·) f) : Filter.li
minf (fun i => c - f i) F = c - Filter.limsup f F
参数：F : Filter ι；f : ι -> R；c : R；bdd_above : F.IsBoundedUnder (· <= ·) f；cobdd :
 F.IsCoboundedUnder (· <= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Antitone.map_limsSup_of_continuousAt`：Antitone.map_limsSup_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_decr : Antitone f) (f_cont : Continu
ousAt f F.limsSup) (bdd_ab…
· 使用定理 `tsub_le_tsub_left`：tsub_le_tsub_left (h : a <= b) (c : α) : c - b <= c -
 a
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_sub_left`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 
: Sub G] [ContinuousSub G] (a : G), Continuous fun x => a - x

--- 原说明 ---
`liminf (c - xᵢ) = c - limsup xᵢ`.
-/
lemma liminf_const_sub (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] [AddLeftMono R] (f : ι → R) (c : R)
    (bdd_above : F.IsBoundedUnder (· ≤ ·) f) (cobdd : F.IsCoboundedUnder (· ≤ ·) f) :
    Filter.liminf (fun i ↦ c - f i) F = c - Filter.limsup f F :=
  (Antitone.map_limsSup_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ c - x)
    (fun _ _ h ↦ tsub_le_tsub_left h c) (continuous_sub_left c).continuousAt bdd_above cobdd).symm

/-- `liminf (xᵢ - c) = (liminf xᵢ) - c`. -/
/-
**liminf_sub_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：liminf_sub_const (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [Co
ntinuousSub R] [OrderedSub R] (f : ι -> R) (c : R) (cobdd : F.IsCoboundedUnder (
· >= ·) f) (bdd_below : F.IsBoundedUnder (· >= ·) f) : Filter.liminf (fun i => f
 i - c) F = Filter.liminf f F - c
参数：F : Filter ι；f : ι -> R；c : R；cobdd : F.IsCoboundedUnder (· >= ·) f；bdd_below
 : F.IsBoundedUnder (· >= ·) f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monotone.map_limsInf_of_continuousAt`：Monotone.map_limsInf_of_continuous
At {F : Filter R} [NeBot F] {f : R -> S} (f_incr : Monotone f) (f_cont : Continu
ousAt f F.limsInf) (cobdd …
· 使用定理 `tsub_le_tsub_right`：tsub_le_tsub_right (h : a <= b) (c : α) : a - c <= b
 - c
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_sub_right`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1
 : Sub G] [ContinuousSub G] (a : G), Continuous fun x => x - a

--- 原说明 ---
`liminf (xᵢ - c) = (liminf xᵢ) - c`.
-/
lemma liminf_sub_const (F : Filter ι) [NeBot F] [AddCommSemigroup R] [Sub R] [ContinuousSub R]
    [OrderedSub R] (f : ι → R) (c : R)
    (cobdd : F.IsCoboundedUnder (· ≥ ·) f) (bdd_below : F.IsBoundedUnder (· ≥ ·) f) :
    Filter.liminf (fun i ↦ f i - c) F = Filter.liminf f F - c :=
  (Monotone.map_limsInf_of_continuousAt (F := F.map f) (f := fun (x : R) ↦ x - c)
    (fun _ _ h ↦ tsub_le_tsub_right h c) (continuous_sub_right c).continuousAt cobdd bdd_below).symm

end LiminfLimsupAddSub -- section

