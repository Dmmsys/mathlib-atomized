/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
module

public import Mathlib.Algebra.Group.Subsemigroup.Operations
public import Mathlib.Algebra.MonoidAlgebra.Support
public import Mathlib.Order.Filter.Extr

/-!
# Lemmas about the `sup` and `inf` of the support of `AddMonoidAlgebra`

## TODO
The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.

Next, the general lemmas get specialized for some yet-to-be-defined `degree`s.
-/

@[expose] public section


variable {R R' A T B ι : Type*}

namespace AddMonoidAlgebra

/-!

## sup-degree and inf-degree of an `AddMonoidAlgebra`

Let `R` be a semiring and let `A` be a `SemilatticeSup`.
For an element `f : R[A]`, this file defines
* `AddMonoidAlgebra.supDegree`: the sup-degree taking values in `WithBot A`,
* `AddMonoidAlgebra.infDegree`: the inf-degree taking values in `WithTop A`.

If the grading type `A` is a linearly ordered additive monoid, then these two notions of degree
coincide with the standard one:
* the sup-degree is the maximum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊥`, if `f = 0`;
* the inf-degree is the minimum of the exponents of the monomials that appear with non-zero
  coefficient in `f`, or `⊤`, if `f = 0`.

The main results are
* `AddMonoidAlgebra.supDegree_mul_le`:
  the sup-degree of a product is at most the sum of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_mul`:
  the inf-degree of a product is at least the sum of the inf-degrees,
* `AddMonoidAlgebra.supDegree_add_le`:
  the sup-degree of a sum is at most the sup of the sup-degrees,
* `AddMonoidAlgebra.le_infDegree_add`:
  the inf-degree of a sum is at least the inf of the inf-degrees.

### Implementation notes

The current plan is to state and prove lemmas about `Finset.sup (Finsupp.support f) D` with a
"generic" degree/weight function `D` from the grading Type `A` to a somewhat ordered Type `B`.
Next, the general lemmas get specialized twice:
* once for `supDegree` (essentially a simple application) and
* once for `infDegree` (a simple application, via `OrderDual`).

These final lemmas are the ones that likely get used the most.  The generic lemmas about
`Finset.support.sup` may not be used directly much outside of this file.
To see this in action, you can look at the triple
`(sup_support_mul_le, maxDegree_mul_le, le_minDegree_mul)`.
-/


section GeneralResultsAssumingSemilatticeSup

variable [SemilatticeSup B] [OrderBot B] [SemilatticeInf T] [OrderTop T]

section Semiring

variable [Semiring R]

section ExplicitDegrees

/-!

In this section, we use `degb` and `degt` to denote "degree functions" on `A` with values in
a type with *b*ot or *t*op respectively.
-/


variable (degb : A → B) (degt : A → T) (f g : R[A])

/-
**AddMonoidAlgebra.sup_support_coeff_add_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：sup_support_coeff_add_le : (f + g).coeff.support.sup degb <= f.coeff.suppo
rt.sup degb ⊔ g.coeff.support.sup degb
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用引理 `Finsupp.support_add`：support_add [DecidableEq ι] : (g₁ + g₂).support sub
seteq g₁.support union g₂.support
· 使用定理 `Finset.sup_union`：sup_union [DecidableEq β] : (s₁ union s₂).sup f = s₁.s
up f ⊔ s₂.sup f
-/
theorem sup_support_coeff_add_le :
    (f + g).coeff.support.sup degb ≤ f.coeff.support.sup degb ⊔ g.coeff.support.sup degb := by
  classical
  exact (Finset.sup_mono Finsupp.support_add).trans_eq Finset.sup_union

@[deprecated (since := "2026-06-18")] alias sup_support_add_le := sup_support_coeff_add_le
/-
**AddMonoidAlgebra.le_inf_support_coeff_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：le_inf_support_coeff_add : f.coeff.support.inf degt ⊓ g.coeff.support.inf 
degt <= (f + g).coeff.support.inf degt
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_add_le`：sup_support_coeff_add_le : (f
 + g).coeff.support.sup degb <= f.coeff.support.sup degb ⊔ g.coeff.support.sup d
egb
-/
theorem le_inf_support_coeff_add :
    f.coeff.support.inf degt ⊓ g.coeff.support.inf degt ≤ (f + g).coeff.support.inf degt :=
  sup_support_coeff_add_le (fun a : A => OrderDual.toDual (degt a)) f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_add := le_inf_support_coeff_add

end ExplicitDegrees

section AddOnly

variable [Add A] [Add B] [Add T] [AddLeftMono B] [AddRightMono B]
  [AddLeftMono T] [AddRightMono T]

/-
**AddMonoidAlgebra.sup_support_coeff_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：sup_support_coeff_mul_le {degb : A -> B} (degbm : forall a b, degb (a + b)
 <= degb a + degb b) (f g : R[A]) : (f * g).coeff.support.sup degb <= f.coeff.su
pport.sup degb + g.coeff.support.sup degb
参数：degbm : forall a b, degb (a + b) <= degb a + degb b；f g : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `AddMonoidAlgebra.support_coeff_mul_subset`：∀ {k : Type u₁} {G : Type u₂}
 [inst : Semiring k] [inst_1 : Add G] [inst_2 : DecidableEq G]   (x y : AddMonoi
dAlgebra k G), (x * y).coeff.su…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_add_le`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 : Add
 α] {β : Type u_5} [inst_2 : SemilatticeSup β]   [inst_3 : OrderBot β] {s t : Fi
nset α}…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
-/
theorem sup_support_coeff_mul_le {degb : A → B} (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (f g : R[A]) :
    (f * g).coeff.support.sup degb ≤ f.coeff.support.sup degb + g.coeff.support.sup degb := by
  classical
  grw [support_coeff_mul_subset, Finset.sup_add_le]
  rintro _fd fds _gd gds
  grw [degbm, ← Finset.le_sup fds, ← Finset.le_sup gds]

@[deprecated (since := "2026-06-18")] alias sup_support_mul_le := sup_support_coeff_mul_le
/-
**AddMonoidAlgebra.le_inf_support_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：le_inf_support_coeff_mul {degt : A -> T} (degtm : forall a b, degt a + deg
t b <= degt (a + b)) (f g : R[A]) : f.coeff.support.inf degt + g.coeff.support.i
nf degt <= (f * g).coeff.support.inf degt
参数：degtm : forall a b, degt a + degt b <= degt (a + b)；f g : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_mul_le`：sup_support_coeff_mul_le {deg
b : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b) (f g : R[A]) :
 (f * g).coeff.support.sup degb…
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
-/
theorem le_inf_support_coeff_mul {degt : A → T} (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (f g : R[A]) :
    f.coeff.support.inf degt + g.coeff.support.inf degt ≤ (f * g).coeff.support.inf degt :=
  sup_support_coeff_mul_le (B := Tᵒᵈ) degtm f g

@[deprecated (since := "2026-06-18")] alias le_inf_support_mul := le_inf_support_coeff_mul

end AddOnly

section AddMonoids

variable [AddMonoid A] [AddMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

/-
**AddMonoidAlgebra.sup_support_list_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : SemilatticeSup B] [
inst_1 : OrderBot B] [inst_2 : Semiring R]   [inst_3 : AddMonoid A] [inst_4 : Ad
dMonoid B] [AddLeftMono B] [AddRightMono B] {degb : A → B},   degb 0 ≤ 0 →     (
∀ (a b : A), degb (a + b) ≤ degb a + degb b) →       ∀ (l : List (AddMonoidAlgeb
ra R A)),         l.prod.coeff.support.sup degb ≤ (List.map (fun f => f.coeff.su
pport.sup degb) l).sum
参数：∀ (a b : A), degb (a + b) ≤ degb a + degb b；l : List (AddMonoidAlgebra R A)；L
ist.map (fun f => f.coeff.support.sup degb) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_support_list_prod_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) :
    ∀ l : List R[A],
      l.prod.coeff.support.sup degb ≤ (l.map fun f : R[A] => f.coeff.support.sup degb).sum
  | [] => by
    rw [List.map_nil, Finset.sup_le_iff, List.prod_nil, List.sum_nil]
    exact fun a ha => by rwa [Finset.mem_singleton.mp (Finsupp.support_single_subset ha)]
  | f::fs => by
    rw [List.prod_cons, List.map_cons, List.sum_cons]
    grw [sup_support_coeff_mul_le degbm, sup_support_list_prod_le degb0 degbm]
/-
**AddMonoidAlgebra.le_inf_support_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：le_inf_support_list_prod (degt0 : 0 <= degt 0) (degtm : forall a b, degt a
 + degt b <= degt (a + b)) (l : List R[A]) : (l.map fun f : R[A] => f.coeff.supp
ort.inf degt).sum <= l.prod.coeff.support.inf degt
参数：degt0 : 0 <= degt 0；degtm : forall a b, degt a + degt b <= degt (a + b)；l : L
ist R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.foldr_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ 
l₂ : List α} [lcomm : LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f
 b l₁ = …
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `OrderDual.ofDual_le_ofDual`：ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual
 a <= ofDual b ↔ b <= a
· 使用定理 `AddMonoidAlgebra.sup_support_list_prod_le`：∀ {R : Type u_1} {A : Type u_
3} {B : Type u_5} [inst : SemilatticeSup B] [inst_1 : OrderBot B] [inst_2 : Semi
ring R]   [inst_3 : AddMonoid A…
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem le_inf_support_list_prod (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (l : List R[A]) :
    (l.map fun f : R[A] => f.coeff.support.inf degt).sum ≤ l.prod.coeff.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr ?_
  refine sup_support_list_prod_le ?_ ?_ l
  · refine (OrderDual.ofDual_le_ofDual.mp ?_)
    exact degt0
  · refine (fun a b => OrderDual.ofDual_le_ofDual.mp ?_)
    exact degtm a b
/-
**AddMonoidAlgebra.sup_support_pow_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：sup_support_pow_le (degb0 : degb 0 <= 0) (degbm : forall a b, degb (a + b)
 <= degb a + degb b) (n : Nat) (f : R[A]) : (f ^ n).coeff.support.sup degb <= n 
• f.coeff.support.sup degb
参数：degb0 : degb 0 <= 0；degbm : forall a b, degb (a + b) <= degb a + degb b；n : N
at；f : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n a).
prod = a ^ n
· 使用定理 `List.sum_replicate`：∀ {M : Type u_2} [inst : AddMonoid M] (n : ℕ) (a : M
), (List.replicate n a).sum = n • a
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `AddMonoidAlgebra.sup_support_list_prod_le`：∀ {R : Type u_1} {A : Type u_
3} {B : Type u_5} [inst : SemilatticeSup B] [inst_1 : OrderBot B] [inst_2 : Semi
ring R]   [inst_3 : AddMonoid A…
· 使用定理 `List.map_replicate`：∀ {n : ℕ} {α : Type u_1} {a : α} {α_1 : Type u_2} {f
 : α → α_1},   List.map f (List.replicate n a) = List.replicate n (f a)
-/
theorem sup_support_pow_le (degb0 : degb 0 ≤ 0) (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b)
    (n : ℕ) (f : R[A]) : (f ^ n).coeff.support.sup degb ≤ n • f.coeff.support.sup degb := by
  rw [← List.prod_replicate, ← List.sum_replicate]
  refine (sup_support_list_prod_le degb0 degbm _).trans_eq ?_
  rw [List.map_replicate]
/-
**AddMonoidAlgebra.le_inf_support_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebr
a`。
形式化陈述：le_inf_support_pow (degt0 : 0 <= degt 0) (degtm : forall a b, degt a + deg
t b <= degt (a + b)) (n : Nat) (f : R[A]) : n • f.coeff.support.inf degt <= (f ^
 n).coeff.support.inf degt
参数：degt0 : 0 <= degt 0；degtm : forall a b, degt a + degt b <= degt (a + b)；n : N
at；f : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.foldr_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ 
l₂ : List α} [lcomm : LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f
 b l₁ = …
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `OrderDual.ofDual_le_ofDual`：ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual
 a <= ofDual b ↔ b <= a
· 使用定理 `AddMonoidAlgebra.sup_support_pow_le`：sup_support_pow_le (degb0 : degb 0 
<= 0) (degbm : forall a b, degb (a + b) <= degb a + degb b) (n : Nat) (f : R[A])
 : (f ^ n).coeff.support.…
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem le_inf_support_pow (degt0 : 0 ≤ degt 0) (degtm : ∀ a b, degt a + degt b ≤ degt (a + b))
    (n : ℕ) (f : R[A]) : n • f.coeff.support.inf degt ≤ (f ^ n).coeff.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <| sup_support_pow_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) n f
  · exact degt0
  · exact degtm _ _

end AddMonoids

end Semiring

section CommutativeLemmas

variable [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B] [AddLeftMono B] [AddRightMono B]
  [AddCommMonoid T] [AddLeftMono T] [AddRightMono T]
  {degb : A → B} {degt : A → T}

/-
**AddMonoidAlgebra.sup_support_coeff_multisetProd_le** 是 Mathlib 中的一个定理，位于命名空间 `
AddMonoidAlgebra`。
形式化陈述：sup_support_coeff_multisetProd_le (degb0 : degb 0 <= 0) (degbm : forall a 
b, degb (a + b) <= degb a + degb b) (m : Multiset R[A]) : m.prod.coeff.support.s
up degb <= (m.map fun f : R[A] => f.coeff.support.sup degb).sum
参数：degb0 : degb 0 <= 0；degbm : forall a b, degb (a + b) <= degb a + degb b；m : M
ultiset R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.quot_mk_to_coe''`：quot_mk_to_coe'' (l : List α) : @Eq (Multiset
 α) (Quot.mk Setoid.r l) l
· 使用定理 `Multiset.map_coe`：∀ {α : Type u_1} {β : Type v} (f : α → β) (l : List α)
, Multiset.map f ↑l = ↑(List.map f l)
· 使用定理 `Multiset.sum_coe`：∀ {M : Type u_3} [inst : AddCommMonoid M] (l : List M)
, (↑l).sum = l.sum
· 使用定理 `Multiset.prod_coe`：prod_coe (l : List M) : prod ↑l = l.prod
· 使用定理 `AddMonoidAlgebra.sup_support_list_prod_le`：∀ {R : Type u_1} {A : Type u_
3} {B : Type u_5} [inst : SemilatticeSup B] [inst_1 : OrderBot B] [inst_2 : Semi
ring R]   [inst_3 : AddMonoid A…
-/
theorem sup_support_coeff_multisetProd_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (m : Multiset R[A]) :
    m.prod.coeff.support.sup degb ≤ (m.map fun f : R[A] => f.coeff.support.sup degb).sum := by
  induction m using Quot.inductionOn
  rw [Multiset.quot_mk_to_coe'', Multiset.map_coe, Multiset.sum_coe, Multiset.prod_coe]
  exact sup_support_list_prod_le degb0 degbm _

@[deprecated (since := "2026-06-18")]
alias sup_support_multiset_prod_le := sup_support_coeff_multisetProd_le
/-
**AddMonoidAlgebra.le_inf_support_coeff_multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `
AddMonoidAlgebra`。
形式化陈述：le_inf_support_coeff_multisetProd (degt0 : 0 <= degt 0) (degtm : forall a 
b, degt a + degt b <= degt (a + b)) (m : Multiset R[A]) : (m.map fun f : R[A] =>
 f.coeff.support.inf degt).sum <= m.prod.coeff.support.inf degt
参数：degt0 : 0 <= degt 0；degtm : forall a b, degt a + degt b <= degt (a + b)；m : M
ultiset R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.Perm.foldr_eq`：∀ {α : Type u_1} {β : Type u_2} {f : α → β → β} {l₁ 
l₂ : List α} [lcomm : LeftCommutative f],   l₁.Perm l₂ → ∀ (b : β), List.foldr f
 b l₁ = …
· 使用定理 `instLeftCommutativeOfCommutativeOfAssociative`：∀ {α : Sort u} {f : α → α
 → α} [hc : Std.Commutative f] [ha : Std.Associative f], LeftCommutative f
· 使用定理 `instCommutativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Commutative fun x1 x2 => x1 ⊓ x2
· 使用定理 `instAssociativeMin_mathlib`：∀ {α : Type u} [inst : SemilatticeInf α], St
d.Associative fun x1 x2 => x1 ⊓ x2
· 使用定理 `OrderDual.ofDual_le_ofDual`：ofDual_le_ofDual [LE α] {a b : αᵒᵈ} : ofDual
 a <= ofDual b ↔ b <= a
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_multisetProd_le`：sup_support_coeff_mu
ltisetProd_le (degb0 : degb 0 <= 0) (degbm : forall a b, degb (a + b) <= degb a 
+ degb b) (m : Multiset R[A]) : m.prod.c…
· 使用定理 `OrderDual.addLeftMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c 
: AddLeftMono α], AddLeftMono αᵒᵈ
· 使用定理 `OrderDual.addRightMono`：∀ {α : Type u} [inst : LE α] [inst_1 : Add α] [c
 : AddRightMono α], AddRightMono αᵒᵈ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem le_inf_support_coeff_multisetProd (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (m : Multiset R[A]) :
    (m.map fun f : R[A] => f.coeff.support.inf degt).sum ≤ m.prod.coeff.support.inf degt := by
  refine OrderDual.ofDual_le_ofDual.mpr <|
    sup_support_coeff_multisetProd_le (OrderDual.ofDual_le_ofDual.mp ?_)
      (fun a b => OrderDual.ofDual_le_ofDual.mp ?_) m
  · exact degt0
  · exact degtm _ _

@[deprecated (since := "2026-06-18")]
alias le_inf_support_multiset_prod := le_inf_support_coeff_multisetProd
/-
**AddMonoidAlgebra.sup_support_coeff_finsetProd_le** 是 Mathlib 中的一个定理，位于命名空间 `Ad
dMonoidAlgebra`。
形式化陈述：sup_support_coeff_finsetProd_le (degb0 : degb 0 <= 0) (degbm : forall a b,
 degb (a + b) <= degb a + degb b) (s : Finset ι) (f : ι -> R[A]) : (∏ i in s, f 
i).coeff.support.sup degb <= ∑ i in s, (f i).coeff.support.sup degb
参数：degb0 : degb 0 <= 0；degbm : forall a b, degb (a + b) <= degb a + degb b；s : F
inset ι；f : ι -> R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_multisetProd_le`：sup_support_coeff_mu
ltisetProd_le (degb0 : degb 0 <= 0) (degbm : forall a b, degb (a + b) <= degb a 
+ degb b) (m : Multiset R[A]) : m.prod.c…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
-/
theorem sup_support_coeff_finsetProd_le (degb0 : degb 0 ≤ 0)
    (degbm : ∀ a b, degb (a + b) ≤ degb a + degb b) (s : Finset ι) (f : ι → R[A]) :
    (∏ i ∈ s, f i).coeff.support.sup degb ≤ ∑ i ∈ s, (f i).coeff.support.sup degb :=
  (sup_support_coeff_multisetProd_le degb0 degbm _).trans_eq <| congr_arg _ <| Multiset.map_map ..

@[deprecated (since := "2026-06-18")]
alias sup_support_finsetProd_le := sup_support_coeff_finsetProd_le

@[deprecated (since := "2026-04-08")]
alias sup_support_finset_prod_le := sup_support_coeff_finsetProd_le
/-
**AddMonoidAlgebra.le_inf_support_coeff_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Ad
dMonoidAlgebra`。
形式化陈述：le_inf_support_coeff_finsetProd (degt0 : 0 <= degt 0) (degtm : forall a b,
 degt a + degt b <= degt (a + b)) (s : Finset ι) (f : ι -> R[A]) : (∑ i in s, (f
 i).coeff.support.inf degt) <= (∏ i in s, f i).coeff.support.inf degt
参数：degt0 : 0 <= degt 0；degtm : forall a b, degt a + degt b <= degt (a + b)；s : F
inset ι；f : ι -> R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `AddMonoidAlgebra.le_inf_support_coeff_multisetProd`：le_inf_support_coeff
_multisetProd (degt0 : 0 <= degt 0) (degtm : forall a b, degt a + degt b <= degt
 (a + b)) (m : Multiset R[A]) : (m.map f…
-/
theorem le_inf_support_coeff_finsetProd (degt0 : 0 ≤ degt 0)
    (degtm : ∀ a b, degt a + degt b ≤ degt (a + b)) (s : Finset ι) (f : ι → R[A]) :
    (∑ i ∈ s, (f i).coeff.support.inf degt) ≤ (∏ i ∈ s, f i).coeff.support.inf degt :=
  le_of_eq_of_le (by rw [Multiset.map_map]; rfl) (le_inf_support_coeff_multisetProd degt0 degtm _)

@[deprecated (since := "2026-06-18")]
alias le_inf_support_finsetProd := le_inf_support_coeff_finsetProd

@[deprecated (since := "2026-04-08")]
alias le_inf_support_finset_prod := le_inf_support_coeff_finsetProd

end CommutativeLemmas

end GeneralResultsAssumingSemilatticeSup


/-! ### Shorthands for special cases
Note that these definitions are reducible, in order to make it easier to apply the more generic
lemmas above. -/


section Degrees

variable [Semiring R] [Ring R']

section SupDegree

variable [SemilatticeSup B] [OrderBot B] (D : A → B)

/-- Let `R` be a semiring, let `A` be an `AddZeroClass`, let `B` be an `OrderBot`,
and let `D : A → B` be a "degree" function.
For an element `f : R[A]`, the element `supDegree f : B` is the supremum of all the elements in the
support of `f`, or `⊥` if `f` is zero.
Often, the Type `B` is `WithBot A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the maximum of the exponents.

If `A := σ →₀ ℕ` then `R[A] = MvPolynomial σ R`, and if we equip `σ` with a linear order then
the induced linear order on `Lex A` equips `MvPolynomial` ring with a
[monomial order](https://en.wikipedia.org/wiki/Monomial_order) (i.e. a linear order on `A`, the
type of (monic) monomials in `R[A]`, that respects addition). We make use of this monomial order
by taking `D := toLex`, and different monomial orders could be accessed via different type
synonyms once they are added. -/
/-
**AddMonoidAlgebra.supDegree** 是 Mathlib 中的一个缩写定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：supDegree (f : R[A]) : B
参数：f : R[A]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a semiring, let `A` be an `AddZeroClass`, let `B` be an `OrderBot`,
and let `D : A → B` be a "degree" function.
For an element `f : R[A]`, the element `supDegree f : B` is the supremum of all 
the elements in the
support of `f`, or `⊥` if `f` is zero.
Often, the Type `B` is `WithBot A`,
If, further, `A` has a linear order, then this notion coincides with the usual o
ne,
using the maximum of the exponents.

If `A := σ →₀ ℕ` then `R[A] = MvPolynomial σ R`, and if we equip `σ` with a line
ar order then
the induced linear order on `Lex A` equips `MvPolynomial` ring with a
[monomial order](https://en.wikipedia.org/wiki/Monomial_order) (i.e. a linear or
der on `A`, the
type of (monic) monomials in `R[A]`, that respects addition). We make use of thi
s monomial order
by taking `D := toLex`, and different monomial orders could be accessed via diff
erent type
synonyms once they are added.
-/
abbrev supDegree (f : R[A]) : B :=
  f.coeff.support.sup D

variable {D}
/-
**AddMonoidAlgebra.supDegree_add_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_add_le {f g : R[A]} : (f + g).supDegree D <= (f.supDegree D) ⊔ (
g.supDegree D)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_add_le`：sup_support_coeff_add_le : (f
 + g).coeff.support.sup degb <= f.coeff.support.sup degb ⊔ g.coeff.support.sup d
egb
-/
theorem supDegree_add_le {f g : R[A]} :
    (f + g).supDegree D ≤ (f.supDegree D) ⊔ (g.supDegree D) :=
  sup_support_coeff_add_le D f g

@[simp]
/-
**AddMonoidAlgebra.supDegree_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：supDegree_neg {f : R'[A]} : (-f).supDegree D = f.supDegree D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.support_neg`：support_neg (f : ι ->₀ G) : support (-f) = support 
f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supDegree_neg {f : R'[A]} : (-f).supDegree D = f.supDegree D := by simp [supDegree]
/-
**AddMonoidAlgebra.supDegree_sub_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_sub_le {f g : R'[A]} : (f - g).supDegree D <= f.supDegree D ⊔ g.
supDegree D
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.supDegree_neg`：supDegree_neg {f : R'[A]} : (-f).supDegr
ee D = f.supDegree D
· 使用定理 `AddMonoidAlgebra.supDegree_add_le`：supDegree_add_le {f g : R[A]} : (f + 
g).supDegree D <= (f.supDegree D) ⊔ (g.supDegree D)
-/
theorem supDegree_sub_le {f g : R'[A]} :
    (f - g).supDegree D ≤ f.supDegree D ⊔ g.supDegree D := by
  rw [sub_eq_add_neg, ← supDegree_neg (f := g)]; apply supDegree_add_le
/-
**AddMonoidAlgebra.supDegree_sum_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_sum_le {ι} {s : Finset ι} {f : ι -> R[A]} : (∑ i in s, f i).supD
egree D <= s.sup (fun i => (f i).supDegree D)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_sum`：∀ {R : Type u_1} {M : Type u_4} {ι : Type u_
7} [inst : Semiring R] (s : Finset ι) (f : ι → AddMonoidAlgebra R M),   (∑ i ∈ s
, f i).coeff = ∑…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Finset.sup_mono`：sup_mono (h : s₁ subseteq s₂) : s₁.sup f <= s₂.sup f
· 使用定理 `Finsupp.support_finsetSum`：support_finsetSum [DecidableEq β] [AddCommMon
oid M] {s : Finset α} {f : α -> β ->₀ M} : (Finset.sum s f).support subseteq s.b
iUnion fun x =>…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Finset.sup_biUnion`：sup_biUnion [DecidableEq β] (s : Finset γ) (t : γ ->
 Finset β) : (s.biUnion t).sup f = s.sup fun x => (t x).sup f
-/
theorem supDegree_sum_le {ι} {s : Finset ι} {f : ι → R[A]} :
    (∑ i ∈ s, f i).supDegree D ≤ s.sup (fun i => (f i).supDegree D) := by
  classical
  simp only [supDegree, coeff_sum]
  grw [Finsupp.support_finsetSum, Finset.sup_biUnion]
/-
**AddMonoidAlgebra.supDegree_single_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：supDegree_single_ne_zero (a : A) {r : R} (hr : r != 0) : (single a r).supD
egree D = D a
参数：a : A；hr : r != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_singleton`：sup_singleton {b : β} : ({b} : Finset β).sup f = f
 b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supDegree_single_ne_zero (a : A) {r : R} (hr : r ≠ 0) :
    (single a r).supDegree D = D a := by
  simp [supDegree, hr]

open scoped Classical in
/-
**AddMonoidAlgebra.supDegree_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_single (a : A) (r : R) : (single a r).supDegree D = if r = 0 the
n ⊥ else D a
参数：a : A；r : R。
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
· 使用定理 `AddMonoidAlgebra.single_zero`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] (m : M), AddMonoidAlgebra.single m 0 = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `AddMonoidAlgebra.supDegree_single_ne_zero`：supDegree_single_ne_zero (a :
 A) {r : R} (hr : r != 0) : (single a r).supDegree D = D a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supDegree_single (a : A) (r : R) :
    (single a r).supDegree D = if r = 0 then ⊥ else D a := by
  split_ifs with hr <;> simp [supDegree_single_ne_zero, hr]
/-
**AddMonoidAlgebra.coeff_eq_zero_of_not_le_supDegree** 是 Mathlib 中的一个定理，位于命名空间 `
AddMonoidAlgebra`。
形式化陈述：coeff_eq_zero_of_not_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a <= p.sup
Degree D) : p.coeff a = 0
参数：hlt : ¬ D a <= p.supDegree D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
-/
theorem coeff_eq_zero_of_not_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a ≤ p.supDegree D) :
    p.coeff a = 0 := by
  contrapose! hlt
  exact Finset.le_sup (Finsupp.mem_support_iff.2 hlt)

@[deprecated (since := "2026-06-18")]
alias apply_eq_zero_of_not_le_supDegree := coeff_eq_zero_of_not_le_supDegree
/-
**AddMonoidAlgebra.supDegree_withBot_some_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.suppo
rt.Nonempty) : supDegree (WithBot.some ∘ D) s = supDegree D s
参数：hs : s.coeff.support.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
-/
theorem supDegree_withBot_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty) :
    supDegree (WithBot.some ∘ D) s = supDegree D s := by
  unfold AddMonoidAlgebra.supDegree
  rw [← Finset.coe_sup' hs, Finset.sup'_eq_sup]
/-
**AddMonoidAlgebra.supDegree_eq_of_isMaxOn** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidA
lgebra`。
形式化陈述：supDegree_eq_of_isMaxOn {p : R[A]} {a : A} (hmem : a in p.coeff.support) (
hmax : IsMaxOn D p.coeff.support a) : p.supDegree D = D a
参数：hmem : a in p.coeff.support；hmax : IsMaxOn D p.coeff.support a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sup_eq_of_isMaxOn`：sup_eq_of_isMaxOn {a : α} (hmem : a in s) (hmax : IsM
axOn D s a) : s.sup D = D a
-/
theorem supDegree_eq_of_isMaxOn {p : R[A]} {a : A} (hmem : a ∈ p.coeff.support)
    (hmax : IsMaxOn D p.coeff.support a) : p.supDegree D = D a :=
  sup_eq_of_isMaxOn hmem hmax

variable {p q : R[A]}

@[simp]
/-
**AddMonoidAlgebra.supDegree_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：supDegree_zero : (0 : R[A]).supDegree D = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem supDegree_zero : (0 : R[A]).supDegree D = ⊥ := by simp [supDegree]
/-
**AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：ne_zero_of_supDegree_ne_bot : p.supDegree D != ⊥ -> p != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `AddMonoidAlgebra.supDegree_zero`：supDegree_zero : (0 : R[A]).supDegree D
 = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_supDegree_ne_bot : p.supDegree D ≠ ⊥ → p ≠ 0 := mt (fun h => h ▸ supDegree_zero)
/-
**AddMonoidAlgebra.ne_zero_of_not_supDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D <= b) : p != 0
参数：h : ¬ p.supDegree D <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot`：ne_zero_of_supDegree_ne_bo
t : p.supDegree D != ⊥ -> p != 0
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_not_supDegree_le {b : B} (h : ¬ p.supDegree D ≤ b) : p ≠ 0 :=
  ne_zero_of_supDegree_ne_bot (fun he => h <| he ▸ bot_le)

variable [AddZeroClass A]
/-
**AddMonoidAlgebra.supDegree_eq_of_max** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：supDegree_eq_of_max {b : B} (hb : b in Set.range D) (hmem : D.invFun b in 
p.coeff.support) (hmax : forall a in p.coeff.support, D a <= b) : p.supDegree D 
= b
参数：hb : b in Set.range D；hmem : D.invFun b in p.coeff.support；hmax : forall a in
 p.coeff.support, D a <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `sup_eq_of_max`：sup_eq_of_max [Nonempty α] {b : β} (hb : b in Set.range D
) (hmem : D.invFun b in s) (hmax : forall a in s, D a <= b) : s.sup D = b
-/
theorem supDegree_eq_of_max {b : B} (hb : b ∈ Set.range D) (hmem : D.invFun b ∈ p.coeff.support)
    (hmax : ∀ a ∈ p.coeff.support, D a ≤ b) : p.supDegree D = b :=
  sup_eq_of_max hb hmem hmax

variable [Add B]
/-
**AddMonoidAlgebra.supDegree_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_mul_le (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) [AddLeft
Mono B] [AddRightMono B] : (p * q).supDegree D <= p.supDegree D + q.supDegree D
参数：hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.sup_support_coeff_mul_le`：sup_support_coeff_mul_le {deg
b : A -> B} (degbm : forall a b, degb (a + b) <= degb a + degb b) (f g : R[A]) :
 (f * g).coeff.support.sup degb…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem supDegree_mul_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftMono B] [AddRightMono B] :
    (p * q).supDegree D ≤ p.supDegree D + q.supDegree D :=
  sup_support_coeff_mul_le (fun {_ _} => (hadd _ _).le) p q
/-
**AddMonoidAlgebra.supDegree_prod_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra
`。
形式化陈述：supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddC
ommMonoid B] [SemilatticeSup B] [OrderBot B] [AddLeftMono B] [AddRightMono B] {D
 : A -> B} (hzero : D 0 = 0) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) {ι
} {s : Finset ι} {f : ι -> R[A]} : (∏ i in s, f i).supDegree D <= ∑ i in s, (f i
).supDegree D
参数：hzero : D 0 = 0；hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_empty`：prod_empty : ∏ x in ∅, f x = 1
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `AddMonoidAlgebra.one_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Zero M], 1 = AddMonoidAlgebra.single 0 1
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AddMonoidAlgebra.supDegree_mul_le`：supDegree_mul_le (hadd : forall a1 a2
, D (a1 + a2) = D a1 + D a2) [AddLeftMono B] [AddRightMono B] : (p * q).supDegre
e D <= p.supDegree D + …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem supDegree_prod_le {R A B : Type*} [CommSemiring R] [AddCommMonoid A] [AddCommMonoid B]
    [SemilatticeSup B] [OrderBot B]
    [AddLeftMono B] [AddRightMono B]
    {D : A → B} (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    {ι} {s : Finset ι} {f : ι → R[A]} :
    (∏ i ∈ s, f i).supDegree D ≤ ∑ i ∈ s, (f i).supDegree D := by
  classical
  refine s.induction ?_ ?_
  · rw [Finset.prod_empty, Finset.sum_empty, one_def, supDegree_single]
    split_ifs; exacts [bot_le, hzero.le]
  · intro i s his ih
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact (supDegree_mul_le hadd).trans (by gcongr)
/-
**AddMonoidAlgebra.coeff_add_of_supDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：coeff_add_of_supDegree_le (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2)
 [AddLeftStrictMono B] [AddRightStrictMono B] (hD : D.Injective) {ap aq : A} (hp
 : p.supDegree D <= D ap) (hq : q.supDegree D <= D aq) : (p * q).coeff (ap + aq)
 = p.coeff ap * q.coeff aq
参数：hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2；hD : D.Injective；hp : p.supDeg
ree D <= D ap；hq : q.supDegree D <= D aq。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.coeff_mul`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] [inst_1 : Add M] [inst_2 : DecidableEq M]   (x y : AddMonoidAlgebra R M)
 (m : M),   (x *…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `addLeftMono_of_addLeftStrictMono`：∀ (M : Type u_3) [inst : Add M] [inst_
1 : PartialOrder M] [AddLeftStrictMono M], AddLeftMono M
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `add_lt_add_of_lt_of_le`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preord
er α] [AddLeftMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c ≤ d → a 
+ c < b + d
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ite_eq_right_iff`：∀ {α : Sort u_1} {p : Prop} [inst : Decidable p] {x y 
: α}, (if p then x else y) = y ↔ p → x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.notMem_support_iff`：notMem_support_iff {f : α ->₀ M} {a} : a ∉ f
.support ↔ f a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [AddLe
ftStrictMono α] {b c : α}, b < c → ∀ (a : α), a + b < a + c
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem coeff_add_of_supDegree_le (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    [AddLeftStrictMono B] [AddRightStrictMono B]
    (hD : D.Injective) {ap aq : A} (hp : p.supDegree D ≤ D ap) (hq : q.supDegree D ≤ D aq) :
    (p * q).coeff (ap + aq) = p.coeff ap * q.coeff aq := by
  classical
  simp_rw [coeff_mul, Finsupp.sum]
  rw [Finset.sum_eq_single ap, Finset.sum_eq_single aq, if_pos rfl]
  · refine fun a ha hne => if_neg (fun he => ?_)
    apply_fun D at he; simp_rw [hadd] at he
    exact (add_lt_add_right (((Finset.le_sup ha).trans hq).lt_of_ne <| hD.ne_iff.2 hne) _).ne he
  · intro h; rw [if_pos rfl, Finsupp.notMem_support_iff.1 h, mul_zero]
  · refine fun a ha hne => Finset.sum_eq_zero (fun a' ha' => if_neg <| fun he => ?_)
    apply_fun D at he
    simp_rw [hadd] at he
    have := addLeftMono_of_addLeftStrictMono B
    exact (add_lt_add_of_lt_of_le (((Finset.le_sup ha).trans hp).lt_of_ne <| hD.ne_iff.2 hne)
      <| (Finset.le_sup ha').trans hq).ne he
  · refine fun h => Finset.sum_eq_zero (fun a _ => ite_eq_right_iff.mpr <| fun _ => ?_)
    rw [Finsupp.notMem_support_iff.mp h, zero_mul]

@[deprecated (since := "2026-06-18")] alias apply_add_of_supDegree_le := coeff_add_of_supDegree_le

end SupDegree

section LinearOrder

variable [LinearOrder B] [OrderBot B] {p q : R[A]} (D : A → B)

/-- If `D` is an injection into a linear order `B`, the leading coefficient of `f : R[A]` is the
  nonzero coefficient of highest degree according to `D`, or 0 if `f = 0`. In general, it is defined
  to be the coefficient at an inverse image of `supDegree f` (if such exists). -/
/-
**AddMonoidAlgebra.leadingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：leadingCoeff [Nonempty A] (f : R[A]) : R
参数：f : R[A]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is an injection into a linear order `B`, the leading coefficient of `f : 
R[A]` is the
  nonzero coefficient of highest degree according to `D`, or 0 if `f = 0`. In ge
neral, it is defined
  to be the coefficient at an inverse image of `supDegree f` (if such exists).
-/
noncomputable def leadingCoeff [Nonempty A] (f : R[A]) : R := f.coeff <| D.invFun <| f.supDegree D

/-- An element `f : R[A]` is monic if its leading coefficient is one. -/
/-
**AddMonoidAlgebra.Monic** 是 Mathlib 中的一个定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：{R : Type u_1} →   {A : Type u_3} →     {B : Type u_5} →       [inst : Sem
iring R] →         [inst_1 : LinearOrder B] → [OrderBot B] → (A → B) → [Nonempty
 A] → AddMonoidAlgebra R A → Prop
参数：A → B。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `f : R[A]` is monic if its leading coefficient is one.
-/
@[reducible] def Monic [Nonempty A] (f : R[A]) : Prop :=
  f.leadingCoeff D = 1

variable {D}

@[simp]
/-
**AddMonoidAlgebra.leadingCoeff_single** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：leadingCoeff_single [Nonempty A] (hD : D.Injective) (a : A) (r : R) : (sin
gle a r).leadingCoeff D = r
参数：hD : D.Injective；a : A；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.invFun.congr_simp`：∀ {α : Sort u} {β : Sort u_3} [inst : Nonemp
ty α] (f f_1 : α → β),   f = f_1 → ∀ (a a_1 : β), a = a_1 → Function.invFun f a 
= Function.invFu…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AddMonoidAlgebra.single_zero`：∀ {R : Type u_1} {M : Type u_4} [inst : Se
miring R] (m : M), AddMonoidAlgebra.single m 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
-/
theorem leadingCoeff_single [Nonempty A] (hD : D.Injective) (a : A) (r : R) :
    (single a r).leadingCoeff D = r := by
  rw [leadingCoeff, supDegree_single]
  split_ifs with hr
  · simp [hr]
  · rw [Function.leftInverse_invFun hD]
    simp

@[simp]
/-
**AddMonoidAlgebra.leadingCoeff_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra
`。
形式化陈述：leadingCoeff_zero [Nonempty A] : (0 : R[A]).leadingCoeff D = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem leadingCoeff_zero [Nonempty A] : (0 : R[A]).leadingCoeff D = 0 := rfl
/-
**AddMonoidAlgebra.Monic.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra.Mon
ic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p : AddMonoidAlgebra R A} {D : A → B}
 [inst_3 : Nonempty A] [Nontrivial R], AddMonoidAlgebra.Monic D p → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.congr_simp`：∀ {R : Type u_1} {A : Type u_3
} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot
 B]   (D D_1 : A → B),   D = D…
-/
lemma Monic.ne_zero [Nonempty A] [Nontrivial R] (hp : p.Monic D) : p ≠ 0 := fun h => by
  simp_rw [Monic, h, leadingCoeff_zero, zero_ne_one] at hp

@[simp]
/-
**AddMonoidAlgebra.monic_one** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：monic_one [AddZeroClass A] (hD : D.Injective) : (1 : R[A]).Monic D
参数：hD : D.Injective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.Monic.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B : Type u
_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   (D : A 
→ B) [inst_3 : No…
· 使用定理 `AddMonoidAlgebra.one_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Zero M], 1 = AddMonoidAlgebra.single 0 1
· 使用定理 `AddMonoidAlgebra.leadingCoeff_single`：leadingCoeff_single [Nonempty A] (
hD : D.Injective) (a : A) (r : R) : (single a r).leadingCoeff D = r
-/
theorem monic_one [AddZeroClass A] (hD : D.Injective) : (1 : R[A]).Monic D := by
  rw [Monic, one_def, leadingCoeff_single hD]

variable (D) in
/-
**AddMonoidAlgebra.exists_supDegree_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `AddMo
noidAlgebra`。
形式化陈述：exists_supDegree_mem_support (hp : p != 0) : exists a in p.coeff.support, 
p.supDegree D = D a
参数：hp : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma exists_supDegree_mem_support (hp : p ≠ 0) : ∃ a ∈ p.coeff.support, p.supDegree D = D a :=
  Finset.exists_mem_eq_sup _ (by simpa [Finsupp.support_nonempty_iff]) D

variable (D) in
/-
**AddMonoidAlgebra.supDegree_mem_range** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgeb
ra`。
形式化陈述：supDegree_mem_range (hp : p != 0) : p.supDegree D in Set.range D
参数：hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddMonoidAlgebra.exists_supDegree_mem_support`：exists_supDegree_mem_supp
ort (hp : p != 0) : exists a in p.coeff.support, p.supDegree D = D a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma supDegree_mem_range (hp : p ≠ 0) : p.supDegree D ∈ Set.range D := by
  obtain ⟨a, -, he⟩ := exists_supDegree_mem_support D hp; exact ⟨a, he.symm⟩

variable {ι : Type*} {s : Finset ι} {i : ι} (hi : i ∈ s) {f : ι → R[A]}
/-
**AddMonoidAlgebra.supDegree_sum_lt** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：supDegree_sum_lt (hs : s.Nonempty) {b : B} (h : forall i in s, (f i).supDe
gree D < b) : (∑ i in s, f i).supDegree D < b
参数：hs : s.Nonempty；h : forall i in s, (f i).supDegree D < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `AddMonoidAlgebra.supDegree_sum_le`：supDegree_sum_le {ι} {s : Finset ι} {
f : ι -> R[A]} : (∑ i in s, f i).supDegree D <= s.sup (fun i => (f i).supDegree 
D)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma supDegree_sum_lt (hs : s.Nonempty) {b : B}
    (h : ∀ i ∈ s, (f i).supDegree D < b) : (∑ i ∈ s, f i).supDegree D < b := by
  refine supDegree_sum_le.trans_lt ((Finset.sup_lt_iff ?_).mpr h)
  obtain ⟨i, hi⟩ := hs; exact bot_le.trans_lt (h i hi)

variable [AddZeroClass A]

open Finsupp in
/-
**AddMonoidAlgebra.supDegree_add_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlg
ebra`。
形式化陈述：supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) : (p + q).supDeg
ree D = p.supDegree D
参数：h : q.supDegree D < p.supDegree D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AddMonoidAlgebra.supDegree_add_le`：supDegree_add_le {f g : R[A]} : (f + 
g).supDegree D <= (f.supDegree D) ⊔ (g.supDegree D)
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `AddMonoidAlgebra.exists_supDegree_mem_support`：exists_supDegree_mem_supp
ort (hp : p != 0) : exists a in p.coeff.support, p.supDegree D = D a
· 使用定理 `AddMonoidAlgebra.ne_zero_of_not_supDegree_le`：ne_zero_of_not_supDegree_l
e {b : B} (h : ¬ p.supDegree D <= b) : p != 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.coeff_eq_zero_of_not_le_supDegree`：coeff_eq_zero_of_not
_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a <= p.supDegree D) : p.coeff a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma supDegree_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).supDegree D = p.supDegree D := by
  apply (supDegree_add_le.trans <| sup_le le_rfl h.le).antisymm
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [he] at h ⊢
  apply Finset.le_sup
  simpa [coeff_eq_zero_of_not_le_supDegree h.not_ge] using ha
/-
**AddMonoidAlgebra.supDegree_add_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAl
gebra`。
形式化陈述：supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) : (p + q).supDe
gree D = q.supDegree D
参数：h : p.supDegree D < q.supDegree D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `AddMonoidAlgebra.supDegree_add_eq_left`：supDegree_add_eq_left (h : q.sup
Degree D < p.supDegree D) : (p + q).supDegree D = p.supDegree D
-/
lemma supDegree_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).supDegree D = q.supDegree D := by
  rw [add_comm, supDegree_add_eq_left h]
/-
**AddMonoidAlgebra.leadingCoeff_add_eq_left** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoid
Algebra`。
形式化陈述：leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) : (p + q).lea
dingCoeff D = p.leadingCoeff D
参数：h : q.supDegree D < p.supDegree D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用引理 `AddMonoidAlgebra.supDegree_mem_range`：supDegree_mem_range (hp : p != 0) 
: p.supDegree D in Set.range D
· 使用定理 `AddMonoidAlgebra.ne_zero_of_not_supDegree_le`：ne_zero_of_not_supDegree_l
e {b : B} (h : ¬ p.supDegree D <= b) : p != 0
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用引理 `AddMonoidAlgebra.supDegree_add_eq_left`：supDegree_add_eq_left (h : q.sup
Degree D < p.supDegree D) : (p + q).supDegree D = p.supDegree D
· 使用定理 `AddMonoidAlgebra.coeff_add`：∀ {R : Type u_1} {M : Type u_4} [inst : Semi
ring R] (x y : AddMonoidAlgebra R M), (x + y).coeff = x.coeff + y.coeff
· 使用引理 `Finsupp.add_apply`：add_apply (g₁ g₂ : ι ->₀ M) (a : ι) : (g₁ + g₂) a = g
₁ a + g₂ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.coeff_eq_zero_of_not_le_supDegree`：coeff_eq_zero_of_not
_le_supDegree {p : R[A]} {a : A} (hlt : ¬ D a <= p.supDegree D) : p.coeff a = 0
· 使用定理 `Function.apply_invFun_apply`：apply_invFun_apply {α β : Type*} {f : α -> 
β} {a : α} : f (@invFun _ _ ⟨a⟩ f (f a)) = f a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
lemma leadingCoeff_add_eq_left (h : q.supDegree D < p.supDegree D) :
    (p + q).leadingCoeff D = p.leadingCoeff D := by
  obtain ⟨a, he⟩ := supDegree_mem_range D (ne_zero_of_not_supDegree_le h.not_ge)
  rw [leadingCoeff, supDegree_add_eq_left h, coeff_add, Finsupp.add_apply, ← leadingCoeff,
    coeff_eq_zero_of_not_le_supDegree (D := D), add_zero]
  rw [← he, Function.apply_invFun_apply (f := D), he]; exact h.not_ge
/-
**AddMonoidAlgebra.leadingCoeff_add_eq_right** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoi
dAlgebra`。
形式化陈述：leadingCoeff_add_eq_right (h : p.supDegree D < q.supDegree D) : (p + q).le
adingCoeff D = q.leadingCoeff D
参数：h : p.supDegree D < q.supDegree D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `AddMonoidAlgebra.leadingCoeff_add_eq_left`：leadingCoeff_add_eq_left (h :
 q.supDegree D < p.supDegree D) : (p + q).leadingCoeff D = p.leadingCoeff D
-/
lemma leadingCoeff_add_eq_right (h : p.supDegree D < q.supDegree D) :
    (p + q).leadingCoeff D = q.leadingCoeff D := by
  rw [add_comm, leadingCoeff_add_eq_left h]
/-
**AddMonoidAlgebra.supDegree_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlg
ebra`。
形式化陈述：supDegree_mem_support (hD : D.Injective) (hp : p != 0) : D.invFun (p.supDe
gree D) in p.coeff.support
参数：hD : D.Injective；hp : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用引理 `AddMonoidAlgebra.exists_supDegree_mem_support`：exists_supDegree_mem_supp
ort (hp : p != 0) : exists a in p.coeff.support, p.supDegree D = D a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
-/
lemma supDegree_mem_support (hD : D.Injective) (hp : p ≠ 0) :
    D.invFun (p.supDegree D) ∈ p.coeff.support := by
  obtain ⟨a, ha, he⟩ := exists_supDegree_mem_support D hp
  rwa [he, Function.leftInverse_invFun hD]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**AddMonoidAlgebra.leadingCoeff_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：leadingCoeff_eq_zero (hD : D.Injective) : p.leadingCoeff D = 0 ↔ p = 0
参数：hD : D.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Function.mtr`：∀ {a b : Prop}, (¬a → ¬b) → b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Finsupp.mem_support_iff`：mem_support_iff {f : α ->₀ M} : forall {a : α},
 a in f.support ↔ f a != 0
· 使用引理 `AddMonoidAlgebra.supDegree_mem_support`：supDegree_mem_support (hD : D.In
jective) (hp : p != 0) : D.invFun (p.supDegree D) in p.coeff.support
· 使用定理 `AddMonoidAlgebra.leadingCoeff_zero`：leadingCoeff_zero [Nonempty A] : (0 
: R[A]).leadingCoeff D = 0
-/
lemma leadingCoeff_eq_zero (hD : D.Injective) : p.leadingCoeff D = 0 ↔ p = 0 := by
  refine ⟨(fun h => ?_).mtr, fun h => h ▸ leadingCoeff_zero⟩
  rw [leadingCoeff, ← Ne, ← Finsupp.mem_support_iff]
  exact supDegree_mem_support hD h
/-
**AddMonoidAlgebra.leadingCoeff_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlge
bra`。
形式化陈述：leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D != 0 ↔ p != 0
参数：hD : D.Injective。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.ne`：∀ {α : Sort u_1} {β : Sort u_2} {a b : α} {c d : β}, (a = b ↔ c 
= d) → (a ≠ b ↔ c ≠ d)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用引理 `AddMonoidAlgebra.leadingCoeff_eq_zero`：leadingCoeff_eq_zero (hD : D.Inje
ctive) : p.leadingCoeff D = 0 ↔ p = 0
-/
lemma leadingCoeff_ne_zero (hD : D.Injective) : p.leadingCoeff D ≠ 0 ↔ p ≠ 0 :=
  (leadingCoeff_eq_zero hD).ne
/-
**AddMonoidAlgebra.supDegree_sub_lt_of_leadingCoeff_eq** 是 Mathlib 中的一个引理，位于命名空间
 `AddMonoidAlgebra`。
形式化陈述：supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {R} [Ring R] {p q :
 R[A]} (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCo
eff D) : (p - q).supDegree D < p.supDegree D ∨ p = q
参数：hD : D.Injective；hd : p.supDegree D = q.supDegree D；hc : p.leadingCoeff D = q
.leadingCoeff D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_right`：∀ {a b : Prop}, a ∨ b ↔ ¬b → a
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `AddMonoidAlgebra.supDegree_sub_le`：supDegree_sub_le {f g : R'[A]} : (f -
 g).supDegree D <= f.supDegree D ⊔ g.supDegree D
· 使用定理 `sup_idem`：sup_idem (a : α) : a ⊔ a = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AddMonoidAlgebra.leadingCoeff_eq_zero`：leadingCoeff_eq_zero (hD : D.Inje
ctive) : p.leadingCoeff D = 0 ↔ p = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `AddMonoidAlgebra.coeff_sub`：∀ {R : Type u_1} {M : Type u_4} [inst : Ring
 R] (x y : AddMonoidAlgebra R M), (x - y).coeff = x.coeff - y.coeff
· 使用引理 `Finsupp.sub_apply`：sub_apply [SubNegZeroMonoid G] (g₁ g₂ : ι ->₀ G) (a :
 ι) : (g₁ - g₂) a = g₁ a - g₂ a
-/
lemma supDegree_sub_lt_of_leadingCoeff_eq (hD : D.Injective) {R} [Ring R] {p q : R[A]}
    (hd : p.supDegree D = q.supDegree D) (hc : p.leadingCoeff D = q.leadingCoeff D) :
    (p - q).supDegree D < p.supDegree D ∨ p = q := by
  rw [or_iff_not_imp_right]
  refine fun he => (supDegree_sub_le.trans ?_).lt_of_ne ?_
  · rw [hd, sup_idem]
  · rw [← sub_eq_zero, ← leadingCoeff_eq_zero hD, leadingCoeff] at he
    refine fun h => he ?_
    rwa [h, coeff_sub, Finsupp.sub_apply, ← leadingCoeff, hd, ← leadingCoeff, sub_eq_zero]
/-
**AddMonoidAlgebra.supDegree_leadingCoeff_sum_eq** 是 Mathlib 中的一个引理，位于命名空间 `AddM
onoidAlgebra`。
形式化陈述：supDegree_leadingCoeff_sum_eq (hi : i in s) (hmax : forall j in s, j != i 
-> (f j).supDegree D < (f i).supDegree D) : (∑ j in s, f j).supDegree D = (f i).
supDegree D ∧ (∑ j in s, f j).leadingCoeff D = (f i).leadingCoeff D
参数：hi : i in s；hmax : forall j in s, j != i -> (f j).supDegree D < (f i).supDegr
ee D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.add_sum_erase`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → f 
a + ∑ x ∈ …
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `AddMonoidAlgebra.supDegree_sum_lt`：supDegree_sum_lt (hs : s.Nonempty) {b
 : B} (h : forall i in s, (f i).supDegree D < b) : (∑ i in s, f i).supDegree D <
 b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `AddMonoidAlgebra.supDegree_add_eq_left`：supDegree_add_eq_left (h : q.sup
Degree D < p.supDegree D) : (p + q).supDegree D = p.supDegree D
· 使用引理 `AddMonoidAlgebra.leadingCoeff_add_eq_left`：leadingCoeff_add_eq_left (h :
 q.supDegree D < p.supDegree D) : (p + q).leadingCoeff D = p.leadingCoeff D
-/
lemma supDegree_leadingCoeff_sum_eq
    (hi : i ∈ s) (hmax : ∀ j ∈ s, j ≠ i → (f j).supDegree D < (f i).supDegree D) :
    (∑ j ∈ s, f j).supDegree D = (f i).supDegree D ∧
    (∑ j ∈ s, f j).leadingCoeff D = (f i).leadingCoeff D := by
  classical
  rw [← s.add_sum_erase _ hi]
  by_cases! hs : s.erase i = ∅
  · rw [hs, Finset.sum_empty, add_zero]; exact ⟨rfl, rfl⟩
  suffices _ from ⟨supDegree_add_eq_left this, leadingCoeff_add_eq_left this⟩
  refine supDegree_sum_lt ?_ (fun j hj => ?_)
  · exact hs
  · rw [Finset.mem_erase] at hj; exact hmax j hj.2 hj.1

open Finset in
/-
**AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree'** 是 Mathlib 中的一个引理，位于命名空间 `Ad
dMonoidAlgebra`。
形式化陈述：sum_ne_zero_of_injOn_supDegree' (hs : exists i in s, f i != 0) (hd : (s : 
Set ι).InjOn (supDegree D ∘ f)) : ∑ i in s, f i != 0
参数：hs : exists i in s, f i != 0；hd : (s : Set ι).InjOn (supDegree D ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `Ne.irrefl`：∀ {α : Sort u} {a : α}, a ≠ a → False
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddMonoidAlgebra.ne_zero_of_supDegree_ne_bot`：ne_zero_of_supDegree_ne_bo
t : p.supDegree D != ⊥ -> p != 0
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Set.InjOn.ne`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : α → β} {x
 y : α}, Set.InjOn f s → x ∈ s → y ∈ s → x ≠ y → f x ≠ f y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用引理 `AddMonoidAlgebra.supDegree_leadingCoeff_sum_eq`：supDegree_leadingCoeff_s
um_eq (hi : i in s) (hmax : forall j in s, j != i -> (f j).supDegree D < (f i).s
upDegree D) : (∑ j in s, f j).supDeg…
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
-/
lemma sum_ne_zero_of_injOn_supDegree' (hs : ∃ i ∈ s, f i ≠ 0)
    (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 := by
  obtain ⟨j, hj, hne⟩ := hs
  obtain ⟨i, hi, he⟩ := exists_mem_eq_sup _ ⟨j, hj⟩ (supDegree D ∘ f)
  by_cases! h : ∀ k ∈ s, k = i
  · refine (sum_eq_single_of_mem j hj (fun k hk hne => ?_)).trans_ne hne
    rw [h k hk, h j hj] at hne; exact hne.irrefl.elim
  obtain ⟨j, hj, hne⟩ := h
  apply ne_zero_of_supDegree_ne_bot (D := D)
  have (k) (hk : k ∈ s) (hne : k ≠ i) : supDegree D (f k) < supDegree D (f i) :=
    ((le_sup hk).trans_eq he).lt_of_ne (hd.ne hk hi hne)
  rw [(supDegree_leadingCoeff_sum_eq hi this).1]
  exact (this j hj hne).ne_bot
/-
**AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree** 是 Mathlib 中的一个引理，位于命名空间 `Add
MonoidAlgebra`。
形式化陈述：sum_ne_zero_of_injOn_supDegree (hs : s.Nonempty) (hf : forall i in s, f i 
!= 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) : ∑ i in s, f i != 0
参数：hs : s.Nonempty；hf : forall i in s, f i != 0；hd : (s : Set ι).InjOn (supDegre
e D ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AddMonoidAlgebra.sum_ne_zero_of_injOn_supDegree'`：sum_ne_zero_of_injOn_s
upDegree' (hs : exists i in s, f i != 0) (hd : (s : Set ι).InjOn (supDegree D ∘ 
f)) : ∑ i in s, f i != 0
-/
lemma sum_ne_zero_of_injOn_supDegree (hs : s.Nonempty)
    (hf : ∀ i ∈ s, f i ≠ 0) (hd : (s : Set ι).InjOn (supDegree D ∘ f)) :
    ∑ i ∈ s, f i ≠ 0 :=
  let ⟨i, hi⟩ := hs
  sum_ne_zero_of_injOn_supDegree' ⟨i, hi, hf i hi⟩ hd

variable [Add B]
variable [AddLeftStrictMono B] [AddRightStrictMono B]
/-
**AddMonoidAlgebra.coeff_supDegree_add_supDegree** 是 Mathlib 中的一个引理，位于命名空间 `AddM
onoidAlgebra`。
形式化陈述：coeff_supDegree_add_supDegree (hD : D.Injective) (hadd : forall a1 a2, D (
a1 + a2) = D a1 + D a2) : (p * q).coeff (D.invFun (p.supDegree D + q.supDegree D
)) = p.leadingCoeff D * q.leadingCoeff D
参数：hD : D.Injective；hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Function.invFun.congr_simp`：∀ {α : Sort u} {β : Sort u_3} [inst : Nonemp
ty α] (f f_1 : α → β),   f = f_1 → ∀ (a a_1 : β), a = a_1 → Function.invFun f a 
= Function.invFu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddMonoidAlgebra.supDegree_zero`：supDegree_zero : (0 : R[A]).supDegree D
 = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `AddMonoidAlgebra.exists_supDegree_mem_support`：exists_supDegree_mem_supp
ort (hp : p != 0) : exists a in p.coeff.support, p.supDegree D = D a
· 使用定理 `Function.leftInverse_invFun`：leftInverse_invFun (hf : Injective f) : Lef
tInverse (invFun f) f
· 使用定理 `AddMonoidAlgebra.coeff_add_of_supDegree_le`：coeff_add_of_supDegree_le (h
add : forall a1 a2, D (a1 + a2) = D a1 + D a2) [AddLeftStrictMono B] [AddRightSt
rictMono B] (hD : D.Injective) {…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
lemma coeff_supDegree_add_supDegree (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).coeff (D.invFun (p.supDegree D + q.supDegree D)) =
      p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp
  obtain rfl | hq := eq_or_ne q 0
  · simp
  obtain ⟨ap, -, hp⟩ := exists_supDegree_mem_support D hp
  obtain ⟨aq, -, hq⟩ := exists_supDegree_mem_support D hq
  simp_rw [leadingCoeff, hp, hq, ← hadd, Function.leftInverse_invFun hD _]
  exact coeff_add_of_supDegree_le hadd hD hp.le hq.le

@[deprecated (since := "2026-06-18")]
alias apply_supDegree_add_supDegree := coeff_supDegree_add_supDegree

set_option backward.isDefEq.respectTransparency false in
/-
**AddMonoidAlgebra.supDegree_mul** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：supDegree_mul (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 
+ D a2) (hpq : leadingCoeff D p * leadingCoeff D q != 0) (hp : p != 0) (hq : q !
= 0) : (p * q).supDegree D = p.supDegree D + q.supDegree D
参数：hD : D.Injective；hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2；hpq : leading
Coeff D p * leadingCoeff D q != 0；hp : p != 0；hq : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `AddMonoidAlgebra.supDegree_eq_of_max`：supDegree_eq_of_max {b : B} (hb : 
b in Set.range D) (hmem : D.invFun b in p.coeff.support) (hmax : forall a in p.c
oeff.support, D a <= b) : …
· 使用定理 `AddSubsemigroup.add_mem`：∀ {M : Type u_1} [inst : Add M] (S : AddSubsemi
group M) {x y : M}, x ∈ S → y ∈ S → x + y ∈ S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddSubsemigroup.coe_set_mk`：∀ {M : Type u_1} [inst : Add M] (s : Set M) 
(h_add : ∀ {a b : M}, a ∈ s → b ∈ s → a + b ∈ s),   ↑{ carrier := s, add_mem' :=
 h_add } = s
· 使用定理 `AddHom.srange_mk`：∀ {M : Type u_1} {N : Type u_2} [inst : Add M] [inst_1
 : Add N] (f : M → N) (hf : ∀ (x y : M), f (x + y) = f x + f y),   { toFun := f,
 map_a…
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `AddSubsemigroup.instAddMemClass`：∀ {M : Type u_1} [inst : Add M], AddMem
Class (AddSubsemigroup M) M
· 使用引理 `AddMonoidAlgebra.supDegree_mem_range`：supDegree_mem_range (hp : p != 0) 
: p.supDegree D in Set.range D
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AddMonoidAlgebra.coeff_supDegree_add_supDegree`：coeff_supDegree_add_supD
egree (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) : (p *
 q).coeff (D.invFun (p.supDegree D +…
· 使用定理 `addLeftMono_of_addLeftStrictMono`：∀ (M : Type u_3) [inst : Add M] [inst_
1 : PartialOrder M] [AddLeftStrictMono M], AddLeftMono M
· 使用定理 `addRightMono_of_addRightStrictMono`：∀ (M : Type u_3) [inst : Add M] [ins
t_1 : PartialOrder M] [AddRightStrictMono M], AddRightMono M
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `AddMonoidAlgebra.supDegree_mul_le`：supDegree_mul_le (hadd : forall a1 a2
, D (a1 + a2) = D a1 + D a2) [AddLeftMono B] [AddRightMono B] : (p * q).supDegre
e D <= p.supDegree D + …
-/
lemma supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hpq : leadingCoeff D p * leadingCoeff D q ≠ 0)
    (hp : p ≠ 0) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  apply supDegree_eq_of_max
  · rw [← AddSubsemigroup.coe_set_mk (Set.range D), ← AddHom.srange_mk _ hadd, SetLike.mem_coe]
    · exact add_mem (supDegree_mem_range D hp) (supDegree_mem_range D hq)
    · exact (AddHom.srange ⟨D, hadd⟩).add_mem
  · simp_rw [Finsupp.mem_support_iff, coeff_supDegree_add_supDegree hD hadd]
    exact hpq
  · have := addLeftMono_of_addLeftStrictMono B
    have := addRightMono_of_addRightStrictMono B
    exact fun a ha => (Finset.le_sup ha).trans (supDegree_mul_le hadd)
/-
**AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_left** 是 Mathlib 中的一个定理，位于命名空间
 `AddMonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       AddMonoidAlgebra.Monic D q →         p ≠ 0 → AddMonoidAlgebra.supD
egree D (p * q) = AddMonoidAlgebra.supDegree D p + AddMonoidAlgebra.supDegree D 
q
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `AddMonoidAlgebra.supDegree_mul`：supDegree_mul (hD : D.Injective) (hadd :
 forall a1 a2, D (a1 + a2) = D a1 + D a2) (hpq : leadingCoeff D p * leadingCoeff
 D q != 0) (hp : p !…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `AddMonoidAlgebra.leadingCoeff_eq_zero`：leadingCoeff_eq_zero (hD : D.Inje
ctive) : p.leadingCoeff D = 0 ↔ p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddMonoidAlgebra.Monic.ne_zero`：∀ {R : Type u_1} {A : Type u_3} {B : Typ
e u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   {p :
 AddMonoidAlgebra R …
-/
lemma Monic.supDegree_mul_of_ne_zero_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hq : q.Monic D) (hp : p ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hp (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp hq.ne_zero
  simp_rw [hq, mul_one, Ne, leadingCoeff_eq_zero hD, hp, not_false_eq_true]
/-
**AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_right** 是 Mathlib 中的一个定理，位于命名空
间 `AddMonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       AddMonoidAlgebra.Monic D p →         q ≠ 0 → AddMonoidAlgebra.supD
egree D (p * q) = AddMonoidAlgebra.supDegree D p + AddMonoidAlgebra.supDegree D 
q
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用引理 `AddMonoidAlgebra.supDegree_mul`：supDegree_mul (hD : D.Injective) (hadd :
 forall a1 a2, D (a1 + a2) = D a1 + D a2) (hpq : leadingCoeff D p * leadingCoeff
 D q != 0) (hp : p !…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `AddMonoidAlgebra.leadingCoeff_eq_zero`：leadingCoeff_eq_zero (hD : D.Inje
ctive) : p.leadingCoeff D = 0 ↔ p = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `AddMonoidAlgebra.Monic.ne_zero`：∀ {R : Type u_1} {A : Type u_3} {B : Typ
e u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   {p :
 AddMonoidAlgebra R …
-/
lemma Monic.supDegree_mul_of_ne_zero_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q ≠ 0) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R; · exact (hq (Subsingleton.elim _ _)).elim
  apply supDegree_mul hD hadd ?_ hp.ne_zero hq
  simp_rw [hp, one_mul, Ne, leadingCoeff_eq_zero hD, hq, not_false_eq_true]
/-
**AddMonoidAlgebra.Monic.supDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       ⊥ + ⊥ = ⊥ →         AddMonoidAlgebra.Monic D p →           AddMono
idAlgebra.Monic D q →             AddMonoidAlgebra.supDegree D (p * q) = AddMono
idAlgebra.supDegree D p + AddMonoidAlgebra.supDegree D q
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `AddMonoidAlgebra.supDegree_zero`：supDegree_zero : (0 : R[A]).supDegree D
 = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_left`：∀ {R : Type u_1} {
A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_
2 : OrderBot B]   {p q : AddMonoidAlgebra …
· 使用定理 `AddMonoidAlgebra.Monic.ne_zero`：∀ {R : Type u_1} {A : Type u_3} {B : Typ
e u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   {p :
 AddMonoidAlgebra R …
-/
lemma Monic.supDegree_mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hbot : (⊥ : B) + ⊥ = ⊥) (hp : p.Monic D) (hq : q.Monic D) :
    (p * q).supDegree D = p.supDegree D + q.supDegree D := by
  cases subsingleton_or_nontrivial R
  · simp_rw [Subsingleton.eq_zero p, Subsingleton.eq_zero q, mul_zero, supDegree_zero, hbot]
  exact hq.supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero
/-
**AddMonoidAlgebra.leadingCoeff_mul** 是 Mathlib 中的一个引理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：leadingCoeff_mul [NoZeroDivisors R] (hD : D.Injective) (hadd : forall a1 a
2, D (a1 + a2) = D a1 + D a2) : (p * q).leadingCoeff D = p.leadingCoeff D * q.le
adingCoeff D
参数：hD : D.Injective；hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.leadingCoeff.congr_simp`：∀ {R : Type u_1} {A : Type u_3
} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot
 B]   (D D_1 : A → B),   D = D…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `AddMonoidAlgebra.coeff_supDegree_add_supDegree`：coeff_supDegree_add_supD
egree (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) : (p *
 q).coeff (D.invFun (p.supDegree D +…
· 使用引理 `AddMonoidAlgebra.supDegree_mul`：supDegree_mul (hD : D.Injective) (hadd :
 forall a1 a2, D (a1 + a2) = D a1 + D a2) (hpq : leadingCoeff D p * leadingCoeff
 D q != 0) (hp : p !…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `AddMonoidAlgebra.leadingCoeff_eq_zero`：leadingCoeff_eq_zero (hD : D.Inje
ctive) : p.leadingCoeff D = 0 ↔ p = 0
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
-/
lemma leadingCoeff_mul [NoZeroDivisors R]
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) :
    (p * q).leadingCoeff D = p.leadingCoeff D * q.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · simp_rw [leadingCoeff_zero, zero_mul, leadingCoeff_zero]
  obtain rfl | hq := eq_or_ne q 0
  · simp_rw [leadingCoeff_zero, mul_zero, leadingCoeff_zero]
  rw [← coeff_supDegree_add_supDegree hD hadd, ← supDegree_mul hD hadd ?_ hp hq, leadingCoeff]
  apply mul_ne_zero <;> rwa [Ne, leadingCoeff_eq_zero hD]
/-
**AddMonoidAlgebra.Monic.leadingCoeff_mul_eq_left** 是 Mathlib 中的一个定理，位于命名空间 `Add
MonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       AddMonoidAlgebra.Monic D q → AddMonoidAlgebra.leadingCoeff D (p * 
q) = AddMonoidAlgebra.leadingCoeff D p
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_left`：∀ {R : Type u_1} {
A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_
2 : OrderBot B]   {p q : AddMonoidAlgebra …
· 使用引理 `AddMonoidAlgebra.coeff_supDegree_add_supDegree`：coeff_supDegree_add_supD
egree (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) : (p *
 q).coeff (D.invFun (p.supDegree D +…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
lemma Monic.leadingCoeff_mul_eq_left
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hq : q.Monic D) :
    (p * q).leadingCoeff D = p.leadingCoeff D := by
  obtain rfl | hp := eq_or_ne p 0
  · rw [zero_mul]
  rw [leadingCoeff, hq.supDegree_mul_of_ne_zero_left hD hadd hp,
    coeff_supDegree_add_supDegree hD hadd, hq, mul_one]
/-
**AddMonoidAlgebra.Monic.leadingCoeff_mul_eq_right** 是 Mathlib 中的一个定理，位于命名空间 `Ad
dMonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       AddMonoidAlgebra.Monic D p → AddMonoidAlgebra.leadingCoeff D (p * 
q) = AddMonoidAlgebra.leadingCoeff D q
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddMonoidAlgebra.leadingCoeff.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B :
 Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   
(D : A → B) [inst_3 : No…
· 使用定理 `AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_right`：∀ {R : Type u_1} 
{A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst
_2 : OrderBot B]   {p q : AddMonoidAlgebra …
· 使用引理 `AddMonoidAlgebra.coeff_supDegree_add_supDegree`：coeff_supDegree_add_supD
egree (hD : D.Injective) (hadd : forall a1 a2, D (a1 + a2) = D a1 + D a2) : (p *
 q).coeff (D.invFun (p.supDegree D +…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma Monic.leadingCoeff_mul_eq_right
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hp : p.Monic D) :
    (p * q).leadingCoeff D = q.leadingCoeff D := by
  obtain rfl | hq := eq_or_ne q 0
  · rw [mul_zero]
  rw [leadingCoeff, hp.supDegree_mul_of_ne_zero_right hD hadd hq,
    coeff_supDegree_add_supDegree hD hadd, hp, one_mul]
/-
**AddMonoidAlgebra.Monic.mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} {A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1
 : LinearOrder B] [inst_2 : OrderBot B]   {p q : AddMonoidAlgebra R A} {D : A → 
B} [inst_3 : AddZeroClass A] [inst_4 : Add B] [AddLeftStrictMono B]   [AddRightS
trictMono B],   Function.Injective D →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + 
D a2) →       AddMonoidAlgebra.Monic D p → AddMonoidAlgebra.Monic D q → AddMonoi
dAlgebra.Monic D (p * q)
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p * q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.Monic.eq_1`：∀ {R : Type u_1} {A : Type u_3} {B : Type u
_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   (D : A 
→ B) [inst_3 : No…
· 使用定理 `AddMonoidAlgebra.Monic.leadingCoeff_mul_eq_left`：∀ {R : Type u_1} {A : T
ype u_3} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : O
rderBot B]   {p q : AddMonoidAlgebra …
-/
lemma Monic.mul
    (hD : D.Injective) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2)
    (hp : p.Monic D) (hq : q.Monic D) : (p * q).Monic D := by
  rw [Monic, hq.leadingCoeff_mul_eq_left hD hadd]; exact hp

section AddMonoid

variable {A B : Type*} [AddMonoid A] [AddMonoid B] [LinearOrder B] [OrderBot B]
  [AddLeftStrictMono B] [AddRightStrictMono B]
  {D : A → B} {p : R[A]} {n : ℕ}

/-
**AddMonoidAlgebra.Monic.pow** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {A : Type u_8} {B : Type u_9} [inst_1
 : AddMonoid A] [inst_2 : AddMonoid B]   [inst_3 : LinearOrder B] [inst_4 : Orde
rBot B] [AddLeftStrictMono B] [AddRightStrictMono B] {D : A → B}   {p : AddMonoi
dAlgebra R A} {n : ℕ},   (∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2) →     Functi
on.Injective D → AddMonoidAlgebra.Monic D p → AddMonoidAlgebra.Monic D (p ^ n)
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `AddMonoidAlgebra.monic_one`：monic_one [AddZeroClass A] (hD : D.Injective
) : (1 : R[A]).Monic D
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `AddMonoidAlgebra.Monic.mul`：∀ {R : Type u_1} {A : Type u_3} {B : Type u_
5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   {p q : A
ddMonoidAlgebra …
-/
lemma Monic.pow
    (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    (hp : p.Monic D) : (p ^ n).Monic D := by
  induction n with
  | zero => rw [pow_zero]; exact monic_one hD
  | succ n ih => rw [pow_succ']; exact hp.mul hD hadd ih
/-
**AddMonoidAlgebra.Monic.supDegree_pow** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgeb
ra.Monic`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {A : Type u_8} {B : Type u_9} [inst_1
 : AddMonoid A] [inst_2 : AddMonoid B]   [inst_3 : LinearOrder B] [inst_4 : Orde
rBot B] [AddLeftStrictMono B] [AddRightStrictMono B] {D : A → B}   {p : AddMonoi
dAlgebra R A} {n : ℕ},   D 0 = 0 →     (∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2
) →       Function.Injective D →         ∀ [Nontrivial R],           AddMonoidAl
gebra.Monic D p → AddMonoidAlgebra.supDegree D (p ^ n) = n • AddMonoidAlgebra.su
pDegree D p
参数：∀ (a1 a2 : A), D (a1 + a2) = D a1 + D a2；p ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `AddMonoidAlgebra.one_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiri
ng R] [inst_1 : Zero M], 1 = AddMonoidAlgebra.single 0 1
· 使用定理 `AddMonoidAlgebra.supDegree_single`：supDegree_single (a : A) (r : R) : (s
ingle a r).supDegree D = if r = 0 then ⊥ else D a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `AddMonoidAlgebra.Monic.supDegree_mul_of_ne_zero_left`：∀ {R : Type u_1} {
A : Type u_3} {B : Type u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_
2 : OrderBot B]   {p q : AddMonoidAlgebra …
· 使用定理 `AddMonoidAlgebra.Monic.pow`：∀ {R : Type u_1} [inst : Semiring R] {A : Ty
pe u_8} {B : Type u_9} [inst_1 : AddMonoid A] [inst_2 : AddMonoid B]   [inst_3 :
 LinearOrder B] …
· 使用定理 `AddMonoidAlgebra.Monic.ne_zero`：∀ {R : Type u_1} {A : Type u_3} {B : Typ
e u_5} [inst : Semiring R] [inst_1 : LinearOrder B] [inst_2 : OrderBot B]   {p :
 AddMonoidAlgebra R …
· 使用定理 `succ_nsmul'`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M) (n : ℕ), (n +
 1) • a = a + n • a
-/
lemma Monic.supDegree_pow
    (hzero : D 0 = 0) (hadd : ∀ a1 a2, D (a1 + a2) = D a1 + D a2) (hD : D.Injective)
    [Nontrivial R] (hp : p.Monic D) :
    (p ^ n).supDegree D = n • p.supDegree D := by
  induction n with
  | zero => rw [pow_zero, zero_nsmul, one_def, supDegree_single 0 1, if_neg one_ne_zero, hzero]
  | succ n ih => rw [pow_succ', (hp.pow hadd hD).supDegree_mul_of_ne_zero_left hD hadd hp.ne_zero,
      ih, succ_nsmul']

end AddMonoid

end LinearOrder

section InfDegree

variable [SemilatticeInf T] [OrderTop T] (D : A → T)

/-- Let `R` be a semiring, let `A` be an `AddZeroClass`, let `T` be an `OrderTop`,
and let `D : A → T` be a "degree" function.
For an element `f : R[A]`, the element `infDegree f : T` is the infimum of all the elements in the
support of `f`, or `⊤` if `f` is zero.
Often, the Type `T` is `WithTop A`,
If, further, `A` has a linear order, then this notion coincides with the usual one,
using the minimum of the exponents. -/
/-
**AddMonoidAlgebra.infDegree** 是 Mathlib 中的一个缩写定义，位于命名空间 `AddMonoidAlgebra`。
形式化陈述：infDegree (f : R[A]) : T
参数：f : R[A]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a semiring, let `A` be an `AddZeroClass`, let `T` be an `OrderTop`,
and let `D : A → T` be a "degree" function.
For an element `f : R[A]`, the element `infDegree f : T` is the infimum of all t
he elements in the
support of `f`, or `⊤` if `f` is zero.
Often, the Type `T` is `WithTop A`,
If, further, `A` has a linear order, then this notion coincides with the usual o
ne,
using the minimum of the exponents.
-/
abbrev infDegree (f : R[A]) : T :=
  f.coeff.support.inf D
/-
**AddMonoidAlgebra.le_infDegree_add** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：le_infDegree_add (f g : R[A]) : (f.infDegree D) ⊓ (g.infDegree D) <= (f + 
g).infDegree D
参数：f g : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.le_inf_support_coeff_add`：le_inf_support_coeff_add : f.
coeff.support.inf degt ⊓ g.coeff.support.inf degt <= (f + g).coeff.support.inf d
egt
-/
theorem le_infDegree_add (f g : R[A]) :
    (f.infDegree D) ⊓ (g.infDegree D) ≤ (f + g).infDegree D :=
  le_inf_support_coeff_add D f g

variable {D} in
/-
**AddMonoidAlgebra.infDegree_withTop_some_comp** 是 Mathlib 中的一个定理，位于命名空间 `AddMon
oidAlgebra`。
形式化陈述：infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.suppo
rt.Nonempty) : infDegree (WithTop.some ∘ D) s = infDegree D s
参数：hs : s.coeff.support.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_inf'`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf 
α] {s : Finset β} (H : s.Nonempty) (f : β → α),   ↑(s.inf' H f) = s.inf (WithTop
.some…
· 使用定理 `Finset.inf'_eq_inf`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeI
nf α] [inst_1 : OrderTop α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.inf
' H f = …
-/
theorem infDegree_withTop_some_comp {s : AddMonoidAlgebra R A} (hs : s.coeff.support.Nonempty) :
    infDegree (WithTop.some ∘ D) s = infDegree D s := by
  unfold AddMonoidAlgebra.infDegree
  rw [← Finset.coe_inf' hs, Finset.inf'_eq_inf]
/-
**AddMonoidAlgebra.le_infDegree_mul** 是 Mathlib 中的一个定理，位于命名空间 `AddMonoidAlgebra`
。
形式化陈述：le_infDegree_mul [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
 (D : AddHom A T) (f g : R[A]) : f.infDegree D + g.infDegree D <= (f * g).infDeg
ree D
参数：D : AddHom A T；f g : R[A]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.le_inf_support_coeff_mul`：le_inf_support_coeff_mul {deg
t : A -> T} (degtm : forall a b, degt a + degt b <= degt (a + b)) (f g : R[A]) :
 f.coeff.support.inf degt + g.c…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddHom.addHomClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N], AddHomClass (M →ₙ+ N) M N
-/
theorem le_infDegree_mul [AddZeroClass A] [Add T] [AddLeftMono T] [AddRightMono T]
    (D : AddHom A T) (f g : R[A]) :
    f.infDegree D + g.infDegree D ≤ (f * g).infDegree D :=
  le_inf_support_coeff_mul (fun {a b : A} => (map_add D a b).ge) _ _

end InfDegree

end Degrees

end AddMonoidAlgebra

