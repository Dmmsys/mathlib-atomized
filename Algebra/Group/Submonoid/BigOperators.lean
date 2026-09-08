/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard,
Amelia Livingston, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Algebra.Group.Support
public import Mathlib.Data.Finset.NoncommProd

/-!
# Submonoids: membership criteria for products and sums

In this file we prove various facts about membership in a submonoid:

* `list_prod_mem`, `multiset_prod_mem`, `prod_mem`: if each element of a collection belongs
  to a multiplicative submonoid, then so does their product;
* `list_sum_mem`, `multiset_sum_mem`, `sum_mem`: if each element of a collection belongs
  to an additive submonoid, then so does their sum;

## Tags
submonoid, submonoids
-/

public section

-- We don't need ordered structures to establish basic membership facts for submonoids
assert_not_exists IsOrderedRing

variable {M A B : Type*}

section SubmonoidClass
variable [Monoid M] [SetLike B M] [SubmonoidClass B M] {x : M} {S : B}

namespace SubmonoidClass

@[to_additive (attr := norm_cast, simp)]
/-
**SubmonoidClass.coe_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod
参数：l : List S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem coe_list_prod (l : List S) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod (SubmonoidClass.subtype S : _ →* M) l

@[to_additive (attr := norm_cast, simp)]
/-
**SubmonoidClass.coe_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m
 : Multiset S) : (m.prod : M) = (m.map (↑)).prod
参数：m : Multiset S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
-/
theorem coe_multiset_prod {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  (SubmonoidClass.subtype S : _ →* M).map_multiset_prod m

@[to_additive (attr := norm_cast, simp)]
/-
**SubmonoidClass.coe_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `SubmonoidClass`。
形式化陈述：coe_finsetProd {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f 
: ι -> S) (s : Finset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M)
参数：f : ι -> S；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem coe_finsetProd {ι M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (f : ι → S)
    (s : Finset ι) : ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) :=
  map_prod (SubmonoidClass.subtype S) f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoidClass.coe_finset_sum := _root_.AddSubmonoidClass.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

end SubmonoidClass

open SubmonoidClass

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive /-- Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`. -/]
/-
**list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：list_prod_mem {l : List M} (hl : forall x in l, x in S) : l.prod in S
参数：hl : forall x in l, x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubmonoidClass.coe_list_prod`：coe_list_prod (l : List S) : (l.prod : M) 
= (l.map (↑)).prod
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S

--- 原说明 ---
Product of a list of elements in a submonoid is in the submonoid.
-/
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ S) : l.prod ∈ S := by
  lift l to List S using hl
  rw [← coe_list_prod]
  exact l.prod.coe_prop

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      /-- Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`. -/]
/-
**multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m
 : Multiset M) (hm : forall a in m, a in S) : m.prod in S
参数：m : Multiset M；hm : forall a in m, a in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SubmonoidClass.coe_multiset_prod`：coe_multiset_prod {M} [CommMonoid M] [
SetLike B M] [SubmonoidClass B M] (m : Multiset S) : (m.prod : M) = (m.map (↑)).
prod
· 使用定理 `Subtype.coe_prop`：coe_prop {S : Set α} (a : { a // a in S }) : ↑a in S
-/
theorem multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := by
  lift m to Multiset S using hm
  rw [← coe_multiset_prod]
  exact m.prod.coe_prop

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
submonoid. -/
@[to_additive
      /-- Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`. -/]
/-
**prod_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι 
: Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c in t, 
f c) in S
参数：h : forall c in t, f c in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem prod_mem {M : Type*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {ι : Type*}
    {t : Finset ι} {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S :=
  multiset_prod_mem (t.1.map f) fun _x hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

end SubmonoidClass

namespace Submonoid
section Monoid
variable [Monoid M] {x : M} (s : Submonoid M)

@[to_additive (attr := norm_cast)]
/-
**Submonoid.coe_list_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod
参数：l : List s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
-/
theorem coe_list_prod (l : List s) : (l.prod : M) = (l.map (↑)).prod :=
  map_list_prod s.subtype l

@[to_additive (attr := norm_cast)]
/-
**Submonoid.coe_multiset_prod** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) : 
(m.prod : M) = (m.map (↑)).prod
参数：S : Submonoid M；m : Multiset S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.map_multiset_prod`：∀ {M : Type u_5} {N : Type u_6} [inst : Com
mMonoid M] [inst_1 : CommMonoid N] (f : M →* N) (s : Multiset M),   f s.prod = (
Multiset.map (⇑f)…
-/
theorem coe_multiset_prod {M} [CommMonoid M] (S : Submonoid M) (m : Multiset S) :
    (m.prod : M) = (m.map (↑)).prod :=
  S.subtype.map_multiset_prod m

@[to_additive (attr := norm_cast)]
/-
**Submonoid.coe_finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：coe_finsetProd {ι M} [CommMonoid M] (S : Submonoid M) (f : ι -> S) (s : Fi
nset ι) : ↑(∏ i in s, f i) = (∏ i in s, f i : M)
参数：S : Submonoid M；f : ι -> S；s : Finset ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
-/
theorem coe_finsetProd {ι M} [CommMonoid M] (S : Submonoid M) (f : ι → S) (s : Finset ι) :
    ↑(∏ i ∈ s, f i) = (∏ i ∈ s, f i : M) :=
  map_prod S.subtype f s

@[deprecated (since := "2026-04-08")]
alias _root_.AddSubmonoid.coe_finset_sum := _root_.AddSubmonoid.coe_finsetSum

@[to_additive existing, deprecated (since := "2026-04-08")]
alias coe_finset_prod := coe_finsetProd

/-- Product of a list of elements in a submonoid is in the submonoid. -/
@[to_additive /-- Sum of a list of elements in an `AddSubmonoid` is in the `AddSubmonoid`. -/]
/-
**Submonoid.list_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：list_prod_mem {l : List M} (hl : forall x in l, x in s) : l.prod in s
参数：hl : forall x in l, x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l, x in S) :
 l.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M

--- 原说明 ---
Product of a list of elements in a submonoid is in the submonoid.
-/
theorem list_prod_mem {l : List M} (hl : ∀ x ∈ l, x ∈ s) : l.prod ∈ s := _root_.list_prod_mem hl

/-- Product of a multiset of elements in a submonoid of a `CommMonoid` is in the submonoid. -/
@[to_additive
      /-- Sum of a multiset of elements in an `AddSubmonoid` of an `AddCommMonoid` is
      in the `AddSubmonoid`. -/]
/-
**Submonoid.multiset_prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M) (h
m : forall a in m, a in S) : m.prod in S
参数：S : Submonoid M；m : Multiset M；hm : forall a in m, a in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] [SetLike B M] [S
ubmonoidClass B M] (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem multiset_prod_mem {M} [CommMonoid M] (S : Submonoid M) (m : Multiset M)
    (hm : ∀ a ∈ m, a ∈ S) : m.prod ∈ S := _root_.multiset_prod_mem m hm

@[to_additive]
/-
**Submonoid.multiset_noncommProd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : fo
rall x in m, x in S) : m.noncommProd comm in S
参数：S : Submonoid M；m : Multiset M；comm；h : forall x in m, x in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.noncommProd_coe`：noncommProd_coe (l : List α) (comm) : noncommP
rod (l : Multiset α) comm = l.prod
· 使用定理 `Submonoid.list_prod_mem`：list_prod_mem {l : List M} (hl : forall x in l,
 x in s) : l.prod in s
-/
theorem multiset_noncommProd_mem (S : Submonoid M) (m : Multiset M) (comm) (h : ∀ x ∈ m, x ∈ S) :
    m.noncommProd comm ∈ S := by
  induction m using Quotient.inductionOn with | h l => ?_
  simp only [Multiset.quot_mk_to_coe, Multiset.noncommProd_coe]
  exact Submonoid.list_prod_mem _ h

/-- Product of elements of a submonoid of a `CommMonoid` indexed by a `Finset` is in the
submonoid. -/
@[to_additive
      /-- Sum of elements in an `AddSubmonoid` of an `AddCommMonoid` indexed by a `Finset`
      is in the `AddSubmonoid`. -/]
/-
**Submonoid.prod_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Fin
set ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c in t, f c) in S
参数：S : Submonoid M；h : forall c in t, f c in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.multiset_prod_mem`：multiset_prod_mem {M} [CommMonoid M] (S : S
ubmonoid M) (m : Multiset M) (hm : forall a in m, a in S) : m.prod in S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M) {ι : Type*} {t : Finset ι}
    {f : ι → M} (h : ∀ c ∈ t, f c ∈ S) : (∏ c ∈ t, f c) ∈ S :=
  S.multiset_prod_mem (t.1.map f) fun _ hx =>
    let ⟨i, hi, hix⟩ := Multiset.mem_map.1 hx
    hix ▸ h i hi

@[to_additive]
/-
**Submonoid.noncommProd_mem** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι -> M) 
(comm) (h : forall c in t, f c in S) : t.noncommProd f comm in S
参数：S : Submonoid M；t : Finset ι；f : ι -> M；comm；h : forall c in t, f c in S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.multiset_noncommProd_mem`：multiset_noncommProd_mem (S : Submon
oid M) (m : Multiset M) (comm) (h : forall x in m, x in S) : m.noncommProd comm 
in S
· 使用定理 `Finset.noncommProd_lemma`：noncommProd_lemma (s : Finset α) (f : α -> β) 
(comm : (s : Set α).Pairwise (Commute on f)) : Set.Pairwise { x | x in Multiset.
map f s.val } …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
-/
theorem noncommProd_mem (S : Submonoid M) {ι : Type*} (t : Finset ι) (f : ι → M) (comm)
    (h : ∀ c ∈ t, f c ∈ S) : t.noncommProd f comm ∈ S := by
  apply multiset_noncommProd_mem
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

end Monoid

section CommMonoid
variable [CommMonoid M] {x : M}

@[to_additive]
/-
**Submonoid.mem_closure_iff_exists_finset_subset** 是 Mathlib 中的一个引理，位于命名空间 `Subm
onoid`。
形式化陈述：mem_closure_iff_exists_finset_subset {s : Set M} : x in closure s ↔ exists
 (f : M -> Nat) (t : Finset M), ↑t subseteq s ∧ f.support subseteq t ∧ ∏ a in t,
 a ^ f a = x where mp hx
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.closure_induction`：closure_induction {s : Set M} {motive : (x 
: M) -> x in closure s -> Prop} (mem : forall (x) (h : x in s), motive x (subset
_closure h)) (one…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Pi.support_single_of_ne`：∀ {ι : Type u_1} {M : Type u_3} [inst : Decidab
leEq ι] [inst_1 : Zero M] {i : ι} {a : M},   a ≠ 0 → Function.support (Pi.single
 i a) = {i}
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `pow_ite`：pow_ite (p : Prop) [Decidable p] (a : α) (b c : β) : a ^ (if p 
then b else c) = if p then a ^ b else a ^ c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.support_add`：∀ {α : Type u_1} {M : Type u_2} [inst : AddZeroCla
ss M] (f g : α → M),   (Function.support fun x => f x + g x) ⊆ Function.support 
f ∪ Functi…
· 使用定理 `Set.union_subset_union`：union_subset_union {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq s₂) (h₂ : t₁ subseteq t₂) : s₁ union t₁ subseteq s₂ union t₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
（共 44 条，此处仅展示前 30 条）
-/
lemma mem_closure_iff_exists_finset_subset {s : Set M} :
    x ∈ closure s ↔
      ∃ (f : M → ℕ) (t : Finset M), ↑t ⊆ s ∧ f.support ⊆ t ∧ ∏ a ∈ t, a ^ f a = x where
  mp hx := by
    classical
    induction hx using closure_induction with
    | one => exact ⟨0, ∅, by simp⟩
    | mem x hx =>
      exact ⟨Pi.single x 1, {x}, by simp [hx, Pi.single_apply]⟩
    | mul x y _ _ hx hy =>
    obtain ⟨f, t, hts, hf, rfl⟩ := hx
    obtain ⟨g, u, hus, hg, rfl⟩ := hy
    refine ⟨f + g, t ∪ u, mod_cast Set.union_subset hts hus,
      (Function.support_add _ _).trans <| mod_cast Set.union_subset_union hf hg, ?_⟩
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    congr 1 <;> symm
    · refine Finset.prod_subset Finset.subset_union_left ?_
      simp +contextual [Function.support_subset_iff'.1 hf]
    · refine Finset.prod_subset Finset.subset_union_right ?_
      simp +contextual [Function.support_subset_iff'.1 hg]
  mpr := by
    rintro ⟨n, t, hts, -, rfl⟩; exact prod_mem _ fun x hx ↦ pow_mem (subset_closure <| hts hx) _

@[to_additive]
/-
**Submonoid.mem_closure_finset** 是 Mathlib 中的一个引理，位于命名空间 `Submonoid`。
形式化陈述：mem_closure_finset {s : Finset M} : x in closure s ↔ exists f : M -> Nat, 
f.support subseteq s ∧ ∏ a in s, a ^ f a = x where mp
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submonoid.mem_closure_iff_exists_finset_subset`：mem_closure_iff_exists_f
inset_subset {s : Set M} : x in closure s ↔ exists (f : M -> Nat) (t : Finset M)
, ↑t subseteq s ∧ f.support subseteq…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_subset`：prod_subset (h : s₁ subseteq s₂) (hf : forall x in s
₂, x ∉ s₁ -> f x = 1) : ∏ x in s₁, f x = ∏ x in s₂, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.support_subset_iff'`：∀ {ι : Type u_1} {M : Type u_3} [inst : Ze
ro M] {f : ι → M} {s : Set ι}, Function.support f ⊆ s ↔ ∀ x ∉ s, f x = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Submonoid.prod_mem`：prod_mem {M : Type*} [CommMonoid M] (S : Submonoid M
) {ι : Type*} {t : Finset ι} {f : ι -> M} (h : forall c in t, f c in S) : (∏ c i
n t, f c…
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Submonoid.subset_closure`：subset_closure : s subseteq closure s
-/
lemma mem_closure_finset {s : Finset M} :
    x ∈ closure s ↔ ∃ f : M → ℕ, f.support ⊆ s ∧ ∏ a ∈ s, a ^ f a = x where
  mp := by
    rw [mem_closure_iff_exists_finset_subset]
    rintro ⟨f, t, hts, hf, rfl⟩
    refine ⟨f, hf.trans hts, .symm <| Finset.prod_subset hts ?_⟩
    simp +contextual [Function.support_subset_iff'.1 hf]
  mpr := by rintro ⟨n, -, rfl⟩; exact prod_mem _ fun x hx ↦ pow_mem (subset_closure hx) _

end CommMonoid
end Submonoid

