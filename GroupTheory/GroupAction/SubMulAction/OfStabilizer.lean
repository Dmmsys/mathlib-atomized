/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.GroupTheory.GroupAction.Embedding
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fin.Tuple.Embedding

/-! # The SubMulAction of the stabilizer of a point on the complement of that point

When a group `G` acts on a type `α`, the stabilizer of a point `a : α`
acts naturally on the complement of that point.

Such actions
(as the similar one, `SubMulAction.ofFixingSubgroup`,
for the fixing subgroup of a set acting on the complement of that set)
are useful to study the multiple transitivity of the group `G`,
since `n`-transitivity of `G` on `α` is equivalent to `n - 1`-transitivity
of `MulAction.stabilizer G a` on the complement of `a`.

We define equivariant maps that relate various of these `SubMulAction`s
and permit to manipulate them in a relatively smooth way.

* `SubMulAction.ofStabilizer a` : the action of `stabilizer G a` on `{a}ᶜ`

* `SubMulAction.ENat_card_ofStabilizer_add_one_eq` and `SubMulAction.nat_card_ofStabilizer_eq`
  compute the cardinality of the `carrier` of that action.

Consider `a b : α` and `g : G` such that `hg : g • b = a`.

* `SubMulAction.ofStabilizer.conjMap hg` is the equivariant map
  from `SubMulAction.ofStabilizer G a` to `SubMulAction.ofStabilizer G b`.
* `SubMulAction.ofStabilizer.snoc` : given `x : Fin n ↪ ofStabilizer G a`,
  append `a` to obtain `y : Fin n.succ ↪ α`
-/

@[expose] public section

open scoped Pointwise

open MulAction Function.Embedding

namespace SubMulAction

variable (G : Type*) [Group G] {α : Type*} [MulAction G α]

/-- Action of the stabilizer of a point on the complement. -/
@[to_additive /-- Action of the stabilizer of a point on the complement. -/]
/-
**SubMulAction.ofStabilizer** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction`。
形式化陈述：ofStabilizer (a : α) : SubMulAction (stabilizer G a) α where carrier
参数：a : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Action of the stabilizer of a point on the complement.
-/
def ofStabilizer (a : α) : SubMulAction (stabilizer G a) α where
  carrier := {a}ᶜ
  smul_mem' g x := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [not_imp_not, smul_eq_iff_eq_inv_smul]
    intro hgx
    apply symm
    rw [hgx, ← smul_eq_iff_eq_inv_smul]
    exact g.prop

@[to_additive]
/-
**SubMulAction.ofStabilizer_carrier** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：ofStabilizer_carrier (a : α) : (ofStabilizer G a).carrier = {a}ᶜ
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofStabilizer_carrier (a : α) : (ofStabilizer G a).carrier = {a}ᶜ :=
  rfl

@[to_additive]
/-
**SubMulAction.mem_ofStabilizer_iff** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：mem_ofStabilizer_iff (a : α) {x : α} : x in ofStabilizer G a ↔ x != a
参数：a : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofStabilizer_iff (a : α) {x : α} : x ∈ ofStabilizer G a ↔ x ≠ a :=
  Iff.rfl

@[to_additive]
/-
**SubMulAction.notMem_val_image** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：notMem_val_image {a : α} (t : Set (ofStabilizer G a)) : a ∉ Subtype.val ''
 t
参数：t : Set (ofStabilizer G a)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem notMem_val_image {a : α} (t : Set (ofStabilizer G a)) :
    a ∉ Subtype.val '' t := by
  rintro ⟨b, hb⟩
  exact b.prop (by simp [hb])

@[to_additive]
/-
**SubMulAction.neq_of_mem_ofStabilizer** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction`。
形式化陈述：neq_of_mem_ofStabilizer (a : α) {x : ofStabilizer G a} : ↑x != a
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
theorem neq_of_mem_ofStabilizer (a : α) {x : ofStabilizer G a} : ↑x ≠ a :=
  x.prop

@[to_additive]
/-
**SubMulAction.ENat_card_ofStabilizer_add_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `SubM
ulAction`。
形式化陈述：ENat_card_ofStabilizer_add_one_eq (a : α) : ENat.card (ofStabilizer G a) +
 1 = ENat.card α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_sum_compl`：mk_sum_compl {α} (s : Set α) : #s + #(sᶜ : Set α)
 = #α
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `OrderRingHom.instRingHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : N
onAssocSemiring α] [inst_1 : Preorder α] [inst_2 : NonAssocSemiring β]   [inst_3
 : Preorder β], Rin…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma ENat_card_ofStabilizer_add_one_eq (a : α) :
    ENat.card (ofStabilizer G a) + 1 = ENat.card α := by
  dsimp only [ENat.card]
  rw [← Cardinal.mk_sum_compl {a}, map_add, add_comm, eq_comm]
  congr
  simp

@[to_additive]
/-
**SubMulAction.nat_card_ofStabilizer_add_one_eq** 是 Mathlib 中的一个引理，位于命名空间 `SubMu
lAction`。
形式化陈述：nat_card_ofStabilizer_add_one_eq [Finite α] (a : α) : Nat.card (ofStabiliz
er G a) + 1 = Nat.card α
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.subtype_card`：subtype_card {p : α -> Prop} (s : Finset α) (H : foral
l x : α, x in s ↔ p x) : Nat.card { x // p x } = Finset.card s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_compl_add_card`：Finset.card_compl_add_card [DecidableEq α] [
Fintype α] (s : Finset α) : #sᶜ + #s = Fintype.card α
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
-/
lemma nat_card_ofStabilizer_add_one_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) + 1 = Nat.card α := by
  classical
  let := Fintype.ofFinite α
  rw [Nat.subtype_card {a}ᶜ, ← Finset.card_singleton a, Finset.card_compl_add_card,
    Nat.card_eq_fintype_card]
  simp [mem_ofStabilizer_iff]

@[to_additive]
/-
**SubMulAction.nat_card_ofStabilizer_eq** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`
。
形式化陈述：nat_card_ofStabilizer_eq [Finite α] (a : α) : Nat.card (ofStabilizer G a) 
= Nat.card α - 1
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_sub_of_add_eq`：∀ {a b c : ℕ}, c + b = a → c = a - b
· 使用引理 `SubMulAction.nat_card_ofStabilizer_add_one_eq`：nat_card_ofStabilizer_add
_one_eq [Finite α] (a : α) : Nat.card (ofStabilizer G a) + 1 = Nat.card α
-/
lemma nat_card_ofStabilizer_eq [Finite α] (a : α) :
    Nat.card (ofStabilizer G a) = Nat.card α - 1 :=
  Nat.eq_sub_of_add_eq (nat_card_ofStabilizer_add_one_eq G a)

variable {G}

/-- Conjugation induces an equivariant map between the SubAddAction of
the stabilizer of a point and that of its translate. -/
/-
**SubMulAction._root_.SubAddAction.ofStabilizer.conjMap** 是 Mathlib 中的一个定义，位于命名空
间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation induces an equivariant map between the SubAddAction of
the stabilizer of a point and that of its translate.
-/
def _root_.SubAddAction.ofStabilizer.conjMap {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g : G} {a b : α} (hg : b = g +ᵥ a) :
    AddActionHom (AddAction.stabilizerEquivStabilizer hg)
      (SubAddAction.ofStabilizer G a) (SubAddAction.ofStabilizer G b) where
  toFun x := ⟨g +ᵥ x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_vadd' := fun ⟨k, hk⟩ x ↦ by
    simp [← SetLike.coe_eq_coe, AddAction.addSubgroup_vadd_def,
      AddAction.stabilizerEquivStabilizer_apply, ← vadd_assoc]

/-- Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate. -/
@[to_additive existing SubAddAction.ofStabilizer.conjMap]
/-
**SubMulAction.ofStabilizer.conjMap** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction.ofSt
abilizer`。
形式化陈述：{G : Type u_1} →   [inst : Group G] →     {α : Type u_2} →       [inst_1 :
 MulAction G α] →         {g : G} →           {a b : α} →             (hg : b = 
g • a) →               ↥(SubMulAction.ofStabilizer G a) →ₑ[⇑(MulAction.stabilize
rEquivStabilizer hg)]                 ↥(SubMulAction.ofStabilizer G b)
参数：hg : b = g • a；SubMulAction.ofStabilizer G a；MulAction.stabilizerEquivStabili
zer hg；SubMulAction.ofStabilizer G b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugation induces an equivariant map between the SubMulAction of
the stabilizer of a point and that of its translate.
-/
def ofStabilizer.conjMap {g : G} {a b : α} (hg : b = g • a) :
    MulActionHom (stabilizerEquivStabilizer hg) (ofStabilizer G a) (ofStabilizer G b) where
  toFun x := ⟨g • x.val, fun hy ↦ x.prop (by simpa [hg] using hy)⟩
  map_smul' := fun ⟨k, hk⟩ ↦ by
    simp [← SetLike.coe_eq_coe, subgroup_smul_def, stabilizerEquivStabilizer, ← smul_assoc]

variable {g h k : G} {a b c : α}
variable (hg : b = g • a) (hh : c = h • b) (hk : c = k • a)

@[to_additive]
/-
**SubMulAction.ofStabilizer.conjMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `SubMulActio
n.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g : G} {a b : α} (hg : b = g • a)   (x : ↥(SubMulAction.ofStabilizer G a)), ↑((
SubMulAction.ofStabilizer.conjMap hg) x) = g • ↑x
参数：hg : b = g • a；x : ↥(SubMulAction.ofStabilizer G a)；(SubMulAction.ofStabilize
r.conjMap hg) x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofStabilizer.conjMap_apply (x : ofStabilizer G a) :
    (conjMap hg x : α) = g • x := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**SubMulAction._root_.AddAction.stabilizerEquivStabilizer_compTriple** 是 Mathlib
 中的一个定理，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.AddAction.stabilizerEquivStabilizer_compTriple
    {G : Type*} [AddGroup G] {α : Type*} [AddAction G α]
    {g h k : G} {a b c : α} {hg : b = g +ᵥ a} {hh : c = h +ᵥ b} {hk : c = k +ᵥ a} (H : k = h + g) :
    CompTriple (AddAction.stabilizerEquivStabilizer hg)
      (AddAction.stabilizerEquivStabilizer hh) (AddAction.stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [AddAction.stabilizerEquivStabilizer, H, AddAut.addConj, ← add_assoc]

set_option backward.isDefEq.respectTransparency false in
variable {hg hh hk} in
@[to_additive existing]
/-
**SubMulAction._root_.MulAction.stabilizerEquivStabilizer_compTriple** 是 Mathlib
 中的一个定理，位于命名空间 `SubMulAction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAction.stabilizerEquivStabilizer_compTriple (H : k = h * g) :
    CompTriple (stabilizerEquivStabilizer hg)
      (stabilizerEquivStabilizer hh) (stabilizerEquivStabilizer hk) where
  comp_eq := by
    ext
    simp [stabilizerEquivStabilizer, H, MulAut.conj, ← mul_assoc]

variable {hg hh hk} in
@[to_additive]
/-
**SubMulAction.ofStabilizer.conjMap_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `SubMul
Action.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g h k : G} {a b c : α} {hg : b = g • a}   {hh : c = h • b} {hk : c = k • a},   
k = h * g →     ∀ (x : ↥(SubMulAction.ofStabilizer G a)),       (SubMulAction.of
Stabilizer.conjMap hh) ((SubMulAction.ofStabilizer.conjMap hg) x) =         (Sub
MulAction.ofStabilizer.conjMap hk) x
参数：x : ↥(SubMulAction.ofStabilizer G a)；SubMulAction.ofStabilizer.conjMap hh；(Su
bMulAction.ofStabilizer.conjMap hg) x；SubMulAction.ofStabilizer.conjMap hk。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofStabilizer.conjMap_comp_apply (H : k = h * g) (x : ofStabilizer G a) :
    conjMap hh (conjMap hg x) = conjMap hk x := by
  simp [← Subtype.coe_inj, conjMap_apply, H, mul_smul]

@[to_additive]
/-
**SubMulAction.ofStabilizer.conjMap_comp_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `Su
bMulAction.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g : G} {a b : α} (hg : b = g • a)   (x : ↥(SubMulAction.ofStabilizer G a)),   (
SubMulAction.ofStabilizer.conjMap ⋯) ((SubMulAction.ofStabilizer.conjMap hg) x) 
= x
参数：hg : b = g • a；x : ↥(SubMulAction.ofStabilizer G a)；SubMulAction.ofStabilizer
.conjMap ⋯；(SubMulAction.ofStabilizer.conjMap hg) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofStabilizer.conjMap_comp_inv_apply (x : ofStabilizer G a) :
    (conjMap (eq_inv_smul_iff.mpr hg.symm)) (conjMap hg x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
/-
**SubMulAction.ofStabilizer.inv_conjMap_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `Su
bMulAction.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g : G} {a b : α} (hg : b = g • a)   (x : ↥(SubMulAction.ofStabilizer G b)),   (
SubMulAction.ofStabilizer.conjMap hg) ((SubMulAction.ofStabilizer.conjMap ⋯) x) 
= x
参数：hg : b = g • a；x : ↥(SubMulAction.ofStabilizer G b)；SubMulAction.ofStabilizer
.conjMap hg；(SubMulAction.ofStabilizer.conjMap ⋯) x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofStabilizer.inv_conjMap_comp_apply (x : ofStabilizer G b) :
    conjMap hg (conjMap (eq_inv_smul_iff.mpr hg.symm) x) = x := by
  simp [← Subtype.coe_inj, conjMap_apply]

@[to_additive]
/-
**SubMulAction.ofStabilizer.conjMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction
.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g h k : G} {a b c : α} (hg : b = g • a)   (hh : c = h • b) (hk : c = k • a) (H 
: k = h * g),   (SubMulAction.ofStabilizer.conjMap hh).comp (SubMulAction.ofStab
ilizer.conjMap hg) =     SubMulAction.ofStabilizer.conjMap hk
参数：hg : b = g • a；hh : c = h • b；hk : c = k • a；H : k = h * g；SubMulAction.ofSta
bilizer.conjMap hh；SubMulAction.ofStabilizer.conjMap hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulActionHom.ext`：ext {f g : X ->ₑ[φ] Y} : (forall x, f x = g x) -> f = 
g
· 使用定理 `MulAction.stabilizerEquivStabilizer_compTriple`：∀ {G : Type u_1} [inst :
 Group G] {α : Type u_2} [inst_1 : MulAction G α] {g h k : G} {a b c : α} {hg : 
b = g • a}   {hh : c = h • b} {hk : …
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SubMulAction.ofStabilizer.conjMap_comp_apply`：∀ {G : Type u_1} [inst : G
roup G] {α : Type u_2} [inst_1 : MulAction G α] {g h k : G} {a b c : α} {hg : b 
= g • a}   {hh : c = h • b} {hk : …
-/
theorem ofStabilizer.conjMap_comp (H : k = h * g) :
    (conjMap hh).comp (conjMap hg) (κ := stabilizerEquivStabilizer_compTriple H) = conjMap hk := by
  ext x
  simpa using conjMap_comp_apply H x

@[to_additive]
/-
**SubMulAction.ofStabilizer.conjMap_bijective** 是 Mathlib 中的一个定理，位于命名空间 `SubMulA
ction.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{g : G} {a b : α} (hg : b = g • a),   Function.Bijective ⇑(SubMulAction.ofStabil
izer.conjMap hg)
参数：hg : b = g • a；SubMulAction.ofStabilizer.conjMap hg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.injective`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α] [i
nst_1 : MulAction α β] (g : α), Function.Injective fun x => g • x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubMulAction.ofStabilizer.conjMap_apply`：∀ {G : Type u_1} [inst : Group 
G] {α : Type u_2} [inst_1 : MulAction G α] {g : G} {a b : α} (hg : b = g • a)   
(x : ↥(SubMulAction.ofStabili…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_eq_coe`：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_inv_smul_iff`：∀ {G : Type u_3} {α : Type u_5} [inst : Group G] [inst_
1 : MulAction G α] {g : G} {a b : α}, a = g⁻¹ • b ↔ g • a = b
· 使用定理 `SubMulAction.ofStabilizer.inv_conjMap_comp_apply`：∀ {G : Type u_1} [inst
 : Group G] {α : Type u_2} [inst_1 : MulAction G α] {g : G} {a b : α} (hg : b = 
g • a)   (x : ↥(SubMulAction.ofStabili…
-/
theorem ofStabilizer.conjMap_bijective : Function.Bijective (conjMap hg) := by
  constructor
  · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    simp only [Subtype.mk_eq_mk]
    apply (MulAction.injective g)
    rwa [← SetLike.coe_eq_coe, conjMap_apply] at hxy
  · intro x
    exact ⟨conjMap _ x, inv_conjMap_comp_apply _ x⟩

/-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`. -/
@[to_additive
  /-- Append `a` to `x : Fin n ↪ ofStabilizer G a`  to get an element of `Fin n.succ ↪ α`. -/]
/-
**SubMulAction.ofStabilizer.snoc** 是 Mathlib 中的一个定义，位于命名空间 `SubMulAction.ofStabi
lizer`。
形式化陈述：{G : Type u_1} →   [inst : Group G] →     {α : Type u_2} →       [inst_1 :
 MulAction G α] → {a : α} → {n : ℕ} → (Fin n ↪ ↥(SubMulAction.ofStabilizer G a))
 → Fin n.succ ↪ α
参数：Fin n ↪ ↥(SubMulAction.ofStabilizer G a)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def ofStabilizer.snoc {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    Fin n.succ ↪ α :=
  Fin.Embedding.snoc (x.trans (subtype _)) (a := a) (by
    simp only [Set.mem_range, trans_apply, Function.Embedding.subtype_apply, not_exists]
    exact fun i ↦ (x i).prop)

@[to_additive]
/-
**SubMulAction.ofStabilizer.snoc_castSucc** 是 Mathlib 中的一个定理，位于命名空间 `SubMulActio
n.ofStabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{a : α} {n : ℕ}   (x : Fin n ↪ ↥(SubMulAction.ofStabilizer G a)) (i : Fin n), (S
ubMulAction.ofStabilizer.snoc x) i.castSucc = ↑(x i)
参数：x : Fin n ↪ ↥(SubMulAction.ofStabilizer G a)；i : Fin n；SubMulAction.ofStabili
zer.snoc x；x i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofStabilizer.snoc_castSucc {n : ℕ} (x : Fin n ↪ ofStabilizer G a) (i : Fin n) :
    snoc x i.castSucc = x i := by
  simp [snoc]

@[to_additive]
/-
**SubMulAction.ofStabilizer.snoc_last** 是 Mathlib 中的一个定理，位于命名空间 `SubMulAction.of
Stabilizer`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {α : Type u_2} [inst_1 : MulAction G α] 
{a : α} {n : ℕ}   (x : Fin n ↪ ↥(SubMulAction.ofStabilizer G a)), (SubMulAction.
ofStabilizer.snoc x) (Fin.last n) = a
参数：x : Fin n ↪ ↥(SubMulAction.ofStabilizer G a)；SubMulAction.ofStabilizer.snoc x
；Fin.last n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofStabilizer.snoc_last {n : ℕ} (x : Fin n ↪ ofStabilizer G a) :
    snoc x (Fin.last n) = a := by
  simp [snoc]

variable (G) in
@[to_additive]
/-
**SubMulAction.exists_smul_of_last_eq** 是 Mathlib 中的一个引理，位于命名空间 `SubMulAction`。
形式化陈述：exists_smul_of_last_eq [IsPretransitive G α] {n : Nat} (a : α) (x : Fin n.
succ ↪ α) : exists (g : G) (y : Fin n ↪ ofStabilizer G a), g • x = ofStabilizer.
snoc y
参数：a : α；x : Fin n.succ ↪ α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.Embedding.ext`：ext {α β} {f g : Embedding α β} (h : forall x, f
 x = g x) : f = g
· 使用定理 `Fin.eq_castSucc_or_eq_last`：eq_castSucc_or_eq_last {n : Nat} (i : Fin (n
 + 1)) : (exists j : Fin n, i = j.castSucc) ∨ i = last n
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Function.Embedding.trans_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sor
t u_3} (f : α ↪ β) (g : β ↪ γ) (a : α), (f.trans g) a = g (f a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Function.Embedding.codRestrict_apply`：codRestrict_apply {α β} (p) (f : α
 ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩
· 使用定理 `Fin.Embedding.snoc_last`：snoc_last {n : Nat} {x : Fin n ↪ α} {a : α} {ha
 : a ∉ range x} : snoc x ha (last n) = a
-/
lemma exists_smul_of_last_eq [IsPretransitive G α] {n : ℕ} (a : α) (x : Fin n.succ ↪ α) :
    ∃ (g : G) (y : Fin n ↪ ofStabilizer G a), g • x = ofStabilizer.snoc y := by
  obtain ⟨g, hgx⟩ := exists_smul_eq G (x (Fin.last n)) a
  have H : ∀ i, Fin.Embedding.init (g • x) i ∈ ofStabilizer G a := fun i ↦ by
    simp only [mem_ofStabilizer_iff,
      Nat.succ_eq_add_one, ← hgx, ← smul_apply, ne_eq]
    suffices Fin.Embedding.init (g • x) i = (g • x) i.castSucc by
      simp [this]
    simp [Fin.Embedding.init, Fin.init_def]
  use g, (Fin.Embedding.init (g • x)).codRestrict (ofStabilizer G a) H
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨i, rfl⟩ | ⟨rfl⟩
  · simpa [ofStabilizer.snoc] using!
      Subtype.ext_iff.mp <| Function.Embedding.codRestrict_apply _ _ H i
  · simpa only [smul_apply, ofStabilizer.snoc, Fin.Embedding.snoc_last]

end SubMulAction

section Pointwise

open MulAction Set

variable (G : Type*) [Group G] (α : Type*) [MulAction G α]

/-- The stabilizer of a set acts on that set. -/
@[to_additive /-- The stabilizer of a set acts on that set. -/]
/-
**_root_.SMul.ofStabilizer** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：_root_.SMul.ofStabilizer (s : Set α) : SMul (stabilizer G s) s where smul 
g x
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stabilizer of a set acts on that set.
-/
instance _root_.SMul.ofStabilizer (s : Set α) :
    SMul (stabilizer G s) s where
  smul g x := ⟨g • ↑x, by
    convert! Set.smul_mem_smul_set x.prop
    exact (mem_stabilizer_iff.mp g.prop).symm⟩

@[simp]
/-
**_root_.SMul.smul_stabilizer_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：_root_.SMul.smul_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
 ((g • x : ↥s) : α) = (g : G) • (x : α)
参数：s : Set α；g : stabilizer G s；x : s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SMul.smul_stabilizer_def (s : Set α) (g : stabilizer G s) (x : s) :
    ((g • x : ↥s) : α) = (g : G) • (x : α) :=
  rfl

/-- The stabilizer of a set acts on that set -/
@[to_additive /-- The stabilizer of a set acts on that set. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stabilizer of a set acts on that set
-/
instance (s : Set α) : MulAction (stabilizer G s) s where
  one_smul x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, OneMemClass.coe_one, one_smul]
  mul_smul g k x := by
    simp only [← Subtype.coe_inj, SMul.smul_stabilizer_def, Subgroup.coe_mul, mul_smul]
/-
**stabilizer_empty_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stabilizer_empty_eq_top : stabilizer G (∅ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_empty`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β] {a
 : α}, a • ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stabilizer_empty_eq_top :
    stabilizer G (∅ : Set α) = ⊤ := by
  aesop
/-
**stabilizer_univ_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stabilizer_univ_eq_top : stabilizer G (Set.univ : Set α) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.smul_set_univ`：smul_set_univ : a • (univ : Set β) = univ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem stabilizer_univ_eq_top :
    stabilizer G (Set.univ : Set α) = ⊤ := by
  aesop

/-- The stabilizer of the complement is the stabilizer of the set. -/
@[simp]
/-
**stabilizer_compl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stabilizer_compl {s : Set α} : stabilizer G sᶜ = stabilizer G s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.smul_set_compl`：smul_set_compl : a • sᶜ = (a • s)ᶜ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x

--- 原说明 ---
The stabilizer of the complement is the stabilizer of the set.
-/
theorem stabilizer_compl {s : Set α} :
    stabilizer G sᶜ = stabilizer G s := by
  have (s : Set α) : stabilizer G s ≤ stabilizer G (sᶜ) := by
    intro g h
    simp [Set.smul_set_compl, mem_stabilizer_iff.1 h]
  refine le_antisymm (le_of_le_of_eq (this _) ?_) (this _)
  rw [compl_compl]

end Pointwise

