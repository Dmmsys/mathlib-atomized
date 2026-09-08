/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.GroupTheory.Coset.Defs

/-!
# Quotients of groups by normal subgroups

This file defines the group structure on the quotient by a normal subgroup.

## Main definitions

* `QuotientGroup.Quotient.Group`: the group structure on `G/N` given a normal subgroup `N` of `G`.
* `mk'`: the canonical group homomorphism `G →* G/N` given a normal subgroup `N` of `G`.
* `lift φ`: the group homomorphism `G/N →* H` given a group homomorphism `φ : G →* H` such that
  `N ⊆ ker φ`.
* `map f`: the group homomorphism `G/N →* H/M` given a group homomorphism `f : G →* H` such that
  `N ⊆ f⁻¹(M)`.

## Tags

quotient groups
-/

@[expose] public section

open Function
open scoped Pointwise

namespace QuotientGroup

variable {G H I M : Type*} [Group G] [Group H] [Monoid M] {N : Subgroup G}

/-
**QuotientGroup.leftRel_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Subgroup G}, QuotientGroup.leftRel 
N = ⊤ ↔ N = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Setoid.mk.congr_simp`：∀ {α : Sort u} (r r_1 : α → α → Prop) (e_r : r = r
_1) (iseqv : Equivalence r),   { r := r, iseqv := iseqv } = { r := r_1, iseqv :=
 ⋯ }
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_additive (attr := simp)] lemma leftRel_eq_top : leftRel N = ⊤ ↔ N = ⊤ := by
  simpa [leftRel, MulAction.orbitRel, funext_iff, MulAction.mem_orbit_iff,
    MulAction.subgroup_smul_def, ← eq_inv_mul_iff_mul_eq]
    using ⟨fun h ↦ by ext; simpa using h _ 1, fun h ↦ by simp [h]⟩
/-
**QuotientGroup.rightRel_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Subgroup G}, QuotientGroup.rightRel
 N = ⊤ ↔ N = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Setoid.mk.congr_simp`：∀ {α : Sort u} (r r_1 : α → α → Prop) (e_r : r = r
_1) (iseqv : Equivalence r),   { r := r, iseqv := iseqv } = { r := r_1, iseqv :=
 ⋯ }
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[to_additive (attr := simp)] lemma rightRel_eq_top : rightRel N = ⊤ ↔ N = ⊤ := by
  simpa [rightRel, MulAction.orbitRel, funext_iff, MulAction.mem_orbit_iff,
    MulAction.subgroup_smul_def, ← eq_mul_inv_iff_mul_eq]
    using ⟨fun h ↦ by ext; simpa using h _ 1, fun h ↦ by simp [h]⟩
/-
**QuotientGroup.subsingleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Subgroup G}, Subsingleton (G ⧸ N) ↔
 N = ⊤
参数：G ⧸ N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] protected lemma subsingleton_iff : Subsingleton (G ⧸ N) ↔ N = ⊤ := by
  simp [HasQuotient.Quotient]
/-
**QuotientGroup.nontrivial_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] {N : Subgroup G}, Nontrivial (G ⧸ N) ↔ N
 ≠ ⊤
参数：G ⧸ N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[to_additive (attr := simp)] protected lemma nontrivial_iff : Nontrivial (G ⧸ N) ↔ N ≠ ⊤ := by
  simp [← not_subsingleton_iff_nontrivial]

variable (N) [nN : N.Normal]

/-- The congruence relation generated by a normal subgroup. -/
@[to_additive /-- The additive congruence relation generated by a normal additive subgroup. -/]
/-
**QuotientGroup.con** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (N : Subgroup G) → [nN : N.Normal] → C
on G
参数：N : Subgroup G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The congruence relation generated by a normal subgroup.
-/
protected def con : Con G where
  toSetoid := leftRel N
  mul' := fun {a b c d} hab hcd => by
    rw [leftRel_eq] at hab hcd ⊢
    dsimp only
    calc
      c⁻¹ * (a⁻¹ * b) * c⁻¹⁻¹ * (c⁻¹ * d) ∈ N := N.mul_mem (nN.conj_mem _ hab _) hcd
      _ = (a * c)⁻¹ * (b * d) := by
        simp only [mul_inv_rev, mul_assoc, inv_mul_cancel_left]

@[to_additive]
/-
**QuotientGroup.Quotient.group** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup.Quotient
`。
形式化陈述：{G : Type u_1} → [inst : Group G] → (N : Subgroup G) → [nN : N.Normal] → G
roup (G ⧸ N)
参数：N : Subgroup G；G ⧸ N。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
instance Quotient.group : Group (G ⧸ N) :=
  inferInstanceAs <| Group (delta% QuotientGroup.con N).Quotient

/--
The congruence relation defined by the kernel of a group homomorphism is equal to its kernel
as a congruence relation.
-/
@[to_additive QuotientAddGroup.con_ker_eq_addConKer
/-- The additive congruence relation defined by the kernel of an additive group homomorphism is
equal to its kernel as an additive congruence relation. -/]
/-
**QuotientGroup.con_ker_eq_conKer** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：con_ker_eq_conKer (f : G ->* M) : QuotientGroup.con f.ker = Con.ker f
参数：f : G ->* M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.ext`：ext {c d : Con M} (H : forall x y, c x y ↔ d x y) : c = d
· 使用定理 `MonoidHom.normal_ker`：∀ {G : Type u_1} [inst : Group G] {M : Type u_7} [
inst_1 : MulOneClass M] (f : G →* M), f.ker.Normal
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.con.eq_1`：∀ {G : Type u_1} [inst : Group G] (N : Subgroup 
G) [nN : N.Normal],   QuotientGroup.con N = { toSetoid := QuotientGroup.leftRel 
N, mul' := ⋯…
· 使用定理 `Con.rel_mk`：rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b
· 使用定理 `Setoid.comm'`：comm' (s : Setoid α) {x y} : s x y ↔ s y x
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Con.ker_rel`：ker_rel (f : F) {x y} : ker f x y ↔ f x = f y
· 使用定理 `MonoidHom.eq_iff`：eq_iff (f : G ->* M) {x y : G} : f x = f y ↔ y⁻¹ * x i
n f.ker
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem con_ker_eq_conKer (f : G →* M) : QuotientGroup.con f.ker = Con.ker f := by
  ext
  rw [QuotientGroup.con, Con.rel_mk, Setoid.comm', leftRel_apply, Con.ker_rel, MonoidHom.eq_iff]

/-- The group homomorphism from `G` to `G/N`. -/
@[to_additive /-- The additive group homomorphism from `G` to `G/N`. -/]
/-
**QuotientGroup.mk'** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：mk' : G ->* G ⧸ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The group homomorphism from `G` to `G/N`.
-/
def mk' : G →* G ⧸ N :=
  MonoidHom.mk' QuotientGroup.mk fun _ _ => rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：coe_mk' : (mk' N : G -> G ⧸ N) = mk
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' : (mk' N : G → G ⧸ N) = mk :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk'_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal] (x : G)
, (QuotientGroup.mk' N) x = ↑x
参数：N : Subgroup G；x : G；QuotientGroup.mk' N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk'_apply (x : G) : mk' N x = x :=
  rfl

@[to_additive]
/-
**QuotientGroup.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal], Functi
on.Surjective ⇑(QuotientGroup.mk' N)
参数：N : Subgroup G；QuotientGroup.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
theorem mk'_surjective : Surjective <| mk' N :=
  @mk_surjective _ _ N

@[to_additive]
/-
**QuotientGroup.mk'_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal] {x y : 
G},   (QuotientGroup.mk' N) x = (QuotientGroup.mk' N) y ↔ ∃ z ∈ N, x * z = y
参数：N : Subgroup G；QuotientGroup.mk' N；QuotientGroup.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_eq_mk' {x y : G} : mk' N x = mk' N y ↔ ∃ z ∈ N, x * z = y :=
  QuotientGroup.eq.trans <| by
    simp only [← _root_.eq_inv_mul_iff_mul_eq, exists_eq_right]

/-- Two `MonoidHom`s from a quotient group are equal if their compositions with
`QuotientGroup.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[to_additive (attr := ext 1100) /-- Two `AddMonoidHom`s from an additive quotient group are equal
if their compositions with `AddQuotientGroup.mk'` are equal.

See note [partially-applied ext lemmas]. -/]
/-
**QuotientGroup.monoidHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：monoidHom_ext ⦃f g : G ⧸ N ->* M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : 
f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem monoidHom_ext ⦃f g : G ⧸ N →* M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  MonoidHom.ext fun x => QuotientGroup.induction_on x <| (DFunLike.congr_fun h :)

@[to_additive (attr := simp)]
/-
**QuotientGroup.eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：eq_one_iff {N : Subgroup G} [N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x in N
参数：x : G。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Subgroup.inv_mem_iff`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G)
 {x : G}, x⁻¹ ∈ H ↔ x ∈ H
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_one_iff {N : Subgroup G} [N.Normal] (x : G) : (x : G ⧸ N) = 1 ↔ x ∈ N := by
  refine QuotientGroup.eq.trans ?_
  rw [mul_one, Subgroup.inv_mem_iff]

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk'_comp_subtype** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal], (Quoti
entGroup.mk' N).comp N.subtype = 1
参数：N : Subgroup G；QuotientGroup.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
lemma mk'_comp_subtype : (mk' N).comp N.subtype = 1 := by ext; simp

set_option linter.docPrime false in
/-- Note: `range_mk'` is a lemma about the primed constructor `QuotientGroup.mk'`, not a
  modified version of some `range_mk`. -/
@[to_additive (attr := simp)]
/-
**QuotientGroup.range_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：range_mk' : (QuotientGroup.mk' N).range = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.range_eq_top`：range_eq_top {N} [Group N] {f : G ->* N} : f.ran
ge = (⊤ : Subgroup N) ↔ Function.Surjective f
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)

--- 原说明 ---
Note: `range_mk'` is a lemma about the primed constructor `QuotientGroup.mk'`, n
ot a
  modified version of some `range_mk`.
-/
theorem range_mk' : (QuotientGroup.mk' N).range = ⊤ :=
  MonoidHom.range_eq_top.mpr (mk'_surjective N)

@[to_additive]
/-
**QuotientGroup.ker_le_range_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：ker_le_range_iff [MulOneClass I] (f : G ->* H) [f.range.Normal] (g : H ->*
 I) : g.ker <= f.range ↔ (mk' f.range).comp g.ker.subtype = 1
参数：f : G ->* H；g : H ->* I。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem ker_le_range_iff [MulOneClass I] (f : G →* H) [f.range.Normal] (g : H →* I) :
    g.ker ≤ f.range ↔ (mk' f.range).comp g.ker.subtype = 1 :=
  ⟨fun h => MonoidHom.ext fun ⟨_, hx⟩ => (eq_one_iff _).mpr <| h hx,
    fun h x hx => (eq_one_iff _).mp <| by exact DFunLike.congr_fun h ⟨x, hx⟩⟩

@[to_additive (attr := simp)]
/-
**QuotientGroup.ker_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G ->* G ⧸ N) = N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
-/
theorem ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G →* G ⧸ N) = N :=
  Subgroup.ext eq_one_iff

@[to_additive]
/-
**QuotientGroup.eq_iff_div_mem** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：eq_iff_div_mem {N : Subgroup G} [nN : N.Normal] {x y : G} : (x : G ⧸ N) = 
y ↔ x / y in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `QuotientGroup.eq`：∀ {α : Type u_1} [inst : Group α] {s : Subgroup α} {a 
b : α}, ↑a = ↑b ↔ a⁻¹ * b ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.Normal.mem_comm_iff`：mem_comm_iff (nH : H.Normal) {a b : G} : a
 * b in H ↔ b * a in H
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem eq_iff_div_mem {N : Subgroup G} [nN : N.Normal] {x y : G} :
    (x : G ⧸ N) = y ↔ x / y ∈ N := by
  refine eq_comm.trans (QuotientGroup.eq.trans ?_)
  rw [nN.mem_comm_iff, div_eq_mul_inv]

-- for commutative groups we don't need normality assumption
@[to_additive]
/-
**QuotientGroup.Quotient.commGroup** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup.Quot
ient`。
形式化陈述：{G : Type u_5} → [inst : CommGroup G] → (N : Subgroup G) → CommGroup (G ⧸ 
N)
参数：N : Subgroup G；G ⧸ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.commGroup {G : Type*} [CommGroup G] (N : Subgroup G) : CommGroup (G ⧸ N) where
  mul_comm := fun a b => Quotient.inductionOn₂' a b fun a b => congr_arg mk (mul_comm a b)

local notation " Q" => G ⧸ N

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_one** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_one : ((1 : G) : Q) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_one : ((1 : G) : Q) = 1 :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_mul** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_mul (a b : G) : ((a * b : G) : Q) = a * b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mul (a b : G) : ((a * b : G) : Q) = a * b :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_inv** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_inv (a : G) : ((a⁻¹ : G) : Q) = (a : Q)⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_inv (a : G) : ((a⁻¹ : G) : Q) = (a : Q)⁻¹ :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_div** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_div (a b : G) : ((a / b : G) : Q) = a / b
参数：a b : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_div (a b : G) : ((a / b : G) : Q) = a / b :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_pow** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_pow (a : G) (n : Nat) : ((a ^ n : G) : Q) = (a : Q) ^ n
参数：a : G；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_pow (a : G) (n : ℕ) : ((a ^ n : G) : Q) = (a : Q) ^ n :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.mk_zpow** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：mk_zpow (a : G) (n : Int) : ((a ^ n : G) : Q) = (a : Q) ^ n
参数：a : G；n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zpow (a : G) (n : ℤ) : ((a ^ n : G) : Q) = (a : Q) ^ n :=
  rfl
/-
**QuotientGroup.map_mk'_self** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal], Subgro
up.map (QuotientGroup.mk' N) N = ⊥
参数：N : Subgroup G；QuotientGroup.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive (attr := simp)] lemma map_mk'_self : N.map (mk' N) = ⊥ := by aesop

/--
The subgroup defined by the class of `1` for a congruence relation on a group.
-/
@[to_additive
/-- The `AddSubgroup` defined by the class of `0` for an additive congruence relation
on an `AddGroup`. -/]
/-
**QuotientGroup._root_.Con.subgroup** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def _root_.Con.subgroup (c : Con G) : Subgroup G where
  carrier := { x | c x 1 }
  one_mem' := c.refl 1
  mul_mem' hx hy := by simpa using c.mul hx hy
  inv_mem' h := by simpa using c.inv h

@[to_additive (attr := simp)]
/-
**QuotientGroup._root_.Con.mem_subgroup_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuotientG
roup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Con.mem_subgroup_iff {c : Con G} {x : G} :
    x ∈ c.subgroup ↔ c x 1 := Iff.rfl

@[to_additive]
/-
**QuotientGroup.** 是 Mathlib 中的一个实例，位于命名空间 `QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (c : Con G) : c.subgroup.Normal :=
  ⟨fun x hx g ↦ by simpa using (c.mul (c.mul (c.refl g) hx) (c.refl g⁻¹))⟩

@[to_additive (attr := simp)]
/-
**QuotientGroup._root_.Con.subgroup_quotientGroupCon** 是 Mathlib 中的一个定理，位于命名空间 `
QuotientGroup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Con.subgroup_quotientGroupCon (H : Subgroup G) [H.Normal] :
    (QuotientGroup.con H).subgroup = H := by
  ext
  simp [QuotientGroup.con, leftRel_apply]

@[to_additive (attr := simp)]
/-
**QuotientGroup.con_subgroup** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：con_subgroup (c : Con G) : QuotientGroup.con c.subgroup = c
参数：c : Con G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.ext`：ext {c d : Con M} (H : forall x y, c x y ↔ d x y) : c = d
· 使用定理 `QuotientGroup.instNormalSubgroup`：∀ {G : Type u_1} [inst : Group G] (c :
 Con G), c.subgroup.Normal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuotientGroup.con.eq_1`：∀ {G : Type u_1} [inst : Group G] (N : Subgroup 
G) [nN : N.Normal],   QuotientGroup.con N = { toSetoid := QuotientGroup.leftRel 
N, mul' := ⋯…
· 使用定理 `Con.rel_mk`：rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b
· 使用定理 `QuotientGroup.leftRel_apply`：leftRel_apply {x y : α} : leftRel s x y ↔ x
⁻¹ * y in s
· 使用定理 `Con.mem_subgroup_iff`：∀ {G : Type u_1} [inst : Group G] {c : Con G} {x :
 G}, x ∈ c.subgroup ↔ c x 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `Con.refl`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x
· 使用定理 `Con.symm`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y : M}, c x y →
 c y x
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
theorem con_subgroup (c : Con G) :
    QuotientGroup.con c.subgroup = c := by
  ext x y
  rw [QuotientGroup.con, Con.rel_mk, leftRel_apply, Con.mem_subgroup_iff]
  exact ⟨fun h ↦ by simpa using c.mul (c.refl x) (c.symm h),
    fun h ↦ by simpa using c.mul (c.refl x⁻¹) (c.symm h)⟩

/--
The normal subgroups correspond to the congruence relations on a group.
-/
@[to_additive (attr := simps) AddSubgroup.orderIsoAddCon
/-- The normal subgroups correspond to the additive congruence relations on an `AddGroup`. -/]
/-
**QuotientGroup._root_.Subgroup.orderIsoCon** 是 Mathlib 中的一个定义，位于命名空间 `QuotientG
roup`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def _root_.Subgroup.orderIsoCon :
    { N : Subgroup G // N.Normal } ≃o Con G where
  toFun N := letI : N.val.Normal := N.prop; QuotientGroup.con N
  invFun c := ⟨c.subgroup, inferInstance⟩
  left_inv := fun ⟨N, _⟩ ↦ Subtype.mk_eq_mk.mpr (Con.subgroup_quotientGroupCon N)
  right_inv c := QuotientGroup.con_subgroup c
  map_rel_iff' := by
    simp only [QuotientGroup.con, Equiv.coe_fn_mk, Con.le_def, Con.rel_mk, leftRel_apply]
    refine ⟨fun h x _ ↦ ?_, fun hle _ _ h ↦ hle h⟩
    specialize @h 1 x
    simp_all

@[to_additive (attr := simp)]
/-
**QuotientGroup.con_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：con_le_iff {N M : Subgroup G} [N.Normal] [M.Normal] : QuotientGroup.con N 
<= QuotientGroup.con M ↔ N <= M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
lemma con_le_iff {N M : Subgroup G} [N.Normal] [M.Normal] :
    QuotientGroup.con N ≤ QuotientGroup.con M ↔ N ≤ M :=
  (Subgroup.orderIsoCon.map_rel_iff (a := ⟨N, inferInstance⟩) (b := ⟨M, inferInstance⟩))

@[to_additive (attr := gcongr)]
/-
**QuotientGroup.con_mono** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：con_mono {N M : Subgroup G} [hN : N.Normal] [hM : M.Normal] (h : N <= M) :
 QuotientGroup.con N <= QuotientGroup.con M
参数：h : N <= M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `QuotientGroup.con_le_iff`：con_le_iff {N M : Subgroup G} [N.Normal] [M.No
rmal] : QuotientGroup.con N <= QuotientGroup.con M ↔ N <= M
-/
lemma con_mono {N M : Subgroup G} [hN : N.Normal] [hM : M.Normal] (h : N ≤ M) :
    QuotientGroup.con N ≤ QuotientGroup.con M :=
  con_le_iff.mpr h

/-- A group homomorphism `φ : G →* M` with `N ⊆ ker(φ)` descends (i.e. `lift`s) to a
group homomorphism `G/N →* M`. -/
@[to_additive /-- An `AddGroup` homomorphism `φ : G →+ M` with `N ⊆ ker(φ)` descends (i.e. `lift`s)
to an `AddGroup` homomorphism `G/N →+ M`. -/]
/-
**QuotientGroup.lift** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：lift (φ : G ->* M) (HN : N <= φ.ker) : Q ->* M
参数：φ : G ->* M；HN : N <= φ.ker。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def lift (φ : G →* M) (HN : N ≤ φ.ker) : Q →* M :=
  (QuotientGroup.con N).lift φ <| con_ker_eq_conKer φ ▸ con_mono HN

@[to_additive (attr := simp)]
/-
**QuotientGroup.lift_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：lift_mk {φ : G ->* M} (HN : N <= φ.ker) (g : G) : lift N φ HN (g : Q) = φ 
g
参数：HN : N <= φ.ker；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) : lift N φ HN (g : Q) = φ g :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.lift_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：lift_mk' {φ : G ->* M} (HN : N <= φ.ker) (g : G) : lift N φ HN (mk g : Q) 
= φ g
参数：HN : N <= φ.ker；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk' {φ : G →* M} (HN : N ≤ φ.ker) (g : G) : lift N φ HN (mk g : Q) = φ g :=
  rfl
-- TODO: replace `mk` with `mk'`)

@[to_additive (attr := simp)]
/-
**QuotientGroup.lift_comp_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：lift_comp_mk' (φ : G ->* M) (HN : N <= φ.ker) : (QuotientGroup.lift N φ HN
).comp (QuotientGroup.mk' N) = φ
参数：φ : G ->* M；HN : N <= φ.ker。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_mk' (φ : G →* M) (HN : N ≤ φ.ker) :
    (QuotientGroup.lift N φ HN).comp (QuotientGroup.mk' N) = φ :=
  rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.lift_quot_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：lift_quot_mk {φ : G ->* M} (HN : N <= φ.ker) (g : G) : lift N φ HN (Quot.m
k _ g : Q) = φ g
参数：HN : N <= φ.ker；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_quot_mk {φ : G →* M} (HN : N ≤ φ.ker) (g : G) :
    lift N φ HN (Quot.mk _ g : Q) = φ g :=
  rfl

@[to_additive]
/-
**QuotientGroup.lift_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Quotien
tGroup`。
形式化陈述：lift_surjective_of_surjective (φ : G ->* M) (hφ : Function.Surjective φ) (
HN : N <= φ.ker) : Function.Surjective (QuotientGroup.lift N φ HN)
参数：φ : G ->* M；hφ : Function.Surjective φ；HN : N <= φ.ker。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.lift_surjective`：Quotient.lift_surjective {α β : Sort*} {s : Se
toid α} (f : α -> β) (h : forall (a b : α), a ≈ b -> f a = f b) (hf : Function.S
urjective f) :…
-/
theorem lift_surjective_of_surjective (φ : G →* M) (hφ : Function.Surjective φ) (HN : N ≤ φ.ker) :
    Function.Surjective (QuotientGroup.lift N φ HN) :=
  Quotient.lift_surjective _ _ hφ

@[to_additive]
/-
**QuotientGroup.ker_lift** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：ker_lift (φ : G ->* M) (HN : N <= φ.ker) : (QuotientGroup.lift N φ HN).ker
 = Subgroup.map (QuotientGroup.mk' N) φ.ker
参数：φ : G ->* M；HN : N <= φ.ker。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.lift_comp_mk'`：lift_comp_mk' (φ : G ->* M) (HN : N <= φ.ke
r) : (QuotientGroup.lift N φ HN).comp (QuotientGroup.mk' N) = φ
· 使用定理 `MonoidHom.comap_ker`：comap_ker {P : Type*} [MulOneClass P] (g : N ->* P)
 (f : G ->* N) : g.ker.comap f = (g.comp f).ker
· 使用定理 `Subgroup.map_comap_eq_self_of_surjective`：map_comap_eq_self_of_surjectiv
e {f : G ->* N} (h : Function.Surjective f) (H : Subgroup N) : map f (comap f H)
 = H
· 使用定理 `QuotientGroup.mk'_surjective`：∀ {G : Type u_1} [inst : Group G] (N : Sub
group G) [nN : N.Normal], Function.Surjective ⇑(QuotientGroup.mk' N)
-/
theorem ker_lift (φ : G →* M) (HN : N ≤ φ.ker) :
    (QuotientGroup.lift N φ HN).ker = Subgroup.map (QuotientGroup.mk' N) φ.ker := by
  rw [← congrArg MonoidHom.ker (lift_comp_mk' N φ HN), ← MonoidHom.comap_ker,
    Subgroup.map_comap_eq_self_of_surjective (mk'_surjective N)]

@[to_additive]
/-
**QuotientGroup.injective_lift_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：injective_lift_iff (φ : G ->* M) (HN : N <= φ.ker) : Function.Injective (Q
uotientGroup.lift N φ HN) ↔ N = φ.ker
参数：φ : G ->* M；HN : N <= φ.ker。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.ker_eq_bot_iff`：ker_eq_bot_iff (f : G ->* M) : f.ker = ⊥ ↔ Fun
ction.Injective f
· 使用定理 `QuotientGroup.ker_lift`：ker_lift (φ : G ->* M) (HN : N <= φ.ker) : (Quot
ientGroup.lift N φ HN).ker = Subgroup.map (QuotientGroup.mk' N) φ.ker
· 使用定理 `Subgroup.map_eq_bot_iff`：map_eq_bot_iff {f : G ->* N} : H.map f = ⊥ ↔ H 
<= f.ker
-/
lemma injective_lift_iff (φ : G →* M) (HN : N ≤ φ.ker) :
    Function.Injective (QuotientGroup.lift N φ HN) ↔ N = φ.ker := by
  rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_lift, Subgroup.map_eq_bot_iff]
  grind [QuotientGroup.ker_mk']

/-- A surjective group homomorphism `φ : G →* H` with `N = ker(φ)` descends (i.e. `lift`s) to a
group isomorphism `G/N ≃* H`. -/
@[to_additive /-- A surjective `AddGroup` homomorphism `φ : G →+ H` with `N = ker(φ)` descends
(i.e. `lift`s) to an `AddGroup` isomorphism `G/N ≃+ H`. -/]
/-
**QuotientGroup.liftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：liftEquiv {φ : G ->* H} (hφ : Function.Surjective φ) (HN : N = φ.ker) : G 
⧸ N ≃* H
参数：hφ : Function.Surjective φ；HN : N = φ.ker。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def liftEquiv {φ : G →* H} (hφ : Function.Surjective φ)
    (HN : N = φ.ker) : G ⧸ N ≃* H :=
  MulEquiv.ofBijective (QuotientGroup.lift N φ HN.le)
    ⟨by rw [← MonoidHom.ker_eq_bot_iff, ker_lift, ← HN, QuotientGroup.map_mk'_self],
      lift_surjective_of_surjective N φ hφ HN.le⟩

@[to_additive (attr := simp)]
/-
**QuotientGroup.liftEquiv_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：liftEquiv_coe {φ : G ->* H} (hφ : Function.Surjective φ) (HN : N = φ.ker) 
(g : G) : liftEquiv N hφ HN (g : Q) = φ g
参数：hφ : Function.Surjective φ；HN : N = φ.ker；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftEquiv_coe {φ : G →* H} (hφ : Function.Surjective φ) (HN : N = φ.ker) (g : G) :
    liftEquiv N hφ HN (g : Q) = φ g := rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.liftEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：liftEquiv_mk {φ : G ->* H} (hφ : Function.Surjective φ) (HN : N = φ.ker) (
g : G) : liftEquiv N hφ HN (mk g : Q) = φ g
参数：hφ : Function.Surjective φ；HN : N = φ.ker；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftEquiv_mk {φ : G →* H} (hφ : Function.Surjective φ) (HN : N = φ.ker) (g : G) :
    liftEquiv N hφ HN (mk g : Q) = φ g := rfl

/-- A group homomorphism `f : G →* H` induces a map `G/N →* H/M` if `N ⊆ f⁻¹(M)`. -/
@[to_additive
      /-- An `AddGroup` homomorphism `f : G →+ H` induces a map `G/N →+ H/M` if `N ⊆ f⁻¹(M)`. -/]
/-
**QuotientGroup.map** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：map (M : Subgroup H) [M.Normal] (f : G ->* H) (h : N <= M.comap f) : G ⧸ N
 ->* H ⧸ M
参数：M : Subgroup H；f : G ->* H；h : N <= M.comap f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def map (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) : G ⧸ N →* H ⧸ M := by
  refine QuotientGroup.lift N ((mk' M).comp f) ?_
  intro x hx
  refine QuotientGroup.eq.2 ?_
  rw [mul_one, Subgroup.inv_mem_iff]
  exact h hx

@[to_additive (attr := simp)]
/-
**QuotientGroup.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_mk (M : Subgroup H) [M.Normal] (f : G ->* H) (h : N <= M.comap f) (x :
 G) : map N M f h ↑x = ↑(f x)
参数：M : Subgroup H；f : G ->* H；h : N <= M.comap f；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h ↑x = ↑(f x) :=
  rfl

@[to_additive]
/-
**QuotientGroup.map_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_mk' (M : Subgroup H) [M.Normal] (f : G ->* H) (h : N <= M.comap f) (x 
: G) : map N M f h (mk' _ x) = ↑(f x)
参数：M : Subgroup H；f : G ->* H；h : N <= M.comap f；x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk' (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ M.comap f) (x : G) :
    map N M f h (mk' _ x) = ↑(f x) :=
  rfl

@[to_additive]
/-
**QuotientGroup.map_surjective_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Quotient
Group`。
形式化陈述：map_surjective_of_surjective (M : Subgroup H) [M.Normal] (f : G ->* H) (hf
 : Function.Surjective (mk ∘ f : G -> H ⧸ M)) (h : N <= M.comap f) : Function.Su
rjective (map N M f h)
参数：M : Subgroup H；f : G ->* H；hf : Function.Surjective (mk ∘ f : G -> H ⧸ M)；h :
 N <= M.comap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.lift_surjective_of_surjective`：lift_surjective_of_surjecti
ve (φ : G ->* M) (hφ : Function.Surjective φ) (HN : N <= φ.ker) : Function.Surje
ctive (QuotientGroup.lift N φ HN)
-/
theorem map_surjective_of_surjective (M : Subgroup H) [M.Normal] (f : G →* H)
    (hf : Function.Surjective (mk ∘ f : G → H ⧸ M)) (h : N ≤ M.comap f) :
    Function.Surjective (map N M f h) :=
  lift_surjective_of_surjective _ _ hf _

@[to_additive]
/-
**QuotientGroup.ker_map** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：ker_map (M : Subgroup H) [M.Normal] (f : G ->* H) (h : N <= Subgroup.comap
 f M) : (map N M f h).ker = Subgroup.map (mk' N) (M.comap f)
参数：M : Subgroup H；f : G ->* H；h : N <= Subgroup.comap f M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuotientGroup.ker_mk'`：ker_mk' : MonoidHom.ker (QuotientGroup.mk' N : G 
->* G ⧸ N) = N
· 使用定理 `QuotientGroup.ker_lift`：ker_lift (φ : G ->* M) (HN : N <= φ.ker) : (Quot
ientGroup.lift N φ HN).ker = Subgroup.map (QuotientGroup.mk' N) φ.ker
-/
theorem ker_map (M : Subgroup H) [M.Normal] (f : G →* H) (h : N ≤ Subgroup.comap f M) :
    (map N M f h).ker = Subgroup.map (mk' N) (M.comap f) := by
  simp_rw [← ker_mk' M, MonoidHom.comap_ker]
  exact QuotientGroup.ker_lift _ _ _

@[to_additive]
/-
**QuotientGroup.map_id_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_id_apply (h : N <= Subgroup.comap (MonoidHom.id _) N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
-/
theorem map_id_apply (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) (x) :
    map N N (MonoidHom.id _) h x = x :=
  induction_on x fun _x => rfl

@[to_additive (attr := simp)]
/-
**QuotientGroup.map_id** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_id (h : N <= Subgroup.comap (MonoidHom.id _) N
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `QuotientGroup.map_id_apply`：map_id_apply (h : N <= Subgroup.comap (Monoi
dHom.id _) N
-/
theorem map_id (h : N ≤ Subgroup.comap (MonoidHom.id _) N := (Subgroup.comap_id N).le) :
    map N N (MonoidHom.id _) h = MonoidHom.id _ :=
  MonoidHom.ext (map_id_apply N h)

@[to_additive (attr := simp)]
/-
**QuotientGroup.map_map** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal]
 [O.Normal] (f : G ->* H) (g : H ->* I) (hf : N <= Subgroup.comap f M) (hg : M <
= Subgroup.comap g O) (hgf : N <= Subgroup.comap (g.comp f) O
参数：M : Subgroup H；O : Subgroup I；f : G ->* H；g : H ->* I；hf : N <= Subgroup.coma
p f M；hg : M <= Subgroup.comap g O。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientGroup.induction_on`：induction_on {C : α ⧸ s -> Prop} (x : α ⧸ s)
 (H : forall z, C (QuotientGroup.mk z)) : C x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _)))
    (x : G ⧸ N) : map M O g hg (map N M f hf x) = map N O (g.comp f) hgf x := by
  refine induction_on x fun x => ?_
  simp only [map_mk, MonoidHom.comp_apply]

@[to_additive (attr := simp)]
/-
**QuotientGroup.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：map_comp_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.No
rmal] [O.Normal] (f : G ->* H) (g : H ->* I) (hf : N <= Subgroup.comap f M) (hg 
: M <= Subgroup.comap g O) (hgf : N <= Subgroup.comap (g.comp f) O
参数：M : Subgroup H；O : Subgroup I；f : G ->* H；g : H ->* I；hf : N <= Subgroup.coma
p f M；hg : M <= Subgroup.comap g O。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `QuotientGroup.map_map`：map_map {I : Type*} [Group I] (M : Subgroup H) (O
 : Subgroup I) [M.Normal] [O.Normal] (f : G ->* H) (g : H ->* I) (hf : N <= Subg
roup.comap …
-/
theorem map_comp_map {I : Type*} [Group I] (M : Subgroup H) (O : Subgroup I) [M.Normal] [O.Normal]
    (f : G →* H) (g : H →* I) (hf : N ≤ Subgroup.comap f M) (hg : M ≤ Subgroup.comap g O)
    (hgf : N ≤ Subgroup.comap (g.comp f) O :=
      hf.trans ((Subgroup.comap_mono hg).trans_eq (Subgroup.comap_comap _ _ _))) :
    (map M O g hg).comp (map N M f hf) = map N O (g.comp f) hgf :=
  MonoidHom.ext (map_map N M O f g hf hg hgf)

section Pointwise
open Set

/-
**QuotientGroup.image_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：∀ {G : Type u_1} [inst : Group G] (N : Subgroup G) [nN : N.Normal], Quotie
ntGroup.mk '' ↑N = 1
参数：N : Subgroup G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `QuotientGroup.map_mk'_self`：∀ {G : Type u_1} [inst : Group G] (N : Subgr
oup G) [nN : N.Normal], Subgroup.map (QuotientGroup.mk' N) N = ⊥
-/
@[to_additive (attr := simp)] lemma image_coe : ((↑) : G → Q) '' N = 1 :=
  congr_arg ((↑) : Subgroup Q → Set Q) <| map_mk'_self N

@[to_additive]
/-
**QuotientGroup.preimage_image_coe** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：preimage_image_coe (s : Set G) : ((↑) : G -> Q) ⁻¹' ((↑) '' s) = N * s
参数：s : Set G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QuotientGroup.eq_one_iff`：eq_one_iff {N : Subgroup G} [N.Normal] (x : G)
 : (x : G ⧸ N) = 1 ↔ x in N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_self'`：div_self' (a : G) : a / a = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `div_mul_cancel`：div_mul_cancel (a b : G) : a / b * b = a
· 使用定理 `RightCancelSemigroup.toIsRightCancelMul`：∀ {G : Type u} [self : RightCan
celSemigroup G], IsRightCancelMul G
-/
lemma preimage_image_coe (s : Set G) : ((↑) : G → Q) ⁻¹' ((↑) '' s) = N * s := by
  ext a
  constructor
  · rintro ⟨b, hb, h⟩
    refine ⟨a / b, (QuotientGroup.eq_one_iff _).1 ?_, b, hb, div_mul_cancel _ _⟩
    simp only [h, QuotientGroup.mk_div, div_self']
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨b, hb, ?_⟩
    simpa only [QuotientGroup.mk_mul, right_eq_mul, QuotientGroup.eq_one_iff]

@[to_additive]
/-
**QuotientGroup.image_coe_inj** 是 Mathlib 中的一个引理，位于命名空间 `QuotientGroup`。
形式化陈述：image_coe_inj {s t : Set G} : ((↑) : G -> Q) '' s = ((↑) : G -> Q) '' t ↔ 
↑N * s = N * t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Surjective.preimage_injective`：∀ {α : Type u_1} {β : Type u_2} 
{f : α → β}, Function.Surjective f → Function.Injective (Set.preimage f)
· 使用定理 `QuotientGroup.mk_surjective`：mk_surjective : Function.Surjective @mk _ _
 s
-/
lemma image_coe_inj {s t : Set G} : ((↑) : G → Q) '' s = ((↑) : G → Q) '' t ↔ ↑N * s = N * t := by
  simp_rw [← preimage_image_coe]
  exact QuotientGroup.mk_surjective.preimage_injective.eq_iff.symm

end Pointwise

section congr

variable (G' : Subgroup G) (H' : Subgroup H) [Subgroup.Normal G'] [Subgroup.Normal H']

/-- `QuotientGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
given that `e` maps `G` to `H`. -/
@[to_additive /-- `QuotientAddGroup.congr` lifts the isomorphism `e : G ≃ H` to `G ⧸ G' ≃ H ⧸ H'`,
given that `e` maps `G` to `H`. -/]
/-
**QuotientGroup.congr** 是 Mathlib 中的一个定义，位于命名空间 `QuotientGroup`。
形式化陈述：congr (e : G ≃* H) (he : G'.map e = H') : G ⧸ G' ≃* H ⧸ H'
参数：e : G ≃* H；he : G'.map e = H'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def congr (e : G ≃* H) (he : G'.map e = H') : G ⧸ G' ≃* H ⧸ H' :=
  { map G' H' e (he ▸ G'.le_comap_map (e : G →* H)) with
    toFun := map G' H' e (he ▸ G'.le_comap_map (e : G →* H))
    invFun := map H' G' e.symm (he ▸ (G'.map_equiv_eq_comap_symm e).le)
    left_inv := fun x => by
      rw [map_map G' H' G' e e.symm (he ▸ G'.le_comap_map (e : G →* H))
        (he ▸ (G'.map_equiv_eq_comap_symm e).le)]
      simp only [← MulEquiv.coe_monoidHom_trans, MulEquiv.self_trans_symm,
        MulEquiv.coe_monoidHom_refl, map_id_apply]
    right_inv := fun x => by
      rw [map_map H' G' H' e.symm e (he ▸ (G'.map_equiv_eq_comap_symm e).le)
        (he ▸ G'.le_comap_map (e : G →* H))]
      simp only [← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, map_id_apply] }

@[simp]
/-
**QuotientGroup.congr_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：congr_mk (e : G ≃* H) (he : G'.map ↑e = H') (x) : congr G' H' e he (mk x) 
= e x
参数：e : G ≃* H；he : G'.map ↑e = H'；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_mk (e : G ≃* H) (he : G'.map ↑e = H') (x) : congr G' H' e he (mk x) = e x :=
  rfl
/-
**QuotientGroup.congr_mk'** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：congr_mk' (e : G ≃* H) (he : G'.map ↑e = H') (x) : congr G' H' e he (mk' G
' x) = mk' H' (e x)
参数：e : G ≃* H；he : G'.map ↑e = H'；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_mk' (e : G ≃* H) (he : G'.map ↑e = H') (x) :
    congr G' H' e he (mk' G' x) = mk' H' (e x) :=
  rfl

@[simp]
/-
**QuotientGroup.congr_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：congr_apply (e : G ≃* H) (he : G'.map ↑e = H') (x : G) : congr G' H' e he 
x = mk' H' (e x)
参数：e : G ≃* H；he : G'.map ↑e = H'；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_apply (e : G ≃* H) (he : G'.map ↑e = H') (x : G) :
    congr G' H' e he x = mk' H' (e x) :=
  rfl

@[simp]
/-
**QuotientGroup.congr_refl** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：congr_refl (he : G'.map (MulEquiv.refl G : G ->* G) = G'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
-/
theorem congr_refl (he : G'.map (MulEquiv.refl G : G →* G) = G' := Subgroup.map_id G') :
    congr G' G' (MulEquiv.refl G) he = MulEquiv.refl (G ⧸ G') := by
  ext ⟨x⟩
  rfl

@[simp]
/-
**QuotientGroup.congr_symm** 是 Mathlib 中的一个定理，位于命名空间 `QuotientGroup`。
形式化陈述：congr_symm (e : G ≃* H) (he : G'.map ↑e = H') : (congr G' H' e he).symm = 
congr H' G' e.symm ((Subgroup.map_symm_eq_iff_map_eq _).mpr he)
参数：e : G ≃* H；he : G'.map ↑e = H'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem congr_symm (e : G ≃* H) (he : G'.map ↑e = H') :
    (congr G' H' e he).symm = congr H' G' e.symm ((Subgroup.map_symm_eq_iff_map_eq _).mpr he) :=
  rfl

end congr

end QuotientGroup

