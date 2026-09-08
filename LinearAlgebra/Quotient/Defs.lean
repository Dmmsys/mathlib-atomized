/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.Logic.Small.Basic

/-!
# Quotients by submodules

* If `p` is a submodule of `M`, `M ⧸ p` is the quotient of `M` with respect to `p`:
  that is, elements of `M` are identified if their difference is in `p`. This is itself a module.

## Main definitions

* `Submodule.Quotient.mk`: a function sending an element of `M` to `M ⧸ p`
* `Submodule.Quotient.module`: `M ⧸ p` is a module
* `Submodule.Quotient.mkQ`: a linear map sending an element of `M` to `M ⧸ p`
* `Submodule.quotEquivOfEq`: if `p` and `p'` are equal, their quotients are equivalent

-/

@[expose] public section

-- For most of this file we work over a noncommutative ring
section Ring

namespace Submodule

variable {R M : Type*} {r : R} {x y : M} [Ring R] [AddCommGroup M] [Module R M]
variable (p p' : Submodule R M)

open QuotientAddGroup

/-- The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be defeq to the `AddSubgroup`
version, where commutativity can't be assumed. -/
/-
**Submodule.quotientRel** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotientRel : Setoid M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation associated to a submodule `p`, defined by `x ≈ y` iff `
-x + y ∈ p`.

Note this is equivalent to `y - x ∈ p`, but defined this way to be defeq to the 
`AddSubgroup`
version, where commutativity can't be assumed.
-/
def quotientRel : Setoid M :=
  QuotientAddGroup.leftRel p.toAddSubgroup
/-
**Submodule.quotientRel_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.quotientRel.eq_1`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring
 R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M)
, p.quotientRel …
· 使用定理 `QuotientAddGroup.leftRel_apply`：∀ {α : Type u_1} [inst : AddGroup α] {s 
: AddSubgroup α} {x y : α}, (QuotientAddGroup.leftRel s) x y ↔ -x + y ∈ s
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
theorem quotientRel_def {x y : M} : p.quotientRel x y ↔ x - y ∈ p :=
  Iff.trans
    (by
      rw [quotientRel, leftRel_apply, sub_eq_add_neg, neg_add, neg_neg]
      rfl)
    neg_mem_iff

/-- The quotient of a module `M` by a submodule `p ⊆ M`. -/
/-
**Submodule.hasQuotient** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：hasQuotient : HasQuotient M (Submodule R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a module `M` by a submodule `p ⊆ M`.
-/
instance hasQuotient : HasQuotient M (Submodule R M) :=
  ⟨fun p => Quotient (quotientRel p)⟩

namespace Quotient
/-- Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`. -/
/-
**Submodule.Quotient.mk** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk {p : Submodule R M} : M -> M ⧸ p
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
Map associating to an element of `M` the corresponding element of `M/p`,
when `p` is a submodule of `M`.
-/
def mk {p : Submodule R M} : M → M ⧸ p :=
  Quotient.mk''
/-
**Submodule.Quotient.mk'_eq_mk'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {p : Submodule R M} (x : M), Quotient.mk' x = Sub
module.Quotient.mk x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
theorem mk'_eq_mk' {p : Submodule R M} (x : M) :
    @Quotient.mk' _ (quotientRel p) x = mk x :=
  rfl
/-
**Submodule.Quotient.mk''_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {p : Submodule R M} (x : M), Quotient.mk'' x = Su
bmodule.Quotient.mk x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem mk''_eq_mk {p : Submodule R M} (x : M) : (Quotient.mk'' x : M ⧸ p) = mk x :=
  rfl
/-
**Submodule.Quotient.quot_mk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient
`。
形式化陈述：quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_mk {p : Submodule R M} (x : M) : (Quot.mk _ x : M ⧸ p) = mk x :=
  rfl
/-
**Submodule.Quotient.quotientAddGroupMk_eq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le.Quotient`。
形式化陈述：quotientAddGroupMk_eq_mk {p : Submodule R M} (x : M) : (QuotientAddGroup.m
k x : M ⧸ p) = mk x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotientAddGroupMk_eq_mk {p : Submodule R M} (x : M) :
    (QuotientAddGroup.mk x : M ⧸ p) = mk x :=
  rfl
/-
**Submodule.Quotient.eq'** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   (p : Submodule R M) {x y : M}, Submodule.Quotient
.mk x = Submodule.Quotient.mk y ↔ -x + y ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuotientAddGroup.eq`：∀ {α : Type u_1} [inst : AddGroup α] {s : AddSubgro
up α} {a b : α}, ↑a = ↑b ↔ -a + b ∈ s
-/
protected theorem eq' {x y : M} : (mk x : M ⧸ p) = mk y ↔ -x + y ∈ p :=
  QuotientAddGroup.eq
/-
**Submodule.Quotient.eq** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   (p : Submodule R M) {x y : M}, Submodule.Quotient
.mk x = Submodule.Quotient.mk y ↔ x - y ∈ p
参数：p : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Submodule.Quotient.eq'`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x 
y : M}, Subm…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `QuotientAddGroup.leftRel_apply`：∀ {α : Type u_1} [inst : AddGroup α] {s 
: AddSubgroup α} {x y : α}, (QuotientAddGroup.leftRel s) x y ↔ -x + y ∈ s
· 使用定理 `Submodule.quotientRel_def`：quotientRel_def {x y : M} : p.quotientRel x y
 ↔ x - y in p
-/
protected theorem eq {x y : M} : (mk x : M ⧸ p) = mk y ↔ x - y ∈ p :=
  (Submodule.Quotient.eq' p).trans (leftRel_apply.symm.trans p.quotientRel_def)
/-
**Submodule.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M ⧸ p) where
  -- Use Quotient.mk'' instead of mk here because mk is not reducible.
  -- This would lead to non-defeq diamonds.
  -- See also the same comment at the One instance for Con.
  zero := Quotient.mk'' 0
/-
**Submodule.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ⧸ p) :=
  ⟨0⟩

@[simp]
/-
**Submodule.Quotient.mk_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_zero : mk 0 = (0 : M ⧸ p)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_zero : mk 0 = (0 : M ⧸ p) :=
  rfl

@[simp]
/-
**Submodule.Quotient.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `Submodule.Quotient.eq'`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x 
y : M}, Subm…
-/
theorem mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x ∈ p := by simpa using (Quotient.eq' p : mk x = 0 ↔ _)

section SMul

variable {S : Type*} [SMul S R] [SMul S M] [IsScalarTower S R M] (P : Submodule R M)

/-
**Submodule.Quotient.instSMul'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：instSMul' : SMul S (M ⧸ P)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
-/
instance instSMul' : SMul S (M ⧸ P) :=
  ⟨fun a =>
    Quotient.map' (a • ·) fun x y h =>
      leftRel_apply.mpr <| by simpa using Submodule.smul_mem P (a • (1 : R)) (leftRel_apply.mp h)⟩

/-- Shortcut to help the elaborator in the common case. -/
/-
**Submodule.Quotient.instSMul** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：instSMul : SMul R (M ⧸ P)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Shortcut to help the elaborator in the common case.
-/
instance instSMul : SMul R (M ⧸ P) :=
  Quotient.instSMul' P

@[simp]
/-
**Submodule.Quotient.mk_smul** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x
参数：r : S；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ p) = r • mk x :=
  rfl
/-
**Submodule.Quotient.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient
`。
形式化陈述：smulCommClass (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMu
lCommClass S T M] : SMulCommClass S T (M ⧸ P) where smul_comm _x _y
参数：T : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
-/
instance smulCommClass (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M]
    [SMulCommClass S T M] : SMulCommClass S T (M ⧸ P) where
  smul_comm _x _y := Quotient.ind' fun _z => congr_arg mk (smul_comm _ _ _)
/-
**Submodule.Quotient.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient
`。
形式化陈述：isScalarTower (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMu
l S T] [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P) where smul_assoc _x _y
参数：T : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
-/
instance isScalarTower (T : Type*) [SMul T R] [SMul T M] [IsScalarTower T R M] [SMul S T]
    [IsScalarTower S T M] : IsScalarTower S T (M ⧸ P) where
  smul_assoc _x _y := Quotient.ind' fun _z => congr_arg mk (smul_assoc _ _ _)
/-
**Submodule.Quotient.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotie
nt`。
形式化陈述：isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCe
ntralScalar S M] : IsCentralScalar S (M ⧸ P) where op_smul_eq_smul _x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.ind'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁ → Prop}
, (∀ (a : α), p (Quotient.mk'' a)) → ∀ (q : Quotient s₁), p q
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `IsCentralScalar.op_smul_eq_smul`：∀ {M : Type u_9} {α : Type u_10} {inst 
: SMul M α} {inst_1 : SMul Mᵐᵒᵖ α} [self : IsCentralScalar M α] (m : M) (a : α),
   MulOpposite.op m •…
-/
instance isCentralScalar [SMul Sᵐᵒᵖ R] [SMul Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M]
    [IsCentralScalar S M] : IsCentralScalar S (M ⧸ P) where
  op_smul_eq_smul _x := Quotient.ind' fun _z => congr_arg mk <| op_smul_eq_smul _ _

end SMul

/-
**Submodule.Quotient.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：addMonoid : AddMonoid (M ⧸ p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid (M ⧸ p) :=
  inferInstanceAs <| AddMonoid (M ⧸ p.toAddSubgroup)
/-
**Submodule.Quotient.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient
`。
形式化陈述：addCommMonoid : AddCommMonoid (M ⧸ p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (M ⧸ p) :=
  inferInstanceAs <| AddCommMonoid (M ⧸ p.toAddSubgroup)
/-
**Submodule.Quotient.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`
。
形式化陈述：addCommGroup : AddCommGroup (M ⧸ p)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup (M ⧸ p) :=
  inferInstanceAs <| AddCommGroup (M ⧸ p.toAddSubgroup)

@[simp]
/-
**Submodule.Quotient.mk_add** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_add : (mk (x + y) : M ⧸ p) = mk x + mk y :=
  rfl

@[simp]
/-
**Submodule.Quotient.mk_neg** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_neg : (mk (-x) : M ⧸ p) = -(mk x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_neg : (mk (-x) : M ⧸ p) = -(mk x) :=
  rfl

@[simp]
/-
**Submodule.Quotient.mk_sub** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y :=
  rfl

variable {p} in
@[simp]
/-
**Submodule.Quotient.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`。
形式化陈述：mk_out (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m
参数：m : M ⧸ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem mk_out (m : M ⧸ p) : Submodule.Quotient.mk (Quotient.out m) = m :=
  Quotient.out_eq m

protected nonrec lemma «forall» {P : M ⧸ p → Prop} : (∀ a, P a) ↔ ∀ a, P (mk a) := Quotient.forall

section Module

variable {S : Type*}

/-
**Submodule.Quotient.mulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M] (P 
: Submodule R M) : MulAction S (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction' [Monoid S] [SMul S R] [MulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : MulAction S (M ⧸ P) := fast_instance%
  Function.Surjective.mulAction mk Quot.mk_surjective <| Submodule.Quotient.mk_smul P
/-
**Submodule.Quotient.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：mulAction (P : Submodule R M) : MulAction R (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulAction (P : Submodule R M) : MulAction R (M ⧸ P) :=
  Quotient.mulAction' P
/-
**Submodule.Quotient.smulZeroClass'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotien
t`。
形式化陈述：smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : S
ubmodule R M) : SMulZeroClass S (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.mk_zero`：mk_zero : mk 0 = (0 : M ⧸ p)
-/
instance smulZeroClass' [SMul S R] [SMulZeroClass S M] [IsScalarTower S R M] (P : Submodule R M) :
    SMulZeroClass S (M ⧸ P) :=
  ZeroHom.smulZeroClass ⟨mk, mk_zero _⟩ <| Submodule.Quotient.mk_smul P
/-
**Submodule.Quotient.smulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient
`。
形式化陈述：smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance smulZeroClass (P : Submodule R M) : SMulZeroClass R (M ⧸ P) :=
  Quotient.smulZeroClass' P
/-
**Submodule.Quotient.distribSMul'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`
。
形式化陈述：distribSMul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submo
dule R M) : DistribSMul S (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul' [SMul S R] [DistribSMul S M] [IsScalarTower S R M] (P : Submodule R M) :
    DistribSMul S (M ⧸ P) := fast_instance%
  Function.Surjective.distribSMul { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)
/-
**Submodule.Quotient.distribSMul** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：distribSMul (P : Submodule R M) : DistribSMul R (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribSMul (P : Submodule R M) : DistribSMul R (M ⧸ P) :=
  Quotient.distribSMul' P
/-
**Submodule.Quotient.distribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quot
ient`。
形式化陈述：distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTo
wer S R M] (P : Submodule R M) : DistribMulAction S (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction' [Monoid S] [SMul S R] [DistribMulAction S M] [IsScalarTower S R M]
    (P : Submodule R M) : DistribMulAction S (M ⧸ P) := fast_instance%
  Function.Surjective.distribMulAction { toFun := mk, map_zero' := rfl, map_add' := fun _ _ => rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)
/-
**Submodule.Quotient.distribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quoti
ent`。
形式化陈述：distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance distribMulAction (P : Submodule R M) : DistribMulAction R (M ⧸ P) :=
  Quotient.distribMulAction' P
/-
**Submodule.Quotient.module'** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Su
bmodule R M) : Module S (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :
    Module S (M ⧸ P) := fast_instance%
  Function.Surjective.module _ { toFun := mk, map_zero' := by rfl, map_add' := fun _ _ => by rfl }
    Quot.mk_surjective (Submodule.Quotient.mk_smul P)
/-
**Submodule.Quotient.module** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
形式化陈述：module (P : Submodule R M) : Module R (M ⧸ P)
参数：P : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module (P : Submodule R M) : Module R (M ⧸ P) :=
  Quotient.module' P

end Module

@[elab_as_elim]
/-
**Submodule.Quotient.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient`
。
形式化陈述：induction_on {C : M ⧸ p -> Prop} (x : M ⧸ p) (H : forall z, C (Submodule.Q
uotient.mk z)) : C x
参数：x : M ⧸ p；H : forall z, C (Submodule.Quotient.mk z)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem induction_on {C : M ⧸ p → Prop} (x : M ⧸ p) (H : ∀ z, C (Submodule.Quotient.mk z)) :
    C x := Quotient.inductionOn' x H
/-
**Submodule.Quotient.mk_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Quotient
`。
形式化陈述：mk_surjective : Function.Surjective (@mk _ _ _ _ _ p)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_surjective : Function.Surjective (@mk _ _ _ _ _ p) := by
  rintro ⟨x⟩
  exact ⟨x, rfl⟩

universe u in
/-
**Submodule.Quotient.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule.Quotient`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {N : Submodule R M} [Small.{u} M] :
    Small.{u} (M ⧸ N) :=
  small_of_surjective (Submodule.Quotient.mk_surjective _)

end Quotient

section

variable {M₂ : Type*} [AddCommGroup M₂] [Module R M₂]

/-
**Submodule.quot_hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quot_hom_ext (f g : (M ⧸ p) ->ₗ[R] M₂) (h : forall x : M, f (Quotient.mk x
) = g (Quotient.mk x)) : f = g
参数：f g : (M ⧸ p) ->ₗ[R] M₂；h : forall x : M, f (Quotient.mk x) = g (Quotient.mk 
x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
-/
theorem quot_hom_ext (f g : (M ⧸ p) →ₗ[R] M₂) (h : ∀ x : M, f (Quotient.mk x) = g (Quotient.mk x)) :
    f = g :=
  LinearMap.ext fun x => Submodule.Quotient.induction_on _ x h

/-- The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map. -/
/-
**Submodule.mkQ** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：mkQ : M ->ₗ[R] M ⧸ p where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from a module `M` to the quotient of `M` by a submodule `p` as a linear 
map.
-/
def mkQ : M →ₗ[R] M ⧸ p where
  toFun := Quotient.mk
  map_add' := by simp
  map_smul' := by simp

@[simp]
/-
**Submodule.mkQ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkQ_apply (x : M) : p.mkQ x = Quotient.mk x :=
  rfl
/-
**Submodule.mkQ_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：mkQ_surjective : Function.Surjective p.mkQ
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkQ_surjective : Function.Surjective p.mkQ := by
  rintro ⟨x⟩; exact ⟨x, rfl⟩

end

variable {R₂ M₂ : Type*} [Ring R₂] [AddCommGroup M₂] [Module R₂ M₂] {τ₁₂ : R →+* R₂}

/-- Two `LinearMap`s from a quotient module are equal if their compositions with
`submodule.mkQ` are equal.

See note [partially-applied ext lemmas]. -/
@[ext high] -- Increase priority so this applies before `LinearMap.ext`
/-
**Submodule.linearMap_qext** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：linearMap_qext ⦃f g : M ⧸ p ->ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ
) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Submodule.Quotient.induction_on`：induction_on {C : M ⧸ p -> Prop} (x : M
 ⧸ p) (H : forall z, C (Submodule.Quotient.mk z)) : C x
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…

--- 原说明 ---
Two `LinearMap`s from a quotient module are equal if their compositions with
`submodule.mkQ` are equal.

See note [partially-applied ext lemmas].
-/
theorem linearMap_qext ⦃f g : M ⧸ p →ₛₗ[τ₁₂] M₂⦄ (h : f.comp p.mkQ = g.comp p.mkQ) : f = g :=
  LinearMap.ext fun x => Submodule.Quotient.induction_on _ x <| (LinearMap.congr_fun h :)

/-- Quotienting by equal submodules gives linearly equivalent quotients. -/
/-
**Submodule.quotEquivOfEq** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p'
参数：h : p = p'。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Quotienting by equal submodules gives linearly equivalent quotients.
-/
def quotEquivOfEq (h : p = p') : (M ⧸ p) ≃ₗ[R] M ⧸ p' :=
  { @Quotient.congr _ _ (quotientRel p) (quotientRel p') (Equiv.refl _) fun a b => by
      subst h
      rfl with
    map_add' := by
      rintro ⟨x⟩ ⟨y⟩
      rfl
    map_smul' := by
      rintro x ⟨y⟩
      rfl }

@[simp]
/-
**Submodule.quotEquivOfEq_mk** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：quotEquivOfEq_mk (h : p = p') (x : M) : Submodule.quotEquivOfEq p p' h (Su
bmodule.Quotient.mk x) = (Submodule.Quotient.mk x)
参数：h : p = p'；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quotEquivOfEq_mk (h : p = p') (x : M) :
    Submodule.quotEquivOfEq p p' h (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x) :=
  rfl

end Submodule

end Ring

