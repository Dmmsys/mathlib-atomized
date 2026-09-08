/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.Complement

/-!

## Pushouts of Monoids and Groups

This file defines wide pushouts of monoids and groups and proves some properties
of the amalgamated product of groups (i.e. the special case where all the maps
in the diagram are injective).

## Main definitions

- `Monoid.PushoutI`: the pushout of a diagram of monoids indexed by a type `ι`
- `Monoid.PushoutI.base`: the map from the amalgamating monoid to the pushout
- `Monoid.PushoutI.of`: the map from each Monoid in the family to the pushout
- `Monoid.PushoutI.lift`: the universal property used to define homomorphisms out of the pushout.

- `Monoid.PushoutI.NormalWord`: a normal form for words in the pushout
- `Monoid.PushoutI.of_injective`: if all the maps in the diagram are injective in a pushout of
  groups then so is `of`
- `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`: For any word `w` in the coproduct,
  if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
  `w` itself is not in the image of the base monoid.

## References

* The normal form theorem follows these [notes](https://webspace.maths.qmul.ac.uk/i.m.chiswell/ggt/lecture_notes/lecture2.pdf)
  from Queen Mary University

## Tags

amalgamated product, pushout, group

-/

@[expose] public section

namespace Monoid

open CoprodI Subgroup Coprod Function List

variable {ι : Type*} {G : ι → Type*} {H : Type*} {K : Type*} [Monoid K]

/-- The relation we quotient by to form the pushout -/
/-
**Monoid.PushoutI.con** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_2} →     {H : Type u_3} →       [inst :
 (i : ι) → Monoid (G i)] →         [inst_1 : Monoid H] → ((i : ι) → H →* G i) → 
Con (Monoid.Coprod (Monoid.CoprodI G) H)
参数：i : ι；G i；(i : ι) → H →* G i；Monoid.Coprod (Monoid.CoprodI G) H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation we quotient by to form the pushout
-/
def PushoutI.con [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) :
    Con (Coprod (CoprodI G) H) :=
  conGen (fun x y : Coprod (CoprodI G) H =>
    ∃ i x', x = inl (of (φ i x')) ∧ y = inr x')

/-- The indexed pushout of monoids, which is the pushout in the category of monoids,
or the category of groups. -/
/-
**Monoid.PushoutI** 是 Mathlib 中的一个定义，位于命名空间 `Monoid`。
形式化陈述：PushoutI [forall i, Monoid (G i)] [Monoid H] (φ : forall i, H ->* G i) : T
ype _
参数：G i；φ : forall i, H ->* G i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexed pushout of monoids, which is the pushout in the category of monoids,
or the category of groups.
-/
def PushoutI [∀ i, Monoid (G i)] [Monoid H] (φ : ∀ i, H →* G i) : Type _ :=
  (PushoutI.con φ).Quotient

namespace PushoutI

section Monoid

variable [∀ i, Monoid (G i)] [Monoid H] {φ : ∀ i, H →* G i}

/-
**Monoid.PushoutI.mul** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_2} →     {H : Type u_3} →       [inst :
 (i : ι) → Monoid (G i)] → [inst_1 : Monoid H] → {φ : (i : ι) → H →* G i} → Mul 
(Monoid.PushoutI φ)
参数：i : ι；G i；i : ι；Monoid.PushoutI φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance mul : Mul (PushoutI φ) := by
  delta PushoutI; infer_instance
/-
**Monoid.PushoutI.one** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_2} →     {H : Type u_3} →       [inst :
 (i : ι) → Monoid (G i)] → [inst_1 : Monoid H] → {φ : (i : ι) → H →* G i} → One 
(Monoid.PushoutI φ)
参数：i : ι；G i；i : ι；Monoid.PushoutI φ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance one : One (PushoutI φ) := by
  delta PushoutI; infer_instance
/-
**Monoid.PushoutI.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI`。
形式化陈述：monoid : Monoid (PushoutI φ)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid : Monoid (PushoutI φ) :=
  { Con.monoid _ with
    toMul := PushoutI.mul
    toOne := PushoutI.one }

/-- The map from each indexing group into the pushout -/
/-
**Monoid.PushoutI.of** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：of (i : ι) : G i ->* PushoutI φ
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from each indexing group into the pushout
-/
def of (i : ι) : G i →* PushoutI φ :=
  (Con.mk' _).comp <| inl.comp CoprodI.of

variable (φ) in
/-- The map from the base monoid into the pushout -/
/-
**Monoid.PushoutI.base** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：base : H ->* PushoutI φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the base monoid into the pushout
-/
def base : H →* PushoutI φ :=
  (Con.mk' _).comp inr
/-
**Monoid.PushoutI.of_comp_eq_base** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ)
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Con.eq`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {a b : M}, ↑a = ↑b ↔
 c a b
-/
theorem of_comp_eq_base (i : ι) : (of i).comp (φ i) = (base φ) := by
  ext x
  apply (Con.eq _).2
  refine ConGen.Rel.of _ _ ?_
  simp only [MonoidHom.comp_apply]
  exact ⟨_, _, rfl, rfl⟩

variable (φ) in
/-
**Monoid.PushoutI.of_apply_eq_base** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x
参数：i : ι；x : H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
· 使用定理 `Monoid.PushoutI.of_comp_eq_base`：of_comp_eq_base (i : ι) : (of i).comp (
φ i) = (base φ)
-/
theorem of_apply_eq_base (i : ι) (x : H) : of i (φ i x) = base φ x := by
  rw [← MonoidHom.comp_apply, of_comp_eq_base]

/-- Define a homomorphism out of the pushout of monoids by defining it on each object in the
diagram -/
/-
**Monoid.PushoutI.lift** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：lift (f : forall i, G i ->* K) (k : H ->* K) (hf : forall i, (f i).comp (φ
 i) = k) : PushoutI φ ->* K
参数：f : forall i, G i ->* K；k : H ->* K；hf : forall i, (f i).comp (φ i) = k。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a homomorphism out of the pushout of monoids by defining it on each objec
t in the
diagram
-/
def lift (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k) :
    PushoutI φ →* K :=
  Con.lift _ (Coprod.lift (CoprodI.lift f) k) <| by
    apply Con.conGen_le.2 fun x y => ?_
    rintro ⟨i, x', rfl, rfl⟩
    simp only [DFunLike.ext_iff, MonoidHom.coe_comp, comp_apply] at hf
    simp [hf]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Monoid.PushoutI.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：lift_of (f : forall i, G i ->* K) (k : H ->* K) (hf : forall i, (f i).comp
 (φ i) = k) {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g
参数：f : forall i, G i ->* K；k : H ->* K；hf : forall i, (f i).comp (φ i) = k；g : G
 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_of (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    {i : ι} (g : G i) : (lift f k hf) (of i g : PushoutI φ) = f i g := by
  delta PushoutI lift of
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe,
    lift_apply_inl, CoprodI.lift_of]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Monoid.PushoutI.lift_base** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：lift_base (f : forall i, G i ->* K) (k : H ->* K) (hf : forall i, (f i).co
mp (φ i) = k) (g : H) : (lift f k hf) (base φ g : PushoutI φ) = k g
参数：f : forall i, G i ->* K；k : H ->* K；hf : forall i, (f i).comp (φ i) = k；g : H
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_base (f : ∀ i, G i →* K) (k : H →* K)
    (hf : ∀ i, (f i).comp (φ i) = k)
    (g : H) : (lift f k hf) (base φ g : PushoutI φ) = k g := by
  delta PushoutI lift base
  simp only [MonoidHom.coe_comp, Con.coe_mk', comp_apply, Con.lift_coe, lift_apply_inr]

-- `ext` attribute should be lower priority than `hom_ext_nonempty`
@[ext 1199]
/-
**Monoid.PushoutI.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：hom_ext {f g : PushoutI φ ->* K} (h : forall i, f.comp (of i : G i ->* _) 
= g.comp (of i : G i ->* _)) (hbase : f.comp (base φ) = g.comp (base φ)) : f = g
参数：h : forall i, f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _)；hbase : f
.comp (base φ) = g.comp (base φ)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.cancel_right`：MonoidHom.cancel_right [MulOne M] [MulOne N] [Mu
lOne P] {g₁ g₂ : N ->* P} {f : M ->* N} (hf : Function.Surjective f) : g₁.comp f
 = g₂.comp f…
· 使用定理 `Con.mk'_surjective`：∀ {M : Type u_1} [inst : MulOneClass M] {c : Con M},
 Function.Surjective ⇑c.mk'
· 使用定理 `Monoid.Coprod.hom_ext`：hom_ext {f g : M ∗ N ->* P} (h₁ : f.comp inl = g.
comp inl) (h₂ : f.comp inr = g.comp inr) : f = g
· 使用定理 `Monoid.CoprodI.ext_hom`：ext_hom (f g : CoprodI M ->* N) (h : forall i, f
.comp (of : M i ->* _) = g.comp of) : f = g
-/
theorem hom_ext {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _))
    (hbase : f.comp (base φ) = g.comp (base φ)) : f = g :=
  (MonoidHom.cancel_right Con.mk'_surjective).mp <|
    Coprod.hom_ext
      (CoprodI.ext_hom _ _ h)
      hbase

@[ext high]
/-
**Monoid.PushoutI.hom_ext_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：hom_ext_nonempty [hn : Nonempty ι] {f g : PushoutI φ ->* K} (h : forall i,
 f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _)) : f = g
参数：h : forall i, f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.hom_ext`：hom_ext {f g : PushoutI φ ->* K} (h : forall i,
 f.comp (of i : G i ->* _) = g.comp (of i : G i ->* _)) (hbase : f.comp (base φ)
 = g.comp (ba…
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.PushoutI.of_comp_eq_base`：of_comp_eq_base (i : ι) : (of i).comp (
φ i) = (base φ)
· 使用定理 `MonoidHom.comp_assoc`：MonoidHom.comp_assoc {Q : Type*} [MulOne M] [MulOn
e N] [MulOne P] [MulOne Q] (f : M ->* N) (g : N ->* P) (h : P ->* Q) : (h.comp g
).comp f =…
-/
theorem hom_ext_nonempty [hn : Nonempty ι]
    {f g : PushoutI φ →* K}
    (h : ∀ i, f.comp (of i : G i →* _) = g.comp (of i : G i →* _)) : f = g :=
  hom_ext h <| by
    cases hn with
    | intro i =>
      ext
      rw [← of_comp_eq_base i, ← MonoidHom.comp_assoc, h, MonoidHom.comp_assoc]

/-- The equivalence that is part of the universal property of the pushout. A hom out of
the pushout is just a morphism out of all groups in the pushout that satisfies a commutativity
condition. -/
@[simps]
/-
**Monoid.PushoutI.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：homEquiv : (PushoutI φ ->* K) ≃ { f : (Π i, G i ->* K) × (H ->* K) // fora
ll i, (f.1 i).comp (φ i) = f.2 }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence that is part of the universal property of the pushout. A hom out
 of
the pushout is just a morphism out of all groups in the pushout that satisfies a
 commutativity
condition.
-/
def homEquiv :
    (PushoutI φ →* K) ≃ { f : (Π i, G i →* K) × (H →* K) // ∀ i, (f.1 i).comp (φ i) = f.2 } :=
  { toFun := fun f => ⟨(fun i => f.comp (of i), f.comp (base φ)),
      fun i => by rw [MonoidHom.comp_assoc, of_comp_eq_base]⟩
    invFun := fun f => lift f.1.1 f.1.2 f.2,
    left_inv := fun _ => hom_ext (by simp [DFunLike.ext_iff])
      (by simp [DFunLike.ext_iff])
    right_inv := fun ⟨⟨_, _⟩, _⟩ => by simp [DFunLike.ext_iff, funext_iff] }

/-- The map from the coproduct into the pushout -/
/-
**Monoid.PushoutI.ofCoprodI** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：ofCoprodI : CoprodI G ->* PushoutI φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map from the coproduct into the pushout
-/
def ofCoprodI : CoprodI G →* PushoutI φ :=
  CoprodI.lift of

@[simp]
/-
**Monoid.PushoutI.ofCoprodI_of** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：ofCoprodI_of (i : ι) (g : G i) : (ofCoprodI (CoprodI.of g) : PushoutI φ) =
 of i g
参数：i : ι；g : G i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.lift_of`：lift_of {N} [Monoid N] (fi : forall i, M i ->* N
) {i} (m : M i) : lift fi (of m) = fi i m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofCoprodI_of (i : ι) (g : G i) :
    (ofCoprodI (CoprodI.of g) : PushoutI φ) = of i g := by
  simp [ofCoprodI]
/-
**Monoid.PushoutI.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：induction_on {motive : PushoutI φ -> Prop} (x : PushoutI φ) (of : forall (
i : ι) (g : G i), motive (of i g)) (base : forall h, motive (base φ h)) (mul : f
orall x y, motive x -> motive y -> motive (x * y)) : motive x
参数：x : PushoutI φ；of : forall (i : ι) (g : G i), motive (of i g)；base : forall h
, motive (base φ h)；mul : forall x y, motive x -> motive y -> motive (x * y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.induction_on`：∀ {M : Type u_1} [inst : Mul M] {c : Con M} {C : c.Quo
tient → Prop} (q : c.Quotient), (∀ (x : M), C ↑x) → C q
· 使用定理 `Monoid.Coprod.induction_on`：induction_on {motive : M ∗ N -> Prop} (m : M
 ∗ N) (inl : forall m, motive (inl m)) (inr : forall n, motive (inr n)) (mul : f
orall x y, motiv…
· 使用定理 `Monoid.CoprodI.induction_on`：induction_on {motive : CoprodI M -> Prop} (
m : CoprodI M) (one : motive 1) (of : forall (i) (m : M i), motive (of m)) (mul 
: forall x y, mot…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem induction_on {motive : PushoutI φ → Prop}
    (x : PushoutI φ)
    (of : ∀ (i : ι) (g : G i), motive (of i g))
    (base : ∀ h, motive (base φ h))
    (mul : ∀ x y, motive x → motive y → motive (x * y)) : motive x := by
  delta PushoutI PushoutI.of PushoutI.base at *
  induction x using Con.induction_on with
  | H x =>
    induction x using Coprod.induction_on with
    | inl g =>
      induction g using CoprodI.induction_on with
      | of i g => exact of i g
      | mul x y ihx ihy =>
        rw [map_mul]
        exact mul _ _ ihx ihy
      | one => simpa using base 1
    | inr h => exact base h
    | mul x y ihx ihy => exact mul _ _ ihx ihy

end Monoid

variable [∀ i, Group (G i)] [Group H] {φ : ∀ i, H →* G i}

/-
**Monoid.PushoutI.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Group (PushoutI φ) :=
  { Con.group (PushoutI.con φ) with
    toMonoid := PushoutI.monoid }

namespace NormalWord

/-
In this section we show that there is a normal form for words in the amalgamated product. To have a
normal form, we need to pick canonical choice of element of each right coset of the base group. The
choice of element in the base group itself is `1`. Given a choice of element of each right coset,
given by the type `Transversal φ` we can find a normal form. The normal form for an element is an
element of the base group, multiplied by a word in the coproduct, where each letter in the word is
the canonical choice of element of its coset. We then show that all groups in the diagram act
faithfully on the normal form. This implies that the maps into the coproduct are injective.

We demonstrate the action is faithful using the equivalence `equivPair`. We show that `G i` acts
faithfully on `Pair d i` and that `Pair d i` is isomorphic to `NormalWord d`. Here, `d` is a
`Transversal`. A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element
of the group `G i`, the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1` Every letter in the `tail` must be in the transversal given by `d`.

We then show that the equivalence between `NormalWord` and `PushoutI`, between the set of normal
words and the elements of the amalgamated product. The key to this is the theorem `prod_smul_empty`,
which says that going from `NormalWord` to `PushoutI` and back is the identity. This is proven
by induction on the word using `consRecOn`.
-/

variable (φ)

/-- The data we need to pick a normal form for words in the pushout. We need to pick a
canonical element of each coset. We also need all the maps in the diagram to be injective -/
/-
**Monoid.PushoutI.NormalWord.Transversal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.Pus
houtI.NormalWord`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_2} →     {H : Type u_3} → [inst : (i : 
ι) → Group (G i)] → [inst_1 : Group H] → ((i : ι) → H →* G i) → Type (max u_1 u_
2)
参数：i : ι；G i；(i : ι) → H →* G i；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The data we need to pick a normal form for words in the pushout. We need to pick
 a
canonical element of each coset. We also need all the maps in the diagram to be 
injective
-/
structure Transversal : Type _ where
  /-- All maps in the diagram are injective -/
  injective : ∀ i, Injective (φ i)
  /-- The underlying set, containing exactly one element of each coset of the base group -/
  set : ∀ i, Set (G i)
  /-- The chosen element of the base group itself is the identity -/
  one_mem : ∀ i, 1 ∈ set i
  /-- We have exactly one element of each coset of the base group -/
  compl : ∀ i, IsComplement (φ i).range (set i)
/-
**Monoid.PushoutI.NormalWord.transversal_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Mon
oid.PushoutI.NormalWord`。
形式化陈述：transversal_nonempty (hφ : forall i, Injective (φ i)) : Nonempty (Transver
sal φ)
参数：hφ : forall i, Injective (φ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Subgroup.exists_isComplement_right`：exists_isComplement_right (H : Subgr
oup G) (g : G) : exists T, IsComplement H T ∧ g in T
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem transversal_nonempty (hφ : ∀ i, Injective (φ i)) : Nonempty (Transversal φ) := by
  choose t ht using fun i => (φ i).range.exists_isComplement_right 1
  apply Nonempty.intro
  exact
    { injective := hφ
      set := t
      one_mem := fun i => (ht i).2
      compl := fun i => (ht i).1 }

variable {φ}

/-- The normal form for words in the pushout. Every element of the pushout is the product of an
element of the base group and a word made up of letters each of which is in the transversal. -/
/-
**Monoid.PushoutI.NormalWord._root_.Monoid.PushoutI.NormalWord** 是 Mathlib 中的一个结
构，位于命名空间 `Monoid.PushoutI.NormalWord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The normal form for words in the pushout. Every element of the pushout is the pr
oduct of an
element of the base group and a word made up of letters each of which is in the 
transversal.
-/
structure _root_.Monoid.PushoutI.NormalWord (d : Transversal φ) extends CoprodI.Word G where
  /-- Every `NormalWord` is the product of an element of the base group and a word made up
  of letters each of which is in the transversal. `head` is that element of the base group. -/
  head : H
  /-- All letters in the word are in the transversal. -/
  normalized : ∀ i g, ⟨i, g⟩ ∈ toList → g ∈ d.set i

/--
A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element of the group `G i`,
the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1`. Every letter in the `tail` must be in the transversal given by `d`.
Similar to `Monoid.CoprodI.Pair` except every letter must be in the transversal
(not including the head letter). -/
/-
**Monoid.PushoutI.NormalWord.Pair** 是 Mathlib 中的一个归纳类型，位于命名空间 `Monoid.PushoutI.N
ormalWord`。
形式化陈述：{ι : Type u_1} →   {G : ι → Type u_2} →     {H : Type u_3} →       [inst :
 (i : ι) → Group (G i)] →         [inst_1 : Group H] →           {φ : (i : ι) → 
H →* G i} → Monoid.PushoutI.NormalWord.Transversal φ → ι → Type (max u_1 u_2)
参数：i : ι；G i；i : ι；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Pair d i` is a word in the coproduct, `Coprod G`, the `tail`, and an element 
of the group `G i`,
the `head`. The first letter of the `tail` must not be an element of `G i`.
Note that the `head` may be `1`. Every letter in the `tail` must be in the trans
versal given by `d`.
Similar to `Monoid.CoprodI.Pair` except every letter must be in the transversal
(not including the head letter).
-/
structure Pair (d : Transversal φ) (i : ι) extends CoprodI.Word.Pair G i where
  /-- All letters in the word are in the transversal. -/
  normalized : ∀ i g, ⟨i, g⟩ ∈ tail.toList → g ∈ d.set i

variable {d : Transversal φ}

/-- The empty normalized word, representing the identity element of the group. -/
@[simps!]
/-
**Monoid.PushoutI.NormalWord.empty** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI.No
rmalWord`。
形式化陈述：empty : NormalWord d
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The empty normalized word, representing the identity element of the group.
-/
def empty : NormalWord d := ⟨CoprodI.Word.empty, 1, fun i g => by simp [CoprodI.Word.empty]⟩
/-
**Monoid.PushoutI.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI.NormalW
ord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (NormalWord d) := ⟨NormalWord.empty⟩
/-
**Monoid.PushoutI.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI.NormalW
ord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : Inhabited (Pair d i) :=
  ⟨{ (empty : NormalWord d) with
      head := 1, tail := _,
      fstIdx_ne := fun h => by cases h }⟩

@[ext]
/-
**Monoid.PushoutI.NormalWord.ext** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI.Norm
alWord`。
形式化陈述：ext {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head) (hlist : w₁.toList 
= w₂.toList) : w₁ = w₂
参数：hhead : w₁.head = w₂.head；hlist : w₁.toList = w₂.toList。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Monoid.CoprodI.Word.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u_2} [
inst : (i : ι) → Monoid (M i)] (toList toList_1 : List ((i : ι) × M i))   (e_toL
ist : toList = toList_1…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.mk.congr_simp`：∀ {ι : Type u_1} {G : ι → Type
 u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i
 : ι) → H →* G i} {d : Monoid.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ext {w₁ w₂ : NormalWord d} (hhead : w₁.head = w₂.head)
    (hlist : w₁.toList = w₂.toList) : w₁ = w₂ := by
  rcases w₁ with ⟨⟨_, _, _⟩, _, _⟩
  rcases w₂ with ⟨⟨_, _, _⟩, _, _⟩
  simp_all

open Subgroup.IsComplement
/-
**Monoid.PushoutI.NormalWord.baseAction** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Pushou
tI.NormalWord`。
形式化陈述：baseAction : MulAction H (NormalWord d)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.normalized`：∀ {ι : Type u_1} {G : ι → Type u_
2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i : 
ι) → H →* G i} {d : Monoid.…
-/
instance baseAction : MulAction H (NormalWord d) :=
  { smul := fun h w => { w with head := h * w.head },
    one_smul := by simp +instances [instHSMul]
    mul_smul := by simp +instances [instHSMul, mul_assoc] }
/-
**Monoid.PushoutI.NormalWord.base_smul_def'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pu
shoutI.NormalWord`。
形式化陈述：base_smul_def' (h : H) (w : NormalWord d) : h • w = { w with head
参数：h : H；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem base_smul_def' (h : H) (w : NormalWord d) :
    h • w = { w with head := h * w.head } := rfl
/-- Take the product of a normal word as an element of the `PushoutI`. We show that this is
bijective, in `NormalWord.equiv`. -/
/-
**Monoid.PushoutI.NormalWord.prod** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI.Nor
malWord`。
形式化陈述：prod (w : NormalWord d) : PushoutI φ
参数：w : NormalWord d。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Take the product of a normal word as an element of the `PushoutI`. We show that 
this is
bijective, in `NormalWord.equiv`.
-/
def prod (w : NormalWord d) : PushoutI φ :=
  base φ w.head * ofCoprodI (w.toWord).prod

@[simp]
/-
**Monoid.PushoutI.NormalWord.prod_base_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pu
shoutI.NormalWord`。
形式化陈述：prod_base_smul (h : H) (w : NormalWord d) : (h • w).prod = base φ h * w.pr
od
参数：h : H；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_base_smul (h : H) (w : NormalWord d) :
    (h • w).prod = base φ h * w.prod := by
  simp only [base_smul_def', prod, map_mul, mul_assoc]

@[simp]
/-
**Monoid.PushoutI.NormalWord.prod_empty** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pushou
tI.NormalWord`。
形式化陈述：prod_empty : (empty : NormalWord d).prod = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_empty : (empty : NormalWord d).prod = 1 := by
  simp [prod, empty]

/-- A constructor that multiplies a `NormalWord` by an element, with condition to make
sure the underlying list does get longer. -/
@[simps!]
/-
**Monoid.PushoutI.NormalWord.cons** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI.Nor
malWord`。
形式化陈述：cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i) (hgr : g 
∉ (φ i).range) : NormalWord d
参数：g : G i；w : NormalWord d；hmw : w.fstIdx != some i；hgr : g ∉ (φ i).range。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…

--- 原说明 ---
A constructor that multiplies a `NormalWord` by an element, with condition to ma
ke
sure the underlying list does get longer.
-/
noncomputable def cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : NormalWord d :=
  letI n := (d.compl i).equiv (g * (φ i w.head))
  letI w' := Word.cons (n.2 : G i) w.toWord hmw
    (mt (coe_equiv_snd_eq_one_iff_mem _ (d.one_mem _)).1
      (mt (mul_mem_cancel_right (by simp)).1 hgr))
  { toWord := w'
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
      simp only [w', Word.cons, mem_cons, Sigma.mk.inj_iff] at hg
      rcases hg with ⟨rfl, hg | hg⟩
      · simp
      · exact w.normalized _ _ (by assumption) }

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Monoid.PushoutI.NormalWord.prod_cons** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pushout
I.NormalWord`。
形式化陈述：prod_cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some i) (hgr
 : g ∉ (φ i).range) : (cons g w hmw hgr).prod = of i g * w.prod
参数：g : G i；w : NormalWord d；hmw : w.fstIdx != some i；hgr : g ∉ (φ i).range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.PushoutI.of_apply_eq_base`：of_apply_eq_base (i : ι) (x : H) : of 
i (φ i x) = base φ x
· 使用定理 `MonoidHom.apply_ofInjective_symm`：apply_ofInjective_symm {f : G ->* N} (
hf : Function.Injective f) (x : f.range) : f ((ofInjective hf).symm x) = x
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Monoid.CoprodI.Word.prod_cons`：prod_cons (i) (m : M i) (w : Word M) (h1 
: m != 1) (h2 : w.fstIdx != some i) : prod (cons m w h2 h1) = of m * prod w
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Monoid.PushoutI.ofCoprodI_of`：ofCoprodI_of (i : ι) (g : G i) : (ofCoprod
I (CoprodI.of g) : PushoutI φ) = of i g
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_cons {i} (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : (cons g w hmw hgr).prod = of i g * w.prod := by
  simp [prod, cons, ← of_apply_eq_base φ i, equiv_fst_eq_mul_inv, mul_assoc]

variable [DecidableEq ι] [∀ i, DecidableEq (G i)]

set_option backward.isDefEq.respectTransparency.types false in
/-- Given a word in `CoprodI`, if every letter is in the transversal and when
we multiply by an element of the base group it still has this property,
then the element of the base group we multiplied by was one. -/
/-
**Monoid.PushoutI.NormalWord.eq_one_of_smul_normalized** 是 Mathlib 中的一个定理，位于命名空间
 `Monoid.PushoutI.NormalWord`。
形式化陈述：eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H) (hw : foral
l i g, ⟨i, g⟩ in w.toList -> g in d.set i) (hφw : forall j g, ⟨j, g⟩ in (CoprodI
.of (φ i h) • w).toList -> g in d.set j) : h = 1
参数：w : CoprodI.Word G；h : H；hw : forall i g, ⟨i, g⟩ in w.toList -> g in d.set i；
hφw : forall j g, ⟨j, g⟩ in (CoprodI.of (φ i h) • w).toList -> g in d.set j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Exists.fst`：∀ {b : Prop} {p : b → Prop}, Exists p → b
· 使用定理 `Exists.snd`：∀ {b : Prop} {p : b → Prop} (h : Exists p), p ⋯
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.equivPair_head`：equivPair_head {i : ι} {w : Word M} 
: (equivPair i w).head = if h : exists (h : w.toList != []), (w.toList.head h).1
 = i then h.snd ▸ (w.toL…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.equiv_snd_eq_self_iff_mem`：equiv_snd_eq_self_iff_m
em {g : G} (h1 : 1 in S) : ((hST.equiv g).snd : G) = g ↔ g in T
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
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.one_mem`：∀ {ι : Type u_1} {G : ι 
→ Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {
φ : (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Subgroup.IsComplement.equiv_one`：equiv_one (hs1 : 1 in S) (ht1 : 1 in T)
 : hST.equiv 1 = (⟨1, hs1⟩, ⟨1, ht1⟩)
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LeftCancelSemigroup.toIsLeftCancelMul`：∀ {G : Type u} [self : LeftCancel
Semigroup G], IsLeftCancelMul G
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Given a word in `CoprodI`, if every letter is in the transversal and when
we multiply by an element of the base group it still has this property,
then the element of the base group we multiplied by was one.
-/
theorem eq_one_of_smul_normalized (w : CoprodI.Word G) {i : ι} (h : H)
    (hw : ∀ i g, ⟨i, g⟩ ∈ w.toList → g ∈ d.set i)
    (hφw : ∀ j g, ⟨j, g⟩ ∈ (CoprodI.of (φ i h) • w).toList → g ∈ d.set j) :
    h = 1 := by
  simp only [← (d.compl _).equiv_snd_eq_self_iff_mem (one_mem _)] at hw hφw
  have hhead : ((d.compl i).equiv (Word.equivPair i w).head).2 =
      (Word.equivPair i w).head := by
    rw [Word.equivPair_head]
    split_ifs with h
    · rcases h with ⟨_, rfl⟩
      exact hw _ _ (List.head_mem _)
    · rw [equiv_one (d.compl i) (one_mem _) (d.one_mem _)]
  by_contra hh1
  have := hφw i (φ i h * (Word.equivPair i w).head) ?_
  · apply hh1
    rw [equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩, hhead] at this
    simpa [((injective_iff_map_eq_one' _).1 (d.injective i))] using this
  · simp only [Word.mem_smul_iff, not_true, false_and, ne_eq, Option.mem_def, mul_right_inj,
      exists_eq_right', mul_eq_left, exists_prop, true_and, false_or]
    constructor
    · intro h
      apply_fun (d.compl i).equiv at h
      simp only [Prod.ext_iff, equiv_one (d.compl i) (one_mem _) (d.one_mem _),
        equiv_mul_left_of_mem (d.compl i) ⟨_, rfl⟩, hhead, Subtype.ext_iff,
        Prod.ext_iff] at h
      rcases h with ⟨h₁, h₂⟩
      rw [h₂, coe_mul, ((d.compl i).coe_equiv_fst_eq_one_iff_mem (one_mem _)).mpr (d.one_mem _),
        mul_one, Subtype.coe_mk, map_eq_one_iff (φ i) (d.injective i)] at h₁
      contradiction
    · rw [Word.equivPair_head]
      dsimp
      split_ifs with hep
      · rcases hep with ⟨hnil, rfl⟩
        rw [head?_eq_some_head hnil]
        simp_all
      · push Not at hep
        by_cases hw : w.toList = []
        · simp [hw, Word.fstIdx]
        · simp [head?_eq_some_head hw, Word.fstIdx, hep hw]
/-
**Monoid.PushoutI.NormalWord.ext_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI
.NormalWord`。
形式化陈述：ext_smul {w₁ w₂ : NormalWord d} (i : ι) (h : CoprodI.of (φ i w₁.head) • w₁
.toWord = CoprodI.of (φ i w₂.head) • w₂.toWord) : w₁ = w₂
参数：i : ι；h : CoprodI.of (φ i w₁.head) • w₁.toWord = CoprodI.of (φ i w₂.head) • w
₂.toWord。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.eq_one_of_smul_normalized`：eq_one_of_smul_nor
malized (w : CoprodI.Word G) {i : ι} (h : H) (hw : forall i g, ⟨i, g⟩ in w.toLis
t -> g in d.set i) (hφw : forall j g, ⟨j, …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Monoid.PushoutI.NormalWord.mk.congr_simp`：∀ {ι : Type u_1} {G : ι → Type
 u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i
 : ι) → H →* G i} {d : Monoid.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `inv_mul_eq_one`：inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `smul_eq_iff_eq_inv_smul`：smul_eq_iff_eq_inv_smul (g : α) {x y : β} : g •
 x = y ↔ x = g⁻¹ • y
-/
theorem ext_smul {w₁ w₂ : NormalWord d} (i : ι)
    (h : CoprodI.of (φ i w₁.head) • w₁.toWord =
         CoprodI.of (φ i w₂.head) • w₂.toWord) :
    w₁ = w₂ := by
  rcases w₁ with ⟨w₁, h₁, hw₁⟩
  rcases w₂ with ⟨w₂, h₂, hw₂⟩
  dsimp at *
  rw [smul_eq_iff_eq_inv_smul, ← mul_smul] at h
  subst h
  simp only [← map_inv, ← map_mul] at hw₁
  have : h₁⁻¹ * h₂ = 1 := eq_one_of_smul_normalized w₂ (h₁⁻¹ * h₂) hw₂ hw₁
  rw [inv_mul_eq_one] at this; subst this
  simp

/-- Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, but
putting head into normal form first, by making sure it is expressed as an element
of the base group multiplied by an element of the transversal. -/
/-
**Monoid.PushoutI.NormalWord.rcons** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI.No
rmalWord`。
形式化陈述：rcons (i : ι) (p : Pair d i) : NormalWord d
参数：i : ι；p : Pair d i。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…

--- 原说明 ---
Given a pair `(head, tail)`, we can form a word by prepending `head` to `tail`, 
but
putting head into normal form first, by making sure it is expressed as an elemen
t
of the base group multiplied by an element of the transversal.
-/
noncomputable def rcons (i : ι) (p : Pair d i) : NormalWord d :=
  letI n := (d.compl i).equiv p.head
  let w := (Word.equivPair i).symm { p.toPair with head := n.2 }
  { toWord := w
    head := (MonoidHom.ofInjective (d.injective i)).symm n.1
    normalized := fun i g hg => by
        dsimp [w] at hg
        rw [Word.equivPair_symm, Word.mem_rcons_iff] at hg
        rcases hg with hg | ⟨_, rfl, rfl⟩
        · exact p.normalized _ _ hg
        · simp }
/-
**Monoid.PushoutI.NormalWord.rcons_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.P
ushoutI.NormalWord`。
形式化陈述：rcons_injective {i : ι} : Function.Injective (rcons (d
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Monoid.PushoutI.NormalWord.mk.injEq`：∀ {ι : Type u_1} {G : ι → Type u_2}
 {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i : ι)
 → H →* G i} {d : Monoid.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Monoid.CoprodI.Word.Pair.mk.injEq`：∀ {ι : Type u_1} {M : ι → Type u_2} [
inst : (i : ι) → Monoid (M i)] {i : ι} (head : M i) (tail : Monoid.CoprodI.Word 
M)   (fstIdx_ne : tail.…
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.mk.injEq`：∀ {ι : Type u_1} {G : ι → Type
 u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i
 : ι) → H →* G i} {d : Monoid.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.IsComplement.equiv_fst_mul_equiv_snd`：equiv_fst_mul_equiv_snd (
g : G) : ↑(hST.equiv g).fst * (hST.equiv g).snd = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem rcons_injective {i : ι} : Function.Injective (rcons (d := d) i) := by
  rintro ⟨⟨head₁, tail₁⟩, _⟩ ⟨⟨head₂, tail₂⟩, _⟩
  simp only [rcons, NormalWord.mk.injEq, EmbeddingLike.apply_eq_iff_eq,
    Word.Pair.mk.injEq, Pair.mk.injEq, and_imp]
  rintro h₁ rfl h₃
  rw [← equiv_fst_mul_equiv_snd (d.compl i) head₁,
      ← equiv_fst_mul_equiv_snd (d.compl i) head₂,
    h₁, h₃]
  simp

/-- The equivalence between `NormalWord`s and pairs. We can turn a `NormalWord` into a
pair by taking the head of the `List` if it is in `G i` and multiplying it by the element of the
base group. -/
/-
**Monoid.PushoutI.NormalWord.equivPair** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Pushout
I.NormalWord`。
形式化陈述：equivPair (i) : NormalWord d ≃ Pair d i
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `NormalWord`s and pairs. We can turn a `NormalWord` into
 a
pair by taking the head of the `List` if it is in `G i` and multiplying it by th
e element of the
base group.
-/
noncomputable def equivPair (i) : NormalWord d ≃ Pair d i :=
  letI toFun : NormalWord d → Pair d i :=
    fun w =>
      letI p := Word.equivPair i (CoprodI.of (φ i w.head) • w.toWord)
      { toPair := p
        normalized := fun j g hg => by
          dsimp only [p] at hg
          rw [Word.of_smul_def, ← Word.equivPair_symm, Equiv.apply_symm_apply] at hg
          dsimp at hg
          exact w.normalized _ _ (Word.mem_of_mem_equivPair_tail _ hg) }
  haveI leftInv : Function.LeftInverse (rcons i) toFun :=
    fun w => ext_smul i <| by
      simp only [toFun, rcons, Word.equivPair_symm,
        Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul,
        MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
        mul_smul, inv_smul_smul, smul_inv_smul]
  { toFun := toFun
    invFun := rcons i
    left_inv := leftInv
    right_inv := fun _ => rcons_injective (leftInv _) }
/-
**Monoid.PushoutI.NormalWord.summandAction** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Pus
houtI.NormalWord`。
形式化陈述：summandAction (i : ι) : MulAction (G i) (NormalWord d)
参数：i : ι。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.normalized`：∀ {ι : Type u_1} {G : ι → Ty
pe u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : 
(i : ι) → H →* G i} {d : Monoid.…
-/
noncomputable instance summandAction (i : ι) : MulAction (G i) (NormalWord d) :=
  { smul := fun g w => (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head }
    one_smul := fun _ => by
      dsimp +instances [instHSMul]
      rw [one_mul]
      exact (equivPair i).symm_apply_apply _
    mul_smul := fun _ _ _ => by
      dsimp +instances [instHSMul]
      simp [mul_assoc, Equiv.apply_symm_apply] }
/-
**Monoid.PushoutI.NormalWord.summand_smul_def'** 是 Mathlib 中的一个定理，位于命名空间 `Monoid
.PushoutI.NormalWord`。
形式化陈述：summand_smul_def' {i : ι} (g : G i) (w : NormalWord d) : g • w = (equivPai
r i).symm { equivPair i w with head
参数：g : G i；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem summand_smul_def' {i : ι} (g : G i) (w : NormalWord d) :
    g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl

set_option backward.isDefEq.respectTransparency false in
/-
**Monoid.PushoutI.NormalWord.mulAction** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.Pushout
I.NormalWord`。
形式化陈述：mulAction : MulAction (PushoutI φ) (NormalWord d)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance mulAction : MulAction (PushoutI φ) (NormalWord d) :=
  MulAction.ofEndHom <|
    lift
      (fun _ => MulAction.toEndHom)
      MulAction.toEndHom <| by
    intro i
    simp only [MulAction.toEndHom, DFunLike.ext_iff, MonoidHom.coe_comp, MonoidHom.coe_mk,
      OneHom.coe_mk, comp_apply]
    intro h
    funext w
    apply NormalWord.ext_smul i
    simp only [summand_smul_def', equivPair, rcons, Word.equivPair_symm, Equiv.coe_fn_mk,
      Equiv.coe_fn_symm_mk, Word.equivPair_smul_same, Word.equivPair_tail_eq_inv_smul,
      Word.rcons_eq_smul, equiv_fst_eq_mul_inv, map_mul, map_inv, mul_smul, inv_smul_smul,
      smul_inv_smul, base_smul_def', MonoidHom.apply_ofInjective_symm]
/-
**Monoid.PushoutI.NormalWord.base_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pus
houtI.NormalWord`。
形式化陈述：base_smul_def (h : H) (w : NormalWord d) : base φ h • w = { w with head
参数：h : H；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem base_smul_def (h : H) (w : NormalWord d) :
    base φ h • w = { w with head := h * w.head } := rfl
/-
**Monoid.PushoutI.NormalWord.summand_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.
PushoutI.NormalWord`。
形式化陈述：summand_smul_def {i : ι} (g : G i) (w : NormalWord d) : of (φ
参数：g : G i；w : NormalWord d。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem summand_smul_def {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = (equivPair i).symm
      { equivPair i w with
        head := g * (equivPair i w).head } := rfl
/-
**Monoid.PushoutI.NormalWord.of_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.P
ushoutI.NormalWord`。
形式化陈述：of_smul_eq_smul {i : ι} (g : G i) (w : NormalWord d) : of (φ
参数：g : G i；w : NormalWord d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.normalized`：∀ {ι : Type u_1} {G : ι → Ty
pe u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : 
(i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.summand_smul_def`：summand_smul_def {i : ι} (g
 : G i) (w : NormalWord d) : of (φ
· 使用定理 `Monoid.PushoutI.NormalWord.summand_smul_def'`：summand_smul_def' {i : ι} 
(g : G i) (w : NormalWord d) : g • w = (equivPair i).symm { equivPair i w with h
ead
-/
theorem of_smul_eq_smul {i : ι} (g : G i) (w : NormalWord d) :
    of (φ := φ) i g • w = g • w := by
  rw [summand_smul_def, summand_smul_def']
/-
**Monoid.PushoutI.NormalWord.base_smul_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid
.PushoutI.NormalWord`。
形式化陈述：base_smul_eq_smul (h : H) (w : NormalWord d) : base φ h • w = h • w
参数：h : H；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.normalized`：∀ {ι : Type u_1} {G : ι → Type u_
2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i : 
ι) → H →* G i} {d : Monoid.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.base_smul_def`：base_smul_def (h : H) (w : Nor
malWord d) : base φ h • w = { w with head
· 使用定理 `Monoid.PushoutI.NormalWord.base_smul_def'`：base_smul_def' (h : H) (w : N
ormalWord d) : h • w = { w with head
-/
theorem base_smul_eq_smul (h : H) (w : NormalWord d) :
    base φ h • w = h • w := by
  rw [base_smul_def, base_smul_def']

/-- Induction principle for `NormalWord`, that corresponds closely to inducting on
the underlying list. -/
@[elab_as_elim]
/-
**Monoid.PushoutI.NormalWord.consRecOn** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.Pushout
I.NormalWord`。
形式化陈述：consRecOn {motive : NormalWord d -> Sort _} (w : NormalWord d) (empty : mo
tive empty) (cons : forall (i : ι) (g : G i) (w : NormalWord d) (hmw : w.fstIdx 
!= some i) (_hgn : g in d.set i) (hgr : g ∉ (φ i).range) (_hw1 : w.head = 1), mo
tive w -> motive (cons g w hmw hgr)) (base : forall (h : H) (w : NormalWord d), 
w.head = 1 -> motive w -> motive (base φ h • w)) : motive w
参数：w : NormalWord d；empty : motive empty；cons : forall (i : ι) (g : G i) (w : No
rmalWord d) (hmw : w.fstIdx != some i) (_hgn : g in d.set i) (hgr : g ∉ (φ i).ra
nge) (_hw1 : w.head = 1), motive w -> motive (cons g w hmw hgr)；base : forall (h
 : H) (w : NormalWord d), w.head = 1 -> motive w -> motive (base φ h • w)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Induction principle for `NormalWord`, that corresponds closely to inducting on
the underlying list.
-/
noncomputable def consRecOn {motive : NormalWord d → Sort _} (w : NormalWord d)
    (empty : motive empty)
    (cons : ∀ (i : ι) (g : G i) (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
      (_hgn : g ∈ d.set i) (hgr : g ∉ (φ i).range) (_hw1 : w.head = 1),
      motive w → motive (cons g w hmw hgr))
    (base : ∀ (h : H) (w : NormalWord d), w.head = 1 → motive w → motive
      (base φ h • w)) : motive w := by
  rcases w with ⟨w, head, h3⟩
  convert! base head ⟨w, 1, h3⟩ rfl ?_
  · simp [base_smul_def]
  · induction w using Word.consRecOn with
    | empty => exact empty
    | cons i g w h1 hg1 ih =>
      convert!
        cons i g ⟨w, 1, fun _ _ h => h3 _ _ (List.mem_cons_of_mem _ h)⟩ h1
          (h3 _ _ List.mem_cons_self) ?_ rfl (ih ?_)
      · simp only [Word.cons, NormalWord.cons, map_one, mul_one,
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · apply d.injective i
        simp only [NormalWord.cons, equiv_fst_eq_mul_inv, MonoidHom.apply_ofInjective_symm,
          map_one, mul_one, mul_inv_cancel, (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]
      · rwa [← SetLike.mem_coe,
          ← coe_equiv_snd_eq_one_iff_mem (d.compl i) (d.one_mem _),
          (equiv_snd_eq_self_iff_mem (d.compl i) (one_mem _)).2
          (h3 _ _ List.mem_cons_self)]


set_option backward.isDefEq.respectTransparency false in
/-
**Monoid.PushoutI.NormalWord.cons_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Push
outI.NormalWord`。
形式化陈述：cons_eq_smul {i : ι} (g : G i) (w : NormalWord d) (hmw : w.fstIdx != some 
i) (hgr : g ∉ (φ i).range) : cons g w hmw hgr = of (φ
参数：g : G i；w : NormalWord d；hmw : w.fstIdx != some i；hgr : g ∉ (φ i).range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.ext_smul`：ext_smul {w₁ w₂ : NormalWord d} (i 
: ι) (h : CoprodI.of (φ i w₁.head) • w₁.toWord = CoprodI.of (φ i w₂.head) • w₂.t
oWord) : w₁ = w₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.CoprodI.Word.cons_eq_smul`：cons_eq_smul {i} {m : M i} {ls h1 h2} 
: cons m ls h1 h2 = of m • ls
· 使用定理 `Monoid.PushoutI.NormalWord.mk.congr_simp`：∀ {ι : Type u_1} {G : ι → Type
 u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i
 : ι) → H →* G i} {d : Monoid.…
· 使用定理 `MonoidHom.apply_ofInjective_symm`：apply_ofInjective_symm {f : G ->* N} (
hf : Function.Injective f) (x : f.range) : f ((ofInjective hf).symm x) = x
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `Monoid.CoprodI.Word.equivPair_tail_eq_inv_smul`：equivPair_tail_eq_inv_sm
ul {G : ι -> Type*} [forall i, Group (G i)] [forall i, DecidableEq (G i)] {i} (w
 : Word G) : (equivPair i w).tail = …
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.normalized`：∀ {ι : Type u_1} {G : ι → Ty
pe u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : 
(i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `Monoid.CoprodI.Word.Pair.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u
_2} [inst : (i : ι) → Monoid (M i)] {i : ι} (head head_1 : M i),   head = head_1
 →     ∀ (tail tail_1 : Mono…
· 使用定理 `Monoid.CoprodI.Word.rcons_eq_smul`：rcons_eq_smul {i} (p : Pair M i) : rc
ons p = of p.head • p.tail
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.mk.congr_simp`：∀ {ι : Type u_1} {G : ι →
 Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ
 : (i : ι) → H →* G i} {d : Monoid.…
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem cons_eq_smul {i : ι} (g : G i)
    (w : NormalWord d) (hmw : w.fstIdx ≠ some i)
    (hgr : g ∉ (φ i).range) : cons g w hmw hgr = of (φ := φ) i g • w := by
  apply ext_smul i
  simp only [cons, Word.cons_eq_smul, MonoidHom.apply_ofInjective_symm,
    equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv, mul_smul, inv_smul_smul, summand_smul_def,
    equivPair, rcons, Word.equivPair_symm, Word.rcons_eq_smul, Equiv.coe_fn_mk,
    Word.equivPair_tail_eq_inv_smul, Equiv.coe_fn_symm_mk, smul_inv_smul]

@[simp]
/-
**Monoid.PushoutI.NormalWord.prod_summand_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid
.PushoutI.NormalWord`。
形式化陈述：prod_summand_smul {i : ι} (g : G i) (w : NormalWord d) : (g • w).prod = of
 i g * w.prod
参数：g : G i；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.injective`：∀ {ι : Type u_1} {G : 
ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]  
 {φ : (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Monoid.CoprodI.Word.Pair.fstIdx_ne`：∀ {ι : Type u_1} {M : ι → Type u_2} 
[inst : (i : ι) → Monoid (M i)] {i : ι} (self : Monoid.CoprodI.Word.Pair M i),  
 self.tail.fstIdx ≠ some…
· 使用定理 `Monoid.CoprodI.Word.equivPair_tail_eq_inv_smul`：equivPair_tail_eq_inv_sm
ul {G : ι -> Type*} [forall i, Group (G i)] [forall i, DecidableEq (G i)] {i} (w
 : Word G) : (equivPair i w).tail = …
· 使用定理 `Monoid.CoprodI.Word.equivPair_smul_same`：equivPair_smul_same {i} (m : M 
i) (w : Word M) : equivPair i (of m • w) = ⟨m * (equivPair i w).head, (equivPair
 i w).tail, (equivPair i w).f…
· 使用定理 `Monoid.CoprodI.Word.Pair.mk.congr_simp`：∀ {ι : Type u_1} {M : ι → Type u
_2} [inst : (i : ι) → Monoid (M i)] {i : ι} (head head_1 : M i),   head = head_1
 →     ∀ (tail tail_1 : Mono…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.mk.congr_simp`：∀ {ι : Type u_1} {G : ι →
 Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ
 : (i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Monoid.PushoutI.NormalWord.Pair.normalized`：∀ {ι : Type u_1} {G : ι → Ty
pe u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : 
(i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `Monoid.CoprodI.Word.rcons_eq_smul`：rcons_eq_smul {i} (p : Pair M i) : rc
ons p = of p.head • p.tail
· 使用定理 `Monoid.PushoutI.NormalWord.mk.congr_simp`：∀ {ι : Type u_1} {G : ι → Type
 u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i
 : ι) → H →* G i} {d : Monoid.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.PushoutI.of_apply_eq_base`：of_apply_eq_base (i : ι) (x : H) : of 
i (φ i x) = base φ x
· 使用定理 `MonoidHom.apply_ofInjective_symm`：apply_ofInjective_symm {f : G ->* N} (
hf : Function.Injective f) (x : f.range) : f ((ofInjective hf).symm x) = x
· 使用定理 `Subgroup.IsComplement.equiv_fst_eq_mul_inv`：equiv_fst_eq_mul_inv (g : G)
 : ↑(hST.equiv g).fst = g * ((hST.equiv g).snd : G)⁻¹
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `Monoid.CoprodI.Word.prod_smul`：prod_smul (m) : forall w : Word M, prod (
m • w) = m * prod w
· 使用定理 `Monoid.PushoutI.ofCoprodI_of`：ofCoprodI_of (i : ι) (g : G i) : (ofCoprod
I (CoprodI.of g) : PushoutI φ) = of i g
· 使用定理 `inv_mul_cancel_left`：inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b
· 使用定理 `mul_inv_cancel_left`：mul_inv_cancel_left (a b : G) : a * (a⁻¹ * b) = b
（共 31 条，此处仅展示前 30 条）
-/
theorem prod_summand_smul {i : ι} (g : G i) (w : NormalWord d) :
    (g • w).prod = of i g * w.prod := by
  simp only [prod, summand_smul_def', equivPair, rcons, Word.equivPair_symm,
    Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk, Word.equivPair_smul_same,
    Word.equivPair_tail_eq_inv_smul, Word.rcons_eq_smul, ← of_apply_eq_base φ i,
    MonoidHom.apply_ofInjective_symm, equiv_fst_eq_mul_inv, mul_assoc, map_mul, map_inv,
    Word.prod_smul, ofCoprodI_of, inv_mul_cancel_left, mul_inv_cancel_left]

@[simp]
/-
**Monoid.PushoutI.NormalWord.prod_smul** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pushout
I.NormalWord`。
形式化陈述：prod_smul (g : PushoutI φ) (w : NormalWord d) : (g • w).prod = g * w.prod
参数：g : PushoutI φ；w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.induction_on`：induction_on {motive : PushoutI φ -> Prop}
 (x : PushoutI φ) (of : forall (i : ι) (g : G i), motive (of i g)) (base : foral
l h, motive (base …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.of_smul_eq_smul`：of_smul_eq_smul {i : ι} (g :
 G i) (w : NormalWord d) : of (φ
· 使用定理 `Monoid.PushoutI.NormalWord.prod_summand_smul`：prod_summand_smul {i : ι} 
(g : G i) (w : NormalWord d) : (g • w).prod = of i g * w.prod
· 使用定理 `Monoid.PushoutI.NormalWord.base_smul_eq_smul`：base_smul_eq_smul (h : H) 
(w : NormalWord d) : base φ h • w = h • w
· 使用定理 `Monoid.PushoutI.NormalWord.prod_base_smul`：prod_base_smul (h : H) (w : N
ormalWord d) : (h • w).prod = base φ h * w.prod
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem prod_smul (g : PushoutI φ) (w : NormalWord d) :
    (g • w).prod = g * w.prod := by
  induction g using PushoutI.induction_on generalizing w with
  | of i g => rw [of_smul_eq_smul, prod_summand_smul]
  | base h => rw [base_smul_eq_smul, prod_base_smul]
  | mul x y ihx ihy => rw [mul_smul, ihx, ihy, mul_assoc]
/-
**Monoid.PushoutI.NormalWord.prod_smul_empty** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.P
ushoutI.NormalWord`。
形式化陈述：prod_smul_empty (w : NormalWord d) : w.prod • empty = w
参数：w : NormalWord d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.prod_empty`：prod_empty : (empty : NormalWord 
d).prod = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Monoid.PushoutI.NormalWord.prod_cons`：prod_cons {i} (g : G i) (w : Norma
lWord d) (hmw : w.fstIdx != some i) (hgr : g ∉ (φ i).range) : (cons g w hmw hgr)
.prod = of i g * w.prod
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Monoid.PushoutI.NormalWord.cons_eq_smul`：cons_eq_smul {i : ι} (g : G i) 
(w : NormalWord d) (hmw : w.fstIdx != some i) (hgr : g ∉ (φ i).range) : cons g w
 hmw hgr = of (φ
· 使用定理 `Monoid.PushoutI.NormalWord.prod_smul`：prod_smul (g : PushoutI φ) (w : No
rmalWord d) : (g • w).prod = g * w.prod
-/
theorem prod_smul_empty (w : NormalWord d) : w.prod • empty = w := by
  induction w using consRecOn with
  | empty => simp
  | cons i g w _ _ _ _ ih =>
    rw [prod_cons, mul_smul, ih, cons_eq_smul]
  | base h w _ ih =>
    rw [prod_smul, mul_smul, ih]

/-- The equivalence between normal forms and elements of the pushout -/
/-
**Monoid.PushoutI.NormalWord.equiv** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI.No
rmalWord`。
形式化陈述：equiv : PushoutI φ ≃ NormalWord d
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.prod_smul_empty`：prod_smul_empty (w : NormalW
ord d) : w.prod • empty = w

--- 原说明 ---
The equivalence between normal forms and elements of the pushout
-/
noncomputable def equiv : PushoutI φ ≃ NormalWord d :=
  { toFun := fun g => g • .empty
    invFun := fun w => w.prod
    left_inv := fun g => by
      simp only [prod_smul, prod_empty, mul_one]
    right_inv := fun w => prod_smul_empty w }
/-
**Monoid.PushoutI.NormalWord.prod_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.Pu
shoutI.NormalWord`。
形式化陈述：prod_injective {ι : Type*} {G : ι -> Type*} [(i : ι) -> Group (G i)] {φ : 
(i : ι) -> H ->* G i} {d : Transversal φ} : Function.Injective (prod : NormalWor
d d -> PushoutI φ)
参数：i : ι；G i；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem prod_injective {ι : Type*} {G : ι → Type*} [(i : ι) → Group (G i)] {φ : (i : ι) → H →* G i}
    {d : Transversal φ} : Function.Injective (prod : NormalWord d → PushoutI φ) := by
  let := Classical.decEq ι
  let := fun i => Classical.decEq (G i)
  exact equiv.symm.injective
/-
**Monoid.PushoutI.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI.NormalW
ord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul (PushoutI φ) (NormalWord d) :=
  ⟨fun h => by simpa using congr_arg prod (h empty)⟩
/-
**Monoid.PushoutI.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI.NormalW
ord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (i : ι) : FaithfulSMul (G i) (NormalWord d) :=
  ⟨by simp [summand_smul_def']⟩
/-
**Monoid.PushoutI.NormalWord.** 是 Mathlib 中的一个实例，位于命名空间 `Monoid.PushoutI.NormalW
ord`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul H (NormalWord d) :=
  ⟨by simp [base_smul_def']⟩

end NormalWord

open NormalWord

/-- All maps into the `PushoutI`, or amalgamated product of groups are injective,
provided all maps in the diagram are injective.

See also `base_injective` -/
/-
**Monoid.PushoutI.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：of_injective (hφ : forall i, Function.Injective (φ i)) (i : ι) : Function.
Injective (of (φ
参数：hφ : forall i, Function.Injective (φ i)；i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.transversal_nonempty`：transversal_nonempty (h
φ : forall i, Injective (φ i)) : Nonempty (Transversal φ)
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Monoid.PushoutI.NormalWord.instFaithfulSMul_1`：∀ {ι : Type u_1} {G : ι →
 Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ
 : (i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monoid.PushoutI.NormalWord.of_smul_eq_smul`：of_smul_eq_smul {i : ι} (g :
 G i) (w : NormalWord d) : of (φ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
All maps into the `PushoutI`, or amalgamated product of groups are injective,
provided all maps in the diagram are injective.

See also `base_injective`
-/
theorem of_injective (hφ : ∀ i, Function.Injective (φ i)) (i : ι) :
    Function.Injective (of (φ := φ) i) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, of_smul_eq_smul])
/-
**Monoid.PushoutI.base_injective** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.PushoutI`。
形式化陈述：base_injective (hφ : forall i, Function.Injective (φ i)) : Function.Inject
ive (base φ)
参数：hφ : forall i, Function.Injective (φ i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.transversal_nonempty`：transversal_nonempty (h
φ : forall i, Injective (φ i)) : Nonempty (Transversal φ)
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `FaithfulSMul.eq_of_smul_eq_smul`：∀ {M : Type u_4} {α : Type u_5} {inst :
 SMul M α} [self : FaithfulSMul M α] {m₁ m₂ : M},   (∀ (a : α), m₁ • a = m₂ • a)
 → m₁ = m₂
· 使用定理 `Monoid.PushoutI.NormalWord.instFaithfulSMul_2`：∀ {ι : Type u_1} {G : ι →
 Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ
 : (i : ι) → H →* G i} {d : Monoid.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Monoid.PushoutI.NormalWord.base_smul_eq_smul`：base_smul_eq_smul (h : H) 
(w : NormalWord d) : base φ h • w = h • w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem base_injective (hφ : ∀ i, Function.Injective (φ i)) :
    Function.Injective (base φ) := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  let _ := Classical.decEq ι
  let _ := fun i => Classical.decEq (G i)
  refine Function.Injective.of_comp
    (f := ((· • ·) : PushoutI φ → NormalWord d → NormalWord d)) ?_
  intro _ _ h
  exact eq_of_smul_eq_smul (fun w : NormalWord d =>
    by simp_all [funext_iff, base_smul_eq_smul])

section Reduced

variable (φ) in
/-- A word in `CoprodI` is reduced if none of its letters are in the base group. -/
/-
**Monoid.PushoutI.Reduced** 是 Mathlib 中的一个定义，位于命名空间 `Monoid.PushoutI`。
形式化陈述：Reduced (w : Word G) : Prop
参数：w : Word G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A word in `CoprodI` is reduced if none of its letters are in the base group.
-/
def Reduced (w : Word G) : Prop :=
  ∀ g, g ∈ w.toList → g.2 ∉ (φ g.1).range
/-
**Monoid.PushoutI.Reduced.exists_normalWord_prod_eq** 是 Mathlib 中的一个定理，位于命名空间 `M
onoid.PushoutI.Reduced`。
形式化陈述：∀ {ι : Type u_1} {G : ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group
 (G i)] [inst_1 : Group H]   {φ : (i : ι) → H →* G i} (d : Monoid.PushoutI.Norma
lWord.Transversal φ) {w : Monoid.CoprodI.Word G},   Monoid.PushoutI.Reduced φ w 
→     ∃ w', w'.prod = Monoid.PushoutI.ofCoprodI w.prod ∧ List.map Sigma.fst w'.t
oList = List.map Sigma.fst w.toList
参数：i : ι；G i；i : ι；d : Monoid.PushoutI.NormalWord.Transversal φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.PushoutI.NormalWord.prod_empty`：prod_empty : (empty : NormalWord 
d).prod = 1
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `Monoid.CoprodI.Word.fstIdx.eq_1`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] (w : Monoid.CoprodI.Word M),   w.fstIdx = Option.ma
p Sigma.fst w.toList.…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head?_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α}
, (List.map f l).head? = Option.map f l.head?
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `Monoid.PushoutI.NormalWord.prod_cons`：prod_cons {i} (g : G i) (w : Norma
lWord d) (hmw : w.fstIdx != some i) (hgr : g ∉ (φ i).range) : (cons g w hmw hgr)
.prod = of i g * w.prod
· 使用定理 `Monoid.CoprodI.Word.prod_cons`：prod_cons (i) (m : M i) (w : Word M) (h1 
: m != 1) (h2 : w.fstIdx != some i) : prod (cons m w h2 h1) = of m * prod w
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Monoid.PushoutI.ofCoprodI_of`：ofCoprodI_of (i : ι) (g : G i) : (ofCoprod
I (CoprodI.of g) : PushoutI φ) = of i g
· 使用定理 `Monoid.PushoutI.NormalWord.Transversal.compl`：∀ {ι : Type u_1} {G : ι → 
Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ 
: (i : ι) → H →* G i} (self : Mono…
· 使用定理 `Monoid.PushoutI.NormalWord.cons_toList`：∀ {ι : Type u_1} {G : ι → Type u
_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ : (i :
 ι) → H →* G i} {d : Monoid.…
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Monoid.CoprodI.Word.cons_toList`：∀ {ι : Type u_1} {M : ι → Type u_2} [in
st : (i : ι) → Monoid (M i)] {i : ι} (m : M i) (w : Monoid.CoprodI.Word M)   (hm
w : w.fstIdx ≠ some i…
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem Reduced.exists_normalWord_prod_eq (d : Transversal φ) {w : Word G} (hw : Reduced φ w) :
    ∃ w' : NormalWord d, w'.prod = ofCoprodI w.prod ∧
      w'.toList.map Sigma.fst = w.toList.map Sigma.fst := by
  induction w using Word.consRecOn with
  | empty => exact ⟨empty, by simp, rfl⟩
  | cons i g w hIdx hg1 ih =>
    rcases ih (fun _ hg => hw _ (List.mem_cons_of_mem _ hg)) with
      ⟨w', hw'prod, hw'map⟩
    refine ⟨cons g w' ?_ ?_, ?_⟩
    · rwa [Word.fstIdx, ← List.head?_map, hw'map, List.head?_map]
    · exact hw _ List.mem_cons_self
    · simp [hw'prod, hw'map]

/-- For any word `w` in the coproduct,
if `w` is reduced (i.e none its letters are in the image of the base monoid), and nonempty, then
`w` itself is not in the image of the base group. -/
/-
**Monoid.PushoutI.Reduced.eq_empty_of_mem_range** 是 Mathlib 中的一个定理，位于命名空间 `Monoi
d.PushoutI.Reduced`。
形式化陈述：∀ {ι : Type u_1} {G : ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group
 (G i)] [inst_1 : Group H]   {φ : (i : ι) → H →* G i},   (∀ (i : ι), Function.In
jective ⇑(φ i)) →     ∀ {w : Monoid.CoprodI.Word G},       Monoid.PushoutI.Reduc
ed φ w →         Monoid.PushoutI.ofCoprodI w.prod ∈ (Monoid.PushoutI.base φ).ran
ge → w = Monoid.CoprodI.Word.empty
参数：i : ι；G i；i : ι；∀ (i : ι), Function.Injective ⇑(φ i)；Monoid.PushoutI.base φ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.PushoutI.NormalWord.transversal_nonempty`：transversal_nonempty (h
φ : forall i, Injective (φ i)) : Nonempty (Transversal φ)
· 使用定理 `Monoid.PushoutI.Reduced.exists_normalWord_prod_eq`：∀ {ι : Type u_1} {G :
 ι → Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H] 
  {φ : (i : ι) → H →* G i} (d : Monoid.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Monoid.CoprodI.Word.empty_toList`：∀ {ι : Type u_1} {M : ι → Type u_2} [i
nst : (i : ι) → Monoid (M i)], Monoid.CoprodI.Word.empty.toList = []
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Monoid.PushoutI.NormalWord.prod_injective`：prod_injective {ι : Type*} {G
 : ι -> Type*} [(i : ι) -> Group (G i)] {φ : (i : ι) -> H ->* G i} {d : Transver
sal φ} : Function.Injective (pr…
· 使用定理 `Monoid.CoprodI.Word.ext`：∀ {ι : Type u_1} {M : ι → Type u_2} {inst : (i 
: ι) → Monoid (M i)} {x y : Monoid.CoprodI.Word M},   x.toList = y.toList → x = 
y
· 使用定理 `List.ext_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α}, (∀ (i : ℕ), l₁[i]?
 = l₂[i]?) → l₁ = l₂
· 使用定理 `Option.ext`：∀ {α : Type u_1} {o₁ o₂ : Option α}, (∀ (a : α), o₁ = some a
 ↔ o₂ = some a) → o₁ = o₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `getElem?_neg`：∀ {cont : Type u_1} {idx : Type u_2} {elem : Type u_3} {do
m : cont → idx → Prop} [inst : GetElem? cont idx elem dom]   [LawfulGetElem cont
 i…
· 使用定理 `List.instLawfulGetElemNatLtLength`：∀ {α : Type u_1}, LawfulGetElem (List
 α) ℕ α fun as i => i < as.length
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
For any word `w` in the coproduct,
if `w` is reduced (i.e none its letters are in the image of the base monoid), an
d nonempty, then
`w` itself is not in the image of the base group.
-/
theorem Reduced.eq_empty_of_mem_range
    (hφ : ∀ i, Injective (φ i)) {w : Word G} (hw : Reduced φ w)
    (h : ofCoprodI w.prod ∈ (base φ).range) : w = .empty := by
  rcases transversal_nonempty φ hφ with ⟨d⟩
  rcases hw.exists_normalWord_prod_eq d with ⟨w', hw'prod, hw'map⟩
  rcases h with ⟨h, heq⟩
  have : (NormalWord.prod (d := d) ⟨.empty, h, by simp⟩) = base φ h := by
    simp [NormalWord.prod]
  rw [← hw'prod, ← this] at heq
  suffices w'.toWord = .empty by
    simp [this, @eq_comm _ []] at hw'map
    ext
    simp [hw'map]
  rw [← prod_injective heq]

end Reduced

/-- The intersection of the images of the maps from any two distinct groups in the diagram
into the amalgamated product is the image of the map from the base group in the diagram. -/
/-
**Monoid.PushoutI.inf_of_range_eq_base_range** 是 Mathlib 中的一个定理，位于命名空间 `Monoid.P
ushoutI`。
形式化陈述：inf_of_range_eq_base_range (hφ : forall i, Injective (φ i)) {i j : ι} (hij
 : i != j) : (of i).range ⊓ (of j).range = (base φ).range
参数：hφ : forall i, Injective (φ i)；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MonoidHom.mem_range`：mem_range {f : G ->* N} {y : N} : y in f.range ↔ ex
ists x, f x = y
· 使用定理 `Monoid.PushoutI.of_apply_eq_base`：of_apply_eq_base (i : ι) (x : H) : of 
i (φ i x) = base φ x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`：∀ {ι : Type u_1} {G : ι →
 Type u_2} {H : Type u_3} [inst : (i : ι) → Group (G i)] [inst_1 : Group H]   {φ
 : (i : ι) → H →* G i},   (∀ (i : ι…
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
The intersection of the images of the maps from any two distinct groups in the d
iagram
into the amalgamated product is the image of the map from the base group in the 
diagram.
-/
theorem inf_of_range_eq_base_range
    (hφ : ∀ i, Injective (φ i)) {i j : ι} (hij : i ≠ j) :
    (of i).range ⊓ (of j).range = (base φ).range :=
  le_antisymm
    (by
      intro x ⟨⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩
      by_contra hx
      have hx1 : x ≠ 1 := by rintro rfl; simp_all only [ne_eq, one_mem, not_true_eq_false]
      have hg₁1 : g₁ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) i) (by simp_all)
      have hg₂1 : g₂ ≠ 1 :=
        ne_of_apply_ne (of (φ := φ) j) (by simp_all)
      have hg₁r : g₁ ∉ (φ i).range := by
        rintro ⟨y, rfl⟩
        subst hg₁
        exact hx (of_apply_eq_base φ i y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      have hg₂r : g₂ ∉ (φ j).range := by
        rintro ⟨y, rfl⟩
        subst hg₂
        exact hx (of_apply_eq_base φ j y ▸ MonoidHom.mem_range.2 ⟨y, rfl⟩)
      let w : Word G := ⟨[⟨_, g₁⟩, ⟨_, g₂⁻¹⟩], by simp_all, by simp_all⟩
      have hw : Reduced φ w := by
        simp only [w, Reduced, List.mem_cons,
          forall_eq_or_imp, not_false_eq_true,
          hg₁r, hg₂r, List.mem_nil_iff, false_imp_iff, imp_true_iff, and_true,
          inv_mem_iff]
      have := hw.eq_empty_of_mem_range hφ (by
        simp only [w, Word.prod, List.map_cons, List.prod_cons, List.prod_nil,
          List.map_nil, map_mul, ofCoprodI_of, hg₁, hg₂, map_inv, mul_one,
          mul_inv_cancel, one_mem])
      simp [w, Word.empty] at this)
    (le_inf
      (by rw [← of_comp_eq_base i]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ i h, rfl⟩)
      (by rw [← of_comp_eq_base j]
          rintro _ ⟨h, rfl⟩
          exact MonoidHom.mem_range.2 ⟨φ j h, rfl⟩))

end PushoutI

end Monoid

