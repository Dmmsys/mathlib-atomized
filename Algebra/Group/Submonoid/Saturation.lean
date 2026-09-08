/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Divisibility.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.OmegaCompletePartialOrder

/-! # Saturation of a submonoid

We define a submonoid `s` to be saturated if `x * y ∈ s → x ∈ s ∧ y ∈ s`. The type of all
saturated submonoids forms a complete lattice. For a given submonoid `s` we construct the saturation
of `s` as the smallest saturated submonoid containing `s`, which when the underlying type is a
commutative monoid, is given by the formula `{x : M | ∃ y : M, x * y ∈ s}`.

Saturated submonoids are used in the context of localisations.

We also define the type of saturated submonoids, and endow on it the structure of a complete
lattice.

## Main Definitions

* `Submonoid.MulSaturated`: the condition `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. Not to be confused with
  `Submonoid.PowSaturated`.
* `SaturatedSubmonoid`: the type of `Submonoid` satisfying `MulSaturated`. It is a complete lattice.
* `Submonoid.saturation`: the smallest saturated submonoid containing a given submonoid.

-/

@[expose] public section

namespace Submonoid

/-- Given a submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x * y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `MulSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/
@[to_additive
/-- Given an additive submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x + y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `AddSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/]
/-
**Submonoid.MulSaturated** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：MulSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop
参数：s : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MulSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop :=
  ∀ ⦃x y⦄, x * y ∈ s → x ∈ s ∧ y ∈ s

namespace MulSaturated
variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h in
@[to_additive]
/-
**Submonoid.MulSaturated.mul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSat
urated`。
形式化陈述：mul_mem_iff {x y : M} : x * y in s ↔ x in s ∧ y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
-/
theorem mul_mem_iff {x y : M} : x * y ∈ s ↔ x ∈ s ∧ y ∈ s :=
  ⟨@h _ _, and_imp.mpr mul_mem⟩

@[to_additive]
/-
**Submonoid.MulSaturated.top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSaturated`。
形式化陈述：top : MulSaturated (⊤ : Submonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem top : MulSaturated (⊤ : Submonoid M) := fun _ _ _ ↦ ⟨trivial, trivial⟩

include h₁ h₂ in
@[to_additive]
/-
**Submonoid.MulSaturated.inf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSaturated`。
形式化陈述：inf : MulSaturated (s₁ ⊓ s₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inf : MulSaturated (s₁ ⊓ s₂) :=
  fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

@[to_additive]
/-
**Submonoid.MulSaturated.sInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSaturated`
。
形式化陈述：sInf {f : Set (Submonoid M)} (hf : forall s in f, s.MulSaturated) : (sInf 
f).MulSaturated
参数：Submonoid M；hf : forall s in f, s.MulSaturated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem sInf {f : Set (Submonoid M)} (hf : ∀ s ∈ f, s.MulSaturated) :
    (sInf f).MulSaturated := fun _ _ hxy ↦ by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs ↦ (hf s hs <| hxy s hs).1, fun s hs ↦ (hf s hs <| hxy s hs).2⟩

@[to_additive]
/-
**Submonoid.MulSaturated.iInf** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSaturated`
。
形式化陈述：iInf {ι : Sort*} {f : ι -> Submonoid M} (hf : forall i, (f i).MulSaturated
) : (iInf f).MulSaturated
参数：hf : forall i, (f i).MulSaturated。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.MulSaturated.sInf`：sInf {f : Set (Submonoid M)} (hf : forall s
 in f, s.MulSaturated) : (sInf f).MulSaturated
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.forall_mem_range`：forall_mem_range {p : α -> Prop} : (forall a in ra
nge f, p a) ↔ forall i, p (f i)
-/
theorem iInf {ι : Sort*} {f : ι → Submonoid M} (hf : ∀ i, (f i).MulSaturated) :
    (iInf f).MulSaturated :=
  sInf <| Set.forall_mem_range.mpr hf

/-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/]
/-
**Submonoid.MulSaturated.of_left** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSaturat
ed`。
形式化陈述：of_left {M : Type*} [CommMonoid M] {s : Submonoid M} (h : forall ⦃x y⦄, x 
* y in s -> x in s) : s.MulSaturated
参数：h : forall ⦃x y⦄, x * y in s -> x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
If `M` is commutative, we only need to check the left condition `x ∈ s`.
-/
theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.MulSaturated :=
  fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

/-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/
@[to_additive /-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/]
/-
**Submonoid.MulSaturated.of_right** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid.MulSatura
ted`。
形式化陈述：of_right {M : Type*} [CommMonoid M] {s : Submonoid M} (h : forall ⦃x y⦄, x
 * y in s -> y in s) : s.MulSaturated
参数：h : forall ⦃x y⦄, x * y in s -> y in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.MulSaturated.of_left`：of_left {M : Type*} [CommMonoid M] {s : 
Submonoid M} (h : forall ⦃x y⦄, x * y in s -> x in s) : s.MulSaturated
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a

--- 原说明 ---
If `M` is commutative, we only need to check the right condition `y ∈ s`.
-/
theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.MulSaturated :=
  of_left fun x y ↦ mul_comm x y ▸ @h y x

end MulSaturated

end Submonoid

-- automatic generation failed
/-- A saturated additive submonoid is a submonoid `s` that satisfies `x + y ∈ s → x ∈ s ∧ y ∈ s`. -/
/-
**SaturatedAddSubmonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [AddZeroClass M] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A saturated additive submonoid is a submonoid `s` that satisfies `x + y ∈ s → x 
∈ s ∧ y ∈ s`.
-/
structure SaturatedAddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubmonoid M where
  addSaturated : toAddSubmonoid.AddSaturated

/-- A saturated submonoid is a submonoid `s` that satisfies `x * y ∈ s → x ∈ s ∧ y ∈ s`. -/
/-
**SaturatedSubmonoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [MulOneClass M] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A saturated submonoid is a submonoid `s` that satisfies `x * y ∈ s → x ∈ s ∧ y ∈
 s`.
-/
@[to_additive] structure SaturatedSubmonoid (M : Type*) [MulOneClass M] extends Submonoid M where
  mulSaturated : toSubmonoid.MulSaturated

namespace SaturatedSubmonoid
variable {M : Type*} [MulOneClass M]

attribute [simp] mulSaturated SaturatedAddSubmonoid.addSaturated

@[to_additive]
/-
**SaturatedSubmonoid.toSubmonoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedS
ubmonoid`。
形式化陈述：toSubmonoid_injective : (toSubmonoid (M
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq ↦ by congr

@[to_additive (attr := ext)]
/-
**SaturatedSubmonoid.ext** 是 Mathlib 中的一个引理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) :
 s₁ = s₂
参数：h : s₁.toSubmonoid = s₂.toSubmonoid。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SaturatedSubmonoid.toSubmonoid_injective`：toSubmonoid_injective : (toSub
monoid (M
-/
lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
  toSubmonoid_injective h

variable (M) in
@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (SaturatedSubmonoid M) M where
  coe := (·.carrier)
  coe_injective _ _ h := toSubmonoid_injective <| SetLike.coe_injective h

@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (SaturatedSubmonoid M) := .ofSetLike ..

@[to_additive]
/-
**SaturatedSubmonoid.ext'** 是 Mathlib 中的一个引理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：ext' {s₁ s₂ : SaturatedSubmonoid M} (h : forall x, x in s₁ ↔ x in s₂) : s₁
 = s₂
参数：h : forall x, x in s₁ ↔ x in s₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
-/
lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  SetLike.ext h

variable (M) in
@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SubmonoidClass (SaturatedSubmonoid M) M where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem

@[to_additive (attr := simp)]
/-
**SaturatedSubmonoid.mem_toSubmonoid** 是 Mathlib 中的一个引理，位于命名空间 `SaturatedSubmono
id`。
形式化陈述：mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x in s.toSubmonoid ↔ 
x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Top (SaturatedSubmonoid M) where
  top := { (⊤ : Submonoid M) with mulSaturated := .top }

@[to_additive (attr := simp)]
/-
**SaturatedSubmonoid.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：mem_top {x : M} : x in (⊤ : SaturatedSubmonoid M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
theorem mem_top {x : M} : x ∈ (⊤ : SaturatedSubmonoid M) := trivial

variable (M) in
@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Min (SaturatedSubmonoid M) where
  min s₁ s₂ := { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

variable (M) in
@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (SaturatedSubmonoid M) where
  sInf f :=
  { carrier := ⋂ s ∈ f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs ↦ mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ ↦ one_mem _
    mulSaturated := by
      convert! Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

@[to_additive]
/-
**SaturatedSubmonoid.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x in sInf f ↔ forall s
 in f, x in s
参数：SaturatedSubmonoid M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x ∈ sInf f ↔ ∀ s ∈ f, x ∈ s :=
  Set.mem_iInter₂

variable (M) in
@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (SaturatedSubmonoid M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

end SaturatedSubmonoid

namespace Submonoid

/-- The saturation of a submonoid `s` is the intersection of all saturated submonoids that contain
`s`.

If `M` is a commutative monoid, then this is `{x : M | ∃ y : M, x * y ∈ s}`. -/
@[to_additive
/-- The saturation of an additive submonoid `s` is the intersection of all saturated submonoids
that contain `s`.

If `M` is a commutative additive monoid, then this is `{x : M | ∃ y : M, x + y ∈ s}`. -/]
/-
**Submonoid.saturation** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmon
oid M
参数：s : Submonoid M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmonoid M :=
  sInf {t | s ≤ t.toSubmonoid}

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

variable (M) in
@[to_additive]
/-
**Submonoid.gc_saturation** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：gc_saturation : GaloisConnection (saturation (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SaturatedSubmonoid.mem_sInf`：mem_sInf {f : Set (SaturatedSubmonoid M)} {
x : M} : x in sInf f ↔ forall s in f, x in s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem gc_saturation : GaloisConnection (saturation (M := M)) (·.toSubmonoid) := fun _ _ ↦
  ⟨fun ih _ hx ↦ ih <| SaturatedSubmonoid.mem_sInf.mpr fun _ ht ↦ ht hx,
  fun ih _ hx ↦ SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

variable (M) in
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedSubmonoid.toSubmonoid`. -/
@[to_additive
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedAddSubmonoid.toAddSubmonoid`. -/]
/-
**Submonoid.giSaturation** 是 Mathlib 中的一个定义，位于命名空间 `Submonoid`。
形式化陈述：giSaturation : GaloisInsertion (saturation (M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
def giSaturation : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  choice s hs := { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

@[to_additive]
/-
**Submonoid.saturation_le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_le_iff_le : a.saturation <= b ↔ a <= b.toSubmonoid
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem saturation_le_iff_le : a.saturation ≤ b ↔ a ≤ b.toSubmonoid := gc_saturation ..

@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

@[to_additive]
/-
**Submonoid.le_toSubmonoid_saturation** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：le_toSubmonoid_saturation : a <= a.saturation.toSubmonoid
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (gc_saturation M).le_u_l a

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_toSubmonoid** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_toSubmonoid : b.saturation = b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem saturation_toSubmonoid : b.saturation = b := (giSaturation M).l_u_eq b

@[to_additive (attr := elab_as_elim)]
/-
**Submonoid.saturation_induction** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_induction {s : Submonoid M} {p : (x : M) -> x in s.saturation -
> Prop} (mem : forall (x) (hx : x in s), p x (le_toSubmonoid_saturation hx)) (mu
l : forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)) (of_mul : f
orall (x y) (hxy : x * y in s.saturation), p (x * y) hxy -> p x (s.saturation.2 
hxy).1 ∧ p y (s.saturation.2 hxy).2) {x : M} (hx : x in s.saturation) : p x hx
参数：x : M；mem : forall (x) (hx : x in s), p x (le_toSubmonoid_saturation hx)；mul 
: forall x y hx hy, p x hx -> p y hy -> p (x * y) (mul_mem hx hy)；of_mul : foral
l (x y) (hxy : x * y in s.saturation), p (x * y) hxy -> p x (s.saturation.2 hxy)
.1 ∧ p y (s.saturation.2 hxy).2；hx : x in s.saturation。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.le_toSubmonoid_saturation`：le_toSubmonoid_saturation : a <= a.
saturation.toSubmonoid
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SaturatedSubmonoid.instSubmonoidClass`：∀ (M : Type u_1) [inst : MulOneCl
ass M], SubmonoidClass (SaturatedSubmonoid M) M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SaturatedSubmonoid.mulSaturated`：∀ {M : Type u_1} [inst : MulOneClass M]
 (self : SaturatedSubmonoid M), self.MulSaturated
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `OneMemClass.one_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
One M} {inst_1 : SetLike S M} [self : OneMemClass S M] (s : S), 1 ∈ s
· 使用定理 `SubmonoidClass.toOneMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   On
eMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SaturatedSubmonoid.mem_sInf`：mem_sInf {f : Set (SaturatedSubmonoid M)} {
x : M} : x in sInf f ↔ forall s in f, x in s
-/
theorem saturation_induction {s : Submonoid M}
    {p : (x : M) → x ∈ s.saturation → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (le_toSubmonoid_saturation hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (of_mul : ∀ (x y) (hxy : x * y ∈ s.saturation),
      p (x * y) hxy → p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x ∈ s.saturation) : p x hx := by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | ∃ hx, p x hx }
    one_mem' := ⟨_ , mem 1 <| one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ ↦ ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
  exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h ↦ ⟨_, mem _ h⟩) |>.2

end MulOneClass

section CommMonoid
variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

@[to_additive]
/-
**Submonoid.mem_saturation_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_saturation_iff : x in s.saturation ↔ exists y, x * y in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.saturation_induction`：saturation_induction {s : Submonoid M} {
p : (x : M) -> x in s.saturation -> Prop} (mem : forall (x) (hx : x in s), p x (
le_toSubmonoid_satur…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `MulMemClass.mul_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Mul M} {inst_1 : SetLike S M} [self : MulMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SaturatedSubmonoid.mulSaturated`：∀ {M : Type u_1} [inst : MulOneClass M]
 (self : SaturatedSubmonoid M), self.MulSaturated
· 使用定理 `Submonoid.le_toSubmonoid_saturation`：le_toSubmonoid_saturation : a <= a.
saturation.toSubmonoid
-/
theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ ↦ ih₂.elim fun y₂ h₂ ↦
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h ↦ ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

@[to_additive]
/-
**Submonoid.mem_saturation_iff'** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_saturation_iff' : x in s.saturation ↔ exists y, y * x in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [mem_saturation_iff, mul_comm x]
/-
**Submonoid.mem_saturation_iff_exists_dvd** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：mem_saturation_iff_exists_dvd : x in s.saturation ↔ exists m in s, x ∣ m
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

end CommMonoid

end Submonoid

namespace SaturatedSubmonoid

@[to_additive]
/-
**SaturatedSubmonoid.** 是 Mathlib 中的一个实例，位于命名空间 `SaturatedSubmonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (M : Type*) [MulOneClass M] :
    CompleteLattice (SaturatedSubmonoid M) :=
  { (inferInstance : PartialOrder (SaturatedSubmonoid M)),
    (inferInstance : Top (SaturatedSubmonoid M)),
    (inferInstance : Min (SaturatedSubmonoid M)),
    (inferInstance : CompleteSemilatticeInf (SaturatedSubmonoid M)),
    (Submonoid.giSaturation M).liftCompleteLattice with }

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

@[to_additive]
/-
**SaturatedSubmonoid.bot_def** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥ := rfl

@[to_additive]
/-
**SaturatedSubmonoid.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：sup_def {s₁ s₂ : SaturatedSubmonoid M} : s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.to
Submonoid).saturation
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

@[to_additive]
/-
**SaturatedSubmonoid.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：sSup_def {f : Set (SaturatedSubmonoid M)} : sSup f = (sSup (toSubmonoid ''
 f)).saturation
参数：SaturatedSubmonoid M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

@[to_additive]
/-
**SaturatedSubmonoid.iSup_def** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：iSup_def {ι : Sort*} {f : ι -> SaturatedSubmonoid M} : iSup f = (⨆ i, (f i
).toSubmonoid).saturation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.l_iSup_u`：l_iSup_u [CompleteLattice α] [CompleteLattice 
β] (gi : GaloisInsertion l u) {ι : Sort x} (f : ι -> β) : l (⨆ i, u (f i)) = ⨆ i
, f i
-/
theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation :=
  (Submonoid.giSaturation M).l_iSup_u f |>.symm

end MulOneClass

section CommMonoid
variable [CommMonoid M]

@[to_additive]
/-
**SaturatedSubmonoid.mem_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `SaturatedSubmonoid`。
形式化陈述：mem_bot_iff {x : M} : x in (⊥ : SaturatedSubmonoid M) ↔ IsUnit x
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
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

end CommMonoid

end SaturatedSubmonoid

namespace Submonoid
variable {M : Type*} [MulOneClass M]

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_bot : (⊥ : Submonoid M).saturation = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (gc_saturation M).l_bot

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_top** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_top : (⊤ : Submonoid M).saturation = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_top`：l_top [Preorder α] [PartialOrder β] [OrderTop α] 
[OrderTop β] (gi : GaloisInsertion l u) : l ⊤ = ⊤
-/
theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (giSaturation M).l_top

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_sup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_sup {s₁ s₂ : Submonoid M} : (s₁ ⊔ s₂).saturation = s₁.saturatio
n ⊔ s₂.saturation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (gc_saturation M).l_sup

-- note that it does not preserve inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_sSup {f : Set (Submonoid M)} : (sSup f).saturation = ⨆ s in f, 
s.saturation
参数：Submonoid M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s ∈ f, s.saturation := (gc_saturation M).l_sSup

@[to_additive (attr := simp)]
/-
**Submonoid.saturation_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Submonoid`。
形式化陈述：saturation_iSup {ι : Sort*} {f : ι -> Submonoid M} : (iSup f).saturation =
 ⨆ i, (f i).saturation
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `Submonoid.gc_saturation`：gc_saturation : GaloisConnection (saturation (M
-/
theorem saturation_iSup {ι : Sort*} {f : ι → Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (gc_saturation M).l_iSup

end Submonoid

