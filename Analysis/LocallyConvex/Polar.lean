/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Kalle Kytölä
-/
module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.Topology.Algebra.Module.Spaces.WeakBilin

/-!
# Polar set

In this file we define the polar set. There are different notions of the polar, we will define the
*absolute polar*. The advantage over the real polar is that we can define the absolute polar for
any bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`, where `𝕜` is a normed commutative ring and
`E` and `F` are modules over `𝕜`.

## Main definitions

* `LinearMap.polar`: The polar of a bilinear form `B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜`.

## Main statements

* `LinearMap.polar_eq_iInter`: The polar as an intersection.
* `LinearMap.subset_bipolar`: The polar is a subset of the bipolar.
* `LinearMap.polar_isClosed`: The polar is closed in the weak topology induced by `B.flip`.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

polar
-/

@[expose] public section

variable {𝕜 E F : Type*}

open Topology

namespace LinearMap

section NormedRing

variable [NormedCommRing 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-- The (absolute) polar of `s : Set E` is given by the set of all `y : F` such that `‖B x y‖ ≤ 1`
for all `x ∈ s`. -/
/-
**LinearMap.polar** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：polar (s : Set E) : Set F
参数：s : Set E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (absolute) polar of `s : Set E` is given by the set of all `y : F` such that
 `‖B x y‖ ≤ 1`
for all `x ∈ s`.
-/
def polar (s : Set E) : Set F :=
  { y : F | ∀ x ∈ s, ‖B x y‖ ≤ 1 }
/-
**LinearMap.polar_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_mem_iff (s : Set E) (y : F) : y in B.polar s ↔ forall x in s, ‖B x y
‖ <= 1
参数：s : Set E；y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem polar_mem_iff (s : Set E) (y : F) : y ∈ B.polar s ↔ ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  Iff.rfl
/-
**LinearMap.polar_mem** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_mem (s : Set E) (y : F) (hy : y in B.polar s) : forall x in s, ‖B x 
y‖ <= 1
参数：s : Set E；y : F；hy : y in B.polar s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem polar_mem (s : Set E) (y : F) (hy : y ∈ B.polar s) : ∀ x ∈ s, ‖B x y‖ ≤ 1 :=
  hy
/-
**LinearMap.polar_eq_biInter_preimage** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_eq_biInter_preimage (s : Set E) : B.polar s = ⋂ x in s, ((B x) ⁻¹' M
etric.closedBall (0 : 𝕜) 1)
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem polar_eq_biInter_preimage (s : Set E) :
    B.polar s = ⋂ x ∈ s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1) := by aesop

-- TODO: this theorem is abusing defeq between F and WeakBilin B.flip
/-
**LinearMap.polar_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_isClosed (s : Set E) : IsClosed (X
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_eq_biInter_preimage`：polar_eq_biInter_preimage (s : Set 
E) : B.polar s = ⋂ x in s, ((B x) ⁻¹' Metric.closedBall (0 : 𝕜) 1)
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `WeakBilin.eval_continuous`：eval_continuous (y : F) : Continuous fun x : 
WeakBilin B => B x y
· 使用引理 `Metric.isClosed_closedBall`：isClosed_closedBall : IsClosed (closedBall x
 ε)
-/
theorem polar_isClosed (s : Set E) : IsClosed (X := WeakBilin B.flip) (B.polar s) := by
  rw [polar_eq_biInter_preimage]
  exact isClosed_biInter
    fun _ _ ↦ Metric.isClosed_closedBall.preimage (WeakBilin.eval_continuous B.flip _)

@[simp]
/-
**LinearMap.zero_mem_polar** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：zero_mem_polar (s : Set E) : (0 : F) in B.polar s
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem zero_mem_polar (s : Set E) : (0 : F) ∈ B.polar s := fun _ _ => by
  simp only [map_zero, norm_zero, zero_le_one]
/-
**LinearMap.polar_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_nonempty (s : Set E) : Set.Nonempty (B.polar s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.zero_mem_polar`：zero_mem_polar (s : Set E) : (0 : F) in B.pola
r s
-/
theorem polar_nonempty (s : Set E) : Set.Nonempty (B.polar s) := by
  use 0
  exact zero_mem_polar B s
/-
**LinearMap.polar_eq_iInter** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_eq_iInter {s : Set E} : B.polar s = ⋂ x in s, { y : F | ‖B x y‖ <= 1
 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem polar_eq_iInter {s : Set E} : B.polar s = ⋂ x ∈ s, { y : F | ‖B x y‖ ≤ 1 } := by
  ext
  simp only [polar_mem_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/-- The map `B.polar : Set E → Set F` forms an order-reversing Galois connection with
`B.flip.polar : Set F → Set E`. We use `OrderDual.toDual` and `OrderDual.ofDual` to express
that `polar` is order-reversing. -/
/-
**LinearMap.polar_gc** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.polar) (B.flip.polar ∘ O
rderDual.ofDual)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
The map `B.polar : Set E → Set F` forms an order-reversing Galois connection wit
h
`B.flip.polar : Set F → Set E`. We use `OrderDual.toDual` and `OrderDual.ofDual`
 to express
that `polar` is order-reversing.
-/
theorem polar_gc :
    GaloisConnection (OrderDual.toDual ∘ B.polar) (B.flip.polar ∘ OrderDual.ofDual) := fun _ _ =>
  ⟨fun h _ hx _ hy => h hy _ hx, fun h _ hx _ hy => h hy _ hx⟩

@[simp]
/-
**LinearMap.polar_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_iUnion {ι} {s : ι -> Set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `LinearMap.polar_gc`：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.po
lar) (B.flip.polar ∘ OrderDual.ofDual)
-/
theorem polar_iUnion {ι} {s : ι → Set E} : B.polar (⋃ i, s i) = ⋂ i, B.polar (s i) :=
  B.polar_gc.l_iSup

@[simp]
/-
**LinearMap.polar_union** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_union {s t : Set E} : B.polar (s union t) = B.polar s inter B.polar 
t
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `LinearMap.polar_gc`：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.po
lar) (B.flip.polar ∘ OrderDual.ofDual)
-/
theorem polar_union {s t : Set E} : B.polar (s ∪ t) = B.polar s ∩ B.polar t :=
  B.polar_gc.l_sup
/-
**LinearMap.polar_antitone** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_antitone : Antitone (B.polar : Set E -> Set F)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `LinearMap.polar_gc`：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.po
lar) (B.flip.polar ∘ OrderDual.ofDual)
-/
theorem polar_antitone : Antitone (B.polar : Set E → Set F) :=
  B.polar_gc.monotone_l

@[simp]
/-
**LinearMap.polar_empty** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_empty : B.polar ∅ = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `LinearMap.polar_gc`：polar_gc : GaloisConnection (OrderDual.toDual ∘ B.po
lar) (B.flip.polar ∘ OrderDual.ofDual)
-/
theorem polar_empty : B.polar ∅ = Set.univ :=
  B.polar_gc.l_bot

@[simp]
/-
**LinearMap.polar_singleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_singleton {a : E} : B.polar {a} = { y | ‖B a y‖ <= 1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.polar_mem_iff`：polar_mem_iff (s : Set E) (y : F) : y in B.pola
r s ↔ forall x in s, ‖B x y‖ <= 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
-/
theorem polar_singleton {a : E} : B.polar {a} = { y | ‖B a y‖ ≤ 1 } := le_antisymm
  (fun _ hy => hy _ rfl)
  (fun y hy => (polar_mem_iff _ _ _).mp (fun _ hb => by rw [Set.mem_singleton_iff.mp hb]; exact hy))
/-
**LinearMap.mem_polar_singleton** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：mem_polar_singleton {x : E} (y : F) : y in B.polar {x} ↔ ‖B x y‖ <= 1
参数：y : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_singleton`：polar_singleton {a : E} : B.polar {a} = { y |
 ‖B a y‖ <= 1 }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_polar_singleton {x : E} (y : F) : y ∈ B.polar {x} ↔ ‖B x y‖ ≤ 1 := by
  simp only [polar_singleton, Set.mem_ofPred_eq]
/-
**LinearMap.polar_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_zero : B.polar ({0} : Set E) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_singleton`：polar_singleton {a : E} : B.polar {a} = { y |
 ‖B a y‖ <= 1 }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_zero : B.polar ({0} : Set E) = Set.univ := by
  simp only [polar_singleton, map_zero, zero_apply, norm_zero, zero_le_one, Set.ofPred_true]
/-
**LinearMap.subset_bipolar** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：subset_bipolar (s : Set E) : s subseteq B.flip.polar (B.polar s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.flip_apply`：flip_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M)
 (n : N) : flip f n m = f m n
-/
theorem subset_bipolar (s : Set E) : s ⊆ B.flip.polar (B.polar s) := fun x hx y hy => by
  rw [B.flip_apply]
  exact hy x hx

@[simp]
/-
**LinearMap.tripolar_eq_polar** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：tripolar_eq_polar (s : Set E) : B.polar (B.flip.polar (B.polar s)) = B.pol
ar s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `LinearMap.polar_antitone`：polar_antitone : Antitone (B.polar : Set E -> 
Set F)
· 使用定理 `LinearMap.subset_bipolar`：subset_bipolar (s : Set E) : s subseteq B.flip
.polar (B.polar s)
-/
theorem tripolar_eq_polar (s : Set E) : B.polar (B.flip.polar (B.polar s)) = B.polar s :=
  (B.polar_antitone (B.subset_bipolar s)).antisymm (subset_bipolar B.flip (B.polar s))
/-
**LinearMap.sInter_polar_finite_subset_eq_polar** 是 Mathlib 中的一个定理，位于命名空间 `Linea
rMap`。
形式化陈述：sInter_polar_finite_subset_eq_polar (s : Set E) : ⋂₀ (B.polar '' { F | F.F
inite ∧ F subseteq s }) = B.polar s
参数：s : Set E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LinearMap.polar_singleton`：polar_singleton {a : E} : B.polar {a} = { y |
 ‖B a y‖ <= 1 }
· 使用定理 `Set.finite_singleton`：finite_singleton (a : α) : ({a} : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `LinearMap.polar_antitone`：polar_antitone : Antitone (B.polar : Set E -> 
Set F)
-/
theorem sInter_polar_finite_subset_eq_polar (s : Set E) :
    ⋂₀ (B.polar '' { F | F.Finite ∧ F ⊆ s }) = B.polar s := by
  ext x
  simp only [Set.sInter_image, Set.mem_ofPred_eq, Set.mem_iInter, and_imp]
  refine ⟨fun hx a ha ↦ ?_, fun hx F _ hF₂ => polar_antitone _ hF₂ hx⟩
  simpa [mem_polar_singleton] using hx _ (Set.finite_singleton a) (Set.singleton_subset_iff.mpr ha)

end NormedRing

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommMonoid E] [AddCommMonoid F]
variable [Module 𝕜 E] [Module 𝕜 F]


variable (B : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜)

/-
**LinearMap.polar_univ** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_univ (h : SeparatingRight B) : B.polar Set.univ = {(0 : F)}
参数：h : SeparatingRight B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `le_of_forall_gt_imp_ge_of_dense`：le_of_forall_gt_imp_ge_of_dense (h : fo
rall a, a₂ < a -> a₁ <= a) : a₁ <= a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `NormedField.exists_norm_lt`：exists_norm_lt {r : Real} (hr : 0 < r) : exi
sts x : α, 0 < ‖x‖ ∧ ‖x‖ < r
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `mul_inv_cancel_left₀`：mul_inv_cancel_left₀ (h : a != 0) (b : G₀) : a * (
a⁻¹ * b) = b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `trivial`：True
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem polar_univ (h : SeparatingRight B) : B.polar Set.univ = {(0 : F)} := by
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨by simp only [zero_mem_polar], fun y hy => h _ fun x => ?_⟩
  refine norm_le_zero_iff.mp (le_of_forall_gt_imp_ge_of_dense fun ε hε => ?_)
  rcases NormedField.exists_norm_lt 𝕜 hε with ⟨c, hc, hcε⟩
  calc
    ‖B x y‖ = ‖c‖ * ‖B (c⁻¹ • x) y‖ := by
      rw [B.map_smul, LinearMap.smul_apply, smul_eq_mul, norm_mul, norm_inv,
        mul_inv_cancel_left₀ hc.ne']
    _ ≤ ε * 1 := by gcongr; exact hy _ trivial
    _ = ε := mul_one _
/-
**LinearMap.polar_subMulAction** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：polar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) 
: B.polar m = { y | forall x in m, B x y = 0 }
参数：m : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
-/
theorem polar_subMulAction {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    B.polar m = { y | ∀ x ∈ m, B x y = 0 } := by
  ext y
  constructor
  · intro hy x hx
    obtain ⟨r, hr⟩ := NormedField.exists_lt_norm 𝕜 ‖B x y‖⁻¹
    contrapose! hr
    rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hr)]
    simpa using hy _ (SMulMemClass.smul_mem r hx)
  · intro h x hx
    simp [h x hx]

/-- The polar of a set closed under scalar multiplication as a submodule -/
/-
**LinearMap.polarSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Su
bmodule 𝕜 F
参数：m : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar of a set closed under scalar multiplication as a submodule
-/
def polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : Submodule 𝕜 F :=
  .copy (⨅ x ∈ m, LinearMap.ker (B x)) (B.polar m) <| by ext; simp [polar_subMulAction]

end NontriviallyNormedField

end LinearMap

namespace StrongDual

section

variable (R M : Type*) [SeminormedCommRing R] [TopologicalSpace M] [AddCommGroup M] [Module R M]

/-
**StrongDual.dualPairing_separatingLeft** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：dualPairing_separatingLeft : (topDualPairing R M).SeparatingLeft
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `ContinuousLinearMap.coe_injective`：coe_injective : Function.Injective ((
↑) : (M₁ ->SL[σ₁₂] M₂) -> M₁ ->ₛₗ[σ₁₂] M₂)
-/
theorem dualPairing_separatingLeft : (topDualPairing R M).SeparatingLeft := by
  rw [LinearMap.separatingLeft_iff_ker_eq_bot, LinearMap.ker_eq_bot]
  exact ContinuousLinearMap.coe_injective

end

section

/-- Given a subset `s` in a monoid `M` (over a commutative ring `R`), the polar `polar R s` is the
subset of `StrongDual R M` consisting of those functionals which evaluate to something of norm at
most one at all points `z ∈ s`. -/
/-
**StrongDual.polar** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：polar (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M] [Topolo
gicalSpace M] [Module R M] : Set M -> Set (StrongDual R M)
参数：R : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subset `s` in a monoid `M` (over a commutative ring `R`), the polar `pol
ar R s` is the
subset of `StrongDual R M` consisting of those functionals which evaluate to som
ething of norm at
most one at all points `z ∈ s`.
-/
def polar (R : Type*) [NormedCommRing R] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module R M] : Set M → Set (StrongDual R M) :=
  (topDualPairing R M).flip.polar

/-- Given a subset `s` in a monoid `M` (over a field `𝕜`) closed under scalar multiplication,
the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 M` consisting of those functionals
which evaluate to zero at all points `z ∈ s`. -/
/-
**StrongDual.polarSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `StrongDual`。
形式化陈述：polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCom
mMonoid M] [TopologicalSpace M] [Module 𝕜 M] {S : Type*} [SetLike S M] [SMulMemC
lass S 𝕜 M] (m : S) : Submodule 𝕜 (StrongDual 𝕜 M)
参数：𝕜 : Type*；m : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a subset `s` in a monoid `M` (over a field `𝕜`) closed under scalar multip
lication,
the polar `polarSubmodule 𝕜 s` is the submodule of `StrongDual 𝕜 M` consisting o
f those functionals
which evaluate to zero at all points `z ∈ s`.
-/
def polarSubmodule (𝕜 : Type*) [NontriviallyNormedField 𝕜] {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [Module 𝕜 M] {S : Type*} [SetLike S M] [SMulMemClass S 𝕜 M] (m : S) :
    Submodule 𝕜 (StrongDual 𝕜 M) := (topDualPairing 𝕜 M).flip.polarSubmodule m

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommMonoid E] [TopologicalSpace E] [Module 𝕜 E]
/-
**StrongDual.polarSubmodule_eq_polar** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) : (polarSubmodule 𝕜 m : Set
 (StrongDual 𝕜 E)) = polar 𝕜 m
参数：m : SubMulAction 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `SubMulAction.instSMulMemClass`：∀ {R : Type u} {M : Type v} [inst : SMul 
R M], SMulMemClass (SubMulAction R M) R M
-/
lemma polarSubmodule_eq_polar (m : SubMulAction 𝕜 E) :
    (polarSubmodule 𝕜 m : Set (StrongDual 𝕜 E)) = polar 𝕜 m := rfl
/-
**StrongDual.mem_polar_iff** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' in polar 𝕜 s ↔ forall
 z in s, ‖x' z‖ <= 1
参数：s : Set E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_polar_iff {x' : StrongDual 𝕜 E} (s : Set E) : x' ∈ polar 𝕜 s ↔ ∀ z ∈ s, ‖x' z‖ ≤ 1 :=
  Iff.rfl
/-
**StrongDual.polarSubmodule_eq_setOfPred** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：polarSubmodule_eq_setOfPred {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E]
 (m : S) : polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | forall x in m, y x = 0 }
参数：m : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.polar_subMulAction`：polar_subMulAction {S : Type*} [SetLike S 
E] [SMulMemClass S 𝕜 E] (m : S) : B.polar m = { y | forall x in m, B x y = 0 }
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
-/
lemma polarSubmodule_eq_setOfPred {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) :
    polarSubmodule 𝕜 m = { y : StrongDual 𝕜 E | ∀ x ∈ m, y x = 0 } :=
  (topDualPairing 𝕜 E).flip.polar_subMulAction _

@[deprecated (since := "2026-07-09")]
alias polarSubmodule_eq_setOf := polarSubmodule_eq_setOfPred
/-
**StrongDual.mem_polarSubmodule** 是 Mathlib 中的一个引理，位于命名空间 `StrongDual`。
形式化陈述：mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) 
(y : StrongDual 𝕜 E) : y in polarSubmodule 𝕜 m ↔ forall x in m, y x = 0
参数：m : S；y : StrongDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `propext_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `StrongDual.polarSubmodule_eq_setOfPred`：polarSubmodule_eq_setOfPred {S :
 Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S) : polarSubmodule 𝕜 m = { y : 
StrongDual 𝕜 E | forall x in…
-/
lemma mem_polarSubmodule {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E] (m : S)
    (y : StrongDual 𝕜 E) : y ∈ polarSubmodule 𝕜 m ↔ ∀ x ∈ m, y x = 0 :=
  propext_iff.mp congr($(polarSubmodule_eq_setOfPred 𝕜 m) y)

@[simp]
/-
**StrongDual.zero_mem_polar** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) in polar 𝕜 s
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.zero_mem_polar`：zero_mem_polar (s : Set E) : (0 : F) in B.pola
r s
-/
theorem zero_mem_polar (s : Set E) : (0 : StrongDual 𝕜 E) ∈ polar 𝕜 s :=
  LinearMap.zero_mem_polar _ s
/-
**StrongDual.polar_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s)
参数：s : Set E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.polar_nonempty`：polar_nonempty (s : Set E) : Set.Nonempty (B.p
olar s)
-/
theorem polar_nonempty (s : Set E) : Set.Nonempty (polar 𝕜 s) :=
  LinearMap.polar_nonempty _ _

open Set

@[simp]
/-
**StrongDual.polar_empty** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：polar_empty : polar 𝕜 (∅ : Set E) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.polar_empty`：polar_empty : B.polar ∅ = Set.univ
-/
theorem polar_empty : polar 𝕜 (∅ : Set E) = Set.univ :=
  LinearMap.polar_empty _

@[simp]
/-
**StrongDual.polar_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ <= 1 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.polar_singleton`：polar_singleton {a : E} : B.polar {a} = { y |
 ‖B a y‖ <= 1 }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_singleton {a : E} : polar 𝕜 {a} = { x | ‖x a‖ ≤ 1 } := by
  simp only [polar, LinearMap.polar_singleton, LinearMap.flip_apply, topDualPairing_apply]
/-
**StrongDual.mem_polar_singleton** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y in polar 𝕜 {a} ↔ ‖y a
‖ <= 1
参数：y : StrongDual 𝕜 E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StrongDual.polar_singleton`：polar_singleton {a : E} : polar 𝕜 {a} = { x 
| ‖x a‖ <= 1 }
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_polar_singleton {a : E} (y : StrongDual 𝕜 E) : y ∈ polar 𝕜 {a} ↔ ‖y a‖ ≤ 1 := by
  simp only [polar_singleton, mem_ofPred_eq]
/-
**StrongDual.polar_zero** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：polar_zero : polar 𝕜 ({0} : Set E) = Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.polar_zero`：polar_zero : B.polar ({0} : Set E) = Set.univ
-/
theorem polar_zero : polar 𝕜 ({0} : Set E) = Set.univ :=
  LinearMap.polar_zero _

end

section

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]

open Set

@[simp]
/-
**StrongDual.polar_univ** 是 Mathlib 中的一个定理，位于命名空间 `StrongDual`。
形式化陈述：polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.polar_univ`：polar_univ (h : SeparatingRight B) : B.polar Set.u
niv = {(0 : F)}
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.flip_separatingRight`：flip_separatingRight {B : M₁ ->ₛₗ[I₁] M₂
 ->ₛₗ[I₂] M} : B.flip.SeparatingRight ↔ B.SeparatingLeft
· 使用定理 `StrongDual.dualPairing_separatingLeft`：dualPairing_separatingLeft : (top
DualPairing R M).SeparatingLeft
-/
theorem polar_univ : polar 𝕜 (univ : Set E) = {(0 : StrongDual 𝕜 E)} :=
  (topDualPairing 𝕜 E).flip.polar_univ
    (LinearMap.flip_separatingRight.mpr (dualPairing_separatingLeft 𝕜 E))

end

end StrongDual

