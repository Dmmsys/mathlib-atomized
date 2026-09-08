/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Convex cones

In an `R`-module `M`, we define a convex cone as a set `s` such that `a • x + b • y ∈ s` whenever
`x, y ∈ s` and `a, b > 0`. We prove that convex cones form a `CompleteLattice`, and define their
images (`ConvexCone.map`) and preimages (`ConvexCone.comap`) under linear maps.

We define pointed, blunt, flat and salient cones, and prove the correspondence between
convex cones and ordered modules.

We define `Convex.toCone` to be the minimal cone that includes a given convex set.

## Main statements

In `Mathlib/Analysis/Convex/Cone/Extension.lean` we prove
the M. Riesz extension theorem and a form of the Hahn-Banach theorem.

In `Mathlib/Analysis/Convex/Cone/Dual.lean` we prove
a variant of the hyperplane separation theorem.

## Implementation notes

While `Convex R` is a predicate on sets, `ConvexCone R M` is a bundled convex cone.

## References

* https://en.wikipedia.org/wiki/Convex_cone
* [Stephen P. Boyd and Lieven Vandenberghe, *Convex Optimization*][boydVandenberghe2004]
* [Emo Welzl and Bernd Gärtner, *Cone Programming*][welzl_garter]
-/

@[expose] public section

assert_not_exists TopologicalSpace Real Cardinal

open Set LinearMap Pointwise

variable {𝕜 R G M N O : Type*}

/-! ### Definition of `ConvexCone` and basic properties -/

section Definitions

variable [Semiring R] [PartialOrder R]

variable (R M) in
/-- A convex cone is a subset `s` of an `R`-module such that `a • x + b • y ∈ s` whenever `a, b > 0`
and `x, y ∈ s`. -/
@[wikidata Q2256541]
/-
**ConvexCone** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_2) → (M : Type u_4) → [Semiring R] → [PartialOrder R] → [AddCo
mmMonoid M] → [SMul R M] → Type u_4
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is a subset `s` of an `R`-module such that `a • x + b • y ∈ s` whe
never `a, b > 0`
and `x, y ∈ s`.
-/
structure ConvexCone [AddCommMonoid M] [SMul R M] where
  /-- The **carrier set** underlying this cone: the set of points contained in it -/
  carrier : Set M
  smul_mem' : ∀ ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ carrier → c • x ∈ carrier
  add_mem' : ∀ ⦃x⦄ (_ : x ∈ carrier) ⦃y⦄ (_ : y ∈ carrier), x + y ∈ carrier

end Definitions

namespace ConvexCone

section OrderedSemiring

variable [Semiring R] [PartialOrder R] [AddCommMonoid M]

section SMul

variable [SMul R M] {C C₁ C₂ : ConvexCone R M} {s : Set M} {c : R} {x : M}

/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SetLike (ConvexCone R M) M where
  coe := carrier
  coe_injective C₁ C₂ h := by cases C₁; congr!
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (ConvexCone R M) := .ofSetLike (ConvexCone R M) M
/-
**ConvexCone.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (s : Set M) (h₁ : ∀ ⦃c : R⦄
, 0 < c → ∀ ⦃x : M⦄, x ∈ s → c • x ∈ s)   (h₂ : ∀ ⦃x : M⦄, x ∈ s → ∀ ⦃y : M⦄, y 
∈ s → x + y ∈ s), ↑{ carrier := s, smul_mem' := h₁, add_mem' := h₂ } = s
参数：s : Set M；h₁ : ∀ ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ s → c • x ∈ s；h₂ : ∀ ⦃x : M⦄
, x ∈ s → ∀ ⦃y : M⦄, y ∈ s → x + y ∈ s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_mk (s : Set M) (h₁ h₂) : ↑(mk (R := R) s h₁ h₂) = s := rfl
/-
**ConvexCone.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {s : Set M} {x : M} {h₁ : ∀
 ⦃c : R⦄, 0 < c → ∀ ⦃x : M⦄, x ∈ s → c • x ∈ s}   {h₂ : ∀ ⦃x : M⦄, x ∈ s → ∀ ⦃y 
: M⦄, y ∈ s → x + y ∈ s}, x ∈ { carrier := s, smul_mem' := h₁, add_mem' := h₂ } 
↔ x ∈ s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk {h₁ h₂} : x ∈ mk (R := R) s h₁ h₂ ↔ x ∈ s := .rfl

/-- Two `ConvexCone`s are equal if they have the same elements. -/
@[ext]
/-
**ConvexCone.ext** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：ext (h : forall x, x in C₁ ↔ x in C₂) : C₁ = C₂
参数：h : forall x, x in C₁ ↔ x in C₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q

--- 原说明 ---
Two `ConvexCone`s are equal if they have the same elements.
-/
theorem ext (h : ∀ x, x ∈ C₁ ↔ x ∈ C₂) : C₁ = C₂ := SetLike.ext h

variable (C) in
@[aesop 90% (rule_sets := [SetLike])]
/-
**ConvexCone.smul_mem** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C : ConvexCone R M) {c : R
} {x : M}, 0 < c → x ∈ C → c • x ∈ C
参数：C : ConvexCone R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexCone.smul_mem'`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R
] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (se
lf : Conve…
-/
protected lemma smul_mem (hc : 0 < c) (hx : x ∈ C) : c • x ∈ C := C.smul_mem' hc hx

variable (C) in
/-
**ConvexCone.add_mem** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C : ConvexCone R M) ⦃x : M
⦄, x ∈ C → ∀ ⦃y : M⦄, y ∈ C → x + y ∈ C
参数：C : ConvexCone R M。
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexCone.add_mem'`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (sel
f : Conve…
-/
protected lemma add_mem ⦃x⦄ (hx : x ∈ C) ⦃y⦄ (hy : y ∈ C) : x + y ∈ C := C.add_mem' hx hy
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMemClass (ConvexCone R M) M where add_mem ha hb := add_mem' _ ha hb

/-- Copy of a convex cone with a new `carrier` equal to the old one. Useful to fix definitional
equalities. -/
/-
**ConvexCone.copy** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：{R : Type u_2} →   {M : Type u_4} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : AddCommMonoid M] → [inst_3 : SMul R M] →
 (C : ConvexCone R M) → (s : Set M) → s = ↑C → ConvexCone R M
参数：C : ConvexCone R M；s : Set M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a convex cone with a new `carrier` equal to the old one. Useful to fix d
efinitional
equalities.
-/
@[simps] protected def copy (C : ConvexCone R M) (s : Set M) (hs : s = C) : ConvexCone R M where
  carrier := s
  add_mem' := hs.symm ▸ C.add_mem'
  smul_mem' := by simpa [hs] using! C.smul_mem'
/-
**ConvexCone.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：copy_eq (C : ConvexCone R M) (s : Set M) (hs) : C.copy s hs = C
参数：C : ConvexCone R M；s : Set M；hs。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
lemma copy_eq (C : ConvexCone R M) (s : Set M) (hs) : C.copy s hs = C := SetLike.coe_injective hs
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (ConvexCone R M) where
  sInf S :=
    ⟨⋂ C ∈ S, C, fun _r hr _x hx ↦ mem_biInter fun C hC ↦ C.smul_mem hr <| mem_iInter₂.1 hx C hC,
      fun _ hx _ hy ↦
      mem_biInter fun C hC ↦ add_mem (mem_iInter₂.1 hx C hC) (mem_iInter₂.1 hy C hC)⟩

@[simp, norm_cast]
/-
**ConvexCone.coe_sInf** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：coe_sInf (S : Set (ConvexCone R M)) : ↑(sInf S) = ⋂ C in S, (C : Set M)
参数：S : Set (ConvexCone R M)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_sInf (S : Set (ConvexCone R M)) : ↑(sInf S) = ⋂ C ∈ S, (C : Set M) := rfl
/-
**ConvexCone.mem_sInf** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {x : M} {S : Set (ConvexCon
e R M)}, x ∈ sInf S ↔ ∀ C ∈ S, x ∈ C
参数：ConvexCone R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
-/
@[simp] lemma mem_sInf {S : Set (ConvexCone R M)} : x ∈ sInf S ↔ ∀ C ∈ S, x ∈ C := mem_iInter₂

@[simp, norm_cast]
/-
**ConvexCone.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：coe_iInf {ι : Sort*} (f : ι -> ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : S
et M)
参数：f : ι -> ConvexCone R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_iInf {ι : Sort*} (f : ι → ConvexCone R M) : ↑(iInf f) = ⋂ i, (f i : Set M) := by
  simp [iInf]

@[simp]
/-
**ConvexCone.mem_iInf** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：mem_iInf {ι : Sort*} {f : ι -> ConvexCone R M} : x in iInf f ↔ forall i, x
 in f i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_iInf {ι : Sort*} {f : ι → ConvexCone R M} : x ∈ iInf f ↔ ∀ i, x ∈ f i :=
  mem_iInter₂.trans <| by simp
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSemilatticeInf (ConvexCone R M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

variable (R s) in
/-- The cone hull of a set. The smallest convex cone containing that set. -/
/-
**ConvexCone.hull** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：hull : ConvexCone R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone hull of a set. The smallest convex cone containing that set.
-/
def hull : ConvexCone R M := sInf {C : ConvexCone R M | s ⊆ C}
/-
**ConvexCone.subset_hull** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：subset_hull : s subseteq hull R s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma subset_hull : s ⊆ hull R s := by simp [hull]
/-
**ConvexCone.hull_min** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：hull_min (hsC : s subseteq C) : hull R s <= C
参数：hsC : s subseteq C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
lemma hull_min (hsC : s ⊆ C) : hull R s ≤ C := sInf_le hsC
/-
**ConvexCone.hull_le_iff** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：hull_le_iff : hull R s <= C ↔ s subseteq C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `ConvexCone.subset_hull`：subset_hull : s subseteq hull R s
· 使用引理 `ConvexCone.hull_min`：hull_min (hsC : s subseteq C) : hull R s <= C
-/
lemma hull_le_iff : hull R s ≤ C ↔ s ⊆ C := ⟨subset_hull.trans, hull_min⟩
/-
**ConvexCone.gc_hull_coe** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：gc_hull_coe : GaloisConnection (hull R : Set M -> ConvexCone R M) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexCone.hull_le_iff`：hull_le_iff : hull R s <= C ↔ s subseteq C
-/
lemma gc_hull_coe : GaloisConnection (hull R : Set M → ConvexCone R M) (↑) :=
  fun _C _s ↦ hull_le_iff

/-- Galois insertion between `ConvexCone` and `SetLike.coe`. -/
/-
**ConvexCone.gi** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：{R : Type u_2} →   {M : Type u_4} →     [inst : Semiring R] →       [inst_
1 : PartialOrder R] →         [inst_2 : AddCommMonoid M] → [inst_3 : SMul R M] →
 GaloisInsertion (ConvexCone.hull R) SetLike.coe
参数：ConvexCone.hull R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexCone.gc_hull_coe`：gc_hull_coe : GaloisConnection (hull R : Set M -
> ConvexCone R M) (↑)

--- 原说明 ---
Galois insertion between `ConvexCone` and `SetLike.coe`.
-/
protected def gi : GaloisInsertion (hull R : Set M → ConvexCone R M) (↑) where
  gc := gc_hull_coe
  le_l_u _ := subset_hull
  choice s hs := (hull R s).copy s <| subset_hull.antisymm hs
  choice_eq _ _ := copy_eq _ _ _
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Bot (ConvexCone R M) :=
  ⟨⟨∅, fun _ _ _ => False.elim, fun _ => False.elim⟩⟩
/-
**ConvexCone.notMem_bot** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {x : M}, x ∉ ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma notMem_bot : x ∉ (⊥ : ConvexCone R M) := id
/-
**ConvexCone.coe_bot** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M], ↑⊥ = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_bot : ↑(⊥ : ConvexCone R M) = (∅ : Set M) := rfl

@[simp, norm_cast]
/-
**ConvexCone.coe_eq_empty** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ConvexCone.coe_bot`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] 
[inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M], ↑⊥ =
 ∅
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coe_eq_empty : (C : Set M) = ∅ ↔ C = ⊥ := by rw [← coe_bot (R := R)]; norm_cast
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (ConvexCone R M) where
  bot := ⊥
  bot_le _ := empty_subset _
  __ := instCompleteSemilatticeInf
  __ := ConvexCone.gi.liftCompleteLattice

variable (C₁ C₂) in
/-
**ConvexCone.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C₁ C₂ : ConvexCone R M), ↑
(C₁ ⊓ C₂) = ↑C₁ ∩ ↑C₂
参数：C₁ C₂ : ConvexCone R M；C₁ ⊓ C₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_inf : (C₁ ⊓ C₂) = (C₁ ∩ C₂ : Set M) := rfl
/-
**ConvexCone.mem_inf** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {C₁ C₂ : ConvexCone R M} {x
 : M}, x ∈ C₁ ⊓ C₂ ↔ x ∈ C₁ ∧ x ∈ C₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_inf : x ∈ C₁ ⊓ C₂ ↔ x ∈ C₁ ∧ x ∈ C₂ := .rfl
/-
**ConvexCone.mem_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {x : M}, x ∈ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
@[simp] lemma mem_top : x ∈ (⊤ : ConvexCone R M) := mem_univ x
/-
**ConvexCone.coe_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M], ↑⊤ = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_top : ↑(⊤ : ConvexCone R M) = (univ : Set M) := rfl
/-
**ConvexCone.disjoint_coe** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {C₁ C₂ : ConvexCone R M}, D
isjoint ↑C₁ ↑C₂ ↔ Disjoint C₁ C₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, norm_cast] lemma disjoint_coe : Disjoint (C₁ : Set M) C₂ ↔ Disjoint C₁ C₂ := by
  simp [disjoint_iff, ← coe_inf]
/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ConvexCone R M) := ⟨⊥⟩

end SMul

section Module

variable [Module R M] (C : ConvexCone R M)

/-
**ConvexCone.convex** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (C : ConvexCone R 
M), Convex R ↑C
参数：C : ConvexCone R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `convex_iff_forall_pos`：convex_iff_forall_pos : Convex 𝕜 s ↔ forall ⦃x⦄, 
x in s -> forall ⦃y⦄, y in s -> forall ⦃a b : 𝕜⦄, 0 < a -> 0 < b -> a + b = 1 ->
 a • x + b …
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `ConvexCone.instAddMemClass`：∀ {R : Type u_2} {M : Type u_4} [inst : Semi
ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R 
M], AddMemClass …
· 使用定理 `ConvexCone.smul_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C :
 ConvexCo…
-/
protected theorem convex : Convex R (C : Set M) :=
  convex_iff_forall_pos.2 fun _ hx _ hy _ _ ha hb _ ↦ add_mem (C.smul_mem ha hx) (C.smul_mem hb hy)

end Module

section Maps

variable [AddCommMonoid N] [AddCommMonoid O]
variable [Module R M] [Module R N] [Module R O]

/-- The image of a convex cone under an `R`-linear map is a convex cone. -/
/-
**ConvexCone.map** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：map (f : M ->ₗ[R] N) (C : ConvexCone R M) : ConvexCone R N where carrier
参数：f : M ->ₗ[R] N；C : ConvexCone R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of a convex cone under an `R`-linear map is a convex cone.
-/
def map (f : M →ₗ[R] N) (C : ConvexCone R M) : ConvexCone R N where
  carrier := f '' C
  smul_mem' := fun c hc _ ⟨x, hx, hy⟩ => hy ▸ f.map_smul c x ▸ mem_image_of_mem f (C.smul_mem hc hx)
  add_mem' := fun _ ⟨x₁, hx₁, hy₁⟩ _ ⟨x₂, hx₂, hy₂⟩ =>
    hy₁ ▸ hy₂ ▸ f.map_add x₁ x₂ ▸ mem_image_of_mem f (add_mem hx₁ hx₂)

@[simp, norm_cast]
/-
**ConvexCone.coe_map** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：coe_map (C : ConvexCone R M) (f : M ->ₗ[R] N) : (C.map f : Set N) = f '' C
参数：C : ConvexCone R M；f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_map (C : ConvexCone R M) (f : M →ₗ[R] N) : (C.map f : Set N) = f '' C :=
  rfl

@[simp]
/-
**ConvexCone.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：mem_map {f : M ->ₗ[R] N} {C : ConvexCone R M} {y : N} : y in C.map f ↔ exi
sts x in C, f x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
-/
theorem mem_map {f : M →ₗ[R] N} {C : ConvexCone R M} {y : N} : y ∈ C.map f ↔ ∃ x ∈ C, f x = y :=
  Set.mem_image f C y
/-
**ConvexCone.map_map** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：map_map (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R M) : (C.map f)
.map g = C.map (g.comp f)
参数：g : N ->ₗ[R] O；f : M ->ₗ[R] N；C : ConvexCone R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
-/
theorem map_map (g : N →ₗ[R] O) (f : M →ₗ[R] N) (C : ConvexCone R M) :
    (C.map f).map g = C.map (g.comp f) :=
  SetLike.coe_injective <| image_image g f C

@[simp]
/-
**ConvexCone.map_id** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：map_id (C : ConvexCone R M) : C.map LinearMap.id = C
参数：C : ConvexCone R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
-/
theorem map_id (C : ConvexCone R M) : C.map LinearMap.id = C :=
  SetLike.coe_injective <| image_id _

/-- The preimage of a convex cone under an `R`-linear map is a convex cone. -/
/-
**ConvexCone.comap** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：comap (f : M ->ₗ[R] N) (C : ConvexCone R N) : ConvexCone R M where carrier
参数：f : M ->ₗ[R] N；C : ConvexCone R N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a convex cone under an `R`-linear map is a convex cone.
-/
def comap (f : M →ₗ[R] N) (C : ConvexCone R N) : ConvexCone R M where
  carrier := f ⁻¹' C
  smul_mem' c hc x hx := by
    rw [mem_preimage, f.map_smul c]
    exact C.smul_mem hc hx
  add_mem' x hx y hy := by
    rw [mem_preimage, f.map_add]
    exact add_mem hx hy

@[simp]
/-
**ConvexCone.coe_comap** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：coe_comap (f : M ->ₗ[R] N) (C : ConvexCone R N) : (C.comap f : Set M) = f 
⁻¹' C
参数：f : M ->ₗ[R] N；C : ConvexCone R N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comap (f : M →ₗ[R] N) (C : ConvexCone R N) : (C.comap f : Set M) = f ⁻¹' C :=
  rfl

@[simp]
/-
**ConvexCone.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：comap_id (C : ConvexCone R M) : C.comap LinearMap.id = C
参数：C : ConvexCone R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (C : ConvexCone R M) : C.comap LinearMap.id = C :=
  rfl
/-
**ConvexCone.comap_comap** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：comap_comap (g : N ->ₗ[R] O) (f : M ->ₗ[R] N) (C : ConvexCone R O) : (C.co
map g).comap f = C.comap (g.comp f)
参数：g : N ->ₗ[R] O；f : M ->ₗ[R] N；C : ConvexCone R O。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comap (g : N →ₗ[R] O) (f : M →ₗ[R] N) (C : ConvexCone R O) :
    (C.comap g).comap f = C.comap (g.comp f) :=
  rfl

@[simp]
/-
**ConvexCone.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：mem_comap {f : M ->ₗ[R] N} {C : ConvexCone R N} {x : M} : x in C.comap f ↔
 f x in C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {f : M →ₗ[R] N} {C : ConvexCone R N} {x : M} : x ∈ C.comap f ↔ f x ∈ C :=
  Iff.rfl

end Maps

end OrderedSemiring

section LinearOrderedField

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

section MulAction

variable [AddCommMonoid M]
variable [MulAction 𝕜 M] (C : ConvexCone 𝕜 M)

/-
**ConvexCone.smul_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : M} : c • x in C ↔ x in C
参数：hc : 0 < c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexCone.smul_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C :
 ConvexCo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `inv_smul_smul₀`：∀ {α : Type u_4} {β : Type u_5} [inst : GroupWithZero α]
 [inst_1 : MulAction α β] {a : α},   a ≠ 0 → ∀ (x : β), a⁻¹ • a • x = x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : M} : c • x ∈ C ↔ x ∈ C :=
  ⟨fun h => inv_smul_smul₀ hc.ne' x ▸ C.smul_mem (inv_pos.2 hc) h, C.smul_mem hc⟩

end MulAction
end LinearOrderedField

/-! ### Convex cones with extra properties -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [SMul R M] {C C₁ C₂ : ConvexCone R M}

/-- A convex cone is pointed if it includes `0`. -/
/-
**ConvexCone.Pointed** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：Pointed (C : ConvexCone R M) : Prop
参数：C : ConvexCone R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is pointed if it includes `0`.
-/
def Pointed (C : ConvexCone R M) : Prop := (0 : M) ∈ C

/-- A convex cone is blunt if it doesn't include `0`. -/
/-
**ConvexCone.Blunt** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：Blunt (C : ConvexCone R M) : Prop
参数：C : ConvexCone R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is blunt if it doesn't include `0`.
-/
def Blunt (C : ConvexCone R M) : Prop := (0 : M) ∉ C
/-
**ConvexCone.blunt_iff_not_pointed** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：blunt_iff_not_pointed : C.Blunt ↔ ¬ C.Pointed
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma blunt_iff_not_pointed : C.Blunt ↔ ¬ C.Pointed := .rfl
/-
**ConvexCone.pointed_iff_not_blunt** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：pointed_iff_not_blunt : C.Pointed ↔ ¬ C.Blunt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pointed_iff_not_blunt : C.Pointed ↔ ¬ C.Blunt := by simp [Blunt, Pointed]
/-
**ConvexCone.Pointed.mono** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Pointed`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {C₁ C₂ : ConvexCone R M}, C
₁ ≤ C₂ → C₁.Pointed → C₂.Pointed
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pointed.mono (h : C₁ ≤ C₂) : C₁.Pointed → C₂.Pointed := @h _
/-
**ConvexCone.Blunt.anti** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Blunt`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] {C₁ C₂ : ConvexCone R M}, C
₂ ≤ C₁ → C₁.Blunt → C₂.Blunt
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Blunt.anti (h : C₂ ≤ C₁) : C₁.Blunt → C₂.Blunt := (· ∘ @h 0)

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup G] [SMul R G] {C C₁ C₂ : ConvexCone R G}

/-- A convex cone is flat if it contains some nonzero vector `x` and its opposite `-x`. -/
/-
**ConvexCone.Flat** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：Flat (C : ConvexCone R G) : Prop
参数：C : ConvexCone R G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is flat if it contains some nonzero vector `x` and its opposite `-
x`.
-/
def Flat (C : ConvexCone R G) : Prop := ∃ x ∈ C, x ≠ (0 : G) ∧ -x ∈ C

/-- A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`. -/
/-
**ConvexCone.Salient** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：Salient (C : ConvexCone R G) : Prop
参数：C : ConvexCone R G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is salient if it doesn't include `x` and `-x` for any nonzero `x`.
-/
def Salient (C : ConvexCone R G) : Prop := ∀ x ∈ C, x ≠ (0 : G) → -x ∉ C
/-
**ConvexCone.salient_iff_not_flat** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：salient_iff_not_flat : C.Salient ↔ ¬ C.Flat
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem salient_iff_not_flat : C.Salient ↔ ¬ C.Flat := by simp [Salient, Flat]
/-
**ConvexCone.Flat.mono** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Flat`。
形式化陈述：∀ {R : Type u_2} {G : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup G]   [inst_3 : SMul R G] {C₁ C₂ : ConvexCone R G}, C₁
 ≤ C₂ → C₁.Flat → C₂.Flat
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Flat.mono (h : C₁ ≤ C₂) : C₁.Flat → C₂.Flat
  | ⟨x, hxS, hx, hnxS⟩ => ⟨x, h hxS, hx, h hnxS⟩
/-
**ConvexCone.Salient.anti** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Salient`。
形式化陈述：∀ {R : Type u_2} {G : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup G]   [inst_3 : SMul R G] {C₁ C₂ : ConvexCone R G}, C₂
 ≤ C₁ → C₁.Salient → C₂.Salient
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Salient.anti (h : C₂ ≤ C₁) : C₁.Salient → C₂.Salient :=
  fun hS x hxT hx hnT => hS x (h hxT) hx (h hnT)

/-- A flat cone is always pointed (contains `0`). -/
/-
**ConvexCone.Flat.pointed** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Flat`。
形式化陈述：∀ {R : Type u_2} {G : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup G]   [inst_3 : SMul R G] {C : ConvexCone R G}, C.Flat
 → C.Pointed
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexCone.Pointed.eq_1`：∀ {R : Type u_2} {M : Type u_4} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] 
(C : ConvexCo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `AddMemClass.add_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst : 
Add M} {inst_1 : SetLike S M} [self : AddMemClass S M] {s : S}   {a b : M}, a ∈ 
s → b ∈ s…
· 使用定理 `ConvexCone.instAddMemClass`：∀ {R : Type u_2} {M : Type u_4} [inst : Semi
ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R 
M], AddMemClass …

--- 原说明 ---
A flat cone is always pointed (contains `0`).
-/
theorem Flat.pointed (hC : C.Flat) : C.Pointed := by
  obtain ⟨x, hx, _, hxneg⟩ := hC
  rw [Pointed, ← add_neg_cancel x]
  exact add_mem hx hxneg

/-- A blunt cone (one not containing `0`) is always salient. -/
/-
**ConvexCone.Blunt.salient** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.Blunt`。
形式化陈述：∀ {R : Type u_2} {G : Type u_3} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup G]   [inst_3 : SMul R G] {C : ConvexCone R G}, C.Blun
t → C.Salient
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexCone.salient_iff_not_flat`：salient_iff_not_flat : C.Salient ↔ ¬ C.
Flat
· 使用引理 `ConvexCone.blunt_iff_not_pointed`：blunt_iff_not_pointed : C.Blunt ↔ ¬ C.
Pointed
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `ConvexCone.Flat.pointed`：∀ {R : Type u_2} {G : Type u_3} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup G]   [inst_3 : SMul R G] {
C : ConvexCon…

--- 原说明 ---
A blunt cone (one not containing `0`) is always salient.
-/
theorem Blunt.salient : C.Blunt → C.Salient := by
  rw [salient_iff_not_flat, blunt_iff_not_pointed]
  exact mt Flat.pointed

/-- A pointed convex cone defines a preorder. -/
@[instance_reducible]
/-
**ConvexCone.toPreorder** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：toPreorder (C : ConvexCone R G) (h₁ : C.Pointed) : Preorder G where le x y
参数：C : ConvexCone R G；h₁ : C.Pointed。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointed convex cone defines a preorder.
-/
def toPreorder (C : ConvexCone R G) (h₁ : C.Pointed) : Preorder G where
  le x y := y - x ∈ C
  le_refl x := by rw [sub_self x]; exact h₁
  le_trans x y z xy zy := by simpa using add_mem zy xy

/-- A pointed and salient cone defines a partial order. -/
@[instance_reducible]
/-
**ConvexCone.toPartialOrder** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：toPartialOrder (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) : Pa
rtialOrder G
参数：C : ConvexCone R G；h₁ : C.Pointed；h₂ : C.Salient。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pointed and salient cone defines a partial order.
-/
def toPartialOrder (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) : PartialOrder G :=
  { toPreorder C h₁ with
    le_antisymm := by
      intro a b ab ba
      by_contra h
      have h' : b - a ≠ 0 := fun h'' => h (eq_of_sub_eq_zero h'').symm
      have H := h₂ (b - a) ab h'
      rw [neg_sub b a] at H
      exact H ba }

/-- A pointed and salient cone defines an `IsOrderedAddMonoid`. -/
/-
**ConvexCone.to_isOrderedAddMonoid** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：to_isOrderedAddMonoid (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salien
t) : let _
参数：C : ConvexCone R G；h₁ : C.Pointed；h₂ : C.Salient。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_add_right_eq_sub`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a + c - (b + c) = a - b

--- 原说明 ---
A pointed and salient cone defines an `IsOrderedAddMonoid`.
-/
lemma to_isOrderedAddMonoid (C : ConvexCone R G) (h₁ : C.Pointed) (h₂ : C.Salient) :
    let _ := toPartialOrder C h₁ h₂
    IsOrderedAddMonoid G where
  __ := toPartialOrder C h₁ h₂
  add_le_add_left a b hab c := show b + c - (a + c) ∈ C by rwa [add_sub_add_right_eq_sub]

end AddCommGroup

section Module

section Monoid

variable [AddCommMonoid M] [Module R M] {C₁ C₂ : ConvexCone R M} {x : M}

/-
**ConvexCone.** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (ConvexCone R M) :=
  ⟨⟨0, fun _ _ => by simp, fun _ => by simp⟩⟩
/-
**ConvexCone.mem_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {x : M}, x ∈ 0 ↔ x
 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_zero : x ∈ (0 : ConvexCone R M) ↔ x = 0 := .rfl
/-
**ConvexCone.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M], ↑0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_zero : ((0 : ConvexCone R M) : Set M) = 0 := rfl
/-
**ConvexCone.pointed_zero** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：pointed_zero : (0 : ConvexCone R M).Pointed
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexCone.Pointed.eq_1`：∀ {R : Type u_2} {M : Type u_4} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] 
(C : ConvexCo…
· 使用定理 `ConvexCone.mem_zero`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module 
R M] {x :…
-/
theorem pointed_zero : (0 : ConvexCone R M).Pointed := by rw [Pointed, mem_zero]
/-
**ConvexCone.instAdd** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
形式化陈述：instAdd : Add (ConvexCone R M) where add C₁ C₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAdd : Add (ConvexCone R M) where
  add C₁ C₂ := {
    carrier := C₁ + C₂
    smul_mem' := by
      rintro c hc _ ⟨x, hx, y, hy, rfl⟩
      rw [smul_add]
      use c • x, C₁.smul_mem hc hx, c • y, C₂.smul_mem hc hy
    add_mem' := by
      rintro _ ⟨x₁, hx₁, x₂, hx₂, rfl⟩ y ⟨y₁, hy₁, y₂, hy₂, rfl⟩
      exact ⟨x₁ + y₁, add_mem hx₁ hy₁, x₂ + y₂, add_mem hx₂ hy₂, add_add_add_comm ..⟩
  }
/-
**ConvexCone.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (C₁ C₂ : ConvexCon
e R M), ↑(C₁ + C₂) = ↑C₁ + ↑C₂
参数：C₁ C₂ : ConvexCone R M；C₁ + C₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, norm_cast] lemma coe_add (C₁ C₂ : ConvexCone R M) : ↑(C₁ + C₂) = (C₁ + C₂ : Set M) := rfl
/-
**ConvexCone.mem_add** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C₁ C₂ : ConvexCon
e R M} {x : M}, x ∈ C₁ + C₂ ↔ ∃ y ∈ C₁, ∃ z ∈ C₂, y + z = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_add : x ∈ C₁ + C₂ ↔ ∃ y ∈ C₁, ∃ z ∈ C₂, y + z = x := .rfl
/-
**ConvexCone.instAddZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
形式化陈述：instAddZeroClass : AddZeroClass (ConvexCone R M) where zero_add _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddZeroClass : AddZeroClass (ConvexCone R M) where
  zero_add _ := by ext; simp
  add_zero _ := by ext; simp
/-
**ConvexCone.instAddCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `ConvexCone`。
形式化陈述：instAddCommSemigroup : AddCommSemigroup (ConvexCone R M) where add_assoc _
 _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommSemigroup : AddCommSemigroup (ConvexCone R M) where
  add_assoc _ _ _ := SetLike.coe_injective <| add_assoc _ _ _
  add_comm _ _ := SetLike.coe_injective <| add_comm _ _

end Monoid

section Reproducing

variable [AddCommGroup M] [Module R M]

/-- A convex cone is reproducing if its set of element differences equals the entire module,
i.e., every element of `M` can be written as a difference of two elements of `C`. -/
/-
**ConvexCone.IsReproducing** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：IsReproducing (C : ConvexCone R M) : Prop
参数：C : ConvexCone R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone is reproducing if its set of element differences equals the entire
 module,
i.e., every element of `M` can be written as a difference of two elements of `C`
.
-/
def IsReproducing (C : ConvexCone R M) : Prop :=
  (C : Set M) - (C : Set M) = Set.univ

/-- A sufficient criterion for a convex cone `C` to be reproducing is that `Set.univ` is a subset
of `C - C`. -/
/-
**ConvexCone.IsReproducing.of_univ_subset** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.
IsReproducing`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {C : ConvexCone R M
}, Set.univ ⊆ ↑C - ↑C → C.IsReproducing
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
A sufficient criterion for a convex cone `C` to be reproducing is that `Set.univ
` is a subset
of `C - C`.
-/
theorem IsReproducing.of_univ_subset {C : ConvexCone R M}
    (h : Set.univ ⊆ (C : Set M) - (C : Set M)) : C.IsReproducing :=
  Set.eq_univ_iff_forall.mpr fun _ ↦ h (Set.mem_univ _)

/-- The set difference of a reproducing cone with itself equals `Set.univ`. -/
/-
**ConvexCone.IsReproducing.sub_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.IsR
eproducing`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {C : ConvexCone R M
}, C.IsReproducing → ↑C - ↑C = Set.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set difference of a reproducing cone with itself equals `Set.univ`.
-/
lemma IsReproducing.sub_eq_univ {C : ConvexCone R M} (hC : C.IsReproducing) :
    (C : Set M) - (C : Set M) = Set.univ :=
  hC

end Reproducing

section Generating

variable [AddCommMonoid M] [Module R M]

/-- A convex cone `C` is generating if its linear span is the entire `R`-module `M`.

`IsGenerating` is equivalent to `IsReproducing` modulo some conditions.
See `IsReproducing.isGenerating` and `IsGenerating.isReproducing` for details. -/
@[simp, deprecated "write out the definition" (since := "2026-03-30")]
/-
**ConvexCone.IsGenerating** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：IsGenerating (C : ConvexCone R M) : Prop
参数：C : ConvexCone R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A convex cone `C` is generating if its linear span is the entire `R`-module `M`.

`IsGenerating` is equivalent to `IsReproducing` modulo some conditions.
See `IsReproducing.isGenerating` and `IsGenerating.isReproducing` for details.
-/
def IsGenerating (C : ConvexCone R M) : Prop :=
  Submodule.span R (C : Set M) = ⊤

/-- A sufficient criteria for a convex cone `C` to be generating is that top is less than or equal
to the linear span of `C`. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.IsGenerating.of_top_le_span** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.I
sGenerating`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C : ConvexCone R 
M}, ⊤ ≤ Submodule.span R ↑C → C.IsGenerating
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a

--- 原说明 ---
A sufficient criteria for a convex cone `C` to be generating is that top is less
 than or equal
to the linear span of `C`.
-/
theorem IsGenerating.of_top_le_span {C : ConvexCone R M} (h : ⊤ ≤ Submodule.span R (C : Set M)) :
    C.IsGenerating :=
  eq_top_iff.mpr h

/-- The linear span of a generating convex cone equals top. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.IsGenerating.span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.IsGe
nerating`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C : ConvexCone R 
M}, C.IsGenerating → Submodule.span R ↑C = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear span of a generating convex cone equals top.
-/
lemma IsGenerating.span_eq_top {C : ConvexCone R M} (hC : C.IsGenerating) :
    Submodule.span R (C : Set M) = ⊤ :=
  hC

/-- Top is less than or equal to the linear span of a generating convex cone. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.IsGenerating.top_le_span** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.IsGe
nerating`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C : ConvexCone R 
M}, C.IsGenerating → ⊤ ≤ Submodule.span R ↑C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `ConvexCone.IsGenerating.span_eq_top`：∀ {R : Type u_2} {M : Type u_4} [in
st : Semiring R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 
: _root_.Module R M] {C :…

--- 原说明 ---
Top is less than or equal to the linear span of a generating convex cone.
-/
lemma IsGenerating.top_le_span {C : ConvexCone R M} (hC : C.IsGenerating) :
    ⊤ ≤ Submodule.span R (C : Set M) :=
  hC.span_eq_top.ge

/-- The whole `R`-module `M` (viewed as the top convex cone) is generating. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.isGenerating_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：isGenerating_top : (⊤ : ConvexCone R M).IsGenerating
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_univ`：span_univ : span R (univ : Set M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The whole `R`-module `M` (viewed as the top convex cone) is generating.
-/
theorem isGenerating_top : (⊤ : ConvexCone R M).IsGenerating := by
  simp

/-- The empty convex cone is generating iff the module is a subsingleton. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.isGenerating_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：isGenerating_bot_iff : (⊥ : ConvexCone R M).IsGenerating ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subsingleton_iff`：subsingleton_iff : Subsingleton (Submodule R
 M) ↔ Subsingleton M
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α

--- 原说明 ---
The empty convex cone is generating iff the module is a subsingleton.
-/
theorem isGenerating_bot_iff : (⊥ : ConvexCone R M).IsGenerating ↔ Subsingleton M := by
  simpa only [IsGenerating, coe_bot, Submodule.span_empty, ← Submodule.subsingleton_iff R] using
    subsingleton_iff_bot_eq_top

/-- In a subsingleton module, the empty convex cone is generating. -/
@[deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.isGenerating_bot** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：isGenerating_bot [Subsingleton M] : (⊥ : ConvexCone R M).IsGenerating
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ConvexCone.isGenerating_bot_iff`：isGenerating_bot_iff : (⊥ : ConvexCone 
R M).IsGenerating ↔ Subsingleton M

--- 原说明 ---
In a subsingleton module, the empty convex cone is generating.
-/
theorem isGenerating_bot [Subsingleton M] : (⊥ : ConvexCone R M).IsGenerating :=
  isGenerating_bot_iff.mpr inferInstance

/-- A convex cone containing a generating cone is also a generating cone. -/
@[gcongr, deprecated "no replacement" (since := "2026-03-30")]
/-
**ConvexCone.IsGenerating.mono** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.IsGeneratin
g`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C₁ C₂ : ConvexCon
e R M}, C₁ ≤ C₂ → C₁.IsGenerating → C₂.IsGenerating
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexCone.IsGenerating.eq_1`：∀ {R : Type u_2} {M : Type u_4} [inst : Se
miring R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : _root
_.Module R M] (C :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…

--- 原说明 ---
A convex cone containing a generating cone is also a generating cone.
-/
theorem IsGenerating.mono {C₁ C₂ : ConvexCone R M} (h : C₁ ≤ C₂) (hgen : C₁.IsGenerating) :
    C₂.IsGenerating := by
  rw [IsGenerating, ← top_le_iff] at hgen ⊢
  exact hgen.trans (Submodule.span_mono h)
/-
**ConvexCone.IsReproducing.span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.IsR
eproducing`。
形式化陈述：∀ {R : Type u_7} {M : Type u_8} [inst : Ring R] [inst_1 : PartialOrder R] 
[inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] {C : ConvexCone R M}, C
.IsReproducing → Submodule.span R ↑C = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_sub`：∀ {α : Type u_2} [inst : Sub α] {s t : Set α} {a : α}, a ∈ 
s - t ↔ ∃ x ∈ s, ∃ y ∈ t, x - y = a
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `ConvexCone.IsReproducing.eq_1`：∀ {R : Type u_2} {M : Type u_4} [inst : S
emiring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] (C : …
· 使用定理 `sub_mem`：∀ {M : Type u_3} {S : Type u_4} [inst : SubNegMonoid M] [inst_1
 : SetLike S M] [hSM : AddSubgroupClass S M] {H : S}   {x y : M}, x ∈ H → y ∈…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
-/
theorem IsReproducing.span_eq_top {R : Type*} {M : Type*} [Ring R] [PartialOrder R]
    [AddCommGroup M] [Module R M] {C : ConvexCone R M} (h : C.IsReproducing) :
    Submodule.span R (C : Set M) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  rw [IsReproducing, Set.eq_univ_iff_forall] at h
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_sub.mp (h x)
  exact sub_mem (Submodule.subset_span hy) (Submodule.subset_span hz)

@[deprecated (since := "2026-03-30")] alias IsReproducing.isGenerating := IsReproducing.span_eq_top
/-
**ConvexCone.IsReproducing.of_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone.
IsReproducing`。
形式化陈述：∀ {R : Type u_7} {M : Type u_8} [inst : Ring R] [inst_1 : LinearOrder R] [
AddLeftStrictMono R] [inst_3 : AddCommGroup M]   [Nontrivial M] [inst_5 : _root_
.Module R M] {C : ConvexCone R M}, Submodule.span R ↑C = ⊤ → C.IsReproducing
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConvexCone.IsReproducing.eq_1`：∀ {R : Type u_2} {M : Type u_4} [inst : S
emiring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] (C : …
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `ConvexCone.add_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] 
[inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C : 
ConvexCo…
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `ConvexCone.smul_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C :
 ConvexCo…
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_sub_neg`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b : α)
, -a - -b = b - a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `trivial`：True
-/
theorem IsReproducing.of_span_eq_top {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M}
    (h : Submodule.span R (C : Set M) = ⊤) :
    C.IsReproducing := by
  rw [IsReproducing, Set.eq_univ_iff_forall]
  intro x
  -- A generating cone in a nontrivial module must be nonempty
  have hne : (C : Set M).Nonempty := Set.nonempty_iff_ne_empty.2 fun h' => by simp [h'] at h
  -- Build the submodule S = C - C and show span C ⊆ S
  let S : Submodule R M := {
    carrier := (C : Set M) - (C : Set M)
    add_mem' := by
      rintro _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ + y₂, C.add_mem hy₁ hy₂, z₁ + z₂, C.add_mem hz₁ hz₂, add_sub_add_comm ..⟩
    zero_mem' := by
      obtain ⟨c, hc⟩ := hne
      exact ⟨c, hc, c, hc, sub_self c⟩
    smul_mem' := by
      rintro r _ ⟨y, hy, z, hz, rfl⟩
      simp only [Set.mem_sub, SetLike.mem_coe]
      rcases lt_trichotomy r 0 with hr | rfl | hr
      · -- r < 0: use (-r) • z - (-r) • y = r • (y - z)
        refine ⟨(-r) • z, C.smul_mem (neg_pos.mpr hr) hz,
               (-r) • y, C.smul_mem (neg_pos.mpr hr) hy, ?_⟩
        rw [neg_smul, neg_smul, neg_sub_neg, smul_sub]
      · -- r = 0
        simp only [zero_smul]
        obtain ⟨c, hc⟩ := hne
        exact ⟨c, hc, c, hc, sub_self c⟩
      · -- r > 0: use r • y - r • z
        exact ⟨r • y, C.smul_mem hr hy, r • z, C.smul_mem hr hz, (smul_sub r y z).symm⟩}
  have hCS : (C : Set M) ⊆ S := fun x hx ↦
    let ⟨c, hc⟩ := hne; ⟨x + c, C.add_mem hx hc, c, hc, add_sub_cancel_right x c⟩
  exact (h ▸ Submodule.span_le.mpr hCS) trivial

@[deprecated (since := "2026-03-30")]
alias IsGenerating.isReproducing := IsReproducing.of_span_eq_top
/-
**ConvexCone.span_eq_top_iff_isReproducing** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone
`。
形式化陈述：span_eq_top_iff_isReproducing {R : Type*} {M : Type*} [Ring R] [LinearOrde
r R] [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : Con
vexCone R M} : Submodule.span R (C : Set M) = ⊤ ↔ C.IsReproducing
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ConvexCone.IsReproducing.of_span_eq_top`：∀ {R : Type u_7} {M : Type u_8}
 [inst : Ring R] [inst_1 : LinearOrder R] [AddLeftStrictMono R] [inst_3 : AddCom
mGroup M]   [Nontrivial M] [i…
· 使用定理 `ConvexCone.IsReproducing.span_eq_top`：∀ {R : Type u_7} {M : Type u_8} [i
nst : Ring R] [inst_1 : PartialOrder R] [inst_2 : AddCommGroup M]   [inst_3 : _r
oot_.Module R M] {C : Conv…
-/
theorem span_eq_top_iff_isReproducing {R : Type*} {M : Type*} [Ring R] [LinearOrder R]
    [AddLeftStrictMono R] [AddCommGroup M] [Nontrivial M] [Module R M] {C : ConvexCone R M} :
    Submodule.span R (C : Set M) = ⊤ ↔ C.IsReproducing :=
  ⟨.of_span_eq_top, IsReproducing.span_eq_top⟩

@[deprecated (since := "2026-03-30")]
alias isGenerating_iff_isReproducing := IsReproducing.span_eq_top

end Generating

end Module

end OrderedSemiring

section Field
variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]
  {C : ConvexCone 𝕜 M} {s : Set M} {x : M}

/-- The cone hull of a convex set is simply the union of the open halflines through that set. -/
/-
**ConvexCone.mem_hull_of_convex** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：mem_hull_of_convex (hs : Convex 𝕜 s) : x in hull 𝕜 s ↔ exists r : 𝕜, 0 < r
 ∧ x in r • s where mp hx
参数：hs : Convex 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ConvexCone.hull_min`：hull_min (hsC : s subseteq C) : hull R s <= C
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Convex.add_smul`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : Field 𝕜] [inst_
1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [inst_3 : AddCommGroup E] [inst_4 :
 _roo…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `ConvexCone.smul_mem`：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] (C :
 ConvexCo…
· 使用引理 `ConvexCone.subset_hull`：subset_hull : s subseteq hull R s

--- 原说明 ---
The cone hull of a convex set is simply the union of the open halflines through 
that set.
-/
lemma mem_hull_of_convex (hs : Convex 𝕜 s) : x ∈ hull 𝕜 s ↔ ∃ r : 𝕜, 0 < r ∧ x ∈ r • s where
  mp hx := hull_min (C := {
              carrier := {y | ∃ r : 𝕜, 0 < r ∧ y ∈ r • s}
              smul_mem' := by
                intro r₁ hr₁ y ⟨r₂, hr₂, hy⟩
                refine ⟨r₁ * r₂, mul_pos hr₁ hr₂, ?_⟩
                rw [mul_smul]
                exact smul_mem_smul_set hy
              add_mem' := by
                rintro y₁ ⟨r₁, hr₁, hy₁⟩ y₂ ⟨r₂, hr₂, hy₂⟩
                refine ⟨r₁ + r₂, add_pos hr₁ hr₂, ?_⟩
                rw [hs.add_smul hr₁.le hr₂.le]
                exact add_mem_add hy₁ hy₂
            }) (fun y hy ↦ ⟨1, by simpa⟩) hx
  mpr := by rintro ⟨r, hr, y, hy, rfl⟩; exact (hull 𝕜 s).smul_mem hr <| subset_hull hy

/-- The cone hull of a convex set is simply the union of the open halflines through that set. -/
/-
**ConvexCone.coe_hull_of_convex** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：coe_hull_of_convex (hs : Convex 𝕜 s) : hull 𝕜 s = {x | exists r : 𝕜, 0 < r
 ∧ x in r • s}
参数：hs : Convex 𝕜 s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `ConvexCone.mem_hull_of_convex`：mem_hull_of_convex (hs : Convex 𝕜 s) : x 
in hull 𝕜 s ↔ exists r : 𝕜, 0 < r ∧ x in r • s where mp hx

--- 原说明 ---
The cone hull of a convex set is simply the union of the open halflines through 
that set.
-/
lemma coe_hull_of_convex (hs : Convex 𝕜 s) : hull 𝕜 s = {x | ∃ r : 𝕜, 0 < r ∧ x ∈ r • s} := by
  ext; exact mem_hull_of_convex hs
/-
**ConvexCone.disjoint_hull_left_of_convex** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`
。
形式化陈述：disjoint_hull_left_of_convex (hs : Convex 𝕜 s) : Disjoint (hull 𝕜 s) C ↔ D
isjoint s C where mp
参数：hs : Convex 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ConvexCone.disjoint_coe`：∀ {R : Type u_2} {M : Type u_4} [inst : Semirin
g R] [inst_1 : PartialOrder R] [inst_2 : AddCommMonoid M]   [inst_3 : SMul R M] 
{C₁ C₂ : Conv…
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用引理 `ConvexCone.subset_hull`：subset_hull : s subseteq hull R s
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `ConvexCone.mem_hull_of_convex`：mem_hull_of_convex (hs : Convex 𝕜 s) : x 
in hull 𝕜 s ↔ exists r : 𝕜, 0 < r ∧ x in r • s where mp hx
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ConvexCone.smul_mem_iff`：smul_mem_iff {c : 𝕜} (hc : 0 < c) {x : M} : c •
 x in C ↔ x in C
-/
lemma disjoint_hull_left_of_convex (hs : Convex 𝕜 s) : Disjoint (hull 𝕜 s) C ↔ Disjoint s C where
  mp := by rw [← disjoint_coe]; exact .mono_left subset_hull
  mpr := by
    simp_rw [← disjoint_coe, disjoint_left, SetLike.mem_coe, mem_hull_of_convex hs]
    rintro hsC _ ⟨r, hr, y, hy, rfl⟩
    exact (C.smul_mem_iff hr).not.mpr (hsC hy)
/-
**ConvexCone.disjoint_hull_right_of_convex** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone
`。
形式化陈述：disjoint_hull_right_of_convex (hs : Convex 𝕜 s) : Disjoint C (hull 𝕜 s) ↔ 
Disjoint ↑C s
参数：hs : Convex 𝕜 s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_comm`：disjoint_comm : Disjoint a b ↔ Disjoint b a
· 使用引理 `ConvexCone.disjoint_hull_left_of_convex`：disjoint_hull_left_of_convex (h
s : Convex 𝕜 s) : Disjoint (hull 𝕜 s) C ↔ Disjoint s C where mp
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma disjoint_hull_right_of_convex (hs : Convex 𝕜 s) : Disjoint C (hull 𝕜 s) ↔ Disjoint ↑C s := by
  rw [disjoint_comm, disjoint_hull_left_of_convex hs, disjoint_comm]

end Field
end ConvexCone

namespace Submodule

/-! ### Submodules are cones -/


section OrderedSemiring

variable [Semiring R] [PartialOrder R]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] {C C₁ C₂ : Submodule R M} {x : M}

/-- Every submodule is trivially a convex cone. -/
/-
**Submodule.toConvexCone** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：toConvexCone (C : Submodule R M) : ConvexCone R M where carrier
参数：C : Submodule R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…

--- 原说明 ---
Every submodule is trivially a convex cone.
-/
def toConvexCone (C : Submodule R M) : ConvexCone R M where
  carrier := C
  smul_mem' c _ _ hx := C.smul_mem c hx
  add_mem' _ hx _ hy := C.add_mem hx hy
/-
**Submodule.coe_toConvexCone** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] (C : Submodule R M
), ↑C.toConvexCone = ↑C
参数：C : Submodule R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_toConvexCone (C : Submodule R M) : C.toConvexCone = (C : Set M) := rfl
/-
**Submodule.mem_toConvexCone** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M] {C : Submodule R M
} {x : M}, x ∈ C.toConvexCone ↔ x ∈ C
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_toConvexCone : x ∈ C.toConvexCone ↔ x ∈ C := .rfl

@[simp]
/-
**Submodule.toConvexCone_le_toConvexCone** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toConvexCone_le_toConvexCone : C₁.toConvexCone <= C₂.toConvexCone ↔ C₁ <= 
C₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toConvexCone_le_toConvexCone : C₁.toConvexCone ≤ C₂.toConvexCone ↔ C₁ ≤ C₂ := .rfl
/-
**Submodule.toConvexCone_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M], ⊥.toConvexCone = 
0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConvexCone_bot : (⊥ : Submodule R M).toConvexCone = 0 := rfl
/-
**Submodule.toConvexCone_top** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : _root_.Module R M], ⊤.toConvexCone = 
⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toConvexCone_top : (⊤ : Submodule R M).toConvexCone = ⊤ := rfl

@[simp]
/-
**Submodule.toConvexCone_inf** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：toConvexCone_inf (C₁ C₂ : Submodule R M) : (C₁ ⊓ C₂).toConvexCone = C₁.toC
onvexCone ⊓ C₂.toConvexCone
参数：C₁ C₂ : Submodule R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toConvexCone_inf (C₁ C₂ : Submodule R M) :
    (C₁ ⊓ C₂).toConvexCone = C₁.toConvexCone ⊓ C₂.toConvexCone := rfl

@[simp]
/-
**Submodule.pointed_toConvexCone** 是 Mathlib 中的一个引理，位于命名空间 `Submodule`。
形式化陈述：pointed_toConvexCone (C : Submodule R M) : C.toConvexCone.Pointed
参数：C : Submodule R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
lemma pointed_toConvexCone (C : Submodule R M) : C.toConvexCone.Pointed := C.zero_mem

end AddCommMonoid

end OrderedSemiring

end Submodule

/-! ### Positive cone of an ordered module -/

namespace ConvexCone

section PositiveCone
variable [Semiring R] [PartialOrder R] [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulMono R M] {x : M}

variable (R M) in
/-- The positive cone is the convex cone formed by the set of nonnegative elements in an ordered
module. -/
/-
**ConvexCone.positive** 是 Mathlib 中的一个定义，位于命名空间 `ConvexCone`。
形式化陈述：positive : ConvexCone R M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The positive cone is the convex cone formed by the set of nonnegative elements i
n an ordered
module.
-/
def positive : ConvexCone R M where
  carrier := Set.Ici 0
  smul_mem' _ hc _ (hx : _ ≤ _) := smul_nonneg hc.le hx
  add_mem' _ (hx : _ ≤ _) _ (hy : _ ≤ _) := add_nonneg hx hy
/-
**ConvexCone.mem_positive** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：∀ {R : Type u_2} {M : Type u_4} [inst : Semiring R] [inst_1 : PartialOrder
 R] [inst_2 : AddCommMonoid M]   [inst_3 : PartialOrder M] [inst_4 : IsOrderedAd
dMonoid M] [inst_5 : _root_.Module R M] [inst_6 : PosSMulMono R M]   {x : M}, x 
∈ ConvexCone.positive R M ↔ 0 ≤ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_positive : x ∈ positive R M ↔ 0 ≤ x := .rfl

variable (R M) in
@[simp]
/-
**ConvexCone.coe_positive** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：coe_positive : ↑(positive R M) = Set.Ici (0 : M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_positive : ↑(positive R M) = Set.Ici (0 : M) :=
  rfl

/-- The positive cone of an ordered module is always salient. -/
/-
**ConvexCone.salient_positive** 是 Mathlib 中的一个引理，位于命名空间 `ConvexCone`。
形式化陈述：salient_positive {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedA
ddMonoid G] [Module R G] [PosSMulMono R G] : Salient (positive R G)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a

--- 原说明 ---
The positive cone of an ordered module is always salient.
-/
lemma salient_positive {G : Type*} [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    [Module R G] [PosSMulMono R G] : Salient (positive R G) :=
  fun x hx_nonneg hx_ne_zero hx_nonpos ↦ lt_irrefl (0 : G) <| by
    simpa using add_pos_of_nonneg_of_pos hx_nonpos <| hx_nonneg.lt_of_ne' hx_ne_zero

/-- The positive cone of an ordered module is always pointed. -/
/-
**ConvexCone.pointed_positive** 是 Mathlib 中的一个定理，位于命名空间 `ConvexCone`。
形式化陈述：pointed_positive : Pointed (positive R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The positive cone of an ordered module is always pointed.
-/
theorem pointed_positive : Pointed (positive R M) :=
  le_refl 0

end PositiveCone

section StrictlyPositiveCone
variable [Semiring R] [PartialOrder R] [AddCommGroup M] [PartialOrder M] [IsOrderedAddMonoid M]
  [Module R M] [PosSMulStrictMono R M] {x : M}

variable (R M) in
/-- The cone of strictly positive elements.

Note that this naming diverges from the mathlib convention of `pos` and `nonneg` due to "positive
cone" (`ConvexCone.positive`) being established terminology for the non-negative elements. -/
def strictlyPositive : ConvexCone R M where
  carrier := Set.Ioi 0
  smul_mem' _ hc _ (hx : _ < _) := smul_pos hc hx
  add_mem' _ hx _ hy := add_pos hx hy

@[simp]
lemma mem_strictlyPositive : x ∈ strictlyPositive R M ↔ 0 < x := .rfl

variable (R M) in
@[simp]
theorem coe_strictlyPositive : ↑(strictlyPositive R M) = Set.Ioi (0 : M) :=
  rfl

lemma strictlyPositive_le_positive : strictlyPositive R M ≤ positive R M := fun _ => le_of_lt

/-- The strictly positive cone of an ordered module is always salient. -/
theorem salient_strictlyPositive : Salient (strictlyPositive R M) :=
  salient_positive.anti strictlyPositive_le_positive

/-- The strictly positive cone of an ordered module is always blunt. -/
theorem blunt_strictlyPositive : Blunt (strictlyPositive R M) :=
  lt_irrefl 0

end StrictlyPositiveCone

end ConvexCone

/-! ### Cone over a convex set -/


section ConeFromConvex

variable [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup M] [Module 𝕜 M]

namespace Convex

/-- The set of vectors proportional to those in a convex set forms a convex cone. -/
@[deprecated "Use `ConvexCone.hull` and `ConvexCone.coe_hull_of_convex`" (since := "2026-03-30")]
def toCone (s : Set M) (hs : Convex 𝕜 s) : ConvexCone 𝕜 M := by
  apply ConvexCone.mk (⋃ (c : 𝕜) (_ : 0 < c), c • s) <;> simp only [mem_iUnion, mem_smul_set]
  · rintro c c_pos _ ⟨c', c'_pos, x, hx, rfl⟩
    exact ⟨c * c', mul_pos c_pos c'_pos, x, hx, (smul_smul _ _ _).symm⟩
  · rintro _ ⟨cx, cx_pos, x, hx, rfl⟩ _ ⟨cy, cy_pos, y, hy, rfl⟩
    have : 0 < cx + cy := add_pos cx_pos cy_pos
    refine ⟨_, this, _, convex_iff_div.1 hs hx hy cx_pos.le cy_pos.le this, ?_⟩
    simp only [smul_add, smul_smul, mul_div_assoc', mul_div_cancel_left₀ _ this.ne']

variable {s : Set M} (hs : Convex 𝕜 s) {x : M}

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]
theorem mem_toCone : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ ∃ y ∈ s, c • y = x := by
  simp only [toCone, ConvexCone.mem_mk, mem_iUnion, mem_smul_set, eq_comm, exists_prop]

@[deprecated ConvexCone.mem_hull_of_convex (since := "2026-03-30")]
theorem mem_toCone' : x ∈ hs.toCone s ↔ ∃ c : 𝕜, 0 < c ∧ c • x ∈ s := by
  refine hs.mem_toCone.trans ⟨?_, ?_⟩
  · rintro ⟨c, hc, y, hy, rfl⟩
    exact ⟨c⁻¹, inv_pos.2 hc, by rwa [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩
  · rintro ⟨c, hc, hcx⟩
    exact ⟨c⁻¹, inv_pos.2 hc, _, hcx, by rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]⟩

@[deprecated ConvexCone.subset_hull (since := "2026-03-30")]
theorem subset_toCone : s ⊆ hs.toCone s := fun x hx =>
  hs.mem_toCone'.2 ⟨1, zero_lt_one, by rwa [one_smul]⟩

/-- `hs.toCone s` is the least cone that includes `s`. -/
@[deprecated "`ConvexCone.gi.gc.isLeast_l`" (since := "2026-03-30")]
theorem toCone_isLeast : IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } (hs.toCone s) := by
  refine ⟨hs.subset_toCone, fun t ht x hx => ?_⟩
  rcases hs.mem_toCone.1 hx with ⟨c, hc, y, hy, rfl⟩
  exact t.smul_mem hc (ht hy)

@[deprecated "`ConvexCone.gi.gc.isLUB_u.sSup_eq`" (since := "2026-03-30")]
theorem toCone_eq_sInf : hs.toCone s = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  hs.toCone_isLeast.isGLB.sInf_eq.symm

end Convex

@[deprecated "no replacement" (since := "2026-03-30")]
theorem convexHull_toCone_isLeast (s : Set M) :
    IsLeast { t : ConvexCone 𝕜 M | s ⊆ t } ((convex_convexHull 𝕜 s).toCone _) := by
  convert! (convex_convexHull 𝕜 s).toCone_isLeast using 1
  ext t
  exact ⟨fun h => convexHull_min h t.convex, (subset_convexHull 𝕜 s).trans⟩

@[deprecated "no replacement" (since := "2026-03-30")]
theorem convexHull_toCone_eq_sInf (s : Set M) :
    (convex_convexHull 𝕜 s).toCone _ = sInf { t : ConvexCone 𝕜 M | s ⊆ t } :=
  Eq.symm <| IsGLB.sInf_eq <| IsLeast.isGLB <| convexHull_toCone_isLeast s

end ConeFromConvex

