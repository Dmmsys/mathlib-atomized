/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Topology.ContinuousMap.ContinuousMapZero
public import Mathlib.Topology.ContinuousMap.Ordered

/-! # Continuous functions as a star-ordered ring

The type class `ContinuousSqrt` gives a sufficient condition on `R` to make `C(α, R)`
and `C(α, R)₀` into a `StarOrderedRing` for any topological space `α`, thereby providing a means
by which we can ensure `C(α, R)` has this property. This condition is satisfied
by `ℝ≥0`, `ℝ`, and `ℂ`, and the instances can be found in the file
`Mathlib/Topology/ContinuousMap/ContinuousSqrt.lean`.

## Implementation notes

Instead of asking for a well-behaved square root on `{x : R | 0 ≤ x}` in the obvious way, we instead
require that, for every `x y  : R` such that `x ≤ y`, there exist some `s` such that `x + s*s = y`.
This is because we need this type class to work for `ℝ≥0` for the
continuous functional calculus. We could instead assume `[OrderedSub R] [ContinuousSub R]`, but that
would lead to a proliferation of type class assumptions in the general case of the continuous
functional calculus, which we want to avoid because there is *already* a proliferation of type
classes there. At the moment, we only expect this class to be used in that context so this is a
reasonable compromise.

The field `ContinuousSqrt.sqrt` is data, which means that, if we implement an instance of the class
for a generic C⋆-algebra, we'll get a non-defeq diamond for the case `R := ℂ`. This shouldn't really
be a problem since the only purpose is to obtain the instance `StarOrderedRing C(α, R)`, which is a
`Prop`, but we note it for future reference.
-/

public section

/-- A type class encoding the property that there is a continuous square root function on
nonnegative elements. This holds for `ℝ≥0`, `ℝ` and `ℂ` (as well as any C⋆-algebra), and this
allows us to derive an instance of `StarOrderedRing C(α, R)` under appropriate hypotheses.
In order for this to work on `ℝ≥0`, we actually must force our square root function to be defined
on and well-behaved for pairs `x : R × R` with `x.1 ≤ x.2`. -/
/-
**ContinuousSqrt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [LE R] → [NonUnitalSemiring R] → [TopologicalSpace R] → T
ype u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class encoding the property that there is a continuous square root functi
on on
nonnegative elements. This holds for `ℝ≥0`, `ℝ` and `ℂ` (as well as any C⋆-algeb
ra), and this
allows us to derive an instance of `StarOrderedRing C(α, R)` under appropriate h
ypotheses.
In order for this to work on `ℝ≥0`, we actually must force our square root funct
ion to be defined
on and well-behaved for pairs `x : R × R` with `x.1 ≤ x.2`.
-/
class ContinuousSqrt (R : Type*) [LE R] [NonUnitalSemiring R] [TopologicalSpace R] where
  /-- `sqrt (a, b)` returns a value `s` such that `b = a + s * s` when `a ≤ b`. -/
  protected sqrt : R × R → R
  protected continuousOn_sqrt : ContinuousOn sqrt {x | x.1 ≤ x.2}
  protected sqrt_nonneg (x : R × R) : x.1 ≤ x.2 → 0 ≤ sqrt x
  protected sqrt_mul_sqrt (x : R × R) : x.1 ≤ x.2 → x.2 = x.1 + sqrt x * sqrt x

namespace ContinuousMap

variable {α : Type*} [TopologicalSpace α]

set_option backward.isDefEq.respectTransparency false in
/-
**ContinuousMap.** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [PartialOrder R] [NonUnitalSemiring R] [StarRing R]
    [StarOrderedRing R] [TopologicalSpace R] [ContinuousStar R] [IsTopologicalSemiring R]
    [ContinuousSqrt R] : StarOrderedRing C(α, R) := by
  refine StarOrderedRing.of_le_iff ?_
  intro f g
  constructor
  · rw [ContinuousMap.le_def]
    intro h
    use (mk _ ContinuousSqrt.continuousOn_sqrt.domRestrict).comp
      ⟨_, map_continuous (f.prodMk g) |>.codRestrict (s := {x | x.1 ≤ x.2}) (by exact h)⟩
    ext x
    simpa [IsSelfAdjoint.star_eq <| .of_nonneg (ContinuousSqrt.sqrt_nonneg (f x, g x) (h x))]
      using ContinuousSqrt.sqrt_mul_sqrt (f x, g x) (h x)
  · rintro ⟨p, rfl⟩
    exact fun x ↦ le_add_of_nonneg_right (star_mul_self_nonneg (p x))

end ContinuousMap

namespace ContinuousMapZero

variable {α : Type*} [TopologicalSpace α] [Zero α]

/-
**ContinuousMapZero.instStarOrderedRing** 是 Mathlib 中的一个实例，位于命名空间 `ContinuousMap
Zero`。
形式化陈述：instStarOrderedRing {R : Type*} [TopologicalSpace R] [CommSemiring R] [Par
tialOrder R] [NoZeroDivisors R] [StarRing R] [StarOrderedRing R] [IsTopologicalS
emiring R] [ContinuousStar R] [StarOrderedRing C(α, R)] : StarOrderedRing C(α, R
)₀ where le_iff f g
参数：α, R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ContinuousMapZero.le_def`：le_def [PartialOrder R] (f g : C(X, R)₀) : f <
= g ↔ forall x, f x <= g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.coe_coe`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topologic
alSpace X] [inst_1 : TopologicalSpace Y] {F : Type u_3}   [inst_2 : FunLike F X 
Y] [inst_3 …
· 使用定理 `ContinuousMap.le_def`：le_def [PartialOrder β] {f g : C(α, β)} : f <= g ↔
 forall a, f a <= g a
· 使用定理 `StarOrderedRing.le_iff`：∀ {R : Type u_3} {inst : NonUnitalSemiring R} {i
nst_1 : PartialOrder R} {inst_2 : StarRing R} [self : StarOrderedRing R]   (x y 
: R), x ≤ y …
· 使用定理 `AddSubmonoid.closure_induction_left`：∀ {M : Type u_1} [inst : AddMonoid 
M] {s : Set M} {motive : (m : M) → m ∈ AddSubmonoid.closure s → Prop},   motive 
0 ⋯ →     (∀ (x : M) (hx …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubmonoid.instAddSubmonoidClass`：∀ {M : Type u_1} [inst : AddZeroClas
s M], AddSubmonoidClass (AddSubmonoid M) M
· 使用引理 `ContinuousMapZero.ext`：ext {f g : C(X, R)₀} (h : forall x, f x = g x) : 
f = g
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `StarOrderedRing.nonneg_iff`：nonneg_iff : 0 <= x ↔ x in AddSubmonoid.clos
ure (Set.range fun s : R => star s * s)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_add_of_nonneg_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1
 : LE α] [AddLeftMono α] {a b : α}, 0 ≤ b → a ≤ a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `StarOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} [inst : NonUnital
Semiring R] [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R],
   IsOrderedAddMonoid R
· 使用定理 `star_mul_self_nonneg`：star_mul_self_nonneg (r : R) : 0 <= star r * r
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
（共 35 条，此处仅展示前 30 条）
-/
instance instStarOrderedRing {R : Type*}
    [TopologicalSpace R] [CommSemiring R] [PartialOrder R] [NoZeroDivisors R] [StarRing R]
    [StarOrderedRing R] [IsTopologicalSemiring R] [ContinuousStar R] [StarOrderedRing C(α, R)] :
    StarOrderedRing C(α, R)₀ where
  le_iff f g := by
    constructor
    · rw [le_def, ← ContinuousMap.coe_coe, ← ContinuousMap.coe_coe g, ← ContinuousMap.le_def,
        StarOrderedRing.le_iff]
      rintro ⟨p, hp_mem, hp⟩
      induction hp_mem using AddSubmonoid.closure_induction_left generalizing f g with
      | zero => exact ⟨0, zero_mem _, by ext x; congrm($(hp) x)⟩
      | add_left s s_mem p p_mem hp' =>
        obtain ⟨s, rfl⟩ := s_mem
        simp only at *
        have h₀ : (star s * s + p) 0 = 0 := by simpa using congr($(hp) 0).symm
        rw [← add_assoc] at hp
        have p'₀ : 0 ≤ p 0 := by rw [← StarOrderedRing.nonneg_iff] at p_mem; exact p_mem 0
        have s₉ : (star s * s) 0 = 0 := le_antisymm ((le_add_of_nonneg_right p'₀).trans_eq h₀)
          (star_mul_self_nonneg (s 0))
        have s₀' : s 0 = 0 := by aesop
        let s' : C(α, R)₀ := ⟨s, s₀'⟩
        obtain ⟨p', hp'_mem, rfl⟩ := hp' (f + star s' * s') g hp
        refine ⟨star s' * s' + p', ?_, by rw [add_assoc]⟩
        exact add_mem (AddSubmonoid.subset_closure ⟨s', rfl⟩) hp'_mem
    · rintro ⟨p, hp, rfl⟩
      induction hp using AddSubmonoid.closure_induction generalizing f with
      | mem s s_mem =>
        obtain ⟨s, rfl⟩ := s_mem
        exact fun x ↦ le_add_of_nonneg_right (star_mul_self_nonneg (s x))
      | zero => simp
      | add g₁ g₂ _ _ h₁ h₂ => calc
          f ≤ f + g₁ := h₁ f
          _ ≤ (f + g₁) + g₂ := h₂ (f + g₁)
          _ = f + (g₁ + g₂) := add_assoc _ _ _

end ContinuousMapZero

