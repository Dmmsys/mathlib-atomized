/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Affine spaces are convex spaces

This file shows that every affine space is a convex space.

## Main results

* `AddTorsor.toConvexSpace`: An affine space over a module is a convex space.
* `AddTorsor.sConvexComb_eq_affineCombination`: The convex combination equals the affine
  combination.
* `AddTorsor.convexCombPair_eq_lineMap`: Binary convex combinations are given by `lineMap`.
-/

public noncomputable section

open scoped Affine

variable {R V P I : Type*}
variable [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
variable [AddCommGroup V] [Module R V] [AddTorsor V P]

open Convexity

namespace AddTorsor

/-- The convex combination of points in an affine space, given a probability distribution. -/
@[expose]
/-
**AddTorsor.convexCombination** 是 Mathlib 中的一个定义，位于命名空间 `AddTorsor`。
形式化陈述：convexCombination (s : StdSimplex R P) : P
参数：s : StdSimplex R P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The convex combination of points in an affine space, given a probability distrib
ution.
-/
def convexCombination (s : StdSimplex R P) : P :=
  s.weights.support.affineCombination R id s.weights
/-
**AddTorsor.convexCombination_single** 是 Mathlib 中的一个定理，位于命名空间 `AddTorsor`。
形式化陈述：convexCombination_single (x : P) : convexCombination (StdSimplex.single x 
: StdSimplex R P) = x
参数：x : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0
-/
theorem convexCombination_single (x : P) :
    convexCombination (StdSimplex.single x : StdSimplex R P) = x := by
  simp only [convexCombination, StdSimplex.single]
  rw [Finsupp.support_single _ one_ne_zero]
  exact ({x} : Finset P).affineCombination_of_eq_one_of_eq_zero _ _
    (Finset.mem_singleton_self x) Finsupp.single_eq_same fun j _ hne => Finsupp.single_eq_of_ne hne
/-
**AddTorsor.convexCombination_assoc** 是 Mathlib 中的一个定理，位于命名空间 `AddTorsor`。
形式化陈述：convexCombination_assoc (f : StdSimplex R (StdSimplex R P)) : convexCombin
ation (f.map convexCombination) = convexCombination f.join
参数：f : StdSimplex R (StdSimplex R P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Convexity.StdSimplex.total`：∀ {R : Type u} [inst : LE R] [inst_1 : AddCo
mmMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   (
self.weights.sum…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_finsetSum_index`：∀ {α : Type u_1} {ι : Type u_2} {M : Type u
_8} {N : Type u_10} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {s : F
inset ι} {g : ι →…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.lt_of_ne'`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, b ≤
 a → a ≠ b → b < a
· 使用定理 `Convexity.StdSimplex.nonneg`：∀ {R : Type u} [inst : LE R] [inst_1 : AddC
ommMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   
0 ≤ self.weights
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
-/
theorem convexCombination_assoc (f : StdSimplex R (StdSimplex R P)) :
    convexCombination (f.map convexCombination) = convexCombination f.join := by
  -- Choose a base point
  obtain ⟨b⟩ : Nonempty P := inferInstance
  -- Express both sides using weightedVSubOfPoint with base point b
  have hL := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (f.map convexCombination).weights.support (f.map convexCombination).weights id
    (f.map convexCombination).total b
  have hR := Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    f.join.weights.support f.join.weights id f.join.total b
  simp only [convexCombination, hL, hR]
  congr 1
  -- Now show the weighted vector sums are equal
  simp only [Finset.weightedVSubOfPoint_apply, StdSimplex.map, StdSimplex.join, id]
  -- Rewrite LHS using sum_mapDomain_index
  change (Finsupp.mapDomain convexCombination f.weights).sum (fun x w => w • (x -ᵥ b)) = _
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp) (fun _ _ _ => by simp [add_smul])]
  simp only [Finsupp.sum, convexCombination]
  -- Expand convexCombination d using base point b
  conv_lhs =>
    congr; · skip
    ext d
    rw [d.weights.support.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
        _ _ d.total b, vadd_vsub, Finset.weightedVSubOfPoint_apply]
    simp only [id]
  simp_rw [Finset.smul_sum, smul_smul]
  -- Expand RHS using sum_finsetSum_index
  let h : P → R → V := fun x w => w • (x -ᵥ b)
  have h_rhs : (∑ d ∈ f.weights.support, f.weights d • d.weights).sum h
      = ∑ d ∈ f.weights.support, (f.weights d • d.weights).sum h :=
    (Finsupp.sum_finsetSum_index (h := h) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _)).symm
  simp only [Finsupp.sum] at h_rhs ⊢
  rw [h_rhs]
  -- Both sides are now double sums; show the inner sums match
  congr 1
  ext d
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  -- Show that d.support = (f.weights d • d.weights).support
  by_cases hd : f.weights d = 0
  · simp [hd]
  · refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext p
    simp only [Finsupp.mem_support_iff, ne_eq]
    constructor
    · intro hp
      exact (mul_pos ((f.nonneg d).lt_of_ne' hd) ((d.nonneg p).lt_of_ne' hp)).ne'
    · intro hp hp'
      simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hp', mul_zero,
        not_true_eq_false] at hp

/-- Any affine space is a convex space.

This is not an instance because its convex combination operation is defined through the choice of an
arbitrary basepoint, which makes it very diamond-prone. -/
@[implicit_reducible]
/-
**AddTorsor.toConvexSpace** 是 Mathlib 中的一个定义，位于命名空间 `AddTorsor`。
形式化陈述：toConvexSpace : ConvexSpace R P where sConvexComb
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.convexCombination_single`：convexCombination_single (x : P) : c
onvexCombination (StdSimplex.single x : StdSimplex R P) = x
· 使用定理 `AddTorsor.convexCombination_assoc`：convexCombination_assoc (f : StdSimpl
ex R (StdSimplex R P)) : convexCombination (f.map convexCombination) = convexCom
bination f.join

--- 原说明 ---
Any affine space is a convex space.

This is not an instance because its convex combination operation is defined thro
ugh the choice of an
arbitrary basepoint, which makes it very diamond-prone.
-/
def toConvexSpace : ConvexSpace R P where
  sConvexComb := convexCombination
  sConvexComb_single := convexCombination_single
  assoc := convexCombination_assoc

attribute [local instance] toConvexSpace

/-- `ConvexSpace.sConvexComb` in an affine space is the affine combination. -/
/-
**AddTorsor.sConvexComb_eq_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `AddTorso
r`。
形式化陈述：sConvexComb_eq_affineCombination (s : StdSimplex R P) : s.sConvexComb = s.
weights.support.affineCombination R id s.weights
参数：s : StdSimplex R P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ConvexSpace.sConvexComb` in an affine space is the affine combination.
-/
theorem sConvexComb_eq_affineCombination (s : StdSimplex R P) :
    s.sConvexComb = s.weights.support.affineCombination R id s.weights := by
  rfl

@[deprecated (since := "2026-05-15")]
alias convexCombination_eq_affineCombination := sConvexComb_eq_affineCombination
/-
**AddTorsor.iConvexComb_eq_affineCombination** 是 Mathlib 中的一个定理，位于命名空间 `AddTorso
r`。
形式化陈述：iConvexComb_eq_affineCombination (s : StdSimplex R I) (f : I -> P) : s.iCo
nvexComb f = s.weights.support.affineCombination R f s.weights
参数：s : StdSimplex R I；f : I -> P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.sConvexComb_eq_affineCombination`：sConvexComb_eq_affineCombina
tion (s : StdSimplex R P) : s.sConvexComb = s.weights.support.affineCombination 
R id s.weights
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Convexity.StdSimplex.total`：∀ {R : Type u} [inst : LE R] [inst_1 : AddCo
mmMonoid R] [inst_2 : One R] {M : Type v} (self : Convexity.StdSimplex R M),   (
self.weights.sum…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.sum_mapDomain_index`：∀ {α : Type u_1} {β : Type u_2} {M : Type u
_5} {N : Type u_6} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid N]   {f : α 
→ β} {s : α →₀ M}…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Convexity.StdSimplex.weights_map`：∀ {R : Type u} [inst : PartialOrder R]
 [inst_1 : Semiring R] [inst_2 : IsStrictOrderedRing R] {M : Type v} {N : Type w
}   (g : M → N) (f : C…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
theorem iConvexComb_eq_affineCombination (s : StdSimplex R I) (f : I → P) :
    s.iConvexComb f = s.weights.support.affineCombination R f s.weights := by
  let p : P := Nonempty.some inferInstance
  simp only [iConvexComb, sConvexComb_eq_affineCombination]
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (b := p) (h := (s.map f).total),
    Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one
    (b := p) (h := s.total)]
  suffices ((s.weights.mapDomain f).sum fun x r ↦ r • (x -ᵥ p)) =
    s.weights.sum fun x r ↦ r • (f x -ᵥ p) by simpa
  simp [Finsupp.sum_mapDomain_index, add_smul]

set_option backward.isDefEq.respectTransparency.types false in
/-- `convexCombPair` in an affine space is the affine line map. -/
/-
**AddTorsor.convexCombPair_eq_lineMap** 是 Mathlib 中的一个定理，位于命名空间 `AddTorsor`。
形式化陈述：convexCombPair_eq_lineMap (s t : R) (hs : 0 <= s) (ht : 0 <= t) (h : s + t
 = 1) (x y : P) : convexCombPair s t hs ht h x y = AffineMap.lineMap y x s
参数：s t : R；hs : 0 <= s；ht : 0 <= t；h : s + t = 1；x y : P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddTorsor.sConvexComb_eq_affineCombination`：sConvexComb_eq_affineCombina
tion (s : StdSimplex R P) : s.sConvexComb = s.weights.support.affineCombination 
R id s.weights
· 使用定理 `Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one`：affi
neCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one (w : ι -> k) (p : ι -> P
) (h : ∑ i in s, w i = 1) (b : P) : s.affineCombination …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finsupp.sum_add_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [
inst : DecidableEq α] [inst_1 : AddZeroClass M]   [inst_2 : AddCommMonoid N] {f 
g : α →₀ M}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finsupp.sum_single_index`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10
} [inst : Zero M] [inst_1 : AddCommMonoid N] {a : α} {b : M}   {h : α → M → N}, 
h a 0 = 0 → (f…
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a

--- 原说明 ---
`convexCombPair` in an affine space is the affine line map.
-/
theorem convexCombPair_eq_lineMap (s t : R) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : s + t = 1) (x y : P) :
    convexCombPair s t hs ht h x y = AffineMap.lineMap y x s := by
  simp only [convexCombPair, AddTorsor.sConvexComb_eq_affineCombination, StdSimplex.duple,
    AffineMap.lineMap_apply]
  classical
  -- Use weighted subtraction with base point y
  rw [Finset.affineCombination_eq_weightedVSubOfPoint_vadd_of_sum_eq_one _ _ id (b := y)]
  swap
  · -- Prove sum of weights equals 1
    trans (Finsupp.single x s + Finsupp.single y t).sum fun _ r => r
    · apply Finset.sum_congr rfl
      intro i _
      simp only [Finsupp.coe_add, Pi.add_apply]
    · rw [Finsupp.sum_add_index (by simp) (by simp), Finsupp.sum_single_index (by simp),
        Finsupp.sum_single_index (by simp), h]
  -- Now simplify the weighted subtraction
  congr 1
  rw [Finset.weightedVSubOfPoint_apply]
  simp only [id]
  -- Convert to Finsupp.sum
  change (Finsupp.single x s + Finsupp.single y t).sum (fun p w => w • (p -ᵥ y)) = _
  rw [Finsupp.sum_add_index (by simp) (fun _ a b => by simp [add_smul]),
    Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
  simp [vsub_self]

end AddTorsor

