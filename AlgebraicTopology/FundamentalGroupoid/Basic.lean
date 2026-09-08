/-
Copyright (c) 2021 Shing Tak Lam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam
-/
module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Homotopy.Path
public import Mathlib.Data.Set.Subsingleton

/-!
# Fundamental groupoid of a space

Given a topological space `X`, we can define the fundamental groupoid of `X` to be the category with
objects being points of `X`, and morphisms `x ⟶ y` being paths from `x` to `y`, quotiented by
homotopy equivalence. With this, the fundamental group of `X` based at `x` is just the automorphism
group of `x`.
-/

@[expose] public section

open CategoryTheory

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {x₀ x₁ : X}

noncomputable section

open unitInterval

namespace Path

namespace Homotopy

section

/-- Auxiliary function for `reflTransSymm`. -/
/-
**Path.Homotopy.reflTransSymmAux** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：reflTransSymmAux (x : I × I) : Real
参数：x : I × I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for `reflTransSymm`.
-/
def reflTransSymmAux (x : I × I) : ℝ :=
  if (x.2 : ℝ) ≤ 1 / 2 then x.1 * 2 * x.2 else x.1 * (2 - 2 * x.2)

@[continuity, fun_prop]
/-
**Path.Homotopy.continuous_reflTransSymmAux** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homo
topy`。
形式化陈述：continuous_reflTransSymmAux : Continuous reflTransSymmAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if_le`：continuous_if_le [TopologicalSpace γ] [forall x, Decid
able (f x <= g x)] {f' g' : β -> γ} (hf : Continuous f) (hg : Continuous g) (hf'
 : Con…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `ContinuousOn.fun_mul`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Mul M] [ContinuousMul M] {X : Type u_2}   [inst_3 : TopologicalSpace X] {f 
g : X → M}…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `ContinuousOn.mul_const`：ContinuousOn.mul_const (hf : ContinuousOn f s) (
b : M) : ContinuousOn (f · * b) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.comp_continuousOn'`：Continuous.comp_continuousOn' {g : β -> γ
} {f : α -> β} {s : Set α} (hg : Continuous g) (hf : ContinuousOn f s) : Continu
ousOn (fun x => g (…
· 使用定理 `ContinuousOn.fst`：ContinuousOn.fst {f : α -> β × γ} {s : Set α} (hf : Co
ntinuousOn f s) : ContinuousOn (fun x => (f x).1) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ContinuousOn.snd`：ContinuousOn.snd {f : α -> β × γ} {s : Set α} (hf : Co
ntinuousOn f s) : ContinuousOn (fun x => (f x).2) s
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
-/
theorem continuous_reflTransSymmAux : Continuous reflTransSymmAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)
/-
**Path.Homotopy.reflTransSymmAux_mem_I** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`
。
形式化陈述：reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x in I
参数：x : I × I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_le_one₀`：mul_le_one₀ [MulPosMono M₀] (ha : a <= 1) (hb₀ : 0 <= b) (h
b : b <= 1) : a * b <= 1
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem reflTransSymmAux_mem_I (x : I × I) : reflTransSymmAux x ∈ I := by
  dsimp only [reflTransSymmAux]
  split_ifs
  · constructor
    · apply mul_nonneg <;> grind
    · rw [mul_assoc]
      apply mul_le_one₀ <;> grind
  · constructor
    · apply mul_nonneg <;> grind
    · apply mul_le_one₀ <;> grind

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₀` to
  `p.trans p.symm`. -/
/-
**Path.Homotopy.reflTransSymm** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) 
where toFun x
参数：p : Path x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopy.reflTransSymmAux_mem_I`：reflTransSymmAux_mem_I (x : I × I)
 : reflTransSymmAux x in I

--- 原说明 ---
For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path ba
sed at `x₀` to
  `p.trans p.symm`.
-/
def reflTransSymm (p : Path x₀ x₁) : Homotopy (Path.refl x₀) (p.trans p.symm) where
  toFun x := p ⟨reflTransSymmAux x, reflTransSymmAux_mem_I x⟩
  continuous_toFun := by fun_prop
  map_zero_left := by simp [reflTransSymmAux]
  map_one_left x := by
    simp only [reflTransSymmAux, Path.trans]
    cases le_or_gt (x : ℝ) 2⁻¹ with
    | inl hx => simp [hx, ← extend_apply]
    | inr hx =>
      have : p.extend (2 - 2 * ↑x) = p.extend (1 - (2 * ↑x - 1)) := by ring_nf
      simpa [hx.not_ge, ← extend_apply]
  prop' t := by norm_num [reflTransSymmAux]

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path based at `x₁` to
  `p.symm.trans p`. -/
/-
**Path.Homotopy.reflSymmTrans** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p)
参数：p : Path x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any path `p` from `x₀` to `x₁`, we have a homotopy from the constant path ba
sed at `x₁` to
  `p.symm.trans p`.
-/
def reflSymmTrans (p : Path x₀ x₁) : Homotopy (Path.refl x₁) (p.symm.trans p) :=
  (reflTransSymm p.symm).cast rfl <| congr_arg _ (Path.symm_symm _)

end

section TransRefl

/-- Auxiliary function for `trans_refl_reparam`. -/
/-
**Path.Homotopy.transReflReparamAux** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：transReflReparamAux (t : I) : Real
参数：t : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for `trans_refl_reparam`.
-/
def transReflReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 2 then 2 * t else 1

@[continuity, fun_prop]
/-
**Path.Homotopy.continuous_transReflReparamAux** 是 Mathlib 中的一个定理，位于命名空间 `Path.H
omotopy`。
形式化陈述：continuous_transReflReparamAux : Continuous transReflReparamAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if_le`：continuous_if_le [TopologicalSpace γ] [forall x, Decid
able (f x <= g x)] {f' g' : β -> γ} (hf : Continuous f) (hg : Continuous g) (hf'
 : Con…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem continuous_transReflReparamAux : Continuous transReflReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by grind)
/-
**Path.Homotopy.transReflReparamAux_mem_I** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homoto
py`。
形式化陈述：transReflReparamAux_mem_I (t : I) : transReflReparamAux t in I
参数：t : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 68 条，此处仅展示前 30 条）
-/
theorem transReflReparamAux_mem_I (t : I) : transReflReparamAux t ∈ I := by
  unfold transReflReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
/-
**Path.Homotopy.transReflReparamAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotop
y`。
形式化陈述：transReflReparamAux_zero : transReflReparamAux 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transReflReparamAux_zero : transReflReparamAux 0 = 0 := by
  norm_num [transReflReparamAux]
/-
**Path.Homotopy.transReflReparamAux_one** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy
`。
形式化陈述：transReflReparamAux_one : transReflReparamAux 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_false`：isRat_le_false [Ring α] [LinearOrde
r α] [IsStrictOrderedRing α] {a b : α} {na nb : Int} {da db : Nat} (ha : IsRat a
 na da) (hb : IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem transReflReparamAux_one : transReflReparamAux 1 = 1 := by
  norm_num [transReflReparamAux]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Path.Homotopy.trans_refl_reparam** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：trans_refl_reparam (p : Path x₀ x₁) : p.trans (Path.refl x₁) = p.reparam (
fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by fun_prop) (Su
btype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one)
参数：p : Path x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `Path.Homotopy.transReflReparamAux_mem_I`：transReflReparamAux_mem_I (t : 
I) : transReflReparamAux t in I
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Path.Homotopy.transReflReparamAux_zero`：transReflReparamAux_zero : trans
ReflReparamAux 0 = 0
· 使用定理 `Path.Homotopy.transReflReparamAux_one`：transReflReparamAux_one : transRe
flReparamAux 1 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem trans_refl_reparam (p : Path x₀ x₁) :
    p.trans (Path.refl x₁) =
      p.reparam (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transReflReparamAux_zero) (Subtype.ext transReflReparamAux_one) := by
  ext
  unfold transReflReparamAux
  simp only [coe_reparam]
  grind

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (Path.refl x₁)` to `p`. -/
/-
**Path.Homotopy.transRefl** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p
参数：p : Path x₀ x₁。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopy.transReflReparamAux_mem_I`：transReflReparamAux_mem_I (t : 
I) : transReflReparamAux t in I

--- 原说明 ---
For any path `p` from `x₀` to `x₁`, we have a homotopy from `p.trans (Path.refl 
x₁)` to `p`.
-/
def transRefl (p : Path x₀ x₁) : Homotopy (p.trans (Path.refl x₁)) p :=
  ((Homotopy.reparam p (fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩)
          (by fun_prop) (Subtype.ext transReflReparamAux_zero)
          (Subtype.ext transReflReparamAux_one)).cast
      rfl (trans_refl_reparam p).symm).symm

/-- For any path `p` from `x₀` to `x₁`, we have a homotopy from `(Path.refl x₀).trans p` to `p`. -/
/-
**Path.Homotopy.reflTrans** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p
参数：p : Path x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For any path `p` from `x₀` to `x₁`, we have a homotopy from `(Path.refl x₀).tran
s p` to `p`.
-/
def reflTrans (p : Path x₀ x₁) : Homotopy ((Path.refl x₀).trans p) p :=
  (transRefl p.symm).symm₂.cast (by simp) (by simp)

end TransRefl

section Assoc

/-- Auxiliary function for `trans_assoc_reparam`. -/
/-
**Path.Homotopy.transAssocReparamAux** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：transAssocReparamAux (t : I) : Real
参数：t : I。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function for `trans_assoc_reparam`.
-/
def transAssocReparamAux (t : I) : ℝ :=
  if (t : ℝ) ≤ 1 / 4 then 2 * t else if (t : ℝ) ≤ 1 / 2 then t + 1 / 4 else 1 / 2 * (t + 1)

@[continuity, fun_prop]
/-
**Path.Homotopy.continuous_transAssocReparamAux** 是 Mathlib 中的一个定理，位于命名空间 `Path.
Homotopy`。
形式化陈述：continuous_transAssocReparamAux : Continuous transAssocReparamAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_if_le`：continuous_if_le [TopologicalSpace γ] [forall x, Decid
able (f x <= g x)] {f' g' : β -> γ} (hf : Continuous f) (hg : Continuous g) (hf'
 : Con…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `ContinuousOn.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [in
st_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : Topological
Space X] {f …
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
-/
theorem continuous_transAssocReparamAux : Continuous transAssocReparamAux :=
  continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop)
    (continuous_if_le (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      (by grind)).continuousOn (by grind)
/-
**Path.Homotopy.transAssocReparamAux_mem_I** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homot
opy`。
形式化陈述：transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t in I
参数：t : I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 74 条，此处仅展示前 30 条）
-/
theorem transAssocReparamAux_mem_I (t : I) : transAssocReparamAux t ∈ I := by
  unfold transAssocReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]
/-
**Path.Homotopy.transAssocReparamAux_zero** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homoto
py`。
形式化陈述：transAssocReparamAux_zero : transAssocReparamAux 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_true`：isRat_le_true [Ring α] [LinearOrder 
α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Int} -> {da db : Nat} -> IsRa
t a na da -> IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transAssocReparamAux_zero : transAssocReparamAux 0 = 0 := by
  norm_num [transAssocReparamAux]
/-
**Path.Homotopy.transAssocReparamAux_one** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotop
y`。
形式化陈述：transAssocReparamAux_one : transAssocReparamAux 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_eq`：∀ {α : Type u_1} [inst : DivisionSem
iring α] {n d : ℕ} {a n' d' : α},   Mathlib.Meta.NormNum.IsNNRat a n d → ↑n = n'
 → ↑d = d' → a = n' / d'
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isRat_le_false`：isRat_le_false [Ring α] [LinearOrde
r α] [IsStrictOrderedRing α] {a b : α} {na nb : Int} {da db : Nat} (ha : IsRat a
 na da) (hb : IsRat b nb …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_add`：isNNRat_add {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HAdd.hAdd -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transAssocReparamAux_one : transAssocReparamAux 1 = 1 := by
  norm_num [transAssocReparamAux]
/-
**Path.Homotopy.trans_assoc_reparam** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopy`。
形式化陈述：trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r
 : Path x₂ x₃) : (p.trans q).trans r = (p.trans (q.trans r)).reparam (fun t => ⟨
transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop) (Subtype.ex
t transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)
参数：p : Path x₀ x₁；q : Path x₁ x₂；r : Path x₂ x₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.ext`：∀ {X : Type u_1} [inst : TopologicalSpace X] {x y : X} {γ₁ γ₂ 
: Path x y}, ⇑γ₁ = ⇑γ₂ → γ₁ = γ₂
· 使用定理 `Path.Homotopy.transAssocReparamAux_mem_I`：transAssocReparamAux_mem_I (t 
: I) : transAssocReparamAux t in I
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Path.Homotopy.transAssocReparamAux_zero`：transAssocReparamAux_zero : tra
nsAssocReparamAux 0 = 0
· 使用定理 `Path.Homotopy.transAssocReparamAux_one`：transAssocReparamAux_one : trans
AssocReparamAux 1 = 1
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `unitInterval.mul_pos_mem_iff`：mul_pos_mem_iff {a t : Real} (ha : 0 < a) 
: a * t in I ↔ t in Set.Icc (0 : Real) (1 / a)
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `unitInterval.two_mul_sub_one_mem_iff`：two_mul_sub_one_mem_iff {t : Real}
 : 2 * t - 1 in I ↔ t in Set.Icc (1 / 2 : Real) 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Path.trans_apply`：trans_apply (γ : Path x y) (γ' : Path y z) (t : I) : (
γ.trans γ') t = if h : (t : Real) <= 1 / 2 then γ ⟨2 * t, (mul_pos_mem_iff zero_
lt_two…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
（共 95 条，此处仅展示前 30 条）
-/
theorem trans_assoc_reparam {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    (p.trans q).trans r =
      (p.trans (q.trans r)).reparam
        (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
        (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one) := by
  ext x
  simp only [transAssocReparamAux, Path.trans_apply, Function.comp_apply, Path.coe_reparam]
  split_ifs
  iterate 12 grind
  · linarith
  · linarith
  · grind

/-- For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.trans r)`. -/
/-
**Path.Homotopy.transAssoc** 是 Mathlib 中的一个定义，位于命名空间 `Path.Homotopy`。
形式化陈述：transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x
₂ x₃) : Homotopy ((p.trans q).trans r) (p.trans (q.trans r))
参数：p : Path x₀ x₁；q : Path x₁ x₂；r : Path x₂ x₃。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopy.transAssocReparamAux_mem_I`：transAssocReparamAux_mem_I (t 
: I) : transAssocReparamAux t in I

--- 原说明 ---
For paths `p q r`, we have a homotopy from `(p.trans q).trans r` to `p.trans (q.
trans r)`.
-/
def transAssoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    Homotopy ((p.trans q).trans r) (p.trans (q.trans r)) :=
  ((Homotopy.reparam (p.trans (q.trans r))
          (fun t => ⟨transAssocReparamAux t, transAssocReparamAux_mem_I t⟩) (by fun_prop)
          (Subtype.ext transAssocReparamAux_zero) (Subtype.ext transAssocReparamAux_one)).cast
      rfl (trans_assoc_reparam p q r).symm).symm

end Assoc

end Homotopy

namespace Homotopic

/-
**Path.Homotopic.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：refl_trans (p : Path x₀ x₁) : ((Path.refl x₀).trans p).Homotopic p
参数：p : Path x₀ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_trans (p : Path x₀ x₁) :
    ((Path.refl x₀).trans p).Homotopic p :=
  ⟨Homotopy.reflTrans p⟩
/-
**Path.Homotopic.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：trans_refl (p : Path x₀ x₁) : (p.trans (Path.refl x₁)).Homotopic p
参数：p : Path x₀ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_refl (p : Path x₀ x₁) :
    (p.trans (Path.refl x₁)).Homotopic p :=
  ⟨Homotopy.transRefl p⟩
/-
**Path.Homotopic.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：trans_symm (p : Path x₀ x₁) : (p.trans p.symm).Homotopic (Path.refl x₀)
参数：p : Path x₀ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm (p : Path x₀ x₁) :
    (p.trans p.symm).Homotopic (Path.refl x₀) :=
  ⟨(Homotopy.reflTransSymm p).symm⟩
/-
**Path.Homotopic.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：symm_trans (p : Path x₀ x₁) : (p.symm.trans p).Homotopic (Path.refl x₁)
参数：p : Path x₀ x₁。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (p : Path x₀ x₁) :
    (p.symm.trans p).Homotopic (Path.refl x₁) :=
  ⟨(Homotopy.reflSymmTrans p).symm⟩
/-
**Path.Homotopic.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic`。
形式化陈述：trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path 
x₂ x₃) : ((p.trans q).trans r).Homotopic (p.trans (q.trans r))
参数：p : Path x₀ x₁；q : Path x₁ x₂；r : Path x₂ x₃。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x₁) (q : Path x₁ x₂) (r : Path x₂ x₃) :
    ((p.trans q).trans r).Homotopic (p.trans (q.trans r)) :=
  ⟨Homotopy.transAssoc p q r⟩

namespace Quotient

@[simp, grind =]
/-
**Path.Homotopic.Quotient.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Q
uotient`。
形式化陈述：refl_trans (γ : Homotopic.Quotient x₀ x₁) : trans (refl x₀) γ = γ
参数：γ : Homotopic.Quotient x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Path.Homotopic.refl_trans`：refl_trans (p : Path x₀ x₁) : ((Path.refl x₀)
.trans p).Homotopic p
-/
theorem refl_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (refl x₀) γ = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.refl_trans γ

@[simp, grind =]
/-
**Path.Homotopic.Quotient.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Q
uotient`。
形式化陈述：trans_refl (γ : Homotopic.Quotient x₀ x₁) : trans γ (refl x₁) = γ
参数：γ : Homotopic.Quotient x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Path.Homotopic.trans_refl`：trans_refl (p : Path x₀ x₁) : (p.trans (Path.
refl x₁)).Homotopic p
-/
theorem trans_refl (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (refl x₁) = γ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_refl, eq] using Homotopic.trans_refl γ

@[simp, grind =]
/-
**Path.Homotopic.Quotient.trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Q
uotient`。
形式化陈述：trans_symm (γ : Homotopic.Quotient x₀ x₁) : trans γ (symm γ) = refl x₀
参数：γ : Homotopic.Quotient x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Path.Homotopic.trans_symm`：trans_symm (p : Path x₀ x₁) : (p.trans p.symm
).Homotopic (Path.refl x₀)
-/
theorem trans_symm (γ : Homotopic.Quotient x₀ x₁) :
    trans γ (symm γ) = refl x₀ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.trans_symm γ

@[simp, grind =]
/-
**Path.Homotopic.Quotient.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.Q
uotient`。
形式化陈述：symm_trans (γ : Homotopic.Quotient x₀ x₁) : trans (symm γ) γ = refl x₁
参数：γ : Homotopic.Quotient x₀ x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Path.Homotopic.symm_trans`：symm_trans (p : Path x₀ x₁) : (p.symm.trans p
).Homotopic (Path.refl x₁)
-/
theorem symm_trans (γ : Homotopic.Quotient x₀ x₁) :
    trans (symm γ) γ = refl x₁ := by
  induction γ using Quotient.ind with | mk γ =>
  simpa [← mk_trans, ← mk_symm, ← mk_refl, eq] using Homotopic.symm_trans γ

@[simp, grind _=_]
/-
**Path.Homotopic.Quotient.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Path.Homotopic.
Quotient`。
形式化陈述：trans_assoc {x₀ x₁ x₂ x₃ : X} (γ₀ : Homotopic.Quotient x₀ x₁) (γ₁ : Homoto
pic.Quotient x₁ x₂) (γ₂ : Homotopic.Quotient x₂ x₃) : trans (trans γ₀ γ₁) γ₂ = t
rans γ₀ (trans γ₁ γ₂)
参数：γ₀ : Homotopic.Quotient x₀ x₁；γ₁ : Homotopic.Quotient x₁ x₂；γ₂ : Homotopic.Qu
otient x₂ x₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Path.Homotopic.Quotient.ind`：∀ {X : Type u} [inst : TopologicalSpace X] 
{x y : X} {motive : Path.Homotopic.Quotient x y → Prop},   (∀ (a : Path x y), mo
tive (Path.Homoto…
· 使用定理 `Path.Homotopic.trans_assoc`：trans_assoc {x₀ x₁ x₂ x₃ : X} (p : Path x₀ x
₁) (q : Path x₁ x₂) (r : Path x₂ x₃) : ((p.trans q).trans r).Homotopic (p.trans 
(q.trans r))
-/
theorem trans_assoc {x₀ x₁ x₂ x₃ : X}
    (γ₀ : Homotopic.Quotient x₀ x₁)
    (γ₁ : Homotopic.Quotient x₁ x₂)
    (γ₂ : Homotopic.Quotient x₂ x₃) :
    trans (trans γ₀ γ₁) γ₂ = trans γ₀ (trans γ₁ γ₂) := by
  induction γ₀ using Quotient.ind with | mk γ₀ =>
  induction γ₁ using Quotient.ind with | mk γ₁ =>
  induction γ₂ using Quotient.ind with | mk γ₂ =>
  simpa [← mk_trans, eq] using Homotopic.trans_assoc γ₀ γ₁ γ₂

end Quotient

end Homotopic

end Path

/-- The fundamental groupoid of a space `X` is defined to be a wrapper around `X`, and we
subsequently put a `CategoryTheory.Groupoid` structure on it. -/
@[ext]
/-
**FundamentalGroupoid** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_3 → Type u_3
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The fundamental groupoid of a space `X` is defined to be a wrapper around `X`, a
nd we
subsequently put a `CategoryTheory.Groupoid` structure on it.
-/
structure FundamentalGroupoid (X : Type*) where
  /-- View a term of `FundamentalGroupoid X` as a term of `X`. -/
  as : X

namespace FundamentalGroupoid

/-- The equivalence between `X` and the underlying type of its fundamental groupoid.
  This is useful for transferring constructions (instances, etc.)
  from `X` to `πₓ X`. -/
@[simps]
/-
**FundamentalGroupoid.equiv** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroupoid`。
形式化陈述：equiv (X : Type*) : FundamentalGroupoid X ≃ X where toFun x
参数：X : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between `X` and the underlying type of its fundamental groupoid.
  This is useful for transferring constructions (instances, etc.)
  from `X` to `πₓ X`.
-/
def equiv (X : Type*) : FundamentalGroupoid X ≃ X where
  toFun x := x.as
  invFun x := .mk x

@[simp]
/-
**FundamentalGroupoid.isEmpty_iff** 是 Mathlib 中的一个引理，位于命名空间 `FundamentalGroupoid
`。
形式化陈述：isEmpty_iff (X : Type*) : IsEmpty (FundamentalGroupoid X) ↔ IsEmpty X
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.isEmpty_congr`：isEmpty_congr (e : α ≃ β) : IsEmpty α ↔ IsEmpty β
-/
lemma isEmpty_iff (X : Type*) :
    IsEmpty (FundamentalGroupoid X) ↔ IsEmpty X :=
  equiv _ |>.isEmpty_congr
/-
**FundamentalGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [IsEmpty X] :
    IsEmpty (FundamentalGroupoid X) :=
  equiv _ |>.isEmpty

@[simp]
/-
**FundamentalGroupoid.nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `FundamentalGroupoi
d`。
形式化陈述：nonempty_iff (X : Type*) : Nonempty (FundamentalGroupoid X) ↔ Nonempty X
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
-/
lemma nonempty_iff (X : Type*) :
    Nonempty (FundamentalGroupoid X) ↔ Nonempty X :=
  equiv _ |>.nonempty_congr
/-
**FundamentalGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [Nonempty X] :
    Nonempty (FundamentalGroupoid X) :=
  equiv _ |>.nonempty

@[simp]
/-
**FundamentalGroupoid.subsingleton_iff** 是 Mathlib 中的一个引理，位于命名空间 `FundamentalGro
upoid`。
形式化陈述：subsingleton_iff (X : Type*) : Subsingleton (FundamentalGroupoid X) ↔ Subs
ingleton X
参数：X : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton_congr`：subsingleton_congr (e : α ≃ β) : Subsingleton 
α ↔ Subsingleton β
-/
lemma subsingleton_iff (X : Type*) :
    Subsingleton (FundamentalGroupoid X) ↔ Subsingleton X :=
  equiv _ |>.subsingleton_congr
/-
**FundamentalGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (X : Type*) [Subsingleton X] :
    Subsingleton (FundamentalGroupoid X) :=
  equiv _ |>.subsingleton

-- TODO: It seems that `Equiv.nontrivial_congr` doesn't exist.
-- Once it is added, please add the corresponding lemma and instance.
/-
**FundamentalGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Type*} [Inhabited X] : Inhabited (FundamentalGroupoid X) :=
  ⟨⟨default⟩⟩
/-
**FundamentalGroupoid.** 是 Mathlib 中的一个实例，位于命名空间 `FundamentalGroupoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Groupoid (FundamentalGroupoid X) where
  Hom x y := Path.Homotopic.Quotient x.as y.as
  id x := ⟦Path.refl x.as⟧
  comp := Path.Homotopic.Quotient.trans
  id_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.reflTrans f⟩
  comp_id := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨Path.Homotopy.transRefl f⟩
  assoc := by rintro _ _ _ _ ⟨f⟩ ⟨g⟩ ⟨h⟩; exact Quotient.sound ⟨Path.Homotopy.transAssoc f g h⟩
  inv := Quotient.lift (fun f ↦ ⟦f.symm⟧) (by rintro a b ⟨h⟩; exact Quotient.sound ⟨h.symm₂⟩)
  inv_comp := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflSymmTrans f).symm⟩
  comp_inv := by rintro _ _ ⟨f⟩; exact Quotient.sound ⟨(Path.Homotopy.reflTransSymm f).symm⟩
/-
**FundamentalGroupoid.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroupoid`。
形式化陈述：comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = 
p.trans q
参数：x y z : FundamentalGroupoid X；p : x ⟶ y；q : y ⟶ z。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_eq (x y z : FundamentalGroupoid X) (p : x ⟶ y) (q : y ⟶ z) : p ≫ q = p.trans q := rfl
/-
**FundamentalGroupoid.id_eq_path_refl** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGrou
poid`。
形式化陈述：id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x.as⟧
参数：x : FundamentalGroupoid X。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_eq_path_refl (x : FundamentalGroupoid X) : 𝟙 x = ⟦Path.refl x.as⟧ := rfl

/-- The functor on fundamental groupoid induced by a continuous map. -/
/-
**FundamentalGroupoid.map** 是 Mathlib 中的一个定义，位于命名空间 `FundamentalGroupoid`。
形式化陈述：{X : Type u_1} →   {Y : Type u_2} →     [inst : TopologicalSpace X] →     
  [inst_1 : TopologicalSpace Y] → C(X, Y) → CategoryTheory.Functor (FundamentalG
roupoid X) (FundamentalGroupoid Y)
参数：X, Y；FundamentalGroupoid X；FundamentalGroupoid Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor on fundamental groupoid induced by a continuous map.
-/
@[simps] def map (f : C(X, Y)) : FundamentalGroupoid X ⥤ FundamentalGroupoid Y where
  obj x := ⟨f x.as⟩
  map p := p.map f
  map_id _ := rfl
  map_comp := by rintro _ _ _ ⟨p⟩ ⟨q⟩; exact congr_arg Quotient.mk'' (p.map_trans q f.continuous)

@[simp]
/-
**FundamentalGroupoid.map_id** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroupoid`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X],   FundamentalGroupoid.map (C
ontinuousMap.id X) = CategoryTheory.Functor.id (FundamentalGroupoid X)
参数：ContinuousMap.id X；FundamentalGroupoid X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem map_id : map (.id X) = 𝟭 _ := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

@[simp]
/-
**FundamentalGroupoid.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroupoid`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {Z : Type u_3}   [inst_2 : TopologicalSpace Z] (g : C(Y, Z)) (f 
: C(X, Y)),   FundamentalGroupoid.map (g.comp f) = (FundamentalGroupoid.map f).c
omp (FundamentalGroupoid.map g)
参数：g : C(Y, Z)；f : C(X, Y)；g.comp f；FundamentalGroupoid.map f；FundamentalGroupoi
d.map g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem map_comp {Z : Type*} [TopologicalSpace Z] (g : C(Y, Z)) (f : C(X, Y)) :
    map (g.comp f) = map f ⋙ map g := by
  simp only [map]; congr; ext x y ⟨p⟩; rfl

/-- The functor sending a topological space `X` to its fundamental groupoid. -/
/-
**FundamentalGroupoid.fundamentalGroupoidFunctor** 是 Mathlib 中的一个定义，位于命名空间 `Fund
amentalGroupoid`。
形式化陈述：fundamentalGroupoidFunctor : TopCat ⥤ Grpd where obj X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a topological space `X` to its fundamental groupoid.
-/
def fundamentalGroupoidFunctor : TopCat ⥤ Grpd where
  obj X := { α := FundamentalGroupoid X }
  map f := map f.hom
  map_id _ := FundamentalGroupoid.map_id
  map_comp _ _ := FundamentalGroupoid.map_comp _ _

@[inherit_doc] scoped notation "π" => FundamentalGroupoid.fundamentalGroupoidFunctor

/-- The fundamental groupoid of a topological space. -/
scoped notation "πₓ" => FundamentalGroupoid.fundamentalGroupoidFunctor.obj

/-- The functor between fundamental groupoids induced by a continuous map. -/
scoped notation "πₘ" => FundamentalGroupoid.fundamentalGroupoidFunctor.map

/-
**FundamentalGroupoid.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `FundamentalGroupoid`。
形式化陈述：map_eq {X Y : TopCat.{u}} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Qu
otient x₀ x₁) : (πₘ (TopCat.ofHom f)).map p = p.map f
参数：f : C(X, Y)；p : Path.Homotopic.Quotient x₀ x₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq {X Y : TopCat.{u}} {x₀ x₁ : X} (f : C(X, Y)) (p : Path.Homotopic.Quotient x₀ x₁) :
    (πₘ (TopCat.ofHom f)).map p = p.map f := rfl

/-- Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space. -/
/-
**FundamentalGroupoid.toTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroupoid`。
形式化陈述：toTop {X : TopCat.{u}} (x : πₓ X) : X
参数：x : πₓ X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by converting a point in a groupoid back to a point in
the underlying topological space.
-/
abbrev toTop {X : TopCat.{u}} (x : πₓ X) : X := x.as

/-- Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space. -/
/-
**FundamentalGroupoid.fromTop** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroupoid`。
形式化陈述：fromTop {X : TopCat.{u}} (x : X) : πₓ X
参数：x : X。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by converting a point in a topological space to a
point in the fundamental groupoid of that space.
-/
abbrev fromTop {X : TopCat.{u}} (x : X) : πₓ X := ⟨x⟩

/-- Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `Path.Homotopic.Quotient`). -/
/-
**FundamentalGroupoid.toPath** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroupoid`。
形式化陈述：toPath {X : TopCat.{u}} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) : Path.Homotopic.Quot
ient x₀.as x₁.as
参数：p : x₀ ⟶ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by converting an arrow in the fundamental groupoid of
a topological space back to a path in that space (i.e., `Path.Homotopic.Quotient
`).
-/
abbrev toPath {X : TopCat.{u}} {x₀ x₁ : πₓ X} (p : x₀ ⟶ x₁) :
    Path.Homotopic.Quotient x₀.as x₁.as :=
  p

/-- Help the typechecker by converting a path in a topological space to an arrow in the
fundamental groupoid of that space. -/
/-
**FundamentalGroupoid.fromPath** 是 Mathlib 中的一个缩写定义，位于命名空间 `FundamentalGroupoid`
。
形式化陈述：fromPath {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) : FundamentalGrou
poid.mk x₀ ⟶ FundamentalGroupoid.mk x₁
参数：p : Path.Homotopic.Quotient x₀ x₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Help the typechecker by converting a path in a topological space to an arrow in 
the
fundamental groupoid of that space.
-/
abbrev fromPath {x₀ x₁ : X} (p : Path.Homotopic.Quotient x₀ x₁) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x₁ := p

/-- Two paths are equal in the fundamental groupoid if and only if they are homotopic. -/
/-
**FundamentalGroupoid.fromPath_eq_iff_homotopic** 是 Mathlib 中的一个定理，位于命名空间 `Funda
mentalGroupoid`。
形式化陈述：fromPath_eq_iff_homotopic {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁) : 
fromPath (Path.Homotopic.Quotient.mk f) = fromPath (Path.Homotopic.Quotient.mk g
) ↔ f.Homotopic g
参数：f : Path x₀ x₁；g : Path x₀ x₁。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Quotient.sound`：∀ {α : Sort u} {s : Setoid α} {a b : α}, a ≈ b → ⟦a⟧ = ⟦
b⟧

--- 原说明 ---
Two paths are equal in the fundamental groupoid if and only if they are homotopi
c.
-/
theorem fromPath_eq_iff_homotopic {x₀ x₁ : X} (f : Path x₀ x₁) (g : Path x₀ x₁) :
    fromPath (Path.Homotopic.Quotient.mk f) = fromPath (Path.Homotopic.Quotient.mk g) ↔
      f.Homotopic g :=
  ⟨fun ih ↦ Quotient.exact ih, fun h ↦ Quotient.sound h⟩
/-
**FundamentalGroupoid.eqToHom_eq** 是 Mathlib 中的一个引理，位于命名空间 `FundamentalGroupoid`
。
形式化陈述：eqToHom_eq {x₀ x₁ : X} (h : x₀ = x₁) : eqToHom congr(mk $h) = (Path.Homoto
pic.Quotient.refl x₁).cast h rfl
参数：h : x₀ = x₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma eqToHom_eq {x₀ x₁ : X} (h : x₀ = x₁) :
    eqToHom congr(mk $h) = (Path.Homotopic.Quotient.refl x₁).cast h rfl := by subst h; rfl

@[reassoc]
/-
**FundamentalGroupoid.conj_eqToHom** 是 Mathlib 中的一个引理，位于命名空间 `FundamentalGroupoi
d`。
形式化陈述：conj_eqToHom {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = 
x) (hy : y' = y) : eqToHom congr(mk $hx) ≫ p ≫ eqToHom congr(mk $hy.symm) = p.ca
st hx hy
参数：hx : x' = x；hy : y' = y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Path.Homotopic.Quotient.cast_rfl_rfl`：cast_rfl_rfl {x y : X} (γ : Homoto
pic.Quotient x y) : γ.cast rfl rfl = γ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma conj_eqToHom {x y x' y' : X} {p : Path.Homotopic.Quotient x y} (hx : x' = x) (hy : y' = y) :
    eqToHom congr(mk $hx) ≫ p ≫ eqToHom congr(mk $hy.symm) = p.cast hx hy := by
  subst hx hy; simp

end FundamentalGroupoid

