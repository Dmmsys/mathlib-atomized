/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.LocalAtTarget

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` and `(· ^ n)` (for `n ≠ 0`) are a covering map on `{0}ᶜ`.
We also show that any complex polynomial is a covering map on the set of regular values.
-/

public section

open Topology

namespace Complex

/-
**Complex.isAddQuotientCoveringMap_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isAddQuotientCoveringMap_exp : IsAddQuotientCoveringMap (fun z : Complex =
> (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0})) (AddSubgroup.zmultiples (2 * R
eal.pi * I))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup`：∀ {E : T
ype u_1} {X : Type u_2} [inst : TopologicalSpace E] [inst_1 : TopologicalSpace X
] {f : E → X},   Topology.IsQuotientMap f →     ∀ [i…
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `IsOpenMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f → Continuo
us f → Functi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Topology.IsOpenEmbedding.isOpenMap_iff`：∀ {X : Type u_1} {Y : Type u_2} 
{Z : Type u_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : T
opologicalSpace Y] [inst_2 :…
· 使用定理 `IsOpen.isOpenEmbedding_subtypeVal`：IsOpen.isOpenEmbedding_subtypeVal {s 
: Set X} (hs : IsOpen s) : IsOpenEmbedding ((↑) : s -> X)
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.isOpenMap_exp`：isOpenMap_exp : IsOpenMap exp
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Complex.exp_log`：exp_log {x : Complex} (hx : x != 0) : exp (log x) = x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
（共 31 条，此处仅展示前 30 条）
-/
theorem isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}))
      (AddSubgroup.zmultiples (2 * Real.pi * I)) := by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/-- `exp : ℂ → ℂ \ {0}` is a covering map. -/
/-
**Complex.isCoveringMap_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCoveringMap_exp : IsCoveringMap fun z : Complex => (⟨_, z.exp_ne_zero⟩ :
 {z : Complex // z != 0})
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAddQuotientCoveringMap.isCoveringMap`：∀ {E : Type u_1} {X : Type u_2} 
[inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] (f : E → X) (G : Type 
u_3)   [inst_2 : AddGroup G]…
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Complex.isAddQuotientCoveringMap_exp`：isAddQuotientCoveringMap_exp : IsA
ddQuotientCoveringMap (fun z : Complex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // 
z != 0})) (AddSubgroup.zmu…

--- 原说明 ---
`exp : ℂ → ℂ \ {0}` is a covering map.
-/
theorem isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap
/-
**Complex.isCoveringMapOn_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCoveringMapOn.of_isCoveringMap_subtype`：IsCoveringMapOn.of_isCoveringM
ap_subtype {s : Set X} (hs : IsOpen s) {f : E -> X} (h : forall x, f x in s) (hf
 : IsCoveringMap fun x => (⟨f …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Complex.exp_ne_zero`：exp_ne_zero : exp x != 0
· 使用定理 `Complex.isCoveringMap_exp`：isCoveringMap_exp : IsCoveringMap fun z : Com
plex => (⟨_, z.exp_ne_zero⟩ : {z : Complex // z != 0})
-/
theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex

section

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/-
**Polynomial.isCoveringMapOn_eval** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) : IsCoveringMapOn p.eval (p.eva
l '' {k | p.derivative.eval k = 0})ᶜ
参数：p : 𝕜[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn`：IsClosedMap.isCoveri
ngMapOn_of_isLocalHomeomorphOn [T2Space E] (hf : IsClosedMap f) (hs : forall x i
n s, (f ⁻¹' {x}).Finite) (h : IsLocalHom…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Polynomial.isClosedMap_eval`：isClosedMap_eval [ProperSpace R] (p : R[X])
 : IsClosedMap p.eval
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.derivative_C`：derivative_C {a : R} : derivative (C a) = 0
· 使用定理 `Polynomial.eval_zero`：eval_zero : (0 : R[X]).eval x = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.preimage_eval_singleton`：preimage_eval_singleton (hp : p != C
 a) : p.eval ⁻¹' {a} = (p - C a).rootSet R
· 使用定理 `Polynomial.rootSet_finite`：rootSet_finite (p : T[X]) (S : Type*) [CommRi
ng S] [IsDomain S] [Algebra T S] : (p.rootSet S).Finite
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `complete_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [ProperS
pace α], CompleteSpace α
· 使用定理 `HasStrictDerivAt.hasStrictFDerivAt_equiv`：HasStrictDerivAt.hasStrictFDer
ivAt_equiv {f : 𝕜 -> 𝕜} {f' x : 𝕜} (hf : HasStrictDerivAt f f' x) (hf' : f' != 0
) : HasStrictFDerivAt f (Conti…
（共 32 条，此处仅展示前 30 条）
-/
theorem Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) :
    IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx ↦ ?_)
    fun x hx ↦ ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h ↦ hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [preimage_eval_singleton ne] using rootSet_finite ..
/-
**isCoveringMapOn_npow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoveringMapOn_npow (n : Nat) (hn : (n : 𝕜) != 0) : IsCoveringMapOn (fun 
x : 𝕜 => x ^ n) {0}ᶜ
参数：n : Nat；hn : (n : 𝕜) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsCoveringMapOn.mono`：mono {t : Set X} (hf : IsCoveringMapOn f s) (ht : 
t subseteq s) : IsCoveringMapOn f t
· 使用定理 `Polynomial.isCoveringMapOn_eval`：Polynomial.isCoveringMapOn_eval (p : 𝕜[
X]) : IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.derivative_X_pow`：derivative_X_pow (n : Nat) : derivative (X 
^ n : R[X]) = C (n : R) * X ^ (n - 1)
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 33 条，此处仅展示前 30 条）
-/
theorem isCoveringMapOn_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : 𝕜 ↦ x ^ n) {0}ᶜ := by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h ↦ _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n ≠ 0 by aesop] using fun _ ↦ Ne.symm h

/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`). -/
/-
**isCoveringMap_npow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoveringMap_npow (n : Nat) (hn : (n : 𝕜) != 0) : IsCoveringMap fun x : {
x : 𝕜 // x != 0} => (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x != 0})
参数：n : Nat；hn : (n : 𝕜) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsCoveringMap.comp_homeomorph`：comp_homeomorph {E'} [TopologicalSpace E'
] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g)
· 使用定理 `IsCoveringMapOn.isCoveringMap_restrictPreimage`：IsCoveringMapOn.isCoveri
ngMap_restrictPreimage (hf : IsCoveringMapOn f s) : IsCoveringMap (s.restrictPre
image f)
· 使用定理 `isCoveringMapOn_npow`：isCoveringMapOn_npow (n : Nat) (hn : (n : 𝕜) != 0)
 : IsCoveringMapOn (fun x : 𝕜 => x ^ n) {0}ᶜ

--- 原说明 ---
`(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`).
-/
theorem isCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x ≠ 0}) _) using 1
  ext; simp [show n ≠ 0 by aesop]

set_option backward.isDefEq.respectTransparency false in
/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`). -/
/-
**isCoveringMap_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoveringMap_zpow (n : Int) (hn : (n : 𝕜) != 0) : IsCoveringMap fun x : {
x : 𝕜 // x != 0} => (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 // x != 0})
参数：n : Int；hn : (n : 𝕜) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isCoveringMap_npow`：isCoveringMap_npow (n : Nat) (hn : (n : 𝕜) != 0) : I
sCoveringMap fun x : {x : 𝕜 // x != 0} => (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 /
/ x != 0…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `IsCoveringMap.comp_homeomorph`：comp_homeomorph {E'} [TopologicalSpace E'
] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g)
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n

--- 原说明 ---
`(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`).
-/
theorem isCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert! isCoveringMap_npow n _ <;> aesop
  · convert! (isCoveringMap_npow n _).comp_homeomorph (.inv₀ 𝕜)
    · simp [Homeomorph.inv₀]
    · simpa using hn
/-
**isCoveringMapOn_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCoveringMapOn_zpow (n : Int) (hn : (n : 𝕜) != 0) : IsCoveringMapOn (fun 
x : 𝕜 => x ^ n) {0}ᶜ
参数：n : Int；hn : (n : 𝕜) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `zpow_eq_zero_iff`：zpow_eq_zero_iff {n : Int} (hn : n != 0) : a ^ n = 0 ↔
 a = 0
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCoveringMapOn.of_isCoveringMap_restrictPreimage`：IsCoveringMapOn.of_is
CoveringMap_restrictPreimage (hs : IsOpen s) (hfs : IsOpen (f ⁻¹' s)) (hf : IsCo
veringMap (s.restrictPreimage f)) : IsC…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.isOpen_compl`：∀ {X : Type u} {inst : TopologicalSpace X} {s : S
et X} [self : IsClosed s], IsOpen sᶜ
· 使用定理 `isClosed_singleton`：isClosed_singleton [T1Space X] {x : X} : IsClosed ({
x} : Set X)
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `IsCoveringMap.comp_homeomorph`：comp_homeomorph {E'} [TopologicalSpace E'
] (g : E' ≃ₜ E) : IsCoveringMap (f ∘ g)
· 使用定理 `isCoveringMap_zpow`：isCoveringMap_zpow (n : Int) (hn : (n : 𝕜) != 0) : I
sCoveringMap fun x : {x : 𝕜 // x != 0} => (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 
// x != …
-/
theorem isCoveringMapOn_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : 𝕜 ↦ x ^ n) {0}ᶜ := by
  have (x : 𝕜) : x ^ n = 0 ↔ x = 0 := zpow_eq_zero_iff (by aesop)
  refine .of_isCoveringMap_restrictPreimage _ (by simp) ?_ ?_
  · convert isClosed_singleton (x := (0 : 𝕜)).isOpen_compl
    ext; simp [this]
  · convert! (isCoveringMap_zpow n hn).comp_homeomorph (.setCongr _) using 1
    ext; simpa using! (this _).not

attribute [-instance] Units.mulAction'
/-
**isQuotientCoveringMap_npow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientCoveringMap_npow (n : Nat) (hn : (n : 𝕜) != 0) (surj : (fun x : 
𝕜 => x ^ n).Surjective) : IsQuotientCoveringMap (fun x : 𝕜ˣ => x ^ n) (powMonoid
Hom (α
参数：n : Nat；hn : (n : 𝕜) != 0；surj : (fun x : 𝕜 => x ^ n).Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rootsOfUnity_eq_ker`：rootsOfUnity_eq_ker : rootsOfUnity k M = (powMonoid
Hom k).ker
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `IsClosedMap.isQuotientMap`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [
inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → Cont
inuous f → Func…
· 使用定理 `IsClosedMap.restrictPreimage`：IsClosedMap.restrictPreimage (H : IsClosed
Map f) (s : Set β) : IsClosedMap (s.restrictPreimage f)
· 使用定理 `isClosedMap_pow`：∀ (R : Type u_2) [inst : NormedRing R] [IsAbsoluteValue
 norm] [ProperSpace R] (n : ℕ), IsClosedMap fun x => x ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Continuous.restrictPreimage`：Continuous.restrictPreimage {f : X -> Y} {s
 : Set Y} (h : Continuous f) : Continuous (s.restrictPreimage f)
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Function.Surjective.restrictPreimage`：∀ {α : Type u_1} {β : Type u_2} (t
 : Set β) {f : α → β},   Function.Surjective f → Function.Surjective (t.restrict
Preimage f)
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Topology.IsQuotientMap.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u
_3} {f : X → Y} {g : Y → Z} [inst : TopologicalSpace X]   [inst_1 : TopologicalS
pace Y] [inst_2 :…
（共 43 条，此处仅展示前 30 条）
-/
theorem isQuotientCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜 ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (powMonoidHom (α := 𝕜ˣ) n).ker := by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ ↦ x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuotientMap.comp this).comp (e.trans (.ofEqSubtypes _)).isQuotientMap
    · exact (e.left_inv _).symm
    · ext; simp [NeZero.ne]
  refine this.isQuotientCoveringMap_of_subgroup _
    (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity ..))) ?_
  simp [mul_pow, mul_inv_eq_one, eq_comm]
/-
**Complex.isQuotientCoveringMap_npow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (n : ℕ) [NeZero n], IsQuotientCoveringMap (fun z => z ^ n) ↥(powMonoidHo
m n).ker
参数：n : ℕ；fun z => z ^ n；powMonoidHom n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isQuotientCoveringMap_npow`：isQuotientCoveringMap_npow (n : Nat) (hn : (
n : 𝕜) != 0) (surj : (fun x : 𝕜 => x ^ n).Surjective) : IsQuotientCoveringMap (f
un x : 𝕜ˣ => x ^…
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Complex.cpow_nat_inv_pow`：cpow_nat_inv_pow (x : Complex) {n : Nat} (hn :
 n != 0) : (x ^ (n⁻¹ : Complex)) ^ n = x
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
protected theorem Complex.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (fun z : ℂˣ ↦ z ^ n) (powMonoidHom (α := ℂˣ) n).ker :=
  isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ ↦ ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩
/-
**isQuotientCoveringMap_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isQuotientCoveringMap_zpow (n : Int) (hn : (n : 𝕜) != 0) (surj : (fun x : 
𝕜 => x ^ n).Surjective) : IsQuotientCoveringMap (fun x : 𝕜ˣ => x ^ n) (zpowGroup
Hom (α
参数：n : Int；hn : (n : 𝕜) != 0；surj : (fun x : 𝕜 => x ^ n).Surjective。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `isQuotientCoveringMap_npow`：isQuotientCoveringMap_npow (n : Nat) (hn : (
n : 𝕜) != 0) (surj : (fun x : 𝕜 => x ^ n).Surjective) : IsQuotientCoveringMap (f
un x : 𝕜ˣ => x ^…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpowGroupHom_apply`：∀ {α : Type u_1} [inst : DivisionCommMonoid α] (n : 
ℤ) (x : α), (zpowGroupHom n) x = x ^ n
· 使用定理 `zpow_neg`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a 
^ (-n) = (a ^ n)⁻¹
· 使用定理 `powMonoidHom_apply`：∀ {α : Type u_1} [inst : CommMonoid α] (n : ℕ) (x : 
α), (powMonoidHom n) x = x ^ n
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsTopologicalGroup.toContinuousInv`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousInv G
· 使用定理 `Units.instIsTopologicalGroupOfContinuousMul`：∀ {α : Type u} [inst : Mono
id α] [inst_1 : TopologicalSpace α] [ContinuousMul α], IsTopologicalGroup αˣ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `Units.val_inv_eq_inv_val`：∀ {α : Type u} [inst : DivisionMonoid α] (u : 
αˣ), ↑u⁻¹ = (↑u)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsQuotientCoveringMap.homeomorph_comp`：∀ {E : Type u_1} {X : Type u_2} [
inst : TopologicalSpace E] [inst_1 : TopologicalSpace X] {f : E → X} {G : Type u
_3}   [inst_2 : Group G] [i…
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
（共 34 条，此处仅展示前 30 条）
-/
theorem isQuotientCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜 ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (zpowGroupHom (α := 𝕜ˣ) n).ker := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by aesop) (by simpa using surj)
  rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
  convert (isQuotientCoveringMap_npow n (by aesop) _).homeomorph_comp (.inv 𝕜ˣ)
  · ext; simp
  convert! inv_involutive.surjective.comp surj; simp

end

