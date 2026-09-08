/-
Copyright (c) 2026 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/

module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# The radical of a quadratic form

We define the radical of a quadratic form. This is a standard construction if 2 is invertible
in the coefficient ring, but is more fiddly otherwise. We follow the account in
Chapter II, §7 of [elman-karpenko-merkurjev-2008].
-/

open Finset QuadraticMap

@[expose] public noncomputable section

namespace QuadraticMap

variable {R M M' P : Type*} [AddCommGroup M] [AddCommGroup M'] [AddCommGroup P]
  [CommRing R] [Module R M] [Module R M'] [Module R P] (Q : QuadraticMap R M P)

/-- The radical of a quadratic form `Q` on `M`.

This is the largest submodule `N` such that `Q` lifts to a quadratic form on `M ⧸ N`; see
`Submodule.le_radical_iff` for this characterization.

See also [elman-karpenko-merkurjev-2008], Chapter II, §7. -/
/-
**QuadraticMap.radical** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：radical : Submodule R M where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The radical of a quadratic form `Q` on `M`.

This is the largest submodule `N` such that `Q` lifts to a quadratic form on `M 
⧸ N`; see
`Submodule.le_radical_iff` for this characterization.

See also [elman-karpenko-merkurjev-2008], Chapter II, §7.
-/
def radical : Submodule R M where
  carrier := {x : M | Q x = 0 ∧ QuadraticMap.polarBilin Q x = 0}
  zero_mem' := by simp
  smul_mem' a x hx := by simp [QuadraticMap.map_smul, hx.1, hx.2]
  add_mem' := fun {x y} hx hy ↦ by
    refine ⟨?_, by simp [hx.2, hy.2]⟩
    have := congr_arg (· y) hx.2
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
      LinearMap.zero_apply, sub_sub, sub_eq_zero] at this
    rw [this, hx.1, hy.1, zero_add]

variable {Q}
/-
**QuadraticMap.mem_radical_iff'** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：mem_radical_iff' {m : M} : m in Q.radical ↔ Q m = 0 ∧ forall n : M, Q (m +
 n) = Q n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QuadraticMap.polar_add_left`：polar_add_left (x x' y : M) : polar Q (x + 
x') y = polar Q x y + polar Q x' y
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
· 使用定理 `QuadraticMap.polar_add_right`：polar_add_right (x y y' : M) : polar Q x (
y + y') = polar Q x y + polar Q x y'
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma mem_radical_iff' {m : M} :
    m ∈ Q.radical ↔ Q m = 0 ∧ ∀ n : M, Q (m + n) = Q n := by
  simp +contextual [radical, QuadraticMap.polarBilin, LinearMap.ext_iff,
    QuadraticMap.polar, sub_sub, sub_eq_zero]

/-- The radical of a quadratic form is preserved by isometry equivalences. -/
/-
**QuadraticMap.IsometryEquiv.map_radical** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap
.IsometryEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M' : Type u_3} {P : Type u_4} [inst : Add
CommGroup M] [inst_1 : AddCommGroup M']   [inst_2 : AddCommGroup P] [inst_3 : Co
mmRing R] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R M']   [inst_6 :
 _root_.Module R P] {Q : QuadraticMap R M P} {Q' : QuadraticMap R M' P} (e : Q.I
sometryEquiv Q'),   Submodule.map (↑e.toLinearEquiv) Q.radical = Q'.radical
参数：e : Q.IsometryEquiv Q'；↑e.toLinearEquiv。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.IsometryEquiv.map_app`：map_app (f : Q₁.IsometryEquiv Q₂) (m
 : M₁) : Q₂ (f m) = Q₁ m
· 使用定理 `QuadraticMap.IsometryEquiv.apply_symm_apply`：∀ {R : Type u_2} {M₁ : Type
 u_5} {M₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCommMo
noid M₁]   [inst_2 : AddCommMonoi…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `QuadraticMap.IsometryEquiv.instLinearEquivClass`：∀ {R : Type u_2} {M₁ : 
Type u_5} {M₂ : Type u_6} {N : Type u_9} [inst : CommSemiring R] [inst_1 : AddCo
mmMonoid M₁]   [inst_2 : AddCommMonoi…
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The radical of a quadratic form is preserved by isometry equivalences.
-/
@[simp] lemma IsometryEquiv.map_radical {Q' : QuadraticMap R M' P}
    (e : IsometryEquiv Q Q') : Q.radical.map e.toLinearMap = Q'.radical := by
  ext
  simp [mem_radical_iff', ← e.map_app, -map_app, e.toEquiv.forall_congr_left]

/-- The rank of the radical of a quadratic map is invariant under equivalences. -/
/-
**QuadraticMap.Equivalent.rank_radical_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMa
p.Equivalent`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {M' : Type u_3} {P : Type u_4} [inst : Add
CommGroup M] [inst_1 : AddCommGroup M']   [inst_2 : AddCommGroup P] [inst_3 : Co
mmRing R] [inst_4 : _root_.Module R M] [inst_5 : _root_.Module R M']   [inst_6 :
 _root_.Module R P] {Q : QuadraticMap R M P} {Q' : QuadraticMap R M' P},   Q.Equ
ivalent Q' → Module.finrank R ↥Q.radical = Module.finrank R ↥Q'.radical
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.IsometryEquiv.map_radical`：∀ {R : Type u_1} {M : Type u_2} 
{M' : Type u_3} {P : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup M'
]   [inst_2 : AddCommGroup P…
· 使用定理 `LinearEquiv.finrank_map_eq`：finrank_map_eq (f : M ≃ₗ[R] N) (p : Submodul
e R M) : finrank R (p.map (f : M ->ₗ[R] N)) = finrank R p

--- 原说明 ---
The rank of the radical of a quadratic map is invariant under equivalences.
-/
lemma Equivalent.rank_radical_eq {Q' : QuadraticMap R M' P} (h : Equivalent Q Q') :
    Module.finrank R Q.radical = Module.finrank R Q'.radical := by
  obtain ⟨e⟩ := h
  rw [← e.map_radical, LinearEquiv.finrank_map_eq]

-- auxiliary lemma for lifting quadratic maps to quotients
/-
**QuadraticMap.lift_aux** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lift_aux {N : Submodule R M} (hN : N ≤ Q.radical)
    (m m' : M) (hmm' : Submodule.quotientRel N m m') : Q m = Q m' := by
  rw [Submodule.quotientRel_def] at hmm'
  rw [(by simp : m = m' + (m - m')), QuadraticMap.map_add Q m' (m - m'),
    (hN hmm').1, add_zero, polar_comm, ← polarBilin_apply_apply]
  simp [(hN hmm').2]

variable (Q) in
/-- Lift a quadratic map on `M` to `M ⧸ N`, where `N` is contained in the radical. -/
/-
**QuadraticMap.lift** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {P : Type u_4} →       [inst : Add
CommGroup M] →         [inst_1 : AddCommGroup P] →           [inst_2 : CommRing 
R] →             [inst_3 : _root_.Module R M] →               [inst_4 : _root_.M
odule R P] →                 (Q : QuadraticMap R M P) → (N : Submodule R M) → N 
≤ Q.radical → QuadraticMap R (M ⧸ N) P
参数：Q : QuadraticMap R M P；N : Submodule R M；M ⧸ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a quadratic map on `M` to `M ⧸ N`, where `N` is contained in the radical.
-/
protected def lift (N : Submodule R M) (hN : N ≤ Q.radical) : QuadraticMap R (M ⧸ N) P := by
  refine QuadraticMap.mk (Quotient.lift Q <| by exact lift_aux hN)
    (fun a m ↦ m.inductionOn (Q.map_smul a)) ?_
  use Q.polarBilin.liftQ₂ N N (fun n hn ↦ (hN hn).2) (fun n hn ↦ ?_)
  · simp only [Submodule.Quotient.forall]
    exact QuadraticMap.map_add Q -- remarkably, this works
  · simp_rw [LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.flip_apply,
      polarBilin_apply_apply, polar_comm, ← polarBilin_apply_apply, (hN hn).2, forall_true_iff]

@[simp]
/-
**QuadraticMap.lift_mk** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：lift_mk {N : Submodule R M} (hN : N <= Q.radical) (m : M) : Q.lift N hN (S
ubmodule.Quotient.mk m) = Q m
参数：hN : N <= Q.radical；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_mk {N : Submodule R M} (hN : N ≤ Q.radical) (m : M) :
    Q.lift N hN (Submodule.Quotient.mk m) = Q m :=
  rfl

/--
Universal property of the radical of a quadratic form:
`Q.radical` is the largest subspace `N` such that
`Q` factors through a quadratic form on `M ⧸ N`. -/
/-
**QuadraticMap.le_radical_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：le_radical_iff {N : Submodule R M} : N <= Q.radical ↔ exists Q' : Quadrati
cMap R (M ⧸ N) P, Q'.comp N.mkQ = Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `AddSubsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Add M] (carrier 
carrier_1 : Set M) (e_carrier : carrier = carrier_1)   (add_mem' : ∀ {a b : M}, 
a ∈ carrier → b ∈ c…
· 使用定理 `AddSubmonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : AddZeroClass M] (to
AddSubsemigroup toAddSubsemigroup_1 : AddSubsemigroup M)   (e_toAddSubsemigroup 
: toAddSubsemigr…
· 使用定理 `Submodule.mk.congr_simp`：∀ {R : Type u} {M : Type v} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (toAddSubmonoid toAdd
Submonoid_1 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
Universal property of the radical of a quadratic form:
`Q.radical` is the largest subspace `N` such that
`Q` factors through a quadratic form on `M ⧸ N`.
-/
lemma le_radical_iff {N : Submodule R M} :
    N ≤ Q.radical ↔ ∃ Q' : QuadraticMap R (M ⧸ N) P, Q'.comp N.mkQ = Q := by
  constructor
  · exact fun hN ↦ ⟨Q.lift N hN, rfl⟩
  · rintro ⟨Q', rfl⟩ m hm
    simp [radical, (Submodule.Quotient.mk_eq_zero _).mpr hm, LinearMap.ext_iff, polar]

/-- The radical of a quadratic map is contained in the kernel of its polar bilinear map.

See `radical_eq_ker_polarBilin` for the equality when 2 is invertible in the
coefficient ring. -/
/-
**QuadraticMap.radical_le_ker_polarBilin** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap
`。
形式化陈述：radical_le_ker_polarBilin : Q.radical <= Q.polarBilin.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
The radical of a quadratic map is contained in the kernel of its polar bilinear 
map.

See `radical_eq_ker_polarBilin` for the equality when 2 is invertible in the
coefficient ring.
-/
lemma radical_le_ker_polarBilin : Q.radical ≤ Q.polarBilin.ker := by
  intro m
  simp +contextual [mem_radical_iff', LinearMap.ext_iff, QuadraticMap.polar]

/--
A quadratic map is said to be **nondegenerate** if its radical is 0,
and the radical of its associated polar form has rank ≤ 1.
(The second condition is automatic if 2 is invertible in `R`, but not in general.)

See [elman-karpenko-merkurjev-2008], Chapter II, §7.
-/
/-
**QuadraticMap.Nondegenerate** 是 Mathlib 中的一个归纳类型，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {P : Type u_4} →       [inst : Add
CommGroup M] →         [inst_1 : AddCommGroup P] →           [inst_2 : CommRing 
R] →             [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R P] → {
Q : QuadraticMap R M P} → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quadratic map is said to be **nondegenerate** if its radical is 0,
and the radical of its associated polar form has rank ≤ 1.
(The second condition is automatic if 2 is invertible in `R`, but not in general
.)

See [elman-karpenko-merkurjev-2008], Chapter II, §7.
-/
structure Nondegenerate : Prop where
  radical_eq_bot : Q.radical = ⊥
  rank_rad_polar_le : Module.rank R Q.polarBilin.ker ≤ 1

section InvertibleTwo

variable [Invertible (2 : R)]

/--
If `2` is invertible in the coefficient ring,
the radical of a quadratic map is the kernel of its polar bilinear map. -/
/-
**QuadraticMap.radical_eq_ker_polarBilin** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap
`。
形式化陈述：radical_eq_ker_polarBilin : Q.radical = Q.polarBilin.ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `IsUnit.smul_eq_zero`：∀ {G : Type u_2} {M : Type u_3} [inst : Monoid G] [
inst_1 : AddMonoid M] [inst_2 : DistribMulAction G M] {u : G}   {x : M}, IsUnit 
u → (u • …
· 使用定理 `isUnit_of_invertible`：isUnit_of_invertible [Monoid α] (a : α) [Invertibl
e a] : IsUnit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…

--- 原说明 ---
If `2` is invertible in the coefficient ring,
the radical of a quadratic map is the kernel of its polar bilinear map.
-/
lemma radical_eq_ker_polarBilin : Q.radical = Q.polarBilin.ker := by
  ext m
  simp only [mem_radical_iff', LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.zero_apply,
    QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
  refine ⟨by simp +contextual, fun h ↦ ?_⟩
  suffices Q m = 0 by grind
  specialize h m
  rwa [← two_smul R, QuadraticMap.map_smul, sub_sub, ← two_smul R, mul_smul, ← smul_sub,
    (isUnit_of_invertible 2).smul_eq_zero, two_smul, add_sub_cancel_right] at h

/-- If `2` is invertible in the coefficient ring,
the radical of a quadratic map is the kernel of its associated bilinear map. -/
/-
**QuadraticMap.radical_eq_ker_associated** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap
`。
形式化陈述：radical_eq_ker_associated : Q.radical = (QuadraticMap.associated Q).ker
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.radical_eq_ker_polarBilin`：radical_eq_ker_polarBilin : Q.ra
dical = Q.polarBilin.ker
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `2` is invertible in the coefficient ring,
the radical of a quadratic map is the kernel of its associated bilinear map.
-/
lemma radical_eq_ker_associated : Q.radical = (QuadraticMap.associated Q).ker := by
  rw [radical_eq_ker_polarBilin]
  ext m
  simp [associated_apply, LinearMap.ext_iff, QuadraticMap.polar, invOf_smul_eq_iff]

/--
If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate iff its radical is 0.
(Use `QuadraticMap.Nondegenerate.radical_eq_bot`
for the one-way implication in all characteristics.)
-/
/-
**QuadraticMap.nondegenerate_iff_radical_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Quadr
aticMap`。
形式化陈述：nondegenerate_iff_radical_eq_bot : Q.Nondegenerate ↔ Q.radical = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticMap.Nondegenerate.radical_eq_bot`：∀ {R : Type u_1} {M : Type u_
2} {P : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup P] [inst_2 : Co
mmRing R]   [inst_3 : _root_.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `QuadraticMap.radical_eq_ker_polarBilin`：radical_eq_ker_polarBilin : Q.ra
dical = Q.polarBilin.ker
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α

--- 原说明 ---
If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate iff its radical is 0.
(Use `QuadraticMap.Nondegenerate.radical_eq_bot`
for the one-way implication in all characteristics.)
-/
lemma nondegenerate_iff_radical_eq_bot :
    Q.Nondegenerate ↔ Q.radical = ⊥ := by
  refine ⟨Nondegenerate.radical_eq_bot, fun h ↦ ⟨h, ?_⟩⟩
  rw [← QuadraticMap.radical_eq_ker_polarBilin, h]
  nontriviality R
  simp only [rank_subsingleton', zero_le]

/-- If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate
iff its associated bilinear map is nondegenerate. -/
/-
**QuadraticMap.nondegenerate_associated_iff** 是 Mathlib 中的一个引理，位于命名空间 `Quadratic
Map`。
形式化陈述：nondegenerate_associated_iff : (QuadraticMap.associated Q).Nondegenerate ↔
 Q.Nondegenerate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.nondegenerate_iff_radical_eq_bot`：nondegenerate_iff_radical
_eq_bot : Q.Nondegenerate ↔ Q.radical = ⊥
· 使用引理 `QuadraticMap.radical_eq_ker_associated`：radical_eq_ker_associated : Q.ra
dical = (QuadraticMap.associated Q).ker
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `QuadraticMap.associated_flip`：associated_flip : (associatedHom S Q).flip
 = associatedHom S Q
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate
iff its associated bilinear map is nondegenerate.
-/
lemma nondegenerate_associated_iff :
    (QuadraticMap.associated Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, radical_eq_ker_associated,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y ↦ (congr_arg (· x y) (associated_flip R Q)).trans

/-- If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate
iff its polar bilinear map is nondegenerate. -/
/-
**QuadraticMap.nondegenerate_polar_iff** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：nondegenerate_polar_iff : (QuadraticMap.polarBilin Q).Nondegenerate ↔ Q.No
ndegenerate
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuadraticMap.nondegenerate_iff_radical_eq_bot`：nondegenerate_iff_radical
_eq_bot : Q.Nondegenerate ↔ Q.radical = ⊥
· 使用引理 `QuadraticMap.radical_eq_ker_polarBilin`：radical_eq_ker_polarBilin : Q.ra
dical = Q.polarBilin.ker
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QuadraticMap.polar_comm`：polar_comm (f : M -> N) (x y : M) : polar f x y
 = polar f y x
· 使用定理 `LinearMap.separatingLeft_iff_ker_eq_bot`：separatingLeft_iff_ker_eq_bot {
B : M₁ ->ₛₗ[I₁] M₂ ->ₛₗ[I₂] M} : B.SeparatingLeft ↔ LinearMap.ker B = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If `2` is invertible in the coefficient ring,
a quadratic map is nondegenerate
iff its polar bilinear map is nondegenerate.
-/
lemma nondegenerate_polar_iff :
    (QuadraticMap.polarBilin Q).Nondegenerate ↔ Q.Nondegenerate := by
  rw [nondegenerate_iff_radical_eq_bot, radical_eq_ker_polarBilin,
    LinearMap.IsRefl.nondegenerate_iff_separatingLeft, LinearMap.separatingLeft_iff_ker_eq_bot]
  exact fun x y ↦ (polar_comm Q y x).trans

end InvertibleTwo

end QuadraticMap

namespace QuadraticForm
variable {𝕜 ι : Type*} [Field 𝕜] [NeZero (2 : 𝕜)] [Fintype ι] {w : ι → 𝕜}

/-- Over a field of characteristic different from `2`,
the radical of a weighted-sum-of-squares quadratic form is the number of zero weights. -/
/-
**QuadraticForm.radical_weightedSumSquares** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticF
orm`。
形式化陈述：radical_weightedSumSquares : radical (weightedSumSquares 𝕜 w) = Pi.spanSub
set 𝕜 {i | w i = 0}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.weightedSumSquares_apply`：weightedSumSquares_apply [Monoid 
S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S) (v : ι -> R) : weig
htedSumSquares R w v = ∑ i …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `add_sq`：add_sq (a b : α) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
Over a field of characteristic different from `2`,
the radical of a weighted-sum-of-squares quadratic form is the number of zero we
ights.
-/
lemma radical_weightedSumSquares :
    radical (weightedSumSquares 𝕜 w) = Pi.spanSubset 𝕜 {i | w i = 0} := by
  classical
  ext v
  simp only [mem_radical_iff', weightedSumSquares_apply, ← pow_two, smul_eq_mul, Pi.add_apply,
    add_sq, mul_add, sum_add_distrib, add_eq_right, Pi.mem_spanSubset_iff]
  constructor
  · rintro ⟨hv, hvv'⟩ i
    simpa [hv, Pi.single_apply, NeZero.ne, or_iff_not_imp_left] using hvv' (Pi.single i 1)
  · simpa only [← sum_add_distrib]
      using fun h ↦ ⟨sum_eq_zero (by grind), fun v ↦ sum_eq_zero (by grind)⟩

/-- If the quadratic form `Q` is equivalent to a weighted sum of squares with weights `w`, then
the rank of `Q.radical` is equal to the number of zero weights. -/
/-
**QuadraticForm.finrank_radical_of_equiv_weightedSumSquares** 是 Mathlib 中的一个引理，位
于命名空间 `QuadraticForm`。
形式化陈述：finrank_radical_of_equiv_weightedSumSquares {M : Type*} [AddCommGroup M] [
Module 𝕜 M] {Q : QuadraticForm 𝕜 M} (hQ : Equivalent Q (weightedSumSquares 𝕜 w))
 : Module.finrank 𝕜 Q.radical = {i | w i = 0}.ncard
参数：hQ : Equivalent Q (weightedSumSquares 𝕜 w)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.Equivalent.rank_radical_eq`：∀ {R : Type u_1} {M : Type u_2}
 {M' : Type u_3} {P : Type u_4} [inst : AddCommGroup M] [inst_1 : AddCommGroup M
']   [inst_2 : AddCommGroup P…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `QuadraticForm.radical_weightedSumSquares`：radical_weightedSumSquares : r
adical (weightedSumSquares 𝕜 w) = Pi.spanSubset 𝕜 {i | w i = 0}
· 使用引理 `Pi.dim_spanSubset`：Pi.dim_spanSubset [Finite ι] [Nontrivial R] {s : Set 
ι} : Module.finrank R (Pi.spanSubset R s) = s.ncard
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R

--- 原说明 ---
If the quadratic form `Q` is equivalent to a weighted sum of squares with weight
s `w`, then
the rank of `Q.radical` is equal to the number of zero weights.
-/
lemma finrank_radical_of_equiv_weightedSumSquares {M : Type*} [AddCommGroup M] [Module 𝕜 M]
    {Q : QuadraticForm 𝕜 M} (hQ : Equivalent Q (weightedSumSquares 𝕜 w)) :
    Module.finrank 𝕜 Q.radical = {i | w i = 0}.ncard := by
  rw [hQ.rank_radical_eq, radical_weightedSumSquares, Pi.dim_spanSubset]

end QuadraticForm

