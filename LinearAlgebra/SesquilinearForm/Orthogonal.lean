/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Christopher Hoskin
-/
module

public import Mathlib.LinearAlgebra.SesquilinearForm.Basic

import Mathlib.Algebra.Module.Torsion.Field

/-!
# Orthogonal complement

This file defines the orthogonal submodule of a submodule with respect to a sesqui-blinear map.

## Main declarations

* `orthogonalBilin` provides the orthogonal complement with respect to a sesqui-bilinear map
-/

@[expose] public section

open Module LinearMap

variable {R R₁ R₂ M M₁ M₂ : Type*}

namespace Submodule

/-! ### The orthogonal complement -/

variable [CommSemiring R] [CommSemiring R₁] [CommSemiring R₂]
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid M₁] [Module R₁ M₁]
variable [AddCommMonoid M₂] [Module R₂ M₂]
variable {I₁ : R₁ →+* R} {I₂ : R₂ →+* R}
variable {B : M₁ →ₛₗ[I₁] M₂ →ₛₗ[I₂] M}
variable {S T : Submodule R₁ M₁}

variable (B S) in
/-- The orthogonal complement of a submodule `N` with respect to some bilinear map is the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear maps this definition has a
chirality; in addition to this "left" orthogonal complement one could define a "right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition is not currently
provided in mathlib. -/
/-
**Submodule.orthogonalBilin** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：orthogonalBilin : Submodule R₂ M₂ where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orthogonal complement of a submodule `N` with respect to some bilinear map i
s the set of
elements `x` which are orthogonal to all elements of `N`; i.e., for all `y` in `
N`, `B x y = 0`.

Note that for general (neither symmetric nor antisymmetric) bilinear maps this d
efinition has a
chirality; in addition to this "left" orthogonal complement one could define a "
right" orthogonal
complement for which, for all `y` in `N`, `B y x = 0`.  This variant definition 
is not currently
provided in mathlib.
-/
def orthogonalBilin : Submodule R₂ M₂ where
  carrier := {y | ∀ x ∈ S, B x y = 0}
  zero_mem' := by simp
  add_mem' {u v} hu hv x hx := by simp [hu _ hx, hv _ hx]
  smul_mem' c y hy x hx := by simp [hy _ hx]
/-
**Submodule.mem_orthogonalBilin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_4} {M₁ : Type
 u_5} {M₂ : Type u_6} [inst : CommSemiring R]   [inst_1 : CommSemiring R₁] [inst
_2 : CommSemiring R₂] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   
[inst_5 : AddCommMonoid M₁] [inst_6 : _root_.Module R₁ M₁] [inst_7 : AddCommMono
id M₂] [inst_8 : _root_.Module R₂ M₂]   {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {B : M₁ 
→ₛₗ[I₁] M₂ →ₛₗ[I₂] M} {S : Submodule R₁ M₁} {m : M₂},   m ∈ Submodule.orthogonal
Bilin B S ↔ ∀ n ∈ S, (B n) m = 0
参数：B n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem mem_orthogonalBilin_iff {m : M₂} :
  m ∈ S.orthogonalBilin B ↔ ∀ n ∈ S, B n m = 0 := .rfl
/-
**Submodule.orthogonalBilin_le** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {R₁ : Type u_2} {R₂ : Type u_3} {M : Type u_4} {M₁ : Type
 u_5} {M₂ : Type u_6} [inst : CommSemiring R]   [inst_1 : CommSemiring R₁] [inst
_2 : CommSemiring R₂] [inst_3 : AddCommMonoid M] [inst_4 : _root_.Module R M]   
[inst_5 : AddCommMonoid M₁] [inst_6 : _root_.Module R₁ M₁] [inst_7 : AddCommMono
id M₂] [inst_8 : _root_.Module R₂ M₂]   {I₁ : R₁ →+* R} {I₂ : R₂ →+* R} {B : M₁ 
→ₛₗ[I₁] M₂ →ₛₗ[I₂] M} {S T : Submodule R₁ M₁},   S ≤ T → Submodule.orthogonalBil
in B T ≤ Submodule.orthogonalBilin B S
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[gcongr] theorem orthogonalBilin_le (h : S ≤ T) :
    orthogonalBilin B T ≤ orthogonalBilin B S := fun _ hy _ hx ↦ hy _ (h hx)

section IsRefl

variable {I₂ : R₁ →+* R} {B : M₁ →ₛₗ[I₁] M₁ →ₛₗ[I₂] M}

/-
**Submodule.le_orthogonalBilin_orthogonalBilin** 是 Mathlib 中的一个定理，位于命名空间 `Submod
ule`。
形式化陈述：le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) : S <= (S.orthogonalBili
n B).orthogonalBilin B
参数：b : B.IsRefl。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_orthogonalBilin_orthogonalBilin (b : B.IsRefl) :
    S ≤ (S.orthogonalBilin B).orthogonalBilin B := fun n hn _m hm ↦ b _ _ (hm n hn)

end IsRefl

end Submodule

namespace LinearMap

section Orthogonal

variable {K K₁ V V₁ V₂ : Type*}
variable [Field K] [AddCommGroup V] [Module K V] [Field K₁] [AddCommGroup V₁] [Module K₁ V₁]
  [AddCommGroup V₂] [Module K V₂] {J : K →+* K} {J₁ : K₁ →+* K} {J₁' : K₁ →+* K}

-- ↓ This lemma only applies in fields as we require `a * b = 0 → a = 0 ∨ b = 0`
/-
**LinearMap.span_singleton_inf_orthogonal_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：span_singleton_inf_orthogonal_eq_bot (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x 
: V₁) (hx : B x x != 0) : (K₁ ∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = ⊥
参数：B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂；x : V₁；hx : B x x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Submodule.mem_span_finset`：Submodule.mem_span_finset {s : Finset M} {x :
 M} : x in span R s ↔ exists f : M -> R, f.support subseteq s ∧ ∑ a in s, f a • 
a = x where mp
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `MulActionSemiHomClass.map_smulₛₗ`：∀ {F : Type u_8} {M : outParam (Type u
_9)} {N : outParam (Type u_10)} {φ : outParam (M → N)} {X : outParam (Type u_11)
}   {Y : outParam (Typ…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
-/
theorem span_singleton_inf_orthogonal_eq_bot (B : V₁ →ₛₗ[J₁] V₁ →ₛₗ[J₁'] V₂) (x : V₁)
    (hx : B x x ≠ 0) : (K₁ ∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = ⊥ := by
  rw [← Finset.coe_singleton]
  refine eq_bot_iff.2 fun y h ↦ ?_
  obtain ⟨μ, -, rfl⟩ := Submodule.mem_span_finset.1 h.1
  replace h := h.2 x (by simp [Submodule.mem_span] : x ∈ Submodule.span K₁ ({x} : Finset V₁))
  rw [Finset.sum_singleton] at h ⊢
  suffices hμzero : μ x = 0 by rw [hμzero, zero_smul, Submodule.mem_bot]
  rw [map_smulₛₗ] at h
  exact Or.elim (smul_eq_zero.mp h)
      (fun y ↦ by simpa using y)
      (fun hfalse ↦ False.elim <| hx hfalse)

-- ↓ This lemma only applies in fields since we use the `mul_eq_zero`
/-
**LinearMap.orthogonal_span_singleton_eq_to_lin_ker** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap`。
形式化陈述：orthogonal_span_singleton_eq_to_lin_ker {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V
) : (K ∙ x).orthogonalBilin B = LinearMap.ker (B x)
参数：x : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `LinearMap.map_smulₛₗ₂`：map_smulₛₗ₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (r : 
R) (x y) : f (r • x) y = ρ₁₂ r • f x y
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `DivisionSemiring.to_moduleIsTorsionFree`：∀ {𝕜 : Type u_1} {M : Type u_2}
 [inst : DivisionSemiring 𝕜] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module 
𝕜 M],   Module.IsTorsionFree …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `Or.intro_right`：∀ {b : Prop} (a : Prop), b → a ∨ b
-/
theorem orthogonal_span_singleton_eq_to_lin_ker {B : V →ₗ[K] V →ₛₗ[J] V₂} (x : V) :
    (K ∙ x).orthogonalBilin B = LinearMap.ker (B x) := by
  ext y
  simp_rw [Submodule.mem_orthogonalBilin_iff, LinearMap.mem_ker, Submodule.mem_span_singleton]
  constructor
  · exact fun h ↦ h x ⟨1, one_smul _ _⟩
  · rintro h _ ⟨z, rfl⟩
    rw [map_smulₛₗ₂, smul_eq_zero]
    exact Or.intro_right _ h

-- todo: Generalize this to sesquilinear maps
/-
**LinearMap.span_singleton_sup_orthogonal_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：span_singleton_sup_orthogonal_eq_top {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx
 : B x x != 0) : (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B = ⊤
参数：hx : B x x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.orthogonal_span_singleton_eq_to_lin_ker`：orthogonal_span_singl
eton_eq_to_lin_ker {B : V ->ₗ[K] V ->ₛₗ[J] V₂} (x : V) : (K ∙ x).orthogonalBilin
 B = LinearMap.ker (B x)
· 使用定理 `LinearMap.span_singleton_sup_ker_eq_top`：span_singleton_sup_ker_eq_top (
f : V ->ₗ[K] K) {x : V} (hx : f x != 0) : K ∙ x ⊔ ker f = ⊤
-/
theorem span_singleton_sup_orthogonal_eq_top {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    (K ∙ x) ⊔ (K ∙ x).orthogonalBilin B = ⊤ := by
  rw [orthogonal_span_singleton_eq_to_lin_ker]
  exact (B x).span_singleton_sup_ker_eq_top hx

-- todo: Generalize this to sesquilinear maps
/-- Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the singleton of `x`
  is complement to its orthogonal complement. -/
/-
**LinearMap.isCompl_span_singleton_orthogonal** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap`。
形式化陈述：isCompl_span_singleton_orthogonal {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : 
B x x != 0) : IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B)
参数：hx : B x x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `LinearMap.span_singleton_inf_orthogonal_eq_bot`：span_singleton_inf_ortho
gonal_eq_bot (B : V₁ ->ₛₗ[J₁] V₁ ->ₛₗ[J₁'] V₂) (x : V₁) (hx : B x x != 0) : (K₁ 
∙ x) ⊓ (K₁ ∙ x).orthogonalBilin B = …
· 使用定理 `codisjoint_iff`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : Ord
erTop α] {a b : α}, Codisjoint a b ↔ a ⊔ b = ⊤
· 使用定理 `LinearMap.span_singleton_sup_orthogonal_eq_top`：span_singleton_sup_ortho
gonal_eq_top {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) : (K ∙ x) ⊔ (K 
∙ x).orthogonalBilin B = ⊤

--- 原说明 ---
Given a bilinear form `B` and some `x` such that `B x x ≠ 0`, the span of the si
ngleton of `x`
  is complement to its orthogonal complement.
-/
theorem isCompl_span_singleton_orthogonal {B : V →ₗ[K] V →ₗ[K] K} {x : V} (hx : B x x ≠ 0) :
    IsCompl (K ∙ x) ((K ∙ x).orthogonalBilin B) :=
  { disjoint := disjoint_iff.2 <| span_singleton_inf_orthogonal_eq_bot B x hx
    codisjoint := codisjoint_iff.2 <| span_singleton_sup_orthogonal_eq_top hx }

end Orthogonal

section CommRing

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M₁] [Module R M₁] {I I' : R →+* R}

/-- The restriction of a reflexive bilinear map `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`. -/
/-
**LinearMap.nondegenerate_restrict_of_disjoint_orthogonal** 是 Mathlib 中的一个定理，位于命
名空间 `LinearMap`。
形式化陈述：nondegenerate_restrict_of_disjoint_orthogonal {B : M ->ₗ[R] M ->ₗ[R] M₁} (
hB : B.IsRefl) {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) : (B.
domRestrict₁₂ W W).Nondegenerate
参数：hB : B.IsRefl；hW : Disjoint W (W.orthogonalBilin B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.IsRefl.nondegenerate_iff_separatingLeft`：∀ {R : Type u_1} {M :
 Type u_5} {M₁ : Type u_6} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] [inst_3 : AddCo…
· 使用定理 `LinearMap.IsRefl.domRestrict`：domRestrict (p : Submodule R₁ M₁) : (B.dom
Restrict₁₂ p p).IsRefl
· 使用定理 `Submodule.mk_eq_zero`：mk_eq_zero {x} (h : x in p) : (⟨x, h⟩ : p) = 0 ↔ x
 = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `LinearMap.IsRefl.eq_zero`：eq_zero : forall {x y}, B x y = 0 -> B y x = 0

--- 原说明 ---
The restriction of a reflexive bilinear map `B` onto a submodule `W` is
nondegenerate if `W` has trivial intersection with its orthogonal complement,
that is `Disjoint W (W.orthogonalBilin B)`.
-/
theorem nondegenerate_restrict_of_disjoint_orthogonal {B : M →ₗ[R] M →ₗ[R] M₁} (hB : B.IsRefl)
    {W : Submodule R M} (hW : Disjoint W (W.orthogonalBilin B)) :
    (B.domRestrict₁₂ W W).Nondegenerate := by
  rw [(hB.domRestrict W).nondegenerate_iff_separatingLeft]
  rintro ⟨x, hx⟩ b₁
  rw [Submodule.mk_eq_zero, ← Submodule.mem_bot R]
  refine hW.le_bot ⟨hx, fun y hy ↦ ?_⟩
  specialize b₁ ⟨y, hy⟩
  simp_rw [domRestrict₁₂_apply] at b₁
  exact hB.eq_zero b₁

end CommRing

end LinearMap

