/-
Copyright (c) 2025 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel, Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorPower.Pairing
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Constructs a basis for exterior powers
-/

@[expose] public section

variable {R K M E : Type*} {n : ℕ}
  [CommRing R] [Field K] [AddCommGroup M] [Module R M] [AddCommGroup E] [Module K E]

namespace exteriorPower

/-! Finiteness of the exterior power. -/

/-- The `n`th exterior power of a finite module is a finite module. -/
/-
**exteriorPower.instFinite** 是 Mathlib 中的一个实例，位于命名空间 `exteriorPower`。
形式化陈述：instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `ExteriorAlgebra.exteriorPower.eq_1`：∀ (R : Type u1) [inst : CommRing R] 
(n : ℕ) (M : Type u2) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   
⋀[R]^n M = (ExteriorAlge…
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.FG.pow`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M : Submodule R A}, M.FG → ∀ (
n : ℕ)…
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…

--- 原说明 ---
The `n`th exterior power of a finite module is a finite module.
-/
instance instFinite [Module.Finite R M] : Module.Finite R (⋀[R]^n M) := by
  rw [Module.Finite.iff_fg, ExteriorAlgebra.exteriorPower, LinearMap.range_eq_map]
  exact Submodule.FG.pow (Submodule.FG.map _ Module.Finite.fg_top) n

/-! We construct a basis of `⋀[R]^n M` from a basis of `M`. -/

open Module Set Set.powersetCard

variable (R n)

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a finset of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of `M` by
applying the `exteriorPower.linearForm` construction to the family of linear forms
given by the coordinates of `b` indexed by elements of `s` (ordered using the given order on
`I`). -/
/-
**exteriorPower.** 是 Mathlib 中的一个定义，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a basis of `M` indexed by a linearly ordered type `I` and `s` is a fin
set of
`I` of cardinality `n`, then we get a linear form on the `n`th exterior power of
 `M` by
applying the `exteriorPower.linearForm` construction to the family of linear for
ms
given by the coordinates of `b` indexed by elements of `s` (ordered using the gi
ven order on
`I`).
-/
noncomputable def ιMultiDual {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) : Module.Dual R (⋀[R]^n M) :=
  pairingDual R M n (ιMulti_family R n b.coord s)

@[simp]
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMultiDual_apply_ιMulti {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) (v : Fin n → M) :
    ιMultiDual R n b s (ιMulti R n v) =
    (Matrix.of fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j) (v i)).det := by
  simp [ιMultiDual, ιMulti_family, pairingDual_ιMulti_ιMulti]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a fi
nset of `I`
of cardinality `n`. If we apply the linear form on `⋀[R]^n M` defined by `b` and
 `s`
to the exterior product of the `b i` for `i ∈ s`, then we get `1`.
-/
lemma ιMultiDual_apply_diag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s : powersetCard I n) :
    ιMultiDual R n b s (ιMulti_family R n b s) = 1 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  suffices Matrix.of (fun i j => b.coord (powersetCard.ofFinEmbEquiv.symm s j)
    (b (powersetCard.ofFinEmbEquiv.symm s i))) = 1 by
    simp_rw [Function.comp_apply, this, Matrix.det_one]
  ext
  simp [Matrix.one_apply, Finsupp.single_apply]

/-- Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a finset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠ t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of the
`b i` for `i ∈ t`, then we get `0`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `b` be a basis of `M` indexed by a linearly ordered type `I` and `s` be a fi
nset of `I`
of cardinality `n`. Let `t` be a finset of `I` of cardinality `n` such that `s ≠
 t`. If we apply
the linear form on `⋀[R]^n M` defined by `b` and `s` to the exterior product of 
the
`b i` for `i ∈ t`, then we get `0`.
-/
lemma ιMultiDual_apply_nondiag {I : Type*} [LinearOrder I] (b : Basis I R M)
    (s t : powersetCard I n) (hst : s ≠ t) :
    ιMultiDual R n b s (ιMulti_family R n b t) = 0 := by
  rw [ιMulti_family, ιMultiDual_apply_ιMulti]
  obtain ⟨i, his, hit⟩ := (exists_mem_notMem_iff_ne s t).mp hst
  obtain ⟨k, rfl⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  apply Matrix.det_eq_zero_of_column_eq_zero k
  simp_rw [Matrix.of_apply, Basis.coord_apply, Function.comp_apply, Basis.repr_self]
  intro j
  apply Finsupp.single_eq_of_ne
  by_contra! h
  apply hit
  rw [h, powersetCard.ofFinEmbEquiv_symm_apply, ← powersetCard.mem_coe_iff]
  exact Finset.orderEmbOfFin_mem t.val t.prop j

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements is linearly
independent in the `n`th exterior power of `M`. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a basis of `M` (indexed by a linearly ordered type), then the family
`exteriorPower.ιMulti R n b` of the `n`-fold exterior products of its elements i
s linearly
independent in the `n`th exterior power of `M`.
-/
lemma ιMulti_family_linearIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    LinearIndependent R (ιMulti_family R n b) :=
  LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun s ↦ ιMultiDual R n b s)
    (fun _ _ h => ιMultiDual_apply_nondiag R n b _ _ h)
    (fun _ => ιMultiDual_apply_diag _ _ _ _)

variable {R} in
/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the `n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b`. -/
/-
**exteriorPower._root_.Module.Basis.exteriorPower** 是 Mathlib 中的一个定义，位于命名空间 `ext
eriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the 
`n`th
exterior power of `M` formed by the `n`-fold exterior products of elements of `b
`.
-/
noncomputable def _root_.Module.Basis.exteriorPower {I : Type*} [LinearOrder I] (b : Basis I R M) :
    Basis (powersetCard I n) R (⋀[R]^n M) :=
  Basis.mk (ιMulti_family_linearIndependent_ofBasis _ _ _)
    (eq_top_iff.mp <| ιMulti_family_span_of_span R b.span_eq)

@[simp]
/-
**exteriorPower.coe_basis** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) : DFunLike.coe (b.
exteriorPower n) = ιMulti_family R n b
参数：b : Basis I R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用引理 `exteriorPower.ιMulti_family_linearIndependent_ofBasis`：ιMulti_family_lin
earIndependent_ofBasis {I : Type*} [LinearOrder I] (b : Basis I R M) : LinearInd
ependent R (ιMulti_family R n b)
-/
lemma coe_basis {I : Type*} [LinearOrder I] (b : Basis I R M) :
    DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b :=
  Basis.coe_mk _ _
/-
**exteriorPower.basis_apply** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCar
d I n) : b.exteriorPower n s = ιMulti_family R n b s
参数：b : Basis I R M；s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `exteriorPower.coe_basis`：coe_basis {I : Type*} [LinearOrder I] (b : Basi
s I R M) : DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b
-/
lemma basis_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    b.exteriorPower n s = ιMulti_family R n b s := by
  rw [coe_basis]

/-- If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the corresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th exterior power
defined by `b` and `s` in `exteriorPower.ιMultiDual`. -/
/-
**exteriorPower.basis_coord** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCar
d I n) : Basis.coord (b.exteriorPower n) s = ιMultiDual R n b s
参数：b : Basis I R M；s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext_on`：ext_on {s : Set M} {f g : M ->ₛₗ[σ₁₂] M₂} (hv : span R
 s = ⊤) (h : Set.EqOn f g s) : f = g
· 使用引理 `exteriorPower.ιMulti_family_span_of_span`：ιMulti_family_span_of_span {I 
: Type*} [LinearOrder I] {v : I -> M} (hv : Submodule.span R (Set.range v) = ⊤) 
: Submodule.span R (Set.range …
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用引理 `exteriorPower.ιMultiDual_apply_diag`：ιMultiDual_apply_diag {I : Type*} [
LinearOrder I] (b : Basis I R M) (s : powersetCard I n) : ιMultiDual R n b s (ιM
ulti_family R n b s) = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `exteriorPower.basis_apply`：basis_apply {I : Type*} [LinearOrder I] (b : 
Basis I R M) (s : powersetCard I n) : b.exteriorPower n s = ιMulti_family R n b 
s
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用引理 `exteriorPower.ιMultiDual_apply_nondiag`：ιMultiDual_apply_nondiag {I : Ty
pe*} [LinearOrder I] (b : Basis I R M) (s t : powersetCard I n) (hst : s != t) :
 ιMultiDual R n b s (ιMulti_…
· 使用定理 `Finsupp.single_eq_of_ne`：single_eq_of_ne (h : a' != a) : (single a b : α
 ->₀ M) a' = 0

--- 原说明 ---
If `b` is a basis of `M` indexed by a linearly ordered type `I` and `B` is the c
orresponding
basis of the `n`th exterior power of `M`, indexed by the set of finsets `s` of `
I` of cardinality
`n`, then the coordinate function of `B` at `s` is the linear form on the `n`th 
exterior power
defined by `b` and `s` in `exteriorPower.ιMultiDual`.
-/
lemma basis_coord {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.coord (b.exteriorPower n) s = ιMultiDual R n b s := by
  apply LinearMap.ext_on (ιMulti_family_span_of_span R (Basis.span_eq b))
  rintro x ⟨t, rfl⟩
  rw [Basis.coord_apply]
  by_cases! hst : s = t
  · rw [hst, ιMultiDual_apply_diag, ← basis_apply, Basis.repr_self, Finsupp.single_eq_same]
  · rw [ιMultiDual_apply_nondiag R n b s t hst, ← basis_apply, Basis.repr_self,
      Finsupp.single_eq_of_ne hst]
/-
**exteriorPower.basis_repr_apply** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n
 M) (s : powersetCard I n) : Basis.repr (b.exteriorPower n) x s = ιMultiDual R n
 b s x
参数：b : Basis I R M；x : ⋀[R]^n M；s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用引理 `exteriorPower.basis_coord`：basis_coord {I : Type*} [LinearOrder I] (b : 
Basis I R M) (s : powersetCard I n) : Basis.coord (b.exteriorPower n) s = ιMulti
Dual R n b s
-/
lemma basis_repr_apply {I : Type*} [LinearOrder I] (b : Basis I R M) (x : ⋀[R]^n M)
    (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) x s = ιMultiDual R n b s x := by
  simpa [← Basis.coord_apply] using LinearMap.congr_fun (basis_coord R n b s) x

@[simp]
/-
**exteriorPower.basis_repr_self** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powerse
tCard I n) : Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) s = 1
参数：b : Basis I R M；s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `exteriorPower.basis_repr_apply`：basis_repr_apply {I : Type*} [LinearOrde
r I] (b : Basis I R M) (x : ⋀[R]^n M) (s : powersetCard I n) : Basis.repr (b.ext
eriorPower n) x s = …
· 使用引理 `exteriorPower.ιMultiDual_apply_diag`：ιMultiDual_apply_diag {I : Type*} [
LinearOrder I] (b : Basis I R M) (s : powersetCard I n) : ιMultiDual R n b s (ιM
ulti_family R n b s) = 1
-/
lemma basis_repr_self {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) s = 1 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_diag R n b s

@[simp]
/-
**exteriorPower.basis_repr_ne** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M) {s t : powerse
tCard I n} (hst : s != t) : Basis.repr (b.exteriorPower n) (ιMulti_family R n b 
s) t = 0
参数：b : Basis I R M；hst : s != t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `exteriorPower.basis_repr_apply`：basis_repr_apply {I : Type*} [LinearOrde
r I] (b : Basis I R M) (x : ⋀[R]^n M) (s : powersetCard I n) : Basis.repr (b.ext
eriorPower n) x s = …
· 使用引理 `exteriorPower.ιMultiDual_apply_nondiag`：ιMultiDual_apply_nondiag {I : Ty
pe*} [LinearOrder I] (b : Basis I R M) (s t : powersetCard I n) (hst : s != t) :
 ιMultiDual R n b s (ιMulti_…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma basis_repr_ne {I : Type*} [LinearOrder I] (b : Basis I R M)
    {s t : powersetCard I n} (hst : s ≠ t) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) t = 0 := by
  simpa [basis_repr_apply] using ιMultiDual_apply_nondiag R n b t s hst.symm
/-
**exteriorPower.basis_repr** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard
 I n) : Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) = Finsupp.single 
s 1
参数：b : Basis I R M；s : powersetCard I n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `exteriorPower.basis_repr_self`：basis_repr_self {I : Type*} [LinearOrder 
I] (b : Basis I R M) (s : powersetCard I n) : Basis.repr (b.exteriorPower n) (ιM
ulti_family R n b s…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `exteriorPower.basis_repr_ne`：basis_repr_ne {I : Type*} [LinearOrder I] (
b : Basis I R M) {s t : powersetCard I n} (hst : s != t) : Basis.repr (b.exterio
rPower n) (ιMulti…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.single_eq_of_ne'`：single_eq_of_ne' (h : a != a') : (single a b :
 α ->₀ M) a' = 0
-/
lemma basis_repr {I : Type*} [LinearOrder I] (b : Basis I R M) (s : powersetCard I n) :
    Basis.repr (b.exteriorPower n) (ιMulti_family R n b s) = Finsupp.single s 1 := by
  ext t
  by_cases hst : s = t <;> simp [hst]

/-! ### Freeness and dimension of `⋀[R]^n M`. -/

/-- If `M` is a free module, then so is its `n`th exterior power. -/
/-
**exteriorPower.instFree** 是 Mathlib 中的一个实例，位于命名空间 `exteriorPower`。
形式化陈述：instFree [Module.Free R M] : Module.Free R (⋀[R]^n M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
If `M` is a free module, then so is its `n`th exterior power.
-/
instance instFree [Module.Free R M] : Module.Free R (⋀[R]^n M) := by
  classical
  have ⟨I, b⟩ := Module.Free.exists_basis R M
  let : LinearOrder I := linearOrderOfSTO WellOrderingRel
  exact Module.Free.of_basis (b.exteriorPower n)

variable [Nontrivial R]

/-- If `R` is non-trivial and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`. -/
/-
**exteriorPower.finrank_eq** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
形式化陈述：finrank_eq [Module.Free R M] [Module.Finite R M] : Module.finrank R (⋀[R]^
n M) = Nat.choose (Module.finrank R M) n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Set.powersetCard.card`：∀ (α : Type u_1) (n : ℕ), Nat.card ↑(Set.powerset
Card α n) = (Nat.card α).choose n

--- 原说明 ---
If `R` is non-trivial and `M` is finite free of rank `r`, then
the `n`th exterior power of `M` is of finrank `Nat.choose r n`.
-/
lemma finrank_eq [Module.Free R M] [Module.Finite R M] :
    Module.finrank R (⋀[R]^n M) = Nat.choose (Module.finrank R M) n := by
  classical
  let : LinearOrder (Module.Free.ChooseBasisIndex R M) := linearOrderOfSTO WellOrderingRel
  let B := (Module.Free.chooseBasis R M).exteriorPower n
  rw [Module.finrank_eq_card_basis (Module.Free.chooseBasis R M), Module.finrank_eq_card_basis B,
    Fintype.card_eq_nat_card, powersetCard.card, Fintype.card_eq_nat_card]

/-! Results that only hold over a field. -/

/-- If `v` is a linearly independent family of vectors (indexed by a linearly ordered type),
then the family of its `n`-fold exterior products is also linearly independent. -/
/-
**exteriorPower.** 是 Mathlib 中的一个引理，位于命名空间 `exteriorPower`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `v` is a linearly independent family of vectors (indexed by a linearly ordere
d type),
then the family of its `n`-fold exterior products is also linearly independent.
-/
lemma ιMulti_family_linearIndependent_field {I : Type*} [LinearOrder I] {v : I → E}
    (hv : LinearIndependent K v) : LinearIndependent K (ιMulti_family K n v) := by
  let W := Submodule.span K (Set.range v)
  suffices ∃ b : Basis I K W, v = W.subtype ∘ b by
    obtain ⟨b, hb⟩ := this
    rw [hb, ← map_comp_ιMulti_family]
    exact LinearIndependent.map' (coe_basis K n b ▸ (b.exteriorPower n).linearIndependent)
      _ (LinearMap.ker_eq_bot.mpr (map_injective_field (Submodule.subtype_injective _)))
  use Module.Basis.span hv
  ext i
  rw [Submodule.coe_subtype, Function.comp_apply, Basis.span_apply]

end exteriorPower

