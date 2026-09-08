/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Semisimple

/-!
# Eigenspaces of semisimple linear endomorphisms

This file contains basic results relevant to the study of eigenspaces of semisimple linear
endomorphisms.

## Main definitions / results

* `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`: for a semisimple endomorphism,
  a generalized eigenspace is an eigenspace.
* `Module.End.IsSemisimple.iSup_maxGenEigenspace_eq_top_iff`: a semisimple endomorphism is
  triangularizable if and only if it is diagonalizable.
* `Module.End.IsSemisimple.iSup_eigenspace_eq_top`: over an algebraically closed field,
  the eigenspaces of a semisimple endomorphism span the whole space.
* `Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue`: a semisimple endomorphism over
  an algebraically closed field is zero iff all eigenvalues are zero.

-/

public section

open Function Set

namespace Module.End

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {f g : End R M}

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil** 是 Mathli
b 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil {μ : R} {k : Nat∞
} {m : M} (hm : m in f.genEigenspace μ k) (hfg : Commute f g) (hss : g.IsFinitel
ySemisimple) (hnil : IsNilpotent (f - g)) : g m = μ • m
参数：hm : m in f.genEigenspace μ k；hfg : Commute f g；hss : g.IsFinitelySemisimple；
hnil : IsNilpotent (f - g)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.mem_genEigenspace`：mem_genEigenspace {f : End R M} {μ : R} {k
 : Nat∞} {x : M} : x in f.genEigenspace μ k ↔ exists l : Nat, l <= k ∧ x in Line
arMap.ker ((f - μ …
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用引理 `Algebra.commute_algebraMap_right`：commute_algebraMap_right (r : R) (x : 
A) : Commute x (algebraMap R A r)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `sub_sub_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b c
 : G), c - a - (c - b) = b - a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `LinearMap.restrict_sub`：restrict_sub {R R₂ M M₂ : Type*} [Ring R] [Ring 
R₂] {σ₁₂ : R ->+* R₂} [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R₂
 M₂] {p : Su…
· 使用定理 `LinearMap.restrict.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Typ
e u_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用引理 `LinearMap.restrict_commute`：restrict_commute {f g : M ->ₗ[R] M} (h : Com
mute f g) {p : Submodule R M} (hf : MapsTo f p p) (hg : MapsTo g p p) : Commute 
(f.restrict hf) …
· 使用引理 `Module.End.isNilpotent_restrict_sub_algebraMap`：isNilpotent_restrict_sub
_algebraMap (f : End R M) (μ : R) (k : Nat) (h : MapsTo (f - algebraMap R (End R
 M) μ) (f.genEigenspace μ k) (f.genE…
· 使用定理 `Module.End.isNilpotent.restrict`：∀ {R : Type u_1} {M : Type u_3} [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f : M →ₗ
[R] M} {p : Submodule…
· 使用引理 `Module.End.eq_zero_of_isNilpotent_of_isFinitelySemisimple`：eq_zero_of_is
Nilpotent_of_isFinitelySemisimple (hn : IsNilpotent f) (hs : IsFinitelySemisimpl
e f) : f = 0
· 使用定理 `Module.End.IsFinitelySemisimple.restrict`：∀ {R : Type u_1} {M : Type u_2
} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {
f : Module.End R M} {p : Submo…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.End.mem_genEigenspace_nat`：mem_genEigenspace_nat {f : End R M} {μ
 : R} {k : Nat} {x : M} : x in f.genEigenspace μ k ↔ x in LinearMap.ker ((f - μ 
• 1) ^ k)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
-/
lemma apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil
    {μ : R} {k : ℕ∞} {m : M} (hm : m ∈ f.genEigenspace μ k)
    (hfg : Commute f g) (hss : g.IsFinitelySemisimple) (hnil : IsNilpotent (f - g)) :
    g m = μ • m := by
  rw [f.mem_genEigenspace] at hm
  obtain ⟨l, -, hm⟩ := hm
  rw [← f.mem_genEigenspace_nat] at hm
  set p := f.genEigenspace μ l
  have h₁ : MapsTo g p p := mapsTo_genEigenspace_of_comm hfg μ l
  have h₂ : MapsTo (g - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (hfg.sub_right <| Algebra.commute_algebraMap_right μ f) μ l
  have h₃ : MapsTo (f - g) p p :=
    mapsTo_genEigenspace_of_comm (Commute.sub_right rfl hfg) μ l
  have h₄ : MapsTo (f - algebraMap R (End R M) μ) p p :=
    mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ l
  replace hfg : Commute (f - algebraMap R (End R M) μ) (f - g) :=
    (Commute.sub_right rfl hfg).sub_left <| Algebra.commute_algebraMap_left μ (f - g)
  suffices IsNilpotent ((g - algebraMap R (End R M) μ).restrict h₂) by
    replace this : g.restrict h₁ - algebraMap R (End R p) μ = 0 :=
      eq_zero_of_isNilpotent_of_isFinitelySemisimple this (by simpa using hss.restrict _)
    simpa [LinearMap.restrict_apply, sub_eq_zero] using LinearMap.congr_fun this ⟨m, hm⟩
  simpa [LinearMap.restrict_sub h₄ h₃] using (LinearMap.restrict_commute hfg h₄ h₃).isNilpotent_sub
    (f.isNilpotent_restrict_sub_algebraMap μ l) (Module.End.isNilpotent.restrict h₃ hnil)
/-
**Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace** 是 Mathlib 中的一个定理
，位于命名空间 `Module.End.IsFinitelySemisimple`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {f : Module.End R M}, f.IsFinitelySemisimple 
→ ∀ (μ : R) {k : ℕ∞}, 0 < k → (f.genEigenspace μ) k = f.eigenspace μ
参数：μ : R；f.genEigenspace μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用引理 `Module.End.apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil`：app
ly_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil {μ : R} {k : Nat∞} {m : M}
 (hm : m in f.genEigenspace μ k) (hfg : Commute f g) (hss…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma IsFinitelySemisimple.genEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) {k : ℕ∞} (hk : 0 < k) :
    f.genEigenspace μ k = f.eigenspace μ := by
  refine le_antisymm (fun m hm ↦ mem_eigenspace_iff.mpr ?_) (f.genEigenspace μ |>.mono ?_)
  · apply apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hm rfl hf
    simp
  · exact Order.one_le_iff_pos.mpr hk
/-
**Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace** 是 Mathlib 中的一
个定理，位于命名空间 `Module.End.IsFinitelySemisimple`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {f : Module.End R M}, f.IsFinitelySemisimple 
→ ∀ (μ : R), f.maxGenEigenspace μ = f.eigenspace μ
参数：μ : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.IsFinitelySemisimple.genEigenspace_eq_eigenspace`：∀ {R : Type
 u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _ro
ot_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `ENat.top_pos`：top_pos : (0 : Nat∞) < ⊤
-/
lemma IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace
    (hf : f.IsFinitelySemisimple) (μ : R) :
    f.maxGenEigenspace μ = f.eigenspace μ :=
  hf.genEigenspace_eq_eigenspace μ ENat.top_pos

/-- A finitely-semisimple endomorphism is triangularizable if and only if it is diagonalizable. -/
/-
**Module.End.IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff** 是 Mathlib 中
的一个定理，位于命名空间 `Module.End.IsFinitelySemisimple`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {f : Module.End R M}, f.IsFinitelySemisimple 
→ (⨆ μ, f.maxGenEigenspace μ = ⊤ ↔ ⨆ μ, f.eigenspace μ = ⊤)
参数：⨆ μ, f.maxGenEigenspace μ = ⊤ ↔ ⨆ μ, f.eigenspace μ = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`：∀ {R : T
ype u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : 
_root_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A finitely-semisimple endomorphism is triangularizable if and only if it is diag
onalizable.
-/
lemma IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff (hf : f.IsFinitelySemisimple) :
    (⨆ μ : R, f.maxGenEigenspace μ) = ⊤ ↔ (⨆ μ : R, f.eigenspace μ) = ⊤ := by
  simp [hf.maxGenEigenspace_eq_eigenspace]

/-- A semisimple endomorphism is triangularizable if and only if it is diagonalizable. -/
/-
**Module.End.IsSemisimple.iSup_maxGenEigenspace_eq_top_iff** 是 Mathlib 中的一个定理，位于
命名空间 `Module.End.IsSemisimple`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   {f : Module.End R M}, f.IsSemisimple → (⨆ μ, 
f.maxGenEigenspace μ = ⊤ ↔ ⨆ μ, f.eigenspace μ = ⊤)
参数：⨆ μ, f.maxGenEigenspace μ = ⊤ ↔ ⨆ μ, f.eigenspace μ = ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.IsFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff`：∀ {R :
 Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 
: _root_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `Module.End.IsSemisimple.isFinitelySemisimple`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   {f : Module.End R M}, f.IsSemis…

--- 原说明 ---
A semisimple endomorphism is triangularizable if and only if it is diagonalizabl
e.
-/
lemma IsSemisimple.iSup_maxGenEigenspace_eq_top_iff (hf : f.IsSemisimple) :
    (⨆ μ : R, f.maxGenEigenspace μ) = ⊤ ↔ (⨆ μ : R, f.eigenspace μ) = ⊤ :=
  hf.isFinitelySemisimple.iSup_maxGenEigenspace_eq_top_iff

section AlgClosed

variable {K V : Type*} [Field K] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {f : End K V}

/-
**Module.End.IsSemisimple.iSup_eigenspace_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.End.IsSemisimple`。
形式化陈述：∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 :
 AddCommGroup V] [inst_3 : _root_.Module K V]   [FiniteDimensional K V] {f : Mod
ule.End K V}, f.IsSemisimple → ⨆ μ, f.eigenspace μ = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Module.End.IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`：∀ {R : T
ype u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : 
_root_.Module R M]   {f : Module.End R M}, f.IsFinit…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.End.isFinitelySemisimple_iff_isSemisimple`：isFinitelySemisimple_i
ff_isSemisimple [Module.Finite R M] : f.IsFinitelySemisimple ↔ f.IsSemisimple
· 使用定理 `Module.End.iSup_maxGenEigenspace_eq_top`：iSup_maxGenEigenspace_eq_top [I
sAlgClosed K] [FiniteDimensional K V] (f : End K V) : ⨆ (μ : K), f.maxGenEigensp
ace μ = ⊤
-/
lemma IsSemisimple.iSup_eigenspace_eq_top (hf : f.IsSemisimple) :
    ⨆ μ : K, f.eigenspace μ = ⊤ := by
  simpa only [(isFinitelySemisimple_iff_isSemisimple.mpr hf).maxGenEigenspace_eq_eigenspace] using
    iSup_maxGenEigenspace_eq_top f
/-
**Module.End.IsSemisimple.eq_zero_iff_forall_eigenvalue** 是 Mathlib 中的一个定理，位于命名空
间 `Module.End.IsSemisimple`。
形式化陈述：∀ {K : Type u_3} {V : Type u_4} [inst : Field K] [IsAlgClosed K] [inst_2 :
 AddCommGroup V] [inst_3 : _root_.Module K V]   [FiniteDimensional K V] {f : Mod
ule.End K V}, f.IsSemisimple → (f = 0 ↔ ∀ (μ : K), f.HasEigenvalue μ → μ = 0)
参数：f = 0 ↔ ∀ (μ : K), f.HasEigenvalue μ → μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `Module.End.IsSemisimple.iSup_eigenspace_eq_top`：∀ {K : Type u_3} {V : Ty
pe u_4} [inst : Field K] [IsAlgClosed K] [inst_2 : AddCommGroup V] [inst_3 : _ro
ot_.Module K V]   [FiniteDimensional…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `Module.End.hasEigenvalue_iff`：hasEigenvalue_iff {f : End R M} {μ : R} : 
f.HasEigenvalue μ ↔ f.eigenspace μ != ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.End.eigenspace_zero`：eigenspace_zero (f : End R M) : f.eigenspace
 0 = LinearMap.ker f
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
-/
lemma IsSemisimple.eq_zero_iff_forall_eigenvalue (hf : f.IsSemisimple) :
    f = 0 ↔ ∀ μ : K, f.HasEigenvalue μ → μ = 0 := by
  constructor
  · rintro rfl μ hμ
    by_contra hμ0
    obtain ⟨x, hx, hx_ne⟩ := (Submodule.ne_bot_iff _).mp hμ
    rw [mem_eigenspace_iff] at hx
    exact hx_ne ((smul_eq_zero.mp hx.symm).resolve_left hμ0)
  · intro h
    suffices f.eigenspace 0 = ⊤ by rwa [eigenspace_zero, LinearMap.ker_eq_top] at this
    rw [← hf.iSup_eigenspace_eq_top]
    refine le_antisymm (le_iSup _ 0) (iSup_le fun μ ↦ ?_)
    rcases eq_or_ne μ 0 with rfl | hμ
    · exact le_refl _
    · have : f.eigenspace μ = ⊥ := not_not.mp (hasEigenvalue_iff.not.mp fun he ↦ hμ (h μ he))
      simp [this]

end AlgClosed

end Module.End

