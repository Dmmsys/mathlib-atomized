/-
Copyright (c) 2025 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Antoine Chambert-Loir
-/
module

public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.LinearAlgebra.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Center

/-!
# Group actions on projectivization

Show that (among other groups), the general linear group
and the special linear groups of `V` act on `ℙ K V`.

Prove that these actions are 2-transitive.

## TODO

Generalize to the special linear group over a division ring.

-/

@[expose] public section

open scoped LinearAlgebra.Projectivization Matrix

namespace Projectivization

section DivisionRing

variable {G K V : Type*} [AddCommGroup V] [DivisionRing K] [Module K V]
  [Group G] [DistribMulAction G V] [SMulCommClass G K V]

set_option backward.isDefEq.respectTransparency false in
/-- Any group acting `K`-linearly on `V` (such as the general linear group) acts on `ℙ V`. -/
@[simps -isSimp]
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any group acting `K`-linearly on `V` (such as the general linear group) acts on 
`ℙ V`.
-/
instance : MulAction G (ℙ K V) where
  smul g x := x.map (DistribMulAction.toModuleEnd _ _ g)
    (DistribMulAction.toLinearEquiv _ _ g).injective
  one_smul x := show map _ _ _ = _ by simp [map_one, Module.End.one_eq_id]
  mul_smul g g' x := show map _ _ _ = map _ _ (map _ _ _) by
    simp_rw [map_mul, Module.End.mul_eq_comp]
    rw [map_comp, Function.comp_apply]
/-
**Projectivization.generalLinearGroup_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `Projec
tivization`。
形式化陈述：generalLinearGroup_smul_def (g : LinearMap.GeneralLinearGroup K V) (x : ℙ 
K V) : g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective
参数：g : LinearMap.GeneralLinearGroup K V；x : ℙ K V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma generalLinearGroup_smul_def (g : LinearMap.GeneralLinearGroup K V) (x : ℙ K V) :
    g • x = x.map g.toLinearEquiv.toLinearMap g.toLinearEquiv.injective := by
  rfl
/-
**Projectivization.matrixSpecialLinearGroup_smul_def** 是 Mathlib 中的一个引理，位于命名空间 `
Projectivization`。
形式化陈述：matrixSpecialLinearGroup_smul_def {ι F : Type*} [Fintype ι] [DecidableEq ι
] [Field F] (g : Matrix.SpecialLinearGroup ι F) (x : ℙ F (ι -> F)) : g • x = g.t
oLin'_equiv • x
参数：g : Matrix.SpecialLinearGroup ι F；x : ℙ F (ι -> F)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
-/
lemma matrixSpecialLinearGroup_smul_def {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F]
    (g : Matrix.SpecialLinearGroup ι F) (x : ℙ F (ι → F)) :
    g • x = g.toLin'_equiv • x := by
  rfl

@[simp]
/-
**Projectivization.smul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：smul_mk (g : G) {v : V} (hv : v != 0) : g • mk K v hv = mk K (g • v) ((smu
l_ne_zero_iff_ne g).mpr hv)
参数：g : G；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma smul_mk (g : G) {v : V} (hv : v ≠ 0) :
    g • mk K v hv = mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv) :=
  rfl

section transitivity

open MulAction FiniteDimensional LinearEquiv

variable (K V) in
/-
**Projectivization.linearEquiv_is_two_pretransitive** 是 Mathlib 中的一个实例，位于命名空间 `P
rojectivization`。
形式化陈述：linearEquiv_is_two_pretransitive : IsMultiplyPretransitive (V ≃ₗ[K] V) (ℙ 
K V) 2
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.is_two_pretransitive_iff`：is_two_pretransitive_iff : IsMultipl
yPretransitive G α 2 ↔ forall {a b c d : α} (_ : a != b) (_ : c != d), exists g 
: G, g • a = c ∧ g • b =…
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIndependent.linearCombinationEquiv_apply_coe`：∀ {ι : Type u'} {R :
 Type u_2} {M : Type u_4} {v : ι → M} [inst : Semiring R] [inst_1 : AddCommMonoi
d M]   [inst_2 : _root_.Module R M] (hv …
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.linearIndependent_pair_iff_ne`：linearIndependent_pair_i
ff_ne {D D' : ℙ K V} : LinearIndependent K ![D.rep, D'.rep] ↔ D != D'
· 使用定理 `FiniteDimensional.span_of_finite`：span_of_finite {A : Set V} (hA : Set.F
inite A) : FiniteDimensional K (Submodule.span K A)
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.exists_linearEquiv_restrict_eq`：∀ {K : Type u} {V : Type v} [i
nst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V]   {
W W' : Submodule K V} [FiniteD…
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用引理 `Projectivization.smul_mk`：smul_mk (g : G) {v : V} (hv : v != 0) : g • mk
 K v hv = mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv)
· 使用定理 `Projectivization.mk_eq_mk_iff`：mk_eq_mk_iff (v w : V) (hv : v != 0) (hw 
: w != 0) : mk K v hv = mk K w hw ↔ exists a : Kˣ, a • w = v
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
instance linearEquiv_is_two_pretransitive :
    IsMultiplyPretransitive (V ≃ₗ[K] V) (ℙ K V) 2 := by
  rw [is_two_pretransitive_iff]
  intro D D' E E' hD hE
  have qD {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 0 1) = D.rep := by simp
  have qD' {D D' : ℙ K V} (hD : LinearIndependent K ![D.rep, D'.rep]) :
    hD.linearCombinationEquiv (Finsupp.single 1 1) = D'.rep := by simp
  rw [← linearIndependent_pair_iff_ne] at hD hE
  let f := hD.linearCombinationEquiv.symm ≪≫ₗ hE.linearCombinationEquiv
  have : FiniteDimensional K (Submodule.span K (Set.range ![D.rep, D'.rep])) :=
    span_of_finite K (Set.finite_range _)
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  use g
  constructor
  · rw [← mk_rep D, ← mk_rep E, smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD hD, ← hg, ← qD hE]
    simp [f]
  · rw [← mk_rep D', ← mk_rep E', smul_mk, mk_eq_mk_iff]
    use 1
    simp only [one_smul, LinearEquiv.smul_def, ← qD' hD, ← hg, ← qD' hE]
    simp [f]

variable (K V) in
/-
**Projectivization.generalLinearGroup_is_two_pretransitive** 是 Mathlib 中的一个实例，位于
命名空间 `Projectivization`。
形式化陈述：generalLinearGroup_is_two_pretransitive : IsMultiplyPretransitive (LinearM
ap.GeneralLinearGroup K V) (ℙ K V) 2
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用引理 `Projectivization.smul_mk`：smul_mk (g : G) {v : V} (hv : v != 0) : g • mk
 K v hv = mk K (g • v) ((smul_ne_zero_iff_ne g).mpr hv)
· 使用定理 `MulAction.IsPretransitive.of_embedding`：∀ {G : Type u_1} {α : Type u_2} 
[inst : Group G] [inst_1 : MulAction G α] {H : Type u_3} {β : Type u_4}   [inst_
2 : Group H] [inst_3 : MulAc…
· 使用定理 `Function.surjective_id`：∀ {α : Sort u_1}, Function.Surjective id
-/
instance generalLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (LinearMap.GeneralLinearGroup K V) (ℙ K V) 2 := by
  let f : ℙ K V →ₑ[LinearMap.GeneralLinearGroup.ofLinearEquiv (R := K) (M := V)] ℙ K V := {
    toFun := id
    map_smul' e D := by
      simp only [id_eq]
      rw [← mk_rep D, smul_mk, smul_mk]
      dsimp }
  exact IsPretransitive.of_embedding (f := f) Function.surjective_id

end transitivity

end DivisionRing

section Field

open MulAction LinearEquiv SpecialLinearGroup

variable {K V : Type*} [AddCommGroup V] [Field K] [Module K V]

/-
**Projectivization.specialLinearGroup_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `Projec
tivization`。
形式化陈述：specialLinearGroup_smul_def (g : SpecialLinearGroup K V) (D : ℙ K V) : g •
 D = g.toLinearEquiv • D
参数：g : SpecialLinearGroup K V；D : ℙ K V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpecialLinearGroup.instSMulCommClass`：∀ {R : Type u_1} {V : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   SMul
CommClass (SpecialLinearGr…
-/
theorem specialLinearGroup_smul_def (g : SpecialLinearGroup K V) (D : ℙ K V) :
    g • D = g.toLinearEquiv • D := rfl

variable (K V) in
/-
**Projectivization.specialLinearGroup_is_two_pretransitive** 是 Mathlib 中的一个实例，位于
命名空间 `Projectivization`。
形式化陈述：specialLinearGroup_is_two_pretransitive : IsMultiplyPretransitive (Special
LinearGroup K V) (ℙ K V) 2
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SpecialLinearGroup.instSMulCommClass`：∀ {R : Type u_1} {V : Type u_2} [i
nst : CommRing R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V],   SMul
CommClass (SpecialLinearGr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.is_two_pretransitive_iff`：is_two_pretransitive_iff : IsMultipl
yPretransitive G α 2 ↔ forall {a b c d : α} (_ : a != b) (_ : c != d), exists g 
: G, g • a = c ∧ g • b =…
· 使用定理 `Projectivization.linearIndepOn_pair`：linearIndepOn_pair (D D' : ℙ K V) :
 LinearIndepOn K id {D.rep, D'.rep}
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Projectivization.rep_nonzero`：rep_nonzero (v : ℙ K V) : v.rep != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Projectivization.mk_rep`：mk_rep (v : ℙ K V) : mk K v.rep v.rep_nonzero =
 v
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Module.Basis.coord_apply`：∀ {ι : Type u_10} {R : Type u_11} {M : Type u_
12} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M
] (b : Module.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LinearMap.transvection.det`：∀ {R : Type u_3} {V : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module R V]   [Module.Free R 
V] [Module.Finit…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
（共 97 条，此处仅展示前 30 条）
-/
instance specialLinearGroup_is_two_pretransitive :
    IsMultiplyPretransitive (SpecialLinearGroup K V) (ℙ K V) 2 := by
  have := linearEquiv_is_two_pretransitive K V
  rw [is_two_pretransitive_iff] at this ⊢
  intro D D' E E' hD hE
  obtain ⟨g, gD, gE⟩ := this hD hE
  by_cases hV : FiniteDimensional K V
  · suffices ∀ a : Kˣ, ∃ h : V ≃ₗ[K] V, h.det = a ∧ h • D = D ∧ h • D' = D' by
      obtain ⟨h, hdet, hD, hE⟩ := this (g.det)⁻¹
      use ⟨g * h, by simp [hdet]⟩
      simp [specialLinearGroup_smul_def, toLinearEquiv_eq_coe, mul_smul, gD, hD, gE, hE]
    intro a
    rw [← linearIndependent_pair_iff_ne] at hD
    have := linearIndepOn_pair D D'
    let s := (linearIndepOn_pair D D').extend (Set.subset_univ _)
    let b : Module.Basis s K V := Module.Basis.extend this
    rw [← mk_rep D, ← mk_rep D']
    have hD_mem : D.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    have hD'_mem : D'.rep ∈ s := LinearIndepOn.subset_extend _ _ (by simp)
    refine ⟨dilatransvection (f := b.coord ⟨D.rep, hD_mem⟩)
      (v := (a.val - 1) • b ⟨D.rep, hD_mem⟩) (by simp), ?_, ?_, ?_⟩
    · simp [← Units.val_inj, coe_det, LinearMap.transvection.det]
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use a
      rw [← coe_coe, dilatransvection.coe_toLinearMap,
        LinearMap.transvection.apply, Module.Basis.coord_apply]
      suffices (b.repr D.rep) ⟨D.rep, hD_mem⟩ = 1 by
        rw [this, Module.Basis.extend_apply_self, Units.smul_def]
        module
      nth_rewrite 1 [show D.rep = (⟨D.rep, hD_mem⟩ : s) by rfl]
      rw [← Module.Basis.extend_apply_self, Module.Basis.repr_self]
      simp
    · rw [smul_mk, mk_eq_mk_iff, LinearEquiv.smul_def]
      use 1
      rw [one_smul, ← coe_coe, dilatransvection.coe_toLinearMap,
        LinearMap.transvection.apply, Module.Basis.coord_apply]
      suffices (b.repr D'.rep) ⟨D.rep, hD_mem⟩ = 0 by
        rw [Module.Basis.extend_apply_self]
        simp [this]
      nth_rewrite 1 [show D'.rep = (⟨D'.rep, hD'_mem⟩ : s) by rfl]
      rw [← Module.Basis.extend_apply_self, Module.Basis.repr_self]
      apply Finsupp.single_eq_of_ne
      simp only [ne_eq, ← Subtype.coe_inj]
      intro h
      apply Fin.zero_ne_one
      apply hD.injective
      simp [h]
  use ⟨g, by
    rw [← Units.val_inj, coe_det]
    apply LinearMap.det_eq_one_of_not_module_finite hV⟩
  simp [← gD, ← gE, specialLinearGroup_smul_def, toLinearEquiv_eq_coe]

/-- The special linear group `SpecialLinearGroup K V` acts primitively on `ℙ K V`. -/
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The special linear group `SpecialLinearGroup K V` acts primitively on `ℙ K V`.
-/
instance : IsPreprimitive (SpecialLinearGroup K V) (ℙ K V) :=
  isPreprimitive_of_is_two_pretransitive inferInstance

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsMultiplyPretransitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K)) 2 :=
  let φ : SpecialLinearGroup K (ι → K) →* Matrix.SpecialLinearGroup ι K :=
    Matrix.SpecialLinearGroup.toLin'_equiv.symm.toMonoidHom
  let f : ℙ K (ι → K) →ₑ[φ] ℙ K (ι → K) :=
    { toFun := id
      map_smul' g D := by simp [φ, matrixSpecialLinearGroup_smul_def]}
  IsPretransitive.of_embedding (f := f) Function.surjective_id
/-
**Projectivization.prePrimitive_SL** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
形式化陈述：prePrimitive_SL : IsPreprimitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι -
> K))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.isPreprimitive_of_is_two_pretransitive`：isPreprimitive_of_is_t
wo_pretransitive (h2 : IsMultiplyPretransitive G α 2) : IsPreprimitive G α
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
· 使用定理 `Projectivization.instIsMultiplyPretransitiveSpecialLinearGroupForallOfNa
tNat`：∀ {K : Type u_1} [inst : Field K] {ι : Type u_3} [inst_1 : Fintype ι] [ins
t_2 : DecidableEq ι],   MulAction.IsMultiplyPretransitive (Matrix.…
-/
instance prePrimitive_SL : IsPreprimitive (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  isPreprimitive_of_is_two_pretransitive inferInstance
/-
**Projectivization.SL_mulAction_ker** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`
。
形式化陈述：SL_mulAction_ker : (MulAction.toPermHom (Matrix.SpecialLinearGroup ι K) (ℙ
 K (ι -> K))).ker = Subgroup.center (Matrix.SpecialLinearGroup ι K)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `Matrix.instSMulCommClassSpecialLinearGroupForall`：∀ {F : Type u_1} [inst
 : CommRing F] {ι : Type u_2} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι],   S
MulCommClass (Matrix.SpecialLinearGrou…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulAction.toPermHom_apply`：∀ (G : Type u_1) (α : Type u_5) [inst : Group
 G] [inst_1 : MulAction G α] (a : G),   (MulAction.toPermHom G α) a = MulAction.
toPerm a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MulAction.toPerm_apply`：∀ {α : Type u_5} {β : Type u_6} [inst : Group α]
 [inst_1 : MulAction α β] (a : α) (x : β),   (MulAction.toPerm a) x = a • x
· 使用定理 `LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent`：exists_eq_sm
ul_id_of_forall_notLinearIndependent [CommRing R] [IsDomain R] [AddCommGroup V] 
[Module R V] [Free R V] {f : V ->ₗ[R] V} (h : fo…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
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
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 47 条，此处仅展示前 30 条）
-/
lemma SL_mulAction_ker :
    (MulAction.toPermHom (Matrix.SpecialLinearGroup ι K) (ℙ K (ι → K))).ker =
      Subgroup.center (Matrix.SpecialLinearGroup ι K) := by
  ext m
  simp only [MonoidHom.mem_ker, toPermHom_apply, Equiv.Perm.one_def, DFunLike.ext_iff, toPerm_apply,
    Equiv.refl_apply, Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨fun hm ↦ ?_, fun ⟨r, hr1, hr2⟩ l ↦ ?_⟩
  · set f : (ι → K) →ₗ[K] ι → K := (Matrix.SpecialLinearGroup.toLin' m).toLinearMap with hf
    obtain ⟨a, ha⟩ := f.exists_eq_smul_id_of_forall_notLinearIndependent fun (v : ι → K) ↦ by
      by_cases hv : v = 0
      · simp [hv, linearIndependent_fin2]
      · simpa [LinearIndependent.pair_iff' hv, mk_eq_mk_iff'] using! hm (.mk K v hv)
    have hscalar : m.1 = Matrix.scalar ι a := calc
      m.1 = LinearMap.toMatrix' f := by
        rw [hf, Matrix.SpecialLinearGroup.toLin'_to_linearMap, LinearMap.toMatrix'_toLin']
      _ = (algebraMap K (Module.End K (ι → K)) a).toMatrix' := congrArg LinearMap.toMatrix' ha
      _ = Matrix.scalar ι a := LinearMap.toMatrix'_algebraMap a
    exact ⟨a, by simpa [hscalar] using m.2, hscalar.symm⟩
  · induction l using Projectivization.ind with | _ v hv =>
    simp only [smul_mk, mk_eq_mk_iff']
    use r
    change _ = m.1 • v
    simp [← hr2]

/-- The action of the special linear group on `ℙ F (ι → F)` factors through the
projective special linear group `PSL = SL ⧸ Z(SL)`. -/
/-
**Projectivization.PSLAction.toPermHom** 是 Mathlib 中的一个定义，位于命名空间 `Projectivizati
on.PSLAction`。
形式化陈述：{K : Type u_1} →   [inst : Field K] →     {ι : Type u_3} →       [inst_1 :
 Fintype ι] →         [inst_2 : DecidableEq ι] → Matrix.ProjectiveSpecialLinearG
roup ι K →* Equiv.Perm (Projectivization K (ι → K))
参数：Projectivization K (ι → K)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The action of the special linear group on `ℙ F (ι → F)` factors through the
projective special linear group `PSL = SL ⧸ Z(SL)`.
-/
def PSLAction.toPermHom :
    Matrix.ProjectiveSpecialLinearGroup ι K →* Equiv.Perm (ℙ K (ι → K)) :=
  QuotientGroup.lift _ (MulAction.toPermHom _ _) (le_of_eq SL_mulAction_ker.symm)
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  MulAction.compHom _ PSLAction.toPermHom
/-
**Projectivization._root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk** 是 M
athlib 中的一个引理，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk (g : Matrix.SpecialLinearGroup ι K)
    (p : ℙ K (ι → K)) : (g : Matrix.ProjectiveSpecialLinearGroup ι K) • p = g • p := rfl
/-
**Projectivization._root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injectiv
e** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective :
    Function.Injective (PSLAction.toPermHom (K := K) (ι := ι)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  rwa [← MonoidHom.mem_ker, PSLAction.toPermHom,
    QuotientGroup.ker_lift, SL_mulAction_ker, QuotientGroup.map_mk'_self,
    Subgroup.mem_bot] at hg
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FaithfulSMul (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  faithfulSMul_iff.2 fun g hg ↦
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective <| Equiv.ext fun x ↦ by
      simpa using! hg x
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreprimitive (Matrix.ProjectiveSpecialLinearGroup ι K) (ℙ K (ι → K)) :=
  @MulAction.IsPreprimitive.of_surjective _ _ _ _ _ _ _ _ (QuotientGroup.mk' _)
    {toFun := id, map_smul' := by intros; simp; rfl} (prePrimitive_SL (ι := ι) (K := K))
    Function.surjective_id

open MatrixGroups Matrix.ProjGenLinGroup
/-
**Projectivization.** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction PGL(ι, K) (ℙ K (ι → K)) :=
  mulActionOfGL fun u ↦ ind fun v hv ↦ by
    simp only [smul_mk, mk_eq_mk_iff]
    exact ⟨u, by simp [Units.smul_def]⟩

@[simp]
/-
**Projectivization.PGL.mk_smul_mk** 是 Mathlib 中的一个定理，位于命名空间 `Projectivization.PG
L`。
形式化陈述：∀ {K : Type u_1} [inst : Field K] {ι : Type u_3} [inst_1 : Fintype ι] [ins
t_2 : DecidableEq ι] (g : GL ι K) {v : ι → K}   (hv : v ≠ 0), Matrix.ProjGenLinG
roup.mk g • Projectivization.mk K v hv = Projectivization.mk K (g • v) ⋯
参数：g : GL ι K；hv : v ≠ 0；g • v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma PGL.mk_smul_mk (g : GL ι K) {v : ι → K} (hv : v ≠ 0) :
    (.mk g : PGL(ι, K)) • mk K v hv = mk K (g • v) (smul_ne_zero_iff_ne g|>.2 hv) := rfl

end Field

end Projectivization

